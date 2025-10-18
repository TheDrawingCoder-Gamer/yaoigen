package gay.menkissing.yaoigen

import language.experimental.saferExceptions

import scala.collection.mutable
import util.ResourceLocation
import parser.ast
import java.nio.file.Path
import java.io.File
import gay.menkissing.yaoigen.util.FileInfo
import gay.menkissing.yaoigen.util.ResourceKind
import io.circe.Json
import gay.menkissing.yaoigen.util.ScoreboardLocation
import gay.menkissing.yaoigen.parser.ast.Parameter
import gay.menkissing.yaoigen.parser.ast.ReturnType
import gay.menkissing.yaoigen.parser.ast.ParameterKind
import gay.menkissing.yaoigen.util.{mcdisplay, given}

object Resolver:
  sealed abstract class ResolverError extends Exception:
    def showPretty: String
  case class ParseError(err: String) extends ResolverError:
    override def showPretty: String = err
  case class ResolutionError(location: util.Location, msg: Seq[String]) extends ResolverError:
    override def showPretty: String =
      s"${location.pretty}\n${msg.mkString("\n")}"

  object ResolutionError:
    def apply(loc: util.Location, msg: String): ResolutionError =
      ResolutionError(loc, Seq(msg))

  // mutable scope
  class Scope(
    val parent: Int,
    val children: mutable.HashMap[String, mutable.ArrayDeque[Int]] = mutable.HashMap(),
    val functionRegistry: mutable.HashMap[String, ResourceLocation] = mutable.HashMap()
    ):
    def addChild(name: String, child: Int): Unit =
      children.get(name) match
        case Some(v) => v.append(child)
        case None => children(name) = mutable.ArrayDeque(child)

    def getChild(name: String): Option[Int] =
      children.get(name).map(_.removeHead())
  
  case class FunctionDefinition(
                               location: ResourceLocation,
                               arguments: List[Parameter],
                               returnType: ReturnType
                               )

case class ResolveResult(
  scopes: Vector[Resolver.Scope],
  config: Option[Json],
  tickFunctions: List[String],
  loadFunctions: List[String],
  usedScoreboards: Map[String, String],
  functionRegistry: Map[ResourceLocation, Resolver.FunctionDefinition],
  resultTree: List[ast.Namespace]
  )

case class ResolveContext(fileInfo: util.FileInfo)

class Resolver:
  import Resolver.*
  val scopes = mutable.ArrayBuffer[Scope]()
  val includedModules = mutable.HashSet[String]()
  var config: Option[Json] = None
  val tickFunctions = mutable.ArrayBuffer[String]()
  val loadFunctions = mutable.ArrayBuffer[String]()
  val usedScoreboards = mutable.HashMap[String, String]()
  val functionRegistry = mutable.HashMap[ResourceLocation, FunctionDefinition]()

  def pushScope(name: String, parent: Int): Int =
    scopes.append(Scope(parent))
    val index = scopes.length - 1
    scopes(parent).addChild(name, index)
    index

  def addFunction(scope: Int, name: String, location: ResourceLocation): Unit =
    scopes(scope).functionRegistry(name) = location

  def resolveModule(name: String, items: List[ast.Decl], location: ResourceLocation, parentScope: Int)(using ResolveContext): List[ast.Decl] throws ResolverError =
    val index = pushScope(name, parentScope)
    val newLoc = location.copy(modules = location.modules.appended(name))
    items.map: item =>
      resolveItem(item, newLoc, index)

  private def parseIncludedItems(pos: util.Location, path: String)(using ctx: ResolveContext): List[ast.Decl] throws ResolverError =
    val newInfo = ctx.fileInfo.copy(file = path)
    val parser = Parser(newInfo)
    val file = File(path)
    parser.parseIncludedItems.parseFile(file).toEither.left.map(_ => ResolutionError(pos, "Couldn't open file"))
      .flatMap(_.toEither.left.map[ResolverError](ParseError.apply)) match
        case Left(err) => throw err
        case Right(items) => items
  def resolveItem(item: ast.Decl, location: ResourceLocation, parentScope: Int)(using ctx: ResolveContext): ast.Decl throws ResolverError =
    import ast.Decl.*
    item match
      case Module(p, name, items) =>
        Module(p, name, resolveModule(name, items, location, parentScope))
      case UseModule(modulePos, name) =>
        val newPath =
          if ctx.fileInfo.root == ctx.fileInfo.file then
            // resolve sibling
            Path.of(ctx.fileInfo.root).resolveSibling(name + ".yaoi")
          else
            // resolve subdirectory
            assert(ctx.fileInfo.file.endsWith(".yaoi"))
            Path.of(ctx.fileInfo.file.dropRight(5)).resolve(name + ".yaoi")
        val newInfo = ctx.fileInfo.copy(file = newPath.toString)
        Module(modulePos, name, resolveModule(name, parseIncludedItems(modulePos, newPath.toString), location, parentScope)(using ResolveContext(newInfo)))

      case IncludedItems(pos, from, _) =>
        val newPath =
          Path.of(ctx.fileInfo.file).resolveSibling(from + ".yaoi")
        val newInfo = ctx.fileInfo.copy(file = newPath.toString)
        IncludedItems(pos, from, 
          parseIncludedItems(pos, newPath.toString).map: it =>
            resolveItem(it, location, parentScope)(using ResolveContext(newInfo))
        )
        


      case f @ ZFunction(_, returnType, name, params, _) =>
        resolveFunction(returnType, name, params, location, parentScope)
        f
        
      case r: ZResource => r
      case c @ ZConfig(pos, data) =>
        if config.isDefined  then
          throw ResolutionError(pos, "Duplicate mcmeta")
        else
          config = Some(data)
        c
        
      case b: ZBuiltinCall => b
    
  
  private def resolveFunction(returnType: ReturnType, name: String, params: List[Parameter], location: ResourceLocation, parentScope: Int): Unit = {
    val functionLocation = location.withName(name)
    val functionPath = functionLocation.mcdisplay

    if params.exists(_.kind == ParameterKind.Scoreboard) then
      usedScoreboards(ScoreboardLocation(functionLocation, "").scoreboardString) = "dummy"

    val definition = FunctionDefinition(
      functionLocation,
      params,
      returnType
    )

    addFunction(parentScope, name, location)

    functionRegistry(functionLocation) = definition

    if name == "tick" && location.modules.isEmpty then
      tickFunctions.append(functionPath)
    else if name == "load" && location.modules.isEmpty then
      loadFunctions.append(functionPath)

  }

  def resolveNamespace(ns: ast.Namespace, parentScope: Int)(using ResolveContext): ast.Namespace throws ResolverError =
    val index = pushScope(ns.name, parentScope)

    val resource = ResourceLocation(ns.name, List(), ResourceKind.Module)

    val newItems = 
      ns.items.map: item =>
        resolveItem(item, resource, index)
    ast.Namespace(ns.pos, ns.name, newItems)


  def resolveTrees(root: String): Either[ResolverError, ResolveResult] =
    scopes.append(Scope(0))
    val file = File(root)
    val parser = Parser(FileInfo(root, root))
    parser.parseAll.parseFile(file).toEither.left.map(_ => ResolutionError(util.Location(0, 0, root, root), "Couldn't open file"))
      .flatMap(_.toEither.left.map[ResolverError](ParseError.apply)).flatMap: tree =>
        try
          val newNses =
            tree.map: ns =>
              resolveNamespace(ns, 0)(using ResolveContext(FileInfo(root, root)))
          
          Right(ResolveResult(scopes.toVector, config, tickFunctions.toList, loadFunctions.toList, usedScoreboards.toMap, functionRegistry.toMap, newNses))
        catch
          case x: ResolverError =>
            Left(x)


      


    

