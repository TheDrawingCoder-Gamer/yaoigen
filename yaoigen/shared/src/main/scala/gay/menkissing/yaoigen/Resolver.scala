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
  case class ResolutionError(location: Option[util.Location], msg: Seq[String]) extends ResolverError:
    override def showPretty: String =
      location match
        case Some(v) =>
          error.LocationError.show(v, msg)
        case None =>
          msg.mkString("\n")

  object ResolutionError:
    def apply(loc: util.Location, msg: Seq[String]): ResolutionError =
      ResolutionError(Some(loc), msg)
    def apply(loc: util.Location, msg: String): ResolutionError =
      ResolutionError(Some(loc), Seq(msg))

    def global(msg: Seq[String]): ResolutionError =
      ResolutionError(None, msg)
    def global(msg: String): ResolutionError =
      ResolutionError(None, Seq(msg))

  case class ResolvedScope(
    val children: Map[String, ResolvedScope],
    val functionRegistry: Map[String, ResourceLocation]
  )(parentRes: => Option[ResolvedScope]):
    lazy val parent = parentRes

  // mutable scope
  class Scope(
    val parent: Int,
    val children: mutable.HashMap[String, Int] = mutable.HashMap(),
    val functionRegistry: mutable.HashMap[String, ResourceLocation] = mutable.HashMap()
    ):
      // this part is only ever used in Resolver, so we can just make it ResolverError
    def addChild(pos: util.Location, name: String, child: Int): Unit throws ResolutionError =
      children.get(name) match
        case Some(_) => 
          throw ResolutionError(pos, s"Duplicate child $name")
        case None => children(name) = child

    def getChild(name: String): Option[Int] =
      children.get(name)
  
  case class FunctionDefinition(
                               location: ResourceLocation,
                               arguments: List[Parameter],
                               returnType: ReturnType
                               )

case class ResolveResult(
  scope: Resolver.ResolvedScope,
  config: Option[Json],
  tickFunctions: List[String],
  loadFunctions: List[String],
  usedScoreboards: Map[String, String],
  functionRegistry: Map[ResourceLocation, Resolver.FunctionDefinition],
  resultTree: List[ast.Namespace]
  )

case class ResolveContext(fileInfo: util.FileInfo, subModuleAllowed: Boolean)

class Resolver:
  import Resolver.*
  val scopes = mutable.ArrayBuffer[Scope]()
  val includedModules = mutable.HashSet[String]()
  var config: Option[Json] = None
  val tickFunctions = mutable.ArrayBuffer[String]()
  val loadFunctions = mutable.ArrayBuffer[String]()
  val usedScoreboards = mutable.HashMap[String, String]()
  val functionRegistry = mutable.HashMap[ResourceLocation, FunctionDefinition]()

  object report:
    val nonfatalErrors = mutable.ArrayBuffer[ResolverError]()

    def apply(err: ResolverError): Unit =
      nonfatalErrors.append(err)
    
    def displayAll: Unit throws ResolverError =
      nonfatalErrors.foreach: it =>
        println(it.showPretty)
      if nonfatalErrors.nonEmpty then
        throw ResolutionError.global(Seq("Resolution errors found", "(couldn't parse and assemble all files)"))

    def submoduleError(pos: util.Location): Unit =
      report(ResolutionError(pos, Seq("Can't do submodules inside an included file.", "If you need submodules, make the entire heirarchy submodules.")))

  def assembleScope(mut: Scope, parent: => Option[ResolvedScope]): ResolvedScope =
    // ??????????????
    // Evil recursion
    lazy val children: List[(String, ResolvedScope)] =
      mut.children.toList.map: (name, idx) =>
        (name, assembleScope(scopes(idx), Some(res)))
    lazy val res: ResolvedScope =
      ResolvedScope(children.toMap, mut.functionRegistry.toMap)(parent)
    res

    


  def pushScope(pos: util.Location, name: String, parent: Int): Int throws ResolutionError =
    scopes.append(Scope(parent))
    val index = scopes.length - 1
    scopes(parent).addChild(pos, name, index)
    index

  def addFunction(scope: Int, name: String, location: ResourceLocation): Unit =
    scopes(scope).functionRegistry(name) = location

  def resolveModule(pos: util.Location, name: String, items: List[ast.Decl], location: ResourceLocation, parentScope: Int)(using ResolveContext): List[ast.Decl] throws ResolverError =
    val index = pushScope(pos, name, parentScope)
    val newLoc = location.copy(modules = location.modules.appended(name))
    items.map: item =>
      resolveItem(item, newLoc, index)

  private def parseIncludedItems(pos: util.Location, path: String)(using ctx: ResolveContext): List[ast.Decl] throws ResolverError =
    val newInfo = ctx.fileInfo.copy(file = path)
    val parser = Parser(newInfo)
    val file = File(path)
    parser.parseIncludedItems.parseFile(file).toEither.left.map(_ => ResolutionError(pos, s"Can't open file $path"))
      .flatMap(_.toEither.left.map[ResolverError](ParseError.apply)) match
        case Left(err) =>
          report(err)
          List()
        case Right(items) => items



  def getSubmoduleInfo(info: FileInfo, name: String): FileInfo =
    val newPath =
      if info.root == info.file then
        Path.of(info.root).resolveSibling(name + ".yaoi").normalize()
      else
        assert(info.file.endsWith(".yaoi"))
        Path.of(info.file.dropRight(5)).resolve(name + ".yaoi").normalize()
    info.copy(file = newPath.toString)
  def resolveItem(item: ast.Decl, location: ResourceLocation, parentScope: Int)(using ctx: ResolveContext): ast.Decl throws ResolverError =
    import ast.Decl.*
    item match
      case Module(p, name, items) =>
        Module(p, name, resolveModule(p, name, items, location, parentScope))
      case m @ SubModule(modulePos, name) =>
        if !ctx.subModuleAllowed then
          report.submoduleError(modulePos)
          return m
        val newInfo = getSubmoduleInfo(ctx.fileInfo, name)
        Module(modulePos, name, resolveModule(modulePos, name, parseIncludedItems(modulePos, newInfo.file), location, parentScope)(using ctx.copy(fileInfo = newInfo)))
      case m @ UsedModule(modulePos, name) =>
        if !ctx.subModuleAllowed then
          report.submoduleError(modulePos)
          return m
        val newInfo = getSubmoduleInfo(ctx.fileInfo, name)
        IncludedItems(modulePos, name,
          parseIncludedItems(modulePos, newInfo.file)(using ctx.copy(fileInfo = newInfo)).map: it =>
            resolveItem(it, location, parentScope)(using ctx.copy(fileInfo = newInfo)))

      case IncludedItems(pos, from, _) =>
        val newPath =
          Path.of(ctx.fileInfo.file).resolveSibling(from + ".yaoi").normalize()
        val newInfo = ctx.fileInfo.copy(file = newPath.toString)
        IncludedItems(pos, from, 
          parseIncludedItems(pos, newPath.toString).map: it =>
            resolveItem(it, location, parentScope)(using ResolveContext(newInfo, false))
        )
        


      case f @ ZFunction(_, returnType, name, params, _) =>
        resolveFunction(returnType, name, params, location, parentScope)
        f
        
      case r: ZResource => r
      case c @ ZConfig(pos, data) =>
        if config.isDefined  then
          report(ResolutionError(pos, "Duplicate mcmeta"))
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
    val index = pushScope(ns.pos, ns.name, parentScope)

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
              resolveNamespace(ns, 0)(using ResolveContext(FileInfo(root, root), true))
          
          // displays any errors and throws if there were any at all
          report.displayAll
          Right(ResolveResult(assembleScope(scopes.head, None), config, tickFunctions.toList, loadFunctions.toList, usedScoreboards.toMap, functionRegistry.toMap, newNses))
        catch
          case x: ResolverError =>
            Left(x)


      


    

