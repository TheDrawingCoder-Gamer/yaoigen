package gay.menkissing.yaoigen

import language.experimental.saferExceptions

import gay.menkissing.yaoigen.parser.ast.{ArrayKind, BinopKind, CommandPart, ElseStatement, Expr, ForRange, InsertedExpr, ParameterKind, ReturnType, Stmt, UnaryKind}
import util.{Location, ResourceKind, ResourceLocation, ScoreboardLocation, StorageLocation, mcdisplay, given}
import util.MCFunctionDisplay.{mcfunc, given}

import java.util.Comparator
import scala.collection.mutable
import scala.util.Using
import cats.implicits.*
import cats.*
import gay.menkissing.yaoigen.Compiler.FileTree.Item
import gay.menkissing.yaoigen.parser.ast
import gay.menkissing.yaoigen.parser.ast.Decl.ZResource
import io.circe.*
import io.circe.syntax.*

import java.nio.file.attribute.BasicFileAttributes
import java.nio.file.{FileVisitResult, Path, SimpleFileVisitor}
import gay.menkissing.yaoigen.util.MCFunctionDisplay
import gay.menkissing.yaoigen.parser.ast.BuiltinArg
import gay.menkissing.yaoigen.util.PathHelper




object Compiler:
  case class MinecraftTag(values: List[String]) derives Decoder, Encoder


  case class MCMetaPack(packFormat: Int, description: String)

  given Decoder[MCMetaPack] =
    Decoder.forProduct2("pack_format", "description")(MCMetaPack.apply)

  given Encoder[MCMetaPack] =
    Encoder.forProduct2("pack_format", "description")(u =>
      (u.packFormat, u.description)
    )

  case class MCMeta(pack: MCMetaPack) derives Encoder, Decoder



  case class InternalError(location: util.Location, msg: String) extends RuntimeException:
    override def getMessage: String =
      show"Internal error ${location}:\n${msg}"

  sealed abstract class CompileError extends Exception:
    val location: util.Location
    val msg: Seq[String]

    override def getMessage: String =
      show"${location}:\n${msg.mkString("\n")}"
    def showPretty: String =
      error.LocationError.show(location, msg)
      

  case class NonfatalCompileError(location: util.Location, msg: Seq[String]) extends CompileError
  case class FatalCompileError(location: util.Location, msg: Seq[String]) extends CompileError

  object CompileError:
    // if thrown, non fatal just means back out of the function - other functions should be able to be compiled correctly so we can get more errors
    def nonfatal(location: util.Location, msg: String): CompileError =
      NonfatalCompileError(location, msg.linesIterator.toSeq)
    def nonfatal(location: util.Location, msg: Seq[String]): CompileError =
      NonfatalCompileError(location, msg)
    def fatal(location: util.Location, msg: String): CompileError =
      FatalCompileError(location, msg.linesIterator.toSeq)
    def fatal(location: util.Location, msg: Seq[String]): CompileError =
      FatalCompileError(location, msg)

  case class CalledFunction(location: ResourceLocation, returnType: ReturnType)

  enum FunctionCommand:
    case PlainCall(location: ResourceLocation)
    case MacroCall(location: ResourceLocation, storage: ResourceLocation)

  given MCFunctionDisplay[FunctionCommand] =
    case FunctionCommand.PlainCall(location) => mcfunc"function $location"
    case FunctionCommand.MacroCall(location, storage) => mcfunc"function $location with storage $storage"

  enum NestKind:
    case Loop(loopContext: LoopContext)
    case Block
    case Transparent

  enum AssignTarget:
    case Scoreboard(loc: ScoreboardLocation)
    case Data(kind: DataKind)

  case class NestedInfo(kind: NestKind, parent: Option[NestedInfo], actualLocation: ResourceLocation, label: Option[String]):
    def currentLoopContext: Option[LoopContext] =
      kind match
        case NestKind.Loop(loopContext) => Some(loopContext)
        case _ =>
          parent match
            case Some(p) => p.currentLoopContext
            case None => None
        

    def getLoop: Option[NestedInfo] =
      kind match
        case NestKind.Loop(_) => Some(this)
        case _ =>
          parent match
            case Some(p) => p.getLoop
            case None => None

    def isLoop: Boolean =
      kind match
        case NestKind.Loop(_) => true
        case _ => false

    def canBeBroken: Boolean =
      kind match
        case NestKind.Loop(_) => true
        case NestKind.Block => true
        case NestKind.Transparent => false

    def loopsUntilLabel(label: String): (NestedInfo, Int) throws CompileError =
      kind match
        case NestKind.Loop(_) if this.label.exists(_ == label) =>
          (this, 0)
        case _ =>
          parent match
            case None =>
              throw CompileError.nonfatal(util.Location.blank, s"No such label $label in scope")
            case Some(p) =>
              val (it, n) = p.loopsUntilLabel(label)
              if this.isLoop then
                (it, n + 1)
              else
                (it, n)
          

  enum DataKind:
    case Storage(storage: StorageLocation)
    case Entity(selector: String, path: String)
    case Block(pos: (BlockCoord, BlockCoord, BlockCoord), path: String)

    def editPath(f: String => String): DataKind =
      this match
        case Storage(loc) => DataKind.Storage(loc.copy(name = f(loc.name)))
        case Entity(selector, path) => DataKind.Entity(selector, f(path))
        case Block(pos, path) => DataKind.Block(pos, f(path))

    def subPath(x: String): DataKind =
      editPath(path => util.PathHelper.subPath(path, x))
    def index(i: Int): DataKind = editPath(path => s"$path[$i]")



  given MCFunctionDisplay[DataKind] =
    case DataKind.Storage(storage) => mcfunc"storage $storage"
    case DataKind.Entity(selector, path) => s"entity $selector $path"
    case DataKind.Block((x, y, z), path) => mcfunc"block $x $y $z $path"

  enum StorageKind:
    case Modify, MacroModify
    case Store, MacroStore

  object Expression:
    def void(at: util.Location): Expression =
      Expression(at, false, ExpressionKind.EVoid)

  case class Expression(location: util.Location, needsMacro: Boolean, kind: ExpressionKind):
    def index(indexPos: util.Location, idx: Int): Expression throws CompileError =
      kind match
        case ExpressionKind.EStorage(path) => copy(location = indexPos, kind = ExpressionKind.EStorage(path.copy(name = s"${path.name}[$idx]")))
        case ExpressionKind.EEntity(selector, path) => copy(location = indexPos, kind = ExpressionKind.EEntity(selector, s"$path[$idx]"))
        case ExpressionKind.EBlock(pos, path) => copy(location = indexPos, kind = ExpressionKind.EBlock(pos, s"$path[$idx]"))
        case ExpressionKind.EArray(values, _) =>
          if idx >= values.length then
            throw CompileError.nonfatal(indexPos, "Index out of range")
          else
            values(idx)
        case ExpressionKind.EByteArray(values) =>
          if idx >= values.length then
            throw CompileError.nonfatal(indexPos, "Index out of range")
          else
            values(idx)
        case ExpressionKind.EIntArray(values) =>
          if idx >= values.length then
            throw CompileError.nonfatal(indexPos, "Index out of range")
          else
            values(idx)
        case ExpressionKind.ELongArray(values) =>
          if idx >= values.length then
            throw CompileError.nonfatal(indexPos, "Index out of range")
          else
            values(idx)
        case _ =>
          throw CompileError.nonfatal(indexPos, "This expression can't be indexed")
    def subPath(indexPos: util.Location, name: String): Expression throws CompileError =
      kind match
        case ExpressionKind.EStorage(path) => copy(location = indexPos, kind = ExpressionKind.EStorage(path.copy(name = PathHelper.subPath(path.name, name))))
        case ExpressionKind.EEntity(selector, path) => copy(location = indexPos, kind = ExpressionKind.EEntity(selector, PathHelper.subPath(path, name)))
        case ExpressionKind.EBlock(pos, path) => copy(location = indexPos, kind = ExpressionKind.EBlock(pos, PathHelper.subPath(path, name)))
        case ExpressionKind.ECompound(kvs) =>
          kvs.get(name) match
            case Some(value) => value
            case _ =>
              throw CompileError.nonfatal(indexPos, s"No such key '$name'")
        case _ =>
          throw CompileError.nonfatal(indexPos, "This expression can't be indexed")
    def valueEqual(that: Expression): Option[Boolean] =
      (this.kind, that.kind) match
        case (ExpressionKind.EVoid, ExpressionKind.EVoid) => Some(true)
        case (ExpressionKind.EByte(l0), ExpressionKind.EByte(r0)) => Some(l0 == r0)
        case (ExpressionKind.EShort(l0), ExpressionKind.EShort(r0)) => Some(l0 == r0)
        case (ExpressionKind.EInteger(l0), ExpressionKind.EInteger(r0)) => Some(l0 == r0)
        case (ExpressionKind.ELong(l0), ExpressionKind.ELong(r0)) => Some(l0 == r0)
        case (ExpressionKind.EFloat(l0), ExpressionKind.EFloat(r0)) => Some(l0 == r0)
        case (ExpressionKind.EDouble(l0), ExpressionKind.EDouble(r0)) => Some(l0 == r0)
        case (ExpressionKind.EBoolean(l0), ExpressionKind.EBoolean(r0)) => Some(l0 == r0)
        case (ExpressionKind.EString(l0), ExpressionKind.EString(r0)) => Some(l0 == r0)
        case (ExpressionKind.EArray(lValues, _), ExpressionKind.EArray(rValues, _)) => compareExprArray(lValues, rValues)
        case (ExpressionKind.EByteArray(lValues), ExpressionKind.EByteArray(rValues)) => compareExprArray(lValues, rValues)
        case (ExpressionKind.EIntArray(lValues), ExpressionKind.EIntArray(rValues)) => compareExprArray(lValues, rValues)
        case (ExpressionKind.ELongArray(lValues), ExpressionKind.ELongArray(rValues)) => compareExprArray(lValues, rValues)
        case (ExpressionKind.ECompound(lValues), ExpressionKind.ECompound(rValues)) =>
          if lValues.size != rValues.size then
            Some(false)
          else
            lValues.iterator.foldLeft(Option(true)): 
              case (Some(false), _) => Some(false)
              case (equals, (key, a)) =>
                rValues.get(key) match
                  case Some(b) =>
                    a.valueEqual(b) match
                      case Some(true) => equals
                      case it => it
                  case None =>
                    Some(false)
        case (ExpressionKind.EScoreboard(_), other) if !other.nbtType.numeric => Some(false)
        case (other, ExpressionKind.EScoreboard(_)) if !other.nbtType.numeric => Some(false)
        case (ExpressionKind.EStorage(_), _)
             | (_, ExpressionKind.EStorage(_))
             | (ExpressionKind.EScoreboard(_), _)
             | (_, ExpressionKind.EScoreboard(_))
             | (ExpressionKind.ECondition(_), _)
             | (_, ExpressionKind.ECondition(_))
             | (ExpressionKind.EEntity(_, _), _)
             | (_, ExpressionKind.EEntity(_, _))
             | (ExpressionKind.EBlock(_, _), _)
             | (_, ExpressionKind.EBlock(_, _)) => None
        case _ => Some(false)

    def toData(compiler: Compiler, code: mutable.ArrayBuffer[String], data: DataKind, operation: String, dataType: NbtType, namespace: String): Unit throws CompileError =
      kind.toComptimeString(false) match
        case Some(v) =>
          code.append(mcfunc"data modify $data ${operation} value ${v}")
        case None => 
          val (conversionCode, kind2) =
            kind match
              case ExpressionKind.EVoid => throw CompileError.nonfatal(location, "Can't store void in storage")
              case ExpressionKind.EByte(_)
                  | ExpressionKind.EShort(_)
                  | ExpressionKind.EInteger(_)
                  | ExpressionKind.ELong(_)
                  | ExpressionKind.EFloat(_)
                  | ExpressionKind.EDouble(_)
                  | ExpressionKind.EBoolean(_)
                  | ExpressionKind.EString(_) => throw InternalError(location, "INTERNAL ERROR: This value should have a compile time string representation")
              case ExpressionKind.EArray(values, nbtType) => return arrayToStorage(values, "", compiler, code, data, nbtType, namespace)
              case ExpressionKind.EByteArray(values) => return arrayToStorage(values, "B; ", compiler, code, data, NbtType.Byte, namespace)
              case ExpressionKind.EIntArray(values) => return arrayToStorage(values, "I; ", compiler, code, data, NbtType.Int, namespace)
              case ExpressionKind.ELongArray(values) => return arrayToStorage(values, "L; ", compiler, code, data, NbtType.Long, namespace)
              case ExpressionKind.ECompound(values) => return compoundToStorage(values, compiler, code, data, namespace)
              case ExpressionKind.EStorage(loc) =>
                (mcfunc"from storage ${loc}", StorageKind.Modify)
              case ExpressionKind.EEntity(selector, path) =>
                (s"from entity $selector $path", StorageKind.Modify)
              case ExpressionKind.EBlock((x, y, z), path) =>
                (mcfunc"from block $x $y $z $path", StorageKind.Modify)
              case ExpressionKind.ESubString(loc, start, end) =>
                (mcfunc"string storage ${loc} ${start}${if end.nonEmpty then " " + end.get.toString else ""}", StorageKind.Modify)
              case ExpressionKind.EScoreboard(loc) =>
                (mcfunc"scoreboard players get ${loc}", StorageKind.Store)
              case ExpressionKind.EMacro(loc) =>
                (mcfunc"value $$(${loc.name})", StorageKind.MacroModify)
              case ExpressionKind.ECondition(cond) =>
                cond.compile(compiler, code, namespace, false) match
                  case EvaluatedCondition.Check(c) =>
                    (s"execute ${c}", StorageKind.Store)
                  case EvaluatedCondition.Known(v) =>
                    (s"value $v", StorageKind.Modify)

          val kind3 =
            (kind2, needsMacro) match
              case (StorageKind.Modify, true) => StorageKind.MacroModify
              case (StorageKind.Store, true) => StorageKind.MacroStore
              case _ => kind2
          val storeType = dataType.storeString.getOrElse("int")
          kind3 match
            case StorageKind.Modify =>
              code.append(mcfunc"data modify $data ${operation} ${conversionCode}")
            case StorageKind.MacroModify =>
              code.append(mcfunc"$$data modify $data ${operation} ${conversionCode}")
            case StorageKind.Store =>
              if operation == "set" then
                code.append(mcfunc"execute store result $data ${storeType} 1 run ${conversionCode}")
              else
                val tempStorage = compiler.nextStorage(namespace)
                code.append(
                  mcfunc"execute store result storage ${tempStorage} ${storeType} 1 run ${conversionCode}"
                )
                code.append(
                  mcfunc"data modify $data ${operation} from storage ${tempStorage}"
                )
            case StorageKind.MacroStore =>
              if operation == "set" then
                code.append(mcfunc"$$execute store result $data ${storeType} 1 run ${conversionCode}")
              else
                val tempStorage = compiler.nextStorage(namespace)
                code.append(
                  mcfunc"$$execute store result storage ${tempStorage} ${storeType} 1 run ${conversionCode}"
                )
                code.append(
                  mcfunc"data modify storage $data ${operation} from storage ${tempStorage}"
                )

    def toStorage(compiler: Compiler, code: mutable.ArrayBuffer[String], storage: StorageLocation, operation: String, dataType: NbtType): Unit throws CompileError =
      toData(compiler, code, DataKind.Storage(storage), operation, dataType, storage.storage.namespace)
        


    def toReturnCommand(compiler: Compiler, code: mutable.ArrayBuffer[String], namespace: String): String throws CompileError =
      this.kind match
        case ExpressionKind.EVoid => throw CompileError.nonfatal(location, "Cannot return void")
        case ExpressionKind.Numeric(n) => s"return $n"
        case ExpressionKind.EBoolean(b) =>
          if b then "return 1" else "return 0"
        case ExpressionKind.EString(_)
            | ExpressionKind.ESubString(_, _, _)
            | ExpressionKind.EArray(_, _)
            | ExpressionKind.EByteArray(_)
            | ExpressionKind.EIntArray(_)
            | ExpressionKind.ELongArray(_)
            | ExpressionKind.ECompound(_) => throw CompileError.nonfatal(location, "Can only directly return numeric values")
        case ExpressionKind.EStorage(storage) =>
          mcfunc"return run data get storage ${storage}"
        case ExpressionKind.EScoreboard(scoreboard) =>
          mcfunc"return run scoreboard players get ${scoreboard}"
        case ExpressionKind.EMacro(name) =>
          mcfunc"$$return $$(${name})"
        case ExpressionKind.ECondition(condition) =>
          condition.compile(compiler, code, namespace, false) match
            case EvaluatedCondition.Check(c) => s"return run execute ${c}"
            case EvaluatedCondition.Known(v) => if v then "return 1" else "return 0"
        case _ =>
          // unreachable
          throw InternalError(location, "Unreachable")


    def toScore(compiler: Compiler, code: mutable.ArrayBuffer[String], namespace: String): (String, ScoreKind) throws CompileError =
      kind match
        case ExpressionKind.EVoid => throw CompileError.nonfatal(location, "Cannot assign void to a value")
        case ExpressionKind.EByte(b) => (b.toString, ScoreKind.Direct("set"))
        case ExpressionKind.EShort(s) => (s.toString, ScoreKind.Direct("set"))
        case ExpressionKind.EInteger(i) => (i.toString, ScoreKind.Direct("set"))
        case ExpressionKind.ELong(l) => (l.toString, ScoreKind.Direct("set"))
        case ExpressionKind.EFloat(f) => (f.floor.toInt.toString, ScoreKind.Direct("set"))
        case ExpressionKind.EDouble(d) => (d.floor.toInt.toString, ScoreKind.Direct("set"))
        case ExpressionKind.EBoolean(b) => (if b then "1" else "0", ScoreKind.Direct("set"))
        case ExpressionKind.EString(_) | ExpressionKind.ESubString(_, _, _) => throw CompileError.nonfatal(location, "Cannot assign string to scoreboard")
        case ExpressionKind.EArray(_, _) => throw CompileError.nonfatal(location, "Cannot assign array to scoreboard")
        case ExpressionKind.EByteArray(_) => throw CompileError.nonfatal(location, "Cannot assign array to scoreboard")
        case ExpressionKind.EIntArray(_) => throw CompileError.nonfatal(location, "Cannot assign array to scoreboard")
        case ExpressionKind.ELongArray(_) => throw CompileError.nonfatal(location, "Cannot assign array to scoreboard")
        case ExpressionKind.ECompound(_) => throw CompileError.nonfatal(location, "Cannot assign compound to scoreboard")
        case ExpressionKind.EStorage(loc) => (mcfunc"data get storage $loc", ScoreKind.Indirect)
        case ExpressionKind.EEntity(selector, path) => (s"data get entity $selector $path", ScoreKind.Indirect)
        case ExpressionKind.EBlock((x, y, z), path) => (mcfunc"data get block $x $y $z $path", ScoreKind.Indirect)
        case ExpressionKind.EScoreboard(loc) => (mcfunc"= $loc", ScoreKind.Direct("operation"))
        case ExpressionKind.EMacro(loc) => (s"$$(${loc.name})", ScoreKind.DirectMacro("set"))
        case ExpressionKind.ECondition(cond) =>
          cond.compile(compiler, code, namespace, false) match
            case EvaluatedCondition.Check(c) => (s"execute $c", ScoreKind.Indirect)
            case EvaluatedCondition.Known(b) => (if b then "1" else "0", ScoreKind.Direct("set"))


    def toCondition(compiler: Compiler, code: mutable.ArrayBuffer[String], namespace: String): Condition throws CompileError =
      kind match
        case ExpressionKind.EVoid => throw CompileError.nonfatal(location, "Can't check void")
        case ExpressionKind.EByte(b) => Condition.Known(b != 0)
        case ExpressionKind.EShort(s) => Condition.Known(s != 0)
        case ExpressionKind.EInteger(i) => Condition.Known(i != 0)
        case ExpressionKind.ELong(l) => Condition.Known(l != 0)
        case ExpressionKind.EFloat(f) => Condition.Known(f != 0)
        case ExpressionKind.EDouble(d) => Condition.Known(d != 0)
        case ExpressionKind.EBoolean(b) => Condition.Known(b)
        case ExpressionKind.EString(_) => throw CompileError.nonfatal(location, "Can't use string as condition")
        case ExpressionKind.EArray(_, _) => throw CompileError.nonfatal(location, "Can't use array as condition")
        case ExpressionKind.EByteArray(_) => throw CompileError.nonfatal(location, "Can't use array as condition")
        case ExpressionKind.EIntArray(_) => throw CompileError.nonfatal(location, "Can't use array as condition")
        case ExpressionKind.ELongArray(_) => throw CompileError.nonfatal(location, "Can't use array as condition")
        case ExpressionKind.ECompound(_) => throw CompileError.nonfatal(location, "Can't use compound as condition")
        case ExpressionKind.EStorage(_) | ExpressionKind.EMacro(_) | ExpressionKind.EEntity(_, _) | ExpressionKind.EBlock(_, _) =>
          val scoreboard = compiler.copyToScoreboard(code, this, namespace)
          Condition.Truthy(scoreboard)
        case ExpressionKind.ESubString(_, _, _) => throw CompileError.nonfatal(location, "Can't use string as condition")
        case ExpressionKind.EScoreboard(loc) =>
          Condition.Truthy(loc)
        case ExpressionKind.ECondition(cond) => cond




  case class NumericComparison(
                              operator: (ScoreboardLocation, ScoreboardLocation) => Condition,
                              halfOperator: (ScoreboardLocation, Int) => Condition,
                              constOp: (Int, Int) => Boolean,
                              inverse: () => NumericComparison
                              )
  object NumericComparison:
    lazy val less: NumericComparison =
      NumericComparison(Condition.Less.apply, (scoreboard, value) => Condition.Match(scoreboard, MatchRange.Range(None, Some(value - 1))), _ < _, () => greater)
    lazy val lessEq: NumericComparison =
      NumericComparison(Condition.LessEq.apply, (scoreboard, value) => Condition.Match(scoreboard, MatchRange.Range(None, Some(value))),_ <= _, () => greaterEq)
    lazy val greater: NumericComparison =
      NumericComparison(Condition.Greater.apply, (scoreboard, value) => Condition.Match(scoreboard, MatchRange.Range(Some(value + 1), None)) ,_ > _, () => less)
    lazy val greaterEq: NumericComparison =
      NumericComparison(Condition.GreaterEq.apply, (scoreboard, value) => Condition.Match(scoreboard, MatchRange.Range(Some(value), None)),_ >= _, () => lessEq)

  enum NbtType(val numeric: Boolean, val storeString: Option[String] = None):
    case Unknown extends NbtType(false)
    case Numeric extends NbtType(true)
    case Byte extends NbtType(true, Some("byte"))
    case Short extends NbtType(true, Some("short"))
    case Int extends NbtType(true, Some("int"))
    case Long extends NbtType(true, Some("long"))
    case Float extends NbtType(true, Some("float"))
    case Double extends NbtType(true, Some("double"))
    case ByteArray extends NbtType(false)
    case IntArray extends NbtType(false)
    case LongArray extends NbtType(false)
    case String extends NbtType(false)
    case List extends NbtType(false)
    case Compound extends NbtType(false)


  enum ScoreboardOperation(val operator: String, val nativeOperator: Option[String], val constantOp: (Int, Int) => Int, val binopKind: parser.ast.BinopKind, val commutative: Boolean):
    import parser.ast.BinopKind.*
    case Add extends ScoreboardOperation("+", Some("add"), _ + _, BinopKind.Plus, true)
    case Sub extends ScoreboardOperation("-", Some("remove"), _ - _, BinopKind.Minus, false)
    case Mul extends ScoreboardOperation("*", None, _ * _, BinopKind.Times, true)
    case Div extends ScoreboardOperation("/", None, _ / _, BinopKind.Divide, false)
    // scala is java based so im just going to assume that modulo here has the same semantics
    case Mod extends ScoreboardOperation("%", None, _ % _, BinopKind.Modulo, false)

  object ExpressionKind:
    object Numeric:
      def unapply(kind: ExpressionKind): Option[Int] =
        kind.numericValue

  private def compareExprArray(lValues: List[Expression], rValues: List[Expression]): Option[Boolean] =
    if lValues.lengthCompare(rValues) != 0 then
      Some(false)
    else
      lValues.zip(rValues).foldLeft(Option(true)): 
        case (Some(false), _) => Some(false)
        case (equals, (a, b)) =>
        a.valueEqual(b) match
          case Some(true) => equals
          case Some(false) => Some(false)
          case None => None


  def displayConstant(c: Int): String =
    if c < 0 then
      s"neg${c.abs}"
    else
      c.toString

  private def arrayToString(values: List[Expression], prefix: String): Option[String] =
    val valueStrings = values.traverse(_.kind.toComptimeString(false))
    valueStrings.map: it =>
      it.mkString(s"[$prefix",",","]")

  private def arrayToStorage(
    elements: List[Expression],
    prefix: String,
    compiler: Compiler,
    code: mutable.ArrayBuffer[String],
    data: DataKind,
    dataType: NbtType,
    namespace: String,
  ): Unit throws CompileError =
    val constantElements = mutable.ArrayBuffer[String]()
    val computedElementsCode = mutable.ArrayBuffer[String]()
    elements.zipWithIndex.foreach: (expr, i)  =>
      expr.kind.toComptimeString(false) match
        case Some(value) =>
          constantElements.append(value)
        case _ =>
          expr.toData(compiler, code, data, s"insert $i", dataType, namespace)
    // TODO: sus
    code.append(mcfunc"data modify $data set value [${prefix}${constantElements.mkString(", ")}]")
    code.appendAll(computedElementsCode)

  private def compoundToStorage(
    elements: Map[String, Expression],
    compiler: Compiler,
    code: mutable.ArrayBuffer[String],
    data: DataKind,
    namespace: String
  ): Unit throws CompileError =
    val constantElements = mutable.ArrayBuffer[String]()
    val computedElementsCode = mutable.ArrayBuffer[String]()

    elements.foreach: (key, value) =>
      value.kind.toComptimeString(false) match
        case Some(value) =>
          constantElements.append(s"$key: $value")
        case _ =>
          val elementLocation = data.subPath(key)
          value.toData(
            compiler,
            computedElementsCode,
            elementLocation,
            "set",
            NbtType.Unknown,
            namespace
          )
    code.append(
      mcfunc"data modify $data set value {${constantElements.mkString(", ")}}"
    )
    code.appendAll(computedElementsCode)

  enum ExpressionKind:
    case EVoid
    case EByte(b: Byte)
    case EShort(s: Short)
    case EInteger(i: Int)
    case ELong(l: Long)
    case EFloat(f: Float)
    case EDouble(d: Double)
    case EBoolean(b: Boolean)
    case EString(s: String)
    case EArray(values: List[Expression], valuesType: NbtType)
    case EByteArray(values: List[Expression])
    case EIntArray(values: List[Expression])
    case ELongArray(values: List[Expression])
    case ECompound(values: Map[String, Expression])
    case EStorage(loc: StorageLocation)
    case EEntity(selector: String, path: String)
    case EBlock(pos: (BlockCoord, BlockCoord, BlockCoord), path: String)
    case ESubString(loc: StorageLocation, start: Int, end: Option[Int])
    case EScoreboard(loc: ScoreboardLocation)
    case EMacro(loc: StorageLocation)
    case ECondition(cond: Compiler.Condition)

      

    def nbtType: NbtType =
      this match
        case ExpressionKind.EVoid => NbtType.Unknown
        case ExpressionKind.EByte(_) => NbtType.Byte
        case ExpressionKind.EShort(_) => NbtType.Short
        case ExpressionKind.EInteger(_) => NbtType.Int
        case ExpressionKind.ELong(_) => NbtType.Long
        case ExpressionKind.EFloat(_) => NbtType.Float
        case ExpressionKind.EDouble(_) => NbtType.Double
        case ExpressionKind.EBoolean(_) => NbtType.Byte
        case ExpressionKind.EString(_) => NbtType.String
        case ExpressionKind.EArray(_, _) => NbtType.List
        case ExpressionKind.EByteArray(_) => NbtType.ByteArray
        case ExpressionKind.EIntArray(_) => NbtType.IntArray
        case ExpressionKind.ELongArray(_) => NbtType.LongArray
        case ExpressionKind.ECompound(_) => NbtType.Compound
        case ExpressionKind.EStorage(_) => NbtType.Unknown
        case ExpressionKind.EEntity(_, _) => NbtType.Unknown
        case ExpressionKind.EBlock(_, _) => NbtType.Unknown
        case ExpressionKind.ESubString(_, _, _) => NbtType.String
        case ExpressionKind.EScoreboard(_) => NbtType.Numeric
        case ExpressionKind.EMacro(_) => NbtType.Unknown
        case ExpressionKind.ECondition(_) => NbtType.Byte

    def numericValue: Option[Int] =
      this match
        case ExpressionKind.EByte(b) => Some(b.toInt)
        case ExpressionKind.EShort(s) => Some(s.toInt)
        case ExpressionKind.EInteger(i) => Some(i)
        case ExpressionKind.ELong(l) => Some(l.toInt)
        case ExpressionKind.EFloat(f) => Some(f.floor.toInt)
        case ExpressionKind.EDouble(d) => Some(d.floor.toInt)
        case _ => None

    def toComptimeString(topLevel: Boolean): Option[String] =
      this match
        case ExpressionKind.EVoid => None
        case ExpressionKind.EByte(b) => Some(s"${b}b")
        case ExpressionKind.EShort(s) => Some(s"${s}s")
        case ExpressionKind.EInteger(i) => Some(i.toString)
        case ExpressionKind.ELong(l) => Some(s"${l}l")
        case ExpressionKind.EFloat(f) => Some(s"${f}f")
        case ExpressionKind.EDouble(d) => Some(s"${d}d")
        case ExpressionKind.EBoolean(b) => Some(b.toString)
        case ExpressionKind.EString(s) =>
          if topLevel then
            Some(s)
          else
            Some("\"" + util.StringEscape.escaped(s) + "\"")
        case ExpressionKind.EArray(values, _) => arrayToString(values, "")
        case ExpressionKind.EByteArray(values) => arrayToString(values, "B; ")
        case ExpressionKind.EIntArray(values) => arrayToString(values, "I; ")
        case ExpressionKind.ELongArray(values) => arrayToString(values, "L; ")
        case ExpressionKind.ECompound(values) =>
          values.toList.traverse: (key, value) =>
            value.kind.toComptimeString(false).map: it => 
              if !key.head.isDigit && key.forall(c => c.isLetterOrDigit || c == '_') then
                s"$key: $it"
              else
                val esc = util.StringEscape.escaped(key)
                s"\"$esc\": $it"
          .map: valueStrings =>
            valueStrings.mkString("{", ", ", "}")
        case ExpressionKind.EStorage(loc) =>
          if topLevel then
            Some(loc.mcdisplay)
          else None
        case ExpressionKind.EEntity(selector, path) => None
        case ExpressionKind.EBlock(pos, path) => None
        case ExpressionKind.ESubString(loc, start, end) => None
        case ExpressionKind.EScoreboard(loc) =>
          if topLevel then
            Some(loc.mcdisplay)
          else None
        case ExpressionKind.EMacro(loc) => None
        case ExpressionKind.ECondition(cond) =>
          cond.compileFlat(false) match
            case Some(EvaluatedCondition.Known(v)) => Some(if v then "1b" else "0b")
            case _ => None

  enum PositionMode:
    case Absolute, Relative, Caret

    def prefix: String =
      this match
        case PositionMode.Absolute => ""
        case PositionMode.Relative => "~"
        case PositionMode.Caret => "^"
 
  object exprUnapply:
    // TODO: selector?
    object Identifier:
      def unapply(it: ast.Expr): Option[String] =
        it match
          case Expr.ZVariable(_, path) if path.namespace.isEmpty && path.modules.isEmpty => Some(path.name)
          case _ => None
    object ResourcePath:
      def unapply(it: ast.Expr)(using context: FuncContext): Option[ResourceLocation] =
        it match
          case Expr.ZVariable(_, path) =>
            Some(ResourceLocation.resolveResource(context.location, path))
          case _ => None
    object ScoreboardPath:
      def unapply(it: ast.Expr)(using context: FuncContext): Option[ScoreboardLocation] =
        it match
          case Expr.ZScoreboardVariable(_, path) =>
            Some(ScoreboardLocation.resolveResource(context.location, path))
          case _ => None
    object StoragePath:
      // can't believe this shit actually works
      // This one is used in the main compiler, so any additions here will match
      def unapply(it: ast.Expr)(using context: FuncContext): Option[(util.Location, StorageLocation)] =
        it match
          case Expr.ZVariable(pos, path) =>
            Some((pos, StorageLocation.resolveResource(context.location, path)))
          case Expr.ZBuiltinCall(pos, ast.BuiltinCall("storage", StoragePath(storage))) =>
            Some((pos, storage))
          case _ => None
      def unapply(it: List[BuiltinArg])(using context: FuncContext): Option[StorageLocation] =
        it match
          case List(BuiltinArg.BExpr(_, ResourcePath(path)), BuiltinArg.BExpr(_, Expr.ZString(_, nbtPath))) =>
            Some(StorageLocation(path, nbtPath))
          case List(BuiltinArg.BExpr(_, ResourcePath(path))) =>
            Some(StorageLocation(path, ""))
          case _ => None

    object EntityStorage:
      def unapply(it: ast.Expr): Option[(util.Location, String, String)] =
        it match
          case Expr.ZBuiltinCall(pos, ast.BuiltinCall("entity", args)) =>
            args match
              case EntityStorage(selector, path) =>
                Some((pos, selector, path))
              case _ => None
          case _ => None
      def unapply(args: List[BuiltinArg]): Option[(String, String)] =
        args match
          case List(BuiltinArg.BExpr(_, Expr.ZString(_, selector)), BuiltinArg.BExpr(_, Expr.ZString(_, path))) =>
            Some((selector, path))
          case List(BuiltinArg.BExpr(_, Expr.ZString(_, selector))) =>
            Some((selector, ""))
          case _ => None
    object BlockEntityStorage:
      def unapply(it: ast.Expr): Option[(util.Location, (BlockCoord, BlockCoord, BlockCoord), String)] =
        it match
          case Expr.ZBuiltinCall(pos, ast.BuiltinCall("block_entity", BlockEntityStorage(blockPos, path))) =>
            Some((pos, blockPos, path))
          case _ => None

      def unapply(args: List[BuiltinArg]): Option[((BlockCoord, BlockCoord, BlockCoord), String)] =
        args match
          case List(BuiltinArg.BExpr(_, BlockCoord(x)), BuiltinArg.BExpr(_, BlockCoord(y)), BuiltinArg.BExpr(_, BlockCoord(z)), BuiltinArg.BExpr(_, Expr.ZString(_, path))) =>
            Some(((x, y, z), path))
          case List(BuiltinArg.BExpr(_, BlockCoord(x)), BuiltinArg.BExpr(_, BlockCoord(y)), BuiltinArg.BExpr(_, BlockCoord(z))) =>
            Some(((x, y, z), ""))
          case _ => None
    object BossbarStore:
      def unapply(args: List[BuiltinArg])(using FuncContext): Option[(ResourceLocation, String)] =
        args match
          case List(BuiltinArg.BExpr(_, ResourcePath(bossbarId)), BuiltinArg.BExpr(_, Identifier(maxOrValue))) =>
            Some((bossbarId, maxOrValue))
          case _ => None
      def unapply(it: ast.Expr)(using FuncContext): Option[(ResourceLocation, String)] =
        it match
          case Expr.ZBuiltinCall(pos, ast.BuiltinCall("bossbar", BossbarStore(bossbarId, maxOrValue))) =>
            Some((bossbarId, maxOrValue))
          case _ => None
    object IntegralExpr:
      def unapply(it: ast.Expr): Option[Int] =
        it match
          case Expr.ZByte(_, b) => Some(b.toInt)
          case Expr.ZShort(_, s) => Some(s.toInt)
          case Expr.ZInt(_, i) => Some(i.toInt)
          case Expr.ZLong(_, l) => Some(l.toInt)
          case Expr.Unary(_, UnaryKind.Negate, IntegralExpr(value)) => Some(-value)
          case _ => None
    object NumericExpr:
      def unapply(it: ast.Expr): Option[Double] =
        it match
          case Expr.ZByte(_, b) => Some(b.toDouble)
          case Expr.ZShort(_, s) => Some(s.toDouble)
          case Expr.ZInt(_, i) => Some(i.toDouble)
          case Expr.ZLong(_, l) => Some(l.toDouble)
          case Expr.ZFloat(_, f) => Some(f.toDouble)
          case Expr.ZDouble(_, d) => Some(d)
          case Expr.Unary(_, UnaryKind.Negate, NumericExpr(value)) => Some(-value)
          case _ => None


  case class CommandCoord(pos: Double, mode: PositionMode)
  object CommandCoord:
    import exprUnapply.*
    def unapply(it: ast.Expr): Option[CommandCoord] =
      it match
        case Expr.Unary(_, UnaryKind.Tilde, NumericExpr(value)) =>
          Some(CommandCoord(value, PositionMode.Relative))
        case Expr.Unary(_, UnaryKind.Caret, NumericExpr(value)) =>
          Some(CommandCoord(value, PositionMode.Caret))
        case NumericExpr(value) =>
          Some(CommandCoord(value, PositionMode.Absolute))
        case _ => None
  case class BlockCoord(pos: Int, mode: PositionMode)
  object BlockCoord:
    import exprUnapply.*
    def unapply(arg: ast.Expr): Option[BlockCoord] =
      arg match
        case Expr.Unary(_, UnaryKind.Tilde, IntegralExpr(value)) =>
          Some(BlockCoord(value, PositionMode.Relative))
        case Expr.Unary(_, UnaryKind.Caret, IntegralExpr(value)) =>
          Some(BlockCoord(value, PositionMode.Caret))
        case IntegralExpr(value) =>
          Some(BlockCoord(value, PositionMode.Absolute))
        case _ => None
    def unapply(builtin: BuiltinArg): Option[BlockCoord] =
      builtin match
        case BuiltinArg.BExpr(_, BlockCoord(x)) => Some(x)
        case _ => None

  given MCFunctionDisplay[CommandCoord] = x =>
    s"${x.mode.prefix}${x.pos}"
  given MCFunctionDisplay[BlockCoord] = x =>
    s"${x.mode.prefix}${x.pos}"

  def chainExecuteCommand(rootCommand: String, childCommand: String): String =
    if childCommand.startsWith("execute ") then
      s"$rootCommand ${childCommand.substring(8)}"
    else if childCommand.startsWith("$execute ") then
      s"$$$rootCommand run ${childCommand.substring(9)}"
    else if childCommand.startsWith("$") then
      s"$$$rootCommand run ${childCommand.tail}"
    else
      s"$rootCommand run $childCommand"
  
  def chainExecuteInstruction(prefixInstruction: String, childCommand: String): String =
    chainExecuteCommand(s"execute $prefixInstruction", childCommand)

  object builtinExecute:
    import exprUnapply.*
    case class BuiltinExecuteComponent(name: String, run: (Compiler, util.Location, List[BuiltinArg]) => FuncContext ?=> String throws CompileError)
    object BuiltinExecuteComponent:
      def make(name: String)(run: (Compiler, util.Location, List[BuiltinArg]) => FuncContext ?=> String throws CompileError): BuiltinExecuteComponent =
        BuiltinExecuteComponent(name, run)

    
    object BuiltinRotation:
      def unapply(it: BuiltinArg): Option[CommandCoord] =
        it match
          case BuiltinArg.BExpr(_, CommandCoord(rot)) if rot.mode != PositionMode.Caret =>
            Some(rot)
          case _ => None


    object BuiltinVec3:
      def unapply(it: BuiltinArg): Option[(CommandCoord, CommandCoord, CommandCoord)] =
        it match
          case BuiltinArg.BExpr(_, Expr.ZList(_, ast.ArrayKind.Any, List(CommandCoord(x), CommandCoord(y), CommandCoord(z)))) =>
            Some((x, y, z))
          case _ => None
      def unapply(it: List[BuiltinArg]): Option[(CommandCoord, CommandCoord, CommandCoord)] =
        it match
          case List(BuiltinArg.BExpr(_, CommandCoord(x)), BuiltinArg.BExpr(_, CommandCoord(y)), BuiltinArg.BExpr(_, CommandCoord(z))) =>
            Some((x, y, z))
          case _ => None

    def handleStore(compiler: Compiler, pos: util.Location, args: List[BuiltinArg])(using context: FuncContext): String throws CompileError =
      args match
        case List(BuiltinArg.BExpr(subPos, BossbarStore(bossbarId, maxOrValue))) =>
          maxOrValue match
            case "max" | "value" => ()
            case _ =>
              compiler.report.nonfatal:
                CompileError.nonfatal(subPos, "Expected 'max' or 'value'")
          mcfunc"bossbar $bossbarId $maxOrValue"
        case List(BuiltinArg.BExpr(_, ScoreboardPath(score))) =>
          // store in scoreboard
          mcfunc"score $score"
          
        
        case List(BuiltinArg.BExpr(_, expr),
                  BuiltinArg.BExpr(_, Identifier(kind)),
                  BuiltinArg.BExpr(_, NumericExpr(scale))) =>
                    val assignTarget = compiler.compileAssignTarget(expr)
                    assignTarget match
                      case AssignTarget.Data(dataKind) =>
                        mcfunc"$dataKind $kind ${scale.toString}"
                      case _ =>
                        throw InternalError(pos, "Scoreboard case should have been handled already")

        case _ =>
          throw CompileError.nonfatal(pos, "Invalid store arguments")



    object Anchor:
      def unapply(it: BuiltinArg): Option[String] =
        it match
          case BuiltinArg.BExpr(_, Expr.ZString(_, str)) if str == "eyes" || str == "feet" => Some(str)
          case _ => None
    val components: Map[String, BuiltinExecuteComponent] =
      List[BuiltinExecuteComponent](
        BuiltinExecuteComponent.make("as") { (_, pos, args) => context ?=>
          args match
            case List(BuiltinArg.BExpr(_, Expr.ZString(_, selector))) =>
              s"as $selector"
            case _ =>
              throw CompileError.nonfatal(pos, "Expected a selector")
        },
        BuiltinExecuteComponent.make("at") { (_, pos, args) => context ?=> 
          args match
            case List(BuiltinArg.BExpr(_, Expr.ZString(_, selector))) =>
              s"at $selector"
            case _ =>
              throw CompileError.nonfatal(pos, "Expected a selector")
        },
        BuiltinExecuteComponent.make("align") { (_, pos, args) => context ?=> 
          args match
            case List(BuiltinArg.BExpr(_, Expr.ZString(_, axes))) =>
              s"align $axes"
            case _ =>
              throw CompileError.nonfatal(pos, "Expected string with axes")
        },
        BuiltinExecuteComponent.make("anchored") { (_, pos, args) => context ?=>
          args match
            case List(Anchor(str)) =>
              s"anchored $str"
            case _ =>
              throw CompileError.nonfatal(pos, "Expected 'feet' or 'eyes'")
        },
        BuiltinExecuteComponent.make("facing") { (_, pos, args) => context ?=> 
          args match
            case BuiltinVec3(x, y, z) =>
              mcfunc"facing $x $y $z"
            case List(BuiltinArg.BExpr(_, Expr.ZString(_, selector)), Anchor(str)) =>
              s"facing entity $selector $str"
            case _ =>
              throw CompileError.nonfatal(pos, "Expected either a position, or a selector and an anchor.")
        },
        BuiltinExecuteComponent.make("in") { (_, pos, args) => context ?=>
          args match
            case List(BuiltinArg.BExpr(_, Expr.ZString(_, dimension))) =>
              s"in $dimension"
            case _ =>
              throw CompileError.nonfatal(pos, "Expected string with dimension identifier")
        },
        BuiltinExecuteComponent.make("on") { (_, pos, args) => context ?=> 
          args match
            case List(BuiltinArg.BExpr(_, Expr.ZString(_, relation))) =>
              s"on $relation"
            case _ =>
              throw CompileError.nonfatal(pos, "Expected relation string")
        },
        BuiltinExecuteComponent.make("positioned") { (_, pos, args) => context ?=>
          args match
            case List(BuiltinArg.BExpr(_, Expr.ZString(_, selector))) =>
              s"positioned as $selector"
            case BuiltinVec3(x, y, z) =>
              mcfunc"positioned $x $y $z"
            case _ =>
              throw CompileError.nonfatal(pos, "Expected selector or position")
        },
        BuiltinExecuteComponent.make("rotated") { (_, pos, args) => context ?=>
          args match
            case List(BuiltinArg.BExpr(_, Expr.ZString(_, selector))) =>
              s"rotated as $selector"
            case List(BuiltinRotation(yaw), BuiltinRotation(pitch)) =>
              mcfunc"rotated $yaw $pitch"
            case _ =>
              throw CompileError.nonfatal(pos, "Expected selector or rotation")
        },
        BuiltinExecuteComponent.make("store_success") { (compiler, pos, args) => context ?=>
          val storeStr = handleStore(compiler, pos, args)
          s"store success $storeStr"
        },
        BuiltinExecuteComponent.make("store_result") { (compiler, pos, args) => context ?=>
          val storeStr = handleStore(compiler, pos, args)
          s"store result $storeStr"
        }
      ).map(it => (it.name, it)).toMap

    def compileFinalCommand(compiler: Compiler, pos: util.Location, arg: ast.BuiltinArg)(using context: FuncContext): String throws CompileError =
      arg match
        
        case BuiltinArg.BExpr(_, Expr.ZBuiltinCall(_, ast.BuiltinCall("inline", List(BuiltinArg.BExpr(_, Expr.ZFunctionCall(pos, call)))))) =>
          val (command, _) = compiler.compileFunctionCall(pos, call)
          command.mcdisplay
        case BuiltinArg.BExpr(_, Expr.ZBuiltinCall(callPos, ast.BuiltinCall(name, args))) =>
          components.get(name) match
            case Some(comp) =>
              if args.isEmpty then
                throw CompileError.nonfatal(callPos, "Expected arguments")
              val instruction = comp.run(compiler, pos, args.init)
              val finalCommand = compileFinalCommand(compiler, pos, args.last)
              chainExecuteInstruction(instruction, finalCommand)
            case None =>
              throw CompileError.nonfatal(callPos, "Expected @inline or a chained execute call")
        case BuiltinArg.BExpr(_, Expr.ZFunctionCall(pos, call)) =>
          if call.args.exists(_.executorSensitive) then
            compiler.report.warning:
              CompileError.nonfatal(pos, 
              Seq(
                "There's an argument to this function that is executor sensitive or could be changed between calls.",
                "To make the argument get evaluated for each call, use a block instead of an inline call.",
                "To surpress this warning, wrap the call in an @inline call."
              ))
          val (command, _) = compiler.compileFunctionCall(pos, call)
          command.mcdisplay
        case BuiltinArg.BBlock(pos, stmts) =>
          val func = compiler.nextFunction("execute", context.location.namespace)
          val subContext = context.nested(NestKind.Transparent, func, None)
          compiler.compileBlock(stmts)(using subContext)
          subContext.code.length match
            case 0 => throw CompileError.nonfatal(pos, "Block must have at least 1 output command")
            case 1 => subContext.code.head
            case _ =>
              compiler.addFunctionItem(util.Location.blank, func, subContext.code.toList)
              if subContext.hasMacroArgs then
                mcfunc"function $func with storage ${context.location}"
              else
                mcfunc"function $func"
        case _ =>
          throw CompileError.nonfatal(pos, "Expected block or function call")

  object builtinDefinitions:
    import exprUnapply.*
    def spawn(replace: Boolean)(compiler: Compiler, pos: util.Location, args: List[BuiltinArg])(using context: FuncContext): Expression throws CompileError =
      val (call, value, timeStr) =
        args match
          case List(BuiltinArg.BExpr(_, NumericExpr(value)), BuiltinArg.BExpr(_, Identifier(timeStr)), BuiltinArg.BExpr(_, Expr.ZFunctionCall(_, call))) =>
            (call, value, timeStr)
          case List(BuiltinArg.BExpr(_, Expr.ZString(strPos, str)), BuiltinArg.BExpr(_, Expr.ZFunctionCall(_, call))) =>
            val (num, unit) = (str.init, str.last)
            val goodNum = num.toDoubleOption.getOrElse(throw CompileError.nonfatal(strPos, "Expected string to be a number with a unit at the end (either s, t, or d)"))
            (call, goodNum, unit.toString)
          case List(BuiltinArg.BExpr(_, NumericExpr(value)), BuiltinArg.BExpr(_, Expr.ZFunctionCall(_, call))) =>
            (call, value, "t")
          case _ =>
            throw CompileError.nonfatal(pos, "Expected a number, optionally a unit of measurement, and a function call.")
      val timeType =
        timeStr match
          case "ticks" | "t" => ast.TimeType.Ticks
          case "seconds" | "s" => ast.TimeType.Seconds
          case "days" | "d" => ast.TimeType.Day
          case s =>
            compiler.report.nonfatal:
              CompileError.nonfatal(pos,
                s"Expected 'ticks', 't', 'seconds', 's', 'days', or 'd'. Got '$s'"
              )
            ast.TimeType.Ticks
      compiler.compileSpawnCall(pos, call, ast.Delay(util.Location.blank, value.toFloat, timeType), replace)
      Expression.void(pos)

    val all: Map[String, Builtin] =
      List[Builtin](
        Builtin.sideEffect("scoreboard") { (compiler, pos, args, location) => 
          val (score, criteria) =
            args match
              case List(BuiltinArg.BExpr(_, Expr.ZVariable(_, path))) =>
                (ResourceLocation.resolveResource(location, path), "dummy")
              case List(BuiltinArg.BExpr(_, Expr.ZVariable(_, path)), BuiltinArg.BExpr(_, Expr.ZString(_, crit))) =>
                (ResourceLocation.resolveResource(location, path), crit)
              case _ =>
                throw CompileError.nonfatal(pos, "Expected a path and optionally a criteria type.")
        
          compiler.useScoreboard(ScoreboardLocation.scoreboardStringOf(score), criteria)
        },
        Builtin.exprOnly("reset") { (_, pos, args) => context ?=>
          val (name, score) =
            args match
              case List(BuiltinArg.BExpr(_, Expr.ZString(_, name)), BuiltinArg.BExpr(_, ResourcePath(path))) =>
                (name, path)
              case List(BuiltinArg.BExpr(_, ScoreboardPath(score))) =>
                (score.name, score.scoreboard)
              case _ =>
                throw CompileError.nonfatal(pos, "Expected a name and a path")
          
          val scoreboardLoc = ScoreboardLocation(score, name)
          context.code.append(mcfunc"scoreboard players reset ${scoreboardLoc}")

          Expression.void(pos)
          
        },
        Builtin.exprOnly("enable") { (_, pos, args) => context ?=>
          val scoreboard =
            args match
              case List(BuiltinArg.BExpr(_, Expr.ZString(_, name)), BuiltinArg.BExpr(_, ResourcePath(score))) =>
                ScoreboardLocation(score, name)
              case List(BuiltinArg.BExpr(_, ScoreboardPath(score))) => score
              case _ =>
                throw CompileError.nonfatal(pos, "Expected a name and a path.")
          context.code.append(mcfunc"scoreboard players enable ${scoreboard}")
          Expression.void(pos)
        },
        Builtin.exprOnly("check") { (_, pos, args) => context ?=>
          args match
            case List(BuiltinArg.BExpr(_, Expr.ZString(_, checkCode))) =>
              Expression(pos, false, ExpressionKind.ECondition(Condition.Check(checkCode)))
            case _ =>
              throw CompileError.nonfatal(pos, "Expected check code (the bit that comes after `if` in execute commands)")
        },
        Builtin.exprOnly("is_block") { (_, pos, args) => context ?=>
          args match
            case List(BuiltinArg.BExpr(_, BlockCoord(x)), BuiltinArg.BExpr(_, BlockCoord(y)), BuiltinArg.BExpr(_, BlockCoord(z)), BuiltinArg.BExpr(_, Expr.ZString(_, blockPredicate))) =>
              Expression(pos, false, ExpressionKind.ECondition(Condition.Check(mcfunc"block $x $y $z $blockPredicate")))
            case _ =>
              throw CompileError.nonfatal(pos, "Expected block pos and block predicate")
        },
        Builtin.insertOnly("scoreboard_string") { (_, pos, args) => context ?=>
          args match
            case List(BuiltinArg.BExpr(_, ResourcePath(path))) =>
              ScoreboardLocation.scoreboardStringOf(path)
            case _ =>
              throw CompileError.nonfatal(pos, "Expected path")
        },
        Builtin.exprOnly("spawn")(spawn(true)),
        Builtin.exprOnly("spawn_append")(spawn(false)),
        Builtin.wrapComponent(builtinExecute.components("as")),
        Builtin.wrapComponent(builtinExecute.components("at")),
        Builtin.wrapComponent(builtinExecute.components("positioned")),
        Builtin.wrapComponent(builtinExecute.components("store_success")),
        Builtin.wrapComponent(builtinExecute.components("store_result")),
        Builtin.exprOnly("store_from") { (compiler, pos, args) => context ?=> 
          args match
            case Nil =>
              throw CompileError.nonfatal(pos, "Expected at least 1 argument")
            case _ =>
              val init = args.init
              val last = args.last
              val storeStr = builtinExecute.handleStore(compiler, pos, init)
              last match
                case BuiltinArg.BExpr(_, ScoreboardPath(score)) =>
                  context.code += mcfunc"execute store result $storeStr run scoreboard players get $score"
                case BuiltinArg.BExpr(_, StoragePath(_, storage)) =>
                  context.code += mcfunc"execute store result $storeStr run data get storage $storage"
                case _ =>
                  throw CompileError.nonfatal(pos, "TODO: make this more generic")
              Expression.void(pos)
              
        },
        Builtin.exprOnly("execute") { (compiler, pos, args) => context ?=> 
          args match
            case Nil =>
              throw CompileError.nonfatal(pos, "Expected at least 1 argument")
            case _ =>
              val inits = args.init
              val last = args.last
              val strs = inits.map:
                case BuiltinArg.BExpr(_, Expr.ZBuiltinCall(callPos, ast.BuiltinCall(name, args))) =>
                  builtinExecute.components.get(name) match
                    case Some(value) =>
                      value.run(compiler, callPos, args)
                    case None =>
                      compiler.report.nonfatal(CompileError.nonfatal(callPos, s"No such execute builtin $name"))
                      ""
                case _ =>
                  compiler.report.nonfatal(CompileError.nonfatal(pos, "Expected a builtin call for all but the last argument"))
                  ""
              val finalCommand = builtinExecute.compileFinalCommand(compiler, pos, last)
              
              val executeCommand = chainExecuteInstruction(strs.mkString(" "), finalCommand)
              context.code.append(executeCommand)
              Expression.void(pos)
        },
        Builtin.exprOnly("storage") { (_, pos, args) => context ?=>
          args match
            case StoragePath(path) =>
              Expression(pos, false, ExpressionKind.EStorage(path))
            case _ =>
              throw CompileError.nonfatal(pos, "Expected storage resource location and nbt path")
        },
        Builtin.exprOnly("entity") { (_, pos, args) => context ?=>
          args match
            case EntityStorage(selector, path) =>
              Expression(pos, false, ExpressionKind.EEntity(selector, path))
            case _ =>
              throw CompileError.nonfatal(pos, "Expected entity selector and nbt path")
        },
        Builtin.exprOnly("block_entity") { (_, pos, args) => context ?=>
          args match
            case BlockEntityStorage(blockPos, path) =>
              Expression(pos, false, ExpressionKind.EBlock(blockPos, path))
            case _ =>
              throw CompileError.nonfatal(pos, "Expected block position and nbt path")
        }
      ).map(it => (it.name, it)).toMap

  case class Builtin(name: String, 
                     exprFn: Option[(Compiler, util.Location, ast.BuiltinCall) => FuncContext ?=> Expression throws CompileError] = None,
                     insertFn: Option[(Compiler, util.Location, ast.BuiltinCall) => FuncContext ?=> String throws CompileError] = None,
                     declFn: Option[(Compiler, util.Location, ast.BuiltinCall, ResourceLocation) => Unit throws CompileError] = None):
    
    def expr(compiler: Compiler, pos: util.Location, call: ast.BuiltinCall)(using context: FuncContext): Expression throws CompileError =
      exprFn.getOrElse(throw CompileError.nonfatal(pos, s"The $name builtin doesn't work in expressions"))(compiler, pos, call)
    def inserted(compiler: Compiler, pos: util.Location, call: ast.BuiltinCall)(using context: FuncContext): String throws CompileError =
      insertFn.getOrElse(throw CompileError.nonfatal(pos, s"The $name builtin doesn't work in inserts"))(compiler, pos, call)
    def decl(compiler: Compiler, pos: util.Location, call: ast.BuiltinCall, location: ResourceLocation): Unit throws CompileError =
      declFn.getOrElse(throw CompileError.nonfatal(pos, s"The $name builtin doesn't work at toplevel"))(compiler, pos, call, location)

    def tryInlineExpression: Builtin =
      copy(
        insertFn =
          Some:
            (compiler, pos, call) =>
              exprFn match
                case Some(it) =>
                  val res = it(compiler, pos, call)
                  res.kind.toComptimeString(true).getOrElse(throw CompileError.nonfatal(pos, "Expression has no comptime representation"))
                case None =>
                  throw CompileError.nonfatal(pos, "This builtin has no expression function to inline")

            
      )

  object Builtin:
    def wrapComponent(child: builtinExecute.BuiltinExecuteComponent): Builtin =
      Builtin(
        child.name,
        exprFn =
          Some:
            (compiler, pos, call) => context ?=> {
              if call.args.isEmpty then
                throw CompileError.nonfatal(pos, "Expected arguments")
              else
                val instruction = child.run(compiler, pos, call.args.init)
                val finalCommand = builtinExecute.compileFinalCommand(compiler, pos, call.args.last)
                context.code += chainExecuteInstruction(instruction, finalCommand)
                Expression.void(pos)
            }
      )

    // Side effect that can be in Expr or Decl position
    def sideEffect(nameArg: String)(func: (Compiler, util.Location, List[ast.BuiltinArg],ResourceLocation) => Unit throws CompileError): Builtin =
      Builtin(
        nameArg,
        exprFn =
          Some:
            (compiler, pos, call) => context ?=>
              func(compiler, pos, call.args, context.location)
              Expression.void(pos),
        declFn =
          Some:
            (compiler, pos, call, location) =>
              func(compiler, pos, call.args, location)
      )

    def insertOnly(nameArg: String)(func: (Compiler, util.Location, List[ast.BuiltinArg]) => FuncContext ?=> String throws CompileError): Builtin =
      Builtin(
        nameArg,
        insertFn =
          Some:
            (compiler, pos, call) => context ?=>
              func(compiler, pos, call.args)
      )


    def exprOnly(nameArg: String)(func: (Compiler, util.Location, List[ast.BuiltinArg]) => FuncContext ?=> Expression throws CompileError): Builtin =
      Builtin(
        nameArg,
        exprFn =
          Some:
            (compiler, pos, call) =>
              func(compiler, pos, call.args)
      )

  enum ScoreKind:
    case Direct(operation: String)
    case DirectMacro(operation: String)
    case Indirect
    case IndirectMacro

  enum MatchRange:
    case Single(n: Int)
    case Range(min: Option[Int], max: Option[Int])

    def show: String = this match
      case MatchRange.Single(n) => n.toString
      case MatchRange.Range(min, max) => min.mkString("") + ".." + max.mkString("")

  // UNLIKE ZOGLIN, WE ARE NOT PUTTING STRINGS IN THIS SHIT UNLESS WE ABSOLUTELY HAVE TO
  // This can also represent Or and other things that require code to be generated
  // before the condition is actually evaluated
  enum Condition:
    case Less(left: ScoreboardLocation, right: ScoreboardLocation)
    case LessEq(left: ScoreboardLocation, right: ScoreboardLocation)
    case Greater(left: ScoreboardLocation, right: ScoreboardLocation)
    case GreaterEq(left: ScoreboardLocation, right: ScoreboardLocation)
    case Eq(left: ScoreboardLocation, right: ScoreboardLocation)
    case Match(score: ScoreboardLocation, range: MatchRange)
    // this should be `execute if {...} run` (only the {...} bit)
    // we NEVER include if or unless, and NEVER have more than one in here
    case Check(value: String)
    case Known(v: Boolean)
    case And(left: Condition, right: Condition)
    case Or(left: Condition, right: Condition)
    case Inverted(v: Condition)

    // Delay checking truthyness as long as possible, so we can optimize negated truthy checks
    case Truthy(score: ScoreboardLocation)

    // Does this always result in a single condition with no code edits, that can be safely combined together?
    def flat: Boolean =
      this match
        case Condition.And(_, _) | Condition.Or(_, _) => false
        case Condition.Inverted(x) => x.flat
        case _ => true

    def simplify: Condition =
      this match
        case Condition.And(l, r) =>
          val left = l.simplify
          val right = r.simplify
          (left, right) match
            case (Condition.Known(false), _) => Condition.Known(false)
            case (_, Condition.Known(false)) => Condition.Known(false)
            case (l, Condition.Known(true)) => l
            case (Condition.Known(true), l) => l
            case _ => Condition.And(left, right)
        case Condition.Or(l, r) =>
          val left = l.simplify
          val right = r.simplify
          (left, right) match
            case (Condition.Known(false), r) => r
            case _ => Condition.Or(left, right)
        case Condition.Inverted(v) =>
          val value = v.simplify
          value match
            case Condition.Known(x) => Condition.Known(!x)
            case Condition.And(l, r) => Condition.Or(Condition.Inverted(l), Condition.Inverted(r))
            case Condition.Or(l, r) => Condition.And(Condition.Inverted(l), Condition.Inverted(r))
            case _ => Condition.Inverted(value)
        case _ => this

    // Try to compile a one liner from this condition.
    def compileFlat(inverted: Boolean): Option[EvaluatedCondition] =
      import EvaluatedCondition.Check as ECCheck
      import EvaluatedCondition.Known as ECKnown
      val prefix = if inverted then "unless" else "if"
      this.simplify match
          case Condition.Less(left, right) =>
            Some(ECCheck(mcfunc"$prefix score ${left} < ${right}"))
          case Condition.LessEq(left, right) =>
            Some(ECCheck(mcfunc"$prefix score ${left} <= ${right}"))
          case Condition.Greater(left, right) =>
            Some(ECCheck(mcfunc"$prefix score ${left} > ${right}"))
          case Condition.GreaterEq(left, right) =>
            Some(ECCheck(mcfunc"$prefix score ${left} >= ${right}"))
          case Condition.Eq(left, right) =>
            Some(ECCheck(mcfunc"$prefix score ${left} = ${right}"))
          case Condition.Match(score, range) =>
            Some(ECCheck(mcfunc"$prefix score ${score} matches ${range.show}"))
          case Condition.Check(value) =>
            Some(ECCheck(prefix + " " + value))
          case Condition.Truthy(score) =>
            if inverted then
              Some(ECCheck(mcfunc"unless score $score matches ..-1 unless score $score matches 1.."))
            else
              Some(ECCheck(mcfunc"if score $score matches ${Int.MinValue}..${Int.MaxValue} unless score $score matches 0"))
          case Condition.Known(v) =>
            val x = if inverted then !v else v
            Some(ECKnown(x))
          case Condition.Inverted(v) =>
            v.compileFlat(!inverted)
          case Condition.And(l, r) =>
            if inverted then
              None
            else
              (l.compileFlat(false), r.compileFlat(false)).mapN { (left, right) =>
                (left, right) match
                  case (ECCheck(l), ECCheck(r)) =>
                    ECCheck(s"${l} ${r}")
                  case (_, ECKnown(r)) =>
                    if !r then
                      ECKnown(false)
                    else
                      left
                  case (ECKnown(l), r) =>
                    if !l then
                      ECKnown(false)
                    else
                      r
              }
          case Condition.Or(l, r) =>
            if !inverted then
              None
            else
              (l.compileFlat(true), r.compileFlat(true)).mapN { (left, right) =>
                (left, right) match
                  case (ECCheck(l), ECCheck(r)) =>
                    ECCheck(s"${l} ${r}")
                  case (ECKnown(l), r) =>
                    if l then
                      ECKnown(true)
                    else
                      r
                  case (l, ECKnown(r)) =>
                    if r then
                      ECKnown(true)
                    else
                      l
              }




    def compile(compiler: Compiler, code: mutable.ArrayBuffer[String], namespace: String, inverted: Boolean): EvaluatedCondition throws CompileError =
      import EvaluatedCondition.Check as ECCheck
      import EvaluatedCondition.Known as ECKnown
      this.compileFlat(inverted) match
        case Some(v) => v
        // we couldn't make a oneliner out of this one : (
        case _ =>
          this match
            case Condition.Or(l, r) =>
              if inverted then
                Condition.And(Condition.Inverted(l), Condition.Inverted(r)).compile(compiler, code, namespace, false)
              else
                l.compile(compiler, code, namespace, false) match
                  case ECKnown(true) => ECKnown(true)
                  case ECKnown(false) =>
                    r.compile(compiler, code, namespace, false)
                  case ECCheck(x) =>
                    r.compile(compiler, code, namespace, false) match
                      case ECKnown(true) => ECKnown(true)
                      case ECKnown(false) => ECCheck(x)
                      case ECCheck(y) =>
                        val var1 = compiler.nextScoreboard(namespace)
                        compiler.setScoreboard(code, var1, Expression(util.Location.blank, false, ExpressionKind.EBoolean(false)))
                        code.append(mcfunc"execute ${x} run scoreboard players set ${var1} 1")
                        code.append(mcfunc"execute ${y} run scoreboard players set ${var1} 1")
                        ECCheck(mcfunc"if score ${var1} matches 1")

                      
            case Condition.And(l, r) =>
              if inverted then
                Condition.Or(Condition.Inverted(l), Condition.Inverted(r)).compile(compiler, code, namespace, false)
              else
                l.compile(compiler, code, namespace, false) match
                  case ECKnown(false) => ECKnown(false)
                  case ECKnown(true) =>
                    r.compile(compiler, code, namespace, false)
                  case ECCheck(x) =>
                    r.compile(compiler, code, namespace, false) match
                      case ECKnown(false) => ECKnown(false)
                      case ECKnown(true) =>
                        ECCheck(x)
                      case ECCheck(y) =>
                        val var1 = compiler.nextScoreboard(namespace)
                        val var2 = compiler.nextScoreboard(namespace)
                        code.append(mcfunc"execute ${x} run scoreboard players set ${var1} 1")
                        code.append(mcfunc"execute ${y} run scoreboard players set ${var2} 1")

                        ECCheck(mcfunc"if score ${var1} matches 1 if score ${var2} matches 1")

            case Condition.Inverted(v) =>
              v.compile(compiler, code, namespace, !inverted)

            case _ => throw InternalError(util.Location.blank, "INTERNAL ERROR: Expected a non-flat conditional to be Or, And, or Inverted.")


  enum EvaluatedCondition:
    case Check(str: String)
    case Known(value: Boolean)


  case class LoopContext(condition: Option[ast.Expr],
                         continueExpr: Option[ast.Expr],
                         location: ResourceLocation)

  class FuncContext(var location: ResourceLocation,
                    var returnType: ReturnType,
                    var hasNestedReturns: util.Box[Boolean] = util.Box(false),
                    var hasNestedContinue: util.Box[Boolean] = util.Box(false),
                    var hasNestedBreak: util.Box[Boolean] = util.Box(false),
                    val code: mutable.ArrayBuffer[String] = mutable.ArrayBuffer(),
                    val isNested: Boolean = false,
                    var hasMacroArgs: Boolean = false,
                    val nestInfo: Option[NestedInfo] = None,
                    var currentContinueLabels: mutable.Set[String] = mutable.Set.empty,
                    var currentBreakLabels: mutable.Set[String] = mutable.Set.empty):



    def plain: FuncContext =
      FuncContext(location, returnType,
        hasNestedReturns = this.hasNestedReturns,
        hasNestedContinue = this.hasNestedContinue,
        hasNestedBreak = this.hasNestedBreak,
        isNested = isNested,
        hasMacroArgs = hasMacroArgs,
        code = code,
        nestInfo = nestInfo,
        currentContinueLabels = currentContinueLabels,
        currentBreakLabels = currentBreakLabels)

    def nested(kind: NestKind, actualLocation: ResourceLocation, label: Option[String]): FuncContext =
      FuncContext(location, returnType,
        hasNestedReturns = this.hasNestedReturns,
        hasNestedContinue = this.hasNestedContinue,
        hasNestedBreak = this.hasNestedBreak,
        isNested = true,
        hasMacroArgs = hasMacroArgs,
        nestInfo = Some(NestedInfo(kind, nestInfo, actualLocation, label)),
        currentContinueLabels = currentContinueLabels,
        currentBreakLabels = currentBreakLabels)


  case class FileTree(namespaces: List[FileTree.Namespace]):
    import java.nio.file.{Files, Path}
    def generate(path: String, config: Json): Unit =
      val rootPath = Path.of(path)
      if Files.exists(rootPath) then
        Using(Files.walk(rootPath)): walk =>
          walk.sorted(Comparator.reverseOrder())
            .map(_.toFile)
            .forEach(_.delete(): Unit)
        .get

      
      val workingPath = rootPath.resolve("data")
      Files.createDirectories(workingPath)
      Files.writeString(rootPath.resolve("yaoi.txt"), "")

      val mcmeta = config.spaces4

      Files.writeString(rootPath.resolve("pack.mcmeta"), mcmeta)

      namespaces.foreach: ns =>
        ns.generate(path)

  object FileTree:
    import java.nio.file.{Files, Path}
    case class Namespace(name: String, items: mutable.ArrayBuffer[Item]):
      def generate(path: String): Unit =
        items.foreach: item =>
          item.generate(path, ResourceLocation.module(name, List()))

      def getModule(path: List[String]): mutable.ArrayBuffer[Item] =
        if path.isEmpty then
          return items

        val first = path.head

        items.find {
          case Item.Module(name, _) => name == first
          case _ => false
        } match
          case Some(v: Item.Module) => v.getModule(path.tail)
          case _ =>
            val module = Item.Module(first, mutable.ArrayBuffer())
            items.append(module)
            module.getModule(path.tail)

    sealed trait Item:
      def generate(rootPath: String, localPath: ResourceLocation): Unit

    object Item:
      case class Module(name: String, items: mutable.ArrayBuffer[Item]) extends Item:
        def generate(rootPath: String, localPath: ResourceLocation): Unit =
          val newLocalPath = localPath.join(name)
          items.foreach: item =>
            item.generate(rootPath, newLocalPath)
        def getModule(path: List[String]): mutable.ArrayBuffer[Item] =
          if path.isEmpty then
            return items

          val first = path.head
          items.find {
            case Item.Module(name, _) => name == first
            case _ => false
          } match
            case Some(v: Item.Module) => v.getModule(path.tail)
            case _ =>
              val module = Module(first, mutable.ArrayBuffer())
              items.append(module)
              module.getModule(path.tail)
      case class ZFunction(name: String, commands: List[String], location: util.Location) extends Item:
        def generate(rootPath: String, localPath: ResourceLocation): Unit =
          val dirPath = Path.of(rootPath, "data", localPath.namespace, "function", localPath.modules.mkString("/"))
          Files.createDirectories(dirPath)
          val filePath = dirPath.resolve(name + ".mcfunction")
          Files.writeString(filePath, commands.mkString("\n"))
          ()
      case class ZTextResource(name: String, kind: String, isAsset: Boolean, text: String, location: util.Location) extends Item:
        override def equals(obj: Any): Boolean =
          obj match
            case that: ZTextResource =>
              this.name == that.name && this.kind == that.kind && this.isAsset == that.isAsset

        override def generate(rootPath: String, localPath: ResourceLocation): Unit =
          val resourceDir = if isAsset then "assets" else "data"
          var dirPath = Path.of(rootPath, resourceDir, localPath.namespace)
          if kind != "." then
            dirPath = dirPath.resolve(kind)
          dirPath = dirPath.resolve(localPath.modules.mkString("/"))

          Files.createDirectories(dirPath)
          val filePath = dirPath.resolve(name + ".json")
          Files.writeString(filePath, text)
          ()
      case class ZFileResource(kind: String, isAsset: Boolean, path: String, location: util.Location) extends Item:
        import java.nio.file.FileSystems
        override def generate(rootPath: String, localPath: ResourceLocation): Unit =
          val resourceDir = if isAsset then "assets" else "data"
          var dirPath = Path.of(rootPath, resourceDir, localPath.namespace)
          if kind != "." then
            dirPath = dirPath.resolve(kind)

          dirPath = dirPath.resolve(localPath.modules.mkString("/"))
          Files.createDirectories(dirPath)

          val matcher = FileSystems.getDefault.getPathMatcher("glob:" + path)
          Files.walkFileTree(Path.of(location.file).getParent, new SimpleFileVisitor[Path] {
            override def visitFile(file: Path, attrs: BasicFileAttributes): FileVisitResult =
              if matcher.matches(file) then
                Files.createDirectories(dirPath.resolve(file).getParent)
                Files.copy(file, dirPath.resolve(file))
                ()
              FileVisitResult.CONTINUE
          })
          ()


class Compiler:
  import Compiler.*
  import Resolver.FunctionDefinition
  val usedScoreboards: mutable.HashMap[String, String] = mutable.HashMap()
  val constantScoreboardValues: mutable.HashSet[Int] = mutable.HashSet()
  var currentScope: Resolver.ResolvedScope = null
  val tickFunctions: mutable.ArrayBuffer[String] = mutable.ArrayBuffer()
  val loadFunctions: mutable.ArrayBuffer[String] = mutable.ArrayBuffer()
  val functionRegistry: mutable.HashMap[ResourceLocation, FunctionDefinition] = mutable.HashMap()
  val namespaces: mutable.HashMap[String, FileTree.Namespace] = mutable.HashMap()
  val counters: mutable.HashMap[String, Int] = mutable.HashMap()
  var config: Option[Json] = None
  val nonFatalErrors: mutable.ArrayBuffer[CompileError] = mutable.ArrayBuffer()
  val warnings: mutable.ArrayBuffer[CompileError] = mutable.ArrayBuffer()

  object report:
    def nonfatal(err: CompileError): Unit =
      nonFatalErrors.append(err)

    def warning(err: CompileError): Unit =
      warnings.append(err)

  def loadResolved(resolve: ResolveResult): Unit =
    this.currentScope = resolve.scope
    this.config = resolve.config
    this.tickFunctions ++= resolve.tickFunctions
    this.loadFunctions ++= resolve.loadFunctions
    this.functionRegistry ++= resolve.functionRegistry.iterator

  def nextCounter(name: String): Int =
    if counters.contains(name) then
      counters(name) += 1
      counters(name)
    else
      counters(name) = 0
      0

  def nextFunction(funcType: String, namespace: String): ResourceLocation =
    ResourceLocation("yaoigen", List("generated", namespace, funcType, s"fn_${nextCounter(s"function:${funcType}")}"), ResourceKind.Func)


  def enterScope(name: String): Unit = {
    currentScope = currentScope.children(name)
  }

  def exitScope(): Unit = {
    currentScope = currentScope.parent.get
  }

  def getLocation(location: ResourceLocation): mutable.ArrayBuffer[FileTree.Item] =
    if !namespaces.contains(location.namespace) then
      namespaces(location.namespace) = FileTree.Namespace(location.namespace, mutable.ArrayBuffer())

    val namespace = namespaces(location.namespace)

    namespace.getModule(location.modules)

  def useScoreboard(name: String, criteria: String = "dummy"): Unit = {
    if usedScoreboards.contains(name) && criteria != "dummy" then
      usedScoreboards(name) = criteria
    else
      usedScoreboards(name) = criteria
  }


  def addItem(location: ResourceLocation, item: FileTree.Item): Unit throws CompileError =
    val items = getLocation(location)
    items.foreach: i =>
      (i, item) match
        case (FileTree.Item.ZFunction(name, _, _), FileTree.Item.ZFunction(name2, _, loc)) if name == name2 =>
          throw CompileError.nonfatal(loc, s"Function \"${name2}\" is already defined.")
        case (a: FileTree.Item.ZTextResource, b: FileTree.Item.ZTextResource) if a == b =>
          throw CompileError.nonfatal(b.location, s"${b.kind} \"${b.name}\" is already defined")
        case _ => ()
    
    items.append(item)

  def compileItem(ast: parser.ast.Decl, location: ResourceLocation): Unit throws CompileError =
    import parser.ast.Decl.*
    ast match
      case func: ZFunction => compileAstFunction(func, location)
      case module: parser.ast.Decl.Module => compileModule(module, location)
      case include: parser.ast.Decl.IncludedItems => 
        include.items.foreach: item =>
          compileItem(item, location)
      case _: UseModule => throw InternalError(ast.pos, "shouldn't be present here")
      case resource: ZResource => compileResource(resource, location)
      case ZConfig(pos, data) => ()
      case ZBuiltinCall(pos, call) => builtins.compileDecl(pos, call, location)

  def compileResource(resource: ZResource, location: ResourceLocation): Unit throws CompileError =
    import parser.ast.ResourceContent
    resource.content match
      case ResourceContent.Text(name, json) =>
        val compiled = json.spaces4
        val resource2 = FileTree.Item.ZTextResource(name, resource.kind, resource.isAsset, compiled, resource.pos)
        addItem(location, resource2)
      case ResourceContent.File(path, file) =>
        val filePath = Path.of(path).getParent
        val resource2 = FileTree.Item.ZFileResource(resource.kind, resource.isAsset, filePath.resolve(file).toString, resource.pos)
        addItem(location, resource2)


  private def compileAstFunction(func: parser.ast.Decl.ZFunction, location: ResourceLocation): Unit throws CompileError =
    val fnLocation = location.withName(func.name)
    val hasMacroArgs = func.params.exists(_.kind == ParameterKind.Macro)
    val context = FuncContext(fnLocation, func.returnType)
    context.hasMacroArgs = hasMacroArgs
    // TODO comptime
    compileBlock(func.stmts)(using context)
    addFunctionItem(func.pos, context.location, context.code.toList)
    
    // TODO: comptime



  private def addFunctionItem(location: util.Location, fnLocation: ResourceLocation, commands: List[String]): Unit throws CompileError =
    val (module, name) = fnLocation.trySplit.get
    val function = FileTree.Item.ZFunction(name, commands, location)
    addItem(module, function)

  private def compileBlock(block: List[parser.ast.Stmt])(using context: FuncContext): Unit throws FatalCompileError =
    block.foreach: stmt =>
      try
        compileStatement(stmt)
      catch
        case x: CompileError =>
          x match
            case y: FatalCompileError => throw y
            case y: NonfatalCompileError => report.nonfatal(y)

  

  private def compileIfStatementWithoutChild(condition: parser.ast.Expr, body: List[parser.ast.Stmt], isChild: Boolean)(using context: FuncContext): Unit throws CompileError =
    val condExpr = compileExpression(condition, false)
    val cond = condExpr.toCondition(this, context.code, context.location.namespace)
    // If it returns a EvaluatedCondition.Known, it should NEVER append code to our context
    val evaluatedCondition = cond.compile(this, context.code, context.location.namespace, false)
    evaluatedCondition match
      case EvaluatedCondition.Known(false) => ()
      case EvaluatedCondition.Known(true) =>
        compileBlock(body)
      case EvaluatedCondition.Check(checkCode) =>
        if body.nonEmpty && body.tail.isEmpty then
          body.head match
            case ast.Stmt.ZReturn(_, None) =>
              context.code += s"execute $checkCode run return 0"
              return
            case _ => ()
        val parameterStorage = context.location
        val func = nextFunction("if", context.location.namespace)
        val subContext = context.nested(NestKind.Transparent, func, None)
        
        compileBlock(body)(using subContext)
        val command =
          subContext.code.length match
            case 0 => ""
            case 1 if !subContext.hasNestedContinue.value =>
              subContext.code(0)
            case _ =>
              addFunctionItem(util.Location.blank, func, subContext.code.toList)
              if subContext.hasMacroArgs then
                mcfunc"function ${func} with storage ${parameterStorage}"
              else
                mcfunc"function ${func}"
        if command.nonEmpty then
          val executeCommand = 
            if !isChild then
              chainExecuteInstruction(checkCode, command)
            else
              s"execute ${checkCode} run return run ${command}"
          context.code.append(executeCommand) 
        
              


  def compileIfStatement(ifStatement: parser.ast.IfStatement)(using context: FuncContext): Unit throws CompileError =
    ifStatement.child match
      case Some(_) =>
        val ifFunc = nextFunction("if", context.location.namespace)

        val parameterStorage = context.location
        if context.hasMacroArgs then
          context.code.append(mcfunc"function ${ifFunc} with storage ${parameterStorage}")
        else
          context.code.append(mcfunc"function ${ifFunc}")

        val subContext = context.nested(NestKind.Transparent, ifFunc, None)

        var ifStmt = ifStatement
        def whileMethod(): Unit throws CompileError = {
          while true do
            compileIfStatementWithoutChild(ifStmt.cond, ifStmt.block, true)(using subContext)
            ifStmt.child match
              case Some(ElseStatement.EIfStatement(eif)) =>
                ifStmt = eif
              case Some(ElseStatement.Block(block)) =>
                compileBlock(block)(using subContext)
                return
              case None => return
        }
        whileMethod()
        val (module, name) = ifFunc.trySplit.get

        addItem(module, Item.ZFunction(name, subContext.code.toList, util.Location.blank))

      case None =>
        compileIfStatementWithoutChild(ifStatement.cond, ifStatement.block, false)

  def compileLoop(pos: util.Location, self: ResourceLocation, body: List[ast.Stmt], delay: Option[ast.Delay])(using context: FuncContext): Unit throws CompileError =
    val continueLocation = self.join("continue")
    val loopContext = context.nestInfo.flatMap(_.currentLoopContext).getOrElse(throw InternalError(pos, "INTERNAL ERROR: When compiling a loop, there should be a loop context"))
    loopContext.condition match
      case Some(conditionAstExpr) =>
        val conditionExpr = compileExpression(conditionAstExpr, false)
        val condition = conditionExpr.toCondition(this, context.code, context.location.namespace)
        val evaluatedCondition = condition.compile(this, context.code, context.location.namespace, inverted = true)
        evaluatedCondition match
          case EvaluatedCondition.Known(false) => return
          case EvaluatedCondition.Known(true) => ()
          case EvaluatedCondition.Check(checkCode) =>
            context.code.append(s"execute ${checkCode} run return 0")
      case _ => ()
    compileBlock(body)
    val subContext = context.nested(NestKind.Transparent, continueLocation, None)
    loopContext.continueExpr.foreach: continueExpr =>
      compileExpression(continueExpr, true)(using subContext)

    delay match
      case Some(delay) =>
        subContext.code.append(mcfunc"schedule function $self ${delay.toString}")
      case None =>
        subContext.code.append(mcfunc"function $self")
    context.code.append(mcfunc"function $continueLocation")

    
    addFunctionItem(util.Location.blank, continueLocation, subContext.code.toList)
    addFunctionItem(util.Location.blank, self, context.code.toList)
             
    
    


  def compileForLoop(pos: util.Location, forLoop: ast.Stmt.ZFor)(using context: FuncContext): Unit throws CompileError =
    val func = nextFunction("for", context.location.namespace)
    val loopContext =
      forLoop.range match
        case ForRange.Single(n) =>
          val _ = compileAssignment(forLoop.variable, Expr.ZInt(util.Location.blank, 0))
          LoopContext(Some(Expr.Binop(util.Location.blank, ast.BinopKind.Less, forLoop.variable, n)), Some(Expr.Binop(util.Location.blank, ast.BinopKind.AddAssign, forLoop.variable, Expr.ZInt(util.Location.blank, 1))), func)
        case ForRange.Range(min, inclusive, max) =>
          val _ = compileAssignment(forLoop.variable, min)
          LoopContext(Some(Expr.Binop(util.Location.blank, if inclusive then ast.BinopKind.LessEq else ast.BinopKind.Less, forLoop.variable, max)), Some(Expr.Binop(util.Location.blank, ast.BinopKind.AddAssign, forLoop.variable, Expr.ZInt(util.Location.blank, 1))), func)


    val subContext = context.nested(NestKind.Loop(loopContext), func, forLoop.label)
    compileLoop(pos, func, forLoop.body, forLoop.delay)(using subContext)
    context.code.append(mcfunc"function $func")



  def compileWhileLoop(whileLoop: parser.ast.Stmt.ZWhile)(using context: FuncContext): Unit throws CompileError =
    val func = nextFunction("while", context.location.namespace)
    val subContext = context.nested(NestKind.Loop(LoopContext(Some(whileLoop.cond), whileLoop.continueExpr, func)), func, whileLoop.label)


    compileLoop(whileLoop.cond.pos, func, whileLoop.body, whileLoop.delay)(using subContext)
    context.code.append(mcfunc"function $func")


  def compileStatement(statement: parser.ast.Stmt)(using context: FuncContext): Unit throws CompileError =
    statement match
      case Stmt.Eval(_, expr) => 
        val _ = compileExpression(expr, true)
      case x: Stmt.Command =>
        val cmd = compileCommand(x) 
        context.code.append(cmd)

      case Stmt.ZIf(pos, ifStatement) =>
        val subContext = context.plain
        subContext.hasNestedReturns = util.Box(false)
        subContext.hasNestedContinue = util.Box(false)
        subContext.hasNestedBreak = util.Box(false)
        compileIfStatement(ifStatement)(using subContext)
        if subContext.hasNestedReturns.value then
          context.hasNestedReturns.value = true
          generateNestedReturn()
        if subContext.hasNestedBreak.value then
          context.hasNestedBreak.value = true
          generateNestedBreak()
        if subContext.hasNestedContinue.value then
          context.hasNestedContinue.value = true
          generateNestedContinue()
        


      case s: Stmt.ZWhile =>
        val subContext = context.plain
        subContext.hasNestedReturns = util.Box(false)
        subContext.hasNestedContinue = util.Box(false)
        subContext.hasNestedBreak = util.Box(false)
        compileWhileLoop(s)(using subContext)
        if subContext.hasNestedReturns.value then
          context.hasNestedReturns.value = true
          generateNestedReturn()
        if subContext.hasNestedBreak.value then
          context.hasNestedBreak.value = true
          generateNestedBreak()
        if subContext.hasNestedContinue.value then
          context.hasNestedContinue.value = true
          generateNestedContinue()
      case s: Stmt.ZFor =>
        val subContext = context.plain
        subContext.hasNestedReturns = util.Box(false)
        subContext.hasNestedContinue = util.Box(false)
        subContext.hasNestedBreak = util.Box(false)
        compileForLoop(statement.pos, s)(using subContext)
        if subContext.hasNestedReturns.value then
          context.hasNestedReturns.value = true
          generateNestedReturn()
        if subContext.hasNestedBreak.value then
          context.hasNestedBreak.value = true
          generateNestedBreak()
        if subContext.hasNestedContinue.value then
          context.hasNestedContinue.value = true
          generateNestedContinue()
      case Stmt.ZReturn(_, expr) => compileReturn(expr)
      case Stmt.ZContinue(pos, label) =>
        compileContinue(pos, label)
      case Stmt.ZBreak(pos, label) =>
        compileBreak(pos, label)

  def compileSpawnCall(pos: util.Location, call: ast.FunctionCall, delay: ast.Delay, replace: Boolean)(using context: FuncContext): Unit throws CompileError =
    val (command, _) = compileFunctionCall(pos, call)
    command match
      case FunctionCommand.MacroCall(_, _) =>
        report.nonfatal:
          CompileError.nonfatal(pos,
            Seq(
              "Spawn calls can't call macro functions."
            )
          )
      case _ => ()
    context.code += mcfunc"schedule $command ${delay.toString} ${if replace then "replace" else "append"}"

  def compileExecuteBlock(instruction: String, block: List[Stmt], kind: String)(using context: FuncContext): Unit throws CompileError =
    val func = nextFunction(kind, context.location.namespace)
    val subContext = context.nested(NestKind.Transparent, func, None)
    compileBlock(block)(using subContext)
    subContext.code.length match
      case 0 => ()
      case 1 =>
        context.code += chainExecuteInstruction(instruction, subContext.code.head)
      case _ =>
        addFunctionItem(util.Location.blank, func, subContext.code.toList)
        context.code += mcfunc"execute $instruction run function $func"

  object internals:
    // TODO: do this idiomatically
    lazy val resetDirectReturn: ResourceLocation = {
      val location = ResourceLocation.function("yaoigen", List("internal", "0.1.0", "reset_return"))
      try
          addFunctionItem(util.Location.blank, location, List(
            // TODO: better namespace for the "applies to everything" than minecraft?
            "scoreboard players operation $temp_return yaoigen.internal.minecraft.vars = $should_return yaoigen.internal.minecraft.vars",
            "scoreboard players reset $should_return yaoigen.internal.minecraft.vars",
            "return run scoreboard players get $temp_return yaoigen.internal.minecraft.vars"
          ))
      catch
        case _: CompileError =>
          throw InternalError(util.Location.blank, "Should be able to add reset_return once")
      location
    }
    lazy val break: ResourceLocation = {
      val location = ResourceLocation.function("yaoigen", List("internal", "0.1.0", "break"))
      try
        addFunctionItem(util.Location.blank, location, List(
          // if break_n is at 0, we reached the loop we want to break from
          "execute if score $break_n yaoigen.internal.minecraft.vars matches ..0 run scoreboard players reset $should_break yaoigen.internal.minecraft.vars",
          "execute if score $break_n yaoigen.internal.minecraft.vars matches ..0 run return run return 0",
          // otherwise, decrement WITHOUT RESETTING THE VARIABLE!
          "scoreboard players remove $break_n yaoigen.internal.minecraft.vars 1"
        ))
      catch
        case _: CompileError =>
          throw InternalError(util.Location.blank, "We SHOULD be able to add break once")
      location
    }

  def generateNestedBreak()(using context: FuncContext): Unit =
    useScoreboard("yaoigen.internal.minecraft.vars")
    context.nestInfo.get.kind match
      case NestKind.Loop(_) =>
        val label = context.nestInfo.get.label
        label.foreach: label =>
          context.currentBreakLabels -= label
        if context.currentBreakLabels.isEmpty then
          context.hasNestedBreak.value = false
        
        context.code.append(
          mcfunc"execute if score $$should_break yaoigen.internal.minecraft.vars matches ${Int.MinValue}..${Int.MaxValue} run return run function ${internals.break}"
        )
      case _ =>
        context.code.append(
          s"execute if score $$should_break yaoigen.internal.minecraft.vars matches ${Int.MinValue}..${Int.MaxValue} run return 0"
        )

  def generateNestedContinue()(using context: FuncContext): Unit throws CompileError =
    // When a continue is compiled, it SHOULD:tm: already check the nestInfo
    if context.nestInfo.isDefined then
      useScoreboard(s"yaoigen.internal.minecraft.vars")
      context.nestInfo.get.kind match
        case NestKind.Loop(loopContext) =>
          val label = context.nestInfo.get.label
          label.foreach: label =>
            context.currentContinueLabels -= label
          if context.currentContinueLabels.isEmpty then
            context.hasNestedContinue.value = false

          val continueFn = loopContext.location.join("continue")
          val commands = List(
            // if continue_n is at 0, we reached the loop we want to continue
            mcfunc"execute if score $$continue_n yaoigen.internal.minecraft.vars matches ..0 run scoreboard players reset $$should_continue yaoigen.internal.minecraft.vars",
            mcfunc"execute if score $$continue_n yaoigen.internal.minecraft.vars matches ..0 run return run function ${continueFn}",
            // otherwise, decrement WITHOUT RESETTING THE VARIABLE!
            mcfunc"scoreboard players remove $$continue_n yaoigen.internal.minecraft.vars 1"

          )
          val fn = nextFunction("continue", context.location.namespace)
          addFunctionItem(util.Location.blank, fn, commands)
          context.code.append(
            mcfunc"execute if score $$should_continue yaoigen.internal.minecraft.vars matches ${Int.MinValue}..${Int.MaxValue} run return run function ${fn}"
          )
        case _ =>
          context.code.append(
            s"execute if score $$should_continue yaoigen.internal.minecraft.vars matches ${Int.MinValue}..${Int.MaxValue} run return 0"
          )

  def generateNestedReturn()(using context: FuncContext): Unit =
    useScoreboard(s"yaoigen.internal.minecraft.vars")
    val returnCommand =
      context.returnType match
        case ReturnType.Storage | ReturnType.Scoreboard if context.isNested => "return 0"
        case ReturnType.Storage | ReturnType.Scoreboard =>
          "return run scoreboard players reset $should_return yaoigen.internal.minecraft.vars"
        case ReturnType.Direct =>
          mcfunc"return run function ${internals.resetDirectReturn}"
    context.code.append(
      s"execute if score $$should_return yaoigen.internal.minecraft.vars matches ${Int.MinValue}..${Int.MaxValue} run $returnCommand"
    )

  def cleanCommandString(str: String): String =
    str.split(raw"\r?\n\s*").mkString(" ")

  object insertedExpr:
    def compile(part: CommandPart.Inserted)(using context: FuncContext): (String, Boolean) throws CompileError =
      part.expr match
        case InsertedExpr.MacroVariable(pos, name) =>
          if context.nestInfo.flatMap(_.getLoop).isDefined then
            report.nonfatal:
              CompileError.nonfatal(pos,
                Seq(
                  "This macro insert is inside of a loop.",
                  "For performance reasons, loops never pass their macro arguments to their children.",
                  "If you really want to do macro stuff for each loop,",
                  "Extract the macro into a seperate function and pass a normal argument."
                )
              )
          (s"$$(__${name})", true)
        case InsertedExpr.ScoreboardVariable(_, path) =>
          val scoreboard = ScoreboardLocation.resolveResource(context.location, path)
          (scoreboard.mcdisplay, false)
        case InsertedExpr.ResourceRef(pos, path) =>
          if path.namespace.isEmpty then
            report.warning:
              CompileError.nonfatal(pos,
                Seq(
                  "This inserted path has no namespace - this means it's being interpreted as a variable relative",
                  "to the current function.",
                  "If you want it to be relative to the current module, prefix it with ~/"
                ))
          val resolved = ResourceLocation.resolveResource(context.location, path)
          (resolved.mcdisplay, false)
        case InsertedExpr.ZBlock(pos, mayBeInlined, stmts) =>
          val func = nextFunction("block", context.location.namespace)
          val subContext = context.nested(NestKind.Transparent, func, None)
          compileBlock(stmts)(using subContext)
          subContext.code.length match
            case 0 => throw CompileError.nonfatal(pos, "Inserted blocks must have at least one statement")
            case 1 if mayBeInlined =>
              (subContext.code.head, false)
            case _ =>
              addFunctionItem(util.Location.blank, func, subContext.code.toList)
              if subContext.hasMacroArgs then
                (mcfunc"function ${func} with storage ${context.location}", false)
              else
                (mcfunc"function ${func}", false)
          
        case InsertedExpr.ZBuiltinCall(pos, call) =>
          (builtins.compileInserted(pos, call), false)
        case InsertedExpr.ZFunctionCall(pos, call, pollute) =>
          if !pollute && call.args.exists(_.executorSensitive) then
            report.warning:
              CompileError.nonfatal(pos, 
                Seq(
                  "This function call has arguments that may be executor sensitive, or be affected by commands inside the function.", 
                  "To call it while evaluating the arguments only once and in the current scope,", 
                  "add a @ after the &.",
                  "To evaluate the arguments for each call, and inside the command's scope, use a block (&!).",
                  "Note: the function itself will always be executed in the command's scope",
                  "this warning only affects the arguments."
                )
              )
          val (command, _) = compileFunctionCall(pos, call)
          command match
            case FunctionCommand.MacroCall(_, _) if !pollute =>
              report.warning:
                CompileError.nonfatal(pos,
                  Seq(
                    "This function call requires macros -",
                    "If this is inside a schedule function, this will not work.",
                    "If you would like to use macros where it would be acceptable in vanilla, add @ after the &.",
                    "If you want to use it where it would NOT be acceptable, make it a block (&!)"
                  )
                )
            case _ => ()
          
          (command.mcdisplay, false)



  def compileCommand(command: parser.ast.Stmt.Command)(using context: FuncContext): String throws CompileError =
    // : )
    val (res, needsMacro) = command.parts.foldLeft(("", false)) {
      case ((res, needsMacro), CommandPart.Literal(str)) =>
        (res + cleanCommandString(str), needsMacro)
      case ((res, needsMacro), inserted: CommandPart.Inserted) =>
        val (compiled, insertNeedsMacro) = insertedExpr.compile(inserted)
        (res + compiled, needsMacro || insertNeedsMacro)
    }    

    if needsMacro || res.startsWith("$") then
      context.hasMacroArgs = true
    if needsMacro && !res.startsWith("$") then
      "$" + res
    else
      res
    





  def compileNot(pos: util.Location, value: parser.ast.Expr)(using context: FuncContext): Expression throws CompileError =
    val operand = compileExpression(value, false)
    val needsMacro = operand.needsMacro
    val condition = operand.toCondition(this, context.code, context.location.namespace)
    Expression(pos, needsMacro, ExpressionKind.ECondition(Condition.Inverted(condition)))


  def compileNegate(pos: util.Location, value: parser.ast.Expr)(using context: FuncContext): Expression throws CompileError =
    val operand = compileExpression(value, false)
    val kind =
      operand.kind match
        case ExpressionKind.EVoid
              | ExpressionKind.EString(_)
              | ExpressionKind.EArray(_, _)
              | ExpressionKind.EByteArray(_)
              | ExpressionKind.EIntArray(_)
              | ExpressionKind.ELongArray(_)
              | ExpressionKind.ECompound(_)
              | ExpressionKind.ESubString(_, _, _)
              | ExpressionKind.ECondition(_)
              | ExpressionKind.EBoolean(_) => throw CompileError.nonfatal(pos, "Can only negate numbers")
        case ExpressionKind.EByte(b) =>
          ExpressionKind.EByte((-b).toByte)
        case ExpressionKind.EShort(s) =>
          ExpressionKind.EShort((-s).toShort)
        case ExpressionKind.EInteger(i) =>
          ExpressionKind.EInteger(-i)
        case ExpressionKind.ELong(l) =>
          ExpressionKind.ELong(-l)
        case ExpressionKind.EFloat(f) =>
          ExpressionKind.EFloat(-f)
        case ExpressionKind.EDouble(d) =>
          ExpressionKind.EDouble(-d)
        case ExpressionKind.EStorage(loc) =>
          val tempStorage = nextStorage(context.location.namespace)
          context.code.append(
            mcfunc"${if operand.needsMacro then "$" else ""}execute store result storage ${tempStorage} int -1 run data get storage ${loc}"
          )
          ExpressionKind.EStorage(tempStorage)
        case ExpressionKind.EEntity(selector, path) =>
          val tempStorage = nextStorage(context.location.namespace)
          context.code.append(
            mcfunc"${if operand.needsMacro then "$" else ""}execute store result storage ${tempStorage} int -1 run data get entity $selector $path"
          )
          ExpressionKind.EStorage(tempStorage)
        case ExpressionKind.EBlock((x, y, z), path) =>
          val tempStorage = nextStorage(context.location.namespace)
          context.code.append(
            mcfunc"${if operand.needsMacro then "$" else ""}execute store result storage ${tempStorage} int -1 run data get block $x $y $z $path"
          )
          ExpressionKind.EStorage(tempStorage)
        case ExpressionKind.EScoreboard(loc) =>
          val tempStorage = nextStorage(context.location.namespace)
          context.code.append(
            mcfunc"${if operand.needsMacro then "$" else ""}execute store result storage ${tempStorage} int -1 run scoreboard players get ${loc}"
          )
          ExpressionKind.EStorage(tempStorage)
        
        case ExpressionKind.EMacro(_) =>
          val tempStorage = copyToStorage(context.code, operand, context.location.namespace)
          context.code.append(
            mcfunc"execute store result ${tempStorage} int -1 run data get storage ${tempStorage}"
          )
          ExpressionKind.EStorage(tempStorage)
    Expression(pos, operand.needsMacro, kind)

  def compileUnaryExpression(expr: parser.ast.Expr.Unary)(using context: FuncContext): Expression throws CompileError =
    expr.kind match
      case UnaryKind.Not => compileNot(expr.pos, expr.expr)
      case UnaryKind.Negate => compileNegate(expr.pos, expr.expr)
      case UnaryKind.Caret => throw CompileError.nonfatal(expr.pos, "^ is invalid in normal expressions")
      case UnaryKind.Tilde => throw CompileError.nonfatal(expr.pos, "~ is invalid in normal expressions")

  def compileNumericOperation(left: parser.ast.Expr, operator: ScoreboardOperation, right: parser.ast.Expr)(using context: FuncContext): Expression throws CompileError =
    val l = compileExpression(left, false)
    val r = compileExpression(right, false)
    val needsMacro = l.needsMacro || r.needsMacro
    val kind =
      (l.kind, r.kind) match
        case (ExpressionKind.Numeric(lv), ExpressionKind.Numeric(rv)) =>
          ExpressionKind.EInteger(operator.constantOp(lv, rv))
        case (ExpressionKind.Numeric(_), _) if operator.commutative =>
          val scoreboard = copyToScoreboard(context.code, r, context.location.namespace)
          scoreboardOperation(scoreboard, l, operator)
          ExpressionKind.EScoreboard(scoreboard)
        case _ =>
          val scoreboard = copyToScoreboard(context.code, l, context.location.namespace)
          scoreboardOperation(scoreboard, r, operator)
          ExpressionKind.EScoreboard(scoreboard)
    Expression(left.pos, needsMacro, kind)



  def compileOperatorAssignment(left: parser.ast.Expr, operator: ScoreboardOperation, right: parser.ast.Expr)(using context: FuncContext): Expression throws CompileError =
    left match
      case Expr.ZScoreboardVariable(_, path) =>
        val l = compileExpression(left, false)
        val r = compileExpression(right, false)
        val scoreboard = ScoreboardLocation.resolveResource(context.location, path)
        useScoreboard(scoreboard.scoreboardString)
        scoreboardOperation(scoreboard, r, operator)
        l
      case _ =>
        compileAssignment(left, parser.ast.Expr.Binop(right.pos, operator.binopKind, left, right))

  def compileAssignTarget(expr: parser.ast.Expr)(using context: FuncContext): AssignTarget throws CompileError =
    expr match
      case exprUnapply.StoragePath(_, storage) =>
        AssignTarget.Data(DataKind.Storage(storage))
      case exprUnapply.ScoreboardPath(scoreboard) =>
        AssignTarget.Scoreboard(scoreboard)
      case exprUnapply.EntityStorage(_, selector, path) =>
        AssignTarget.Data(DataKind.Entity(selector, path))
      case exprUnapply.BlockEntityStorage(_, blockPos, path) =>
        AssignTarget.Data(DataKind.Block(blockPos, path))
      case ast.Expr.ZMember(pos, name, root) =>
        compileAssignTarget(root) match
          case AssignTarget.Data(kind) => 
            AssignTarget.Data(kind.subPath(name))
          case AssignTarget.Scoreboard(_) =>
            throw CompileError.nonfatal(pos, "Can't index scoreboard")
      case ast.Expr.ZIndex(pos, index, root) =>
        val idx = compileExpression(index, false)
        idx.kind.numericValue match
          case Some(value) =>
            compileAssignTarget(root) match
              case AssignTarget.Data(kind) =>
                AssignTarget.Data(kind.index(value))
              case _ => 
                throw CompileError.nonfatal(pos, "Can't index scoreboard")
          case None =>
            throw CompileError.nonfatal(pos, "TODO: Dynamic index")
      case _ =>
        throw CompileError.nonfatal(expr.pos, "Invalid assignment target")
        

  def compileAssignment(left: parser.ast.Expr, right: parser.ast.Expr)(using context: FuncContext): Expression throws CompileError =
    compileAssignTarget(left) match
      case AssignTarget.Scoreboard(scoreboard) =>
        val l = compileExpression(left, false)
        val r = compileExpression(right, false)
        setScoreboard(context.code, scoreboard, r)
        useScoreboard(scoreboard.scoreboardString)
        l
      case AssignTarget.Data(data) =>
        val l = compileExpression(left, false)
        val r = compileExpression(right, false)
        setData(context.code, data, r, context.location.namespace)
        l


  def compileMatchComparison(code: mutable.ArrayBuffer[String], value: Expression, range: MatchRange, namespace: String): ExpressionKind throws CompileError =
    val scoreboard = moveToScoreboard(code, value, namespace)
    ExpressionKind.ECondition(Condition.Match(scoreboard, range))

  def storageComparison(code: mutable.ArrayBuffer[String], left: Expression, right: Expression, checkEquality: Boolean, namespace: String): ExpressionKind throws CompileError =
    val rightStorage = moveToStorage(code, right, namespace)
    val tempStorage = copyToStorage(code, left, namespace)

    val conditionScoreboard = nextScoreboard(namespace)
    code.append(
      mcfunc"execute store success score ${conditionScoreboard} run data modify storage ${tempStorage} set from storage ${rightStorage}"
    )
    ExpressionKind.ECondition(Condition.Match(conditionScoreboard, MatchRange.Single(if checkEquality then 0 else 1)))

  def compileNotEquals(left: parser.ast.Expr, right: parser.ast.Expr)(using context: FuncContext): Expression throws CompileError =
    val l = compileExpression(left, false)
    val r = compileExpression(right, false)
    val needsMacro = l.needsMacro || r.needsMacro
    l.valueEqual(r) match
      case Some(equal) =>
        Expression(left.pos, false, ExpressionKind.EBoolean(equal))
      case _ =>
        val kind =
          (l.kind, r.kind) match
            case (ExpressionKind.EVoid, _) | (_, ExpressionKind.EVoid) =>
              throw CompileError.nonfatal(left.pos, "Cannot compare with void.")
            case (ExpressionKind.EStorage(_), _) | (_, ExpressionKind.EStorage(_)) =>
              storageComparison(context.code, l, r, false, context.location.namespace)
            case (leftKind, rightKind) if leftKind.nbtType.numeric && rightKind.nbtType.numeric =>
              val leftScore = moveToScoreboard(context.code, l, context.location.namespace)
              val rightScore = moveToScoreboard(context.code, r, context.location.namespace)
              ExpressionKind.ECondition(Condition.Inverted(Condition.Eq(leftScore, rightScore)))
            case _ =>
              storageComparison(context.code, l, r, false, context.location.namespace)
        Expression(left.pos, needsMacro, kind)
    



  def compileEquals(left: parser.ast.Expr, right: parser.ast.Expr)(using context: FuncContext): Expression throws CompileError =
    val l = compileExpression(left, false)
    val r = compileExpression(right, false)
    val needsMacro = l.needsMacro || r.needsMacro
    l.valueEqual(r) match
      case Some(equal) =>
        Expression(left.pos, false, ExpressionKind.EBoolean(equal))
      case _ => 
        val kind = 
          (l.kind, r.kind) match
            case (ExpressionKind.EVoid, _) | (_, ExpressionKind.EVoid) =>
              throw CompileError.nonfatal(left.pos, "Cannot compare with void.")
            case (ExpressionKind.EStorage(_), _) | (_, ExpressionKind.EStorage(_)) =>
              storageComparison(context.code, l, r, true, context.location.namespace)
            case (ExpressionKind.Numeric(v), _) =>
              compileMatchComparison(context.code, r, MatchRange.Single(v), context.location.namespace)
            case (_, ExpressionKind.Numeric(v)) =>
              compileMatchComparison(context.code, l, MatchRange.Single(v), context.location.namespace)
            case (leftKind, rightKind) if leftKind.nbtType.numeric && rightKind.nbtType.numeric =>
              val leftScore = moveToScoreboard(context.code, l, context.location.namespace)
              val rightScore = moveToScoreboard(context.code, r, context.location.namespace)
              ExpressionKind.ECondition(Condition.Eq(leftScore, rightScore))
            case _ =>
              storageComparison(context.code, l, r, true, context.location.namespace)
        Expression(left.pos, needsMacro, kind)
    


  def compileNumericComparison(left: parser.ast.Expr, right: parser.ast.Expr, comparator: NumericComparison)(using context: FuncContext): Expression throws CompileError =
    val l = compileExpression(left, false)
    val r = compileExpression(right, false)
    val kind =
      (l.kind, r.kind) match
        case (ExpressionKind.EVoid, _) | (_, ExpressionKind.EVoid) =>
          throw CompileError.nonfatal(left.pos, "Cannot compare with void.")
        case (ExpressionKind.EBoolean(_), _) | (_, ExpressionKind.EBoolean(_)) =>
          throw CompileError.nonfatal(left.pos, "Cannot compare with boolean.")
        case (ExpressionKind.EString(_), _) | (_, ExpressionKind.EString(_)) =>
          throw CompileError.nonfatal(left.pos, "Cannot compare with string.")
        case (ExpressionKind.Numeric(lv), ExpressionKind.Numeric(rv)) =>
          ExpressionKind.EBoolean(comparator.constOp(lv, rv))
        case (ExpressionKind.Numeric(lv), _) =>
          val scoreboard = moveToScoreboard(context.code, r, context.location.namespace)
          ExpressionKind.ECondition(comparator.inverse().halfOperator(scoreboard, lv))
        case (_, ExpressionKind.Numeric(rv)) =>
          val scoreboard =moveToScoreboard(context.code, l, context.location.namespace)
          ExpressionKind.ECondition(comparator.halfOperator(scoreboard, rv))
        case _ =>
          val leftScore = moveToScoreboard(context.code, l, context.location.namespace)
          val rightScore = moveToScoreboard(context.code, r, context.location.namespace)
          ExpressionKind.ECondition(comparator.operator(leftScore, rightScore))
    Expression(left.pos, l.needsMacro || r.needsMacro, kind)
    






  def compileLogicalOr(pos: util.Location, left: parser.ast.Expr, right: parser.ast.Expr)(using context: FuncContext): Expression throws CompileError =
    val l = compileExpression(left, false)
    val r = compileExpression(right, false)
    val leftCondition = l.toCondition(this, context.code, context.location.namespace)
    val rightCondition = r.toCondition(this, context.code, context.location.namespace)
    val kind = ExpressionKind.ECondition(Condition.Or(leftCondition, rightCondition).simplify)

    Expression(pos, l.needsMacro || r.needsMacro, kind)
    
    

  def compileLogicalAnd(pos: util.Location, left: parser.ast.Expr, right: parser.ast.Expr)(using context: FuncContext): Expression throws CompileError =
    val l = compileExpression(left, false)
    val r = compileExpression(right, false)
    val leftCondition = l.toCondition(this, context.code, context.location.namespace)
    val rightCondition = r.toCondition(this, context.code, context.location.namespace)
    val kind = ExpressionKind.ECondition(Condition.And(leftCondition, rightCondition).simplify)

    Expression(pos, l.needsMacro || r.needsMacro, kind)
      
    

  def compileBinaryExpression(expr: parser.ast.Expr.Binop)(using context: FuncContext): Expression throws CompileError =
    expr.name match
      case BinopKind.Equals => compileEquals(expr.l, expr.r)
      case BinopKind.Unequal => compileNotEquals(expr.l, expr.r)
      case BinopKind.Greater => compileNumericComparison(expr.l, expr.r, NumericComparison.greater)
      case BinopKind.GreaterEq => compileNumericComparison(expr.l, expr.r, NumericComparison.greaterEq)
      case BinopKind.Less => compileNumericComparison(expr.l, expr.r, NumericComparison.less)
      case BinopKind.LessEq => compileNumericComparison(expr.l, expr.r, NumericComparison.lessEq)
      case BinopKind.Plus => compileNumericOperation(expr.l, ScoreboardOperation.Add, expr.r)
      case BinopKind.Minus => compileNumericOperation(expr.l, ScoreboardOperation.Sub, expr.r)
      case BinopKind.Times => compileNumericOperation(expr.l, ScoreboardOperation.Mul, expr.r)
      case BinopKind.Divide => compileNumericOperation(expr.l, ScoreboardOperation.Div, expr.r)
      case BinopKind.Modulo => compileNumericOperation(expr.l, ScoreboardOperation.Mod, expr.r)
      case BinopKind.And => compileLogicalAnd(expr.pos, expr.l, expr.r)
      case BinopKind.Or => compileLogicalOr(expr.pos, expr.l, expr.r)
      case BinopKind.Assign => compileAssignment(expr.l, expr.r)
      case BinopKind.AddAssign => compileOperatorAssignment(expr.l, ScoreboardOperation.Add, expr.r)
      case BinopKind.SubAssign => compileOperatorAssignment(expr.l, ScoreboardOperation.Sub, expr.r)
      case BinopKind.MulAssign => compileOperatorAssignment(expr.l, ScoreboardOperation.Mul, expr.r)
      case BinopKind.DivAssign => compileOperatorAssignment(expr.l, ScoreboardOperation.Div, expr.r)
      case BinopKind.ModAssign => compileOperatorAssignment(expr.l, ScoreboardOperation.Mod, expr.r)

  def compileFunctionCall(pos: util.Location, functionCall: parser.ast.FunctionCall)(using context: FuncContext): (FunctionCommand, CalledFunction) throws CompileError =
    val path = ResourceLocation.resolveResource(context.location.module, functionCall.path)
    val functionDefinition =
      functionRegistry.get(path) match
        case Some(v) => v
        case _ =>
          FunctionDefinition(path, List(), ReturnType.Direct)

    val hasMacroArgs = functionDefinition.arguments.exists(_.kind == ParameterKind.Macro)

    val parameterStorage = functionDefinition.location

    val defaultContext = FuncContext(functionDefinition.location, ReturnType.Direct)
    val argIterator = functionCall.args.iterator
    functionDefinition.arguments.foreach: parameter =>
      val argument =
        (argIterator.hasNext, parameter.default) match
          case (true, _) => compileExpression(argIterator.next, false)
          case (false, Some(parameter)) =>
            val expr = compileExpression(parameter, false)(using defaultContext)
            context.code.appendAll(defaultContext.code)
            defaultContext.code.clear()
            expr
          case (false, None) => throw CompileError.nonfatal(pos, "Expected more arguments")
      parameter.kind match
        case ParameterKind.Storage =>
          val storage = StorageLocation(parameterStorage, parameter.name)
          setStorage(context.code, storage, argument)
        case ParameterKind.Scoreboard =>
          val scoreboard = ScoreboardLocation(parameterStorage, s"$$${parameter.name}")
          setScoreboard(context.code, scoreboard, argument)
        case ParameterKind.Macro =>
          val storage = StorageLocation(parameterStorage, s"__${parameter.name}")
          setStorage(context.code, storage, argument)
        case _ => ???
      

    val command =
      if hasMacroArgs then
        FunctionCommand.MacroCall(functionDefinition.location, parameterStorage)
      else
        FunctionCommand.PlainCall(functionDefinition.location)

    (command, CalledFunction(functionDefinition.location, functionDefinition.returnType))
    


  def compileContinue(pos: util.Location, label: Option[String])(using context: FuncContext): Unit throws CompileError =
    val (nestInfo, curLoop) = context.nestInfo.flatMap { nestInfo =>
      nestInfo.getLoop.map(it => (nestInfo, it))
    }.getOrElse(throw CompileError.nonfatal(pos, "continue may only be inside of loops"))
    if !nestInfo.isLoop || (label.isDefined && nestInfo.label != label) then
      context.hasNestedContinue.value = true
      label.foreach: it =>
        context.currentContinueLabels += it
      val loopsUntilLabel = label.map(it => nestInfo.loopsUntilLabel(it))
      
      context.code ++= List(
        s"scoreboard players set $$continue_n yaoigen.internal.minecraft.vars ${loopsUntilLabel.map(_._2).getOrElse(0)}",
        mcfunc"return run scoreboard players set $$should_continue yaoigen.internal.minecraft.vars 0"
      )
    else
      context.code.append(mcfunc"return run function ${curLoop.actualLocation}")

  def compileBreak(pos: util.Location, label: Option[String])(using context: FuncContext): Unit throws CompileError =
    val (nestInfo, _) = context.nestInfo.flatMap { nestInfo =>
      nestInfo.getLoop.map(it => (nestInfo, it))
    }.getOrElse(throw CompileError.nonfatal(pos, "break may only be inside of loops"))
    if !nestInfo.isLoop || (label.isDefined && nestInfo.label != label) then
      context.hasNestedBreak.value = true
      label.foreach: it =>
        context.currentBreakLabels += it
      val loopsUntilLabel = label.map(it => nestInfo.loopsUntilLabel(it))
      context.code ++= List(
        s"scoreboard players set $$break_n yaoigen.internal.minecraft.vars ${loopsUntilLabel.map(_._2).getOrElse(0)}",
        mcfunc"return run scoreboard players set $$should_break yaoigen.internal.minecraft.vars 0"
      )
    else
      context.code.append(mcfunc"return 0")


  def compileReturn(value: Option[parser.ast.Expr])(using context: FuncContext): Unit throws CompileError =
    if context.isNested then
      context.hasNestedReturns.value = true
    val hasValue = value.nonEmpty
  
    val expression = value.map(it => compileExpression(it, false))
      
    expression match
      case Some(v) =>
        context.returnType match
          case ReturnType.Storage =>
            val returnStorage = StorageLocation(context.location, "return")
            setStorage(context.code, returnStorage, v)
          case ReturnType.Scoreboard =>
            val scoreboard = ScoreboardLocation(context.location, "$return")
            setScoreboard(context.code, scoreboard, v)
          case ReturnType.Direct =>
            if context.isNested then
              setScoreboard(context.code, ScoreboardLocation.internal("minecraft", "$should_return"), v)
            else
              val cmd = v.toReturnCommand(this, context.code, context.location.namespace)
              context.code.append(cmd)
      case _ => ()

    if context.returnType != ReturnType.Direct && context.isNested then
      setScoreboard(context.code, ScoreboardLocation.internal("minecraft", "$should_return"), Expression(util.Location.blank, false, ExpressionKind.EInteger(1)))


    if hasValue then
      if context.returnType != ReturnType.Direct || context.isNested then
        context.code.append("return 0")
    else
      context.code.append("return fail")
    


  object builtins:
    def compileDecl(pos: util.Location, call: ast.BuiltinCall, location: ResourceLocation): Unit throws CompileError =
      Compiler.builtinDefinitions.all.get(call.name) match
        case Some(v) => v.decl(Compiler.this, pos, call, location)
        case _ => throw CompileError.nonfatal(pos, s"No such builtin ${call.name}")


    def compileInserted(pos: util.Location, call: ast.BuiltinCall)(using context: FuncContext): String throws CompileError =
      Compiler.builtinDefinitions.all.get(call.name) match
        case Some(v) => v.inserted(Compiler.this, pos, call)
        case _ => throw CompileError.nonfatal(pos, s"No such builtin ${call.name}")


    def compile(pos: util.Location, call: ast.BuiltinCall)(using context: FuncContext): Expression throws CompileError =
      Compiler.builtinDefinitions.all.get(call.name) match
        case Some(v) => v.expr(Compiler.this, pos, call)
        case _ => throw CompileError.nonfatal(pos, s"No such builtin ${call.name}")



  def verifyTypes(kinds: List[Expression], kind: ast.ArrayKind, message: String): NbtType throws CompileError =
    // Some NBT targets allow mixed types, so lets just not check it at all...
    if kind == ArrayKind.Any then
      return NbtType.Unknown
    var singleType =
      kind match
        case ArrayKind.Any => NbtType.Unknown
        case ArrayKind.Byte => NbtType.Byte
        case ArrayKind.Int => NbtType.Int
        case ArrayKind.Long => NbtType.Long

    kinds.foreach: kind =>
      (kind.kind, singleType) match
        case (ExpressionKind.EVoid, _) =>
          report.nonfatal(CompileError.nonfatal(kind.location, "Cannot use void as a value"))
        case (typ, NbtType.Unknown) =>
          singleType = typ.nbtType
        case (t, NbtType.Numeric) if t.nbtType.numeric =>
          singleType = t.nbtType
        case (ExpressionKind.EByte(_), NbtType.Byte) => ()
        case (ExpressionKind.EShort(_), NbtType.Short) => ()
        case (ExpressionKind.EInteger(_), NbtType.Int) => ()
        case (ExpressionKind.ELong(_), NbtType.Long) => ()
        case (ExpressionKind.EFloat(_), NbtType.Float) => ()
        case (ExpressionKind.EDouble(_), NbtType.Double) => ()
        case (ExpressionKind.EStorage(_), _) => ()
        case (ExpressionKind.EScoreboard(_), t) if t.numeric => ()
        case (ExpressionKind.EBoolean(_), NbtType.Byte) => ()
        case (ExpressionKind.EString(_), NbtType.String) => ()
        case (ExpressionKind.EArray(_, _), NbtType.List) => ()
        case (ExpressionKind.ECondition(_), NbtType.Byte) => ()
        case (ExpressionKind.ECompound(_), NbtType.Compound) => ()
        case _ =>
          report.nonfatal(CompileError.nonfatal(kind.location, message))
    
    if singleType == NbtType.Numeric then
      singleType = NbtType.Int

    singleType
  def compileArray(kind: ast.ArrayKind, expressions: List[ast.Expr], pos: util.Location)(using context: FuncContext): Expression throws CompileError =
    val kinds =
      expressions.map: expr =>
        compileExpression(expr, false)
  
    val errMsg =
      kind match
        case ast.ArrayKind.Any => "Arrays can only contain values of the same type"
        case ast.ArrayKind.Byte => "Byte arrays can only contain byte values"
        case ast.ArrayKind.Int => "Int arrays can only contain int values"
        case ast.ArrayKind.Long => "Long arrays can only contain long values"

    val dataType =verifyTypes(kinds, kind, errMsg)

    val exprKind =
      kind match
        case ast.ArrayKind.Any => ExpressionKind.EArray(kinds, dataType)
        case ast.ArrayKind.Byte => ExpressionKind.EByteArray(kinds)
        case ast.ArrayKind.Int => ExpressionKind.EIntArray(kinds)
        case ast.ArrayKind.Long => ExpressionKind.ELongArray(kinds)

    Expression(pos, false, exprKind)

  def compileCompound(pos: util.Location, keyValues: Map[String, ast.Expr])(using context: FuncContext): Expression throws CompileError =
    val kvs = 
      keyValues.map: (key, value) =>
        (key, compileExpression(value, false))
    
    Expression(pos, false, ExpressionKind.ECompound(kvs))



  def compileExpression(expr: ast.Expr, ignored: Boolean)(using context: FuncContext): Expression throws CompileError =
    expr match
      case s: Expr.Binop => compileBinaryExpression(s)
      case s: Expr.Unary  => compileUnaryExpression(s)
      case Expr.ZString(pos, contents) => Expression(pos, false, ExpressionKind.EString(contents))
      case Expr.ZByte(pos, num) => Expression(pos, false, ExpressionKind.EByte(num))
      case Expr.ZShort(pos, num) => Expression(pos, false, ExpressionKind.EShort(num))
      case Expr.ZInt(pos, num) => Expression(pos, false, ExpressionKind.EInteger(num))
      case Expr.ZLong(pos, num) => Expression(pos, false, ExpressionKind.ELong(num))
      case Expr.ZFloat(pos, num) => Expression(pos, false, ExpressionKind.EFloat(num))
      case Expr.ZDouble(pos, num) => Expression(pos, false, ExpressionKind.EDouble(num))
      case Expr.ZBool(pos, v) => Expression(pos, false, ExpressionKind.EBoolean(v))
      case Expr.ZList(pos, kind, values) => compileArray(kind, values, pos)
      case Expr.ZCompound(pos, map) => compileCompound(pos, map)
      case exprUnapply.StoragePath(pos, storage) => Expression(pos, false, ExpressionKind.EStorage(storage))
      case member: Expr.ZMember =>
        compileMember(member)
      case index: Expr.ZIndex => compileIndex(index)
      case Expr.ZVariable(pos, _) => throw InternalError(pos, "Already matched")
      case Expr.ZScoreboardVariable(pos, path) => Expression(pos, false, ExpressionKind.EScoreboard(ScoreboardLocation.resolveResource(context.location, path)))
      case Expr.ZMacroVariable(pos, name) => Expression(pos, true, ExpressionKind.EMacro(StorageLocation(context.location, "__" + name)))
      case Expr.ZBuiltinCall(pos, call) =>
        builtins.compile(pos, call)
      case Expr.ZFunctionCall(pos, functionCall) =>
        val (command, called) = compileFunctionCall(pos, functionCall)
        // can be either macro or non macro
        val commandStr = command.mcdisplay
        called.returnType match
          case ReturnType.Storage =>
            val storage = StorageLocation(called.location, "return")
            if !ignored then
              context.code.append(mcfunc"data modify storage ${storage} set value false")
            context.code.append(commandStr)
            Expression(expr.pos, false, ExpressionKind.EStorage(storage))
          case ReturnType.Scoreboard =>
            val scoreboard = ScoreboardLocation(called.location, "$return")
            if !ignored then
              context.code.append(mcfunc"scoreboard players set ${scoreboard} 0")
            context.code.append(commandStr)
            Expression(expr.pos, false, ExpressionKind.EScoreboard(scoreboard))
          case ReturnType.Direct =>
            val scoreboard = nextScoreboard(context.location.namespace)
            context.code.append(mcfunc"execute store result score ${scoreboard} run ${commandStr}")
            Expression(expr.pos, false, ExpressionKind.EScoreboard(scoreboard))
        

      case Expr.Atom(pos, expr) => compileExpression(expr, ignored)

  def compileMember(member: parser.ast.Expr.ZMember)(using context: FuncContext): Expression throws CompileError =
    val root = compileExpression(member.expr, false)
    root.subPath(member.pos, member.name)
  
  def compileIndex(index: parser.ast.Expr.ZIndex)(using context: FuncContext): Expression throws CompileError =
    val root = compileExpression(index.expr, false)
    val indexExpr = compileExpression(index.index, false)
    indexExpr.kind match
      case ExpressionKind.Numeric(value) =>
        root.index(index.pos, value)
      case _ =>
        throw CompileError.nonfatal(index.pos, "Dynamic indexing is currently unsupported")

  def compileModule(module: parser.ast.Decl.Module, location: ResourceLocation): Unit throws FatalCompileError =
    enterScope(module.name)
    // TODO: comptime

    val newLocation = location.join(module.name)
    module.items.foreach: item =>
      try
        compileItem(item, newLocation)
      catch
        case x: CompileError =>
          x match
            case y: NonfatalCompileError => report.nonfatal(y)
            case y: FatalCompileError => throw y
    exitScope()
    // TODO: comptime
  def compileNamespace(ast: parser.ast.Namespace): Unit throws CompileError =
    loadFunctions.prepend(s"yaoigen:generated/${ast.name}/load")
    enterScope(ast.name)
    // TODO: comptime

    val resource = ResourceLocation.module(ast.name, List())

    ast.items.foreach: item =>
      compileItem(item, resource)

    exitScope()
    // TODO: comptime

    val loadCommands = usedScoreboards.map((name, criteria) => s"scoreboard objectives add $name $criteria")

    val loadFunction = FileTree.Item.ZFunction("load", loadCommands.toList, util.Location.blank)

    addItem(ResourceLocation.module("yaoigen", List("generated", ast.name)), loadFunction)

  def compileTree(namespaces: List[ast.Namespace]): FileTree throws CompileError =
    namespaces.foreach: ns =>
      compileNamespace(ns)

    val constantCommands = constantScoreboardValues.toList.map(constant => s"scoreboard players set $$${displayConstant(constant)} yaoigen.internal.constants $constant")
    if constantCommands.nonEmpty then
      val constantFunction = FileTree.Item.ZFunction("load", constantCommands.prepended("scoreboard objectives add yaoigen.internal.constants dummy"), util.Location.blank)
      addItem(ResourceLocation.module("yaoigen", List("internal")), constantFunction)
      loadFunctions.prepend("yaoigen:internal/load")

    val loadJson = MinecraftTag(loadFunctions.toList).asJson.spaces4

    val load = FileTree.Item.ZTextResource("load", "tags/function", false, loadJson, util.Location.blank)

    val location = ResourceLocation.module("minecraft", List())


    addItem(location, load)
    if tickFunctions.nonEmpty then
      val tickJson = MinecraftTag(tickFunctions.toList).asJson.spaces4
      val tick = FileTree.Item.ZTextResource("tick", "tags/function", false, tickJson, util.Location.blank)
      addItem(location, tick)
    
    FileTree(this.namespaces.values.toList)

  def compile(resolved: ResolveResult, output: String, force: Boolean): Either[CompileError, Unit] =
    import java.nio.file.{Files, Path}
    val rootPath = Path.of(output)
    if !force && Files.exists(rootPath) && !Files.exists(rootPath.resolve("yaoi.txt")) then
      Left(CompileError.fatal(util.Location.blank, "The output directory has data in it, \nbut it's not made by yaoigen (no yaoi.txt); use --force to force"))
    else
      try
        loadResolved(resolved)
        val tree = compileTree(resolved.resultTree)

        if nonFatalErrors.isEmpty then
          tree.generate(output, this.config.getOrElse(MCMeta(MCMetaPack(description = "", packFormat = 48)).asJson))
        Right(())

      catch
        case x: CompileError =>
          Left(x)
      finally
        warnings.foreach: warning =>
          println("Warning:")
          println(warning.showPretty)

        nonFatalErrors.foreach: error =>
          println("Error:")
          println(error.showPretty)


      


  def nextScoreboard(namespace: String): ScoreboardLocation =
    useScoreboard(s"yaoigen.internal.${namespace}.vars")
    val nextNum = nextCounter("scoreboard")
    ScoreboardLocation(ResourceLocation("yaoigen", List("internal", namespace, "vars"), ResourceKind.Func), s"$$var_${nextNum}")

  def nextStorage(namespace: String): StorageLocation =
    val nextNum = nextCounter("storage")
    StorageLocation(ResourceLocation("yaoigen", List("internal", namespace, "vars"), ResourceKind.Func), "var_" + nextNum)

  def constantScoreboard(number: Int): ScoreboardLocation =
    useScoreboard("yaoigen.internal.constants")
    constantScoreboardValues += number
    val strRep = displayConstant(number)
    ScoreboardLocation(ResourceLocation("yaoigen", List("internal", "constants"), ResourceKind.Func), "$" + strRep)


  def copyToStorage(code: mutable.ArrayBuffer[String], value: Expression, namespace: String): StorageLocation throws CompileError =
    val storage = nextStorage(namespace)
    setStorage(code, storage, value)
    storage
  def moveToStorage(code: mutable.ArrayBuffer[String], value: Expression, namespace: String): StorageLocation throws CompileError =
    value.kind match
      case ExpressionKind.EStorage(storage) => storage
      case _ => copyToStorage(code, value, namespace)

  
  def setData(code: mutable.ArrayBuffer[String], data: DataKind, value: Expression, namespace: String): Unit throws CompileError =
    value.toData(this, code, data, "set", NbtType.Unknown, namespace)

  def setStorage(code: mutable.ArrayBuffer[String], storage: StorageLocation, value: Expression): Unit throws CompileError =
    setData(code, DataKind.Storage(storage), value, storage.storage.namespace)

  def scoreboardOperation(scoreboard: ScoreboardLocation, value: Expression, operation: ScoreboardOperation)(using context: FuncContext): Unit throws CompileError =
    value.kind match
      case ExpressionKind.EVoid
           | ExpressionKind.EString(_)
           | ExpressionKind.EArray(_, _)
            | ExpressionKind.EByteArray(_)
            | ExpressionKind.EIntArray(_)
            | ExpressionKind.ELongArray(_)
            | ExpressionKind.ESubString(_, _, _)
            | ExpressionKind.ECompound(_) => throw CompileError.nonfatal(value.location, "Can only perform operations on numbers.")
      case ExpressionKind.Numeric(value) =>
        operation.nativeOperator match
          case Some(native) =>
            context.code.append(mcfunc"scoreboard players $native ${scoreboard} ${value}")
          case None =>
            val const = constantScoreboard(value)
            context.code.append(mcfunc"scoreboard players operation ${scoreboard} ${operation.operator}= ${const}")
      case _ =>
        val otherScoreboard = moveToScoreboard(context.code, value, context.location.namespace)
        context.code.append(mcfunc"scoreboard players operation ${scoreboard} ${operation.operator}= ${otherScoreboard}")


  def setScoreboard(code: mutable.ArrayBuffer[String], scoreboard: ScoreboardLocation, value: Expression): Unit throws CompileError =
    val (conversionCode, kind) = value.toScore(this, code, scoreboard.scoreboard.namespace)
    kind match
      case ScoreKind.Direct(operation) =>
        code.append(mcfunc"scoreboard players ${operation} ${scoreboard} ${conversionCode}")
      case ScoreKind.DirectMacro(operation) =>
        code.append(mcfunc"$$scoreboard players ${operation} ${scoreboard} ${conversionCode}")
      case ScoreKind.Indirect =>
        code.append(mcfunc"execute store result score ${scoreboard} run ${conversionCode}")
      case ScoreKind.IndirectMacro =>
        code.append(mcfunc"$$execute store result score ${scoreboard} run ${conversionCode}")
    


  def copyToScoreboard(code: mutable.ArrayBuffer[String], value: Expression, namespace: String): ScoreboardLocation throws CompileError =
    val scoreboard = nextScoreboard(namespace)
    setScoreboard(code, scoreboard, value)
    scoreboard


  def moveToScoreboard(code: mutable.ArrayBuffer[String], value: Expression, namespace: String): ScoreboardLocation throws CompileError =
    value.kind match
      case ExpressionKind.EScoreboard(loc) => loc
      case _ => copyToScoreboard(code, value, namespace)
