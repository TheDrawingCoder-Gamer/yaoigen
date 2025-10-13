package gay.menkissing.yaoigen

import language.experimental.saferExceptions

import gay.menkissing.yaoigen.parser.ast.{ArrayKind, BinopKind, CommandPart, ElseStatement, Expr, ForRange, InsertedExpr, Parameter, ParameterKind, ReturnType, Stmt, UnaryKind}
import util.{Location, ResourceKind, ResourceLocation, ScoreboardLocation, StorageLocation, mcdisplay, given}
import util.MCFunctionDisplay.{mcfunc, given}

import java.util.Comparator
import scala.collection.mutable
import scala.util.Using
import scala.annotation.nowarn
import cats.implicits.*
import cats.*
import gay.menkissing.yaoigen.Compiler.FileTree.Item
import gay.menkissing.yaoigen.parser.ast
import gay.menkissing.yaoigen.parser.ast.Decl.ZResource
import io.circe.*
import io.circe.syntax.*

import java.nio.file.attribute.BasicFileAttributes
import java.nio.file.{FileVisitResult, Path, SimpleFileVisitor}




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

  case class CompileError(location: util.Location, msg: String) extends Exception:
    override def getMessage: String =
      show"Compile error ${location}:\n${msg}"

  case class CalledFunction(location: ResourceLocation, returnType: ReturnType)

  enum NestKind:
    case Loop(loopContext: LoopContext)
    case Block
    case Transparent

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
              throw CompileError(util.Location.blank, s"No such label $label in scope")
            case Some(p) =>
              val (it, n) = p.loopsUntilLabel(label)
              if this.isLoop then
                (it, n + 1)
              else
                (it, n)
          

  enum StorageKind:
    case Modify, MacroModify
    case Store, MacroStore

  object Expression:
    def void(at: util.Location): Expression =
      Expression(at, false, ExpressionKind.EVoid)

  case class Expression(location: util.Location, needsMacro: Boolean, kind: ExpressionKind):
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
             | (_, ExpressionKind.ECondition(_)) => None
        case _ => Some(false)

    def toStorage(compiler: Compiler, code: mutable.ArrayBuffer[String], storage: StorageLocation, operation: String, dataType: NbtType): Unit throws CompileError =
      kind.toComptimeString(false) match
        case Some(v) =>
          code.append(mcfunc"data modify storage ${storage} ${operation} value ${v}")
        case None => 
          val (conversionCode, kind2) =
            kind match
              case ExpressionKind.EVoid => throw CompileError(location, "Can't store void in storage")
              case ExpressionKind.EByte(_)
                  | ExpressionKind.EShort(_)
                  | ExpressionKind.EInteger(_)
                  | ExpressionKind.ELong(_)
                  | ExpressionKind.EFloat(_)
                  | ExpressionKind.EDouble(_)
                  | ExpressionKind.EBoolean(_)
                  | ExpressionKind.EString(_) => throw InternalError(location, "INTERNAL ERROR: This value should have a compile time string representation")
              case ExpressionKind.EArray(values, nbtType) => return arrayToStorage(values, "", compiler, code, storage, nbtType)
              case ExpressionKind.EByteArray(values) => return arrayToStorage(values, "B; ", compiler, code, storage, NbtType.Byte)
              case ExpressionKind.EIntArray(values) => return arrayToStorage(values, "I; ", compiler, code, storage, NbtType.Int)
              case ExpressionKind.ELongArray(values) => return arrayToStorage(values, "L; ", compiler, code, storage, NbtType.Long)
              case ExpressionKind.ECompound(values) => return compoundToStorage(values, compiler, code, storage)
              case ExpressionKind.EStorage(loc) =>
                (mcfunc"from storage ${loc}", StorageKind.Modify)
              case ExpressionKind.ESubString(loc, start, end) =>
                (mcfunc"string storage ${loc} ${start}${if end.nonEmpty then " " + end.get.toString else ""}", StorageKind.Modify)
              case ExpressionKind.EScoreboard(loc) =>
                (mcfunc"scoreboard players get ${loc}", StorageKind.Store)
              case ExpressionKind.EMacro(loc) =>
                (mcfunc"value $$(${loc.name})", StorageKind.MacroModify)
              case ExpressionKind.ECondition(cond) =>
                cond.compile(compiler, code, storage.storage.namespace, false) match
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
              code.append(mcfunc"data modify storage ${storage} ${operation} ${conversionCode}")
            case StorageKind.MacroModify =>
              code.append(mcfunc"$$data modify storage ${storage} ${operation} ${conversionCode}")
            case StorageKind.Store =>
              if operation == "set" then
                code.append(mcfunc"execute store result storage ${storage} ${storeType} 1 run ${conversionCode}")
              else
                val tempStorage = compiler.nextStorage(storage.storage.namespace)
                code.append(
                  mcfunc"execute store result storage ${tempStorage} ${storeType} 1 run ${conversionCode}"
                )
                code.append(
                  mcfunc"data modify storage ${storage} ${operation} from storage ${tempStorage}"
                )
            case StorageKind.MacroStore =>
              if operation == "set" then
                code.append(mcfunc"$$execute store result storage ${storage} ${storeType} 1 run ${conversionCode}")
              else
                val tempStorage = compiler.nextStorage(storage.storage.namespace)
                code.append(
                  mcfunc"$$execute store result storage ${tempStorage} ${storeType} 1 run ${conversionCode}"
                )
                code.append(
                  mcfunc"data modify storage ${storage} ${operation} from storage ${tempStorage}"
                )
        


    def toReturnCommand(compiler: Compiler, code: mutable.ArrayBuffer[String], namespace: String): String throws CompileError =
      this.kind match
        case ExpressionKind.EVoid => throw CompileError(location, "Cannot return void")
        case ExpressionKind.Numeric(n) => s"return $n"
        case ExpressionKind.EBoolean(b) =>
          if b then "return 1" else "return 0"
        case ExpressionKind.EString(_)
            | ExpressionKind.ESubString(_, _, _)
            | ExpressionKind.EArray(_, _)
            | ExpressionKind.EByteArray(_)
            | ExpressionKind.EIntArray(_)
            | ExpressionKind.ELongArray(_)
            | ExpressionKind.ECompound(_) => throw CompileError(location, "Can only directly return numeric values")
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
        case ExpressionKind.EVoid => throw CompileError(location, "Cannot assign void to a value")
        case ExpressionKind.EByte(b) => (b.toString, ScoreKind.Direct("set"))
        case ExpressionKind.EShort(s) => (s.toString, ScoreKind.Direct("set"))
        case ExpressionKind.EInteger(i) => (i.toString, ScoreKind.Direct("set"))
        case ExpressionKind.ELong(l) => (l.toString, ScoreKind.Direct("set"))
        case ExpressionKind.EFloat(f) => (f.floor.toInt.toString, ScoreKind.Direct("set"))
        case ExpressionKind.EDouble(d) => (d.floor.toInt.toString, ScoreKind.Direct("set"))
        case ExpressionKind.EBoolean(b) => (if b then "1" else "0", ScoreKind.Direct("set"))
        case ExpressionKind.EString(_) | ExpressionKind.ESubString(_, _, _) => throw CompileError(location, "Cannot assign string to scoreboard")
        case ExpressionKind.EArray(_, _) => throw CompileError(location, "Cannot assign array to scoreboard")
        case ExpressionKind.EByteArray(_) => throw CompileError(location, "Cannot assign array to scoreboard")
        case ExpressionKind.EIntArray(_) => throw CompileError(location, "Cannot assign array to scoreboard")
        case ExpressionKind.ELongArray(_) => throw CompileError(location, "Cannot assign array to scoreboard")
        case ExpressionKind.ECompound(_) => throw CompileError(location, "Cannot assign compound to scoreboard")
        case ExpressionKind.EStorage(loc) => (mcfunc"data get storage $loc", ScoreKind.Indirect)
        case ExpressionKind.EScoreboard(loc) => (mcfunc"= $loc", ScoreKind.Direct("operation"))
        case ExpressionKind.EMacro(loc) => (s"$$(${loc.name})", ScoreKind.DirectMacro("set"))
        case ExpressionKind.ECondition(cond) =>
          cond.compile(compiler, code, namespace, false) match
            case EvaluatedCondition.Check(c) => (s"execute $c", ScoreKind.Indirect)
            case EvaluatedCondition.Known(b) => (if b then "1" else "0", ScoreKind.Direct("set"))


    def toCondition(compiler: Compiler, code: mutable.ArrayBuffer[String], namespace: String): Condition throws CompileError =
      kind match
        case ExpressionKind.EVoid => throw CompileError(location, "Can't check void")
        case ExpressionKind.EByte(b) => Condition.Known(b != 0)
        case ExpressionKind.EShort(s) => Condition.Known(s != 0)
        case ExpressionKind.EInteger(i) => Condition.Known(i != 0)
        case ExpressionKind.ELong(l) => Condition.Known(l != 0)
        case ExpressionKind.EFloat(f) => Condition.Known(f != 0)
        case ExpressionKind.EDouble(d) => Condition.Known(d != 0)
        case ExpressionKind.EBoolean(b) => Condition.Known(b)
        case ExpressionKind.EString(_) => throw CompileError(location, "Can't use string as condition")
        case ExpressionKind.EArray(_, _) => throw CompileError(location, "Can't use array as condition")
        case ExpressionKind.EByteArray(_) => throw CompileError(location, "Can't use array as condition")
        case ExpressionKind.EIntArray(_) => throw CompileError(location, "Can't use array as condition")
        case ExpressionKind.ELongArray(_) => throw CompileError(location, "Can't use array as condition")
        case ExpressionKind.ECompound(_) => throw CompileError(location, "Can't use compound as condition")
        case ExpressionKind.EStorage(_) | ExpressionKind.EMacro(_) =>
          val scoreboard = compiler.copyToScoreboard(code, this, namespace)
          Condition.And(Condition.Match(scoreboard, MatchRange.Range(Some(Int.MinValue), Some(Int.MaxValue))), Condition.Inverted(Condition.Match(scoreboard, MatchRange.Single(0))))
        case ExpressionKind.ESubString(_, _, _) => throw CompileError(location, "Can't use string as condition")
        case ExpressionKind.EScoreboard(loc) =>
          // if score {scoreboard} matches (the entire int range) unless score {scoreboard} matches 0
          // Do this so an unset scoreboard is ALWAYS considered false
          Condition.And(Condition.Match(loc, MatchRange.Range(Some(Int.MinValue), Some(Int.MaxValue))), Condition.Inverted(Condition.Match(loc, MatchRange.Single(0))))
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


  private def arrayToString(values: List[Expression], prefix: String): Option[String] =
    val valueStrings = values.traverse(_.kind.toComptimeString(false))
    valueStrings.map: it =>
      it.mkString(s"[$prefix",",","]")

  private def arrayToStorage(
    elements: List[Expression],
    prefix: String,
    compiler: Compiler,
    code: mutable.ArrayBuffer[String],
    storage: StorageLocation,
    dataType: NbtType
  ): Unit throws CompileError =
    val constantElements = mutable.ArrayBuffer[String]()
    val computedElementsCode = mutable.ArrayBuffer[String]()
    elements.zipWithIndex.foreach: (expr, i)  =>
      expr.kind.toComptimeString(false) match
        case Some(value) =>
          constantElements.append(value)
        case _ =>
          expr.toStorage(compiler, code, storage, s"insert $i", dataType)
    // TODO: sus
    code.append(mcfunc"data modify storage $storage set value [${prefix}${constantElements.mkString(", ")}]")
    code.appendAll(computedElementsCode)

  private def compoundToStorage(
    elements: Map[String, Expression],
    compiler: Compiler,
    code: mutable.ArrayBuffer[String],
    storage: StorageLocation,
  ): Unit throws CompileError =
    val constantElements = mutable.ArrayBuffer[String]()
    val computedElementsCode = mutable.ArrayBuffer[String]()

    elements.foreach: (key, value) =>
      value.kind.toComptimeString(false) match
        case Some(value) =>
          constantElements.append(s"$key: $value")
        case _ =>
          val elementLocation = storage.copy(name = s"${storage.name}.$key")

          value.toStorage(
            compiler,
            computedElementsCode,
            elementLocation,
            "set",
            NbtType.Unknown
          )
    code.append(
      mcfunc"data modify storage $storage set value {${constantElements.mkString(", ")}}"
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
            value.kind.toComptimeString(false).map(it => s"$key: $it")
          .map: valueStrings =>
            valueStrings.mkString("{", ", ", "}")
        case ExpressionKind.EStorage(loc) =>
          if topLevel then
            Some(loc.mcdisplay)
          else None
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


  val builtins: Map[String, Builtin] =
    List[Builtin](
      Builtin.sideEffect("scoreboard") { (compiler, pos, args, location) => 
        val (score, criteria) =
          args match
            case List(Expr.ZVariable(_, path)) =>
              (ResourceLocation.resolveResource(location, path), "dummy")
            case List(Expr.ZVariable(_, path), Expr.ZString(_, crit)) =>
              (ResourceLocation.resolveResource(location, path), crit)
            case _ =>
              throw CompileError(pos, "Expected a path and optionally a criteria type.")
      
        compiler.useScoreboard(ScoreboardLocation.scoreboardStringOf(score), criteria)
      },
      Builtin.exprOnly("reset") { (_, pos, args) => context ?=>
        val (name, score) =
          args match
            case List(Expr.ZString(_, name), Expr.ZVariable(_, path)) =>
              (name, path)
            case _ =>
              throw CompileError(pos, "Expected a name and a path")
        
        val scoreboardLoc = ScoreboardLocation(ResourceLocation.resolveResource(context.location, score), name)
        context.code.append(mcfunc"scoreboard players reset ${scoreboardLoc}")

        Expression.void(pos)
        
      },
      Builtin.exprOnly("enable") { (_, pos, args) => context ?=>
        args match
          case List(Expr.ZString(_, name), Expr.ZVariable(_, score)) =>
            val scoreboardLoc = ScoreboardLocation(ResourceLocation.resolveResource(context.location, score), name)
            context.code.append(mcfunc"scoreboard players enable ${scoreboardLoc}")

            Expression.void(pos)
          case _ =>
            throw CompileError(pos, "Expected a name and a path.")


      },
      Builtin.exprOnly("condition") { (_, pos, args) => context ?=>
        args match
          case List(Expr.ZString(_, checkCode)) =>
            Expression(pos, false, ExpressionKind.ECondition(Condition.Check(checkCode)))
          case _ =>
            throw CompileError(pos, "Expected check code (the bit that comes after `if` in execute commands)")
      },
      Builtin.insertOnly("scoreboard_string") { (_, pos, args) => context ?=>
        args match
          case List(Expr.ZVariable(_, path)) =>
            val resolved = ResourceLocation.resolveResource(context.location, path)
            ScoreboardLocation.scoreboardStringOf(resolved)
          case _ =>
            throw CompileError(pos, "Expected path")

      }
    ).map(it => (it.name, it)).toMap

  trait Builtin:
    val name: String

    @nowarn("id=E198")
    def expr(compiler: Compiler, pos: util.Location, call: ast.BuiltinCall)(using context: FuncContext): Expression throws CompileError =
      throw CompileError(pos, s"The $name builtin doesn't work in expressions")

    @nowarn("id=E198")
    def inserted(compiler: Compiler, pos: util.Location, call: ast.BuiltinCall)(using context: FuncContext): String throws CompileError =
      throw CompileError(pos, s"The $name builtin doesn't work in inserts")

    @nowarn("id=E198")
    def decl(compiler: Compiler, pos: util.Location, call: ast.BuiltinCall, location: ResourceLocation): Unit throws CompileError =
      throw CompileError(pos, s"The $name builtin doesn't work at toplevel")

  object Builtin:
    // Side effect that can be in Expr or Decl position
    def sideEffect(nameArg: String)(func: (Compiler, util.Location, List[ast.Expr],ResourceLocation) => Unit throws CompileError): Builtin =
      new Builtin:
        override val name: String = nameArg

        override def expr(compiler: Compiler, pos: Location, call: ast.BuiltinCall)(using context: FuncContext): Expression throws CompileError =
          func(compiler, pos, call.args, context.location)
          Expression.void(pos)


        override def decl(compiler: Compiler, pos: Location, call: ast.BuiltinCall, location: ResourceLocation): Unit throws CompileError =
          func(compiler, pos, call.args, location)

    def insertOnly(nameArg: String)(func: (Compiler, util.Location, List[ast.Expr]) => FuncContext ?=> String throws CompileError): Builtin =
      new Builtin:
        override val name: String = nameArg


        override def inserted(compiler: Compiler, pos: Location, call: ast.BuiltinCall)(using context: FuncContext): String throws CompileError =
          func(compiler, pos, call.args)


    def exprOnly(nameArg: String)(func: (Compiler, util.Location, List[ast.Expr]) => FuncContext ?=> Expression throws CompileError): Builtin =
      new Builtin:
        override val name: String = nameArg

        override def expr(compiler: Compiler, pos: Location, call: ast.BuiltinCall)(using context: FuncContext): Expression throws CompileError =
          func(compiler, pos, call.args)

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
  case class FunctionDefinition(
                               location: ResourceLocation,
                               arguments: List[Parameter],
                               returnType: ReturnType
                               )

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


  class Scope(val parent: Int,
              val children: mutable.HashMap[String, mutable.ArrayDeque[Int]] = mutable.HashMap(),
              val functionRegistry: mutable.HashMap[String, ResourceLocation] = mutable.HashMap()
             ):
    def addChild(name: String, child: Int): Unit =
      children.get(name) match
        case Some(v) => v.append(child)
        case None => children(name) = mutable.ArrayDeque(child)

    def getChild(name: String): Option[Int] =
      children.get(name).map(_.removeHead())

    override def toString: String =
      s"Scope(parent = $parent, children = ${children.mkString("HashMap(",",",")")}, functionRegistry = ${functionRegistry.mkString("HashMap(",",",")")})"
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
  val scopes: mutable.ArrayBuffer[Compiler.Scope] = mutable.ArrayBuffer()
  val usedScoreboards: mutable.HashMap[String, String] = mutable.HashMap()
  val constantScoreboardValues: mutable.HashSet[Int] = mutable.HashSet()
  var currentScope: Int = 0
  val tickFunctions: mutable.ArrayBuffer[String] = mutable.ArrayBuffer()
  val loadFunctions: mutable.ArrayBuffer[String] = mutable.ArrayBuffer()
  val functionRegistry: mutable.HashMap[ResourceLocation, FunctionDefinition] = mutable.HashMap()
  val namespaces: mutable.HashMap[String, FileTree.Namespace] = mutable.HashMap()
  val counters: mutable.HashMap[String, Int] = mutable.HashMap()
  var config: Option[Json] = None

  def nextCounter(name: String): Int =
    if counters.contains(name) then
      counters(name) += 1
      counters(name)
    else
      counters(name) = 0
      0

  def nextFunction(funcType: String, namespace: String): ResourceLocation =
    ResourceLocation("yaoigen", List("generated", namespace, funcType, s"fn_${nextCounter(s"function:${funcType}")}"), ResourceKind.Func)
  def pushScope(name: String, parent: Int): Int = {
    scopes.append(Compiler.Scope(parent))
    val index = scopes.length - 1
    scopes(parent).addChild(name, index)
    index
  }

  def enterScope(name: String): Unit = {
    currentScope = scopes(currentScope).getChild(name).get
  }

  def exitScope(): Unit = {
    currentScope = scopes(currentScope).parent
  }

  def addFunction(scope: Int, name: String, location: ResourceLocation): Unit = {
      scopes(scope).functionRegistry(name) = location
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


  private object register:
    private def registerNamespace(ns: parser.ast.Namespace, parentScope: Int): Unit throws CompileError =
      val index = pushScope(ns.name, parentScope)

      val resource = ResourceLocation(ns.name, List(), ResourceKind.Module)

      ns.items.foreach: decl =>
        registerItem(decl, resource, index)

    def apply(nses: List[ast.Namespace]): Unit throws CompileError =
      scopes.append(Compiler.Scope(0))
      nses.foreach: ns =>
        registerNamespace(ns, 0)

    private def registerItem(item: parser.ast.Decl, location: ResourceLocation, parentScope: Int): Unit throws CompileError = {
      import parser.ast.Decl.*
      item match
        case Module(_, name, items) => registerModule(name, items, location, parentScope)
        case IncludedItems(_, _, items) => items.foreach(item => registerItem(item, location, parentScope))
        case ZFunction(_, returnType, name, params, stmts) => registerFunction(returnType, name, params, location, parentScope)
        case ZResource(_, _, _, _) => ()
        case ZBuiltinCall(_, _) => ()
        case ZConfig(pos, data) =>
          if Compiler.this.config.isDefined then
            throw CompileError(pos, "Duplicate MCMeta")
          else
            Compiler.this.config = Some(data)
    }

    private def registerModule(name: String, items: List[parser.ast.Decl], location: ResourceLocation, parentScope: Int): Unit throws CompileError = {
      val index = pushScope(name, parentScope)
      val newLoc = location.copy(modules = location.modules.appended(name))
      items.foreach: item =>
        registerItem(item, newLoc, index)
    }

    private def registerFunction(returnType: ReturnType, name: String, params: List[Parameter], location: ResourceLocation, parentScope: Int): Unit = {
        val functionLocation = location.withName(name)
        val functionPath = functionLocation.mcdisplay

        if params.exists(_.kind == ParameterKind.Scoreboard) then
          useScoreboard(ScoreboardLocation(functionLocation, "").scoreboardString)

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

  def addItem(location: ResourceLocation, item: FileTree.Item): Unit throws CompileError =
    val items = getLocation(location)
    items.foreach: i =>
      (i, item) match
        case (FileTree.Item.ZFunction(name, _, _), FileTree.Item.ZFunction(name2, _, loc)) if name == name2 =>
          throw CompileError(loc, s"Function \"${name2}\" is already defined.")
        case (a: FileTree.Item.ZTextResource, b: FileTree.Item.ZTextResource) if a == b =>
          throw CompileError(b.location, s"${b.kind} \"${b.name}\" is already defined")
        case _ => ()
    
    items.append(item)

  def compileItem(ast: parser.ast.Decl, location: ResourceLocation): Unit throws CompileError =
    import parser.ast.Decl.*
    ast match
      case func: ZFunction => compileAstFunction(func, location)
      case module: parser.ast.Decl.Module => compileModule(module, location)
      case incl: IncludedItems => incl.items.foreach(it => compileItem(it, location))
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

  private def compileBlock(block: List[parser.ast.Stmt])(using context: FuncContext): Unit throws CompileError =
    block.foreach: stmt =>
      compileStatement(stmt)


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
          val executeCommand = s"execute ${checkCode} ${if isChild then "run return run" else "run"} ${command}"
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
                return compileBlock(block)(using subContext)
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
        // Right now we don't actually check nested continues here. They are only for if statement to not fuck it up
        // When labelled continues are implemented, then it'll have to be checked
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
      val loopContext = context.nestInfo.get.currentLoopContext.get
      useScoreboard(s"yaoigen.internal.minecraft.vars")
      context.nestInfo.get.kind match
        case NestKind.Loop(_) =>
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
    val returnCommand =
      context.returnType match
        case ReturnType.Storage | ReturnType.Scoreboard if context.isNested => "return 0"
        case ReturnType.Storage | ReturnType.Scoreboard =>
          s"return run scoreboard players reset $$should_return yaoigen.internal.minecraft.vars"
        case ReturnType.Direct =>
          mcfunc"return run function ${internals.resetDirectReturn}"
    context.code.append(
      s"execute if score $$should_return yaoigen.internal.minecraft.vars matches ${Int.MinValue}..${Int.MaxValue} run $returnCommand"
    )

  def cleanCommandString(str: String): String =
    str.split(raw"\r?\n\w*").mkString(" ")

  object insertedExpr:
    def compile(part: CommandPart.Inserted)(using context: FuncContext): (String, Boolean) throws CompileError =
      part.expr match
        case InsertedExpr.MacroVariable(_, name) =>
          (s"$$(__${name})", true)
        case InsertedExpr.ScoreboardVariable(_, path) =>
          val scoreboard = ScoreboardLocation.resolveResource(context.location, path)
          (scoreboard.mcdisplay, false)
        case InsertedExpr.ResourceRef(_, path) =>
          val resolved = ResourceLocation.resolveResource(context.location, path)
          (resolved.mcdisplay, false)
        case InsertedExpr.ZBlock(pos, mayBeInlined, stmts) =>
          val func = nextFunction("block", context.location.namespace)
          val subContext = context.nested(NestKind.Transparent, func, None)
          compileBlock(stmts)(using subContext)
          subContext.code.length match
            case 0 => throw CompileError(pos, "Inserted blocks must have at least one statement")
            case 1 if mayBeInlined =>
              (subContext.code.head, false)
            case _ =>
              addFunctionItem(util.Location.blank, func, subContext.code.toList)
              (mcfunc"function ${func}", false)
          

        case InsertedExpr.ZBuiltinCall(pos, call) =>
          (builtins.compileInserted(pos, call), false)


  def compileCommand(command: parser.ast.Stmt.Command)(using context: FuncContext): String throws CompileError =
    // : )
    val (res, needsMacro) = command.parts.foldLeft(("", false)) {
      case ((res, needsMacro), CommandPart.Literal(str)) =>
        (res + cleanCommandString(str), needsMacro)
      case ((res, needsMacro), inserted: CommandPart.Inserted) =>
        val (compiled, insertNeedsMacro) = insertedExpr.compile(inserted)
        (res + compiled, needsMacro || insertNeedsMacro)
    }    

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
              | ExpressionKind.EBoolean(_) => throw CompileError(pos, "Can only negate numbers")
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
            mcfunc"${if operand.needsMacro then "$" else ""}execute store result storage ${tempStorage} int -1 run data get ${loc}"
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


  def compileAssignment(left: parser.ast.Expr, right: parser.ast.Expr)(using context: FuncContext): Expression throws CompileError =
    left match
      case Expr.ZVariable(_, path) =>
        val l = compileExpression(left, false)
        val r = compileExpression(right, false)
        val storage = StorageLocation.resolveResource(context.location, path)
        setStorage(context.code, storage, r)
        l
      case Expr.ZScoreboardVariable(_, path) =>
        val l = compileExpression(left, false)
        val r = compileExpression(right, false)
        val scoreboard = ScoreboardLocation.resolveResource(context.location, path)
        setScoreboard(context.code, scoreboard, r)
        useScoreboard(scoreboard.scoreboardString)
        l
        
      case _ => throw CompileError(left.pos, "Can only assign to a variable")


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
              throw CompileError(left.pos, "Cannot compare with void.")
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
              throw CompileError(left.pos, "Cannot compare with void.")
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
          throw CompileError(left.pos, "Cannot compare with void.")
        case (ExpressionKind.EBoolean(_), _) | (_, ExpressionKind.EBoolean(_)) =>
          throw CompileError(left.pos, "Cannot compare with boolean.")
        case (ExpressionKind.EString(_), _) | (_, ExpressionKind.EString(_)) =>
          throw CompileError(left.pos, "Cannot compare with string.")
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

  def compileFunctionCall(pos: util.Location, functionCall: parser.ast.FunctionCall)(using context: FuncContext): (String, CalledFunction) throws CompileError =
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
          case (false, None) => throw CompileError(pos, "Expected more arguments")
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
        mcfunc"function ${functionDefinition.location} with storage ${parameterStorage}"
      else
        mcfunc"function ${functionDefinition.location}"

    (command, CalledFunction(functionDefinition.location, functionDefinition.returnType))
    


  def compileContinue(pos: util.Location, label: Option[String])(using context: FuncContext): Unit throws CompileError =
    val (nestInfo, curLoop) = context.nestInfo.flatMap { nestInfo =>
      nestInfo.getLoop.map(it => (nestInfo, it))
    }.getOrElse(throw CompileError(pos, "continue may only be inside of loops"))
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
    }.getOrElse(throw CompileError(pos, "break may only be inside of loops"))
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
      Compiler.builtins.get(call.name) match
        case Some(v) => v.decl(Compiler.this, pos, call, location)
        case _ => throw CompileError(pos, s"No such builtin ${call.name}")


    def compileInserted(pos: util.Location, call: ast.BuiltinCall)(using context: FuncContext): String throws CompileError =
      Compiler.builtins.get(call.name) match
        case Some(v) => v.inserted(Compiler.this, pos, call)
        case _ => throw CompileError(pos, s"No such builtin ${call.name}")


    def compile(pos: util.Location, call: ast.BuiltinCall)(using context: FuncContext): Expression throws CompileError =
      Compiler.builtins.get(call.name) match
        case Some(v) => v.expr(Compiler.this, pos, call)
        case _ => throw CompileError(pos, s"No such builtin ${call.name}")



  def verifyTypes(kinds: List[Expression], kind: ast.ArrayKind, message: String): NbtType throws CompileError =
    var singleType =
      kind match
        case ArrayKind.Any => NbtType.Unknown
        case ArrayKind.Byte => NbtType.Byte
        case ArrayKind.Int => NbtType.Int
        case ArrayKind.Long => NbtType.Long

    kinds.foreach: kind =>
      (kind.kind, singleType) match
        case (ExpressionKind.EVoid, _) =>
          throw CompileError(kind.location, "Cannot use void as a value")
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
        case _ =>
          throw CompileError(kind.location, message)
    
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
      case Expr.ZVariable(pos, path) => Expression(pos, false, ExpressionKind.EStorage(StorageLocation.resolveResource(context.location, path)))
      case Expr.ZScoreboardVariable(pos, path) => Expression(pos, false, ExpressionKind.EScoreboard(ScoreboardLocation.resolveResource(context.location, path)))
      case Expr.ZMacroVariable(pos, name) => Expression(pos, true, ExpressionKind.EMacro(StorageLocation(context.location, "__" + name)))
      case Expr.ZBuiltinCall(pos, call) =>
        builtins.compile(pos, call)
      case Expr.ZFunctionCall(pos, functionCall) =>
        val (command, called) = compileFunctionCall(pos, functionCall)
        called.returnType match
          case ReturnType.Storage =>
            val storage = StorageLocation(called.location, "return")
            if !ignored then
              context.code.append(mcfunc"data modify storage ${storage} set value false")
            context.code.append(command)
            Expression(expr.pos, false, ExpressionKind.EStorage(storage))
          case ReturnType.Scoreboard =>
            val scoreboard = ScoreboardLocation(called.location, "$return")
            if !ignored then
              context.code.append(mcfunc"scoreboard players set ${scoreboard} 0")
            context.code.append(command)
            Expression(expr.pos, false, ExpressionKind.EScoreboard(scoreboard))
          case ReturnType.Direct =>
            val scoreboard = nextScoreboard(context.location.namespace)
            context.code.append(mcfunc"execute store result score ${scoreboard} run ${command}")
            Expression(expr.pos, false, ExpressionKind.EScoreboard(scoreboard))
        

      case Expr.Atom(pos, expr) => compileExpression(expr, ignored)

  def compileModule(module: parser.ast.Decl.Module, location: ResourceLocation): Unit throws CompileError =
    enterScope(module.name)
    // TODO: comptime

    val newLocation = location.join(module.name)
    module.items.foreach: item =>
      compileItem(item, newLocation)
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

  def compileTree(ast: List[parser.ast.Namespace]): FileTree throws CompileError =
    ast.foreach: ns =>
      compileNamespace(ns)
    val loadJson = MinecraftTag(loadFunctions.toList).asJson.spaces4

    val load = FileTree.Item.ZTextResource("load", "tags/function", false, loadJson, util.Location.blank)

    val location = ResourceLocation.module("minecraft", List())


    addItem(location, load)
    if tickFunctions.nonEmpty then
      val tickJson = MinecraftTag(tickFunctions.toList).asJson.spaces4
      val tick = FileTree.Item.ZTextResource("tick", "tags/function", false, tickJson, util.Location.blank)
      addItem(location, tick)
    
    FileTree(namespaces.values.toList)

  def compile(file: List[parser.ast.Namespace], output: String, force: Boolean): Unit throws CompileError =
    import java.nio.file.{Files, Path}
    val rootPath = Path.of(output)
    if !force && Files.exists(rootPath) && !Files.exists(rootPath.resolve("yaoi.txt")) then
      throw CompileError(util.Location.blank, "The output directory has data in it, \nbut it's not made by yaoigen (no yaoi.txt); use --force to force")
    else
      register(file)

      val tree = compileTree(file)

      tree.generate(output, this.config.getOrElse(MCMeta(MCMetaPack(description = "", packFormat = 48)).asJson))


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
    val strRep = if number < 0 then s"neg${math.abs(number)}" else number.toString
    ScoreboardLocation(ResourceLocation("yaoigen", List("internal", "constants"), ResourceKind.Func), "$" + strRep)


  def copyToStorage(code: mutable.ArrayBuffer[String], value: Expression, namespace: String): StorageLocation throws CompileError =
    val storage = nextStorage(namespace)
    setStorage(code, storage, value)
    storage
  def moveToStorage(code: mutable.ArrayBuffer[String], value: Expression, namespace: String): StorageLocation throws CompileError =
    value.kind match
      case ExpressionKind.EStorage(storage) => storage
      case _ => copyToStorage(code, value, namespace)


  def setStorage(code: mutable.ArrayBuffer[String], storage: StorageLocation, value: Expression): Unit throws CompileError =
    value.toStorage(this, code, storage, "set", NbtType.Unknown)

  def scoreboardOperation(scoreboard: ScoreboardLocation, value: Expression, operation: ScoreboardOperation)(using context: FuncContext): Unit throws CompileError =
    value.kind match
      case ExpressionKind.EVoid
           | ExpressionKind.EString(_)
           | ExpressionKind.EArray(_, _)
            | ExpressionKind.EByteArray(_)
            | ExpressionKind.EIntArray(_)
            | ExpressionKind.ELongArray(_)
            | ExpressionKind.ESubString(_, _, _)
            | ExpressionKind.ECompound(_) => throw CompileError(value.location, "Can only perform operations on numbers.")
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
