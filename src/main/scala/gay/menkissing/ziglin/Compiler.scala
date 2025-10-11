package gay.menkissing.ziglin

import gay.menkissing.ziglin.parser.ast.{ArrayKind, BinopKind, CommandPart, ElseStatement, Expr, ForRange, InsertedExpr, Parameter, ParameterKind, ReturnType, Stmt, UnaryKind}
import util.{Location, ResourceKind, ResourceLocation, ScoreboardLocation, StorageLocation, mcdisplay, given}
import util.MCFunctionDisplay.{mcfunc, given}

import java.util.Comparator
import scala.collection.mutable
import scala.util.Using
import cats.implicits.*
import cats.*
import gay.menkissing.ziglin.Compiler.FileTree.Item
import gay.menkissing.ziglin.parser.ast
import gay.menkissing.ziglin.parser.ast.Decl.ZResource
import io.circe.*
import io.circe.syntax.*

import java.nio.file.attribute.BasicFileAttributes
import java.nio.file.{FileVisitResult, Path, SimpleFileVisitor}


object Compiler:
  case class MinecraftTag(values: List[String]) derives Decoder, Encoder
  case class MCMeta(packFormat: String, description: String)

  given Decoder[MCMeta] =
    Decoder.forProduct2("pack_format", "description")(MCMeta.apply)
  given Encoder[MCMeta] =
    Encoder.forProduct2("pack_format", "description")(u =>
      (u.packFormat, u.description)
    )



  case class InternalError(location: util.Location, msg: String) extends RuntimeException:
    override def getMessage: String =
      s"Internal error ${location}:\n${msg}"

  case class CompileError(location: util.Location, msg: String) extends RuntimeException:
    override def getMessage: String =
      s"Compile error ${location}:\n${msg}"

  case class CalledFunction(location: ResourceLocation, returnType: ReturnType)

  enum NestKind:
    case Loop(loopContext: LoopContext)
    case Block

  case class NestedInfo(kind: NestKind, parent: Option[NestedInfo], actualLocation: ResourceLocation, label: Option[String]):
    def currentLoopContext: Option[LoopContext] =
      kind match
        case NestKind.Loop(loopContext) => Some(loopContext)
        case NestKind.Block =>
          parent match
            case Some(p) => p.currentLoopContext
            case None => None

    def getLoop: Option[NestedInfo] =
      kind match
        case NestKind.Loop(_) => Some(this)
        case NestKind.Block =>
          parent match
            case Some(p) => p.getLoop
            case None => None

    def isLoop: Boolean =
      kind match
        case NestKind.Loop(_) => true
        case _ => false

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
        case (ExpressionKind.EArray(lValues, _), ExpressionKind.EArray(rValues, _)) => ???
        case (ExpressionKind.EByteArray(lValues), ExpressionKind.EByteArray(rValues)) => ???
        case (ExpressionKind.EIntArray(lValues), ExpressionKind.EIntArray(rValues)) => ???
        case (ExpressionKind.ELongArray(lValues), ExpressionKind.ELongArray(rValues)) => ???
        case (ExpressionKind.ECompound(lValues), ExpressionKind.ECompound(rValues)) => ???
        case (ExpressionKind.EScoreboard(_), other) if !other.nbtType.numeric => Some(false)
        case (other, ExpressionKind.EScoreboard(_)) if !other.nbtType.numeric => Some(false)
        case (ExpressionKind.EStorage(_), _)
             | (_, ExpressionKind.EStorage(_))
             | (ExpressionKind.EScoreboard(_), _)
             | (_, ExpressionKind.EScoreboard(_))
             | (ExpressionKind.ECondition(_), _)
             | (_, ExpressionKind.ECondition(_)) => None
        case _ => Some(false)

    def toStorage(compiler: Compiler, code: mutable.ArrayBuffer[String], storage: StorageLocation, operation: String, dataType: NbtType): Either[CompileError, Unit] =
      kind.toComptimeString(false) match
        case Some(v) =>
          code.append(mcfunc"data modify storage ${storage} ${operation} value ${v}")
          Right(())
        case None => {
          kind match
            case ExpressionKind.EVoid => Left(CompileError(location, "Can't store void in storage"))
            case ExpressionKind.EByte(_)
                 | ExpressionKind.EShort(_)
                 | ExpressionKind.EInteger(_)
                 | ExpressionKind.ELong(_)
                 | ExpressionKind.EFloat(_)
                 | ExpressionKind.EDouble(_)
                 | ExpressionKind.EBoolean(_)
                 | ExpressionKind.EString(_) => throw InternalError(location, "INTERNAL ERROR: This value should have a compile time string representation")
            case ExpressionKind.EArray(values, nbtType) => ???
            case ExpressionKind.EByteArray(values) => ???
            case ExpressionKind.EIntArray(values) => ???
            case ExpressionKind.ELongArray(values) => ???
            case ExpressionKind.ECompound(values) => ???
            case ExpressionKind.EStorage(loc) =>
              Right((mcfunc"from storage ${loc}", StorageKind.Modify))
            case ExpressionKind.ESubString(loc, start, end) =>
              Right((mcfunc"string storage ${loc} ${start}${if end.nonEmpty then " " + end.get.toString else ""}", StorageKind.Modify))
            case ExpressionKind.EScoreboard(loc) =>
              Right((mcfunc"scoreboard players get ${loc}", StorageKind.Store))
            case ExpressionKind.EMacro(loc) =>
              Right((mcfunc"value $$(${loc.name})", StorageKind.MacroModify))
            case ExpressionKind.ECondition(cond) =>
              cond.compile(compiler, code, storage.storage.namespace, false).map:
                case EvaluatedCondition.Check(c) =>
                  (s"execute ${c}", StorageKind.Store)
                case EvaluatedCondition.Known(v) =>
                  (s"value $v", StorageKind.Modify)
        }.map { (conversionCode, kind2) =>
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
        }


    def toReturnCommand(compiler: Compiler, code: mutable.ArrayBuffer[String], namespace: String): Either[CompileError, String] =
      this.kind match
        case ExpressionKind.EVoid => Left(CompileError(location, "Cannot return void"))
        case ExpressionKind.Numeric(n) => Right(s"return $n")
        case ExpressionKind.EBoolean(b) =>
          Right(if b then "return 1" else "return 0")
        case ExpressionKind.EString(_)
            | ExpressionKind.ESubString(_, _, _)
            | ExpressionKind.EArray(_, _)
            | ExpressionKind.EByteArray(_)
            | ExpressionKind.EIntArray(_)
            | ExpressionKind.ELongArray(_)
            | ExpressionKind.ECompound(_) => Left(CompileError(location, "Can only directly return numeric values"))
        case ExpressionKind.EStorage(storage) =>
          Right(mcfunc"return run data get storage ${storage}")
        case ExpressionKind.EScoreboard(scoreboard) =>
          Right(mcfunc"return run scoreboard players get ${scoreboard}")
        case ExpressionKind.EMacro(name) =>
          Right(mcfunc"$$return $$(${name})")
        case ExpressionKind.ECondition(condition) =>
          condition.compile(compiler, code, namespace, false).map:
            case EvaluatedCondition.Check(c) => s"return run execute ${c}"
            case EvaluatedCondition.Known(v) => if v then "return 1" else "return 0"
        case _ =>
          // unreachable
          throw InternalError(location, "Unreachable")


    def toScore(compiler: Compiler, code: mutable.ArrayBuffer[String], namespace: String): Either[CompileError, (String, ScoreKind)] =
      kind match
        case ExpressionKind.EVoid => Left(CompileError(location, "Cannot assign void to a value"))
        case ExpressionKind.EByte(b) => Right((b.toString, ScoreKind.Direct("set")))
        case ExpressionKind.EShort(s) => Right((s.toString, ScoreKind.Direct("set")))
        case ExpressionKind.EInteger(i) => Right((i.toString, ScoreKind.Direct("set")))
        case ExpressionKind.ELong(l) => Right((l.toString, ScoreKind.Direct("set")))
        case ExpressionKind.EFloat(f) => Right((f.floor.toInt.toString, ScoreKind.Direct("set")))
        case ExpressionKind.EDouble(d) => Right((d.floor.toInt.toString, ScoreKind.Direct("set")))
        case ExpressionKind.EBoolean(b) => Right((if b then "1" else "0", ScoreKind.Direct("set")))
        case ExpressionKind.EString(_) | ExpressionKind.ESubString(_, _, _) => Left(CompileError(location, "Cannot assign string to scoreboard"))
        case ExpressionKind.EArray(values, nbtType) => Left(CompileError(location, "Cannot assign array to scoreboard"))
        case ExpressionKind.EByteArray(values) => Left(CompileError(location, "Cannot assign array to scoreboard"))
        case ExpressionKind.EIntArray(values) => Left(CompileError(location, "Cannot assign array to scoreboard"))
        case ExpressionKind.ELongArray(values) => Left(CompileError(location, "Cannot assign array to scoreboard"))
        case ExpressionKind.ECompound(values) => Left(CompileError(location, "Cannot assign compound to scoreboard"))
        case ExpressionKind.EStorage(loc) => Right((mcfunc"data get storage $loc", ScoreKind.Indirect))
        case ExpressionKind.EScoreboard(loc) => Right((mcfunc"= $loc", ScoreKind.Direct("operation")))
        case ExpressionKind.EMacro(loc) => Right((s"$$(${loc.name})", ScoreKind.DirectMacro("set")))
        case ExpressionKind.ECondition(cond) =>
          cond.compile(compiler, code, namespace, false).map:
            case EvaluatedCondition.Check(c) => (s"execute $c", ScoreKind.Indirect)
            case EvaluatedCondition.Known(b) => (if b then "1" else "0", ScoreKind.Direct("set"))


    def toCondition(compiler: Compiler, code: mutable.ArrayBuffer[String], namespace: String): Either[CompileError, Condition] =
      kind match
        case ExpressionKind.EVoid => Left(CompileError(location, "Can't check void"))
        case ExpressionKind.EByte(b) => Right(Condition.Known(b != 0))
        case ExpressionKind.EShort(s) => Right(Condition.Known(s != 0))
        case ExpressionKind.EInteger(i) => Right(Condition.Known(i != 0))
        case ExpressionKind.ELong(l) => Right(Condition.Known(l != 0))
        case ExpressionKind.EFloat(f) => Right(Condition.Known(f != 0))
        case ExpressionKind.EDouble(d) => Right(Condition.Known(d != 0))
        case ExpressionKind.EBoolean(b) => Right(Condition.Known(b))
        case ExpressionKind.EString(s) => Left(CompileError(location, "Can't use string as condition"))
        case ExpressionKind.EArray(values, nbtType) => Left(CompileError(location, "Can't use array as condition"))
        case ExpressionKind.EByteArray(values) => Left(CompileError(location, "Can't use array as condition"))
        case ExpressionKind.EIntArray(values) => Left(CompileError(location, "Can't use array as condition"))
        case ExpressionKind.ELongArray(values) => Left(CompileError(location, "Can't use array as condition"))
        case ExpressionKind.ECompound(values) => Left(CompileError(location, "Can't use compound as condition"))
        case ExpressionKind.EStorage(_) | ExpressionKind.EMacro(_) =>
          compiler.copyToScoreboard(code, this, namespace).map: scoreboard =>
            Condition.And(Condition.Match(scoreboard, MatchRange.Range(Some(Int.MinValue), Some(Int.MaxValue))), Condition.Inverted(Condition.Match(scoreboard, MatchRange.Single(0))))
        case ExpressionKind.ESubString(loc, start, end) => Left(CompileError(location, "Can't use string as condition"))
        case ExpressionKind.EScoreboard(loc) =>
          // if score {scoreboard} matches (the entire int range) unless score {scoreboard} matches 0
          // Do this so an unset scoreboard is ALWAYS considered false
          Right(Condition.And(Condition.Match(loc, MatchRange.Range(Some(Int.MinValue), Some(Int.MaxValue))), Condition.Inverted(Condition.Match(loc, MatchRange.Single(0)))))
        case ExpressionKind.ECondition(cond) => Right(cond)




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
        case ExpressionKind.EArray(values, nbtType) => ???
        case ExpressionKind.EByteArray(values) => ???
        case ExpressionKind.EIntArray(values) => ???
        case ExpressionKind.ELongArray(values) => ???
        case ExpressionKind.ECompound(values) => ???
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
      Builtin.sideEffect("scoreboard") { (compiler, pos, args, location) => {
        args match
          case List(Expr.ZVariable(_, path)) =>
            Right((ResourceLocation.resolveResource(location, path), "dummy"))
          case List(Expr.ZVariable(_, path), Expr.ZString(_, crit)) =>
            Right((ResourceLocation.resolveResource(location, path), crit))
          case _ =>
            Left(CompileError(pos, "Expected a path and optionally a criteria type."))
      }.map { (score, criteria) =>
        compiler.useScoreboard(ScoreboardLocation.scoreboardStringOf(score), criteria)
      }
      },
      Builtin.exprOnly("reset") { (compiler, pos, args) => context ?=>
        {
          args match
            case List(Expr.ZString(_, name), Expr.ZVariable(_, path)) =>
              Right((name, path))
            case _ =>
              Left(CompileError(pos, "Expected a name and a path"))
        }.map { (name, score) =>
          val scoreboardLoc = ScoreboardLocation(ResourceLocation.resolveResource(context.location, score), name)
          context.code.append(mcfunc"scoreboard players reset ${scoreboardLoc}")

          Expression.void(pos)
        }
      },
      Builtin.exprOnly("enable") { (compiler, pos, args) => context ?=>
        args match
          case List(Expr.ZString(_, name), Expr.ZVariable(_, score)) =>
            val scoreboardLoc = ScoreboardLocation(ResourceLocation.resolveResource(context.location, score), name)
            context.code.append(mcfunc"scoreboard players enable ${scoreboardLoc}")

            Right(Expression.void(pos))
          case _ =>
            Left(CompileError(pos, "Expected a name and a path."))


      },
      Builtin.exprOnly("condition") { (compiler, pos, args) => context ?=>
        args match
          case List(Expr.ZString(_, checkCode)) =>
            Right(Expression(pos, false, ExpressionKind.ECondition(Condition.Check(checkCode))))
          case _ =>
            Left(CompileError(pos, "Expected check code (the bit that comes after `if` in execute commands)"))
      },
      Builtin.insertOnly("scoreboard_string") { (compiler, pos, args) => context ?=>
        args match
          case List(Expr.ZVariable(_, path)) =>
            val resolved = ResourceLocation.resolveResource(context.location, path)
            Right(ScoreboardLocation.scoreboardStringOf(resolved))
          case _ =>
            Left(CompileError(pos, "Expected path"))

      }
    ).map(it => (it.name, it)).toMap

  trait Builtin:
    val name: String

    def expr(compiler: Compiler, pos: util.Location, call: ast.BuiltinCall)(using context: FuncContext): Either[CompileError, Expression] =
      Left(CompileError(pos, s"The $name builtin doesn't work in expressions"))

    def inserted(compiler: Compiler, pos: util.Location, call: ast.BuiltinCall)(using context: FuncContext): Either[CompileError, String] =
      Left(CompileError(pos, s"The $name builtin doesn't work in inserts"))

    def decl(compiler: Compiler, pos: util.Location, call: ast.BuiltinCall, location: ResourceLocation): Either[CompileError, Unit] =
      Left(CompileError(pos, s"The $name builtin doesn't work at toplevel"))

  object Builtin:
    // Side effect that can be in Expr or Decl position
    def sideEffect(nameArg: String)(func: (compiler: Compiler, pos: util.Location, args: List[ast.Expr], location: ResourceLocation) => Either[CompileError, Unit]): Builtin =
      new Builtin:
        override val name: String = nameArg

        override def expr(compiler: Compiler, pos: Location, call: ast.BuiltinCall)(using context: FuncContext): Either[CompileError, Expression] =
          func(compiler, pos, call.args, context.location).map(_ => Expression.void(pos))


        override def decl(compiler: Compiler, pos: Location, call: ast.BuiltinCall, location: ResourceLocation): Either[CompileError, Unit] =
          func(compiler, pos, call.args, location)

    def insertOnly(nameArg: String)(func: (Compiler, util.Location, List[ast.Expr]) => FuncContext ?=> Either[CompileError, String]): Builtin =
      new Builtin:
        override val name: String = nameArg


        override def inserted(compiler: Compiler, pos: Location, call: ast.BuiltinCall)(using context: FuncContext): Either[CompileError, String] =
          func(compiler, pos, call.args)


    def exprOnly(nameArg: String)(func: (Compiler, util.Location, List[ast.Expr]) => FuncContext ?=> Either[CompileError, Expression]): Builtin =
      new Builtin:
        override val name: String = nameArg

        override def expr(compiler: Compiler, pos: Location, call: ast.BuiltinCall)(using context: FuncContext): Either[CompileError, Expression] =
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
                  case (l, ECKnown(r)) =>
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
                    ECCheck(s"${left} ${right}")
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




    def compile(compiler: Compiler, code: mutable.ArrayBuffer[String], namespace: String, inverted: Boolean): Either[CompileError, EvaluatedCondition] =
      import EvaluatedCondition.Check as ECCheck
      import EvaluatedCondition.Known as ECKnown
      this.compileFlat(inverted) match
        case Some(v) => Right(v)
        // we couldn't make a oneliner out of this one : (
        case _ =>
          this match
            case Condition.Or(l, r) =>
              if inverted then
                Condition.And(Condition.Inverted(l), Condition.Inverted(r)).compile(compiler, code, namespace, false)
              else
                l.compile(compiler, code, namespace, false).flatMap:
                  case ECKnown(true) => Right(ECKnown(true))
                  case ECKnown(false) =>
                    r.compile(compiler, code, namespace, false)
                  case ECCheck(x) =>
                    r.compile(compiler, code, namespace, false).flatMap:
                      case ECKnown(true) => Right(ECKnown(true))
                      case ECKnown(false) => Right(ECCheck(x))
                      case ECCheck(y) =>
                        val var1 = compiler.nextScoreboard(namespace)
                        compiler.setScoreboard(code, var1, Expression(util.Location.blank, false, ExpressionKind.EBoolean(false))).map: _ => 
                          code.append(mcfunc"execute ${x} run scoreboard players set ${var1} 1")
                          code.append(mcfunc"execute ${y} run scoreboard players set ${var1} 1")
                          ECCheck(mcfunc"if score ${var1} matches 1")

                      
            case Condition.And(l, r) =>
              if inverted then
                Condition.Or(Condition.Inverted(l), Condition.Inverted(r)).compile(compiler, code, namespace, false)
              else
                l.compile(compiler, code, namespace, false).flatMap:
                  case ECKnown(false) => Right(ECKnown(false))
                  case ECKnown(true) =>
                    r.compile(compiler, code, namespace, false)
                  case ECCheck(x) =>
                    r.compile(compiler, code, namespace, false).map:
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
                    val code: mutable.ArrayBuffer[String] = mutable.ArrayBuffer(),
                    val isNested: Boolean = false,
                    var hasMacroArgs: Boolean = false,
                    val nestInfo: Option[NestedInfo] = None):



    def plain: FuncContext =
      FuncContext(location, returnType,
        hasNestedReturns = this.hasNestedReturns,
        hasNestedContinue = this.hasNestedContinue,
        isNested = isNested,
        hasMacroArgs = hasMacroArgs,
        code = code,
        nestInfo = nestInfo)

    def nested(kind: NestKind, actualLocation: ResourceLocation, label: Option[String]): FuncContext =
      FuncContext(location, returnType,
        hasNestedReturns = this.hasNestedReturns,
        hasNestedContinue = this.hasNestedContinue,
        isNested = true,
        hasMacroArgs = hasMacroArgs,
        nestInfo = Some(NestedInfo(kind, nestInfo, actualLocation, label)))


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
    def generate(path: String): Unit =
      val rootPath = Path.of(path)
      Using(Files.walk(rootPath)): walk =>
        walk.sorted(Comparator.reverseOrder())
          .map(_.toFile)
          .forEach(_.delete(): Unit)
      .get

      val workingPath = rootPath.resolve("data")
      Files.createDirectories(workingPath)

      val mcmeta = MCMeta("48", "").asJson.spaces4

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

  def nextCounter(name: String): Int =
    if counters.contains(name) then
      counters(name) += 1
      counters(name)
    else
      counters(name) = 0
      0

  def nextFunction(funcType: String, namespace: String): ResourceLocation =
    ResourceLocation("ziglin", List("generated", namespace, funcType, s"fn_${nextCounter(s"function:${funcType}")}"), ResourceKind.Func)
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
    private def registerNamespace(ns: parser.ast.Namespace, parentScope: Int): Unit =
      val index = pushScope(ns.name, parentScope)

      val resource = ResourceLocation(ns.name, List(), ResourceKind.Module)

      ns.items.foreach: decl =>
        registerItem(decl, resource, index)

    def apply(nses: List[ast.Namespace]): Unit =
      scopes.append(Compiler.Scope(0))
      nses.foreach: ns =>
        registerNamespace(ns, 0)

    private def registerItem(item: parser.ast.Decl, location: ResourceLocation, parentScope: Int): Unit = {
      import parser.ast.Decl.*
      item match
        case Module(_, name, items) => registerModule(name, items, location, parentScope)
        case IncludedItems(_, _, items) => items.foreach(item => registerItem(item, location, parentScope))
        case ZFunction(_, returnType, name, params, stmts) => registerFunction(returnType, name, params, location, parentScope)
        case ZResource(_, _, _, _) => ()
        case ZBuiltinCall(_, _) => ()
    }

    private def registerModule(name: String, items: List[parser.ast.Decl], location: ResourceLocation, parentScope: Int): Unit = {
      val index = pushScope(name, parentScope)
      val newLoc = location.copy(modules = location.modules.appended(name))
      items.foreach: item =>
        registerItem(item, newLoc, index)
    }

    private def registerFunction(returnType: ReturnType, name: String, params: List[Parameter], location: ResourceLocation, parentScope: Int): Unit = {
        val functionLocation = location.withName(name)
        val functionPath = functionLocation.toString

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

  def addItem(location: ResourceLocation, item: FileTree.Item): Either[CompileError, Unit] =
    val items = getLocation(location)
    items.toList.traverseVoid: i =>
      (i, item) match
        case (FileTree.Item.ZFunction(name, _, _), FileTree.Item.ZFunction(name2, _, loc)) if name == name2 =>
          Left(CompileError(loc, s"Function \"${name2}\" is already defined."))
        case (a: FileTree.Item.ZTextResource, b: FileTree.Item.ZTextResource) if a == b =>
          Left(CompileError(b.location, s"${b.kind} \"${b.name}\" is already defined"))
        case _ => Right(())
    .map: _ =>
      items.append(item)

  def compileItem(ast: parser.ast.Decl, location: ResourceLocation): Either[CompileError, Unit] =
    import parser.ast.Decl.*
    ast match
      case func: ZFunction => compileAstFunction(func, location)
      case module: parser.ast.Decl.Module => compileModule(module, location)
      case incl: IncludedItems => incl.items.traverseVoid(it => compileItem(it, location))
      case resource: ZResource => compileResource(resource, location)
      case ZBuiltinCall(pos, call) => builtins.compileDecl(pos, call, location)

  def compileResource(resource: ZResource, location: ResourceLocation): Either[CompileError, Unit] =
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


  private def compileAstFunction(func: parser.ast.Decl.ZFunction, location: ResourceLocation): Either[CompileError, Unit] =
    val fnLocation = location.withName(func.name)
    val hasMacroArgs = func.params.exists(_.kind == ParameterKind.Macro)
    val context = FuncContext(fnLocation, func.returnType)
    context.hasMacroArgs = hasMacroArgs
    // TODO comptime
    compileBlock(func.stmts)(using context).flatMap { _ =>
      addFunctionItem(func.pos, context.location, context.code.toList)
    }
    // TODO: comptime



  private def addFunctionItem(location: util.Location, fnLocation: ResourceLocation, commands: List[String]): Either[CompileError, Unit] =
    val (module, name) = fnLocation.trySplit.get
    val function = FileTree.Item.ZFunction(name, commands, location)
    addItem(module, function)

  private def compileBlock(block: List[parser.ast.Stmt])(using context: FuncContext): Either[CompileError, Unit] =
    block.traverseVoid: stmt =>
      compileStatement(stmt)


  private def compileIfStatementWithoutChild(condition: parser.ast.Expr, body: List[parser.ast.Stmt], isChild: Boolean)(using context: FuncContext): Either[CompileError, Unit] =
    for {
      condExpr <- compileExpression(condition, false)
      cond <- condExpr.toCondition(this, context.code, context.location.namespace)
      // If it returns a EvaluatedCondition.Known, it should NEVER append code to our context
      evaluatedCondition <- cond.compile(this, context.code, context.location.namespace, false)
      _ <-
        evaluatedCondition match
          case EvaluatedCondition.Known(false) => Right(())
          case EvaluatedCondition.Known(true) =>
            compileBlock(body)
          case EvaluatedCondition.Check(checkCode) =>
            val parameterStorage = context.location
            val func = nextFunction("if", context.location.namespace)
            val subContext = context.nested(NestKind.Block, func, None)
            for {
              _ <- compileBlock(body)(using subContext)
              command <-
                subContext.code.length match
                  case 0 => Right("")
                  case 1 if !subContext.hasNestedContinue.value =>
                    Right(subContext.code(0))
                  case _ =>
                    addFunctionItem(util.Location.blank, func, subContext.code.toList).map: _ =>
                      if subContext.hasMacroArgs then
                        mcfunc"function ${func} with storage ${parameterStorage}"
                      else
                        mcfunc"function ${func}"
            } yield {
              if command.nonEmpty then
                val executeCommand = s"execute ${checkCode} ${if isChild then "run return run" else "run"} ${command}"
                context.code.append(executeCommand) 
            }
              
    } yield ()


  def compileIfStatement(ifStatement: parser.ast.IfStatement)(using context: FuncContext): Either[CompileError, Unit] =
    ifStatement.child match
      case Some(child) =>
        val ifFunc = nextFunction("if", context.location.namespace)

        val parameterStorage = context.location
        if context.hasMacroArgs then
          context.code.append(mcfunc"function ${ifFunc} with storage ${parameterStorage}")
        else
          context.code.append(mcfunc"function ${ifFunc}")

        val subContext = context.nested(NestKind.Block, ifFunc, None)

        var ifStmt = ifStatement
        def whileMethod(): Either[CompileError, Unit] = {
          while true do
            compileIfStatementWithoutChild(ifStmt.cond, ifStmt.block, true)(using subContext) match
              case Left(err) => return Left(err)
              case _ => ()
            ifStmt.child match
              case Some(ElseStatement.EIfStatement(eif)) =>
                ifStmt = eif
              case Some(ElseStatement.Block(block)) =>
                return compileBlock(block)(using subContext)
              case None => return Right(())
          Right(())
        }
        whileMethod().flatMap { _ =>
          val (module, name) = ifFunc.trySplit.get

          addItem(module, Item.ZFunction(name, subContext.code.toList, util.Location.blank))
        }




      case None =>
        compileIfStatementWithoutChild(ifStatement.cond, ifStatement.block, false)

  def compileLoop(pos: util.Location, self: ResourceLocation, body: List[ast.Stmt])(using context: FuncContext): Either[CompileError, Unit] =
    val loopContext = context.nestInfo.flatMap(_.currentLoopContext).getOrElse(throw InternalError(pos, "INTERNAL ERROR: When compiling a loop, there should be a loop context"))
    val first =
      loopContext.condition match
        case Some(conditionAstExpr) =>
          for {
            conditionExpr <- compileExpression(conditionAstExpr, false)
            condition <- conditionExpr.toCondition(this, context.code, context.location.namespace)
            evaluatedCondition <- condition.compile(this, context.code, context.location.namespace, inverted = true)
          } yield {
            evaluatedCondition match
              case EvaluatedCondition.Known(false) => false
              case EvaluatedCondition.Known(true) => true
              case EvaluatedCondition.Check(checkCode) =>
                context.code.append(s"execute ${checkCode} run return 0")
                true
          }
        case _ => Right(true)

    first.flatMap { f =>
      if f then
        compileBlock(body).flatMap { _ =>
          loopContext.continueExpr.traverse: continueExpr =>
            compileExpression(continueExpr, true)
          .flatMap { _ =>
            context.code.append(mcfunc"function $self")

            addFunctionItem(util.Location.blank, self, context.code.toList)
          }
        }
      else
        Right(())

    }

  def compileForLoop(pos: util.Location, forLoop: ast.Stmt.ZFor)(using context: FuncContext): Either[CompileError, Unit] =
    val func = nextFunction("for", context.location.namespace)
    val loopContext =
      forLoop.range match
        case ForRange.Single(n) =>
          compileAssignment(forLoop.variable, Expr.ZInt(util.Location.blank, 0)).map: _ =>
            LoopContext(Some(Expr.Binop(util.Location.blank, ast.BinopKind.Less, forLoop.variable, n)), Some(Expr.Binop(util.Location.blank, ast.BinopKind.AddAssign, forLoop.variable, Expr.ZInt(util.Location.blank, 1))), func)
        case ForRange.Range(min, inclusive, max) =>
          compileAssignment(forLoop.variable, min).map: _ =>
            LoopContext(Some(Expr.Binop(util.Location.blank, if inclusive then ast.BinopKind.LessEq else ast.BinopKind.Less, forLoop.variable, max)), Some(Expr.Binop(util.Location.blank, ast.BinopKind.AddAssign, forLoop.variable, Expr.ZInt(util.Location.blank, 1))), func)


    loopContext.flatMap: loopContext =>
      val subContext = context.nested(NestKind.Loop(loopContext), func, None)
      compileLoop(pos, func, forLoop.body)(using subContext).map: _ =>
        context.code.append(mcfunc"function $func")



  def compileWhileLoop(whileLoop: parser.ast.Stmt.ZWhile)(using context: FuncContext): Either[CompileError, Unit] =
    val func = nextFunction("while", context.location.namespace)
    val subContext = context.nested(NestKind.Loop(LoopContext(Some(whileLoop.cond), whileLoop.continueExpr, func)), func, None)


    compileLoop(whileLoop.cond.pos, func, whileLoop.body)(using subContext).map: _ =>
      context.code.append(mcfunc"function $func")


  def compileStatement(statement: parser.ast.Stmt)(using context: FuncContext): Either[CompileError, Unit] =
    statement match
      case Stmt.Eval(_, expr) => compileExpression(expr, true).void
      case x: Stmt.Command =>
        compileCommand(x).map(cmd => context.code.append(cmd))

      case Stmt.ZIf(pos, ifStatement) =>
        val subContext = context.plain
        subContext.hasNestedReturns = util.Box(false)
        subContext.hasNestedContinue = util.Box(false)
        compileIfStatement(ifStatement)(using subContext).flatMap { _ =>
          if subContext.hasNestedReturns.value then
            context.hasNestedReturns.value = true
            generateNestedReturn()
          if subContext.hasNestedContinue.value then
            context.hasNestedContinue.value = true
            generateNestedContinue()
          else
            Right(())
        }


      case s: Stmt.ZWhile =>
        val subContext = context.plain
        subContext.hasNestedReturns = util.Box(false)
        subContext.hasNestedContinue = util.Box(false)
        compileWhileLoop(s)(using subContext).map: _ =>
          if subContext.hasNestedReturns.value then
            context.hasNestedReturns.value = true
            generateNestedReturn()
        // Right now we don't actually check nested continues here. They are only for if statement to not fuck it up
        // When labelled continues are implemented, then it'll have to be checked
      case s: Stmt.ZFor =>
        val subContext = context.plain
        subContext.hasNestedReturns = util.Box(false)
        subContext.hasNestedContinue = util.Box(false)
        compileForLoop(statement.pos, s)(using subContext).map: _ =>
          if subContext.hasNestedReturns.value then
            context.hasNestedReturns.value = true
            generateNestedReturn()
      case Stmt.ZReturn(pos, expr) => compileReturn(pos, expr)
      case Stmt.ZContinue(pos) =>
        compileContinue(pos)
      case Stmt.ZBreak(_) => ???

  object internals:
    // TODO: do this idiomatically
    lazy val resetDirectReturn: ResourceLocation = {
      val location = ResourceLocation.function("ziglin", List("internal", "0.1.0", "reset_return"))
      addFunctionItem(util.Location.blank, location, List(
        // TODO: better namespace for the "applies to everything" than minecraft?
        "scoreboard players operation $temp_return ziglin.internal.minecraft.vars = $should_return ziglin.internal.minecraft.vars",
        "scoreboard players reset $should_return ziglin.internal.minecraft.vars",
        "return run scoreboard players get $temp_return ziglin.internal.minecraft.vars"
      )).getOrElse(throw InternalError(util.Location.blank, "We should ALWAYS be able to define reset_return once"))
      location
    }
    def continueCommands(loop: ResourceLocation): List[String] =
      List(
        mcfunc"scoreboard players reset $$should_continue ziglin.internal.${ScoreboardLocation.scoreboardStringOf(loop)}.vars",
        mcfunc"return run function $loop"
      )

  def generateNestedContinue()(using context: FuncContext): Either[CompileError, Unit] =
    // When a continue is compiled, it SHOULD:tm: already check the nestInfo
    val loopContext = context.nestInfo.get.currentLoopContext.get
    val scoreboardString = ScoreboardLocation.scoreboardStringOf(loopContext.location)
    useScoreboard(s"ziglin.internal.$scoreboardString.vars")
    context.nestInfo.get.kind match
      case NestKind.Loop(loopContext2) =>
        assert(loopContext2 == loopContext)
        context.hasNestedContinue.value = false
        val commands = internals.continueCommands(loopContext.location)
        val fn = nextFunction("continue", context.location.namespace)
        addFunctionItem(util.Location.blank, fn, commands).map: _ =>
          context.code.append(
            mcfunc"execute if score $$should_continue ziglin.internal.${scoreboardString}.vars matches ${Int.MinValue}..${Int.MaxValue} run return run function ${fn}"
          )
      case _ =>
        Right:
          context.code.append(
            s"execute if score $$should_continue ziglin.internal.${scoreboardString}.vars matches ${Int.MinValue}..${Int.MaxValue} run return 0"
          )

  def generateNestedReturn()(using context: FuncContext): Unit =
    val returnCommand =
      context.returnType match
        case ReturnType.Storage | ReturnType.Scoreboard if context.isNested => "return 0"
        case ReturnType.Storage | ReturnType.Scoreboard =>
          s"return run scoreboard players reset $$should_return ziglin.internal.minecraft.vars"
        case ReturnType.Direct =>
          mcfunc"return run function ${internals.resetDirectReturn}"
    context.code.append(
      s"execute if score $$should_return ziglin.internal.minecraft.vars matches ${Int.MinValue}..${Int.MaxValue} run $returnCommand"
    )

  def cleanCommandString(str: String): String =
    str.split(raw"\r?\n\w*").mkString(" ")

  object insertedExpr:
    def compile(part: CommandPart.Inserted)(using context: FuncContext): Either[CompileError, (String, Boolean)] =
      part.expr match
        case InsertedExpr.MacroVariable(_, name) =>
          Right((s"$$(__${name})", true))
        case InsertedExpr.ScoreboardVariable(_, path) =>
          val scoreboard = ScoreboardLocation.resolveResource(context.location, path)
          Right((scoreboard.mcdisplay, false))
        case InsertedExpr.ResourceRef(_, path) =>
          val resolved = ResourceLocation.resolveResource(context.location, path)
          Right((resolved.mcdisplay, false))
        case InsertedExpr.ZBlock(pos, mayBeInlined, stmts) =>
          val func = nextFunction("block", context.location.namespace)
          val subContext = context.nested(NestKind.Block, func, None)
          compileBlock(stmts)(using subContext).flatMap { _ =>
            subContext.code.length match
              case 0 => Left(CompileError(pos, "Inserted blocks must have at least one statement"))
              case 1 if mayBeInlined =>
                Right((subContext.code.head, false))
              case _ =>
                addFunctionItem(util.Location.blank, func, subContext.code.toList).map: _ =>
                  (mcfunc"function ${func}", false)
          }

        case InsertedExpr.ZBuiltinCall(pos, call) =>
          builtins.compileInserted(pos, call).map((_, false))


  def compileCommand(command: parser.ast.Stmt.Command)(using context: FuncContext): Either[CompileError, String] =
    // : )
    command.parts.foldM(("", false)) {
      case ((res, needsMacro), CommandPart.Literal(str)) =>
        Right((res + cleanCommandString(str), needsMacro))
      case ((res, needsMacro), inserted: CommandPart.Inserted) =>
        insertedExpr.compile(inserted).map { (compiled, insertNeedsMacro) =>
          (res + compiled, needsMacro || insertNeedsMacro)
        }
    }.map { (res, needsMacro) =>
      if needsMacro && !res.startsWith("$") then
        "$" + res
      else
        res
    }





  def compileNot(pos: util.Location, value: parser.ast.Expr)(using context: FuncContext): Either[CompileError, Expression] =
    for {
      operand <- compileExpression(value, false)
      needsMacro = operand.needsMacro
      condition <- operand.toCondition(this, context.code, context.location.namespace)
    } yield Expression(pos, needsMacro, ExpressionKind.ECondition(Condition.Inverted(condition)))


  def compileNegate(pos: util.Location, value: parser.ast.Expr)(using context: FuncContext): Either[CompileError, Expression] =
    for {
      operand <- compileExpression(value, false)
      kind <-
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
               | ExpressionKind.EBoolean(_) => Left(CompileError(pos, "Can only negate numbers"))
          case ExpressionKind.EByte(b) =>
            Right(ExpressionKind.EByte((-b).toByte))
          case ExpressionKind.EShort(s) =>
            Right(ExpressionKind.EShort((-s).toShort))
          case ExpressionKind.EInteger(i) =>
            Right(ExpressionKind.EInteger(-i))
          case ExpressionKind.ELong(l) =>
            Right(ExpressionKind.ELong(-l))
          case ExpressionKind.EFloat(f) =>
            Right(ExpressionKind.EFloat(-f))
          case ExpressionKind.EDouble(d) =>
            Right(ExpressionKind.EDouble(-d))
          case ExpressionKind.EStorage(loc) =>
            val tempStorage = nextStorage(context.location.namespace)
            context.code.append(
              mcfunc"${if operand.needsMacro then "$" else ""}execute store result storage ${tempStorage} int -1 run data get ${loc}"
            )
            Right(ExpressionKind.EStorage(tempStorage))
          case ExpressionKind.EScoreboard(loc) =>
            val tempStorage = nextStorage(context.location.namespace)
            context.code.append(
              mcfunc"${if operand.needsMacro then "$" else ""}execute store result storage ${tempStorage} int -1 run scoreboard players get ${loc}"
            )
            Right(ExpressionKind.EStorage(tempStorage))
          case ExpressionKind.EMacro(_) =>
            copyToStorage(context.code, operand, context.location.namespace).map: tempStorage =>
              context.code.append(
                mcfunc"execute store result ${tempStorage} int -1 run data get storage ${tempStorage}"
              )
              ExpressionKind.EStorage(tempStorage)
    } yield Expression(pos, operand.needsMacro, kind)

  def compileUnaryExpression(expr: parser.ast.Expr.Unary)(using context: FuncContext): Either[CompileError, Expression] =
    expr.kind match
      case UnaryKind.Not => compileNot(expr.pos, expr.expr)
      case UnaryKind.Negate => compileNegate(expr.pos, expr.expr)

  def compileNumericOperation(left: parser.ast.Expr, operator: ScoreboardOperation, right: parser.ast.Expr)(using context: FuncContext): Either[CompileError, Expression] =
    for {
      l <- compileExpression(left, false)
      r <- compileExpression(right, false)
      needsMacro = l.needsMacro || r.needsMacro
      kind <-
        (l.kind, r.kind) match
          case (ExpressionKind.Numeric(lv), ExpressionKind.Numeric(rv)) =>
            Right(ExpressionKind.EInteger(operator.constantOp(lv, rv)))
          case (ExpressionKind.Numeric(_), _) if operator.commutative =>
            for {
              scoreboard <- copyToScoreboard(context.code, r, context.location.namespace)
              _ <- scoreboardOperation(scoreboard, l, operator)
            } yield ExpressionKind.EScoreboard(scoreboard)
          case _ =>
            for {
              scoreboard <- copyToScoreboard(context.code, l, context.location.namespace)
              _ <- scoreboardOperation(scoreboard, r, operator)
            } yield ExpressionKind.EScoreboard(scoreboard)
    } yield Expression(left.pos, needsMacro, kind)



  def compileOperatorAssignment(left: parser.ast.Expr, operator: ScoreboardOperation, right: parser.ast.Expr)(using context: FuncContext): Either[CompileError, Expression] =
    left match
      case Expr.ZScoreboardVariable(_, path) =>
        for {
          l <- compileExpression(left, false)
          r <- compileExpression(right, false)
          scoreboard = ScoreboardLocation.resolveResource(context.location, path)
          _ = useScoreboard(scoreboard.scoreboardString)
          _ <- scoreboardOperation(scoreboard, r, operator)
        } yield l
      case _ =>
        compileAssignment(left, parser.ast.Expr.Binop(right.pos, operator.binopKind, left, right))


  def compileAssignment(left: parser.ast.Expr, right: parser.ast.Expr)(using context: FuncContext): Either[CompileError, Expression] =
    left match
      case Expr.ZVariable(_, path) =>
        for {
          l <- compileExpression(left, false)
          r <- compileExpression(right, false)
          storage = StorageLocation.resolveResource(context.location, path)
          _ <- setStorage(context.code, storage, r)
        } yield l
      case Expr.ZScoreboardVariable(_, path) =>
        for {
          l <- compileExpression(left, false)
          r <- compileExpression(right, false)
          scoreboard = ScoreboardLocation.resolveResource(context.location, path)
          _ <- setScoreboard(context.code, scoreboard, r)
        } yield {
          useScoreboard(scoreboard.scoreboardString)
          l
        }
      case _ => Left(CompileError(left.pos, "Can only assign to a variable"))


  def compileMatchComparison(code: mutable.ArrayBuffer[String], value: Expression, range: MatchRange, namespace: String): Either[CompileError, ExpressionKind] =
    moveToScoreboard(code, value, namespace).map: scoreboard =>
      ExpressionKind.ECondition(Condition.Match(scoreboard, range))

  def storageComparison(code: mutable.ArrayBuffer[String], left: Expression, right: Expression, checkEquality: Boolean, namespace: String): Either[CompileError, ExpressionKind] =
    (moveToStorage(code, right, namespace), copyToStorage(code, left, namespace)).mapN: (rightStorage, tempStorage) =>

      val conditionScoreboard = nextScoreboard(namespace)
      code.append(
        mcfunc"execute store success score ${conditionScoreboard} run data modify storage ${tempStorage} set from storage ${rightStorage}"
      )
      ExpressionKind.ECondition(Condition.Match(conditionScoreboard, MatchRange.Single(if checkEquality then 0 else 1)))

  def compileNotEquals(left: parser.ast.Expr, right: parser.ast.Expr)(using context: FuncContext): Either[CompileError, Expression] =

    (compileExpression(left, false), compileExpression(right, false)).flatMapN { (l, r) =>
      val needsMacro = l.needsMacro || r.needsMacro
      l.valueEqual(r) match
        case Some(equal) =>
          Right(Expression(left.pos, false, ExpressionKind.EBoolean(equal)))
        case _ => {
          (l.kind, r.kind) match
            case (ExpressionKind.EVoid, _) | (_, ExpressionKind.EVoid) =>
              Left(CompileError(left.pos, "Cannot compare with void."))
            case (ExpressionKind.EStorage(_), _) | (_, ExpressionKind.EStorage(_)) =>
              storageComparison(context.code, l, r, false, context.location.namespace)
            case (leftKind, rightKind) if leftKind.nbtType.numeric && rightKind.nbtType.numeric =>
              (moveToScoreboard(context.code, l, context.location.namespace), moveToScoreboard(context.code, r, context.location.namespace)).mapN: (leftScore, rightScore) =>
                ExpressionKind.ECondition(Condition.Inverted(Condition.Eq(leftScore, rightScore)))
            case _ =>
              storageComparison(context.code, l, r, false, context.location.namespace)
        }.map(kind => Expression(left.pos, needsMacro, kind))
    }



  def compileEquals(left: parser.ast.Expr, right: parser.ast.Expr)(using context: FuncContext): Either[CompileError, Expression] =
    (compileExpression(left, false), compileExpression(right, false)).flatMapN { (l, r) =>
      val needsMacro = l.needsMacro || r.needsMacro
      l.valueEqual(r) match
        case Some(equal) =>
          Right(Expression(left.pos, false, ExpressionKind.EBoolean(equal)))
        case _ => {
          (l.kind, r.kind) match
            case (ExpressionKind.EVoid, _) | (_, ExpressionKind.EVoid) =>
              Left(CompileError(left.pos, "Cannot compare with void."))
            case (ExpressionKind.EStorage(_), _) | (_, ExpressionKind.EStorage(_)) =>
              storageComparison(context.code, l, r, true, context.location.namespace)
            case (ExpressionKind.Numeric(v), _) =>
              compileMatchComparison(context.code, r, MatchRange.Single(v), context.location.namespace)
            case (_, ExpressionKind.Numeric(v)) =>
              compileMatchComparison(context.code, l, MatchRange.Single(v), context.location.namespace)
            case (leftKind, rightKind) if leftKind.nbtType.numeric && rightKind.nbtType.numeric =>
              (moveToScoreboard(context.code, l, context.location.namespace), moveToScoreboard(context.code, r, context.location.namespace)).mapN: (leftScore, rightScore) =>
                ExpressionKind.ECondition(Condition.Eq(leftScore, rightScore))
            case _ =>
              storageComparison(context.code, l, r, true, context.location.namespace)
        }.map(kind => Expression(left.pos, needsMacro, kind))
    }


  def compileNumericComparison(left: parser.ast.Expr, right: parser.ast.Expr, comparator: NumericComparison)(using context: FuncContext): Either[CompileError, Expression] =
    (compileExpression(left, false), compileExpression(right, false)).flatMapN { (l, r) => {
      (l.kind, r.kind) match
        case (ExpressionKind.EVoid, _) | (_, ExpressionKind.EVoid) =>
          Left(CompileError(left.pos, "Cannot compare with void."))
        case (ExpressionKind.EBoolean(_), _) | (_, ExpressionKind.EBoolean(_)) =>
          Left(CompileError(left.pos, "Cannot compare with boolean."))
        case (ExpressionKind.EString(_), _) | (_, ExpressionKind.EString(_)) =>
          Left(CompileError(left.pos, "Cannot compare with string."))
        case (ExpressionKind.Numeric(lv), ExpressionKind.Numeric(rv)) =>
          Right(ExpressionKind.EBoolean(comparator.constOp(lv, rv)))
        case (ExpressionKind.Numeric(lv), _) =>
          moveToScoreboard(context.code, r, context.location.namespace).map: scoreboard =>
            ExpressionKind.ECondition(comparator.inverse().halfOperator(scoreboard, lv))
        case (_, ExpressionKind.Numeric(rv)) =>
          moveToScoreboard(context.code, l, context.location.namespace).map: scoreboard =>
            ExpressionKind.ECondition(comparator.halfOperator(scoreboard, rv))
        case _ =>
          (moveToScoreboard(context.code, l, context.location.namespace), moveToScoreboard(context.code, r, context.location.namespace)).mapN: (leftScore, rightScore) =>
            ExpressionKind.ECondition(comparator.operator(leftScore, rightScore))
    }.map(kind => Expression(left.pos, l.needsMacro || r.needsMacro, kind))
    }






  def compileLogicalOr(pos: util.Location, left: parser.ast.Expr, right: parser.ast.Expr)(using context: FuncContext): Either[CompileError, Expression] =
    (compileExpression(left, false), compileExpression(right, false)).flatMapN { (l, r) =>
      (l.toCondition(this, context.code, context.location.namespace), r.toCondition(this, context.code, context.location.namespace)).mapN { (leftCondition, rightCondition) =>
        val kind = ExpressionKind.ECondition(Condition.Or(leftCondition, rightCondition).simplify)

        Expression(pos, l.needsMacro || r.needsMacro, kind)
      }
    }

  def compileLogicalAnd(pos: util.Location, left: parser.ast.Expr, right: parser.ast.Expr)(using context: FuncContext): Either[CompileError, Expression] =
    (compileExpression(left, false), compileExpression(right, false)).flatMapN { (l, r) =>
      (l.toCondition(this, context.code, context.location.namespace), r.toCondition(this, context.code, context.location.namespace)).mapN { (leftCondition, rightCondition) =>
        val kind = ExpressionKind.ECondition(Condition.And(leftCondition, rightCondition).simplify)

        Expression(pos, l.needsMacro || r.needsMacro, kind)
      }
    }

  def compileBinaryExpression(expr: parser.ast.Expr.Binop)(using context: FuncContext): Either[CompileError, Expression] =
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

  def compileFunctionCall(pos: util.Location, functionCall: parser.ast.FunctionCall)(using context: FuncContext): Either[CompileError, (String, CalledFunction)] =
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
    val first = functionDefinition.arguments.traverse: parameter =>
      {
        (argIterator.hasNext, parameter.default) match
          case (true, _) => compileExpression(argIterator.next, false)
          case (false, Some(parameter)) =>
            compileExpression(parameter, false)(using defaultContext).map { expr =>
              context.code.appendAll(defaultContext.code)
              defaultContext.code.clear()
              expr
            }
          case (false, None) => Left(CompileError(pos, "Expected more arguments"))
      }.map { argument =>
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
      }

    first.map { _ =>
      val command =
        if hasMacroArgs then
          mcfunc"function ${functionDefinition.location} with storage ${parameterStorage}"
        else
          mcfunc"function ${functionDefinition.location}"

      (command, CalledFunction(functionDefinition.location, functionDefinition.returnType))
    }


  def compileContinue(pos: util.Location)(using context: FuncContext): Either[CompileError, Unit] =
    context.nestInfo.flatMap { nestInfo =>
      nestInfo.getLoop.map(it => (nestInfo, it))
    }.toRight(CompileError(pos, "continue may only be inside of loops")).map { (nestInfo, curLoop) =>
      val scoreboardString = ScoreboardLocation.scoreboardStringOf(curLoop.actualLocation)
      if !nestInfo.isLoop then
        context.hasNestedContinue.value = true
        context.code.append(
          mcfunc"return run scoreboard players set $$should_continue ziglin.internal.${scoreboardString}.vars 0"
        )
      else
        context.code.append(mcfunc"return run function ${curLoop.actualLocation}")
    }






  def compileReturn(pos: util.Location, value: Option[parser.ast.Expr])(using context: FuncContext): Either[CompileError, Unit] =
    if context.isNested then
      context.hasNestedReturns.value = true
    val hasValue = value.nonEmpty
    for {
      expression <- value.traverse(it => compileExpression(it, false))
      _ <-
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
                  v.toReturnCommand(this, context.code, context.location.namespace).map: it =>
                    context.code.append(it)
          case _ => Right(())
      _ <-
        if context.returnType != ReturnType.Direct && context.isNested then
          setScoreboard(context.code, ScoreboardLocation.internal("minecraft", "$should_return"), Expression(util.Location.blank, false, ExpressionKind.EInteger(1)))
        else
          Right(())
    } yield {

      if hasValue then
        if context.returnType != ReturnType.Direct || context.isNested then
          context.code.append("return 0")
      else
        context.code.append("return fail")
    }


  object builtins:
    def compileDecl(pos: util.Location, call: ast.BuiltinCall, location: ResourceLocation): Either[CompileError, Unit] =
      Compiler.builtins.get(call.name) match
        case Some(v) => v.decl(Compiler.this, pos, call, location)
        case _ => Left(CompileError(pos, s"No such builtin ${call.name}"))


    def compileInserted(pos: util.Location, call: ast.BuiltinCall)(using context: FuncContext): Either[CompileError, String] =
      Compiler.builtins.get(call.name) match
        case Some(v) => v.inserted(Compiler.this, pos, call)
        case _ => Left(CompileError(pos, s"No such builtin ${call.name}"))


    def compile(pos: util.Location, call: ast.BuiltinCall)(using context: FuncContext): Either[CompileError, Expression] =
      Compiler.builtins.get(call.name) match
        case Some(v) => v.expr(Compiler.this, pos, call)
        case _ => Left(CompileError(pos, s"No such builtin ${call.name}"))



  def verifyTypes(kinds: List[Expression], kind: ast.ArrayKind, message: String): Either[CompileError, NbtType] =
    var singleType =
      kind match
        case ArrayKind.Any => NbtType.Unknown
        case ArrayKind.Byte => NbtType.Byte
        case ArrayKind.Int => NbtType.Int
        case ArrayKind.Long => NbtType.Long

    kinds.traverseVoid: kind =>
      (kind.kind, singleType) match
        case (ExpressionKind.EVoid, _) =>
          Left(CompileError(kind.location, "Cannot use void as a value"))
        case (typ, NbtType.Unknown) =>
          singleType = typ.nbtType
          Right(())
        case (t, NbtType.Numeric) if t.nbtType.numeric =>
          singleType = t.nbtType
          Right(())
        case (ExpressionKind.EByte(_), NbtType.Byte) => Right(())
        case (ExpressionKind.EShort(_), NbtType.Short) => Right(())
        case (ExpressionKind.EInteger(_), NbtType.Int) => Right(())
        case (ExpressionKind.ELong(_), NbtType.Long) => Right(())
        case (ExpressionKind.EFloat(_), NbtType.Float) => Right(())
        case (ExpressionKind.EDouble(_), NbtType.Double) => Right(())
        case (ExpressionKind.EStorage(_), _) => Right(())
        case (ExpressionKind.EScoreboard(_), t) if t.numeric => Right(())
        case (ExpressionKind.EBoolean(_), NbtType.Byte) => Right(())
        case (ExpressionKind.EString(_), NbtType.String) => Right(())
        case (ExpressionKind.EArray(_, _), NbtType.List) => Right(())
        case (ExpressionKind.ECondition(_), NbtType.Byte) => Right(())
        case _ =>
          Left(CompileError(kind.location, message))
    .map: _ =>
      if singleType == NbtType.Numeric then
        singleType = NbtType.Int

      singleType
  def compileArray(kind: ast.ArrayKind, expressions: List[ast.Expr], pos: util.Location)(using context: FuncContext): Either[CompileError, Expression] =
    expressions.traverse: expr =>
      compileExpression(expr, false)
    .flatMap: kinds =>
      val errMsg =
        kind match
          case ast.ArrayKind.Any => "Arrays can only contain values of the same type"
          case ast.ArrayKind.Byte => "Byte arrays can only contain byte values"
          case ast.ArrayKind.Int => "Int arrays can only contain int values"
          case ast.ArrayKind.Long => "Long arrays can only contain long values"

      verifyTypes(kinds, kind, errMsg).map: dataType =>

        val exprKind =
          kind match
            case ast.ArrayKind.Any => ExpressionKind.EArray(kinds, dataType)
            case ast.ArrayKind.Byte => ExpressionKind.EByteArray(kinds)
            case ast.ArrayKind.Int => ExpressionKind.EIntArray(kinds)
            case ast.ArrayKind.Long => ExpressionKind.ELongArray(kinds)

        Expression(pos, false, exprKind)

  def compileCompound(pos: util.Location, keyValues: Map[String, ast.Expr])(using context: FuncContext): Either[CompileError, Expression] =
    keyValues.toList.traverse: (key, value) =>
      compileExpression(value, false).map(e => (key, e))
    .map: kvs =>
      Expression(pos, false, ExpressionKind.ECompound(kvs.toMap))



  def compileExpression(expr: ast.Expr, ignored: Boolean)(using context: FuncContext): Either[CompileError, Expression] =
    expr match
      case s @ Expr.Binop(_, name, l, r) => compileBinaryExpression(s)
      case s @ Expr.Unary(_, kind, operand) => compileUnaryExpression(s)
      case Expr.ZString(pos, contents) => Right(Expression(pos, false, ExpressionKind.EString(contents)))
      case Expr.ZByte(pos, num) => Right(Expression(pos, false, ExpressionKind.EByte(num)))
      case Expr.ZShort(pos, num) => Right(Expression(pos, false, ExpressionKind.EShort(num)))
      case Expr.ZInt(pos, num) => Right(Expression(pos, false, ExpressionKind.EInteger(num)))
      case Expr.ZLong(pos, num) => Right(Expression(pos, false, ExpressionKind.ELong(num)))
      case Expr.ZFloat(pos, num) => Right(Expression(pos, false, ExpressionKind.EFloat(num)))
      case Expr.ZDouble(pos, num) => Right(Expression(pos, false, ExpressionKind.EDouble(num)))
      case Expr.ZBool(pos, v) => Right(Expression(pos, false, ExpressionKind.EBoolean(v)))
      case Expr.ZList(pos, kind, values) => compileArray(kind, values, pos)
      case Expr.ZCompound(pos, map) => compileCompound(pos, map)
      case Expr.ZVariable(pos, path) => Right(Expression(pos, false, ExpressionKind.EStorage(StorageLocation.resolveResource(context.location, path))))
      case Expr.ZScoreboardVariable(pos, path) => Right(Expression(pos, false, ExpressionKind.EScoreboard(ScoreboardLocation.resolveResource(context.location, path))))
      case Expr.ZMacroVariable(pos, name) => Right(Expression(pos, true, ExpressionKind.EMacro(StorageLocation(context.location, "__" + name))))
      case Expr.ZBuiltinCall(pos, call) =>
        builtins.compile(pos, call)
      case Expr.ZFunctionCall(pos, functionCall) =>
        compileFunctionCall(pos, functionCall).map { (command, called) =>
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
        }

      case Expr.Atom(pos, expr) => compileExpression(expr, ignored)

  def compileModule(module: parser.ast.Decl.Module, location: ResourceLocation): Either[CompileError, Unit] =
    enterScope(module.name)
    // TODO: comptime

    val newLocation = location.join(module.name)
    module.items.traverseVoid: item =>
      compileItem(item, newLocation)
    .map: _ =>
      exitScope()
    // TODO: comptime
  def compileNamespace(ast: parser.ast.Namespace): Either[CompileError, Unit] =
    loadFunctions.prepend(s"ziglin:generated/${ast.name}/load")
    enterScope(ast.name)
    // TODO: comptime

    val resource = ResourceLocation.module(ast.name, List())

    ast.items.traverseVoid: item =>
      compileItem(item, resource)
    .flatMap: _ =>
      exitScope()
      // TODO: comptime

      val loadCommands = usedScoreboards.map((name, criteria) => s"scoreboard objectives add $name $criteria")

      val loadFunction = FileTree.Item.ZFunction("load", loadCommands.toList, util.Location.blank)

      addItem(ResourceLocation.module("ziglin", List("generated", ast.name)), loadFunction)

  def compileTree(ast: List[parser.ast.Namespace]): Either[CompileError, FileTree] =
    ast.traverseVoid: ns =>
      compileNamespace(ns)
    .flatMap: _ =>
      val loadJson = MinecraftTag(loadFunctions.toList).asJson.spaces4

      val load = FileTree.Item.ZTextResource("load", "tags/function", false, loadJson, util.Location.blank)

      val location = ResourceLocation.module("minecraft", List())


      addItem(location, load).flatMap: _ =>
        if tickFunctions.nonEmpty then
          val tickJson = MinecraftTag(tickFunctions.toList).asJson.spaces4
          val tick = FileTree.Item.ZTextResource("tick", "tags/function", false, tickJson, util.Location.blank)
          addItem(location, tick)
        else
          Right(())
      .map: _ =>
        FileTree(namespaces.values.toList)

  def compile(file: List[parser.ast.Namespace], output: String): Either[CompileError, Unit] =
    register(file)

    compileTree(file).map: tree =>
      tree.generate(output)


  def nextScoreboard(namespace: String): ScoreboardLocation =
    useScoreboard(s"ziglin.internal.${namespace}.vars")
    val nextNum = nextCounter("scoreboard")
    ScoreboardLocation(ResourceLocation("ziglin", List("internal", namespace, "vars"), ResourceKind.Func), s"$$var_${nextNum}")

  def nextStorage(namespace: String): StorageLocation =
    val nextNum = nextCounter("storage")
    StorageLocation(ResourceLocation("ziglin", List("internal", namespace, "vars"), ResourceKind.Func), "var_" + nextNum)

  def constantScoreboard(number: Int): ScoreboardLocation =
    useScoreboard("ziglin.internal.constants")
    constantScoreboardValues += number
    val strRep = if number < 0 then s"neg${math.abs(number)}" else number.toString
    ScoreboardLocation(ResourceLocation("ziglin", List("internal", "constants"), ResourceKind.Func), strRep)


  def copyToStorage(code: mutable.ArrayBuffer[String], value: Expression, namespace: String): Either[CompileError, StorageLocation] =
    val storage = nextStorage(namespace)
    setStorage(code, storage, value).map: _ =>
      storage
  def moveToStorage(code: mutable.ArrayBuffer[String], value: Expression, namespace: String): Either[CompileError, StorageLocation] =
    value.kind match
      case ExpressionKind.EStorage(storage) => Right(storage)
      case _ => copyToStorage(code, value, namespace)


  def setStorage(code: mutable.ArrayBuffer[String], storage: StorageLocation, value: Expression): Either[CompileError, Unit] =
    value.toStorage(this, code, storage, "set", NbtType.Unknown)

  def scoreboardOperation(scoreboard: ScoreboardLocation, value: Expression, operation: ScoreboardOperation)(using context: FuncContext): Either[CompileError, Unit] =
    value.kind match
      case ExpressionKind.EVoid
           | ExpressionKind.EString(_)
           | ExpressionKind.EArray(_, _)
            | ExpressionKind.EByteArray(_)
            | ExpressionKind.EIntArray(_)
            | ExpressionKind.ELongArray(_)
            | ExpressionKind.ESubString(_, _, _)
            | ExpressionKind.ECompound(_) => Left(CompileError(value.location, "Can only perform operations on numbers."))
      case ExpressionKind.Numeric(value) =>
        operation.nativeOperator match
          case Some(native) =>
            context.code.append(mcfunc"scoreboard players $native ${scoreboard} ${value}")
          case None =>
            val const = constantScoreboard(value)
            context.code.append(mcfunc"scoreboard players operation ${scoreboard} ${operation.operator}= ${const}")
        Right(())
      case _ =>
        moveToScoreboard(context.code, value, context.location.namespace).map: otherScoreboard =>
          context.code.append(mcfunc"scoreboard players operation ${scoreboard} ${operation.operator}= ${otherScoreboard}")


  def setScoreboard(code: mutable.ArrayBuffer[String], scoreboard: ScoreboardLocation, value: Expression): Either[CompileError, Unit] =
    value.toScore(this, code, scoreboard.scoreboard.namespace).map { (conversionCode, kind) =>
      kind match
        case ScoreKind.Direct(operation) =>
          code.append(mcfunc"scoreboard players ${operation} ${scoreboard} ${conversionCode}")
        case ScoreKind.DirectMacro(operation) =>
          code.append(mcfunc"$$scoreboard players ${operation} ${scoreboard} ${conversionCode}")
        case ScoreKind.Indirect =>
          code.append(mcfunc"execute store result score ${scoreboard} run ${conversionCode}")
        case ScoreKind.IndirectMacro =>
          code.append(mcfunc"$$execute store result score ${scoreboard} run ${conversionCode}")
    }


  def copyToScoreboard(code: mutable.ArrayBuffer[String], value: Expression, namespace: String): Either[CompileError, ScoreboardLocation] =
    val scoreboard = nextScoreboard(namespace)
    setScoreboard(code, scoreboard, value).map: _ =>
      scoreboard


  def moveToScoreboard(code: mutable.ArrayBuffer[String], value: Expression, namespace: String): Either[CompileError, ScoreboardLocation] =
    value.kind match
      case ExpressionKind.EScoreboard(loc) => Right(loc)
      case _ => copyToScoreboard(code, value, namespace)
