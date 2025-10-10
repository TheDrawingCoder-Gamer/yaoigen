package gay.menkissing.ziglin

import gay.menkissing.ziglin.parser.ast.{ArrayKind, BinopKind, CommandPart, ElseStatement, Expr, ForRange, InsertedExpr, Parameter, ParameterKind, ReturnType, Stmt, UnaryKind, UnresolvedResource}
import util.{Location, ResourceKind, ResourceLocation, ScoreboardLocation, StorageLocation, mcdisplay, given}
import util.MCFunctionDisplay.{mcfunc, given}

import java.util.Comparator
import scala.collection.mutable
import scala.util.Using
import cats.implicits.*
import gay.menkissing.ziglin.Compiler.FileTree.Item
import gay.menkissing.ziglin.parser.ast
import gay.menkissing.ziglin.parser.ast.Decl.ZResource
import io.circe.*
import io.circe.generic.semiauto.*
import io.circe.syntax.*

import java.io.IOException
import java.nio.file.attribute.BasicFileAttributes
import java.nio.file.{FileVisitResult, FileVisitor, Path, SimpleFileVisitor}


object Compiler:
  case class MinecraftTag(values: List[String]) derives Decoder, Encoder
  case class MCMeta(packFormat: String, description: String)

  given Decoder[MCMeta] =
    Decoder.forProduct2("pack_format", "description")(MCMeta.apply)
  given Encoder[MCMeta] =
    Encoder.forProduct2("pack_format", "description")(u =>
      (u.packFormat, u.description)
    )

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

    def toStorage(compiler: Compiler, code: mutable.ArrayBuffer[String], storage: StorageLocation, operation: String, dataType: NbtType): Unit =
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
                   | ExpressionKind.EString(_) => throw CompileError(location, "INTERNAL ERROR: This value should have a compile time string representation")
              case ExpressionKind.EArray(values, nbtType) => ???
              case ExpressionKind.EByteArray(values) => ???
              case ExpressionKind.EIntArray(values) => ???
              case ExpressionKind.ELongArray(values) => ???
              case ExpressionKind.ECompound(values) => ???
              case ExpressionKind.EStorage(loc) =>
                (mcfunc"from storage ${loc}", StorageKind.Modify)
              case ExpressionKind.ESubString(loc, start, end) =>
                (mcfunc"string storage ${loc} ${start}${if end.nonEmpty then " " + end.get.toString else ""}", StorageKind.Modify)
              case ExpressionKind.EScoreboard(loc) =>
                (mcfunc"scoreboard players get ${loc}", StorageKind.Store)
              case ExpressionKind.EMacro(loc) =>
                (mcfunc"value $$(${loc.name})", StorageKind.MacroModify)
              case ExpressionKind.ECondition(cond) =>
                val res = cond.compile(compiler, code, storage.storage.namespace, false)
                res match
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

    def toReturnCommand(compiler: Compiler, code: mutable.ArrayBuffer[String], namespace: String): String =
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
          val evaluated = condition.compile(compiler, code, namespace, false)
          evaluated match
            case EvaluatedCondition.Check(c) => s"return run execute ${c}"
            case EvaluatedCondition.Known(v) => if v then "return 1" else "return 0"


    def toScore(compiler: Compiler, code: mutable.ArrayBuffer[String], namespace: String): (String, ScoreKind) =
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
        case ExpressionKind.EArray(values, nbtType) => throw CompileError(location, "Cannot assign array to scoreboard")
        case ExpressionKind.EByteArray(values) => throw CompileError(location, "Cannot assign array to scoreboard")
        case ExpressionKind.EIntArray(values) => throw CompileError(location, "Cannot assign array to scoreboard")
        case ExpressionKind.ELongArray(values) => throw CompileError(location, "Cannot assign array to scoreboard")
        case ExpressionKind.ECompound(values) => throw CompileError(location, "Cannot assign compound to scoreboard")
        case ExpressionKind.EStorage(loc) => (mcfunc"data get storage ${loc}", ScoreKind.Indirect)
        case ExpressionKind.EScoreboard(loc) => (mcfunc"= ${loc}", ScoreKind.Direct("operation"))
        case ExpressionKind.EMacro(loc) => (s"$$(${loc.name})", ScoreKind.DirectMacro("set"))
        case ExpressionKind.ECondition(cond) =>
          val condStr = cond.compile(compiler, code, namespace, false)
          condStr match
            case EvaluatedCondition.Check(c) => (s"execute ${c}", ScoreKind.Indirect)
            case EvaluatedCondition.Known(b) => (if b then "1" else "0", ScoreKind.Direct("set"))


    def toCondition(compiler: Compiler, code: mutable.ArrayBuffer[String], namespace: String): Condition =
      kind match
        case ExpressionKind.EVoid => throw CompileError(location, "Can't check void")
        case ExpressionKind.EByte(b) => Condition.Known(b != 0)
        case ExpressionKind.EShort(s) => Condition.Known(s != 0)
        case ExpressionKind.EInteger(i) => Condition.Known(i != 0)
        case ExpressionKind.ELong(l) => Condition.Known(l != 0)
        case ExpressionKind.EFloat(f) => Condition.Known(f != 0)
        case ExpressionKind.EDouble(d) => Condition.Known(d != 0)
        case ExpressionKind.EBoolean(b) => Condition.Known(b)
        case ExpressionKind.EString(s) => throw CompileError(location, "Can't use string as condition")
        case ExpressionKind.EArray(values, nbtType) => throw CompileError(location, "Can't use array as condition")
        case ExpressionKind.EByteArray(values) => throw CompileError(location, "Can't use array as condition")
        case ExpressionKind.EIntArray(values) => throw CompileError(location, "Can't use array as condition")
        case ExpressionKind.ELongArray(values) => throw CompileError(location, "Can't use array as condition")
        case ExpressionKind.ECompound(values) => throw CompileError(location, "Can't use compound as condition")
        case ExpressionKind.EStorage(_) | ExpressionKind.EMacro(_) =>
          val scoreboard = compiler.copyToScoreboard(code, this, namespace)
          Condition.And(Condition.Match(scoreboard, MatchRange.Range(Some(Int.MinValue), Some(Int.MaxValue))), Condition.Inverted(Condition.Match(scoreboard, MatchRange.Single(0))))
        case ExpressionKind.ESubString(loc, start, end) => throw CompileError(location, "Can't use string as condition")
        case ExpressionKind.EScoreboard(loc) =>
          // if score {scoreboard} matches (the entire int range) unless score {scoreboard} matches 0
          // Do this so an unset scoreboard is ALWAYS considered false
          Condition.And(Condition.Match(loc, MatchRange.Range(Some(Int.MinValue), Some(Int.MaxValue))), Condition.Inverted(Condition.Match(loc, MatchRange.Single(0))))
        case ExpressionKind.ECondition(cond) => cond




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
      Builtin.sideEffect("scoreboard") { (compiler, pos, args, location) =>
        val (score, criteria) =
          args match
            case List(Expr.Node(Expr.ZVariable(path))) =>
              (ResourceLocation.resolveResource(location, path), "dummy")
            case List(Expr(Expr.ZVariable(path), _), Expr(Expr.ZString(crit), _)) =>
              (ResourceLocation.resolveResource(location, path), crit)
            case _ =>
              throw CompileError(pos, "Expected a path and optionally a criteria type.")

        compiler.useScoreboard(ScoreboardLocation.scoreboardStringOf(score), criteria)
      },
      Builtin.exprOnly("reset") { (compiler, pos, args) => context ?=>
        val (name, score) =
          args match
            case List(Expr.Node(Expr.ZString(name)), Expr.Node(Expr.ZVariable(path))) =>
              (name, path)
            case _ =>
              throw CompileError(pos, "Expected a name and a path.")

        val scoreboardLoc = ScoreboardLocation(ResourceLocation.resolveResource(context.location, score), name)
        context.code.append(mcfunc"scoreboard players reset ${scoreboardLoc}")

        Expression.void(pos)
      },
      Builtin.exprOnly("enable") { (compiler, pos, args) => context ?=>
        val (name, score) =
          args match
            case List(Expr.Node(Expr.ZString(name)), Expr.Node(Expr.ZVariable(path))) =>
              (name, path)
            case _ =>
              throw CompileError(pos, "Expected a name and a path.")

        val scoreboardLoc = ScoreboardLocation(ResourceLocation.resolveResource(context.location, score), name)
        context.code.append(mcfunc"scoreboard players enable ${scoreboardLoc}")

        Expression.void(pos)
      },
      Builtin.exprOnly("condition") { (compiler, pos, args) => context ?=>
        val checkCode =
          args match
            case List(Expr.Node(Expr.ZString(name))) =>
              name
            case _ =>
              throw CompileError(pos, "Expected check code (the bit that comes after `if` in execute commands)")
        Expression(pos, false, ExpressionKind.ECondition(Condition.Check(checkCode)))
      },
      Builtin.insertOnly("scoreboard_string") { (compiler, pos, args) => context ?=>
        val path =
          args match
            case List(Expr.Node(Expr.ZVariable(path))) =>
              path
            case _ =>
              throw CompileError(pos, "Expected path")

        val resolved = ResourceLocation.resolveResource(context.location, path)
        ScoreboardLocation.scoreboardStringOf(resolved)
      }
    ).map(it => (it.name, it)).toMap

  trait Builtin:
    val name: String

    def expr(compiler: Compiler, pos: util.Location, call: ast.BuiltinCall)(using context: FuncContext): Expression

    def inserted(compiler: Compiler, pos: util.Location, call: ast.BuiltinCall)(using context: FuncContext): String

    def decl(compiler: Compiler, pos: util.Location, call: ast.BuiltinCall, location: ResourceLocation): Unit

  object Builtin:
    // Side effect that can be in Expr or Decl position
    def sideEffect(nameArg: String)(func: (compiler: Compiler, pos: util.Location, args: List[ast.Expr], location: ResourceLocation) => Unit): Builtin =
      new Builtin:
        override val name: String = nameArg

        override def expr(compiler: Compiler, pos: Location, call: ast.BuiltinCall)(using context: FuncContext): Expression =
          func(compiler, pos, call.args, context.location)
          Expression.void(pos)

        override def inserted(compiler: Compiler, pos: Location, call: ast.BuiltinCall)(using context: FuncContext): String =
          throw CompileError(pos, s"The $name builtin doesn't work in inserts")

        override def decl(compiler: Compiler, pos: Location, call: ast.BuiltinCall, location: ResourceLocation): Unit =
          func(compiler, pos, call.args, location)

    def insertOnly(nameArg: String)(func: (Compiler, util.Location, List[ast.Expr]) => FuncContext ?=> String): Builtin =
      new Builtin:
        override val name: String = nameArg

        override def expr(compiler: Compiler, pos: Location, call: ast.BuiltinCall)(using context: FuncContext): Expression =
          throw CompileError(pos, s"The $name builtin doesn't work in expressions")

        override def inserted(compiler: Compiler, pos: Location, call: ast.BuiltinCall)(using context: FuncContext): String =
          func(compiler, pos, call.args)

        override def decl(compiler: Compiler, pos: Location, call: ast.BuiltinCall, location: ResourceLocation): Unit =
          throw CompileError(pos, s"The $name builtin doesn't work at toplevel")

    def exprOnly(nameArg: String)(func: (Compiler, util.Location, List[ast.Expr]) => FuncContext ?=> Expression): Builtin =
      new Builtin:
        override val name: String = nameArg

        override def expr(compiler: Compiler, pos: Location, call: ast.BuiltinCall)(using context: FuncContext): Expression =
          func(compiler, pos, call.args)

        override def inserted(compiler: Compiler, pos: Location, call: ast.BuiltinCall)(using context: FuncContext): String =
          throw CompileError(pos, s"The $name builtin doesn't work in inserts")

        override def decl(compiler: Compiler, pos: Location, call: ast.BuiltinCall, location: ResourceLocation): Unit =
          throw CompileError(pos, s"The $name builtin doesn't work at toplevel")

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




    def compile(compiler: Compiler, code: mutable.ArrayBuffer[String], namespace: String, inverted: Boolean): EvaluatedCondition =
      import EvaluatedCondition.Check as ECCheck
      import EvaluatedCondition.Known as ECKnown
      val prefix = if inverted then "unless" else "if"
      this.compileFlat(inverted) match
        case Some(v) => v
        // we couldn't make a oneliner out of this one : (
        case _ =>
          this match
            case Condition.Or(l, r) =>
              if inverted then
                Condition.And(Condition.Inverted(l), Condition.Inverted(r)).compile(compiler, code, namespace, false)
              else
                val left = l.compile(compiler, code, namespace, false)
                left match
                  case ECKnown(true) => ECKnown(true)
                  case ECKnown(false) =>
                    r.compile(compiler, code, namespace, false)
                  case ECCheck(x) =>
                    val right = r.compile(compiler, code, namespace, false)
                    right match
                      case ECKnown(true) => ECKnown(true)
                      case ECKnown(false) =>
                        ECCheck(x)
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

                val left = l.compile(compiler, code, namespace, false)
                left match
                  case ECKnown(false) => ECKnown(false)
                  case ECKnown(true) =>
                    r.compile(compiler, code, namespace, false)
                  case ECCheck(x) =>
                    val right = r.compile(compiler, code, namespace, false)
                    right match
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

            case _ => throw CompileError(util.Location.blank, "INTERNAL ERROR: Expected a non-flat conditional to be Or, And, or Inverted.")


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
          .forEach(_.delete())

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

        items.find { case Item.Module(name, _) => name == first } match
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
          items.find { case Item.Module(name, _) => name == first } match
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
      case class ZFileResource(kind: String, isAsset: Boolean, path: String, location: util.Location) extends Item:
        import java.nio.file.{FileSystems, Paths}
        override def generate(rootPath: String, localPath: ResourceLocation): Unit =
          val resourceDir = if isAsset then "assets" else "data"
          var dirPath = Path.of(rootPath, resourceDir, localPath.namespace)
          if kind != "." then
            dirPath = dirPath.resolve(kind)

          dirPath = dirPath.resolve(localPath.modules.mkString("/"))
          Files.createDirectories(dirPath)

          // TODO: glob
          val matcher = FileSystems.getDefault.getPathMatcher("glob:" + path)
          Files.walkFileTree(Path.of(location.file).getParent, new SimpleFileVisitor[Path] {
            override def visitFile(file: Path, attrs: BasicFileAttributes): FileVisitResult =
              if matcher.matches(file) then
                Files.createDirectories(dirPath.resolve(file).getParent)
                Files.copy(file, dirPath.resolve(file))
              FileVisitResult.CONTINUE
          })



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

  def registerNamespace(ns: parser.ast.Namespace, parentScope: Int): Unit =
    val index = pushScope(ns.name, parentScope)

    val resource = ResourceLocation(ns.name, List(), ResourceKind.Module)

    ns.items.foreach: decl =>
      registerItem(decl, resource, index)

  def register(nses: List[parser.ast.Namespace]): Unit = {
    scopes.append(Compiler.Scope(0))
    nses.foreach: ns =>
      registerNamespace(ns, 0)

  }

  def registerItem(item: parser.ast.Decl, location: ResourceLocation, parentScope: Int): Unit = {
    import parser.ast.Decl.*
    item.node match
      case Module(name, items) => registerModule(name, items, location, parentScope)
      case IncludedItems(_, items) => items.foreach(item => registerItem(item, location, parentScope))
      case ZFunction(returnType, name, params, stmts) => registerFunction(returnType, name, params, stmts, location, parentScope)
      case ZResource(_, _, _) => ()
      case gay.menkissing.ziglin.parser.ast.Decl.ZBuiltinCall(_) => ()
  }

  def registerModule(name: String, items: List[parser.ast.Decl], location: ResourceLocation, parentScope: Int): Unit = {
    val index = pushScope(name, parentScope)
    val newLoc = location.copy(modules = location.modules.appended(name))
    items.foreach: item =>
      registerItem(item, newLoc, index)
  }

  def registerFunction(returnType: ReturnType, name: String, params: List[Parameter], stmts: List[parser.ast.Stmt], location: ResourceLocation, parentScope: Int): Unit = {
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

  def addItem(location: ResourceLocation, item: FileTree.Item): Unit =
    val items = getLocation(location)
    items.foreach: i =>
      (i, item) match
        case (FileTree.Item.ZFunction(name, _, _), FileTree.Item.ZFunction(name2, _, loc)) if name == name2 =>
          throw CompileError(loc, s"Function \"${name2}\" is already defined.")
        case (a: FileTree.Item.ZTextResource, b: FileTree.Item.ZTextResource) if a == b =>
          throw CompileError(b.location, s"${b.kind} \"${b.name}\" is already defined")
        case _ => ()

    items.append(item)

  def compileItem(ast: parser.ast.Decl, location: ResourceLocation): Unit =
    import parser.ast.Decl.*
    ast.node match
      case func: ZFunction => compileAstFunction(ast.pos, func, location)
      case module: parser.ast.Decl.Module => compileModule(module, location)
      case incl: IncludedItems => incl.items.foreach(it => compileItem(it, location))
      case resource: ZResource => compileResource(ast.pos, resource, location)
      case ZBuiltinCall(call) => builtins.compileDecl(ast.pos, call, location)

  def compileResource(pos: util.Location, resource: ZResource, location: ResourceLocation): Unit =
    import parser.ast.ResourceContent
    resource.content match
      case ResourceContent.Text(name, json) =>
        val compiled = json.spaces4
        val resource2 = FileTree.Item.ZTextResource(name, resource.kind, resource.isAsset, compiled, pos)
        addItem(location, resource2)
      case ResourceContent.File(path, file) =>
        val filePath = Path.of(path).getParent
        val resource2 = FileTree.Item.ZFileResource(resource.kind, resource.isAsset, filePath.resolve(file).toString, pos)
        addItem(location, resource2)


  private def compileAstFunction(pos: util.Location, func: parser.ast.Decl.ZFunction, location: ResourceLocation): Unit =
    val fnLocation = location.withName(func.name)
    val hasMacroArgs = func.params.exists(_.kind == ParameterKind.Macro)
    val context = FuncContext(fnLocation, func.returnType)
    context.hasMacroArgs = hasMacroArgs
    // TODO comptime
    compileBlock(func.stmts)(using context)
    // TODO: comptime

    addFunctionItem(pos, context.location, context.code.toList)

  private def addFunctionItem(location: util.Location, fnLocation: ResourceLocation, commands: List[String]): Unit =
    val (module, name) = fnLocation.trySplit.get
    val function = FileTree.Item.ZFunction(name, commands, location)
    addItem(module, function)

  private def compileBlock(block: List[parser.ast.Stmt])(using context: FuncContext): Unit =
    block.foreach: stmt =>
      compileStatement(stmt)

  private def compileIfStatementWithoutChild(condition: parser.ast.Expr, body: List[parser.ast.Stmt], isChild: Boolean)(using context: FuncContext): Unit =
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
        val subContext = context.nested(NestKind.Block, func, None)
        compileBlock(body)(using subContext)
        val command =
          subContext.code.length match
            case 0 => return
            case 1 if !subContext.hasNestedContinue.value =>
              subContext.code(0)
            case _ =>
              addFunctionItem(util.Location.blank, func, subContext.code.toList)
              if subContext.hasMacroArgs then
                mcfunc"function ${func} with storage ${parameterStorage}"
              else
                mcfunc"function ${func}"
        val executeCommand = s"execute ${checkCode} ${if isChild then "run return run" else "run"} ${command}"
        context.code.append(executeCommand)


  def compileIfStatement(ifStatement: parser.ast.IfStatement)(using context: FuncContext): Unit =
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
        def whileMethod(): Unit = {
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

  def compileLoop(pos: util.Location, self: ResourceLocation, body: List[ast.Stmt])(using context: FuncContext): Unit =
    val loopContext = context.nestInfo.flatMap(_.currentLoopContext).getOrElse(throw CompileError(pos, "INTERNAL ERROR: When compiling a loop, there should be a loop context"))
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
    loopContext.continueExpr.foreach: continueExpr =>
      compileExpression(continueExpr, true)

    context.code.append(mcfunc"function $self")

    addFunctionItem(util.Location.blank, self, context.code.toList)

  def compileForLoop(pos: util.Location, forLoop: ast.Stmt.ZFor)(using context: FuncContext): Unit =
    val func = nextFunction("for", context.location.namespace)
    val loopContext =
      forLoop.range match
        case ForRange.Single(n) =>
          compileAssignment(forLoop.variable.pos, forLoop.variable, Expr.ZInt(0).unknownLocation)

          LoopContext(Some(Expr.Binop(ast.BinopKind.Less, forLoop.variable, n).unknownLocation), Some(Expr.Binop(ast.BinopKind.AddAssign, forLoop.variable, Expr.ZInt(1).unknownLocation).unknownLocation), func)
        case ForRange.Range(min, inclusive, max) =>
          compileAssignment(forLoop.variable.pos, forLoop.variable, min)

          LoopContext(Some(Expr.Binop(if inclusive then ast.BinopKind.LessEq else ast.BinopKind.Less, forLoop.variable, max).unknownLocation), Some(Expr.Binop(ast.BinopKind.AddAssign, forLoop.variable, Expr.ZInt(1).unknownLocation).unknownLocation), func)


    val subContext = context.nested(NestKind.Loop(loopContext), func, None)
    compileLoop(pos, func, forLoop.body)(using subContext)
    context.code.append(mcfunc"function $func")



  def compileWhileLoop(whileLoop: parser.ast.Stmt.ZWhile)(using context: FuncContext): Unit =
    val func = nextFunction("while", context.location.namespace)
    val subContext = context.nested(NestKind.Loop(LoopContext(Some(whileLoop.cond), whileLoop.continueExpr, func)), func, None)


    compileLoop(whileLoop.cond.pos, func, whileLoop.body)(using subContext)
    context.code.append(mcfunc"function $func")


  def compileStatement(statement: parser.ast.Stmt)(using context: FuncContext): Unit =
    statement.expr match
      case Stmt.Eval(expr) => compileExpression(expr, true)
      case x: Stmt.Command =>
        val cmd = compileCommand(statement.pos, x)
        context.code.append(cmd)
      case Stmt.ZIf(ifStatement) =>
        val subContext = context.plain
        subContext.hasNestedReturns = util.Box(false)
        subContext.hasNestedContinue = util.Box(false)
        compileIfStatement(ifStatement)(using subContext)
        if subContext.hasNestedReturns.value then
          context.hasNestedReturns.value = true
          generateNestedReturn()
        if subContext.hasNestedContinue.value then
          context.hasNestedContinue.value = true
          println("nesting")
          generateNestedContinue()

      case s: Stmt.ZWhile =>
        val subContext = context.plain
        subContext.hasNestedReturns = util.Box(false)
        subContext.hasNestedContinue = util.Box(false)
        compileWhileLoop(s)(using subContext)
        if subContext.hasNestedReturns.value then
          context.hasNestedReturns.value = true
          generateNestedReturn()
        // Right now we don't actually check nested continues here. They are only for if statement to not fuck it up
        // When labelled continues are implemented, then it'll have to be checked
      case s: Stmt.ZFor =>
        val subContext = context.plain
        subContext.hasNestedReturns = util.Box(false)
        subContext.hasNestedContinue = util.Box(false)
        compileForLoop(statement.pos, s)(using subContext)
        if subContext.hasNestedReturns.value then
          context.hasNestedReturns.value = true
          generateNestedReturn()
      case Stmt.ZReturn(expr) => compileReturn(statement.pos, expr)
      // TODO: these need special handling while nested
      case Stmt.ZContinue =>
        compileContinue(statement.pos)
      case Stmt.ZBreak => ???

  object internals:
    // TODO: do this idiomatically
    lazy val resetDirectReturn: ResourceLocation = {
      val location = ResourceLocation.function("ziglin", List("internal", "0.1.0", "reset_return"))
      addFunctionItem(util.Location.blank, location, List(
        // TODO: better namespace for the "applies to everything" than minecraft?
        "scoreboard players operation $temp_return ziglin.internal.minecraft.vars = $should_return ziglin.internal.minecraft.vars",
        "scoreboard players reset $should_return ziglin.internal.minecraft.vars",
        "return run scoreboard players get $temp_return ziglin.internal.minecraft.vars"
      ))
      location
    }
    def continueCommands(loop: ResourceLocation): List[String] =
      List(
        mcfunc"scoreboard players reset $$should_continue ziglin.internal.${ScoreboardLocation.scoreboardStringOf(loop)}.vars",
        mcfunc"return run function $loop"
      )

  def generateNestedContinue()(using context: FuncContext): Unit =
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
        addFunctionItem(util.Location.blank, fn, commands)
        context.code.append(
          mcfunc"execute if score $$should_continue ziglin.internal.${scoreboardString}.vars matches ${Int.MinValue}..${Int.MaxValue} run return run function ${fn}"
        )
      case _ =>
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
    def compile(pos: util.Location, part: CommandPart.Inserted)(using context: FuncContext): (String, Boolean) =
      part.expr.node match
        case InsertedExpr.MacroVariable(name) =>
          (s"$$(__${name})", true)
        case InsertedExpr.ScoreboardVariable(path) =>
          val scoreboard = ScoreboardLocation.resolveResource(context.location, path)
          (scoreboard.mcdisplay, false)
        case InsertedExpr.ResourceRef(path) =>
          val resolved = ResourceLocation.resolveResource(context.location, path)
          (resolved.mcdisplay, false)
        case InsertedExpr.ZBlock(mayBeInlined, stmts) =>
          val func = nextFunction("block", context.location.namespace)
          val subContext = context.nested(NestKind.Block, func, None)
          compileBlock(stmts)(using subContext)
          subContext.code.length match
            // TODO: safe function to call that does nothing?
            case 0 => ???
            case 1 if mayBeInlined =>
              (subContext.code.head, false)
            case _ =>
              addFunctionItem(util.Location.blank, func, subContext.code.toList)
              (mcfunc"function ${func}", false)
        case InsertedExpr.ZBuiltinCall(call) =>
          (builtins.compileInserted(pos, call), false)


  def compileCommand(pos: util.Location, command: parser.ast.Stmt.Command)(using context: FuncContext): String =
    // : )
    var res = ""
    var needsMacro = false
    command.parts.foreach:
      case CommandPart.Literal(str) =>
        res = res + cleanCommandString(str)
      case inserted: CommandPart.Inserted =>
        val (compiled, insertNeedsMacro) = insertedExpr.compile(pos, inserted)
        res = res + compiled
        needsMacro = needsMacro || insertNeedsMacro
    if needsMacro && !res.startsWith("$") then
      "$" + res
    else
      res



  def compileNot(pos: util.Location, value: parser.ast.Expr)(using context: FuncContext): Expression =
    val operand = compileExpression(value, false)
    val needsMacro = operand.needsMacro

    val condition = operand.toCondition(this, context.code, context.location.namespace)


    Expression(pos, needsMacro, ExpressionKind.ECondition(Condition.Inverted(condition)))

  def compileNegate(pos: util.Location, value: parser.ast.Expr)(using context: FuncContext): Expression =
    val operand = compileExpression(value, false)
    val needsMacro = operand.needsMacro

    val kind = operand.kind match
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
          mcfunc"${if needsMacro then "$" else ""}execute store result storage ${tempStorage} int -1 run data get ${loc}"
        )
        ExpressionKind.EStorage(tempStorage)
      case ExpressionKind.EScoreboard(loc) =>
        val tempStorage = nextStorage(context.location.namespace)
        context.code.append(
          mcfunc"${if needsMacro then "$" else ""}execute store result storage ${tempStorage} int -1 run scoreboard players get ${loc}"
        )
        ExpressionKind.EStorage(tempStorage)
      case ExpressionKind.EMacro(_) =>
        val tempStorage = copyToStorage(context.code, operand, context.location.namespace)
        context.code.append(
          mcfunc"execute store result ${tempStorage} int -1 run data get storage ${tempStorage}"
        )
        ExpressionKind.EStorage(tempStorage)

    Expression(pos, needsMacro, kind)

  def compileUnaryExpression(pos: util.Location, expr: parser.ast.Expr.Unary)(using context: FuncContext): Expression =
    expr.kind match
      case UnaryKind.Not => compileNot(pos, expr.expr)
      case UnaryKind.Negate => compileNegate(pos, expr.expr)

  def compileNumericOperation(pos: util.Location, left: parser.ast.Expr, operator: ScoreboardOperation, right: parser.ast.Expr)(using context: FuncContext): Expression =
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

    Expression(pos, needsMacro, kind)


  def compileOperatorAssignment(pos: util.Location, left: parser.ast.Expr, operator: ScoreboardOperation, right: parser.ast.Expr)(using context: FuncContext): Expression =
    left.expr match
      case Expr.ZScoreboardVariable(path) =>
        val r = compileExpression(right, false)

        val scoreboard = ScoreboardLocation.resolveResource(context.location, path)
        useScoreboard(scoreboard.scoreboardString)
        scoreboardOperation(scoreboard, r, operator)

        r
      case _ =>
        compileAssignment(pos, left, Expr(parser.ast.Expr.Binop(operator.binopKind, left, right), right.pos))


  def compileAssignment(pos: util.Location, left: parser.ast.Expr, right: parser.ast.Expr)(using context: FuncContext): Expression =
    left.expr match
      case Expr.ZVariable(path) =>
        val r = compileExpression(right, false)
        val storage = StorageLocation.resolveResource(context.location, path)
        setStorage(context.code, storage, r)

        r

      case Expr.ZScoreboardVariable(path) =>
        val r = compileExpression(right, false)
        val scoreboard = ScoreboardLocation.resolveResource(context.location, path)

        setScoreboard(context.code, scoreboard, r)
        useScoreboard(scoreboard.scoreboardString)

        r
      case _ => throw CompileError(pos, "Can only assign to a variable")


  def compileMatchComparison(code: mutable.ArrayBuffer[String], value: Expression, range: MatchRange, namespace: String): ExpressionKind =
    val scoreboard = moveToScoreboard(code, value, namespace)
    ExpressionKind.ECondition(Condition.Match(scoreboard, range))

  def storageComparison(code: mutable.ArrayBuffer[String], left: Expression, right: Expression, checkEquality: Boolean, namespace: String): ExpressionKind =
    val rightStorage = moveToStorage(code, right, namespace)
    val tempStorage = copyToStorage(code, left, namespace)
    val conditionScoreboard = nextScoreboard(namespace)
    code.append(
      mcfunc"execute store success score ${conditionScoreboard} run data modify storage ${tempStorage} set from storage ${rightStorage}"
    )
    ExpressionKind.ECondition(Condition.Match(conditionScoreboard, MatchRange.Single(if checkEquality then 0 else 1)))

  def compileNotEquals(pos: util.Location, left: parser.ast.Expr, right: parser.ast.Expr)(using context: FuncContext): Expression =
    val l = compileExpression(left, false)
    val r = compileExpression(right, false)
    val needsMacro = l.needsMacro || r.needsMacro

    l.valueEqual(r) match
      case Some(equal) =>
        Expression(pos, false, ExpressionKind.EBoolean(equal))
      case _ =>
        val kind =
          (l.kind, r.kind) match
            case (ExpressionKind.EVoid, _) | (_, ExpressionKind.EVoid) =>
              throw CompileError(pos, "Cannot compare with void.")
            case (ExpressionKind.EStorage(_), _) | (_, ExpressionKind.EStorage(_)) =>
              storageComparison(context.code, l, r, false, context.location.namespace)
            case (leftKind, rightKind) if leftKind.nbtType.numeric && rightKind.nbtType.numeric =>
              val leftScore = moveToScoreboard(context.code, l, context.location.namespace)
              val rightScore = moveToScoreboard(context.code, r, context.location.namespace)
              ExpressionKind.ECondition(Condition.Inverted(Condition.Eq(leftScore, rightScore)))
            case _ =>
              storageComparison(context.code, l, r, false, context.location.namespace)

        Expression(pos, needsMacro, kind)

  def compileEquals(pos: util.Location, left: parser.ast.Expr, right: parser.ast.Expr)(using context: FuncContext): Expression =
    val l = compileExpression(left, false)
    val r = compileExpression(right, false)
    val needsMacro = l.needsMacro || r.needsMacro

    l.valueEqual(r) match
      case Some(equal) =>
        Expression(pos, false, ExpressionKind.EBoolean(equal))
      case _ =>
        val kind =
          (l.kind, r.kind) match
            case (ExpressionKind.EVoid, _) | (_, ExpressionKind.EVoid) =>
              throw CompileError(pos, "Cannot compare with void.")
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

        Expression(pos, needsMacro, kind)
  def compileGreaterThanEqual(pos: util.Location, left: parser.ast.Expr, right: parser.ast.Expr)(using context: FuncContext): Expression =
    val l = compileExpression(left, false)
    val r = compileExpression(right, false)
    val needsMacro = l.needsMacro || r.needsMacro
    val kind =
      (l.kind, r.kind) match
        case (ExpressionKind.EVoid, _) | (_, ExpressionKind.EVoid) =>
          throw CompileError(pos, "Cannot compare with void.")
        case (ExpressionKind.EBoolean(_), _) | (_, ExpressionKind.EBoolean(_)) =>
          throw CompileError(pos, "Cannot compare with boolean.")
        case (ExpressionKind.EString(_), _) | (_, ExpressionKind.EString(_)) =>
          throw CompileError(pos, "Cannot compare with string.")
        case (ExpressionKind.Numeric(lv), ExpressionKind.Numeric(rv)) =>
          ExpressionKind.EBoolean(lv >= rv)
        case (ExpressionKind.Numeric(lv), _) =>
          val scoreboard = moveToScoreboard(context.code, r, context.location.namespace)
          ExpressionKind.ECondition(Condition.Match(scoreboard, MatchRange.Range(None, Some(lv))))
        case (_, ExpressionKind.Numeric(rv)) =>
          val scoreboard = moveToScoreboard(context.code, l, context.location.namespace)
          ExpressionKind.ECondition(Condition.Match(scoreboard, MatchRange.Range(Some(rv), None)))
        case _ =>
          val leftScore = moveToScoreboard(context.code, l, context.location.namespace)
          val rightScore = moveToScoreboard(context.code, r, context.location.namespace)
          ExpressionKind.ECondition(Condition.GreaterEq(leftScore, rightScore))

    Expression(pos, needsMacro, kind)

  def compileGreaterThan(pos: util.Location, left: parser.ast.Expr, right: parser.ast.Expr)(using context: FuncContext): Expression =
    val l = compileExpression(left, false)
    val r = compileExpression(right, false)
    val needsMacro = l.needsMacro || r.needsMacro
    val kind =
      (l.kind, r.kind) match
        case (ExpressionKind.EVoid, _) | (_, ExpressionKind.EVoid) =>
          throw CompileError(pos, "Cannot compare with void.")
        case (ExpressionKind.EBoolean(_), _) | (_, ExpressionKind.EBoolean(_)) =>
          throw CompileError(pos, "Cannot compare with boolean.")
        case (ExpressionKind.EString(_), _) | (_, ExpressionKind.EString(_)) =>
          throw CompileError(pos, "Cannot compare with string.")
        case (ExpressionKind.Numeric(lv), ExpressionKind.Numeric(rv)) =>
          ExpressionKind.EBoolean(lv > rv)
        case (ExpressionKind.Numeric(lv), _) =>
          val scoreboard = moveToScoreboard(context.code, r, context.location.namespace)
          ExpressionKind.ECondition(Condition.Match(scoreboard, MatchRange.Range(None, Some(lv - 1))))
        case (_, ExpressionKind.Numeric(rv)) =>
          val scoreboard = moveToScoreboard(context.code, l, context.location.namespace)
          ExpressionKind.ECondition(Condition.Match(scoreboard, MatchRange.Range(Some(rv + 1), None)))
        case _ =>
          val leftScore = moveToScoreboard(context.code, l, context.location.namespace)
          val rightScore = moveToScoreboard(context.code, r, context.location.namespace)
          ExpressionKind.ECondition(Condition.Greater(leftScore, rightScore))

    Expression(pos, needsMacro, kind)

  def compileLessThanEqual(pos: util.Location, left: parser.ast.Expr, right: parser.ast.Expr)(using context: FuncContext): Expression =
    val l = compileExpression(left, false)
    val r = compileExpression(right, false)
    val needsMacro = l.needsMacro || r.needsMacro
    val kind =
      (l.kind, r.kind) match
        case (ExpressionKind.EVoid, _) | (_, ExpressionKind.EVoid) =>
          throw CompileError(pos, "Cannot compare with void.")
        case (ExpressionKind.EBoolean(_), _) | (_, ExpressionKind.EBoolean(_)) =>
          throw CompileError(pos, "Cannot compare with boolean.")
        case (ExpressionKind.EString(_), _) | (_, ExpressionKind.EString(_)) =>
          throw CompileError(pos, "Cannot compare with string.")
        case (ExpressionKind.Numeric(lv), ExpressionKind.Numeric(rv)) =>
          ExpressionKind.EBoolean(lv <= rv)
        case (ExpressionKind.Numeric(lv), _) =>
          val scoreboard = moveToScoreboard(context.code, r, context.location.namespace)
          ExpressionKind.ECondition(Condition.Match(scoreboard, MatchRange.Range(Some(lv), None)))
        case (_, ExpressionKind.Numeric(rv)) =>
          val scoreboard = moveToScoreboard(context.code, l, context.location.namespace)
          ExpressionKind.ECondition(Condition.Match(scoreboard, MatchRange.Range(None, Some(rv))))
        case _ =>
          val leftScore = moveToScoreboard(context.code, l, context.location.namespace)
          val rightScore = moveToScoreboard(context.code, r, context.location.namespace)
          ExpressionKind.ECondition(Condition.LessEq(leftScore, rightScore))

    Expression(pos, needsMacro, kind)

  def compileLessThan(pos: util.Location, left: parser.ast.Expr, right: parser.ast.Expr)(using context: FuncContext): Expression =
    val l = compileExpression(left, false)
    val r = compileExpression(right, false)
    val needsMacro = l.needsMacro || r.needsMacro
    val kind =
      (l.kind, r.kind) match
        case (ExpressionKind.EVoid, _) | (_, ExpressionKind.EVoid) =>
          throw CompileError(pos, "Cannot compare with void.")
        case (ExpressionKind.EBoolean(_), _) | (_, ExpressionKind.EBoolean(_)) =>
          throw CompileError(pos, "Cannot compare with boolean.")
        case (ExpressionKind.EString(_), _) | (_, ExpressionKind.EString(_)) =>
          throw CompileError(pos, "Cannot compare with string.")
        case (ExpressionKind.Numeric(lv), ExpressionKind.Numeric(rv)) =>
          ExpressionKind.EBoolean(lv < rv)
        case (ExpressionKind.Numeric(lv), _) =>
          val scoreboard = moveToScoreboard(context.code, r, context.location.namespace)
          ExpressionKind.ECondition(Condition.Match(scoreboard, MatchRange.Range(Some(lv + 1), None)))
        case (_, ExpressionKind.Numeric(rv)) =>
          val scoreboard = moveToScoreboard(context.code, l, context.location.namespace)
          ExpressionKind.ECondition(Condition.Match(scoreboard, MatchRange.Range(None, Some(rv - 1))))
        case _ =>
          val leftScore = moveToScoreboard(context.code, l, context.location.namespace)
          val rightScore = moveToScoreboard(context.code, r, context.location.namespace)
          ExpressionKind.ECondition(Condition.Less(leftScore, rightScore))

    Expression(pos, needsMacro, kind)


  def compileLogicalOr(pos: util.Location, left: parser.ast.Expr, right: parser.ast.Expr)(using context: FuncContext): Expression =
    val l = compileExpression(left, false)
    val r = compileExpression(right, false)
    val needsMacro = l.needsMacro || r.needsMacro

    val leftCondition =
      l.toCondition(this, context.code, context.location.namespace)
    val rightCondition =
      r.toCondition(this, context.code, context.location.namespace)

    val kind = ExpressionKind.ECondition(Condition.Or(leftCondition, rightCondition).simplify)

    Expression(pos, needsMacro, kind)

  def compileLogicalAnd(pos: util.Location, left: parser.ast.Expr, right: parser.ast.Expr)(using context: FuncContext): Expression =
    val l = compileExpression(left, false)
    val r = compileExpression(right, false)
    val needsMacro = l.needsMacro || r.needsMacro

    val leftCondition =
      l.toCondition(this, context.code, context.location.namespace)
    val rightCondition =
      r.toCondition(this, context.code, context.location.namespace)

    val kind = ExpressionKind.ECondition(Condition.And(leftCondition, rightCondition).simplify)

    Expression(pos, needsMacro, kind)

  def compileBinaryExpression(pos: util.Location, expr: parser.ast.Expr.Binop)(using context: FuncContext): Expression =
    expr.name match
      case BinopKind.Equals => compileEquals(pos, expr.l, expr.r)
      case BinopKind.Unequal => compileNotEquals(pos, expr.l, expr.r)
      case BinopKind.Greater => compileGreaterThan(pos, expr.l, expr.r)
      case BinopKind.GreaterEq => compileGreaterThanEqual(pos, expr.l, expr.r)
      case BinopKind.Less => compileLessThan(pos, expr.l, expr.r)
      case BinopKind.LessEq => compileLessThanEqual(pos, expr.l, expr.r)
      case BinopKind.Plus => compileNumericOperation(pos, expr.l, ScoreboardOperation.Add, expr.r)
      case BinopKind.Minus => compileNumericOperation(pos, expr.l, ScoreboardOperation.Sub, expr.r)
      case BinopKind.Times => compileNumericOperation(pos, expr.l, ScoreboardOperation.Mul, expr.r)
      case BinopKind.Divide => compileNumericOperation(pos, expr.l, ScoreboardOperation.Div, expr.r)
      case BinopKind.Modulo => compileNumericOperation(pos, expr.l, ScoreboardOperation.Mod, expr.r)
      case BinopKind.And => compileLogicalAnd(pos, expr.l, expr.r)
      case BinopKind.Or => compileLogicalOr(pos, expr.l, expr.r)
      case BinopKind.Assign => compileAssignment(pos, expr.l, expr.r)
      case BinopKind.AddAssign => compileOperatorAssignment(pos, expr.l, ScoreboardOperation.Add, expr.r)
      case BinopKind.SubAssign => compileOperatorAssignment(pos, expr.l, ScoreboardOperation.Sub, expr.r)
      case BinopKind.MulAssign => compileOperatorAssignment(pos, expr.l, ScoreboardOperation.Mul, expr.r)
      case BinopKind.DivAssign => compileOperatorAssignment(pos, expr.l, ScoreboardOperation.Div, expr.r)
      case BinopKind.ModAssign => compileOperatorAssignment(pos, expr.l, ScoreboardOperation.Mod, expr.r)

  def compileFunctionCall(pos: util.Location, functionCall: parser.ast.FunctionCall)(using context: FuncContext): (String, CalledFunction) =
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

  def compileContinue(pos: util.Location)(using context: FuncContext): Unit =
    val (nestInfo, curLoop) =
      context.nestInfo.flatMap { nestInfo =>
        nestInfo.getLoop.map(it => (nestInfo, it))
      }.getOrElse(throw CompileError(pos, "continue may only be inside of loops"))

    val scoreboardString = ScoreboardLocation.scoreboardStringOf(curLoop.actualLocation)
    if !nestInfo.isLoop then
      println("NEST TUaH! NEST THAT THANG")
      context.hasNestedContinue.value = true
      context.code.append(
        mcfunc"return run scoreboard players set $$should_continue ziglin.internal.${scoreboardString}.vars 0"
      )

    else
      context.code.append(mcfunc"return run function ${curLoop.actualLocation}")




  def compileReturn(pos: util.Location, value: Option[parser.ast.Expr])(using context: FuncContext): Unit =
    if context.isNested then
      context.hasNestedReturns.value = true
    val hasValue = value.nonEmpty
    value match
      case Some(v) =>
        val expression = compileExpression(v, false)

        context.returnType match
          case ReturnType.Storage =>
            val returnStorage = StorageLocation(context.location, "return")
            setStorage(context.code, returnStorage, expression)
          case ReturnType.Scoreboard =>
            val scoreboard = ScoreboardLocation(context.location, "$return")
            setScoreboard(context.code, scoreboard, expression)
          case ReturnType.Direct =>
            if context.isNested then
              setScoreboard(context.code, ScoreboardLocation.internal("minecraft", "$should_return"), expression)
            else
              context.code.append(expression.toReturnCommand(this, context.code, context.location.namespace))
      case _ => ()

    if context.returnType != ReturnType.Direct && context.isNested then
      setScoreboard(context.code, ScoreboardLocation.internal("minecraft", "$should_return"), Expression(util.Location.blank, false, ExpressionKind.EInteger(1)))

    if hasValue then
      if context.returnType != ReturnType.Direct || context.isNested then
        context.code.append("return 0")
    else
      context.code.append("return fail")


  object builtins:
    def compileDecl(pos: util.Location, call: ast.BuiltinCall, location: ResourceLocation): Unit =
      Compiler.builtins.getOrElse(call.name, throw CompileError(pos, s"No such builtin ${call.name}")).decl(Compiler.this, pos, call, location)


    def compileInserted(pos: util.Location, call: ast.BuiltinCall)(using context: FuncContext): String =
      Compiler.builtins.getOrElse(call.name, throw CompileError(pos, s"No such builtin ${call.name}")).inserted(Compiler.this, pos, call)


    def compile(pos: util.Location, call: ast.BuiltinCall)(using context: FuncContext): Expression =
      Compiler.builtins.getOrElse(call.name, throw CompileError(pos, s"No such builtin ${call.name}")).expr(Compiler.this, pos, call)



  def verifyTypes(kinds: List[Expression], kind: ast.ArrayKind, message: String): NbtType =
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
  def compileArray(kind: ast.ArrayKind, expressions: List[ast.Expr], pos: util.Location)(using context: FuncContext): Expression =
    val kinds =
      expressions.map: expr =>
        compileExpression(expr, false)


    val errMsg =
      kind match
        case ast.ArrayKind.Any => "Arrays can only contain values of the same type"
        case ast.ArrayKind.Byte => "Byte arrays can only contain byte values"
        case ast.ArrayKind.Int => "Int arrays can only contain int values"
        case ast.ArrayKind.Long => "Long arrays can only contain long values"

    val dataType = verifyTypes(kinds, kind, errMsg)

    val exprKind =
      kind match
        case ast.ArrayKind.Any => ExpressionKind.EArray(kinds, dataType)
        case ast.ArrayKind.Byte => ExpressionKind.EByteArray(kinds)
        case ast.ArrayKind.Int => ExpressionKind.EIntArray(kinds)
        case ast.ArrayKind.Long => ExpressionKind.ELongArray(kinds)

    Expression(pos, false, exprKind)

  def compileCompound(pos: util.Location, keyValues: Map[String, ast.Expr])(using context: FuncContext): Expression =
    val kinds =
      keyValues.map: (key, value) =>
        (key, compileExpression(value, false))
    
    Expression(pos, false, ExpressionKind.ECompound(kinds))



  def compileExpression(expr: ast.Expr, ignored: Boolean)(using context: FuncContext): Expression =
    expr.expr match
      case s @ Expr.Binop(name, l, r) => compileBinaryExpression(expr.pos, s)
      case s @ Expr.Unary(kind, operand) => compileUnaryExpression(expr.pos, s)
      case Expr.ZString(contents) => Expression(expr.pos, false, ExpressionKind.EString(contents))
      case Expr.ZByte(num) => Expression(expr.pos, false, ExpressionKind.EByte(num))
      case Expr.ZShort(num) => Expression(expr.pos, false, ExpressionKind.EShort(num))
      case Expr.ZInt(num) => Expression(expr.pos, false, ExpressionKind.EInteger(num))
      case Expr.ZLong(num) => Expression(expr.pos, false, ExpressionKind.ELong(num))
      case Expr.ZFloat(num) => Expression(expr.pos, false, ExpressionKind.EFloat(num))
      case Expr.ZDouble(num) => Expression(expr.pos, false, ExpressionKind.EDouble(num))
      case Expr.ZBool(v) => Expression(expr.pos, false, ExpressionKind.EBoolean(v))
      case Expr.ZList(kind, values) => compileArray(kind, values, expr.pos)
      case Expr.ZCompound(map) => compileCompound(expr.pos, map)
      case Expr.ZVariable(path) => Expression(expr.pos, false, ExpressionKind.EStorage(StorageLocation.resolveResource(context.location, path)))
      case Expr.ZScoreboardVariable(path) => Expression(expr.pos, false, ExpressionKind.EScoreboard(ScoreboardLocation.resolveResource(context.location, path)))
      case Expr.ZMacroVariable(name) => Expression(expr.pos, true, ExpressionKind.EMacro(StorageLocation(context.location, "__" + name)))
      case Expr.ZBuiltinCall(call) =>
        builtins.compile(expr.pos, call)
      case Expr.ZFunctionCall(functionCall) =>
        val (command, called) = compileFunctionCall(expr.pos, functionCall)
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
      case Expr.Atom(expr) => compileExpression(expr, ignored)

  def compileModule(module: parser.ast.Decl.Module, location: ResourceLocation): Unit =
    enterScope(module.name)
    // TODO: comptime

    val newLocation = location.join(module.name)
    module.items.foreach: item =>
      compileItem(item, newLocation)

    exitScope()
    // TODO: comptime
  def compileNamespace(ast: parser.ast.Namespace): Unit =
    loadFunctions.prepend(s"ziglin:generated/${ast.name}/load")
    enterScope(ast.name)
    // TODO: comptime

    val resource = ResourceLocation.module(ast.name, List())

    ast.items.foreach: item =>
      compileItem(item, resource)

    exitScope()
    // TODO: comptime

    val loadCommands = usedScoreboards.map((name, criteria) => s"scoreboard objectives add $name $criteria")

    val loadFunction = FileTree.Item.ZFunction("load", loadCommands.toList, util.Location.blank)

    addItem(ResourceLocation.module("ziglin", List("generated", ast.name)), loadFunction)

  def compileTree(ast: List[parser.ast.Namespace]): FileTree =
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

  def compile(file: List[parser.ast.Namespace], output: String): Unit =
    register(file)

    val tree = compileTree(file)
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


  def copyToStorage(code: mutable.ArrayBuffer[String], value: Expression, namespace: String): StorageLocation =
    val storage = nextStorage(namespace)
    setStorage(code, storage, value)
    storage
  def moveToStorage(code: mutable.ArrayBuffer[String], value: Expression, namespace: String): StorageLocation =
    value.kind match
      case ExpressionKind.EStorage(storage) => storage
      case _ => copyToStorage(code, value, namespace)


  def setStorage(code: mutable.ArrayBuffer[String], storage: StorageLocation, value: Expression): Unit =
    value.toStorage(this, code, storage, "set", NbtType.Unknown)

  def scoreboardOperation(scoreboard: ScoreboardLocation, value: Expression, operation: ScoreboardOperation)(using context: FuncContext): Unit =
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


  def setScoreboard(code: mutable.ArrayBuffer[String], scoreboard: ScoreboardLocation, value: Expression): Unit =
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

  def copyToScoreboard(code: mutable.ArrayBuffer[String], value: Expression, namespace: String): ScoreboardLocation =
    val scoreboard = nextScoreboard(namespace)
    setScoreboard(code, scoreboard, value)
    scoreboard


  def moveToScoreboard(code: mutable.ArrayBuffer[String], value: Expression, namespace: String): ScoreboardLocation =
    value.kind match
      case ExpressionKind.EScoreboard(loc) => loc
      case _ => copyToScoreboard(code, value, namespace)
