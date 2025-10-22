package gay.menkissing.yaoigen.parser

import parsley.Parsley
import cats.implicits.*
import gay.menkissing.yaoigen.util.{FileInfo, Location}
import parsley.cats.instances.*
import parsley.syntax.zipped.*
import parsley.generic

object ast:
  case class UnresolvedResource(
                           namespace: Option[String],
                           modules: List[String],
                           name: String
                           )
  object UnresolvedResource extends generic.ParserBridge3[Option[String], List[String], String, UnresolvedResource]

  object bridge:
    type Pos = Location

    trait PosSingleton[+A]:
      def con(pos: Pos): A

      final def <#(op: Parsley[?])(using f: FileInfo): Parsley[A] = f.pos.map(this.con) <~ op

      def make(using f: FileInfo): Parsley[A] = f.pos.map(this.con)
      

    trait PosBridge0[+Z] extends PosSingleton[Z]:
      def apply(pos: Pos): Z

      override final def con(pos: Pos): Z = apply(pos)

    trait PosBridge1[-A, +Z] extends PosSingleton[A => Z]:
      override final def con(pos: Pos): A => Z = this.apply(pos, _)

      def apply(pos: Pos, a: A): Z

      def apply(a: Parsley[A])(using f: FileInfo): Parsley[Z] =
        f.pos <**> a.map(a => this.apply(_, a))

    trait PosBridge2[-A, -B, +Z] extends PosSingleton[(A, B) => Z]:
      override final def con(pos: Pos): (A, B) => Z = this.apply(pos, _, _)

      def apply(pos: Pos, a: A, b: B): Z

      def apply(a: Parsley[A], b: Parsley[B])(using f: FileInfo): Parsley[Z] =
        f.pos <**> (a, b).mapN((a, b) => this.apply(_, a, b))

      def apply(a: Parsley[A])(using f: FileInfo): Parsley[B => Z] =
        f.pos <**> a.map(a => pos => b => this.apply(pos, a, b))

    trait PosBridge3[-A, -B, -C, +Z] extends PosSingleton[(A, B, C) => Z]:
      override final def con(pos: Pos): (A, B, C) => Z = this.apply(pos, _, _, _)

      def apply(pos: Pos, a: A, b: B, c: C): Z

      def apply(a: Parsley[A], b: Parsley[B], c: Parsley[C])(using f: FileInfo): Parsley[Z] =
        f.pos <**> (a, b, c).mapN((a, b, c) => this.apply(_, a, b, c))

      def apply(a: Parsley[A])(using f: FileInfo): Parsley[(B, C) => Z] =
        f.pos <**> a.map(a => pos => (b, c) => this.apply(pos, a, b, c))

    trait PosBridge4[-A, -B, -C, -D, +Z] extends PosSingleton[(A, B, C, D) => Z]:
      override final def con(pos: Pos): (A, B, C, D) => Z = this.apply(pos, _, _, _, _)

      def apply(pos: Pos, a: A, b: B, c: C, d: D): Z

      def apply(a: Parsley[A], b: Parsley[B], c: Parsley[C], d: Parsley[D])(using f: FileInfo): Parsley[Z] =
        f.pos <**> (a, b, c, d).mapN((a, b, c, d) => this.apply(_, a, b, c, d))

      def apply(a: Parsley[A], b: Parsley[B], c: Parsley[C])(using f: FileInfo): Parsley[D => Z] =
        f.pos <**> (a, b, c).mapN((a, b, c) => pos => d => this.apply(pos, a, b, c, d))

    trait PosBridge5[-A, -B, -C, -D, -E, +Z] extends PosSingleton[(A, B, C, D, E) => Z]:
      override final def con(pos: Pos): (A, B, C, D, E) => Z = this.apply(pos, _, _, _, _, _)

      def apply(pos: Pos, a: A, b: B, c: C, d: D, e: E): Z

      def apply(a: Parsley[A], b: Parsley[B], c: Parsley[C], d: Parsley[D], e: Parsley[E])(using f: FileInfo): Parsley[Z] =
        f.pos <**> (a, b, c, d, e).mapN((a, b, c, d, e) => this.apply(_, a, b, c, d, e))

      def curriedPos(using f: FileInfo): Parsley[A => B => C => D => E => Z] =
        this.make.map(_.curried)



  sealed trait BinopKind extends generic.ParserBridge0[BinopKind]
  object BinopKind:
    case object Equals extends BinopKind
    case object Unequal extends BinopKind
    case object Greater extends BinopKind
    case object GreaterEq extends BinopKind
    case object Less extends BinopKind
    case object LessEq extends BinopKind
    case object Plus extends BinopKind
    case object Minus extends BinopKind
    case object Times extends BinopKind
    case object Divide extends BinopKind
    case object Modulo extends BinopKind
    case object And extends BinopKind
    case object Or extends BinopKind
    case object Assign extends BinopKind
    case object AddAssign extends BinopKind
    case object SubAssign extends BinopKind
    case object MulAssign extends BinopKind
    case object DivAssign extends BinopKind
    case object ModAssign extends BinopKind
  sealed trait UnaryKind extends generic.ParserBridge0[UnaryKind]
  object UnaryKind:
    case object Not extends UnaryKind
    case object Negate extends UnaryKind
    case object Tilde extends UnaryKind
    case object Caret extends UnaryKind


  enum ArrayKind:
    case Any, Byte, Int, Long

  case class FunctionCall(path: UnresolvedResource, args: List[Expr])
  object FunctionCall extends generic.ParserBridge2[UnresolvedResource, List[Expr], FunctionCall]

  enum TimeType(val key: String):
    case Ticks extends TimeType("t")
    case Seconds extends TimeType("s")
    case Day extends TimeType("d")

  case class Delay(pos: bridge.Pos, n: Float, kind: TimeType):
    override def toString: String =
      s"$n${kind.key}"
  object Delay extends bridge.PosBridge2[Float, TimeType, Delay]

  case class Decorator(pos: bridge.Pos, name: String, args: List[Expr])
  object Decorator extends bridge.PosBridge2[String, List[Expr], Decorator]

  sealed trait Expr:
    def pos: bridge.Pos
    val executorSensitive = false
  object Expr:

    case class Binop(pos: bridge.Pos, name: BinopKind, l: Expr, r: Expr) extends Expr:
      override val executorSensitive: Boolean = l.executorSensitive || r.executorSensitive
    object Binop extends bridge.PosBridge3[BinopKind, Expr, Expr, Expr]

    case class Unary(pos: bridge.Pos, kind: UnaryKind, expr: Expr) extends Expr:
      override val executorSensitive: Boolean = expr.executorSensitive
    object Unary extends bridge.PosBridge2[UnaryKind, Expr, Expr]

    case class ZString(pos: bridge.Pos, contents: String) extends Expr
    object ZString extends bridge.PosBridge1[String, Expr]

    case class ZIntegral(pos: bridge.Pos, number: BigInt, suffix: Option[Char]) extends Expr
    object ZIntegral extends bridge.PosBridge2[BigInt, Option[Char], Expr]

    case class ZFloating(pos: bridge.Pos, number: BigDecimal, suffix: Option[Char]) extends Expr
    object ZFloating extends bridge.PosBridge2[BigDecimal, Option[Char], Expr]

    case class ZBool(pos: bridge.Pos, num: Boolean) extends Expr
    object ZBool extends bridge.PosBridge1[Boolean, Expr]

    case class ZList(pos: bridge.Pos, kind: ArrayKind, values: List[Expr]) extends Expr:
      override val executorSensitive: Boolean = values.exists(_.executorSensitive)
    object ZList extends bridge.PosBridge2[ArrayKind, List[Expr], Expr]

    case class ZCompound(pos: bridge.Pos, map: Map[String, Expr]) extends Expr:
      override val executorSensitive: Boolean = map.values.exists(_.executorSensitive)
    object ZCompound extends bridge.PosBridge1[Map[String, Expr], Expr]

    case class ZVariable(pos: bridge.Pos, path: UnresolvedResource) extends Expr:
      override val executorSensitive: Boolean = true
    object ZVariable extends bridge.PosBridge1[UnresolvedResource, Expr]

    case class ZScoreboardVariable(pos: bridge.Pos, path: UnresolvedResource) extends Expr:
      override val executorSensitive: Boolean = true
    object ZScoreboardVariable extends bridge.PosBridge1[UnresolvedResource, Expr]

    case class ZMacroVariable(pos: bridge.Pos, name: String) extends Expr
    object ZMacroVariable extends bridge.PosBridge1[String, Expr]

    case class ZFunctionCall(pos: bridge.Pos, functionCall: FunctionCall) extends Expr:
      override val executorSensitive: Boolean = true
    object ZFunctionCall extends bridge.PosBridge1[FunctionCall, Expr]

    case class ZMember(pos: bridge.Pos, name: String, expr: Expr) extends Expr:
      override val executorSensitive: Boolean = expr.executorSensitive
    object ZMember extends bridge.PosBridge2[String, Expr, Expr]

    case class ZIndex(pos: bridge.Pos, index: Expr, expr: Expr) extends Expr:
      override val executorSensitive: Boolean = expr.executorSensitive || index.executorSensitive
    object ZIndex extends bridge.PosBridge2[Expr, Expr, Expr]

    case class Atom(pos: bridge.Pos, expr: Expr) extends Expr:
      override val executorSensitive: Boolean = expr.executorSensitive
    object Atom extends bridge.PosBridge1[Expr, Expr]

    case class ZBuiltinCall(pos: bridge.Pos, call: BuiltinCall) extends Expr
    object ZBuiltinCall extends bridge.PosBridge1[BuiltinCall, Expr]

    object ZTrue extends bridge.PosSingleton[Expr] {
      def con(pos: bridge.Pos): Expr = ZBool(pos, true)
    }

    object ZFalse extends bridge.PosSingleton[Expr] {
      def con(pos: bridge.Pos): Expr = ZBool(pos, false)
    }

    



  enum ForRange:
    case Single(n: Expr)
    case Range(min: Expr, inclusive: Boolean, max: Expr)

  object ForRange:
    object Single extends generic.ParserBridge1[Expr, ForRange]
    object Range extends generic.ParserBridge3[Expr, Boolean, Expr, ForRange]



  enum BuiltinArg:
    case BExpr(pos: bridge.Pos, expr: Expr)
    case BBlock(pos: bridge.Pos, block: List[Stmt])

  object BuiltinArg:
    object BExpr extends bridge.PosBridge1[Expr, BuiltinArg]
    object BBlock extends bridge.PosBridge1[List[Stmt], BuiltinArg]

  case class BuiltinCall(name: String, args: List[BuiltinArg])
  object BuiltinCall extends generic.ParserBridge2[String, List[BuiltinArg], BuiltinCall]

  sealed trait CommandPart

  object CommandPart:
    case class Literal(str: String) extends CommandPart
    object Literal extends generic.ParserBridge1[String, CommandPart]
    case class Inserted(expr: InsertedExpr) extends CommandPart
    object Inserted extends generic.ParserBridge1[InsertedExpr, CommandPart]

  sealed trait InsertedExpr:
    def pos: bridge.Pos
  object InsertedExpr:
    case class MacroVariable(pos: bridge.Pos, name: String) extends InsertedExpr
    object MacroVariable extends bridge.PosBridge1[String, InsertedExpr]

    case class ScoreboardVariable(pos: bridge.Pos, path: UnresolvedResource) extends InsertedExpr
    object ScoreboardVariable extends bridge.PosBridge1[UnresolvedResource, InsertedExpr]

    case class ZFunctionCall(pos: bridge.Pos, functionCall: FunctionCall, pollute: Boolean) extends InsertedExpr
    object ZFunctionCall extends bridge.PosBridge2[FunctionCall, Boolean, ZFunctionCall]

    case class ResourceRef(pos: bridge.Pos, resource: UnresolvedResource) extends InsertedExpr
    object ResourceRef extends bridge.PosBridge1[UnresolvedResource, InsertedExpr]

    //case class FunctionRef(path: Option[UnresolvedResource]) extends InsertedExprNode
    //object FunctionRef extends bridge.NestedBridge1[Option[UnresolvedResource], InsertedExprNode, InsertedExpr], bridge.InsertedExprWrap

    case class ZBlock(pos: bridge.Pos, mayBeInlined: Boolean, stmts: List[Stmt]) extends InsertedExpr
    object ZBlock extends bridge.PosBridge2[Boolean, List[Stmt], InsertedExpr]

    case class ZBuiltinCall(pos: bridge.Pos, call: BuiltinCall) extends InsertedExpr
    object ZBuiltinCall extends bridge.PosBridge1[BuiltinCall, InsertedExpr]




  case class IfStatement(cond: Expr, block: List[Stmt], child: Option[ElseStatement])
  object IfStatement extends generic.ParserBridge3[Expr, List[Stmt], Option[ElseStatement], IfStatement]

  sealed trait ElseStatement
  object ElseStatement:
    case class EIfStatement(eif: IfStatement) extends ElseStatement
    object EIfStatement extends generic.ParserBridge1[IfStatement, ElseStatement]
    case class Block(stmts: List[Stmt]) extends ElseStatement
    object Block extends generic.ParserBridge1[List[Stmt], ElseStatement]

  enum PositionMode:
    case Absolute, Relative, Caret

    def prefix: String =
      this match
        case PositionMode.Absolute => ""
        case PositionMode.Relative => "~"
        case PositionMode.Caret => "^"
 
  case class CommandCoord(pos: Double, mode: PositionMode)

  case class CommandXYZ(x: CommandCoord, y: CommandCoord, z: CommandCoord)
  case class CommandYawPitch(yaw: CommandCoord, pitch: CommandCoord)

  sealed trait ExecutePart:
    def pos: bridge.Pos
  object ExecutePart:
    case class EAlign(pos: bridge.Pos, axes: String) extends ExecutePart
    case class EAnchored(pos: bridge.Pos, isEyes: Boolean) extends ExecutePart
    case class EAs(pos: bridge.Pos, selector: String) extends ExecutePart
    case class EAt(pos: bridge.Pos, selector: String) extends ExecutePart
    sealed trait EFacing extends ExecutePart
    object EFacing:
      case class EPosition(pos: bridge.Pos, coord: CommandXYZ) extends EFacing
      case class EEntity(pos: bridge.Pos, selector: String, isEyes: Boolean) extends EFacing
    
    case class EIn(pos: bridge.Pos, dimension: String) extends ExecutePart
    case class EOn(pos: bridge.Pos, relation: String) extends ExecutePart
    sealed trait EPositioned extends ExecutePart
    object EPositioned:
      case class EPosition(pos: bridge.Pos, coord: CommandXYZ) extends EPositioned
      case class EAs(pos: bridge.Pos, selector: String) extends EPositioned
      case class EOver(pos: bridge.Pos, heightmap: String) extends EPositioned
    sealed trait ERotated extends ExecutePart
    object ERotated:
      case class ERotation(pos: bridge.Pos, coord: CommandYawPitch) extends ERotated
      case class EAs(pos: bridge.Pos, selector: String) extends ERotated
    
    
    case class EIf(pos: bridge.Pos, condition: Expr) extends ExecutePart



  sealed trait Stmt:
    def pos: bridge.Pos
  object Stmt:
    case class Eval(pos: bridge.Pos, expr: Expr) extends Stmt
    object Eval extends bridge.PosBridge1[Expr, Stmt]

    case class Command(pos: bridge.Pos, parts: List[CommandPart]) extends Stmt
    object Command extends bridge.PosBridge1[List[CommandPart], Stmt]

    case class ZIf(pos: bridge.Pos, ifStatement: IfStatement) extends Stmt
    object ZIf extends bridge.PosBridge1[IfStatement, Stmt]

    case class ZWhile(pos: bridge.Pos, cond: Expr, continueExpr: Option[Expr], body: List[Stmt], label: Option[String]) extends Stmt
    object ZWhile extends bridge.PosBridge4[Expr, Option[Expr], List[Stmt], Option[String], Stmt]

    case class ZFor(pos: bridge.Pos, variable: Expr, range: ForRange, body: List[Stmt], label: Option[String]) extends Stmt
    object ZFor extends bridge.PosBridge4[Expr, ForRange, List[Stmt], Option[String], Stmt]

    case class ZDecorated(pos: bridge.Pos, decorators: List[Decorator], stmt: Stmt) extends Stmt
    object ZDecorated extends bridge.PosBridge2[List[Decorator], Stmt, Stmt]

    //case class ZForAs(pos: bridge.Pos, selector: String, body: List[Stmt]) extends Stmt
    //object ZForAs extends bridge.PosBridge2[String, List[Stmt], Stmt]

    //case class ZForAt(pos: bridge.Pos, selector: String, body: List[Stmt]) extends Stmt
    //object ZForAt extends bridge.PosBridge2[String, List[Stmt], Stmt]

    //case class ZExecuteFor(pos: bridge.Pos, s)

    //case class ZSpawnCall(pos: bridge.Pos, call: FunctionCall, delay: Delay) extends Stmt
    //object ZSpawnCall extends bridge.PosBridge2[FunctionCall, Delay, Stmt]

    case class ZReturn(pos: bridge.Pos, expr: Option[Expr]) extends Stmt
    object ZReturn extends bridge.PosBridge1[Option[Expr], Stmt]
    
    case class ZContinue(pos: bridge.Pos, label: Option[String]) extends Stmt
    object ZContinue extends bridge.PosBridge1[Option[String], Stmt]

    // TODO: this would require either an absurd number of generated functions, macros, or a signifigant change to the compiler
    //case class ZAsyncContinue(pos: bridge.Pos, label: Option[String], delay: Delay) extends Stmt
    //object ZAsyncContinue extends bridge.PosBridge2[Option[String], Delay, Stmt]

    case class ZBreak(pos: bridge.Pos, label: Option[String]) extends Stmt
    object ZBreak extends bridge.PosBridge1[Option[String], Stmt]


  enum ReturnType:
    case Storage, Scoreboard, Direct

  enum ParameterKind:
    case Storage extends ParameterKind, generic.ParserBridge0[ParameterKind]
    case Scoreboard extends ParameterKind, generic.ParserBridge0[ParameterKind]
    case Macro extends ParameterKind, generic.ParserBridge0[ParameterKind]
    case CompileTime extends ParameterKind, generic.ParserBridge0[ParameterKind]

  case class Parameter(location: bridge.Pos, kind: ParameterKind, name: String, default: Option[Expr])
  object Parameter:
    def apply(a: Parsley[ParameterKind], b: Parsley[String],c: Parsley[Option[Expr]])(using f: FileInfo): Parsley[Parameter] =
      f.pos <**> (a, b, c).zipped((x, y, z) => p => Parameter(p, x, y, z))

  sealed trait ResourceContent
  object ResourceContent:
    case class Text(name: String, json: io.circe.Json) extends ResourceContent
    case class File(basePath: String, path: String) extends ResourceContent

  sealed trait Decl:
    def pos: bridge.Pos
  
  object Decl:
    case class Module(pos: bridge.Pos, name: String, items: List[Decl]) extends Decl
    object Module extends bridge.PosBridge2[String, List[Decl], Decl]

    
    case class IncludedItems(pos: bridge.Pos, from: String, items: List[Decl]) extends Decl
    object IncludedItems extends bridge.PosBridge2[String, List[Decl], Decl]

    sealed abstract class ResolveTimeOnlyDecl extends Decl
    // Plain submodule that includes as a module
    case class SubModule(pos: bridge.Pos, name: String) extends ResolveTimeOnlyDecl
    object SubModule extends bridge.PosBridge1[String, Decl]

    // Includes the file `name` as if it were a module, but flattens its members into this module
    case class UsedModule(pos: bridge.Pos, name: String) extends ResolveTimeOnlyDecl
    object UsedModule extends bridge.PosBridge1[String, Decl]

    case class ZFunction(pos: bridge.Pos, returnType: ReturnType, name: String, params: List[Parameter], stmts: List[Stmt]) extends Decl
    object ZFunction extends bridge.PosBridge4[ReturnType, String, List[Parameter], List[Stmt], Decl]

    case class ZResource(pos: bridge.Pos, isAsset: Boolean, kind: String, content: ResourceContent) extends Decl
    object ZResource extends bridge.PosBridge3[Boolean, String, ResourceContent, Decl]

    case class ZConfig(pos: bridge.Pos, data: io.circe.Json) extends Decl
    object ZConfig extends bridge.PosBridge1[io.circe.Json, Decl]

    case class ZBuiltinCall(pos: bridge.Pos, call: BuiltinCall) extends Decl
    object ZBuiltinCall extends bridge.PosBridge1[BuiltinCall, Decl]



  case class Namespace(pos: bridge.Pos, name: String, items: List[Decl])
  object Namespace:
    def apply(name: Parsley[String], items: Parsley[List[Decl]])(using f: FileInfo): Parsley[Namespace] =
      (f.pos, name, items).mapN(Namespace.apply)
