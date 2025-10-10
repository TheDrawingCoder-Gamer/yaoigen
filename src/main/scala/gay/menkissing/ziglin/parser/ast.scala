package gay.menkissing.ziglin.parser

import parsley.position.pos
import parsley.Parsley
import cats.implicits.*
import gay.menkissing.ziglin.util.{FileInfo, Location}
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

    trait PosBridge0[+Z]:
      def apply(pos: Pos): Z

      def <#(name: Parsley[?])(using f: FileInfo): Parsley[Z] = f.pos.map(p => this.apply(p)) <~ name

    trait PosBridge1[-A, +Z]:
      def apply(pos: Pos, a: A): Z

      def apply(a: Parsley[A])(using f: FileInfo): Parsley[Z] = f.pos <**> a.map(a => pos => this.apply(pos, a))



    trait NestedBridge[Y, +Z]:
      def wrap(it: Y)(pos: Pos): Z

    trait NestedSingleton[X, +Y, +Z] extends NestedBridge[X, Z]:
      def con(pos: Pos): Y
      def <#(name: Parsley[?])(using f: FileInfo): Parsley[Y] = f.pos.map(p => this.con(p)) <* name

    trait NestedObject[Y, +Z] extends NestedSingleton[Y, Z, Z]:
      def con: Y
      override def con(pos: Pos): Z = this.wrap(this.con)(pos)

    trait NestedBridge0[Y, +Z] extends NestedSingleton[Y, Z, Z]:
      this: Y =>
      override def con(pos: Pos): Z = this.wrap(this)(pos)

    trait NestedBridge1[-A, Y, +Z] extends NestedSingleton[Y, A => Z, Z]:
      def apply(x: A): Y
      def apply(x: Parsley[A])(using f: FileInfo): Parsley[Z] = f.pos <**> x.map((it) => p => this.wrap(this.apply(it))(p))
      override def con(pos: Pos): A => Z = a => this.wrap(this.apply(a))(pos)

    trait NestedBridge2[-A, -B, Y, +Z] extends NestedSingleton[Y, (A, B) => Z, Z]:
      def apply(x: A, y: B): Y

      def apply(a: Parsley[A], b: Parsley[B])(using f: FileInfo): Parsley[Z] = {
        f.pos <**> (a, b).zipped((a, b) => this.wrap(this.apply(a, b)))
      }

      def apply(a: Parsley[A])(using f: FileInfo): Parsley[B => Z] = f.pos <**> a.map(a => pos => b => this.wrap(this.apply(a, b))(pos))


      override def con(pos: Pos): (A, B) => Z = (a, b) => this.wrap(this.apply(a, b))(pos)

    trait NestedBridge3[-A, -B, -C, Y, +Z] extends NestedSingleton[Y, (A, B, C) => Z, Z]:
      def apply(x: A, y: B, c: C): Y

      def apply(a: Parsley[A], b: Parsley[B], c: Parsley[C])(using f: FileInfo): Parsley[Z] = {
        f.pos <**> (a, b, c).zipped((a, b, c) => this.wrap(this.apply(a, b, c)))
      }

      def apply(a: Parsley[A])(using f: FileInfo): Parsley[(B, C) => Z] = f.pos <**> a.map(a => p => (b, c) => this.wrap(apply(a, b, c))(p))


      override def con(pos: Pos): (A, B, C) => Z = (a, b, c) => this.wrap(this.apply(a, b, c))(pos)

    trait NestedBridge4[-A, -B, -C, -D, Y, +Z] extends NestedSingleton[Y, (A, B, C, D) => Z, Z]:
      def apply(x: A, y: B, c: C, d: D): Y

      def apply(a: Parsley[A], b: Parsley[B], c: Parsley[C], d: Parsley[D])(using f: FileInfo): Parsley[Z] = {
        f.pos <**> (a, b, c, d).zipped((a, b, c, d) => this.wrap(this.apply(a, b, c, d)))
      }

      override def con(pos: Pos): (A, B, C, D) => Z = (a, b, c, d) => this.wrap(this.apply(a, b, c, d))(pos)

    trait NestedBridge5[-A, -B, -C, -D, -E, Y, +Z] extends NestedSingleton[Y, (A, B, C, D, E) => Z, Z]:
      def apply(x: A, y: B, c: C, d: D, e: E): Y

      def apply(a: Parsley[A], b: Parsley[B], c: Parsley[C], d: Parsley[D], e: Parsley[E])(using f: FileInfo): Parsley[Z] = {
        f.pos <**> (a, b, c, d, e).zipped((a, b, c, d, e) => this.wrap(this.apply(a, b, c, d, e)))
      }

      override def con(pos: Pos): (A, B, C, D, E) => Z = (a, b, c, d, e) => this.wrap(this.apply(a, b, c, d, e))(pos)

    trait ExprWrap extends NestedBridge[ExprNode, Expr]:
      override def wrap(it: ExprNode)(pos: Pos): Expr = Expr(it, pos)

    trait InsertedExprWrap extends NestedBridge[InsertedExprNode, InsertedExpr]:
      override def wrap(it: InsertedExprNode)(pos: Pos): InsertedExpr = InsertedExpr(it, pos)

    trait StmtWrap extends NestedBridge[StmtNode, Stmt]:
      override def wrap(it: StmtNode)(pos: Pos): Stmt = Stmt(it, pos)

    trait DeclWrap extends NestedBridge[DeclNode, Decl]:
      override def wrap(it: DeclNode)(pos: Pos): Decl = Decl(it, pos)


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


  enum ArrayKind:
    case Any, Byte, Int, Long

  case class FunctionCall(path: UnresolvedResource, args: List[Expr])
  object FunctionCall extends generic.ParserBridge2[UnresolvedResource, List[Expr], FunctionCall]

  sealed trait ExprNode:
    def unknownLocation: Expr =
      Expr(this, Location.blank)
  object Expr:
    object Node:
      def unapply(x: Expr): Option[ExprNode] =
        Some(x.expr)

    case class Binop(name: BinopKind, l: Expr, r: Expr) extends ExprNode
    object Binop extends bridge.NestedBridge3[BinopKind, Expr, Expr, ExprNode, Expr], bridge.ExprWrap

    case class Unary(kind: UnaryKind, expr: Expr) extends ExprNode
    object Unary extends bridge.NestedBridge2[UnaryKind, Expr, ExprNode, Expr], bridge.ExprWrap

    case class ZString(contents: String) extends ExprNode
    object ZString extends bridge.NestedBridge1[String, ExprNode, Expr], bridge.ExprWrap

    case class ZByte(num: Byte) extends ExprNode
    object ZByte extends bridge.NestedBridge1[Byte, ExprNode, Expr], bridge.ExprWrap

    case class ZShort(num: Short) extends ExprNode
    object ZShort extends bridge.NestedBridge1[Short, ExprNode, Expr], bridge.ExprWrap

    case class ZInt(num: Int) extends ExprNode
    object ZInt extends bridge.NestedBridge1[Int, ExprNode, Expr], bridge.ExprWrap

    case class ZLong(num: Long) extends ExprNode
    object ZLong extends bridge.NestedBridge1[Long, ExprNode, Expr], bridge.ExprWrap

    case class ZFloat(num: Float) extends ExprNode
    object ZFloat extends bridge.NestedBridge1[Float, ExprNode, Expr], bridge.ExprWrap

    case class ZDouble(num: Double) extends ExprNode
    object ZDouble extends bridge.NestedBridge1[Double, ExprNode, Expr], bridge.ExprWrap

    case class ZBool(num: Boolean) extends ExprNode
    object ZBool extends bridge.NestedBridge1[Boolean, ExprNode, Expr], bridge.ExprWrap

    case class ZList(kind: ArrayKind, values: List[Expr]) extends ExprNode
    object ZList extends bridge.NestedBridge2[ArrayKind, List[Expr], ExprNode, Expr], bridge.ExprWrap

    case class ZCompound(map: Map[String, Expr]) extends ExprNode
    object ZCompound extends bridge.NestedBridge1[Map[String, Expr], ExprNode, Expr], bridge.ExprWrap

    case class ZVariable(path: UnresolvedResource) extends ExprNode
    object ZVariable extends bridge.NestedBridge1[UnresolvedResource, ExprNode, Expr], bridge.ExprWrap

    case class ZScoreboardVariable(path: UnresolvedResource) extends ExprNode
    object ZScoreboardVariable extends bridge.NestedBridge1[UnresolvedResource, ExprNode, Expr], bridge.ExprWrap

    case class ZMacroVariable(name: String) extends ExprNode
    object ZMacroVariable extends bridge.NestedBridge1[String, ExprNode, Expr], bridge.ExprWrap

    case class ZFunctionCall(functionCall: FunctionCall) extends ExprNode
    object ZFunctionCall extends bridge.NestedBridge1[FunctionCall, ExprNode, Expr], bridge.ExprWrap

    case class Atom(expr: Expr) extends ExprNode
    object Atom extends bridge.NestedBridge1[Expr, ExprNode, Expr], bridge.ExprWrap

    case class ZBuiltinCall(call: BuiltinCall) extends ExprNode
    object ZBuiltinCall extends bridge.NestedBridge1[BuiltinCall, ExprNode, Expr], bridge.ExprWrap

    object ZTrue extends bridge.NestedObject[ExprNode, Expr], bridge.ExprWrap {
      def con = ZBool(true)
    }

    object ZFalse extends bridge.NestedObject[ExprNode, Expr], bridge.ExprWrap {
      def con = ZBool(false)
    }

    



  enum ForRange:
    case Single(n: Expr)
    case Range(min: Expr, inclusive: Boolean, max: Expr)

  object ForRange:
    object Single extends generic.ParserBridge1[Expr, ForRange]
    object Range extends generic.ParserBridge3[Expr, Boolean, Expr, ForRange]


  case class Expr(expr: ExprNode, pos: bridge.Pos)


  case class BuiltinCall(name: String, args: List[Expr])
  object BuiltinCall extends generic.ParserBridge2[String, List[Expr], BuiltinCall]

  sealed trait CommandPart

  object CommandPart:
    case class Literal(str: String) extends CommandPart
    object Literal extends generic.ParserBridge1[String, CommandPart]
    case class Inserted(expr: InsertedExpr) extends CommandPart
    object Inserted extends generic.ParserBridge1[InsertedExpr, CommandPart]

  sealed trait InsertedExprNode
  object InsertedExpr:
    case class MacroVariable(name: String) extends InsertedExprNode
    object MacroVariable extends bridge.NestedBridge1[String, InsertedExprNode, InsertedExpr], bridge.InsertedExprWrap

    case class ScoreboardVariable(path: UnresolvedResource) extends InsertedExprNode
    object ScoreboardVariable extends bridge.NestedBridge1[UnresolvedResource, InsertedExprNode, InsertedExpr], bridge.InsertedExprWrap

    //case class ZFunctionCall(functionCall: FunctionCall) extends InsertedExprNode
    //object ZFunctionCall extends bridge.NestedBridge1[FunctionCall, InsertedExprNode, InsertedExpr], bridge.InsertedExprWrap

    case class ResourceRef(resource: UnresolvedResource) extends InsertedExprNode
    object ResourceRef extends bridge.NestedBridge1[UnresolvedResource, InsertedExprNode, InsertedExpr], bridge.InsertedExprWrap

    //case class FunctionRef(path: Option[UnresolvedResource]) extends InsertedExprNode
    //object FunctionRef extends bridge.NestedBridge1[Option[UnresolvedResource], InsertedExprNode, InsertedExpr], bridge.InsertedExprWrap

    case class ZBlock(mayBeInlined: Boolean, stmts: List[Stmt]) extends InsertedExprNode
    object ZBlock extends bridge.NestedBridge2[Boolean, List[Stmt], InsertedExprNode, InsertedExpr], bridge.InsertedExprWrap

    case class ZBuiltinCall(call: BuiltinCall) extends InsertedExprNode
    object ZBuiltinCall extends bridge.NestedBridge1[BuiltinCall, InsertedExprNode, InsertedExpr], bridge.InsertedExprWrap




  case class InsertedExpr(node: InsertedExprNode, pos: bridge.Pos)

  case class IfStatement(cond: Expr, block: List[Stmt], child: Option[ElseStatement])
  object IfStatement extends generic.ParserBridge3[Expr, List[Stmt], Option[ElseStatement], IfStatement]

  sealed trait ElseStatement
  object ElseStatement:
    case class EIfStatement(eif: IfStatement) extends ElseStatement
    object EIfStatement extends generic.ParserBridge1[IfStatement, ElseStatement]
    case class Block(stmts: List[Stmt]) extends ElseStatement
    object Block extends generic.ParserBridge1[List[Stmt], ElseStatement]

  sealed trait StmtNode
  object Stmt:
    case class Eval(expr: Expr) extends StmtNode
    object Eval extends bridge.NestedBridge1[Expr, StmtNode, Stmt], bridge.StmtWrap

    case class Command(parts: List[CommandPart]) extends StmtNode
    object Command extends bridge.NestedBridge1[List[CommandPart], StmtNode, Stmt], bridge.StmtWrap

    case class ZIf(ifStatement: IfStatement) extends StmtNode
    object ZIf extends bridge.NestedBridge1[IfStatement, StmtNode, Stmt], bridge.StmtWrap

    case class ZWhile(cond: Expr, continueExpr: Option[Expr], body: List[Stmt]) extends StmtNode
    object ZWhile extends bridge.NestedBridge3[Expr, Option[Expr], List[Stmt], StmtNode, Stmt], bridge.StmtWrap

    case class ZFor(variable: Expr, range: ForRange, body: List[Stmt]) extends StmtNode
    object ZFor extends bridge.NestedBridge3[Expr, ForRange, List[Stmt], StmtNode, Stmt], bridge.StmtWrap

    case class ZReturn(expr: Option[Expr]) extends StmtNode
    object ZReturn extends bridge.NestedBridge1[Option[Expr], StmtNode, Stmt], bridge.StmtWrap
    
    case object ZContinue extends StmtNode, bridge.NestedBridge0[StmtNode, Stmt], bridge.StmtWrap
    case object ZBreak extends StmtNode, bridge.NestedBridge0[StmtNode, Stmt], bridge.StmtWrap

  case class Stmt(expr: StmtNode, pos: bridge.Pos)

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

  sealed trait DeclNode
  object Decl:
    case class Module(name: String, items: List[Decl]) extends DeclNode
    object Module extends bridge.NestedBridge2[String, List[Decl], DeclNode, Decl], bridge.DeclWrap

    case class IncludedItems(from: String, items: List[Decl]) extends DeclNode
    object IncludedItems extends bridge.NestedBridge2[String, List[Decl], DeclNode, Decl], bridge.DeclWrap


    case class ZFunction(returnType: ReturnType, name: String, params: List[Parameter], stmts: List[Stmt]) extends DeclNode
    object ZFunction extends bridge.NestedBridge4[ReturnType, String, List[Parameter], List[Stmt], DeclNode, Decl], bridge.DeclWrap

    case class ZResource(isAsset: Boolean, kind: String, content: ResourceContent) extends DeclNode
    object ZResource extends bridge.NestedBridge3[Boolean, String, ResourceContent, DeclNode, Decl], bridge.DeclWrap

    case class ZBuiltinCall(call: BuiltinCall) extends DeclNode
    object ZBuiltinCall extends bridge.NestedBridge1[BuiltinCall, DeclNode, Decl], bridge.DeclWrap




  case class Decl(node: DeclNode, pos: bridge.Pos)

  case class Namespace(pos: bridge.Pos, name: String, items: List[Decl])
  object Namespace:
    def apply(name: Parsley[String], items: Parsley[List[Decl]])(using f: FileInfo): Parsley[Namespace] =
      f.pos <**> (name, items).zipped((n, is) => p => Namespace(p, n, is))