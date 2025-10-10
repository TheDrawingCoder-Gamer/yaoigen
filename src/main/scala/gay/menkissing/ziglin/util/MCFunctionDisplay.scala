package gay.menkissing.ziglin.util

@FunctionalInterface
trait MCFunctionDisplay[T]:
  def mcdisplay(self: T): String

extension[T](self: T)(using x: MCFunctionDisplay[T])
  def mcdisplay: String =
    x.mcdisplay(self)


object MCFunctionDisplay:
  def fromToString[A]: MCFunctionDisplay[A] = a => a.toString

  given material[A](using z: MCFunctionDisplay[A]): Conversion[A, MCShown] = x => MCShown(z.mcdisplay(x))
  extension (ctx: StringContext)
    def mcfunc(args: MCShown*): String =
      ctx.s(args: _*)

// Copied from cats-core
final case class MCShown(override val toString: String) extends AnyVal




given MCFunctionDisplay[String] = identity
given MCFunctionDisplay[Int] = MCFunctionDisplay.fromToString[Int]