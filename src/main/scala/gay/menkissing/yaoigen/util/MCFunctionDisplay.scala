package gay.menkissing.yaoigen.util

import language.implicitConversions

@FunctionalInterface
trait MCFunctionDisplay[T]:
  def mcdisplay(self: T): String

extension[T](self: T)(using x: MCFunctionDisplay[T])
  def mcdisplay: String =
    x.mcdisplay(self)


object MCFunctionDisplay:
  def fromToString[A]: MCFunctionDisplay[A] = a => a.toString

  implicit def material[A](x: A)(using z: MCFunctionDisplay[A]):MCShown = MCShown(z.mcdisplay(x))
  extension (ctx: StringContext)
    def mcfunc(args: MCShown*): String =
      ctx.s(args*)

// Copied from cats-core
final case class MCShown(override val toString: String) extends AnyVal




given MCFunctionDisplay[String] = identity
given MCFunctionDisplay[Int] = MCFunctionDisplay.fromToString[Int]