package gay.menkissing.yaoigen.util

import cats.*
import cats.implicits.*

object catsextras {
  extension[F[_], A] (self: F[A])(using app: Apply[F]) {
    infix def <**>[B](that: F[A => B]): F[B] =
        (self, that).mapN((x, f) => f(x))
  }

  private case class IsMap[F[_], T <: Tuple](value: Tuple.Map[T, F])

  private inline def tupledGeneric[F[_], T <: Tuple](tuple: Tuple.Map[T, F])(using app: Apply[F]): F[T] =
    inline IsMap[F, T](tuple) match
      case t: IsMap[F, _ *: EmptyTuple] => app.map(t.value.head)(_ *: EmptyTuple)
      case t: IsMap[F, _ *: _] =>
        val head = t.value.head
        val tail = tupledGeneric(t.value.tail)
        app.map2(head, tail)(_ *: _)

  extension[H, T <: Tuple, F[_]](tuple: F[H] *: T)(using toMap: Tuple.IsMappedBy[F][T], app: Apply[F])
    inline def tupledEx: F[H *: Tuple.InverseMap[T, F]] =
      tupledGeneric(tuple.head *: toMap(tuple.tail))
  
    inline def mapNEx[R](f: (H *: Tuple.InverseMap[T, F]) => R): F[R] =
      app.map(tuple.tupledEx)(f)
    
    inline def reverseApN[R](f: F[(H *: Tuple.InverseMap[T, F]) => R]): F[R] =
      tuple.tupledEx <**> f
}
