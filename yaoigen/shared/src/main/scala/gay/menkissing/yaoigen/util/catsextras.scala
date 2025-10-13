package gay.menkissing.yaoigen.util

import cats.*
import cats.implicits.*

object catsextras {
  extension[F[_], A] (self: F[A])(using app: Applicative[F]) {
    infix def <**>[B](that: F[A => B]): F[B] =
        (self, that).mapN((x, f) => f(x))
  }
}
