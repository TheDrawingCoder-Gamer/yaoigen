package gay.menkissing.yaoigen.util

import parsley.Parsley
import parsley.position.pos as ppos
import cats.*

case class Location(line: Int, column: Int, file: String, root: String):
  def pretty: String =
    s"${file}:${line}:${column}"

given Show[Location] = _.pretty

object Location:
  def blank: Location =
    Location(0, 0, "", "")

case class FileInfo(file: String, root: String):
  val pos: Parsley[Location] =
    ppos.map((line, col) => Location(line, col, file, root))
