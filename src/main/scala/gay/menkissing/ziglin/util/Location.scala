package gay.menkissing.ziglin.util

import parsley.Parsley
import parsley.position.pos as ppos

import java.nio.file.Path

case class Location(line: Int, column: Int, file: String, root: String):
  def pretty: String =
    s"in ${Path.of(root, file).toString} at line ${line}, column ${column}"
object Location:
  def blank: Location =
    Location(0, 0, "", "")

case class FileInfo(file: String, root: String):
  val pos: Parsley[Location] =
    ppos.map((line, col) => Location(line, col, file, root))
