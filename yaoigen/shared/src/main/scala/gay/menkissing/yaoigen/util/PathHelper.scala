package gay.menkissing.yaoigen.util

object PathHelper:
  def subPath(root: String, sub: String): String =
    val specialName = StringEscape.escaped(sub)
    val saveName =
      if specialName == sub && !sub.head.isDigit && sub.forall(it => it.isLetterOrDigit || it == '_') then
        sub
      else
        s"\"$specialName\""
    
    if root.isEmpty then
      saveName
    else
      s"$root.$saveName"
  def index(root: String, n: Int): String =
    s"$root[$n]"