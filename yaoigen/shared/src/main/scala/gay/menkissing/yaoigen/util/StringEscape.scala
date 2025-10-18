package gay.menkissing.yaoigen.util

object StringEscape:
  def escapedCodePoint(c: Int): String =
    c match
      case '\t' => "\\t"
      case '\r' => "\\r"
      case '\n' => "\\n"
      case '\'' => "\\'"
      case '\"' => "\\\""
      case '\\' => "\\\\"
      case x =>
        if x >= 0x20 && x <= 0x7E then
          String.valueOf(Character.toChars(x))
        else
          val nStr = x.toHexString
          val padding = "0".repeat(8 - nStr.length)
          s"\\U${padding}${nStr}"
  extension (v: String)
    def escaped: String =
      v.codePoints().toArray.map(escapedCodePoint).mkString("")
