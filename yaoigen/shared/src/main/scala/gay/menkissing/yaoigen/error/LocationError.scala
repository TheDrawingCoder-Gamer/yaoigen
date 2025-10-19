package gay.menkissing.yaoigen.error

import parsley.errors.ErrorBuilder
import gay.menkissing.yaoigen.util.Location
import java.nio.file.Path
import java.nio.file.Files

object LocationError:
  // errorbuilder is basically an internal api, but its public and it is very
  // usable for what I need so : )
  def show(location: Location, msg: Seq[String])(using builder: ErrorBuilder[String]): String =
    
    import scala.jdk.CollectionConverters.*
    val badFile = Path.of(location.file)
    try
      val lines = Files.readAllLines(badFile).asScala.toList
      val lineInfo = builder.lineInfo(lines(location.line - 1), Seq(), Seq(), location.column, 1)

      val rawMessages = msg.map(builder.message)
      val messages = builder.combineMessages(rawMessages)
      
      val errLines = builder.specialisedError(messages, lineInfo)
      
      val pos = builder.pos(location.line, location.column)
      val source = builder.source(Some(badFile.toString))

      builder.format(pos, source, errLines)
    catch
      case _ => s"${location.pretty}\n${msg.mkString("\n")}"

