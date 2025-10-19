package gay.menkissing.yaoigen

import language.experimental.saferExceptions

object Main:
  def main(args: Array[String]): Unit =
    var fileIn: Option[String] = None
    var outputIn: Option[String] = None
    var force: Boolean = false
    var wrong = false

    var i = 0

    while i < args.length do
      args(i) match
        case "--force" =>
          force = true
        case "--output" | "-o" =>
          i += 1
          if i == args.length then
            println("Expected path after --output")
            return
          outputIn = Some(args(i))
        case i if i.startsWith("--") =>
          println(s"Error, incorrect argument $i")
          wrong = true
        case it =>
          fileIn = Some(it)
      i += 1
    
    if wrong then
      return
    val file = fileIn match {
      case None =>
        println("Error, need root file to compile")
        return
      case Some(v) => v
    }
    run(file, force, outputIn.getOrElse("build"))
  private def run(file: String, force: Boolean, output: String): Unit =
    val resolver = new Resolver
    resolver.resolveTrees(file) match
      case Left(err) =>
        println(err.showPretty)
      case Right(resolved) =>
        val compiler = new Compiler
        compiler.compile(resolved, output, force) match
          case Left(err) =>
            println(err.showPretty)
          case _ => ()


