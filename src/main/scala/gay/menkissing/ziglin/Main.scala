package gay.menkissing.ziglin

import java.nio.charset.StandardCharsets
import parsley.*

@main def main(file: String): Unit =
  val path = java.nio.file.Path.of(file)
  val fileContent = java.nio.file.Files.readString(path, StandardCharsets.UTF_8)
  val parser = Parser(util.FileInfo(path.toString, path.toString))
  parser.parseAll.parse(fileContent) match
    case Success(ast) => 
      // println(ast)
      println("parsed")
      val compiler = new Compiler
      compiler.compile(ast, "build")
    case Failure(v) => 
      println(v)

