package gay.menkissing.ziglin

import parser.*
import parsley.cats.instances.*
import cats.implicits.*
import gay.menkissing.ziglin.util.FileInfo
import parsley.token.Lexer
import parsley.token.descriptions.*
import text.*
import parsley.token.predicate.Basic
import parsley.combinator.*
import parsley.{Failure, Parsley, Success}
import parsley.Parsley.atomic

import java.nio.charset.StandardCharsets
import java.nio.file.Path

object Parser:
  val nameDesc = {
    NameDesc.plain.copy(
      identifierStart = Basic(_.isLetter),
      identifierLetter = Basic(it => it.isLetterOrDigit || it == '_')
    )
  }

  val spaceDesc = SpaceDesc.plain.copy(
    commentStart = "/*",
    commentEnd = "*/",
    commentLine = "//",
    commentLineAllowsEOF = true,
    nestedComments = true,
    space = Basic(_.isWhitespace),
  )

  // Op 2 or below
  val commands = List(
    "advancement",
    "attribute",
    // "ban",
    // "ban-ip",
    // "banlist",
    "bossbar",
    "clear",
    "clone",
    "damage",
    "data",
    "datapack",
    // "debug",
    "defaultgamemode",
    "dialog",
    "difficulty",
    "effect",
    "enchant",
    "execute",
    "experience",
    "fetchprofile",
    "fill",
    "fillbiome",
    "forceload",
    "function",
    "gamemode",
    "gamerule",
    "give",
    // "help",
    "item",
    // "jfr",
    // "kick",
    "kill",
    "list",
    "locate",
    "loot",
    "me",
    "msg",
    // "op",
    // "pardon",
    // "pardon-ip",
    "particle",
    // "perf",
    "place",
    "playsound",
    "random",
    "recipe",
    "recipe",
    "reload",
    //"return",
    "ride",
    "rotate",
    // "save-all",
    // "save-off",
    // "save-on",
    "say",
    "schedule",
    "scoreboard",
    "seed",
    "setblock",
    "setworldspawn",
    "spawnpoint",
    "spectate",
    "spreadplayers",
    // "stop",
    "stopsound",
    "summon",
    "tag",
    "team",
    "teammsg",
    "teleport",
    "tell",
    "tellraw",
    "test",
    // "tick",
    "time",
    "title",
    "tm",
    "tp",
    // "transfer",
    "trigger",
    "version",
    "w",
    "waypoint",
    "weather",
    // "whitelist",
    "worldborder",
    "xp"
  )

  val hardKeywords = Set("or", "and", "fn", "module", "namespace", "include", "return", "if", "while", "else", "for", "continue", "break")
  val hardOperators = Set(
    "*", "+", "-", "/", "%",
    "*=", "+=", "-=", "/=", "%=", "=",
    "==", "!=", "<", ">", ">=", "<="
  )
  val symbolDesc =
    SymbolDesc.plain.copy(
      hardKeywords = hardKeywords,
      hardOperators = hardOperators
    )

  val textDesc =
    TextDesc.plain.copy(
      // we NEVER EVER use character so should be fine : )
      stringEnds = Set("\"", "'"),
      escapeSequences = EscapeDesc.haskell
    )

  val lexicalDesc =
    LexicalDesc.plain.copy(
      nameDesc = nameDesc,
      spaceDesc = spaceDesc,
      textDesc = textDesc,
      symbolDesc = symbolDesc
    )

  val lexer = new Lexer(lexicalDesc)




class Parser(val fileInfo: FileInfo):
  import Parser.lexer
  import lexer.lexeme
  import lexer.lexeme.symbol.implicits.implicitSymbol
  import lexer.nonlexeme



  given FileInfo = fileInfo

  object json:
    import io.circe.Json


    lazy val jroot: Parsley[Json] =
      jobject <|> jlist

    lazy val jvalue: Parsley[Json] =
      choice(
        lexeme.symbol("null").as(Json.Null),
        lexeme.symbol("false").as(Json.False),
        lexeme.symbol("true").as(Json.True),
        lexeme.signedCombined.number.map {
          case Left(bigInt) => Json.fromBigInt(bigInt)
          case Right(bigDecimal) => Json.fromBigDecimal(bigDecimal)
        },
        lexeme.string.fullUtf16.map(Json.fromString),
        jlist,
        jobject
      )

    lazy val objectKey: Parsley[String] =
      lexeme.names.identifier <|> lexeme.string.fullUtf16

    lazy val jlist: Parsley[Json] =
      lexeme.brackets(lexeme.commaSep(jvalue).map(Json.fromValues) <~ optional(lexeme.symbol.comma))

    lazy val jobject: Parsley[Json] =
      lexeme.braces(lexeme.commaSep((objectKey <~ lexeme.symbol.colon) <~> jvalue).map(Json.fromFields) <~ optional(lexeme.symbol.comma))

  lazy val expr: Parsley[ast.Expr] = {
    atomic(choice(
      op,
      primary
    ))
  }

  lazy val functionCall: Parsley[ast.Expr] = {
    ast.Expr.ZFunctionCall(ast.FunctionCall(ziglinResource, lexeme.parens(lexeme.commaSep(expr))))
  }

  lazy val primary: Parsley[ast.Expr] = {
    choice(
      ast.Expr.ZBool(lexeme.symbol("true").as(true) <|> lexeme.symbol("false").as(false)),
      atomic(ast.Expr.ZByte(lexer.nonlexeme.integer.number8[Byte] <* (parsley.character.satisfy(it => it == 'b' || it == 'B') <* lexer.space.whiteSpace))),
      atomic(ast.Expr.ZShort(lexer.nonlexeme.integer.number16[Short] <* (parsley.character.satisfy(it => it == 's' || it == 'S') <* lexer.space.whiteSpace))),
      atomic(ast.Expr.ZLong(lexer.nonlexeme.integer.number64[Long] <* (parsley.character.satisfy(it => it == 'l' || it == 'L') <* lexer.space.whiteSpace))),
      atomic(ast.Expr.ZFloat(lexer.nonlexeme.floating.float <* (parsley.character.satisfy(it => it == 'f' || it == 'F') <* lexer.space.whiteSpace))),
      atomic(ast.Expr.ZInt(lexer.nonlexeme.integer.number32[Int] <* (parsley.character.satisfy(it => it == 'i' || it == 'I') <* lexer.space.whiteSpace))),
      atomic(ast.Expr.ZDouble(lexer.nonlexeme.floating.double <* (parsley.character.satisfy(it => it == 'd' || it == 'D') <* lexer.space.whiteSpace))),
      atomic(ast.Expr.ZDouble(lexeme.floating.double)),
      atomic(ast.Expr.ZInt(lexeme.integer.number32[Int])),
      ast.Expr.Atom(lexeme.parens(expr)),
      list,
      compound,
      ast.Expr.ZString(lexeme.string.fullUtf16),
      atomic(functionCall),
      atomic(builtinCallExpr),
      ast.Expr.ZScoreboardVariable(parsley.character.char('$') *> scoreboardResource),
      ast.Expr.ZMacroVariable(parsley.character.char('%') *> lexeme.names.identifier),
      atomic(ast.Expr.ZVariable(ziglinResource))
    )
  }


  lazy val arrayKind: Parsley[ast.ArrayKind] =
    atomicChoice(
      (lexeme.symbol("I") *> lexeme.symbol.semi) *> Parsley.pure(ast.ArrayKind.Int),
      (lexeme.symbol("L") *> lexeme.symbol.semi) *> Parsley.pure(ast.ArrayKind.Long),
      (lexeme.symbol("B") *> lexeme.symbol.semi) *> Parsley.pure(ast.ArrayKind.Byte),
      Parsley.pure(ast.ArrayKind.Any)

    )
  lazy val list: Parsley[ast.Expr] = {
    lexeme.brackets(ast.Expr.ZList(arrayKind, lexeme.commaSep(expr)))
  }

  lazy val compound: Parsley[ast.Expr] = {
    lexeme.braces(ast.Expr.ZCompound(lexeme.commaSep(compoundKeyValue).map(_.toMap)))
  }

  lazy val compoundKeyValue: Parsley[(String,ast.Expr)] = {
    (choice(
      atomic(lexeme.names.identifier),
      lexeme.string.fullUtf16
    ) <* lexeme.symbol.colon) <~> expr
  }

  lazy val modulePath =
    Parsley.many(atomic(nonlexeme.names.identifier <* nonlexeme.symbol("/")))

  lazy val namespaceString: Parsley[String] =
    atomic(option(atomic(nonlexeme.names.identifier)).map(_.getOrElse("")) <~ nonlexeme.symbol.colon)
    <|> nonlexeme.symbol("~/").as("~")


  lazy val ziglinResourcePath: Parsley[(List[String], String)] =
    modulePath <~> nonlexeme.names.identifier

  lazy val ziglinResource: Parsley[ast.UnresolvedResource] =
    lexeme(
      (option(namespaceString), ziglinResourcePath).mapN { case (a, (b, c)) =>
        ast.UnresolvedResource(a, b, c)
      })

  val notBracketString =
    parsley.character.stringOfMany(it => !"[]".contains(it))

  lazy val nestedBracketString: Parsley[String] =
    // Parse whitespace INSIDE the brackets, but not after
    lexeme.symbol("[") ~> (notBracketString, option(nestedBracketString.map(it => "[" + it + "]")), notBracketString).mapN(_ + _.getOrElse("") + _) <~ nonlexeme.symbol("]")

  lazy val scoreboardResourcePath: Parsley[(List[String], String)] =
    modulePath <~> (nonlexeme.names.identifier.map(_.prepended('$')) <|> nestedBracketString)

  lazy val scoreboardResource: Parsley[ast.UnresolvedResource] =
    lexeme(
      (option(namespaceString), scoreboardResourcePath).mapN { case (a, (b, c)) =>
        ast.UnresolvedResource(a, b, c)
      })


  lazy val builtinCallExpr: Parsley[ast.Expr] =
    ast.Expr.ZBuiltinCall(builtinCall)

  lazy val builtinCall: Parsley[ast.BuiltinCall] =
    ast.BuiltinCall(nonlexeme.symbol("@") ~> lexeme.names.identifier, lexeme.parens(lexeme.commaSep(expr)))

  lazy val op: Parsley[ast.Expr] = {
    import parsley.expr.*
    import ast.Expr.{Unary, Binop}
    import ast.{BinopKind, UnaryKind}
    parsley.expr.precedence(
      primary
    )(
      Ops[ast.Expr](Prefix)(Unary(UnaryKind.Negate <# "-"), Unary(UnaryKind.Not <# "!")),
      Ops[ast.Expr](InfixL)(Binop(BinopKind.Modulo <# "%")),
      Ops[ast.Expr](InfixL)(Binop(BinopKind.Divide <# "/"), Binop(BinopKind.Times <# "*")),
      Ops[ast.Expr](InfixL)(Binop(BinopKind.Plus <# "+"), Binop(BinopKind.Minus <# "-")),
      Ops[ast.Expr](InfixL)(Binop(BinopKind.Greater <# ">"), Binop(BinopKind.GreaterEq <# ">="), Binop(BinopKind.Less <# "<"), Binop(BinopKind.LessEq <# "<=")),
      Ops[ast.Expr](InfixL)(Binop(BinopKind.Equals <# "=="), Binop(BinopKind.Unequal <# "!=")),
      Ops[ast.Expr](InfixL)(Binop(BinopKind.And <# "and")),
      Ops[ast.Expr](InfixL)(Binop(BinopKind.Or <# "or")),
      // assignment
      Ops[ast.Expr](InfixR)(
        Binop(BinopKind.Assign <# "="),
        Binop(BinopKind.AddAssign <# "+="),
        Binop(BinopKind.SubAssign <# "-="),
        Binop(BinopKind.MulAssign <# "*="),
        Binop(BinopKind.DivAssign <# "/="),
        Binop(BinopKind.ModAssign <# "%=")
      )
    )
  }

  lazy val stmt: Parsley[ast.Stmt] = {
      (quotedCommand <~ optional(lexeme.symbol.semi))
      <|>  whileStmt
      <|> forStmt
      <|> continueStmt
      <|> breakStmt
      <|> ast.Stmt.ZIf(ifStmt)
      <|> (returnStmt <~ optional(lexeme.symbol.semi))
      <|> atomic(unquotedCommand)
      <|> (evalExpr <~ optional(lexeme.symbol.semi))
  }
  
  lazy val continueStmt: Parsley[ast.Stmt] =
    (ast.Stmt.ZContinue <# lexeme.symbol("continue")) <~ optional(lexeme.symbol.semi)
  
  lazy val breakStmt: Parsley[ast.Stmt] =
    (ast.Stmt.ZBreak <# lexeme.symbol("break")) <~ optional(lexeme.symbol.semi)

  def commandPartShared(invalidCharacters: String): Parsley[ast.CommandPart] =
    atomicChoice(
      ast.CommandPart.Inserted(nonlexeme.symbol("&!") ~> ast.InsertedExpr.ZBlock(option(nonlexeme.symbol("!")).map(_.nonEmpty), lexeme.symbol.openBrace ~> Parsley.many(atomic(stmt)) <~ nonlexeme.symbol("}"))),
      ast.CommandPart.Inserted(nonlexeme.symbol("%") ~> ast.InsertedExpr.MacroVariable(nonlexeme.names.identifier)),
      ast.CommandPart.Inserted(nonlexeme.symbol("&") ~> (lexeme.symbol.openBrace ~> inlineInserted <~ nonlexeme.symbol("}"))),
      ast.CommandPart.Literal(parsley.character.string("\\&") #> "&"),
      ast.CommandPart.Literal(parsley.character.string("\\%") #> "%"),
      ast.CommandPart.Literal(parsley.character.string("\\`") #> "`"),
      ast.CommandPart.Literal(parsley.character.stringOfSome(it => !invalidCharacters.contains(it)))
    )

  lazy val quotedCommandPart: Parsley[ast.CommandPart] =
    commandPartShared("`&%")

  lazy val unquotedCommandPart: Parsley[ast.CommandPart] =
    commandPartShared("`&%\n")

  lazy val inlineInserted: Parsley[ast.InsertedExpr] =
    atomicChoice(
      ast.InsertedExpr.ScoreboardVariable(parsley.character.char('$') *> scoreboardResource),
      ast.InsertedExpr.MacroVariable(parsley.character.char('%') *> lexeme.names.identifier),
      ast.InsertedExpr.ResourceRef(ziglinResource),
      ast.InsertedExpr.ZBuiltinCall(builtinCall)
    )

  lazy val quotedCommand =
    lexeme(ast.Stmt.Command(parsley.character.char('`') ~> Parsley.many(quotedCommandPart) <~ parsley.character.char('`')))

  lazy val unquotedCommand =
    lexeme(ast.Stmt.Command((parsley.character.strings(Parser.commands.head, Parser.commands.tail:_*), parsley.character.stringOfSome(parsley.character.whitespace), Parsley.many(unquotedCommandPart)).mapN { (start, space, rest) =>
      rest.prepended(ast.CommandPart.Literal(start + space))
    }))

  val whileKeyword = lexeme.symbol("while")

  lazy val block: Parsley[List[ast.Stmt]] = lexeme.braces(Parsley.many(atomic(stmt)))

  val barSymbol = lexeme.symbol("|")

  lazy val whileStmt: Parsley[ast.Stmt] = {
     ast.Stmt.ZWhile(whileKeyword ~> expr, option(barSymbol ~> expr <~ barSymbol), block)
  }

  lazy val forRange: Parsley[ast.ForRange] =
    atomic(ast.ForRange.Range(expr, (lexeme.symbol("until") #> false) <|> (lexeme.symbol("to") #> true), expr))
    <|> ast.ForRange.Single(expr)

  lazy val forStmt: Parsley[ast.Stmt] =
    ast.Stmt.ZFor(lexeme.symbol("for") ~> expr, lexeme.symbol("in") ~> forRange, block)

  lazy val ifStmt: Parsley[ast.IfStatement] = {
    ast.IfStatement(lexeme.symbol("if") ~> expr, block, option(elseStmt))
  }

  lazy val elseStmt: Parsley[ast.ElseStatement] = {
    lexeme.symbol("else") *> choice(
      atomic(ast.ElseStatement.EIfStatement(ifStmt)),
      ast.ElseStatement.Block(lexeme.braces(Parsley.many(stmt)))
    )
  }


  lazy val returnKeyword: Parsley[Unit] = lexeme.symbol("return")
  lazy val returnStmt: Parsley[ast.Stmt] = {
    lexeme(ast.Stmt.ZReturn(returnKeyword *> option(atomic(expr))))
  }


  lazy val evalExpr: Parsley[ast.Stmt] = {
    // Consume newlines here
    ast.Stmt.Eval(expr)
  }

  lazy val decl: Parsley[ast.Decl] = {
    choice(
      module,
      fnDecl,
      freakyResource,
      includedItems,
      ast.Decl.ZBuiltinCall(builtinCall)
    )
  }

  lazy val resourcePath: Parsley[String] =
    choice(
      lexeme.symbol.dot.as("."),
      (modulePath.map(it => if it.isEmpty then "" else it.mkString("", "/", "/")) <~> lexeme.names.identifier).map(_ + _)
    )

  lazy val freakyResource: Parsley[ast.Decl] =
    ast.Decl.ZResource(lexeme.symbol("res").as(false) <|> lexeme.symbol("asset").as(true), resourcePath, fileResourceBody <|> jsonResourceBody)


  lazy val fileResourceBody: Parsley[ast.ResourceContent] =
    lexeme.string.fullUtf16.map { str =>
      if str.startsWith("/") then
        ast.ResourceContent.File(fileInfo.root, str.tail)
      else
        ast.ResourceContent.File(fileInfo.file, str)
    }

  lazy val jsonResourceBody: Parsley[ast.ResourceContent] =
    (lexeme.names.identifier <~> json.jroot).map(ast.ResourceContent.Text.apply)



  lazy val module:  Parsley[ast.Decl] =
    lexeme.symbol("module") *> ast.Decl.Module(lexeme.names.identifier, lexeme.braces(Parsley.many(decl)))


  // TODO: recursion prevention
  lazy val includedItems: Parsley[ast.Decl] =
    lexeme.symbol("include") *> lexeme.string.fullUtf16.flatMap { rel_path =>
      child(rel_path)
    }.impure

  def child(name: String): Parsley[ast.Decl] =
    val actualName = if !name.endsWith(".ziglin") then name + ".ziglin" else name
    val newPath = Path.of(fileInfo.file).resolveSibling(actualName).normalize()
    val newInfo = fileInfo.copy(file = newPath.toString)
    val newParser = Parser(newInfo)
    val fileData = java.nio.file.Files.readString(newPath, StandardCharsets.UTF_8)
    lexer.fully(Parsley.many(newParser.decl)).parse(fileData) match
      case Success(x) => fileInfo.pos.map(p => ast.Decl.IncludedItems(p, name, x))
      case failure: Failure[_] => parsley.errors.combinator.fail(s"Error in file $newPath:", failure.msg.toString)

  lazy val fnPrefixType: Parsley[ast.ReturnType] =
    choice(
      parsley.character.char('%') #> ast.ReturnType.Direct,
      parsley.character.char('$') #> ast.ReturnType.Scoreboard,
      Parsley.pure(ast.ReturnType.Storage)
    )

  lazy val fnParamKind: Parsley[ast.ParameterKind] =
    choice(
      parsley.character.char('%') #> ast.ParameterKind.Macro,
      parsley.character.char('$') #> ast.ParameterKind.Scoreboard,
      parsley.character.char('&') #> ast.ParameterKind.CompileTime,
      Parsley.pure(ast.ParameterKind.Storage)
    )

  lazy val fnParam: Parsley[ast.Parameter] =
    ast.Parameter(fnParamKind, lexeme.names.identifier, option(lexeme.symbol("=") *> expr))


  lazy val fnDecl: Parsley[ast.Decl] =
    lexeme.symbol("fn") *> ast.Decl.ZFunction(fnPrefixType, lexeme.names.identifier, lexeme.parens(lexeme.commaSep(fnParam)), block)

  def namespace: Parsley[ast.Namespace] =
    lexeme.symbol("namespace") *> ast.Namespace(lexeme.names.identifier, lexeme.braces(Parsley.many(decl)))

  def parseAll: Parsley[List[ast.Namespace]] = lexer.fully(Parsley.many(namespace))

