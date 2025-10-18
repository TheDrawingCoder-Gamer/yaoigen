package gay.menkissing.yaoigen

import parser.*
import parsley.cats.instances.*
import cats.implicits.*
import cats.*
import gay.menkissing.yaoigen.util.FileInfo
import parsley.token.Lexer
import parsley.token.descriptions.*
import parsley.errors.combinator.*
import text.*
import parsley.token.predicate.Basic
import parsley.combinator.*
import parsley.{Failure, Parsley, Success}
import parsley.Parsley.atomic

import java.nio.charset.StandardCharsets
import java.nio.file.Path
import gay.menkissing.yaoigen.parser.ast.UnresolvedResource

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

  val hardKeywords = Set("or", "and", "fn", "module", "namespace", "include", "return", "if", "while", "else", "for", "continue", "break", "use")
  val hardOperators = Set(
    "*", "+", "-", "/", "%",
    "*=", "+=", "-=", "/=", "%=", "=",
    "==", "!=", "<", ">", ">=", "<=",
    "~/", "~", "^"
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


  lazy val functionArguments: Parsley[List[ast.Expr]] =
    lexeme.parens(lexeme.commaSep(expr) <* optional(lexeme.symbol.comma))

  lazy val functionCall: Parsley[ast.FunctionCall] = {
    ast.FunctionCall(unresolvedResource, functionArguments)
  }

  lazy val indexRec: Parsley[ast.Expr => ast.Expr] =
    Defer[Parsley].fix[ast.Expr => ast.Expr] { self =>
      (choice[ast.Expr => ast.Expr](
      ast.Expr.ZMember(lexeme.symbol.dot ~> (lexeme.names.identifier <|> lexeme.string.fullUtf16)),
      ast.Expr.ZIndex(lexeme.brackets(expr)),
      ) <**> self.map[(ast.Expr => ast.Expr) => ast.Expr => ast.Expr](f => g => g.andThen(f))) </> identity
    }

    
  lazy val index: Parsley[ast.Expr] =
    primary <**> indexRec
    

  lazy val primary: Parsley[ast.Expr] = {
    choice(
      ast.Expr.ZBool(lexeme.symbol("true").as(true) <|> lexeme.symbol("false").as(false)),
      floating,
      integral,
      
      ast.Expr.Atom(lexeme.parens(expr)),
      list,
      compound,
      ast.Expr.ZString(lexeme.string.fullUtf16),
      builtinCallExpr,
      ast.Expr.ZScoreboardVariable(parsley.character.char('$') *> scoreboardResource).label("scoreboard variable"),
      ast.Expr.ZMacroVariable(parsley.character.char('%') *> lexeme.names.identifier).label("macro variable"),
      callOrVariable
    )
  }

  lazy val callOrVariable: Parsley[ast.Expr] =
    (fileInfo.pos, unresolvedResource).tupled <**>
      choice(
        functionArguments.map[((util.Location, UnresolvedResource)) => ast.Expr](args => { case (pos, path) => ast.Expr.ZFunctionCall(pos, ast.FunctionCall(path, args)) }).label("function call"),
        Parsley.pure[((util.Location, UnresolvedResource)) => ast.Expr] { case (pos, path) => ast.Expr.ZVariable(pos, path) }.label("variable")
      )

  lazy val floating: Parsley[ast.Expr] =
    lexeme:
      (fileInfo.pos, lexer.nonlexeme.floating.number).tupled <**>
        choice(
          (parsley.character.satisfy(_.toLower == 'f') <~ lexer.space.whiteSpace) #> ((pos, i) => ast.Expr.ZFloat(pos, i.toFloat)),
          (parsley.character.satisfy(_.toLower == 'd') <~ lexer.space.whiteSpace) #> ((pos, i) => ast.Expr.ZDouble(pos, i.toDouble)),
          Parsley.pure((pos, i) => ast.Expr.ZDouble(pos, i.toDouble))
        )

  lazy val integral: Parsley[ast.Expr] = 
    lexeme:
      (fileInfo.pos, lexer.nonlexeme.integer.number).tupled <**>
      // TODO: someway to error out here if we truncate?
        choice(
          (parsley.character.satisfy(_.toLower == 'b') <* lexer.space.whiteSpace) #> ((pos, i) => ast.Expr.ZByte(pos, i.toByte)),
          (parsley.character.satisfy(_.toLower == 's') <* lexer.space.whiteSpace) #> ((pos, i) => ast.Expr.ZShort(pos, i.toShort)),
          (parsley.character.satisfy(_.toLower == 'i') <* lexer.space.whiteSpace) #> ((pos, i) => ast.Expr.ZInt(pos, i.toInt)),
          (parsley.character.satisfy(_.toLower == 'l') <* lexer.space.whiteSpace) #> ((pos, i) => ast.Expr.ZLong(pos, i.toLong)),
          (parsley.character.satisfy(_.toLower == 'f') <* lexer.space.whiteSpace) #> ((pos, i) => ast.Expr.ZFloat(pos, i.toFloat)),
          (parsley.character.satisfy(_.toLower == 'd') <* lexer.space.whiteSpace) #> ((pos, i) => ast.Expr.ZDouble(pos, i.toDouble)),
          Parsley.pure((pos, i) => ast.Expr.ZInt(pos, i.toInt))
        )


  lazy val arrayKind: Parsley[ast.ArrayKind] =
    (lexeme.symbol("I") *> lexeme.symbol.semi).as(ast.ArrayKind.Int)
    <|> (lexeme.symbol("L") *> lexeme.symbol.semi).as(ast.ArrayKind.Long)
    <|> (lexeme.symbol("B") *> lexeme.symbol.semi).as(ast.ArrayKind.Byte)
    </> ast.ArrayKind.Any
  lazy val list: Parsley[ast.Expr] = {
    lexeme.brackets(ast.Expr.ZList(arrayKind, lexeme.commaSep(expr)))
  }

  lazy val compound: Parsley[ast.Expr] = {
    // #{ in case we ever need to do compounds in builtins
    (lexeme.symbol.openBrace <|> lexeme.symbol("#{")) *> ast.Expr.ZCompound(lexeme.commaSep(compoundKeyValue).map(_.toMap) <* optional(lexeme.symbol.comma)) <* lexeme.symbol.closingBrace
  }

  lazy val compoundKeyValue: Parsley[(String,ast.Expr)] = {
    ((lexeme.string.fullUtf16 <|> lexeme.names.identifier) <* lexeme.symbol.colon) <~> expr
  }

  lazy val modulePath =
    Parsley.many(atomic(nonlexeme.names.identifier <* nonlexeme.symbol("/")))

  lazy val namespaceString: Parsley[String] =
    // TODO: way to remove atomic here?
    atomic(option(atomic(nonlexeme.names.identifier)).map(_.getOrElse("")) <~ nonlexeme.symbol.colon)
    <|> nonlexeme.symbol("~/").as("~")


  lazy val unresolvedResourcePath: Parsley[(List[String], String)] =
    sepBy1(nonlexeme.names.identifier, nonlexeme.symbol("/")).map(ls => (ls.init, ls.last))

  lazy val unresolvedResource: Parsley[ast.UnresolvedResource] =
    lexeme:
      (option(namespaceString), unresolvedResourcePath).mapN { case (a, (b, c)) =>
        ast.UnresolvedResource(a, b, c)
      }

  val notBracketString =
    parsley.character.stringOfMany(it => !"[]".contains(it))

  lazy val nestedBracketString: Parsley[String] =
    // Parse whitespace INSIDE the brackets, but not after
    lexeme.symbol("[") ~> (notBracketString, option(nestedBracketString), notBracketString).tupled.span <~ nonlexeme.symbol("]")

  lazy val scoreboardResourcePath: Parsley[(List[String], String)] =
    modulePath <~> (nonlexeme.names.identifier.map(_.prepended('$')) <|> nestedBracketString)

  lazy val scoreboardResource: Parsley[ast.UnresolvedResource] =
    lexeme(
      (option(namespaceString), scoreboardResourcePath).mapN { case (a, (b, c)) =>
        ast.UnresolvedResource(a, b, c)
      })


  lazy val builtinCallExpr: Parsley[ast.Expr] =
    ast.Expr.ZBuiltinCall(builtinCall)

  lazy val builtinArg: Parsley[ast.BuiltinArg] =
    ast.BuiltinArg.BBlock(block)
    <|> ast.BuiltinArg.BExpr(expr)

  lazy val builtinCall: Parsley[ast.BuiltinCall] =
    ast.BuiltinCall(nonlexeme.symbol("@") ~> lexeme.names.identifier, lexeme.parens(lexeme.commaSep(builtinArg)))

  lazy val expr: Parsley[ast.Expr] = {
    import parsley.expr.*
    import ast.Expr.{Unary, Binop}
    import ast.{BinopKind, UnaryKind}
    parsley.expr.precedence(
      index
    )(
      Ops[ast.Expr](Prefix)(Unary(UnaryKind.Negate <# "-"), Unary(UnaryKind.Not <# "!"), Unary(UnaryKind.Tilde <# "~"), Unary(UnaryKind.Caret <# "^")),
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
      (quotedCommand <* optional(lexeme.symbol.semi))
      <|> labeledDefinition
      <|> continueStmt
      <|> breakStmt
      <|> ast.Stmt.ZIf(ifStmt)
      <|> (returnStmt <* optional(lexeme.symbol.semi))
      <|> unquotedCommand
      <|> (evalExpr <* optional(lexeme.symbol.semi))
  }
  
  lazy val continueStmt: Parsley[ast.Stmt] =
    ast.Stmt.ZContinue(lexeme.symbol("continue") ~> option(labelReference)) <~ optional(lexeme.symbol.semi)
  
  lazy val breakStmt: Parsley[ast.Stmt] =
    ast.Stmt.ZBreak(lexeme.symbol("break") ~> option(labelReference)) <~ optional(lexeme.symbol.semi)

  // TODO: weed out atomic here
  def commandPartShared(invalidCharacters: String): Parsley[ast.CommandPart] =
    atomic(ast.CommandPart.Inserted(nonlexeme.symbol("&!") ~> ast.InsertedExpr.ZBlock(option(nonlexeme.symbol("!")).map(_.nonEmpty), lexeme.symbol.openBrace ~> Parsley.many(stmt) <~ nonlexeme.symbol("}"))))
    <|> atomic(ast.CommandPart.Inserted(nonlexeme.symbol("%") ~> ast.InsertedExpr.MacroVariable(nonlexeme.names.identifier)))
    <|> ast.CommandPart.Inserted(lexeme.symbol("&@{") ~> insertedFunctionCall.map(_(true)) <~ nonlexeme.symbol("}"))
    <|> (atomic(lexeme.symbol("&{")) ~> ast.CommandPart.Inserted(inlineInserted <~ nonlexeme.symbol("}")))
    // if we got here, then it must have been an invalid insert
    <|> atomic(ast.CommandPart.Literal(parsley.character.string("&") #> "&"))
    <|> atomic(ast.CommandPart.Literal(parsley.character.string("%") #> "%"))
    <|> atomic(ast.CommandPart.Literal(parsley.character.string("\\`") #> "`"))
    <|> ast.CommandPart.Literal(parsley.character.stringOfSome(it => !invalidCharacters.contains(it)))
    

  lazy val quotedCommandPart: Parsley[ast.CommandPart] =
    commandPartShared("`&%")

  lazy val unquotedCommandPart: Parsley[ast.CommandPart] =
    commandPartShared("`&%\n")

  lazy val insertedFunctionCall: Parsley[Boolean => ast.InsertedExpr.ZFunctionCall] =
    ast.InsertedExpr.ZFunctionCall(functionCall)


  lazy val resourceRefOrCall: Parsley[ast.InsertedExpr] =
    (fileInfo.pos, unresolvedResource).tupled <**>
      choice(
        functionArguments.map(args => {case (pos, res) => ast.InsertedExpr.ZFunctionCall(pos, ast.FunctionCall(res, args), false)}),
        Parsley.pure { case (pos, res) => ast.InsertedExpr.ResourceRef(pos, res) }
      )

  lazy val inlineInserted: Parsley[ast.InsertedExpr] =
    ast.InsertedExpr.ScoreboardVariable(parsley.character.char('$') *> scoreboardResource)
    <|> ast.InsertedExpr.MacroVariable(parsley.character.char('%') *> lexeme.names.identifier)
    <|> ast.InsertedExpr.ZBuiltinCall(builtinCall)
    <|> resourceRefOrCall
      
    

  lazy val quotedCommand =
    lexeme(ast.Stmt.Command(parsley.character.char('`') ~> Parsley.many(quotedCommandPart) <~ parsley.character.char('`')))

  lazy val unquotedCommand =
    lexeme:
      ast.Stmt.Command:
        // OK I think the atomic here is justified
        (atomic(parsley.character.strings(Parser.commands.head, Parser.commands.tail*) <~> parsley.character.stringOfSome(parsley.character.whitespace)) <~> Parsley.many(unquotedCommandPart)).map:
          case ((start, space), rest) =>
            rest.prepended(ast.CommandPart.Literal(start + space))


  val whileKeyword = lexeme.symbol("while")

  lazy val block: Parsley[List[ast.Stmt]] = lexeme.braces(Parsley.many(stmt))

  val barSymbol = lexeme.symbol("|")

  lazy val labelDefinition: Parsley[String] =
    nonlexeme.names.identifier <~ lexeme.symbol.colon

  lazy val labelReference: Parsley[String] =
    nonlexeme.symbol(":") ~> lexeme.names.identifier

  lazy val whileStmt: Parsley[Option[ast.Delay] => Option[String] => ast.Stmt] = {
    ast.Stmt.ZWhile.curriedPos <*> (whileKeyword ~> expr) <*> option(barSymbol ~> expr <~ barSymbol) <*> block
    
  }

  lazy val forRange: Parsley[ast.ForRange] =
    expr <**>
      choice(
        (lexeme.symbol("until").as(false) <|> lexeme.symbol("to").as(true), expr).mapN((inclusive, max) => min => ast.ForRange.Range(min, inclusive, max)),
        Parsley.pure(ast.ForRange.Single.apply)
      )



  lazy val labeledDefinition: Parsley[ast.Stmt] =
    option(atomic(labelDefinition)) <**> loop
    
  lazy val delay: Parsley[ast.Delay] =
    lexeme(
      ast.Delay(
        nonlexeme.unsignedCombined.number32Float[Int].map:
          case Left(v) => v.toFloat
          case Right(r) => r,
        choice(
          lexeme.symbol("d") #> ast.TimeType.Day,
          lexeme.symbol("s") #> ast.TimeType.Seconds,
          lexeme.symbol("t") #> ast.TimeType.Ticks
        ) </> ast.TimeType.Ticks
      )
    )
    

  lazy val spawn: Parsley[ast.Delay] =
    // TODO: stupid no good spawn NOT being a keyword causes jank...
    // but it being a keyword ALSO causes jank
    lexeme.symbol("spawn") ~> lexeme.parens(delay)


  lazy val loop: Parsley[Option[String] => ast.Stmt] =
    option(atomic(spawn)) <**> 
      (forStmt <|> whileStmt)


  lazy val forStmt: Parsley[Option[ast.Delay] => Option[String] => ast.Stmt] =
    ast.Stmt.ZFor.curriedPos <*> (lexeme.symbol("for") ~> expr) <*> (lexeme.symbol("in") ~> forRange) <*> block


  lazy val ifStmt: Parsley[ast.IfStatement] = {
    ast.IfStatement(lexeme.symbol("if") ~> expr, block, option(elseStmt))
  }

  lazy val elseStmt: Parsley[ast.ElseStatement] = {
    lexeme.symbol("else") *> choice(
      ast.ElseStatement.EIfStatement(ifStmt),
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
      config,
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

  lazy val config: Parsley[ast.Decl] =
    ast.Decl.ZConfig(lexeme.symbol("mcmeta") ~> json.jroot)

  lazy val module:  Parsley[ast.Decl] =
    lexeme.symbol("module") *> ast.Decl.Module(lexeme.names.identifier, lexeme.braces(Parsley.many(decl)))


  // TODO: recursion prevention
  lazy val includedItems: Parsley[ast.Decl] =
    lexeme.symbol("include") *> lexeme.string.fullUtf16.flatMap { rel_path =>
      child(rel_path)
    }.impure

  def child(name: String): Parsley[ast.Decl] =
    val actualName = if !name.endsWith(".yaoi") then name + ".yaoi" else name
    val newPath = Path.of(fileInfo.file).resolveSibling(actualName).normalize()
    val newInfo = fileInfo.copy(file = newPath.toString)
    val newParser = Parser(newInfo)
    val fileData = java.nio.file.Files.readString(newPath, StandardCharsets.UTF_8)
    lexer.fully(Parsley.many(newParser.decl)).parse(fileData) match
      case Success(x) => fileInfo.pos.map(p => ast.Decl.IncludedItems(p, name, x))
      case failure: Failure[_] => parsley.errors.combinator.fail(s"Error in file ${newPath.toString}:", failure.msg.toString)

  lazy val fnPrefixType: Parsley[ast.ReturnType] =
    choice(
      parsley.character.char('%') #> ast.ReturnType.Direct,
      parsley.character.char('$') #> ast.ReturnType.Scoreboard,
      Parsley.pure(ast.ReturnType.Storage)
    )

  lazy val fnParamKind: Parsley[ast.ParameterKind] =
    parsley.character.char('%').as(ast.ParameterKind.Macro)
    <|> parsley.character.char('$').as(ast.ParameterKind.Scoreboard)
    <|> parsley.character.char('&').as(ast.ParameterKind.CompileTime)
    </> ast.ParameterKind.Storage

  lazy val fnParam: Parsley[ast.Parameter] =
    ast.Parameter(fnParamKind, lexeme.names.identifier, option(lexeme.symbol("=") *> expr))


  lazy val fnDecl: Parsley[ast.Decl] =
    lexeme.symbol("fn") *> ast.Decl.ZFunction(fnPrefixType, lexeme.names.identifier, lexeme.parens(lexeme.commaSep(fnParam)), block)

  def namespace: Parsley[ast.Namespace] =
    lexeme.symbol("namespace") *> ast.Namespace(lexeme.names.identifier, lexeme.braces(Parsley.many(decl)))

  def parseAll: Parsley[List[ast.Namespace]] = lexer.fully(Parsley.many(namespace))

