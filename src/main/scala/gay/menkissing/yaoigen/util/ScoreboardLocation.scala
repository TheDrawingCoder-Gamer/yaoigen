package gay.menkissing.yaoigen.util

import gay.menkissing.yaoigen.parser.ast.UnresolvedResource

case class ScoreboardLocation(scoreboard: ResourceLocation, name: String):
  def scoreboardString: String =
    ScoreboardLocation.scoreboardStringOf(scoreboard)


given MCFunctionDisplay[ScoreboardLocation] = a =>
  s"${a.name} ${a.scoreboardString}"
    
object ScoreboardLocation:
  def scoreboardStringOf(scoreboard: ResourceLocation): String =
    if scoreboard.modules.isEmpty then
      scoreboard.namespace
    else
      scoreboard.namespace + "." + scoreboard.modules.mkString("", ".", "")
  
  def fromFnLoc(fnLoc: ResourceLocation): ScoreboardLocation =
    val (module, name) = fnLoc.trySplit.get
    ScoreboardLocation(module, name)
  def resolveResource(fnLoc: ResourceLocation, resource: UnresolvedResource): ScoreboardLocation =
    fromFnLoc(ResourceLocation.resolveResource(fnLoc, resource))
  def internal(namespace: String, name: String): ScoreboardLocation =
    ScoreboardLocation(ResourceLocation("yaoigen", List("internal", namespace, "vars"), ResourceKind.Func), name)