package gay.menkissing.yaoigen.util

import gay.menkissing.yaoigen.parser.ast.UnresolvedResource
import gay.menkissing.yaoigen.util.MCFunctionDisplay.{mcfunc, given}
import gay.menkissing.yaoigen.util.given

object StorageLocation:
  def fromFnLoc(fnLoc: ResourceLocation): StorageLocation =
    val (module, name) = fnLoc.trySplit.get
    // resource location with no path is apparently perfectly valid?
    StorageLocation(module, name)
  def resolveResource(fnLoc: ResourceLocation, resource: UnresolvedResource): StorageLocation =
    fromFnLoc(ResourceLocation.resolveResource(fnLoc, resource))

case class StorageLocation(storage: ResourceLocation, name: String):
  def subPath(sub: String): StorageLocation =
    copy(name = PathHelper.subPath(name, sub))
  def index(n: Int): StorageLocation =
    copy(name = PathHelper.index(name, n))
    
given MCFunctionDisplay[StorageLocation] = a =>
  mcfunc"${a.storage} ${a.name}"