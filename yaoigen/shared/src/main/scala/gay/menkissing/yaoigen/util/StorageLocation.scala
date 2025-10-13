package gay.menkissing.yaoigen.util

import gay.menkissing.yaoigen.parser.ast.UnresolvedResource
import gay.menkissing.yaoigen.util.MCFunctionDisplay.{mcfunc, given}
import gay.menkissing.yaoigen.util.given

object StorageLocation:
  def fromFnLoc(fnLoc: ResourceLocation): StorageLocation =
    val (module, name) = fnLoc.trySplit.get
    StorageLocation(module, name)
  def resolveResource(fnLoc: ResourceLocation, resource: UnresolvedResource): StorageLocation =
    fromFnLoc(ResourceLocation.resolveResource(fnLoc, resource))

case class StorageLocation(storage: ResourceLocation, name: String)
    
given MCFunctionDisplay[StorageLocation] = a =>
  mcfunc"${a.storage} ${a.name}"