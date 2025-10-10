package gay.menkissing.ziglin.util

import gay.menkissing.ziglin.parser.ast.UnresolvedResource
import gay.menkissing.ziglin.util.MCFunctionDisplay.{mcfunc, given}
import gay.menkissing.ziglin.util.given

object StorageLocation:
  def fromFnLoc(fnLoc: ResourceLocation): StorageLocation =
    val (module, name) = fnLoc.trySplit.get
    StorageLocation(module, name)
  def resolveResource(fnLoc: ResourceLocation, resource: UnresolvedResource): StorageLocation =
    fromFnLoc(ResourceLocation.resolveResource(fnLoc, resource))

case class StorageLocation(storage: ResourceLocation, name: String)
    
given MCFunctionDisplay[StorageLocation] = a =>
  mcfunc"${a.storage} ${a.name}"