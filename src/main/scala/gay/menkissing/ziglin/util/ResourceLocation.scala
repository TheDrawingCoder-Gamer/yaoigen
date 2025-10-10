package gay.menkissing.ziglin.util

import gay.menkissing.ziglin.parser.ast.UnresolvedResource
import scala.collection.mutable

case class ResourceLocation(
                           namespace: String,
                           modules: List[String],
                           kind: ResourceKind
                           ):
  def join(next: String): ResourceLocation =
    copy(modules = modules.appended(next))
    
  def withName(name: String): ResourceLocation =
    copy(modules = modules.appended(name), kind = ResourceKind.Func)

  def extended(ls: List[String]): ResourceLocation =
    copy(modules = modules ++ ls)

  def module: ResourceLocation =
    kind match
      case ResourceKind.Func =>
        copy(kind = ResourceKind.Module, modules = modules.init)
      case ResourceKind.Module => this

  def trySplit: Option[(ResourceLocation, String)] =
    kind match
      case ResourceKind.Func =>
        val newSelf = copy(modules = modules.init, kind = ResourceKind.Func)
        Some((newSelf, modules.last))

      case ResourceKind.Module => None


object ResourceLocation:
  def module(namespace: String, modules: List[String]): ResourceLocation =
    ResourceLocation(namespace, modules, ResourceKind.Module)

  def function(namespace: String, modules: List[String]): ResourceLocation =
    ResourceLocation(namespace, modules, ResourceKind.Func)
  
  def resolveResource(baseLocation: ResourceLocation, resource: UnresolvedResource): ResourceLocation =

    resource.namespace match
      case Some(v) =>
        var namespace = v
        if v.isEmpty then
          namespace = baseLocation.namespace
        else if v == "~" then
          var loc = baseLocation.module

          loc = loc.extended(resource.modules)
          val name =
            if resource.name.isEmpty then
              val last = loc.modules.last
              loc = loc.copy(modules = loc.modules.init)
              last
            else
              resource.name
          return loc.withName(name)
        end if

        ResourceLocation(namespace, resource.modules, ResourceKind.Module).withName(resource.name)
      case None =>
        var loc = baseLocation
        loc = loc.extended(resource.modules)
        loc.withName(resource.name)


enum ResourceKind:
  case Func, Module

given MCFunctionDisplay[ResourceLocation] = x =>
  s"${x.namespace}:${x.modules.mkString("","/","")}"