import Mettapedia.GSLT.Core.RelationPresentation
import Mettapedia.GSLT.LanguageDef.GSLTILRouteEquipment

/-! # Authored routes interpreted as proof-relevant relations -/

namespace Mettapedia.GSLT.RelationPresentation
namespace AuthoredRoute

open Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax
open Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Internalize an authored route occurrence without requiring it to be a
function.  Every `RouteWitness` remains an inhabitant of the proof-relevant relation. -/
def internalize (program : Program) (route : RouteDecl) :
    Rel Pattern Pattern :=
  Rel.ofLoose (routeLoose program route)

@[simp] theorem internalize_toLoose (program : Program) (route : RouteDecl) :
    (internalize program route).toLoose = routeLoose program route :=
  rfl

/-- Restrict an authored route to a selected typed source and target fibre,
while retaining its exact authored witnesses. -/
def internalizeTyped {program : Program} {route : RouteDecl}
    (profile : TypedRouteProfile program route) :
    Rel profile.Source profile.Target :=
  Rel.ofLoose profile.related

@[simp] theorem internalizeTyped_toLoose
    {program : Program} {route : RouteDecl}
    (profile : TypedRouteProfile program route) :
    (internalizeTyped profile).toLoose = profile.related :=
  rfl

/-- GSLT-IL route admission and relational representability are the
same evidence at the typed-fibre seam. -/
def licenseEquiv {program : Program} {route : RouteDecl}
    (profile : TypedRouteProfile program route) :
    profile.License ≃ Rel.Representation (internalizeTyped profile) :=
  Equiv.refl _

/-- A route witness remains executable before representability is known. -/
def executeWithoutLicense {program : Program} {route : RouteDecl}
    (profile : TypedRouteProfile program route)
    {source : profile.Source} {target : profile.Target}
    (witness : profile.related source target) :
    (internalizeTyped profile).evidence source target :=
  witness

/-- Once a route is licensed, its internalized relation is fibrewise
equivalent to the graph of the compiled map. -/
def representedAsGraph {program : Program} {route : RouteDecl}
    {profile : TypedRouteProfile program route}
    (license : profile.License) (source : profile.Source)
    (target : profile.Target) :
    (internalizeTyped profile).evidence source target ≃
      (Rel.graph (profile.compile license)).evidence source target :=
  license.exact source target

/-- The represented map exposed through the relational presentation is exactly the GSLT-IL
compiled map; no second compilation choice is introduced. -/
@[simp] theorem represented_map_agrees
    {program : Program} {route : RouteDecl}
    {profile : TypedRouteProfile program route}
    (license : profile.License) :
    ((licenseEquiv profile) license).map = profile.compile license :=
  rfl

end AuthoredRoute

end Mettapedia.GSLT.RelationPresentation
