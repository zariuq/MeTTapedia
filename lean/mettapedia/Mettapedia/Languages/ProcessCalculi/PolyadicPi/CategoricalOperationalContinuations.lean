import Mettapedia.Languages.ProcessCalculi.PolyadicPi.CategoricalOperationalGraph
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.CategoricalOperations
import Mettapedia.CategoryTheory.InternalCategoryVertexIso

/-!
# Retained path categories at the complete continuation interface

The actual path diagram is read at the extended name context. The earned
context-function comparison makes its vertices the complete return functions.
The edge object retains the whole finite path, and its function presentation
is compared with the actual function object of paths. Composition uses the
chosen matching pullback; elementary firing evidence enters as one-edge paths.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.CategoricalOperationalContinuations

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory
open Mettapedia.OSLF.Binding
open IntrinsicScopedOperationalPresheafContextHom
open IntrinsicScopedOperationalPresheafEvents
open CategoricalOperational

private theorem map_readout {first second : Ambient} (map : first ⟶ second)
    {world future : Base} (change : world ⟶ future) (supplied : first.obj world) :
    second.map change (map.app world supplied) =
      map.app future (first.map change supplied) :=
  (map.naturality_apply change supplied).symm

abbrev names : Ambient := CategoricalOperations.names algebra
abbrev terms : Ambient := names.functorHom processes
abbrev pathCategory := internalCategory
abbrev pathEdges : Ambient := pathCategory.edge
abbrev extension : Base ⥤ Base := binderExtension algebra [Srt.nm]

/-- The genuine category-valued path diagram at the extended name context. -/
def diagram : Base ⥤ Cat :=
  extension ⋙ InternalCategoryPathDiagram.diagram graph

def extendedCategory : InternalCategory Ambient :=
  InternalCategoryDiagram.category diagram

/-- Every complete continuation is its actual extended-context program. -/
def vertexComparison : terms ≅ extendedCategory.vertex :=
  contextHomIso algebra [Srt.nm] processes

/-- The category laws are transported from the actual retained-path category. -/
def category : InternalCategory Ambient :=
  InternalCategoryVertexIso.category extendedCategory vertexComparison

/-- Whole return functions of paths and the actual edge object agree. -/
def edgeComparison : names.functorHom pathEdges ≅ category.edge :=
  contextHomIso algebra [Srt.nm] pathEdges

private theorem context_map {first second : Ambient} (map : first ⟶ second) :
    (FunctorToTypes.rightAdj names).map map ≫
        (contextHomIso algebra [Srt.nm] second).hom =
      (contextHomIso algebra [Srt.nm] first).hom ≫
        Functor.whiskerLeft extension map := by
  ext world function
  exact contextHomAtEquiv_map algebra [Srt.nm] map world function

@[reassoc] theorem source_complete :
    edgeComparison.hom ≫ category.source =
      (FunctorToTypes.rightAdj names).map pathCategory.source := by
  apply (cancel_mono vertexComparison.hom).mp
  change (contextHomIso algebra [Srt.nm] pathEdges).hom ≫
      ((Functor.whiskerLeft extension pathCategory.source ≫ vertexComparison.inv) ≫
        vertexComparison.hom) = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (context_map pathCategory.source).symm

@[reassoc] theorem target_complete :
    edgeComparison.hom ≫ category.target =
      (FunctorToTypes.rightAdj names).map pathCategory.target := by
  apply (cancel_mono vertexComparison.hom).mp
  change (contextHomIso algebra [Srt.nm] pathEdges).hom ≫
      ((Functor.whiskerLeft extension pathCategory.target ≫ vertexComparison.inv) ≫
        vertexComparison.hom) = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (context_map pathCategory.target).symm

@[reassoc] theorem unit_complete :
    category.unit ≫ edgeComparison.inv =
      (FunctorToTypes.rightAdj names).map pathCategory.unit := by
  apply (cancel_mono edgeComparison.hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact context_map pathCategory.unit

/-- The original elementary receipt enters as its actual one-edge path. -/
def eventInclusion : names.functorHom edges ⟶ category.edge :=
  (FunctorToTypes.rightAdj names).map (InternalCategoryPathDiagram.edgeInclusion graph) ≫
    edgeComparison.hom

@[reassoc] theorem eventInclusion_source :
    eventInclusion ≫ category.source =
      (FunctorToTypes.rightAdj names).map source := by
  rw [eventInclusion, Category.assoc, source_complete, ← Functor.map_comp]
  exact congrArg ((FunctorToTypes.rightAdj names).map)
    (InternalCategoryPathDiagram.edgeInclusion_source graph)

@[reassoc] theorem eventInclusion_target :
    eventInclusion ≫ category.target =
      (FunctorToTypes.rightAdj names).map target := by
  rw [eventInclusion, Category.assoc, target_complete, ← Functor.map_comp]
  exact congrArg ((FunctorToTypes.rightAdj names).map)
    (InternalCategoryPathDiagram.edgeInclusion_target graph)

/-- Reading the inclusion retains the exact supplied event at the extended world. -/
theorem eventInclusion_readout (world : Base)
    (function : (names.functorHom edges).obj world) :
    eventInclusion.app world function =
      InternalCategoryPathDiagram.edge graph (extension.obj world)
        (contextHomAtEquiv algebra [Srt.nm] edges world function) :=
  contextHomAtEquiv_map algebra [Srt.nm]
    (InternalCategoryPathDiagram.edgeInclusion graph) world function

/-- Every actual clone substitution preserves the complete included path. -/
theorem eventInclusion_substitution {world future : Base}
    (change : world ⟶ future) (function : (names.functorHom edges).obj world) :
    category.edge.map change (eventInclusion.app world function) =
      eventInclusion.app future ((names.functorHom edges).map change function) :=
  map_readout eventInclusion change function

/-- The whole chosen composition reads the supplied two paths and their matching endpoints. -/
theorem compose_readout {parameter : Ambient}
    (first second : parameter ⟶ category.edge)
    (matching : first ≫ category.target = second ≫ category.source)
    (world : Base) (supplied : parameter.obj world) :
    (category.compose first second matching).app world supplied =
      InternalCategoryDiagram.Arrow.compose
        (first.app world supplied) (second.app world supplied)
        (congrArg (fun (map : parameter ⟶ extendedCategory.vertex) => map.app world supplied)
          (InternalCategoryVertexIso.matching extendedCategory vertexComparison
            first second matching)) := by
  have actual := InternalCategoryVertexIso.complete_compose_read
    extendedCategory vertexComparison first second matching
  exact (congrArg (fun (map : parameter ⟶ extendedCategory.edge) => map.app world supplied)
    actual).trans (InternalCategoryDiagram.composeWith_apply diagram first second _ world supplied)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.CategoricalOperationalContinuations
