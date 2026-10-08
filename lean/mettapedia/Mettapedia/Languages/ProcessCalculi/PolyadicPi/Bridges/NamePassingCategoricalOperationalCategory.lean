import Mettapedia.Languages.ProcessCalculi.PolyadicPi.CategoricalOperationalContinuations
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalOperationalBeta

/-!
# Complete continuation receipts in the actual retained-path category

Fetch and beta evidence is included into the actual continuation category.
Its source and target are the independently formed whole compiler arrows.
The function presentation recovers every supplied event at every future
context and return argument. Substitution acts on the full retained path.
The elementary-event object remains separate from the category of paths.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalOperationalCategory

open _root_.CategoryTheory _root_.CategoryTheory.CartesianMonoidalCategory
open Mettapedia.CategoryTheory
open Mettapedia.OSLF.Binding
open IntrinsicScopedOperationalPresheafContextHom
open NamePassingCategoricalCompiler
open NamePassingCategoricalOperational


/-- Include an independently supplied complete elementary receipt into paths. -/
def includeReceipt {parameter : Ambient}
    (receipt : parameter ⟶ operations.names.functorHom events) :
    parameter ⟶ CategoricalOperationalContinuations.category.edge :=
  receipt ≫ CategoricalOperationalContinuations.eventInclusion

@[reassoc] theorem includeReceipt_source {parameter : Ambient}
    (receipt : parameter ⟶ operations.names.functorHom events) :
    includeReceipt receipt ≫ CategoricalOperationalContinuations.category.source =
      receipt ≫ (FunctorToTypes.rightAdj operations.names).map source := by
  rw [includeReceipt, Category.assoc, CategoricalOperationalContinuations.eventInclusion_source]

@[reassoc] theorem includeReceipt_target {parameter : Ambient}
    (receipt : parameter ⟶ operations.names.functorHom events) :
    includeReceipt receipt ≫ CategoricalOperationalContinuations.category.target =
      receipt ≫ (FunctorToTypes.rightAdj operations.names).map target := by
  rw [includeReceipt, Category.assoc, CategoricalOperationalContinuations.eventInclusion_target]

@[reassoc] theorem includeReceipt_complete {parameter : Ambient}
    (receipt : parameter ⟶ operations.names.functorHom events) :
    includeReceipt receipt ≫ CategoricalOperationalContinuations.edgeComparison.inv =
      receipt ≫ (FunctorToTypes.rightAdj operations.names).map
        (InternalCategoryPathDiagram.edgeInclusion CategoricalOperational.graph) := by
  simp only [includeReceipt, CategoricalOperationalContinuations.eventInclusion, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- Decoding the supplied path at any future reads that exact elementary event. -/
theorem includeReceipt_future {parameter : Ambient}
    (receipt : parameter ⟶ operations.names.functorHom events)
    (world future : Base) (change : world ⟶ future)
    (supplied : parameter.obj world) (result : operations.names.obj future) :
    ((CategoricalOperationalContinuations.edgeComparison.inv.app world
      ((includeReceipt receipt).app world supplied)).app future change result) =
      InternalCategoryPathDiagram.edge CategoricalOperational.graph future
        ((receipt.app world supplied).app future change result) :=
  congrArg (fun (map : parameter ⟶ operations.names.functorHom CategoricalOperationalContinuations.pathEdges) =>
    (map.app world supplied).app future change result) (includeReceipt_complete receipt)

/-- The actual return-indexed fetch receipt, with its retained unary COMM tree. -/
def fetchPath : fetchDomain ⟶ CategoricalOperationalContinuations.category.edge := includeReceipt fetch

/-- The actual return-indexed beta receipt, with its private scope and binary COMM tree. -/
def betaPath : betaDomain ⟶ CategoricalOperationalContinuations.category.edge := includeReceipt beta

@[reassoc] theorem fetchPath_source : fetchPath ≫ CategoricalOperationalContinuations.category.source = fetchSource := by
  exact (includeReceipt_source fetch).trans fetch_source

@[reassoc] theorem fetchPath_target : fetchPath ≫ CategoricalOperationalContinuations.category.target = snd _ _ := by
  exact (includeReceipt_target fetch).trans fetch_target

@[reassoc] theorem betaPath_source : betaPath ≫ CategoricalOperationalContinuations.category.source = betaSource := by
  exact (includeReceipt_source beta).trans beta_source

@[reassoc] theorem betaPath_target : betaPath ≫ CategoricalOperationalContinuations.category.target = betaTarget := by
  exact (includeReceipt_target beta).trans beta_target

theorem fetchPath_substitution {world future : Base} (change : world ⟶ future)
    (supplied : fetchDomain.obj world) :
    CategoricalOperationalContinuations.category.edge.map change (fetchPath.app world supplied) =
      fetchPath.app future (fetchDomain.map change supplied) :=
  receipt_substitution fetchPath change supplied

theorem betaPath_substitution {world future : Base} (change : world ⟶ future)
    (supplied : betaDomain.obj world) :
    CategoricalOperationalContinuations.category.edge.map change (betaPath.app world supplied) =
      betaPath.app future (betaDomain.map change supplied) :=
  receipt_substitution betaPath change supplied

theorem fetchPath_future (world future : Base) (change : world ⟶ future)
    (supplied : fetchDomain.obj world) (result : operations.names.obj future) :
    ((CategoricalOperationalContinuations.edgeComparison.inv.app world (fetchPath.app world supplied)).app future change result) =
      InternalCategoryPathDiagram.edge CategoricalOperational.graph future
        ((fetch.app world supplied).app future change result) :=
  includeReceipt_future fetch world future change supplied result

theorem betaPath_future (world future : Base) (change : world ⟶ future)
    (supplied : betaDomain.obj world) (result : operations.names.obj future) :
    ((CategoricalOperationalContinuations.edgeComparison.inv.app world (betaPath.app world supplied)).app future change result) =
      InternalCategoryPathDiagram.edge CategoricalOperational.graph future
        ((beta.app world supplied).app future change result) :=
  includeReceipt_future beta world future change supplied result

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalOperationalCategory
