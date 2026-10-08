import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryModelRealization
import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryCategoryControls

/-!
# Complete generated readings across a nonidentity program comparison

The source program presentation reverses the independently constructed
target's Boolean vertices. Actual generated arrows recover the transported
ports and units while retaining every weighted edge. Composition is read
through the independent matching-pair universal property at arbitrary stages.
Endpoint-only observations cannot recover distinct edge weights.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedInternalCategory.ModelControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory Interpretation Controls

def programComparison : base.obj vertex ≅ CategoryControls.weightedCategory.vertex where
  hom := TypeCat.ofHom (fun supplied => !supplied)
  inv := TypeCat.ofHom (fun supplied => !supplied)
  hom_inv_id := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext supplied
    cases supplied <;> rfl
  inv_hom_id := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext supplied
    cases supplied <;> rfl

abbrev generated := ModelRealization.functor vertex base CategoryControls.weightedCategory programComparison
abbrev operations := ModelRealization.operations vertex base CategoryControls.weightedCategory programComparison
abbrev endpointLaws := ModelRealization.endpointLaws vertex base CategoryControls.weightedCategory programComparison
abbrev endpoints := ModelDiagrams.endpoints vertex base operations endpointLaws

def sourceValue : ArrowValue Type :=
  ⟨generated.obj (ModelRealization.edgeObject vertex),
    generated.obj (ModelRealization.programObject vertex),
    generated.map (classOf (ModelRealization.sourceCode vertex))⟩

def targetValue : ArrowValue Type :=
  ⟨generated.obj (ModelRealization.edgeObject vertex),
    generated.obj (ModelRealization.programObject vertex),
    generated.map (classOf (ModelRealization.targetCode vertex))⟩

def unitValue : ArrowValue Type :=
  ⟨generated.obj (ModelRealization.programObject vertex),
    generated.obj (ModelRealization.edgeObject vertex),
    generated.map (classOf (ModelRealization.unitCode vertex))⟩

def compositionValue : ArrowValue Type :=
  ⟨generated.obj (ModelRealization.compositionSource vertex),
    generated.obj (ModelRealization.edgeObject vertex),
    generated.map (classOf (ModelRealization.compositionCode vertex))⟩

theorem complete_source_read : sourceValue =
    ⟨Evidence, Bool, TypeCat.ofHom (fun supplied => !supplied.1)⟩ :=
  ModelRealization.complete_generated_source vertex base CategoryControls.weightedCategory programComparison

theorem complete_target_read : targetValue =
    ⟨Evidence, Bool, TypeCat.ofHom (fun supplied => !supplied.2.1)⟩ :=
  ModelRealization.complete_generated_target vertex base CategoryControls.weightedCategory programComparison

theorem complete_unit_read : unitValue =
    ⟨Bool, Evidence, TypeCat.ofHom (fun supplied => (!supplied, !supplied, 0))⟩ :=
  ModelRealization.complete_generated_unit vertex base CategoryControls.weightedCategory programComparison

theorem complete_composition_read : compositionValue =
    ⟨operations.toGraph.composable, Evidence, operations.composition⟩ :=
  ModelRealization.complete_generated_composition vertex base CategoryControls.weightedCategory programComparison

theorem source_decoder_read : ArrowValue.readAt (some sourceValue) Evidence Bool =
    some (TypeCat.ofHom (fun supplied => !supplied.1)) := by
  rw [complete_source_read, ArrowValue.readAt_supplied]

theorem target_decoder_read : ArrowValue.readAt (some targetValue) Evidence Bool =
    some (TypeCat.ofHom (fun supplied => !supplied.2.1)) := by
  rw [complete_target_read, ArrowValue.readAt_supplied]

theorem unit_decoder_read : ArrowValue.readAt (some unitValue) Bool Evidence =
    some (TypeCat.ofHom (fun supplied => (!supplied, !supplied, 0))) := by
  rw [complete_unit_read, ArrowValue.readAt_supplied]

theorem composition_decoder_read :
    ArrowValue.readAt (some compositionValue) operations.toGraph.composable Evidence =
      some operations.composition := by
  rw [complete_composition_read, ArrowValue.readAt_supplied]

theorem complete_original_base : baseFunctor (Presentation.signature vertex) ⋙ generated = base :=
  ModelRealization.complete_base_restriction vertex base CategoryControls.weightedCategory programComparison

theorem complete_compose_value {stage : Type} (first second : stage ⟶ Evidence)
    (matching : first ≫ operations.target = second ≫ operations.source) (supplied : stage) :
    InternalCategoryPresentedDiagrams.compose endpoints first second matching supplied =
      ((first supplied).1, (second supplied).2.1,
        (first supplied).2.2 + (second supplied).2.2) := by
  have whole := ModelRealization.complete_compose_read vertex base CategoryControls.weightedCategory
    programComparison first second matching
  exact (congrArg (fun arrow : stage ⟶ Evidence => arrow supplied) whole).trans
    (CategoryControls.category_retains_complete_composition first second
      (InternalCategoryVertexIso.matching CategoryControls.weightedCategory programComparison
        first second matching) supplied)

def firstEdge : PUnit ⟶ Evidence := TypeCat.ofHom (fun _ => (false, true, 3))
def secondEdge : PUnit ⟶ Evidence := TypeCat.ofHom (fun _ => (true, false, 7))

theorem supplied_edges_match : firstEdge ≫ operations.target = secondEdge ≫ operations.source := by
  apply TypeCat.Hom.ext
  apply TypeCat.Fun.ext
  funext supplied
  rfl

theorem generated_composition_retains_both_weights :
    InternalCategoryPresentedDiagrams.compose endpoints firstEdge secondEdge supplied_edges_match PUnit.unit =
      ((false, false, 10) : Evidence) :=
  complete_compose_value firstEdge secondEdge supplied_edges_match PUnit.unit

theorem program_comparison_is_nonidentity :
    programComparison.hom ≠ (𝟙 (base.obj vertex) : base.obj vertex ⟶ Bool) := by
  intro same
  have impossible := congrArg (fun arrow : Bool ⟶ Bool => arrow false) same
  change true = false at impossible
  cases impossible

theorem generated_source_differs_from_original :
    ArrowValue.readAt (some sourceValue) Evidence Bool ≠ some graph.source := by
  intro same
  have supplied := Option.some.inj (source_decoder_read.symm.trans same)
  have impossible := congrArg (fun arrow : Evidence ⟶ Bool => arrow (false, true, 3)) supplied
  change true = false at impossible
  cases impossible

theorem transported_ports_retain_distinct_weights :
    operations.source (false, true, 3) = operations.source (false, true, 7) ∧
      operations.target (false, true, 3) = operations.target (false, true, 7) ∧
      ((false, true, 3) : Evidence) ≠ (false, true, 7) :=
  ⟨rfl, rfl, equal_endpoints_distinct_evidence.2.2⟩

theorem no_endpoint_weight_decoder :
    ¬ ∃ decoder : Bool × Bool → Nat, ∀ supplied : Evidence,
      decoder (operations.source supplied, operations.target supplied) = supplied.2.2 := by
  rintro ⟨decoder, reads⟩
  have before := reads (false, true, 3)
  have after := reads (false, true, 7)
  exact (by decide : (3 : Nat) ≠ 7) (before.symm.trans after)

end Mettapedia.CategoryTheory.RelativeClosedInternalCategory.ModelControls
