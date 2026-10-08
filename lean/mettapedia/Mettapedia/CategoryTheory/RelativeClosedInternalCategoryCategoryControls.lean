import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryControls
import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryModelDiagrams
import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryNativeCategory

/-!
# Weighted category laws and an endpoint-preserving separator

Natural-number evidence composes by addition and retains both endpoints.
The three finite category diagrams are independently computed, yielding
associativity in every context. A composition that adds an extra unit has
the same correct endpoint diagrams but is rejected by the category unit law.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedInternalCategory.CategoryControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Controls

abbrev operations := ModelDiagrams.endpoints vertex base weighted weighted_endpoint_laws
abbrev triples := ModelDiagrams.triples vertex base weighted weighted_endpoint_laws

theorem compose_value {stage : Type} (first second : stage ⟶ Evidence)
    (matching : first ≫ graph.target = second ≫ graph.source) (value : stage) :
    InternalCategoryPresentedDiagrams.compose operations first second matching value =
      ((first value).1, (second value).2.1, (first value).2.2 + (second value).2.2) := by
  have firstRead := congrArg (fun arrow : stage ⟶ Evidence => arrow value)
    (PullbackCone.IsLimit.lift_fst operations.pairLimit first second matching)
  have secondRead := congrArg (fun arrow : stage ⟶ Evidence => arrow value)
    (PullbackCone.IsLimit.lift_snd operations.pairLimit first second matching)
  change graph.first (InternalCategoryPresentedDiagrams.pairLift operations first second matching value) = first value at firstRead
  change graph.second (InternalCategoryPresentedDiagrams.pairLift operations first second matching value) = second value at secondRead
  change ((graph.first (InternalCategoryPresentedDiagrams.pairLift operations first second matching value)).1,
      (graph.second (InternalCategoryPresentedDiagrams.pairLift operations first second matching value)).2.1,
      (graph.first (InternalCategoryPresentedDiagrams.pairLift operations first second matching value)).2.2 +
        (graph.second (InternalCategoryPresentedDiagrams.pairLift operations first second matching value)).2.2) = _
  rw [firstRead, secondRead]

theorem weighted_category_laws : ModelDiagrams.LocalLaws vertex base weighted weighted_endpoint_laws where
  leftUnit := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext evidence
    change InternalCategoryPresentedDiagrams.compose operations (operations.source ≫ operations.unit)
      (𝟙 Evidence) _ evidence = evidence
    rw [compose_value]
    rcases evidence with ⟨before, after, weight⟩
    change (before, after, 0 + weight) = (before, after, weight)
    rw [Nat.zero_add]
  rightUnit := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext evidence
    change InternalCategoryPresentedDiagrams.compose operations (𝟙 Evidence)
      (operations.target ≫ operations.unit) _ evidence = evidence
    rw [compose_value]
    rcases evidence with ⟨before, after, weight⟩
    change (before, after, weight + 0) = (before, after, weight)
    rw [Nat.add_zero]
  associativity := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext supplied
    change InternalCategoryPresentedDiagrams.associateLeft operations triples supplied =
      InternalCategoryPresentedDiagrams.associateRight operations triples supplied
    simp only [InternalCategoryPresentedDiagrams.associateLeft,
      InternalCategoryPresentedDiagrams.associateRight, compose_value]
    have innerRead := compose_value (InternalCategoryPresentedDiagrams.middle operations triples)
      triples.snd (InternalCategoryPresentedDiagrams.second_matching operations triples) supplied
    erw [innerRead]
    let first := graph.first (triples.fst supplied)
    let second := graph.second (triples.fst supplied)
    let last := triples.snd supplied
    change (first.1, last.2.1, (first.2.2 + second.2.2) + last.2.2) =
      (first.1, last.2.1, first.2.2 + (second.2.2 + last.2.2))
    rw [Nat.add_assoc]

def weightedCategory : InternalCategory Type :=
  ModelDiagrams.category vertex base weighted weighted_endpoint_laws weighted_category_laws

theorem category_retains_complete_composition {stage : Type} (first second : stage ⟶ Evidence)
    (matching : first ≫ graph.target = second ≫ graph.source) (value : stage) :
    weightedCategory.compose first second matching value =
      ((first value).1, (second value).2.1, (first value).2.2 + (second value).2.2) := by
  have read := InternalCategoryPresentedDiagrams.chosen_compose_read operations first second matching
  exact (congrArg (fun arrow : stage ⟶ Evidence => arrow value) read).trans
    (compose_value first second matching value)

def offset : Meaning.Operations (base.obj vertex) where
  toGraph := graph
  unit := weighted.unit
  composition := TypeCat.ofHom (fun pair =>
    ((graph.first pair).1, (graph.second pair).2.1,
      (graph.first pair).2.2 + (graph.second pair).2.2 + 1))

theorem offset_endpoint_laws : Meaning.EndpointLaws vertex base offset where
  unitSource := weighted_endpoint_laws.unitSource
  unitTarget := weighted_endpoint_laws.unitTarget
  compositionSource := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext pair
    rfl
  compositionTarget := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext pair
    rfl

abbrev offsetOperations := ModelDiagrams.endpoints vertex base offset offset_endpoint_laws

theorem offset_compose_value {stage : Type} (first second : stage ⟶ Evidence)
    (matching : first ≫ graph.target = second ≫ graph.source) (value : stage) :
    InternalCategoryPresentedDiagrams.compose offsetOperations first second matching value =
      ((first value).1, (second value).2.1, (first value).2.2 + (second value).2.2 + 1) := by
  have firstRead := congrArg (fun arrow : stage ⟶ Evidence => arrow value)
    (PullbackCone.IsLimit.lift_fst offsetOperations.pairLimit first second matching)
  have secondRead := congrArg (fun arrow : stage ⟶ Evidence => arrow value)
    (PullbackCone.IsLimit.lift_snd offsetOperations.pairLimit first second matching)
  change graph.first (InternalCategoryPresentedDiagrams.pairLift offsetOperations first second matching value) = first value at firstRead
  change graph.second (InternalCategoryPresentedDiagrams.pairLift offsetOperations first second matching value) = second value at secondRead
  change ((graph.first (InternalCategoryPresentedDiagrams.pairLift offsetOperations first second matching value)).1,
      (graph.second (InternalCategoryPresentedDiagrams.pairLift offsetOperations first second matching value)).2.1,
      (graph.first (InternalCategoryPresentedDiagrams.pairLift offsetOperations first second matching value)).2.2 +
        (graph.second (InternalCategoryPresentedDiagrams.pairLift offsetOperations first second matching value)).2.2 + 1) = _
  rw [firstRead, secondRead]

theorem offset_category_rejected : ¬ ModelDiagrams.LocalLaws vertex base offset offset_endpoint_laws := by
  intro laws
  have same := congrArg (fun arrow : Evidence ⟶ Evidence => arrow (false, true, 3)) laws.leftUnit
  have read := offset_compose_value (offsetOperations.source ≫ offsetOperations.unit) (𝟙 Evidence)
    (by
      change (offsetOperations.source ≫ offsetOperations.unit) ≫ offsetOperations.target =
        (𝟙 offsetOperations.edge) ≫ offsetOperations.source
      rw [Category.assoc, offsetOperations.unitTarget, Category.comp_id, Category.id_comp])
    (false, true, 3)
  have impossible : ((false, true, 4) : Evidence) = (false, true, 3) := read.symm.trans same
  have wrong := congrArg (fun evidence : Evidence => evidence.2.2) impossible
  exact (by decide : (4 : Nat) ≠ 3) wrong

end Mettapedia.CategoryTheory.RelativeClosedInternalCategory.CategoryControls
