import Mettapedia.CategoryTheory.MonoArrowPredicateEquivalence
import Mettapedia.CategoryTheory.TypeSubobjectClassifier
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Monoidal.Closed.Types

/-!
# Complete dependent witnesses in the elementary predicate doctrine

A proper predicate on a dependent family of finite values is classified
by actual generic truth. A guarded map changes the family index and retains
the supplied finite coordinate. The based total equivalence reconstructs
that complete map. The identity map cannot enter the same proper display,
because its zero coordinate violates the guard.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryToposPredicateControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open ElementaryToposPredicateDoctrine MonoArrowPredicateEquivalence

def model := doctrine TypeSubobjectClassifier.classifier

abbrev Values := Σ n : Nat, Fin (n + 2)

abbrev Satisfying := {value : Values // 0 < value.2.val}

def inclusion : Satisfying ⟶ Values := TypeCat.ofHom Subtype.val

instance inclusion_mono : Mono inclusion :=
  (mono_iff_injective inclusion).mpr Subtype.val_injective

def proper : Subobject Values := Subobject.mk inclusion

def properDisplay : MonoArrowImageAdjunction.Predicate (Type) :=
  ⟨Arrow.mk inclusion, by change Mono inclusion; infer_instance⟩

def unrestrictedDisplay : MonoArrowImageAdjunction.Predicate (Type) :=
  MonoArrowImageAdjunction.truth Values

def advance : Values ⟶ Values := TypeCat.ofHom fun value =>
  ⟨value.1 + 1, ⟨value.2.val + 1, by have := value.2.isLt; omega⟩⟩

def guarded : unrestrictedDisplay ⟶ properDisplay :=
  ObjectProperty.homMk (Arrow.homMk
    (TypeCat.ofHom fun value => ⟨advance value, Nat.zero_lt_succ _⟩) advance (by rfl))

theorem characteristic_readout :
    model.generic.characteristic Values proper = TypeSubobjectClassifier.characteristic inclusion := by
  change ElementaryToposPredicateHeyting.characteristic TypeSubobjectClassifier.classifier
      (Subobject.mk inclusion) = TypeSubobjectClassifier.classifier.χ inclusion
  exact (ElementaryToposPredicateHeyting.characteristic_unique
    TypeSubobjectClassifier.classifier (Subobject.mk inclusion)
    (TypeSubobjectClassifier.classifier.χ inclusion)
    (TypeSubobjectClassifier.classifier.pullback_χ_obj_mk_truth inclusion)).symm

theorem generic_truth_retains_guard (value : Values) :
    model.generic.characteristic Values proper value = true ↔ 0 < value.2.val := by
  rw [characteristic_readout]
  change TypeSubobjectClassifier.characteristic inclusion value = true ↔ 0 < value.2.val
  constructor
  · intro held
    obtain ⟨supplied, same⟩ :=
      (TypeSubobjectClassifier.characteristic_true_iff inclusion value).mp held
    exact same ▸ supplied.property
  · intro held
    exact (TypeSubobjectClassifier.characteristic_true_iff inclusion value).mpr
      ⟨⟨value, held⟩, rfl⟩

def supplied : Values := ⟨4, ⟨1, by omega⟩⟩

def zeroCoordinate : Values := ⟨4, ⟨0, by omega⟩⟩

theorem supplied_guard : model.generic.characteristic Values proper supplied = true :=
  (generic_truth_retains_guard supplied).mpr (by change (0 : Nat) < 1; omega)

theorem zero_guard_rejected : model.generic.characteristic Values proper zeroCoordinate ≠ true := by
  intro held
  exact Nat.lt_irrefl 0 ((generic_truth_retains_guard zeroCoordinate).mp held)

def sourceObject := representingObject TypeSubobjectClassifier.classifier unrestrictedDisplay

def targetObject := representingObject TypeSubobjectClassifier.classifier properDisplay

def representedSquare : (toMonos TypeSubobjectClassifier.classifier).obj sourceObject ⟶
    (toMonos TypeSubobjectClassifier.classifier).obj targetObject :=
  (representingIso TypeSubobjectClassifier.classifier unrestrictedDisplay).hom ≫
    guarded ≫ (representingIso TypeSubobjectClassifier.classifier properDisplay).inv

def totalMap : sourceObject ⟶ targetObject :=
  fromSquare TypeSubobjectClassifier.classifier representedSquare

theorem total_map_complete_base : totalMap.base = advance := by
  change 𝟙 Values ≫ advance ≫ 𝟙 Values = advance
  rw [Category.id_comp, Category.comp_id]

theorem total_map_index_readout : (totalMap.base supplied).1 = (5 : Nat) := by
  rw [total_map_complete_base]
  rfl

theorem total_map_finite_readout : (totalMap.base supplied).2.val = (2 : Nat) := by
  rw [total_map_complete_base]
  rfl

theorem omitted_map_changes_witness : (totalMap.base supplied).2.val ≠ supplied.2.val := by
  rw [total_map_finite_readout]
  change (2 : Nat) ≠ 1
  omega

theorem original_identity_has_no_guarded_square :
    ¬ ∃ arrow : unrestrictedDisplay ⟶ properDisplay, arrow.hom.right = 𝟙 Values := by
  rintro ⟨arrow, same⟩
  have recovers := congrArg (fun map : Values ⟶ Values => map zeroCoordinate) (Arrow.w arrow.hom)
  change inclusion (arrow.hom.left zeroCoordinate) = arrow.hom.right zeroCoordinate at recovers
  rw [same] at recovers
  have held := (arrow.hom.left zeroCoordinate).property
  have coordinate := congrArg (fun value : Values => value.2.val) recovers
  change (arrow.hom.left zeroCoordinate).val.2.val = 0 at coordinate
  rw [coordinate] at held
  exact Nat.lt_irrefl 0 held

def index : Values ⟶ Nat := TypeCat.ofHom Sigma.fst

def positiveChoice : Nat ⟶ Satisfying := TypeCat.ofHom fun n =>
  ⟨⟨n, ⟨1, by omega⟩⟩, by change (0 : Nat) < 1; omega⟩

def positiveInput : Nat ⟶ Values := positiveChoice ≫ inclusion

theorem positive_input_index : positiveInput ≫ index = 𝟙 Nat := rfl

theorem positive_input_guard_top : model.reindex positiveInput proper = ⊤ := by
  let square := Subobject.isPullback positiveInput proper
  let supplied := positiveChoice ≫ (Subobject.underlyingIso inclusion).inv
  have recovers : supplied ≫ proper.arrow = positiveInput := by
    change (positiveChoice ≫ (Subobject.underlyingIso inclusion).inv) ≫
      (Subobject.mk inclusion).arrow = positiveChoice ≫ inclusion
    rw [Category.assoc, Subobject.underlyingIso_arrow]
  let complete := square.lift supplied (𝟙 Nat)
    (recovers.trans (Category.id_comp _).symm)
  have admitted : (⊤ : Subobject Nat) ≤ (Subobject.pullback positiveInput).obj proper :=
    Subobject.mk_le_of_comm complete
      (square.lift_snd supplied (𝟙 Nat) (recovers.trans (Category.id_comp _).symm))
  exact eq_top_iff.mpr admitted

/-- Every index has its independently supplied positive finite witness. -/
theorem exists_positive_at_every_index : model.existsAlong index proper = ⊤ := by
  apply eq_top_iff.mpr
  have admitted := model.reindex_mono positiveInput
    ((model.exists_adj index).le_u_l proper)
  rw [positive_input_guard_top, ← model.reindex_comp, positive_input_index,
    model.reindex_id] at admitted
  exact admitted

/-- Universal truth would admit the rejected zero coordinate. -/
theorem universal_positivity_is_not_top : model.forallAlong index proper ≠ ⊤ := by
  intro same
  have admitted : (⊤ : Subobject Values) ≤ proper := by
    have all : (⊤ : Subobject Nat) ≤ model.forallAlong index proper := by rw [same]
    have held := (model.forall_adj index ⊤ proper).mpr all
    rw [model.reindex_top] at held
    exact held
  let complete : sourceObject ⟶ targetObject :=
    (model.toIndexedHeyting.totalHomEquiv sourceObject targetObject).symm
      ⟨𝟙 Values, by
        change Subobject.mk (𝟙 Values) ≤
          ElementaryToposPredicateAdjoints.reindex (𝟙 Values) proper
        rw [ElementaryToposPredicateAdjoints.reindex_id]
        exact admitted⟩
  let recovered : unrestrictedDisplay ⟶ properDisplay :=
    (representingIso TypeSubobjectClassifier.classifier unrestrictedDisplay).inv ≫
      (toMonos TypeSubobjectClassifier.classifier).map complete ≫
      (representingIso TypeSubobjectClassifier.classifier properDisplay).hom
  apply original_identity_has_no_guarded_square
  refine ⟨recovered, ?_⟩
  change (𝟙 Values ≫ 𝟙 Values ≫ 𝟙 Values) = 𝟙 Values
  simp only [Category.id_comp]

theorem actual_based_total_equivalence :
    (equivalence TypeSubobjectClassifier.classifier).functor ⋙
        MonoArrowImageAdjunction.projection (Type) = model.toIndexedHeyting.projection :=
  over_base TypeSubobjectClassifier.classifier

end Mettapedia.CategoryTheory.ElementaryToposPredicateControls
