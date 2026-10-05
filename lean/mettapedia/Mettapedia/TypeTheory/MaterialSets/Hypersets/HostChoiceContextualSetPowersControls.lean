import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetPowers
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetInterpretationControls

/-!
# Duplicate and infinite-future controls for internal powersets

Duplicated child receipts cannot encode different subset truth, because an
identity future move relates their equal values. On the infinite advancing
site, infinitely many subsets of a singleton have the same empty present
child subset and different future thresholds. They are distinct actual
members of its internal powerset at the original receipt bound.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetPowersControls

open _root_.CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open HostChoiceContextualSetInterpretation HostChoiceContextualSetInterpretation.Finality
open HostChoiceContextualSetPowers
open HostChoiceContextualSetInterpretationControls.Infinite
open PowerClassPresheafDescent.Controls
open Mettapedia.TypeTheory.ContextualWitnessCover

universe u
variable {D : Type u} [Category.{u} D]

def duplicateEnumeration (point : D) (value : sets.obj point) : Enumeration (singleton sets point value) where
  Carrier _ := ULift.{u} Bool
  value future _ := sets.map future.2 value
  covered _ _ := ⟨fun same => ⟨ULift.up false, same⟩, fun ⟨_, same⟩ => same⟩

theorem duplicate_truth_agrees (point : D) (value : sets.obj point)
    (code : BoundedCode (duplicateEnumeration point value)) (future : PowerClassPresheafBaseChange.Future.Objects point) :
    code.holds ⟨future, ULift.up false⟩ ↔ code.holds ⟨future, ULift.up true⟩ :=
  code.saturated future _ _ rfl

theorem no_receipt_tag_subset (point : D) (value : sets.obj point) :
    ¬ ∃ code : BoundedCode (duplicateEnumeration point value),
      code.holds ⟨⟨point, 𝟙 point⟩, ULift.up false⟩ ∧
        ¬ code.holds ⟨⟨point, 𝟙 point⟩, ULift.up true⟩ := by
  rintro ⟨code, first, absent⟩
  exact absent ((duplicate_truth_agrees point value code _).mp first)

def wholeCode (point : D) (value : sets.obj point) : BoundedCode (duplicateEnumeration point value) where
  holds _ := True
  closed _ _ _ _ available := available

theorem wholeCode_future {point target : D} (arrow : point ⟶ target)
    (value : sets.obj point) (child : sets.obj target) :
    FutureMember arrow child (wholeCode point value).value ↔ sets.map arrow value = child := by
  refine ((wholeCode point value).value_reading ⟨target, arrow⟩ child).trans ?_
  constructor
  · rintro ⟨_, same, _⟩
    exact same
  · intro same
    exact ⟨ULift.up false, same, trivial⟩

theorem wholeCode_is_singleton (point : D) (value : sets.obj point) :
    (wholeCode point value).value = singletonSet.app point value := by
  apply (internal_extensionality point _ _).mp
  intro target arrow child
  exact (futureMember_iff arrow child _).symm.trans
    ((wholeCode_future arrow value child).trans
      ((future_singleton arrow child value).symm.trans (futureMember_iff arrow child _)))

theorem wholeCode_restricts {point target : D} (arrow : point ⟶ target) (value : sets.obj point) :
    ((wholeCode point value).reindex arrow).value = singletonSet.app target (sets.map arrow value) :=
  ((wholeCode point value).value_reindex arrow).trans
    ((congrArg (sets.map arrow) (wholeCode_is_singleton point value)).trans
      (singletonSet.naturality arrow value))

namespace Infinite

def thresholdPredicate (threshold : ℕ) (point : Stagesᵒᵖ) : Predicate values point where
  holds argument := threshold+1 ≤ stageIndex argument.1.1 ∧ argument.2 = emptySet.val argument.1.1
  closed {first second} move available := by
    have same : values.map move.1.1 first.2 = second.2 := move.2
    exact ⟨available.1.trans (growthLe move.1.1), same.symm.trans
      ((congrArg (values.map move.1.1) available.2).trans (emptySet.property move.1.1))⟩

noncomputable def thresholdEnumeration (threshold : ℕ) (point : Stagesᵒᵖ) :
    Enumeration (thresholdPredicate threshold point) where
  Carrier future := {_receipt : PUnit.{1} // threshold+1 ≤ stageIndex future.1}
  value future _ := emptySet.val future.1
  covered _ _ := ⟨fun ⟨later, same⟩ => ⟨⟨PUnit.unit, later⟩, same.symm⟩,
    fun ⟨receipt, same⟩ => ⟨receipt.property, same.symm⟩⟩

noncomputable def thresholdPower (threshold : ℕ) (point : Stagesᵒᵖ) : Power values point :=
  ⟨thresholdPredicate threshold point, ⟨thresholdEnumeration threshold point⟩⟩

theorem threshold_restrict (threshold : ℕ) {first second : Stagesᵒᵖ} (arrow : first ⟶ second) :
    restrictPower values arrow (thresholdPower threshold first) = thresholdPower threshold second := by
  apply Subtype.ext
  apply Predicate.ext
  intro _
  exact Iff.rfl

noncomputable def thresholdSet (threshold : ℕ) : values.sections :=
  assemble.mapSection ⟨thresholdPower threshold, fun arrow => threshold_restrict threshold arrow⟩

theorem threshold_future (threshold : ℕ) (point target : Stagesᵒᵖ)
    (arrow : point ⟶ target) (child : values.obj target) :
    FutureMember arrow child ((thresholdSet threshold).val point) ↔
      threshold+1 ≤ stageIndex target ∧ child = emptySet.val target := by
  change (unfold.app point (assemble.app point (thresholdPower threshold point))).val.holds _ ↔ _
  rw [unfold_assemble]
  exact Iff.rfl

theorem threshold_present_empty (threshold : ℕ) (child : values.obj (world 0)) :
    ¬ Member (world 0) child ((thresholdSet threshold).val (world 0)) := by
  intro available
  have impossible := ((threshold_future threshold _ _ (𝟙 _) child).mp available).1
  exact Nat.not_succ_le_zero threshold impossible

def arrival (stage : ℕ) : world 0 ⟶ world stage := (homOfLE (Nat.zero_le stage)).op.op

theorem threshold_distinct : Function.Injective (fun threshold => (thresholdSet threshold).val (world 0)) := by
  intro first second same
  change (thresholdSet first).val (world 0) = (thresholdSet second).val (world 0) at same
  have one : FutureMember (arrival (first+1)) (emptySet.val (world (first+1)))
      ((thresholdSet first).val (world 0)) := (threshold_future first _ _ _ _).mpr ⟨Nat.le_refl _, rfl⟩
  have two : FutureMember (arrival (second+1)) (emptySet.val (world (second+1)))
      ((thresholdSet second).val (world 0)) := (threshold_future second _ _ _ _).mpr ⟨Nat.le_refl _, rfl⟩
  rw [same] at one
  rw [← same] at two
  have leOne := ((threshold_future second _ _ _ _).mp one).1
  have leTwo := ((threshold_future first _ _ _ _).mp two).1
  exact Nat.le_antisymm (Nat.le_of_succ_le_succ leTwo) (Nat.le_of_succ_le_succ leOne)

noncomputable def bound : values.sections := singletonSet.mapSection emptySet

theorem threshold_subset_bound (threshold : ℕ) (point : Stagesᵒᵖ) :
    Subset point ((thresholdSet threshold).val point) (bound.val point) := by
  rintro ⟨⟨target, arrow⟩, child⟩ available
  have childEq := ((threshold_future threshold point target arrow child).mp available).2
  exact (future_singleton arrow child (emptySet.val point)).mpr
    ((emptySet.property arrow).trans childEq.symm)

theorem infinitely_many_power_members (threshold : ℕ) :
    Member (world 0) ((thresholdSet threshold).val (world 0)) (powersetSet.app (world 0) (bound.val (world 0))) :=
  (member_powerset _ _ _).mpr (threshold_subset_bound threshold (world 0))

theorem power_members_with_identical_present_subsets :
    Function.Injective (fun threshold => (thresholdSet threshold).val (world 0)) ∧
      ∀ threshold, Member (world 0) ((thresholdSet threshold).val (world 0))
        (powersetSet.app (world 0) (bound.val (world 0))) ∧
        ∀ child, ¬ Member (world 0) child ((thresholdSet threshold).val (world 0)) :=
  ⟨threshold_distinct, fun threshold => ⟨infinitely_many_power_members threshold, threshold_present_empty threshold⟩⟩

theorem present_subset_does_not_enter_empty_power :
    (∀ child : values.obj (world 0), Member (world 0) child (lateSet.val (world 0)) →
      Member (world 0) child (emptySet.val (world 0))) ∧
      ¬ Member (world 0) (lateSet.val (world 0)) (powersetSet.app (world 0) (emptySet.val (world 0))) :=
  ⟨fun child belongs => (late_has_no_present_member child belongs).elim,
    fun belongs => late_ne_empty ((subset_empty_iff _ _).mp ((member_powerset _ _ _).mp belongs))⟩

end Infinite

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetPowersControls
