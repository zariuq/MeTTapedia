import Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerPullback

/-!
# Images on an infinite growing argument family

Forgetting an authored tag merges distinct stable future predicates, while
inverse image of that image admits the erased tag. Actual pullback receipts
retain both tags and satisfy the full-future image comparison. Infinitely
many distinct future predicates are already present over the initial small
argument carrier; present truth alone does not recover them.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerFunctorControls

open CategoryTheory FuturePowerFamilies FuturePowerFunctor FuturePowerPullback
open PowerClassPresheafDescent.Controls
open Mettapedia.TypeTheory.ContextualWitnessCover

def forgetTag : NaturalHom growingSource growingTarget := NaturalHom.ofNatTrans growingObservation

theorem forgetTag_surjective (point : Stagesᵒᵖ) : Function.Surjective (forgetTag.app point) :=
  fun value => ⟨(value, false), rfl⟩

def tagged (point : Stagesᵒᵖ) (tag : Bool) : Predicate growingSource point where
  holds argument := argument.2.2 = tag
  closed {first second} step available := by
    have same := congrArg Prod.snd step.2
    change first.2.2 = second.2.2 at same
    exact same.symm.trans available

def full (point : Stagesᵒᵖ) : Predicate growingTarget point where
  holds _ := True
  closed _ _ := trivial

theorem tagged_image_full (point : Stagesᵒᵖ) (tag : Bool) :
    image forgetTag point (tagged point tag) = full point := by
  apply Predicate.ext
  intro argument
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨(argument.2, tag), rfl, rfl⟩

theorem tags_distinct (point : Stagesᵒᵖ) (value : growingSource.obj point)
    (trueTag : value.2 = true) : tagged point true ≠ tagged point false := by
  intro same
  have truths := congrArg (fun predicate : Predicate growingSource point =>
    predicate.holds (current growingSource point value)) same
  have falseTag : value.2 = false := Eq.mp truths trueTag
  cases trueTag.symm.trans falseTag

theorem distinct_predicates_same_image :
    tagged (world 0) true ≠ tagged (world 0) false ∧
      image forgetTag (world 0) (tagged (world 0) true) =
        image forgetTag (world 0) (tagged (world 0) false) :=
  ⟨tags_distinct (world 0) (stageValue 0 0 (by omega) true) rfl,
    (tagged_image_full (world 0) true).trans (tagged_image_full (world 0) false).symm⟩

def erasedArgument := current growingSource (world 0) (stageValue 0 0 (by omega) false)

theorem erased_tag_admitted_by_inverse_image :
    (inverseImage forgetTag (world 0) (image forgetTag (world 0) (tagged (world 0) true))).holds
        erasedArgument ∧ ¬ (tagged (world 0) true).holds erasedArgument := by
  constructor
  · exact ⟨stageValue 0 0 (by omega) true, rfl, rfl⟩
  · intro impossible
    change false = true at impossible
    cases impossible

def parallelReceipt : (pullback forgetTag forgetTag).obj (world 0) :=
  ⟨(stageValue 0 0 (by omega) true, stageValue 0 0 (by omega) false), rfl⟩

theorem receipt_preserves_both_tags :
    ((firstProjection forgetTag forgetTag).app (world 0) parallelReceipt).2 = true ∧
      ((secondProjection forgetTag forgetTag).app (world 0) parallelReceipt).2 = false := ⟨rfl, rfl⟩

theorem actual_pullback_comparison (point : Stagesᵒᵖ) (tag : Bool) :
    inverseImage forgetTag point (image forgetTag point (tagged point tag)) =
      image (secondProjection forgetTag forgetTag) point
        (inverseImage (firstProjection forgetTag forgetTag) point (tagged point tag)) :=
  image_inverseImage_beckChevalley forgetTag forgetTag point (tagged point tag)

def threshold (bound : Nat) : Predicate growingSource (world 0) where
  holds argument := bound ≤ stageIndex argument.1.1
  closed step available := available.trans (growthLe step.1.1)

def futureArgument (level : Nat) : Arguments growingSource (world 0) :=
  ⟨⟨world level, (homOfLE (show 0 ≤ level from Nat.zero_le level)).op.op⟩,
    stageValue level 0 (Nat.zero_lt_succ level) false⟩

theorem threshold_truth (bound level : Nat) :
    (threshold bound).holds (futureArgument level) ↔ bound ≤ level := Iff.rfl

/-- The power operation adds infinitely many actual future distinctions to
the initial carrier, whose present arguments only have the two source tags. -/
theorem threshold_injective : Function.Injective threshold := by
  intro first second same
  have firstAtSecond := congrArg (fun predicate : Predicate growingSource (world 0) =>
    predicate.holds (futureArgument second)) same
  have firstBelow : first ≤ second := Eq.mpr firstAtSecond (Nat.le_refl second)
  have secondAtFirst := congrArg (fun predicate : Predicate growingSource (world 0) =>
    predicate.holds (futureArgument first)) same
  have secondBelow : second ≤ first := Eq.mp secondAtFirst (Nat.le_refl first)
  exact Nat.le_antisymm firstBelow secondBelow

theorem later_thresholds_same_empty_present (value : growingSource.obj (world 0)) :
    ¬ (threshold 1).holds (current growingSource (world 0) value) ∧
      ¬ (threshold 2).holds (current growingSource (world 0) value) := by
  change ¬ 1 ≤ 0 ∧ ¬ 2 ≤ 0
  exact ⟨Nat.not_succ_le_zero 0, Nat.not_succ_le_zero 1⟩

theorem later_thresholds_distinct : threshold 1 ≠ threshold 2 :=
  fun same => (by decide : 1 ≠ (2 : Nat)) (threshold_injective same)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerFunctorControls
