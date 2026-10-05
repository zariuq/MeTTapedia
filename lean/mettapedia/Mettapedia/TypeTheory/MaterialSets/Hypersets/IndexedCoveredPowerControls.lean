import Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedCoveredPowerBaseChange
import Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerFunctorControls

/-!
# Infinite future controls for the parameter-supported power

At each stage n the source admits n+1 positions and two tags. Infinitely
many supported predicates lie over the initial zero position and have the
same empty present part. Base change retains the transported parameter tag
as well as the original argument and the actual future arrow.

A predicate with an empty present part can admit an incorrectly indexed
argument later. It satisfies every present support test but cannot form an
indexed power element. Thus the whole-future support law is necessary.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedCoveredPowerControls

open CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open IndexedCoveredPowerBaseChange PowerClassPresheafDescent.Controls
open Mettapedia.TypeTheory.ContextualWitnessCover
open Mettapedia.TypeTheory.ContextualImageFactorization (pullback)

def forgetTag : NaturalHom growingSource growingTarget := NaturalHom.ofNatTrans growingObservation

def zeroParameter : growingTarget.obj (world 0) := ⟨0, Nat.zero_lt_one⟩

def zeroThreshold (bound : Nat) : FuturePowerFamilies.Predicate growingSource (world 0) where
  holds argument := argument.2.1.val = 0 ∧ bound ≤ stageIndex argument.1.1
  closed {first second} move admitted := by
    have position := congrArg (fun value : growingSource.obj second.1.1 => value.1.val) move.2
    change first.2.1.val = second.2.1.val at position
    exact ⟨position.symm.trans admitted.1, admitted.2.trans (growthLe move.1.1)⟩

def zeroPower (bound : Nat) : Power growingSource (world 0) := ofFull (zeroThreshold bound)

theorem zero_support (bound : Nat) :
    IndexedCoveredPower.Supports forgetTag (world 0) zeroParameter (zeroPower bound) := by
  intro argument admitted
  apply Fin.ext
  exact admitted.1

def original (bound : Nat) : (IndexedCoveredPower.family forgetTag).obj (world 0) :=
  ⟨(zeroParameter, zeroPower bound), zero_support bound⟩

def input (bound : Nat) (tag : Bool) : (baseFamily forgetTag forgetTag).obj (world 0) :=
  ⟨(original bound, stageValue 0 0 (by omega) tag), rfl⟩

def pulled (bound : Nat) (tag : Bool) : (indexedFamily forgetTag forgetTag).obj (world 0) :=
  (backward forgetTag forgetTag).app (world 0) (input bound tag)

def futurePair (level : Nat) (argumentTag parameterTag : Bool) :
    (argumentFamily forgetTag forgetTag).obj (world level) :=
  ⟨(stageValue level 0 (Nat.zero_lt_succ level) argumentTag,
    stageValue level 0 (Nat.zero_lt_succ level) parameterTag), rfl⟩

def futureArgument (level : Nat) (argumentTag parameterTag : Bool) :
    Arguments (argumentFamily forgetTag forgetTag) (world 0) :=
  ⟨⟨world level, (homOfLE (Nat.zero_le level)).op.op⟩,
    futurePair level argumentTag parameterTag⟩

theorem pulled_truth (bound level : Nat) (savedTag argumentTag parameterTag : Bool) :
    (pulled bound savedTag).val.2.val.holds (futureArgument level argumentTag parameterTag) ↔
      bound ≤ level ∧ parameterTag = savedTag := by
  constructor
  · rintro ⟨admitted, parameterEq⟩
    exact ⟨admitted.2, congrArg Prod.snd parameterEq⟩
  · rintro ⟨available, sameTag⟩
    refine ⟨⟨rfl, available⟩, ?_⟩
    exact Prod.ext (Fin.ext rfl) sameTag

theorem pulled_has_original_small_cover (bound : Nat) (tag : Bool) :
    Nonempty (Enumeration (pulled bound tag).val.2.val) := (pulled bound tag).val.2.property

theorem base_change_keeps_argument_tags (level : Nat) :
    (pulled 0 false).val.2.val.holds (futureArgument level true false) ∧
      (pulled 0 false).val.2.val.holds (futureArgument level false false) :=
  ⟨(pulled_truth 0 level false true false).mpr ⟨Nat.zero_le level, rfl⟩,
    (pulled_truth 0 level false false false).mpr ⟨Nat.zero_le level, rfl⟩⟩

theorem base_change_keeps_parameter_tag :
    (pulled 0 true).val.2.val ≠ (pulled 0 false).val.2.val := by
  intro same
  have truth := congrArg
    (fun predicate : Predicate (argumentFamily forgetTag forgetTag) (world 0) =>
      predicate.holds (futureArgument 0 false true)) same
  have admitted := Eq.mp truth ((pulled_truth 0 0 true false true).mpr ⟨Nat.le_refl 0, rfl⟩)
  have impossible := ((pulled_truth 0 0 false false true).mp admitted).2
  cases impossible

theorem indexed_thresholds_injective : Function.Injective (fun bound => pulled bound false) := by
  intro first second same
  have firstAtSecond := congrArg
    (fun entry : (indexedFamily forgetTag forgetTag).obj (world 0) =>
      entry.val.2.val.holds (futureArgument second false false)) same
  have firstBelow := ((pulled_truth first second false false false).mp
    (Eq.mpr firstAtSecond ((pulled_truth second second false false false).mpr ⟨Nat.le_refl second, rfl⟩))).1
  have secondAtFirst := congrArg
    (fun entry : (indexedFamily forgetTag forgetTag).obj (world 0) =>
      entry.val.2.val.holds (futureArgument first false false)) same
  have secondBelow := ((pulled_truth second first false false false).mp
    (Eq.mp secondAtFirst ((pulled_truth first first false false false).mpr ⟨Nat.le_refl first, rfl⟩))).1
  exact Nat.le_antisymm firstBelow secondBelow

theorem later_indexed_thresholds_empty_present
    (argument : (argumentFamily forgetTag forgetTag).obj (world 0)) :
    ¬ (pulled 1 false).val.2.val.holds (current (argumentFamily forgetTag forgetTag) (world 0) argument) ∧
      ¬ (pulled 2 false).val.2.val.holds (current (argumentFamily forgetTag forgetTag) (world 0) argument) := by
  constructor
  · rintro ⟨admitted, _⟩
    exact Nat.not_succ_le_zero 0 admitted.2
  · rintro ⟨admitted, _⟩
    exact Nat.not_succ_le_zero 1 admitted.2

theorem exact_base_change_roundtrip (bound : Nat) (tag : Bool) :
    (forward forgetTag forgetTag).app (world 0) (pulled bound tag) = input bound tag :=
  forward_backward forgetTag forgetTag (world 0) (input bound tag)

def badPower : Power growingSource (world 0) := ofFull (FuturePowerFunctorControls.threshold 1)

theorem badPower_passes_every_present_support_test (argument : growingSource.obj (world 0)) :
    badPower.val.holds (current growingSource (world 0) argument) →
      forgetTag.app (world 0) argument = zeroParameter := by
  intro impossible
  exact (Nat.not_succ_le_zero 0 impossible).elim

def incorrectlyIndexedFuture : Arguments growingSource (world 0) :=
  ⟨⟨world 1, (homOfLE (show 0 ≤ 1 from Nat.zero_le 1)).op.op⟩,
    stageValue 1 1 (by omega) false⟩

theorem badPower_fails_future_support :
    ¬ IndexedCoveredPower.Supports forgetTag (world 0) zeroParameter badPower := by
  intro supported
  have impossible := congrArg Fin.val (supported incorrectlyIndexedFuture (Nat.le_refl 1))
  change (1 : Nat) = 0 at impossible
  cases impossible

end Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedCoveredPowerControls
