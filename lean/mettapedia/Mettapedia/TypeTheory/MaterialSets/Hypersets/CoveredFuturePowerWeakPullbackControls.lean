import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerWeakPullback
import Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerFunctorControls

/-!
# Correlation retained by matching, beyond the projected observations

The argument family has n+1 positions at stage n, each with an authored
Boolean tag. The diagonal and opposite-tag relations are stable over all
future contexts and have actual covers at the original small bound. Both
projections of both relations are the whole tagged argument family.

The power comparison is therefore not injective. Its canonical section
retains every compatible pair, while a consumer of the original correlation
can distinguish the two relations. No receipt is selected from an
existential cover to build any of these constructions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerWeakPullbackControls

open CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open CoveredFuturePowerWeakPullback PowerClassPresheafDescent.Controls
open Mettapedia.TypeTheory.ContextualWitnessCover
open Mettapedia.TypeTheory.ContextualImageFactorization
  (pullback pullbackFirst pullbackSecond)

def forgetTag : NaturalHom growingSource growingTarget :=
  NaturalHom.ofNatTrans growingObservation

def matchingArguments := pullback forgetTag forgetTag

def fullPredicate (point : Stagesᵒᵖ) : Predicate growingSource point where
  holds _ := True
  closed _ _ := trivial

def fullPower (point : Stagesᵒᵖ) : Power growingSource point :=
  ⟨fullPredicate point, ⟨smallEnumeration (fullPredicate point)⟩⟩

def diagonalPredicate (point : Stagesᵒᵖ) : Predicate matchingArguments point where
  holds argument := argument.2.val.1.2 = argument.2.val.2.2
  closed {first second} move available := by
    have leftTag := congrArg (fun pair : matchingArguments.obj second.1.1 => pair.val.1.2) move.2
    have rightTag := congrArg (fun pair : matchingArguments.obj second.1.1 => pair.val.2.2) move.2
    change first.2.val.1.2 = second.2.val.1.2 at leftTag
    change first.2.val.2.2 = second.2.val.2.2 at rightTag
    exact leftTag.symm.trans (available.trans rightTag)

def oppositePredicate (point : Stagesᵒᵖ) : Predicate matchingArguments point where
  holds argument := argument.2.val.1.2 ≠ argument.2.val.2.2
  closed {first second} move available := by
    have leftTag := congrArg (fun pair : matchingArguments.obj second.1.1 => pair.val.1.2) move.2
    have rightTag := congrArg (fun pair : matchingArguments.obj second.1.1 => pair.val.2.2) move.2
    change first.2.val.1.2 = second.2.val.1.2 at leftTag
    change first.2.val.2.2 = second.2.val.2.2 at rightTag
    exact fun same => available (leftTag.trans (same.trans rightTag.symm))

def diagonal (point : Stagesᵒᵖ) : Power matchingArguments point :=
  ⟨diagonalPredicate point, ⟨smallEnumeration (diagonalPredicate point)⟩⟩

def opposite (point : Stagesᵒᵖ) : Power matchingArguments point :=
  ⟨oppositePredicate point, ⟨smallEnumeration (oppositePredicate point)⟩⟩

theorem diagonal_first (point : Stagesᵒᵖ) :
    imagePower (pullbackFirst forgetTag forgetTag) point (diagonal point) = fullPower point := by
  apply Subtype.ext
  apply Predicate.ext
  intro argument
  exact ⟨fun _ => trivial, fun _ => ⟨⟨(argument.2, argument.2), rfl⟩, rfl, rfl⟩⟩

theorem diagonal_second (point : Stagesᵒᵖ) :
    imagePower (pullbackSecond forgetTag forgetTag) point (diagonal point) = fullPower point := by
  apply Subtype.ext
  apply Predicate.ext
  intro argument
  exact ⟨fun _ => trivial, fun _ => ⟨⟨(argument.2, argument.2), rfl⟩, rfl, rfl⟩⟩

theorem opposite_first (point : Stagesᵒᵖ) :
    imagePower (pullbackFirst forgetTag forgetTag) point (opposite point) = fullPower point := by
  apply Subtype.ext
  apply Predicate.ext
  intro argument
  constructor
  · intro _
    trivial
  · intro _
    refine ⟨⟨(argument.2, (argument.2.1, !argument.2.2)), rfl⟩, rfl, ?_⟩
    change argument.2.2 ≠ (!argument.2.2)
    cases argument.2.2 <;> decide

theorem opposite_second (point : Stagesᵒᵖ) :
    imagePower (pullbackSecond forgetTag forgetTag) point (opposite point) = fullPower point := by
  apply Subtype.ext
  apply Predicate.ext
  intro argument
  constructor
  · intro _
    trivial
  · intro _
    refine ⟨⟨(((argument.2.1, !argument.2.2)), argument.2), rfl⟩, rfl, ?_⟩
    change (!argument.2.2) ≠ argument.2.2
    cases argument.2.2 <;> decide

def diagonalReceipt : matchingArguments.obj (world 0) :=
  ⟨(stageValue 0 0 (by omega) true, stageValue 0 0 (by omega) true), rfl⟩

theorem diagonal_distinct_opposite : diagonal (world 0) ≠ opposite (world 0) := by
  intro same
  have truth := congrArg (fun predicate : Power matchingArguments (world 0) =>
    predicate.val.holds (current matchingArguments (world 0) diagonalReceipt)) same
  have impossible : true ≠ true := Eq.mp truth rfl
  exact impossible rfl

theorem comparison_identifies_correlations (point : Stagesᵒᵖ) :
    (comparison forgetTag forgetTag).app point (diagonal point) =
      (comparison forgetTag forgetTag).app point (opposite point) := by
  apply Subtype.ext
  apply Prod.ext
  · exact (diagonal_first point).trans (opposite_first point).symm
  · exact (diagonal_second point).trans (opposite_second point).symm

theorem comparison_not_injective :
    ¬ Function.Injective ((comparison forgetTag forgetTag).app (world 0)) :=
  fun injective => diagonal_distinct_opposite (injective (comparison_identifies_correlations (world 0)))

def fullPair (point : Stagesᵒᵖ) : (pullback (imageHom forgetTag) (imageHom forgetTag)).obj point :=
  ⟨(fullPower point, fullPower point), rfl⟩

theorem canonical_matching_retains_diagonal :
    ((matchingSection forgetTag forgetTag).app (world 0) (fullPair (world 0))).val.holds
      (current matchingArguments (world 0) diagonalReceipt) := ⟨trivial, trivial⟩

def oppositeReceipt : matchingArguments.obj (world 0) :=
  ⟨(stageValue 0 0 (by omega) true, stageValue 0 0 (by omega) false), rfl⟩

theorem canonical_matching_retains_opposite :
    ((matchingSection forgetTag forgetTag).app (world 0) (fullPair (world 0))).val.holds
      (current matchingArguments (world 0) oppositeReceipt) := ⟨trivial, trivial⟩

theorem canonical_matching_keeps_both_readings :
    ((pullbackFirst forgetTag forgetTag).app (world 0) oppositeReceipt).2 = true ∧
      ((pullbackSecond forgetTag forgetTag).app (world 0) oppositeReceipt).2 = false := ⟨rfl, rfl⟩

theorem matching_cover_at_original_bound (point : Stagesᵒᵖ) :
    Nonempty (Enumeration (((matchingSection forgetTag forgetTag).app point (fullPair point)).val)) :=
  ((matchingSection forgetTag forgetTag).app point (fullPair point)).property

def newReceipt (level : Nat) : matchingArguments.obj (world (level + 1)) :=
  ⟨(stageValue (level + 1) (level + 1) (Nat.lt_succ_self (level + 1)) true,
    stageValue (level + 1) (level + 1) (Nat.lt_succ_self (level + 1)) false), rfl⟩

def extension (level : Nat) : world level ⟶ world (level + 1) :=
  (homOfLE (Nat.le_succ level)).op.op

theorem new_pair_not_in_old_image (level : Nat) :
    ¬ ∃ receipt : matchingArguments.obj (world level),
      matchingArguments.map (extension level) receipt = newReceipt level := by
  rintro ⟨receipt, same⟩
  have position := congrArg (fun pair : matchingArguments.obj (world (level + 1)) => pair.val.1.1.val) same
  change receipt.val.1.1.val = level + 1 at position
  have bounded := receipt.val.1.1.isLt
  rw [position] at bounded
  exact Nat.lt_irrefl _ bounded

end Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerWeakPullbackControls
