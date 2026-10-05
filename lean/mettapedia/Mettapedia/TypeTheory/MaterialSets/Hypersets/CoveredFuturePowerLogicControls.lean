import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerLogic
import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerControls

/-!
# Constructive logic on a genuinely growing covered argument family

The family is the larger-host interpretation of the infinite growing
argument system. The covered predicate that becomes true after stage zero
has no true current argument but has a true continuation of every future
argument. Its relative negation is empty and its relative double negation
holds now. Double-negation elimination therefore fails in this actual
bounded contextual logic, despite every predicate retaining its original
small cover.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerLogicControls

open CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open CoveredFuturePowerLogic CoveredFuturePowerControls
open PowerClassPresheafDescent.Controls

theorem raised_threshold_truth (bound : Nat) (argument : Arguments raised (world 0)) :
    (raisedThreshold bound).val.holds argument ↔ bound ≤ stageIndex argument.1.1 := by
  constructor
  · rintro ⟨_, _, holds⟩
    exact holds
  · intro holds
    exact ⟨argument.2.down, rfl, holds⟩

def bound : Power raised (world 0) := raisedThreshold 0
def laterTruth : Power raised (world 0) := raisedThreshold 1

theorem bound_contains_every_future (argument : Arguments raised (world 0)) :
    bound.val.holds argument := (raised_threshold_truth 0 argument).mpr (Nat.zero_le _)

def nextArrow (argument : Arguments raised (world 0)) :
    argument.1.1 ⟶ world (stageIndex argument.1.1 + 1) :=
  (homOfLE (Nat.le_succ (stageIndex argument.1.1))).op.op

def nextArgument (argument : Arguments raised (world 0)) : Arguments raised (world 0) :=
  ⟨⟨world (stageIndex argument.1.1 + 1), argument.1.2 ≫ nextArrow argument⟩,
    raised.map (nextArrow argument) argument.2⟩

def nextMove (argument : Arguments raised (world 0)) : argument ⟶ nextArgument argument :=
  ⟨⟨nextArrow argument, rfl⟩, rfl⟩

theorem nextArgument_admitted (argument : Arguments raised (world 0)) :
    laterTruth.val.holds (nextArgument argument) :=
  (raised_threshold_truth 1 (nextArgument argument)).mpr (Nat.succ_le_succ (Nat.zero_le _))

def negation (predicate : Power raised (world 0)) : Power raised (world 0) :=
  implicationPower bound predicate.val (bottomPower raised (world 0)).val

theorem laterTruth_bounded : Included laterTruth.val bound.val :=
  fun argument _ => bound_contains_every_future argument

/-- Every proposed negative witness has an actual later positive argument;
the contradiction uses that arrow and retains its argument restriction. -/
theorem negation_laterTruth_empty (argument : Arguments raised (world 0)) :
    ¬ (negation laterTruth).val.holds argument := by
  intro available
  exact available.2 (nextMove argument) (nextArgument_admitted argument)

def initialArgument : Arguments raised (world 0) :=
  current raised (world 0) ⟨stageValue 0 0 (Nat.zero_lt_succ 0) false⟩

theorem laterTruth_absent_now : ¬ laterTruth.val.holds initialArgument := by
  intro impossible
  have boundOne := (raised_threshold_truth 1 initialArgument).mp impossible
  exact Nat.not_succ_le_zero 0 boundOne

theorem doubleNegation_laterTruth_now :
    (negation (negation laterTruth)).val.holds initialArgument := by
  refine ⟨bound_contains_every_future initialArgument, ?_⟩
  intro later _move negative
  exact negation_laterTruth_empty later negative

theorem doubleNegation_does_not_imply_truth :
    ¬ Included (negation (negation laterTruth)).val laterTruth.val :=
  fun eliminate => laterTruth_absent_now (eliminate initialArgument doubleNegation_laterTruth_now)

theorem original_covers_retained :
    Nonempty (Enumeration laterTruth.val) ∧
      Nonempty (Enumeration (negation laterTruth).val) ∧
      Nonempty (Enumeration (negation (negation laterTruth)).val) :=
  ⟨laterTruth.property, (negation laterTruth).property, (negation (negation laterTruth)).property⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerLogicControls
