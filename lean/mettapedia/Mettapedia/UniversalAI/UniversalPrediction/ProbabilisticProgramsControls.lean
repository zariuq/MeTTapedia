import Mettapedia.UniversalAI.UniversalPrediction.ProbabilisticPrograms
import Mettapedia.UniversalAI.UniversalPrediction.BitProgramTape

/-! # Model selection and an emitted prefix followed by divergence -/

set_option autoImplicit false

namespace Mettapedia.UniversalAI.UniversalPrediction.ProbabilisticPrograms.Controls

open Mettapedia.Computability
open BitGenerator

private def atZero (step : Transition Nat Bool) : Generator Nat Bool where
  initial := 0
  atStage _ := step
  stable _ observed := observed

def copy : Generator Nat Bool := atZero fun
  | 0 => some (.read 1 2)
  | 1 => some (.emit false 3)
  | 2 => some (.emit true 4)
  | 3 => some (.emit false 5)
  | 4 => some (.emit true 5)
  | _ => none

def fresh : Generator Nat Bool := atZero fun
  | 0 => some (.read 1 2)
  | 1 => some (.emit false 3)
  | 2 => some (.emit true 3)
  | 3 => some (.read 4 5)
  | 4 => some (.emit false 6)
  | 5 => some (.emit true 6)
  | _ => none

def catalogue : List (Hypothesis Nat) :=
  [⟨1 / 2, by norm_num, copy⟩, ⟨1 / 2, by norm_num, fresh⟩]

theorem next_before_evidence : predictAt catalogue [] 4 true = some (1 / 2) := by
  decide +kernel

theorem first_bit_does_not_identify_model :
    posteriorAt catalogue [true] 4 0 = some (1 / 2) := by
  decide +kernel

theorem next_after_one : predictAt catalogue [true] 4 true = some (3 / 4) := by
  decide +kernel

theorem evidence_mass : catalogueMass catalogue [true, true] 4 = 3 / 8 := by
  decide +kernel

/-- Same prior, different likelihoods of the observed history. -/
theorem copy_learned : posteriorAt catalogue [true, true] 4 0 = some (2 / 3) := by
  decide +kernel

theorem fresh_remains_possible : posteriorAt catalogue [true, true] 4 1 = some (1 / 3) := by
  decide +kernel

/-- Before the cutoff permits an emission, this same true observation has
no known mass. Later it has positive mass. -/
theorem zero_cut_pending : predictAt catalogue [true] 0 true = none := by
  decide +kernel

/-- Nothing beyond the two emitted bits is in the model's next-symbol law. -/
theorem no_extra_output :
    predictAt catalogue [true, true] 4 true = some 0 ∧
    predictAt catalogue [true, true] 4 false = some 0 := by decide +kernel

def emitThenLoop : Generator Nat Bool := atZero fun
  | 0 => some (.emit true 1)
  | _ => some (.silent 1)

private theorem loop_output_empty (fuel : Nat) (tape : List Bool) :
    output (emitThenLoop.atStage fuel) fuel 1 tape = [] := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact ih

private theorem emitThenLoop_cut (fuel : Nat) (tape : List Bool) :
    emitThenLoop.cut (fuel + 1) tape = [true] := by
  change true :: output (emitThenLoop.atStage fuel) fuel 1 tape = [true]
  rw [loop_output_empty]

theorem emitted_prefix_retained : emitThenLoop.event [true] = Set.univ := by
  apply Set.eq_univ_of_forall
  intro tape
  exact ⟨1, by rw [emitThenLoop_cut]⟩

theorem no_second_symbol (bit : Bool) : emitThenLoop.event [true, bit] = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro tape ⟨fuel, seen⟩
  have length := seen.length_le
  cases fuel with
  | zero => simp [Generator.cut, output] at length
  | succ fuel => rw [emitThenLoop_cut] at length; simp at length

/-- A generator may emit a known prefix with probability one while the sum
of probabilities of its immediate extensions is zero. -/
theorem strict_semimeasure :
    emitThenLoop.semimeasure [true] = 1 ∧
      emitThenLoop.semimeasure [true, false] + emitThenLoop.semimeasure [true, true] = 0 := by
  simp [emitted_prefix_retained, no_second_symbol]

/-! The direct code enumeration also executes. The first observed bit is
unresolved until a generator emits it. One additional step changes the
prediction by witnessing an extension of the same observation. -/

#guard BitProgramMixture.predictAt [false] 17 false == none
#guard BitProgramMixture.predictAt [false] 18 false == some 0
#guard BitProgramMixture.predictAt [false] 19 false == some 1

#print axioms next_after_one
#print axioms copy_learned
#print axioms strict_semimeasure

end Mettapedia.UniversalAI.UniversalPrediction.ProbabilisticPrograms.Controls
