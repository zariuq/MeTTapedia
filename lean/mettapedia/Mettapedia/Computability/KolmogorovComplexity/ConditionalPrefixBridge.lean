import Mettapedia.Computability.KolmogorovComplexity.Conditional
import Mettapedia.Computability.KolmogorovComplexity.PrefixComplexity

/-!
# Conditional prefix complexity as a family of Solomonoff machines

This file connects the conditional machines used by algorithmic containment
to Mettapedia's existing unconditional prefix-machine development.  Fixing an
auxiliary condition produces an ordinary prefix-free machine, with exactly the
same programs, outputs, and shortest-program lengths.  Consequently the
Solomonoff/Hutter shortest-program and Kraft theorems can be reused rather
than reproved for each condition.

The distinction between two historical notions of universality remains
explicit:

* `UniversalPFM` says that one ordinary machine simulates every ordinary
  prefix-free machine with a machine-dependent additive bound;
* `UniformlyUniversalConditionalPFM` supplies one compiler prefix for an
  entire conditional machine, uniformly over its auxiliary input.

Both historical classes quantify over arbitrary set-theoretic machines and
are therefore too strong.  `UniversalAI.UniversalMachineBoundary` proves them
uninhabited and replaces them by effective indexed universality.  The slice,
complexity, and Kraft bridges in this file remain valid; the old universality
instances remain temporarily as compatibility interfaces for conditional
theorems whose assumptions are now known to be impossible.

References: Solomonoff (1964), *A Formal Theory of Inductive Inference*;
Hutter (2005), *Universal Artificial Intelligence*, Chapters 2--3.  The
conditional interface is also the finite-description substrate used by the
open-ended world-model developments descending from Hutter and Leike.
-/

namespace KolmogorovComplexity

open scoped Classical BigOperators

open Mettapedia.UniversalAI.SolomonoffPrior

/-- Freeze the auxiliary input of a conditional prefix-free machine. -/
def conditionalSlice (U : ConditionalPrefixFreeMachine)
    (condition : BinString) : PrefixFreeMachine where
  compute := fun program => U.compute program condition
  prefix_free := by
    intro program extension isPrefix distinct halts
    exact U.prefix_free condition program extension isPrefix distinct halts

@[simp] theorem conditionalSlice_compute
    (U : ConditionalPrefixFreeMachine) (condition program : BinString) :
    (conditionalSlice U condition).compute program = U.compute program condition :=
  rfl

/-- Representability is unchanged by freezing the condition. -/
theorem hasProgram_iff_conditionalSlice
    (U : ConditionalPrefixFreeMachine) (condition output : BinString) :
    HasProgram U condition output ↔
      ∃ program, (conditionalSlice U condition).compute program = some output := by
  rfl

/-- Conditional prefix complexity is exactly ordinary prefix complexity on
the fixed-condition slice, including the common `0` convention outside the
represented range. -/
theorem conditionalComplexity_eq_prefixComplexity_slice
    (U : ConditionalPrefixFreeMachine) (condition output : BinString) :
    Kc[U](output | condition) = Kpf[conditionalSlice U condition](output) := by
  by_cases represented : HasProgram U condition output
  · have representedSlice :
        ∃ program, (conditionalSlice U condition).compute program = some output :=
      (hasProgram_iff_conditionalSlice U condition output).mp represented
    apply Nat.le_antisymm
    · obtain ⟨program, computes, lengthEq⟩ :=
        Mettapedia.UniversalAI.SolomonoffPrior.exists_program_of_complexity
          (conditionalSlice U condition) output representedSlice
      have bound := conditionalComplexity_le_program_length U condition output
        program computes
      simpa [prefixComplexity, lengthEq] using bound
    · obtain ⟨program, computes, lengthEq⟩ :=
        exists_program_of_conditionalComplexity U condition output represented
      have bound :=
        Mettapedia.UniversalAI.SolomonoffPrior.complexity_le_program_length
          (conditionalSlice U condition) output program computes
      simpa [prefixComplexity, lengthEq] using bound
  · have notRepresentedSlice :
        ¬ ∃ program, (conditionalSlice U condition).compute program = some output := by
      exact fun h => represented
        ((hasProgram_iff_conditionalSlice U condition output).mpr h)
    rw [conditionalComplexity_eq_zero_of_not_hasProgram U condition output represented]
    change 0 = Mettapedia.UniversalAI.SolomonoffPrior.kolmogorovComplexity
      (conditionalSlice U condition) output
    unfold Mettapedia.UniversalAI.SolomonoffPrior.kolmogorovComplexity
    rw [dif_neg notRepresentedSlice]

/-- Regard an ordinary prefix-free machine as a condition-blind conditional
machine. -/
def conditionBlindLift (M : PrefixFreeMachine) : ConditionalPrefixFreeMachine where
  compute := fun program _condition => M.compute program
  prefix_free := by
    intro _condition program extension isPrefix distinct halts
    exact M.prefix_free program extension isPrefix distinct halts

@[simp] theorem conditionBlindLift_compute
    (M : PrefixFreeMachine) (program condition : BinString) :
    (conditionBlindLift M).compute program condition = M.compute program :=
  rfl

/-- Historical unrestricted conditional universality: every set-theoretic
conditional prefix-free machine is simulated by one compiler prefix, uniformly
over auxiliary input.  This class is uninhabited; use the effective indexed
replacement in `UniversalAI.UniversalMachineBoundary`. -/
class UniformlyUniversalConditionalPFM
    (U : ConditionalPrefixFreeMachine) : Type where
  simulates : ∀ M : ConditionalPrefixFreeMachine, UniformlySimulates U M

/-- Strong conditional universality supplies an ordinary `UniversalPFM`
instance at every fixed condition. -/
instance conditionalSlice.instUniversalPFM
    (U : ConditionalPrefixFreeMachine) [UniformlyUniversalConditionalPFM U]
    (condition : BinString) : UniversalPFM (conditionalSlice U condition) where
  universal := by
    intro M
    let simulation :=
      UniformlyUniversalConditionalPFM.simulates (U := U) (conditionBlindLift M)
    refine ⟨simulation.compilerPrefix.length, ?_⟩
    intro program output computes
    refine ⟨simulation.compilerPrefix ++ program, ?_, ?_⟩
    · change U.compute (simulation.compilerPrefix ++ program) condition = some output
      rw [simulation.compute_eq]
      exact computes
    · simp [List.length_append, Nat.add_comm]

/-- A uniformly universal conditional machine represents every finite output
at every condition. -/
theorem uniformlyUniversalConditional_hasProgram
    (U : ConditionalPrefixFreeMachine) [UniformlyUniversalConditionalPFM U]
    (condition output : BinString) :
    HasProgram U condition output := by
  obtain ⟨program, computes⟩ :=
    universalPFM_has_program (U := conditionalSlice U condition) output
  exact (hasProgram_iff_conditionalSlice U condition output).mpr
    ⟨program, computes⟩

/-- Reuse the UniversalAI shortest-program choice at a fixed condition. -/
noncomputable def shortestConditionalProgram
    (U : ConditionalPrefixFreeMachine) [UniformlyUniversalConditionalPFM U]
    (condition output : BinString) : BinString :=
  shortestProgram (conditionalSlice U condition) output

theorem shortestConditionalProgram_spec
    (U : ConditionalPrefixFreeMachine) [UniformlyUniversalConditionalPFM U]
    (condition output : BinString) :
    IsProgram U (shortestConditionalProgram U condition output) condition output ∧
      (shortestConditionalProgram U condition output).length =
        Kc[U](output | condition) := by
  have specification := shortestProgram_spec
    (U := conditionalSlice U condition) output
  constructor
  · exact specification.1
  · rw [conditionalComplexity_eq_prefixComplexity_slice]
    exact specification.2

/-- Finite conditional Kraft bound inherited from the UniversalAI slice. -/
theorem sum_weightByConditionalComplexity_le_one
    (U : ConditionalPrefixFreeMachine) [UniformlyUniversalConditionalPFM U]
    (condition : BinString) (outputs : Finset BinString) :
    (∑ output ∈ outputs,
      (2 : ENNReal) ^ (-(Kc[U](output | condition) : Int))) ≤ 1 := by
  simpa only [conditionalComplexity_eq_prefixComplexity_slice] using
    (sum_weightByKpf_le_one_ennreal
      (U := conditionalSlice U condition) outputs)

/-- Countable conditional Kraft bound inherited from the UniversalAI slice. -/
theorem tsum_weightByConditionalComplexity_le_one
    (U : ConditionalPrefixFreeMachine) [UniformlyUniversalConditionalPFM U]
    (condition : BinString) :
    (∑' output : BinString,
      (2 : ENNReal) ^ (-(Kc[U](output | condition) : Int))) ≤ 1 := by
  simpa only [conditionalComplexity_eq_prefixComplexity_slice] using
    (tsum_weightByKpf_le_one_ennreal
      (U := conditionalSlice U condition))

/-! ## Negative control -/

/-- Freezing a condition does not make a non-universal machine universal.  The
fixed-output machine cannot represent `[true]`. -/
theorem fixedEmptySlice_not_universal :
    ¬ UniversalPFM (conditionalSlice fixedEmptyMachine []) := by
  intro universal
  letI : UniversalPFM (conditionalSlice fixedEmptyMachine []) := universal
  obtain ⟨program, computes⟩ :=
    universalPFM_has_program
      (U := conditionalSlice fixedEmptyMachine []) [true]
  simp [conditionalSlice, fixedEmptyMachine] at computes

#print axioms conditionalComplexity_eq_prefixComplexity_slice
#print axioms conditionalSlice.instUniversalPFM
#print axioms shortestConditionalProgram_spec
#print axioms sum_weightByConditionalComplexity_le_one
#print axioms tsum_weightByConditionalComplexity_le_one
#print axioms fixedEmptySlice_not_universal

end KolmogorovComplexity
