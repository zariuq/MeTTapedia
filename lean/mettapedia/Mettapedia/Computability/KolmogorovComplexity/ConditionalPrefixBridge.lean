import Mettapedia.Computability.KolmogorovComplexity.PrefixComplexity

/-!
# Conditional slices and effective reference-machine bounds

Fixing an auxiliary condition preserves programs, outputs and shortest-program
lengths. Output completeness gives the ordinary Kraft bounds; effective
reference machines supply it at every condition. No simulation of arbitrary
set-theoretic machines is assumed.
-/

namespace KolmogorovComplexity

open scoped Classical BigOperators

/-- Conditional prefix complexity equals ordinary complexity of the slice. -/
theorem conditionalComplexity_eq_prefixComplexity_slice
    (U : ConditionalPrefixFreeMachine) (condition output : BinString) :
    Kc[U](output | condition) = Kpf[conditionalSlice U condition](output) :=
  conditionalComplexity_eq_kolmogorovComplexity_slice U condition output

/-- A shortest program at any condition of an effective reference machine. -/
noncomputable def shortestConditionalProgram
    (U : ConditionalPrefixFreeMachine) (reference : IsReferenceMachine U)
    (condition output : BinString) : BinString :=
  Classical.choose
    (exists_program_of_conditionalComplexity U condition output
      (reference.hasProgram condition output))

theorem shortestConditionalProgram_spec
    (U : ConditionalPrefixFreeMachine) (reference : IsReferenceMachine U)
    (condition output : BinString) :
    IsProgram U (shortestConditionalProgram U reference condition output) condition output ∧
      (shortestConditionalProgram U reference condition output).length =
        Kc[U](output | condition) :=
  Classical.choose_spec
    (exists_program_of_conditionalComplexity U condition output
      (reference.hasProgram condition output))

/-- Finite conditional Kraft bound inherited from the fixed-condition slice. -/
theorem sum_weightByConditionalComplexity_le_one
    (U : ConditionalPrefixFreeMachine) (reference : IsReferenceMachine U)
    (condition : BinString) (outputs : Finset BinString) :
    (∑ output ∈ outputs,
      (2 : ENNReal) ^ (-(Kc[U](output | condition) : Int))) ≤ 1 := by
  let _ : OutputComplete (conditionalSlice U condition) :=
    ⟨reference.hasProgram condition⟩
  simpa only [conditionalComplexity_eq_prefixComplexity_slice] using
    (sum_weightByKpf_le_one_ennreal
      (U := conditionalSlice U condition) outputs)

/-- Countable conditional Kraft bound inherited from the fixed-condition slice. -/
theorem tsum_weightByConditionalComplexity_le_one
    (U : ConditionalPrefixFreeMachine) (reference : IsReferenceMachine U)
    (condition : BinString) :
    (∑' output : BinString,
      (2 : ENNReal) ^ (-(Kc[U](output | condition) : Int))) ≤ 1 := by
  let _ : OutputComplete (conditionalSlice U condition) :=
    ⟨reference.hasProgram condition⟩
  simpa only [conditionalComplexity_eq_prefixComplexity_slice] using
    (tsum_weightByKpf_le_one_ennreal (U := conditionalSlice U condition))

/-- Freezing a condition does not add missing outputs. -/
theorem fixedEmptySlice_not_outputComplete :
    ¬ OutputComplete (conditionalSlice fixedEmptyMachine []) := by
  intro complete
  obtain ⟨program, computes⟩ := complete.has_program [true]
  simp [conditionalSlice, fixedEmptyMachine] at computes

/-- The singleton-output machine cannot be an effective reference machine. -/
theorem fixedEmptyMachine_not_reference : ¬ IsReferenceMachine fixedEmptyMachine := by
  intro reference
  obtain ⟨program, computes⟩ := reference.hasProgram [] [true]
  simp [IsProgram, fixedEmptyMachine] at computes

#print axioms conditionalComplexity_eq_prefixComplexity_slice
#print axioms shortestConditionalProgram_spec
#print axioms sum_weightByConditionalComplexity_le_one
#print axioms tsum_weightByConditionalComplexity_le_one
#print axioms fixedEmptyMachine_not_reference

end KolmogorovComplexity
