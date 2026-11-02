import Mettapedia.Computability.KolmogorovComplexity.FramedProgramModel
import Mettapedia.Computability.KolmogorovComplexity.FeatureTheory
import Mettapedia.Computability.KolmogorovComplexity.ReferenceMachine

/-!
# Framed programs as effective prefix machines

The complete program-frame parser determines admission. The underlying plain
interpreter runs only the decoded head with the declared condition pairing.
The framed machine is prefix-free and effective; this alone does not assert
constant-overhead reference-machine universality. Its charged payload framing
instead gives an explicit logarithmic upper comparison to a reference machine.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.PairedWordCode

open scoped Classical
open FeatureTheory

noncomputable def prefixMachine (code : PairedWordCode) (U : ConditionalAlgorithm)
    (pairing : ConditionPairing) : ConditionalPrefixFreeMachine where
  compute := fun program condition => (code.execute U pairing.pack program condition).toOption
  prefix_free := by
    intro condition first second pref different halts
    have defined : (code.execute U pairing.pack first condition).Dom := by
      by_contra missing
      exact halts (Part.toOption_eq_none_iff.mpr missing)
    have absent := code.execute_prefix_none U pairing.pack pref different defined
    simp only [absent, Part.none_toOption]

theorem prefixMachine_part (code : PairedWordCode) (U : ConditionalAlgorithm)
    (pairing : ConditionPairing) (program condition : List Bool) :
    Part.ofOption ((code.prefixMachine U pairing).compute program condition) =
      code.execute U pairing.pack program condition :=
  Part.of_toOption _

theorem prefixMachine_effective (code : PairedWordCode) {U : ConditionalAlgorithm}
    (effective : Partrec₂ U) (pairing : ConditionPairing) : Effective (code.prefixMachine U pairing) :=
  (code.execute_partrec effective pairing.pack_computable).of_eq fun input =>
    (code.prefixMachine_part U pairing input.1 input.2).symm

theorem prefixMachine_program_iff (code : PairedWordCode) (U : ConditionalAlgorithm)
    (pairing : ConditionPairing) (program condition output : List Bool) :
    IsProgram (code.prefixMachine U pairing) program condition output ↔
      ∃ head payload, program = code.encode head payload ∧ output ∈ U head (pairing.pack condition payload) := by
  rw [IsProgram, prefixMachine, Part.toOption_eq_some_iff]
  exact code.execute_iff U pairing.pack program condition output

theorem prefixMachine_encoded (code : PairedWordCode) (U : ConditionalAlgorithm) (pairing : ConditionPairing)
    (head payload condition output : List Bool) (observed : output ∈ U head (pairing.pack condition payload)) :
    IsProgram (code.prefixMachine U pairing) (code.encode head payload) condition output :=
  (code.prefixMachine_program_iff U pairing _ _ _).mpr ⟨head, payload, rfl, observed⟩

theorem prefixMachine_complexity_agrees (code : PairedWordCode) (U : ConditionalAlgorithm)
    (pairing : ConditionPairing) (output condition : List Bool) :
    plainConditionalComplexity (code.execute U pairing.pack) output condition =
      conditionalComplexity (code.prefixMachine U pairing) output condition := by
  have same : prefixAlgorithm (code.prefixMachine U pairing) = code.execute U pairing.pack := by
    funext program condition
    exact code.prefixMachine_part U pairing program condition
  rw [← same]
  exact prefix_complexity_agrees _ _ _

theorem prefixMachine_hasProgram (code : PairedWordCode) (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (pairing : ConditionPairing) (condition output : List Bool) :
    HasProgram (code.prefixMachine U pairing) condition output := by
  obtain ⟨head, computes⟩ := universalConditional_hasProgram U universal (pairing.pack condition []) output
  exact ⟨code.encode head [], code.prefixMachine_encoded U pairing head [] condition output computes⟩

/-- A genuine reference machine simulates this effective framed machine
with one constant chosen before every condition and output. -/
theorem reference_lower_bound (code : PairedWordCode) (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) (pairing : ConditionPairing)
    (V : ConditionalPrefixFreeMachine) (reference : IsReferenceMachine V) :
    ∃ overhead : Nat, ∀ condition output,
      conditionalComplexity V output condition ≤
        plainConditionalComplexity (code.execute U pairing.pack) output condition + overhead := by
  obtain ⟨simulation⟩ := reference.2 (code.prefixMachine U pairing) (code.prefixMachine_effective effective pairing)
  refine ⟨simulation.compilerPrefix.length, fun condition output => ?_⟩
  have bound := simulation.conditionalComplexity_le (code.prefixMachine_hasProgram U universal pairing condition output)
  simpa only [code.prefixMachine_complexity_agrees] using bound

/-- The head is compiled once. The complete payload code, rather than its
raw length, is charged for every simulated prefix program. -/
theorem reference_upper_bound (code : PairedWordCode) (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (pairing : ConditionPairing)
    (V : ConditionalPrefixFreeMachine) (effective : Effective V)
    (payloadOverhead : Nat)
    (payloadBound : ∀ payload, (code.payload.put payload).length ≤
      payload.length + 2 * Nat.log 2 (payload.length + 1) + payloadOverhead) :
    ∃ overhead : Nat, ∀ condition output, HasProgram V condition output →
      plainConditionalComplexity (code.execute U pairing.pack) output condition ≤
        conditionalComplexity V output condition +
          2 * Nat.log 2 (conditionalComplexity V output condition + 1) + overhead := by
  obtain ⟨head, compiles⟩ := pairing.relay_compiler U universal (V := prefixAlgorithm V) effective
  refine ⟨(code.head.put head).length + payloadOverhead, fun condition output represented => ?_⟩
  obtain ⟨program, computes, length⟩ := exists_program_of_conditionalComplexity V condition output represented
  have observed : output ∈ prefixAlgorithm V program condition := (prefixAlgorithm_runs _ _ _ _).mpr computes
  have produces := compiles program condition output observed
  have framed : output ∈ code.execute U pairing.pack (code.encode head program) condition := by
    simpa only [code.execute_encoded] using produces
  have minimum := plainConditionalComplexity_le_of_program (code.execute U pairing.pack)
    condition output (code.encode head program) framed
  have packetLength : (code.encode head program).length =
      (code.head.put head).length + (code.payload.put program).length := List.length_append
  have payload := payloadBound program
  rw [length] at payload
  omega

/-- The lower comparison is constant; the upper comparison charges the
declared logarithmic framing. No constant-overhead reference property for
the framed machine is assumed or concluded. -/
theorem reference_two_sided (code : PairedWordCode) (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) (pairing : ConditionPairing)
    (V : ConditionalPrefixFreeMachine) (reference : IsReferenceMachine V)
    (payloadOverhead : Nat)
    (payloadBound : ∀ payload, (code.payload.put payload).length ≤
      payload.length + 2 * Nat.log 2 (payload.length + 1) + payloadOverhead) :
    ∃ overhead : Nat, ∀ condition output,
      conditionalComplexity V output condition ≤
          plainConditionalComplexity (code.execute U pairing.pack) output condition + overhead ∧
      plainConditionalComplexity (code.execute U pairing.pack) output condition ≤
        conditionalComplexity V output condition +
          2 * Nat.log 2 (conditionalComplexity V output condition + 1) + overhead := by
  obtain ⟨lower, lowerBound⟩ := code.reference_lower_bound U universal effective pairing V reference
  obtain ⟨upper, upperBound⟩ := code.reference_upper_bound U universal pairing V reference.1 payloadOverhead payloadBound
  refine ⟨max lower upper, fun condition output => ?_⟩
  have below := lowerBound condition output
  have above := upperBound condition output (reference.hasProgram _ _)
  constructor <;> omega

#print axioms prefixMachine_part
#print axioms prefixMachine_effective
#print axioms prefixMachine_program_iff
#print axioms prefixMachine_encoded
#print axioms prefixMachine_complexity_agrees
#print axioms prefixMachine_hasProgram
#print axioms reference_lower_bound
#print axioms reference_upper_bound
#print axioms reference_two_sided

end KolmogorovComplexity.PairedWordCode
