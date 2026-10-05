import Mettapedia.Computability.KolmogorovComplexity.ReferenceMachine
import Mettapedia.Computability.KolmogorovComplexity.DiscreteSemimeasureCoding
import Mettapedia.UniversalAI.UniversalPrediction
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Effective presented weights

An effective discrete dyadic approximation presents a weight by the supremum
of its finite-stage masses. Its effective Kraft--Chaitin coder gives a finite
comparison constant against every effective reference machine. The same
compiler works uniformly over auxiliary conditions.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.UniversalAI.UniversalPrediction.EffectiveWeights

open KolmogorovComplexity KolmogorovComplexity.KraftChaitin
open scoped ENNReal BigOperators Classical

/-- One finite-stage mass of an effective discrete approximation. -/
def stageWeight (approximation : EffectiveDiscreteDyadic)
    (condition : BinString) (stage : Nat) (output : BinString) : ENNReal :=
  (approximation.numerator condition stage (Encodable.encode output) : ENNReal) /
    (2 : ENNReal) ^ stage

/-- The discrete weight presented by the effective finite-stage masses. -/
def conditionalWeight (approximation : EffectiveDiscreteDyadic)
    (condition output : BinString) : ENNReal :=
  ⨆ stage : Nat, stageWeight approximation condition stage output

/-- Unconditional weights use the empty auxiliary condition. -/
def presentedWeight (approximation : EffectiveDiscreteDyadic)
    (output : BinString) : ENNReal :=
  conditionalWeight approximation [] output

theorem stageWeight_le_one (approximation : EffectiveDiscreteDyadic)
    (condition : BinString) (stage : Nat) (output : BinString) :
    stageWeight approximation condition stage output ≤ 1 := by
  have bound :
      (approximation.numerator condition stage (Encodable.encode output) : ENNReal) ≤
        (2 : ENNReal) ^ stage := by
    exact_mod_cast approximation.numerator_le_pow condition stage (Encodable.encode output)
  exact (ENNReal.div_le_div_right bound ((2 : ENNReal) ^ stage)).trans
    ENNReal.div_self_le_one

theorem conditionalWeight_le_one (approximation : EffectiveDiscreteDyadic)
    (condition output : BinString) : conditionalWeight approximation condition output ≤ 1 :=
  iSup_le fun stage => stageWeight_le_one approximation condition stage output

/-- Positive stage mass supplies an actual coder program and hence a reference
description whose cost is the stage plus the compiler and two reserve bits. -/
theorem positive_numerator_complexity_le
    (approximation : EffectiveDiscreteDyadic) (machine : ConditionalPrefixFreeMachine)
    (simulation : UniformlySimulates machine (discreteDyadicMachine approximation))
    (condition output : BinString) (stage : Nat)
    (positive : 0 < approximation.numerator condition stage (Encodable.encode output)) :
    Kc[machine](output | condition) ≤ stage + 2 + simulation.compilerPrefix.length := by
  have supported : Encodable.encode output ≤ stage := by
    by_contra outside
    have zero := approximation.support condition stage (Encodable.encode output)
      (Nat.lt_of_not_ge outside)
    omega
  have crossing : ThresholdCrossed approximation condition stage
      (Encodable.encode output) stage := by
    refine ⟨supported, le_rfl, ?_⟩
    simp only [Nat.sub_self, pow_zero]
    omega
  have program := discreteDyadicMachine_hasProgram_of_crossed crossing
  have coding := discreteDyadicMachine_complexity_of_crossed crossing
  have translation := simulation.conditionalComplexity_le program
  omega

/-- Finite-stage concentration follows from effective threshold coding. -/
theorem numerator_le_pow_complexity
    (approximation : EffectiveDiscreteDyadic) (machine : ConditionalPrefixFreeMachine)
    (simulation : UniformlySimulates machine (discreteDyadicMachine approximation))
    (condition output : BinString) (stage : Nat) :
    approximation.numerator condition stage (Encodable.encode output) ≤
      2 ^ (stage + (simulation.compilerPrefix.length + 3) -
        Kc[machine](output | condition)) := by
  let mass := approximation.numerator condition stage (Encodable.encode output)
  let complexity := Kc[machine](output | condition)
  let cost := simulation.compilerPrefix.length + 3
  by_cases zero : mass = 0
  · change mass ≤ _
    rw [zero]
    exact Nat.zero_le _
  have positive : 0 < mass := Nat.pos_of_ne_zero zero
  have representedBound : complexity ≤ stage + 2 + simulation.compilerPrefix.length :=
    positive_numerator_complexity_le approximation machine simulation condition output
      stage positive
  have supported : Encodable.encode output ≤ stage := by
    by_contra outside
    have noMass := approximation.support condition stage (Encodable.encode output)
      (Nat.lt_of_not_ge outside)
    exact zero noMass
  by_cases small : complexity ≤ cost
  · have exponent : stage ≤ stage + cost - complexity := by omega
    exact (approximation.numerator_le_pow condition stage (Encodable.encode output)).trans
      (Nat.pow_le_pow_right (by omega) exponent)
  · let threshold := complexity - cost
    have thresholdBound : threshold ≤ stage := by
      dsimp [threshold, complexity, cost] at *
      omega
    have exponent : stage - threshold = stage + cost - complexity := by
      dsimp [threshold]
      omega
    by_contra tooLarge
    have crossing : ThresholdCrossed approximation condition stage
        (Encodable.encode output) threshold := by
      refine ⟨supported, thresholdBound, ?_⟩
      rw [exponent]
      exact (Nat.lt_of_not_ge tooLarge).le
    have program := discreteDyadicMachine_hasProgram_of_crossed crossing
    have coding := discreteDyadicMachine_complexity_of_crossed crossing
    have translation := simulation.conditionalComplexity_le program
    dsimp [threshold, complexity, cost] at *
    omega

/-- Dividing the concentration bound by the stage denominator leaves a
constant independent of the stage and the output. -/
theorem stageWeight_le_const_mul_complexityWeight
    (approximation : EffectiveDiscreteDyadic) (machine : ConditionalPrefixFreeMachine)
    (simulation : UniformlySimulates machine (discreteDyadicMachine approximation))
    (condition output : BinString) (stage : Nat) :
    stageWeight approximation condition stage output ≤
      (2 : ENNReal) ^ ((simulation.compilerPrefix.length + 3 : Nat) : Int) *
        (2 : ENNReal) ^ (-(Kc[machine](output | condition) : Int)) := by
  by_cases zero : approximation.numerator condition stage (Encodable.encode output) = 0
  · simp [stageWeight, zero]
  have positive : 0 < approximation.numerator condition stage (Encodable.encode output) :=
    Nat.pos_of_ne_zero zero
  let cost := simulation.compilerPrefix.length + 3
  let complexity := Kc[machine](output | condition)
  have representedBound := positive_numerator_complexity_le approximation machine
    simulation condition output stage positive
  have fits : complexity ≤ stage + cost := by
    dsimp [complexity, cost]
    omega
  have numeratorBound :
      (approximation.numerator condition stage (Encodable.encode output) : ENNReal) ≤
        (2 : ENNReal) ^ (stage + cost - complexity) := by
    exact_mod_cast numerator_le_pow_complexity approximation machine simulation condition output stage
  have exponent : (((stage + cost - complexity : Nat) : Int) - (stage : Int)) =
      (cost : Int) - (complexity : Int) := by omega
  calc
    stageWeight approximation condition stage output ≤
        (2 : ENNReal) ^ (stage + cost - complexity) / (2 : ENNReal) ^ stage :=
      ENNReal.div_le_div_right numeratorBound ((2 : ENNReal) ^ stage)
    _ = (2 : ENNReal) ^ (((stage + cost - complexity : Nat) : Int) - (stage : Int)) := by
      rw [ENNReal.zpow_sub (by norm_num) (by simp)]
      simp only [zpow_natCast, div_eq_mul_inv]
    _ = (2 : ENNReal) ^ ((cost : Int) - (complexity : Int)) := by rw [exponent]
    _ = (2 : ENNReal) ^ (cost : Int) * (2 : ENNReal) ^ (-(complexity : Int)) := by
      rw [sub_eq_add_neg, ENNReal.zpow_add (by norm_num) (by simp)]

/-- Every presented effective weight admits a finite comparison constant.
The effective coder is simulated with one prefix, uniformly over conditions. -/
theorem exists_finite_const_mul_conditionalWeight
    (U : ReferenceMachine) (approximation : EffectiveDiscreteDyadic) :
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧ ∀ condition output : BinString,
      conditionalWeight approximation condition output ≤
        C * (2 : ENNReal) ^ (-(Kc[U.machine](output | condition) : Int)) := by
  obtain ⟨simulation⟩ := U.reference.2 (discreteDyadicMachine approximation)
    (discreteDyadicMachine_effective approximation)
  refine ⟨(2 : ENNReal) ^ ((simulation.compilerPrefix.length + 3 : Nat) : Int),
    (ENNReal.zpow_pos (by norm_num) (by simp) _).ne',
    ENNReal.zpow_ne_top (by norm_num) (by simp) _, ?_⟩
  intro condition output
  exact iSup_le fun stage => stageWeight_le_const_mul_complexityWeight approximation
    U.machine simulation condition output stage

/-- The empty-condition slice gives the ordinary prefix-complexity weight
`2^{-Kpf}`. The comparison constant is strictly positive and finite. -/
theorem exists_finite_const_mul_kpfWeight
    (U : ReferenceMachine) (approximation : EffectiveDiscreteDyadic) :
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧ ∀ output : BinString,
      presentedWeight approximation output ≤
        C * kpfWeight (conditionalSlice U.machine []) output := by
  obtain ⟨C, positive, finite, bound⟩ :=
    exists_finite_const_mul_conditionalWeight U approximation
  refine ⟨C, positive, finite, ?_⟩
  intro output
  simpa only [presentedWeight, kpfWeight, KolmogorovComplexity.prefixComplexity,
    conditionalComplexity_eq_kolmogorovComplexity_slice]
    using bound [] output

/-- An exact effective presentation of a weight is enough; no target
domination inequality is supplied as a hypothesis. -/
theorem exists_finite_const_mul_kpfWeight_of_representation
    (U : ReferenceMachine) (approximation : EffectiveDiscreteDyadic)
    (v : BinString → ENNReal)
    (representation : ∀ output, v output = presentedWeight approximation output) :
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧ ∀ output : BinString,
      v output ≤ C * kpfWeight (conditionalSlice U.machine []) output := by
  obtain ⟨C, positive, finite, bound⟩ := exists_finite_const_mul_kpfWeight U approximation
  refine ⟨C, positive, finite, ?_⟩
  intro output
  rw [representation output]
  exact bound output

/-- Positive control: the existing point-mass approximation puts unit mass
on the empty output. -/
theorem pointMass_presentedWeight_empty : presentedWeight pointMassDyadic [] = 1 := by
  apply le_antisymm
  · exact conditionalWeight_le_one pointMassDyadic [] []
  · have initial : stageWeight pointMassDyadic [] 0 [] = 1 := by
      norm_num [stageWeight, pointMassDyadic]
    exact le_iSup_of_le 0 initial.ge

/-- Negative control: the same approximation assigns no mass to any
nonempty output. -/
theorem pointMass_presentedWeight_of_nonempty (output : BinString) (nonempty : output ≠ []) :
    presentedWeight pointMassDyadic output = 0 := by
  have codeNonzero : Encodable.encode output ≠ 0 := by
    intro zero
    apply nonempty
    apply Encodable.encode_injective
    exact zero
  apply le_antisymm
  · exact iSup_le fun stage => by
      simp [stageWeight, pointMassDyadic, codeNonzero]
  · exact bot_le

/-- The concrete trimmed reference machine dominates an actual positive
presented weight with a finite constant. -/
theorem canonical_dominates_pointMass :
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧ ∀ output : BinString,
      presentedWeight pointMassDyadic output ≤
        C * kpfWeight (conditionalSlice ReferenceMachine.canonical.machine []) output :=
  exists_finite_const_mul_kpfWeight ReferenceMachine.canonical pointMassDyadic

#print axioms numerator_le_pow_complexity
#print axioms exists_finite_const_mul_kpfWeight
#print axioms exists_finite_const_mul_kpfWeight_of_representation
#print axioms pointMass_presentedWeight_empty
#print axioms pointMass_presentedWeight_of_nonempty
#print axioms canonical_dominates_pointMass

end Mettapedia.UniversalAI.UniversalPrediction.EffectiveWeights
