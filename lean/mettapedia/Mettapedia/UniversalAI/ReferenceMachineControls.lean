import Mettapedia.Computability.HutterComputabilityRational
import Mettapedia.Computability.KolmogorovComplexity.ConditionalPrefixBridge
import Mettapedia.UniversalAI.PredictivePrivilege
import Mettapedia.UniversalAI.UniversalPrediction.HutterV3Kpf
import Mettapedia.UniversalAI.SimplicityUncertainty

/-!
# Inhabited controls for effective reference-machine bounds

The trimmed indexed interpreter supplies programs for every output and obeys
the all-output Kraft bound. A second effective reference machine gives a
strictly shorter description to a selected output. Their complexities and
mixtures nevertheless satisfy the additive and multiplicative invariance
bounds.

The fair-coin generator supplies a concrete lower-semicomputable prefix
measure. Both the binary-code mixture and Hutter's code-weighted mixture
dominate it with positive weights, and the latter has a finite-horizon
relative-entropy bound. Negative controls distinguish effective universality
from unrestricted simulation and output completeness.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.UniversalAI.ReferenceMachineControls

open KolmogorovComplexity
open Mettapedia.UniversalAI.UniversalPrediction
open scoped Classical BigOperators ENNReal

abbrev BinString := List Bool

theorem canonical_hasProgram (condition output : BinString) :
    HasProgram ReferenceMachine.canonical.machine condition output :=
  ReferenceMachine.canonical.reference.hasProgram condition output

theorem canonical_allOutputKraft :
    (∑' output : BinString,
      (2 : ENNReal) ^ (-(Kpf[ReferenceMachine.canonical](output) : Int))) ≤ 1 :=
  tsum_weightByKpf_le_one_ennreal ReferenceMachine.canonical

theorem canonical_conditionalKraft (condition : BinString) :
    (∑' output : BinString,
      (2 : ENNReal) ^
        (-(Kc[ReferenceMachine.canonical.machine](output | condition) : Int))) ≤ 1 :=
  tsum_weightByConditionalComplexity_le_one ReferenceMachine.canonical.machine
    ReferenceMachine.canonical.reference condition

/-- An output outside the canonical interpreter's programs of length at most one. -/
def favouredOutput : BinString :=
  PredictivePrivilege.unfavoured ReferenceMachine.canonical.machine

/-- A distinct interpreter that adds one short description and still hosts
every effective conditional prefix machine. -/
def favouredReference : ReferenceMachine where
  machine := PredictivePrivilege.favour ReferenceMachine.canonical.machine favouredOutput
  reference := PredictivePrivilege.favour_isReferenceMachine
    ReferenceMachine.canonical.reference favouredOutput

theorem favoured_machine_ne_canonical :
    favouredReference.machine ≠ ReferenceMachine.canonical.machine := by
  intro same
  have produces : IsProgram favouredReference.machine [false] [] favouredOutput := rfl
  rw [same] at produces
  exact PredictivePrivilege.unfavoured_not_produced
    ReferenceMachine.canonical.machine le_rfl produces

theorem favoured_reference_ne_canonical :
    favouredReference ≠ ReferenceMachine.canonical := by
  intro same
  exact favoured_machine_ne_canonical (congrArg ReferenceMachine.machine same)

theorem favoured_complexity_strict :
    Kpf[favouredReference](favouredOutput) <
      Kpf[ReferenceMachine.canonical](favouredOutput) := by
  obtain ⟨shortest, produces, length⟩ :=
    SolomonoffPrior.exists_program_of_complexity ReferenceMachine.canonical favouredOutput
      (outputComplete_has_program ReferenceMachine.canonical favouredOutput)
  have long : 1 < shortest.length := by
    by_contra notLong
    exact PredictivePrivilege.unfavoured_not_produced
      ReferenceMachine.canonical.machine (by omega) produces
  have short := SolomonoffPrior.complexity_le_program_length
    (U := favouredReference) (x := favouredOutput) (p := [false]) rfl
  simp only [List.length_singleton] at short
  change shortest.length = Kpf[ReferenceMachine.canonical](favouredOutput) at length
  change Kpf[favouredReference](favouredOutput) ≤ 1 at short
  omega

theorem canonical_cannot_translate_favoured_at_zero :
    ¬ Translates ReferenceMachine.canonical.machine favouredReference.machine 0 := by
  rintro ⟨simulation, bound⟩
  have empty : simulation.compilerPrefix = [] :=
    List.eq_nil_of_length_eq_zero (by omega)
  have runs := simulation.compute_eq [false] []
  rw [empty, List.nil_append] at runs
  exact PredictivePrivilege.unfavoured_not_produced
    ReferenceMachine.canonical.machine le_rfl runs

theorem canonical_favoured_invariance :
    ∃ c : Nat, ∀ output : BinString,
      |((Kpf[ReferenceMachine.canonical](output) : Int) -
        Kpf[favouredReference](output))| ≤ c :=
  SolomonoffPrior.invariance_symmetric ReferenceMachine.canonical favouredReference

theorem canonical_favoured_simplicity_bound :
    ∃ c : Nat, ∀ output : BinString,
      Kpf[ReferenceMachine.canonical](output) ≤ Kpf[favouredReference](output) + c :=
  SimplicityUncertainty.invariance_Kpf ReferenceMachine.canonical favouredReference

private theorem twoPow_computable : Computable fun n : Nat => 2 ^ n := by
  have multiply : Computable₂ ((· * ·) : Nat → Nat → Nat) := Primrec.nat_mul.to_comp
  have step : Computable₂ fun (_ : Nat) (state : Nat × Nat) => state.2 * 2 := by
    simpa using
      (multiply.comp (Computable.snd.comp Computable.snd) (Computable.const 2)).to₂
  have recurse : Computable fun n : Nat =>
      Nat.rec (motive := fun _ => Nat) 1 (fun _ previous => previous * 2) n :=
    Computable.nat_rec Computable.id (Computable.const 1) step
  refine recurse.of_eq ?_
  intro n
  induction n with
  | zero => simp
  | succ n ih => simp [Nat.pow_succ, ih, Nat.mul_comm]

/-- The existing fair-coin generator, with mass `2^{-|word|}` on each cylinder. -/
def coinMeasure : PrefixMeasure := PredictivePrivilege.fairCoin.toPrefixMeasure

theorem coin_two_bit_mass : coinMeasure [false, true] = (1 / 4 : ENNReal) := by
  rw [coinMeasure, PredictivePrivilege.fairCoin_law]
  change (2⁻¹ : ENNReal) ^ 2 = 1 / 4
  rw [← ENNReal.inv_pow]
  norm_num

/-- A computable rational presentation provides a genuine LSC witness. -/
theorem coin_lsc : HutterEnumeration.LowerSemicomputablePrefixMeasure coinMeasure := by
  have ratio := Mettapedia.Computability.Hutter.LowerSemicomputable.of_natRatio
    (num := fun _word : BinString => 1)
    (den := fun word : BinString => 2 ^ word.length)
    (hnum := Computable.const 1)
    (hden := twoPow_computable.comp Computable.list_length)
    (hden_pos := fun _word => pow_pos (by norm_num : 0 < (2 : Nat)) _)
  rw [coinMeasure, PredictivePrivilege.fairCoin_law]
  unfold HutterEnumeration.LowerSemicomputablePrefixMeasure
  have values :
      (fun word : BinString => (HutterEnumerationTheorem.uniformPrefixMeasure word).toReal) =
        fun word : BinString => (1 : ℝ) / ((2 : Nat) ^ word.length : ℝ) := by
    funext word
    change ((2⁻¹ : ENNReal) ^ word.length).toReal =
      (1 : ℝ) / ((2 : Nat) ^ word.length : ℝ)
    simp [ENNReal.toReal_pow, ENNReal.toReal_inv, inv_pow, div_eq_mul_inv]
  rw [values]
  simpa only [Nat.cast_one, Nat.cast_pow] using ratio

/-- Binary indices decode actual semimeasure-enumeration codes. -/
def binaryCodeFamily (index : BinString) : Semimeasure :=
  HutterEnumerationTheoremSemimeasure.evalLSC
    (Nat.Partrec.Code.ofNatCode (ofBinaryBits index))

theorem binaryCodeFamily_at_code (code : Nat.Partrec.Code) :
    binaryCodeFamily (binaryBits (Nat.Partrec.Code.encodeCode code)) =
      HutterEnumerationTheoremSemimeasure.evalLSC code := by
  simp [binaryCodeFamily, ofBinaryBits_binaryBits, ofNatCode_encodeCode]

theorem canonical_weight_pos (index : BinString) :
    0 < kpfWeight (U := ReferenceMachine.canonical) index := by
  unfold kpfWeight
  exact ENNReal.zpow_pos (by norm_num) (by simp) _

theorem canonical_component_dominance (index history : BinString) :
    kpfWeight (U := ReferenceMachine.canonical) index * binaryCodeFamily index history ≤
      xiKpfSemimeasure (U := ReferenceMachine.canonical) binaryCodeFamily history :=
  xiKpf_dominates_index ReferenceMachine.canonical binaryCodeFamily index history

theorem canonical_codeMixture_dominates_coin :
    ∃ weight : ENNReal, weight ≠ 0 ∧
      Dominates
        (xiKpfSemimeasure (U := ReferenceMachine.canonical) binaryCodeFamily)
        coinMeasure weight := by
  obtain ⟨code, codeProduces⟩ := HutterV3Kpf.codesFor_nonempty coinMeasure coin_lsc
  change HutterEnumerationTheoremSemimeasure.evalLSC code =
    coinMeasure.toSemimeasure at codeProduces
  let index := binaryBits (Nat.Partrec.Code.encodeCode code)
  have component : binaryCodeFamily index = coinMeasure.toSemimeasure :=
    (binaryCodeFamily_at_code code).trans codeProduces
  refine ⟨kpfWeight (U := ReferenceMachine.canonical) index,
    (canonical_weight_pos index).ne', ?_⟩
  intro history
  have bound := canonical_component_dominance index history
  simpa only [component, PrefixMeasure.toSemimeasure_apply] using bound

theorem canonical_favoured_codeMixtures_comparable :
    ∃ c : Nat, ∀ history : BinString,
      (2 : ENNReal) ^ (-(c : Int)) *
          xiKpfSemimeasure (U := favouredReference) binaryCodeFamily history ≤
        xiKpfSemimeasure (U := ReferenceMachine.canonical) binaryCodeFamily history :=
  xiKpfSemimeasure_mul_le_of_invariance
    ReferenceMachine.canonical favouredReference binaryCodeFamily

theorem canonical_M₃_dominates_coin :
    Dominates (HutterV3Kpf.M₃ (U := ReferenceMachine.canonical)) coinMeasure
      ((2 : ENNReal) ^ (-(HutterV3Kpf.Kμ (U := ReferenceMachine.canonical) coinMeasure : Int))) :=
  HutterV3Kpf.dominates_M₃_of_LSC_Kμ ReferenceMachine.canonical coinMeasure coin_lsc

theorem canonical_M₃_coin_weight_pos :
    0 < (2 : ENNReal) ^
      (-(HutterV3Kpf.Kμ (U := ReferenceMachine.canonical) coinMeasure : Int)) :=
  ENNReal.zpow_pos (by norm_num) (by simp) _

theorem canonical_M₃_coin_entropy_bound (horizon : Nat) :
    FiniteHorizon.relEntropy coinMeasure
        (HutterV3Kpf.M₃ (U := ReferenceMachine.canonical)) horizon ≤
      (HutterV3Kpf.Kμ (U := ReferenceMachine.canonical) coinMeasure : ℝ) * Real.log 2 :=
  HutterV3Kpf.relEntropy_le_Kμ_log2 ReferenceMachine.canonical coinMeasure coin_lsc horizon

theorem canonical_favoured_coinComplexities_comparable :
    ∃ c : Nat,
      HutterV3Kpf.Kμ (U := ReferenceMachine.canonical) coinMeasure ≤
          HutterV3Kpf.Kμ (U := favouredReference) coinMeasure + c ∧
        HutterV3Kpf.Kμ (U := favouredReference) coinMeasure ≤
          HutterV3Kpf.Kμ (U := ReferenceMachine.canonical) coinMeasure + c := by
  obtain ⟨c, bound⟩ := HutterV3Kpf.invariance_Kμ ReferenceMachine.canonical favouredReference
  exact ⟨c, bound coinMeasure coin_lsc⟩

theorem canonical_no_unrestrictedSimulation :
    ¬ (∀ machine : SolomonoffPrior.PrefixFreeMachine, ∃ c : Nat, ∀ program output,
      machine.compute program = some output → ∃ translated,
        (ReferenceMachine.canonical : SolomonoffPrior.PrefixFreeMachine).compute translated =
            some output ∧ translated.length ≤ program.length + c) :=
  UniversalMachineBoundary.no_unrestrictedSimulation ReferenceMachine.canonical

theorem fixedEmpty_not_reference : ¬ IsReferenceMachine fixedEmptyMachine :=
  fixedEmptyMachine_not_reference

theorem fixedEmpty_missing_outputCompleteness :
    ¬ OutputComplete (conditionalSlice fixedEmptyMachine []) :=
  fixedEmptySlice_not_outputComplete

/-- Without output completeness, the zero convention for missing outputs
invalidates even a two-output Kraft claim. -/
theorem fixedEmpty_twoOutputKraft_exceeds_one :
    1 < ∑ output ∈ ({[false], [true]} : Finset BinString),
      (2 : ENNReal) ^ (-(Kpf[conditionalSlice fixedEmptyMachine []](output) : Int)) := by
  have missing (bit : Bool) : ¬ HasProgram fixedEmptyMachine [] [bit] := by
    rintro ⟨program, computes⟩
    simp [IsProgram, fixedEmptyMachine] at computes
  have complexityZero (bit : Bool) :
      Kpf[conditionalSlice fixedEmptyMachine []]([bit]) = 0 := by
    rw [← conditionalComplexity_eq_prefixComplexity_slice]
    exact conditionalComplexity_eq_zero_of_not_hasProgram
      fixedEmptyMachine [] [bit] (missing bit)
  norm_num [complexityZero]

#print axioms canonical_hasProgram
#print axioms canonical_allOutputKraft
#print axioms canonical_conditionalKraft
#print axioms favoured_complexity_strict
#print axioms canonical_cannot_translate_favoured_at_zero
#print axioms canonical_favoured_invariance
#print axioms canonical_favoured_simplicity_bound
#print axioms coin_lsc
#print axioms canonical_component_dominance
#print axioms canonical_codeMixture_dominates_coin
#print axioms canonical_favoured_codeMixtures_comparable
#print axioms canonical_M₃_dominates_coin
#print axioms canonical_M₃_coin_entropy_bound
#print axioms canonical_favoured_coinComplexities_comparable
#print axioms canonical_no_unrestrictedSimulation
#print axioms fixedEmpty_not_reference
#print axioms fixedEmpty_twoOutputKraft_exceeds_one

end Mettapedia.UniversalAI.ReferenceMachineControls
