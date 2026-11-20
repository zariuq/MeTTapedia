import Mettapedia.Computability.EffectiveBitGenerator
import Mettapedia.UniversalAI.UniversalPrediction.BitGeneratorSemimeasure
import Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.SolomonoffBridge
import Mettapedia.Computability.HutterComputabilityClosure

/-!
# Solomonoff-style prediction indexed by probabilistic program codes

The entries are actual partial-recursive instructions with sequential fair
input. Every index participates, including codes that cannot produce output.
Their prior weights have unary prefix lengths. A finite stage distributes its
bit budget between the code description and the code's input, giving an
executable dyadic lower approximation to the mixture. The posterior and next
output are ratios of these masses at positive support.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAI.UniversalPrediction.BitProgramMixture

open Filter MeasureTheory Mettapedia.Computability Mettapedia.Computability.Hutter
open scoped ENNReal BigOperators
open Mettapedia.Computability.BitGenerator
open Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet
open Nat.Partrec (Code)

theorem stageMass_cast {State : Type*} (program : Generator State Bool)
    [DecidableEq State] (history : List Bool) (stage : Nat) :
    (program.stageMass history stage : ℝ) = dyadic (program.count history stage) stage := by
  simp [Generator.stageMass, dyadic, Rat.cast_div, Rat.cast_pow]

/-- Effectivity is uniform in the transition code, as well as in the
requested history. -/
theorem codeFamily_lowerSemicomputable :
    LowerSemicomputable (fun p : Code × List Bool =>
      ((codeGenerator p.1).semimeasure p.2).toReal) := by
  refine ⟨fun p n => (codeGenerator p.1).count p.2 n, code_count_computable, ?_, ?_⟩
  · intro p i j order
    change dyadic ((codeGenerator p.1).count p.2 i) i ≤ dyadic ((codeGenerator p.1).count p.2 j) j
    rw [← stageMass_cast, ← stageMass_cast]
    exact_mod_cast (codeGenerator p.1).stageMass_mono p.2 order
  · intro p
    simpa only [← stageMass_cast] using (codeGenerator p.1).toReal_stageMass_tendsto p.2

theorem program_lowerSemicomputable (code : Code) :
    FiniteAlphabet.LowerSemicomputableSemimeasure (codeGenerator code).semimeasure := by
  obtain ⟨approx, comp, mono, limit⟩ := codeFamily_lowerSemicomputable
  refine ⟨fun history stage => approx (code, history) stage, ?_,
    fun history => mono (code, history), fun history => limit (code, history)⟩
  exact (comp.comp ((Computable.const code).pair Computable.fst) Computable.snd).to₂

/-- The existing ideal mixture dominates the law of every actual program.
Its enumeration index is a code for the dyadic approximation witness. -/
theorem existingMixture_dominates (program : Code) :
    ∃ index : Code, Dominates (SolomonoffBridge.M₂ (α := Bool))
      (codeGenerator program).semimeasure (encodeWeight index) := by
  let enumeration := HutterEnumerationTheoremSemimeasure.lscSemimeasureEnumeration (α := Bool)
  obtain ⟨index, same⟩ := enumeration.surj_eval _ (program_lowerSemicomputable program)
  exact ⟨index, same ▸ enumeration.xi_dominates_eval index⟩

def programAt (index : Nat) : Generator Nat Bool := codeGenerator (Denumerable.ofNat Code index)

/-- Code `i` has a unary self-delimiting description of length `i + 1`. -/
noncomputable def descriptionWeight (index : Nat) : ℝ≥0∞ := (1 / 2) ^ (index + 1)

theorem descriptionWeight_ne_zero (index : Nat) : descriptionWeight index ≠ 0 := by
  unfold descriptionWeight
  exact pow_ne_zero _ (by norm_num)

theorem descriptionWeight_total : ∑' index : Nat, descriptionWeight index = 1 := by
  unfold descriptionWeight
  rw [ENNReal.tsum_geometric_add_one]
  have halfSub : (1 : ℝ≥0∞) - 1 / 2 = 1 / 2 := by norm_num
  rw [halfSub, ENNReal.mul_inv_cancel (by norm_num) (by finiteness)]

/-- Countable mixture directly indexed by programs that consume random bits. -/
noncomputable def mixture : FiniteAlphabet.Semimeasure Bool :=
  FiniteAlphabet.xiSemimeasure (fun index => (programAt index).semimeasure) descriptionWeight
    descriptionWeight_total.le

@[simp] theorem mixture_apply (history : List Bool) :
    mixture history = ∑' i : Nat, descriptionWeight i * (programAt i).semimeasure history := rfl

theorem dominates_programAt (index : Nat) :
    Dominates mixture (programAt index).semimeasure (descriptionWeight index) :=
  fun history => FiniteAlphabet.xi_dominates_index (fun i => (programAt i).semimeasure)
    descriptionWeight index history

theorem dominates_code (code : Code) :
    Dominates mixture (codeGenerator code).semimeasure (descriptionWeight (Encodable.encode code)) := by
  simpa only [programAt, Denumerable.ofNat_encode] using dominates_programAt (Encodable.encode code)

/-- The usual finite-horizon log-loss bound for any program whose output
law is a prefix probability measure. -/
theorem relEntropy_le_descriptionLength (code : Code) (truth : PrefixMeasure Bool)
    (semantics : truth.toSemimeasure = (codeGenerator code).semimeasure) (horizon : Nat) :
    FiniteAlphabet.FiniteHorizon.relEntropy truth mixture horizon ≤
      (Encodable.encode code + 1) * Real.log 2 := by
  have dominance : Dominates mixture truth (descriptionWeight (Encodable.encode code)) := by
    change Dominates mixture truth.toSemimeasure _
    rw [semantics]
    exact dominates_code code
  have bound := FiniteAlphabet.FiniteHorizon.relEntropy_le_log_inv_of_dominates
    truth mixture dominance (descriptionWeight_ne_zero _) horizon
  exact bound.trans_eq (by
    simpa only [descriptionWeight, encodeWeight, one_div] using
      SolomonoffBridge.log_inv_encodeWeight code)

private def literalStep (history : List Bool) (offset : Nat) : InstructionCode :=
  Option.casesOn history[offset]? (.inl offset) (fun bit => .inr (.inr (bit, offset + 1)))

private theorem literalStep_computable (history : List Bool) : Computable (literalStep history) := by
  exact Computable.option_casesOn
    (Computable.list_getElem?.comp (Computable.const history) Computable.id)
    Computable.sumInl
    ((Computable.sumInr.comp (Computable.sumInr.comp
      (Computable.snd.pair (Computable.succ.comp Computable.fst)))).to₂)

private theorem literalRun (history : List Bool) (code : Code)
    (realizes : ∀ offset, codeMeaning code offset = some (decodeInstruction (literalStep history offset)))
    (offset : Nat) (word : List Bool) (suffix : history.drop offset = word) :
    StreamingInput.Runs (monitor (codeMeaning code)) (offset, word) [] true [] := by
  induction word generalizing offset with
  | nil => exact .halt rfl
  | cons bit tail ih =>
    have head : history[offset]? = some bit := by
      have first : (history.drop offset)[0]? = (bit :: tail)[0]? :=
        congrArg (fun l : List Bool => l[0]?) suffix
      simpa only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] using first
    have rest : history.drop (offset + 1) = tail := by
      rw [← List.drop_drop, suffix]
      rfl
    have emission : codeMeaning code offset = some (.emit bit (offset + 1)) := by
      simpa [literalStep, head, decodeInstruction] using realizes offset
    exact .step (by simp [monitor, emission]) (ih (offset + 1) rest)

/-- Every history is emitted with certainty by some deterministic program. -/
theorem exists_code_emits (history : List Bool) :
    ∃ code : Code, (codeGenerator code).semimeasure history = 1 := by
  obtain ⟨code, realizes⟩ := code_realizes_computable _ (literalStep_computable history)
  have allTapes : (codeGenerator code).event history = Set.univ := by
    refine Set.eq_univ_of_forall fun tape => (code_event_iff_monitor code history tape).mpr ?_
    exact ⟨0, [], literalRun history code realizes 0 history List.drop_zero⟩
  exact ⟨code, by rw [Generator.semimeasure_apply, allTapes, measure_univ]⟩

theorem mixture_pos (history : List Bool) : 0 < (mixture history).toReal := by
  obtain ⟨code, emits⟩ := exists_code_emits history
  have contribution := dominates_code code history
  rw [emits, mul_one] at contribution
  apply ENNReal.toReal_pos _ (mixture.ne_top history)
  exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr (descriptionWeight_ne_zero _)) contribution)

/-- The cutoff accounts for the code prefix before counting its random
input. Every counted tape at this stage has the same overall length. -/
def stageNumerator (history : List Bool) (stage : Nat) : Nat :=
  sumRange (fun i => (programAt i).count history (stage - (i + 1))) stage

def stageMass (history : List Bool) (stage : Nat) : ℚ :=
  (stageNumerator history stage : ℚ) / (2 : ℚ) ^ stage

theorem stageNumerator_computable : Computable₂ stageNumerator := by
  let Input := List Bool × Nat
  let Loop := Input × (Nat × Nat)
  have index : Computable fun input : Loop => input.2.1 :=
    Computable.fst.comp Computable.snd
  have program : Computable fun input : Loop => Denumerable.ofNat Code input.2.1 :=
    (Primrec.ofNat Code).to_comp.comp index
  have history : Computable fun input : Loop => input.1.1 :=
    Computable.fst.comp Computable.fst
  have fuel : Computable fun input : Loop => input.1.2 - (input.2.1 + 1) :=
    Primrec.nat_sub.to_comp.comp (Computable.snd.comp Computable.fst)
      (Computable.succ.comp index)
  have count := code_count_computable.comp ((program.pair history).pair fuel)
  have add : Computable₂ fun (input : Input) (work : Nat × Nat) =>
      work.2 + (programAt work.1).count input.1 (input.2 - (work.1 + 1)) :=
    (Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd) count).to₂
  exact (Computable.nat_rec Computable.snd (Computable.const 0) add).of_eq (fun p =>
    congrFun (natRec_eq_sumRange (fun i => (programAt i).count p.1 (p.2 - (i + 1)))) p.2)

private noncomputable def realWeight (index : Nat) : ℝ := (1 / 2 : ℝ) ^ (index + 1)

private theorem realWeight_nonneg (index : Nat) : 0 ≤ realWeight index :=
  pow_nonneg (by norm_num) _

private theorem summable_realWeight : Summable realWeight :=
  summable_geometric_two.comp_injective Nat.succ_injective

private theorem descriptionWeight_toReal (index : Nat) :
    (descriptionWeight index).toReal = realWeight index := by
  simp [descriptionWeight, realWeight]

private theorem split_budget (count stage index : Nat) (within : index < stage) :
    dyadic count stage = realWeight index * dyadic count (stage - (index + 1)) := by
  unfold realWeight dyadic
  rw [div_pow, one_pow, div_mul_div_comm, one_mul, ← pow_add,
    Nat.add_sub_of_le (Nat.succ_le_of_lt within)]

private noncomputable def term (history : List Bool) (stage index : Nat) : ℝ :=
  if index < stage then
    realWeight index * ((programAt index).stageMass history (stage - (index + 1)) : ℝ)
  else 0

private theorem stage_eq_tsum (history : List Bool) (stage : Nat) :
    (stageMass history stage : ℝ) = ∑' index : Nat, term history stage index := by
  have cast : (stageMass history stage : ℝ) = dyadic (stageNumerator history stage) stage := by
    simp [stageMass, dyadic, Rat.cast_div, Rat.cast_pow]
  rw [cast, stageNumerator, dyadic_sumRange, tsum_eq_sum (s := Finset.range stage)]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have within := Finset.mem_range.mp hi
    rw [split_budget _ _ _ within, term, if_pos within, stageMass_cast]
  · intro i outside
    simp [term, (show ¬ i < stage from fun h => outside (Finset.mem_range.mpr h))]

private theorem stage_between (program : Generator Nat Bool) (history : List Bool) (stage : Nat) :
    0 ≤ (program.stageMass history stage : ℝ) ∧
      (program.stageMass history stage : ℝ) ≤ (program.semimeasure history).toReal := by
  have nonneg : 0 ≤ (program.stageMass history stage : ℝ) := by
    rw [stageMass_cast]
    exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)
  exact ⟨nonneg, by
    have upper := ENNReal.toReal_mono (program.semimeasure.ne_top history)
      (program.stageMass_le history stage)
    rwa [ENNReal.toReal_ofReal nonneg] at upper⟩

private theorem term_bound (history : List Bool) (stage index : Nat) :
    0 ≤ term history stage index ∧ term history stage index ≤ realWeight index := by
  by_cases within : index < stage
  · rw [term, if_pos within]
    have lo := stage_between (programAt index) history (stage - (index + 1))
    have hi := ENNReal.toReal_mono ENNReal.one_ne_top ((programAt index).semimeasure.le_one history)
    refine ⟨mul_nonneg (realWeight_nonneg index) lo.1, ?_⟩
    simpa using mul_le_mul_of_nonneg_left (lo.2.trans (hi.trans_eq ENNReal.toReal_one))
      (realWeight_nonneg index)
  · simp [term, within, realWeight_nonneg]

private theorem term_mono (history : List Bool) (index : Nat) :
    Monotone fun stage => term history stage index := by
  intro early later order
  by_cases within : index < early
  · simp only [term, if_pos within, if_pos (within.trans_le order)]
    apply mul_le_mul_of_nonneg_left _ (realWeight_nonneg index)
    exact_mod_cast (programAt index).stageMass_mono history (Nat.sub_le_sub_right order _)
  · simpa only [term, if_neg within] using (term_bound history later index).1

theorem stageMass_mono (history : List Bool) : Monotone (stageMass history) := by
  intro i j order
  have summable (stage : Nat) : Summable fun index => term history stage index :=
    Summable.of_nonneg_of_le (fun index => (term_bound history stage index).1)
      (fun index => (term_bound history stage index).2) summable_realWeight
  have ordered : (stageMass history i : ℝ) ≤ (stageMass history j : ℝ) := by
    rw [stage_eq_tsum, stage_eq_tsum]
    exact (summable i).tsum_le_tsum (fun index => term_mono history index order) (summable j)
  exact_mod_cast ordered

private theorem term_tendsto (history : List Bool) (index : Nat) :
    Tendsto (fun stage => term history stage index) atTop
      (nhds (realWeight index * ((programAt index).semimeasure history).toReal)) := by
  have shift : Tendsto (fun n : Nat => n - (index + 1)) atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop (k + (index + 1))] with n bound
    omega
  refine (tendsto_const_nhds.mul (((programAt index).toReal_stageMass_tendsto history).comp shift)).congr' ?_
  filter_upwards [eventually_ge_atTop (index + 1)] with n within
  simp [term, Nat.lt_of_succ_le within]

/-- The rational evaluator converges to the countable program mixture. -/
theorem stageMass_tendsto (history : List Bool) :
    Tendsto (fun stage => (stageMass history stage : ℝ)) atTop
      (nhds (mixture history).toReal) := by
  have limit := tendsto_tsum_of_dominated_convergence summable_realWeight (term_tendsto history)
    (Filter.Eventually.of_forall fun stage index => by
      rw [Real.norm_eq_abs, abs_of_nonneg (term_bound history stage index).1]
      exact (term_bound history stage index).2)
  have readout : (mixture history).toReal =
      ∑' index, realWeight index * ((programAt index).semimeasure history).toReal := by
    rw [mixture_apply]
    rw [ENNReal.tsum_toReal_eq]
    · simp only [ENNReal.toReal_mul, descriptionWeight_toReal]
    · intro index
      exact ENNReal.mul_ne_top (by simp [descriptionWeight])
        ((programAt index).semimeasure.ne_top history)
  simpa only [← stage_eq_tsum, ← readout] using limit

theorem mixture_lowerSemicomputable : FiniteAlphabet.LowerSemicomputableSemimeasure mixture := by
  have cast (history : List Bool) (stage : Nat) :
      (stageMass history stage : ℝ) = dyadic (stageNumerator history stage) stage := by
    simp [stageMass, dyadic, Rat.cast_div, Rat.cast_pow]
  refine ⟨stageNumerator, stageNumerator_computable, ?_, ?_⟩
  · intro h i j hij
    change dyadic (stageNumerator h i) i ≤ dyadic (stageNumerator h j) j
    rw [← cast, ← cast]
    exact_mod_cast stageMass_mono h hij
  · intro h
    simpa only [← cast] using stageMass_tendsto h

theorem existingMixture_dominates_mixture :
    ∃ index : Code, Dominates (SolomonoffBridge.M₂ (α := Bool)) mixture (encodeWeight index) := by
  let enumeration := HutterEnumerationTheoremSemimeasure.lscSemimeasureEnumeration (α := Bool)
  obtain ⟨index, same⟩ := enumeration.surj_eval _ mixture_lowerSemicomputable
  exact ⟨index, same ▸ enumeration.xi_dominates_eval index⟩

/-- Predict with the counted mass at this cutoff. The ratio may change when
later executions contribute. A zero denominator leaves the readout unresolved. -/
def predictAt (history : List Bool) (stage : Nat) (next : Bool) : Option ℚ :=
  let total := stageMass history stage
  if total = 0 then none else some (stageMass (history ++ [next]) stage / total)

theorem predictAt_tendsto (history : List Bool) (next : Bool) :
    (∀ᶠ stage in atTop, (predictAt history stage next).isSome) ∧
    Tendsto (fun stage => ((predictAt history stage next).getD 0 : ℝ)) atTop
      (nhds ((mixture (history ++ [next])).toReal / (mixture history).toReal)) := by
  have evidence := mixture_pos history
  have lim := stageMass_tendsto history
  have eventuallyPositive : ∀ᶠ stage in atTop, 0 < (stageMass history stage : ℝ) :=
    (tendsto_order.mp lim).1 0 evidence
  have ready : ∀ᶠ stage in atTop, stageMass history stage ≠ 0 :=
    eventuallyPositive.mono fun stage hp zero => by simp [zero] at hp
  exact ⟨ready.mono fun stage hn => by simp [predictAt, hn],
    ((stageMass_tendsto (history ++ [next])).div lim evidence.ne').congr'
      (ready.mono fun stage hn => by simp [predictAt, hn, Rat.cast_div])⟩

/-- A finite observation apportions the known mass between program indices.
An index outside the cutoff has zero weight in this approximation. -/
def posteriorAt (history : List Bool) (stage index : Nat) : Option ℚ :=
  let numerator := stageNumerator history stage
  if numerator = 0 then none
  else
    some (if index < stage then
      ((programAt index).count history (stage - (index + 1)) : ℚ) / (numerator : ℚ)
    else 0)

theorem posteriorAt_tendsto (history : List Bool) (index : Nat) :
    (∀ᶠ stage in atTop, (posteriorAt history stage index).isSome) ∧
    Tendsto (fun stage => ((posteriorAt history stage index).getD 0 : ℝ)) atTop
      (nhds ((descriptionWeight index * (programAt index).semimeasure history).toReal /
        (mixture history).toReal)) := by
  have evidence := mixture_pos history
  have lim := stageMass_tendsto history
  have ready : ∀ᶠ stage in atTop, stageNumerator history stage ≠ 0 :=
    ((tendsto_order.mp lim).1 0 evidence).mono fun stage positive zero => by
      simp [stageMass, zero] at positive
  refine ⟨ready.mono (fun stage hn => by simp [posteriorAt, hn]), ?_⟩
  rw [ENNReal.toReal_mul, descriptionWeight_toReal]
  refine ((term_tendsto history index).div lim evidence.ne').congr' ?_
  filter_upwards [ready, eventually_ge_atTop (index + 1)] with stage hn within
  have before : index < stage := Nat.lt_of_succ_le within
  change term history stage index / (stageMass history stage : ℝ) =
    ((posteriorAt history stage index).getD 0 : ℝ)
  rw [term, if_pos before, stageMass_cast, ← split_budget _ _ _ before]
  simp only [posteriorAt, if_neg hn, if_pos before, Option.getD_some,
    dyadic, stageMass, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat]
  exact div_div_div_cancel_right₀ (pow_ne_zero stage (by norm_num)) _ _

@[simp] theorem mixture_nil : mixture [] = 1 := by
  simpa only [mixture_apply, Generator.semimeasure_nil, mul_one] using descriptionWeight_total

end Mettapedia.UniversalAI.UniversalPrediction.BitProgramMixture
