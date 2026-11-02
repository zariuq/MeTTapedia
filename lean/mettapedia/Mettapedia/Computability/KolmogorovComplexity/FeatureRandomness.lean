import Mettapedia.Computability.KolmogorovComplexity.FeatureResidualSearch
import Mettapedia.Computability.FiniteBitStrings

/-!
# Finite-string randomness tests induced by compressive features

Franz, Antonenko and Soletskyi, "A theory of incremental compression",
Information Sciences 547 (2021), Section 5, doi:10.1016/j.ins.2020.08.035.
The separate ic-theory Theorem51 development informed the statement audit;
the interpreter, computability and binary enumeration here are shared ones.

The level bound is written as `2^m * card ≤ 2^n`, with natural powers and no
truncated exponent. Thus a level above the source length must be empty. This
is the paper's finite-string test, not an infinite-sequence measure-space
definition. The evaluator parameter below is a bounded computation stage,
not elapsed machine time. No shortest-feature hypothesis is needed.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FeatureTheory.Randomness

open Mettapedia.UniversalAI.TimeBoundedAIXI
open FiniteBitStrings
open scoped Classical BigOperators

def LowerSemicomputable (value : BinString → Nat) : Prop :=
  ∃ approximation : Nat → BinString → Nat,
    Computable₂ approximation ∧
    (∀ source, Monotone (fun stage => approximation stage source)) ∧
    ∀ source, ∃ settled, ∀ stage, settled ≤ stage → approximation stage source = value source

def level (value : BinString → Nat) (length threshold : Nat) : Finset BinString :=
  (bitstringsOfLength length).toFinset.filter (fun source => threshold ≤ value source)

theorem mem_level (value : BinString → Nat) (length threshold : Nat) (source : BinString) :
    source ∈ level value length threshold ↔ source.length = length ∧ threshold ≤ value source := by
  simp only [level, Finset.mem_filter, List.mem_toFinset]
  constructor
  · rintro ⟨member, high⟩
    exact ⟨length_eq_of_mem_bitstringsOfLength member, high⟩
  · rintro ⟨same, high⟩
    exact ⟨same ▸ mem_bitstringsOfLength_self source, high⟩

structure UniformTest (value : BinString → Nat) : Prop where
  lowerSemicomputable : LowerSemicomputable value
  levelBound : ∀ length threshold, 2 ^ threshold * (level value length threshold).card ≤ 2 ^ length

theorem UniformTest.empty_above_length {value : BinString → Nat} (test : UniformTest value)
    (length threshold : Nat) (above : length < threshold) : level value length threshold = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro source member
  have positive : 1 ≤ (level value length threshold).card := Finset.one_le_card.mpr ⟨source, member⟩
  have powers : (2 : Nat) ^ length < 2 ^ threshold := pow_lt_pow_right₀ (by decide) above
  have counted := test.levelBound length threshold
  nlinarith [Nat.two_pow_pos threshold]

theorem UniformTest.length_ge_of_high {value : BinString → Nat} (test : UniformTest value)
    (source : BinString) (threshold : Nat) (high : threshold ≤ value source) : threshold ≤ source.length := by
  by_contra notSmall
  have empty := test.empty_above_length source.length threshold (by omega)
  have present := (mem_level value source.length threshold source).mpr ⟨rfl, high⟩
  simp [empty] at present

theorem UniformTest.unscaled_bound {value : BinString → Nat} (test : UniformTest value)
    (length threshold : Nat) : (level value length threshold).card ≤ 2 ^ (length - threshold) := by
  by_cases bounded : threshold ≤ length
  · have power : (2 : Nat) ^ length = 2 ^ threshold * 2 ^ (length - threshold) := by
      rw [← pow_add, Nat.add_sub_of_le bounded]
    have counted := test.levelBound length threshold
    rw [power] at counted
    exact Nat.le_of_mul_le_mul_left counted (Nat.two_pow_pos threshold)
  · rw [test.empty_above_length length threshold (by omega)]
    simp

/-- The two natural-number conditions used in the independent ic-theory
test interface are together equivalent to the untruncated density bound.
The empty-level clause is essential, not an extra restriction of the paper. -/
theorem uniformTest_iff_natural_bounds (value : BinString → Nat) :
    UniformTest value ↔ LowerSemicomputable value ∧
      (∀ length threshold, (level value length threshold).card ≤ 2 ^ (length - threshold)) ∧
      (∀ length threshold, length < threshold → level value length threshold = ∅) := by
  constructor
  · intro test
    exact ⟨test.lowerSemicomputable, test.unscaled_bound, test.empty_above_length⟩
  · rintro ⟨lower, bounded, empty⟩
    refine ⟨lower, fun length threshold => ?_⟩
    by_cases small : threshold ≤ length
    · have multiplied := Nat.mul_le_mul_left (2 ^ threshold) (bounded length threshold)
      simpa only [← pow_add, Nat.add_sub_of_le small] using multiplied
    · simp [empty length threshold (by omega)]

def maxOver {α : Type} (items : List α) (value : α → Nat) : Nat := (items.map value).foldr max 0

theorem maxOver_mono {α : Type} (items : List α) (first second : α → Nat)
    (bounded : ∀ item ∈ items, first item ≤ second item) : maxOver items first ≤ maxOver items second := by
  induction items with
  | nil => exact le_rfl
  | cons item rest ih =>
      exact max_le_max (bounded item (by simp)) (ih (by intro later member; exact bounded later (by simp [member])))

theorem maxOver_le {α : Type} (items : List α) (value : α → Nat) (bound : Nat)
    (bounded : ∀ item ∈ items, value item ≤ bound) : maxOver items value ≤ bound := by
  induction items with
  | nil => exact Nat.zero_le _
  | cons item rest ih =>
      exact max_le (bounded item (by simp)) (ih (by intro later member; exact bounded later (by simp [member])))

theorem le_maxOver_of_mem {α : Type} (items : List α) (value : α → Nat) (item : α) (member : item ∈ items) :
    value item ≤ maxOver items value := by
  induction items with
  | nil => simp at member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact le_max_left _ _
      · exact (ih later).trans (le_max_right _ _)

theorem exists_mem_of_le_maxOver {α : Type} (items : List α) (value : α → Nat) (threshold : Nat)
    (positive : 0 < threshold) (high : threshold ≤ maxOver items value) :
    ∃ item ∈ items, threshold ≤ value item := by
  induction items with
  | nil => simp [maxOver] at high; omega
  | cons item rest ih =>
      change threshold ≤ max (value item) (maxOver rest value) at high
      rcases le_max_iff.mp high with first | later
      · exact ⟨item, by simp, first⟩
      · obtain ⟨other, member, bound⟩ := ih later
        exact ⟨other, by simp [member], bound⟩

noncomputable def score (U : ConditionalAlgorithm) (feature source residual : BinString) : Nat :=
  if feature.length + residual.length < source.length ∧ source ∈ U feature residual
  then source.length - residual.length - 1 else 0

noncomputable def deficiency (U : ConditionalAlgorithm) (feature source : BinString) : Nat :=
  maxOver (bitstringsUpTo source.length) (score U feature source)

theorem score_of_positive {U : ConditionalAlgorithm} {feature source residual : BinString} {threshold : Nat}
    (positive : 0 < threshold) (high : threshold ≤ score U feature source residual) :
    feature.length + residual.length < source.length ∧ source ∈ U feature residual ∧
      threshold + residual.length + 1 ≤ source.length := by
  unfold score at high
  split_ifs at high with valid
  · exact ⟨valid.1, valid.2, by omega⟩
  · omega

theorem residual_of_positive {U : ConditionalAlgorithm} {feature source : BinString} {threshold : Nat}
    (positive : 0 < threshold) (high : threshold ≤ deficiency U feature source) :
    ∃ residual, feature.length + residual.length < source.length ∧ source ∈ U feature residual ∧
      threshold + residual.length + 1 ≤ source.length := by
  obtain ⟨residual, _member, bounded⟩ := exists_mem_of_le_maxOver _ _ threshold positive high
  exact ⟨residual, score_of_positive positive bounded⟩

theorem deficiency_ge_of_reconstruction {U : ConditionalAlgorithm} {feature source residual : BinString}
    (reconstructs : source ∈ U feature residual) (shorter : feature.length + residual.length < source.length) :
    source.length - residual.length - 1 ≤ deficiency U feature source := by
  have member := mem_bitstringsUpTo_of_length_le (show residual.length ≤ source.length by omega)
  have bounded := le_maxOver_of_mem (bitstringsUpTo source.length) (score U feature source) residual member
  change source.length - residual.length - 1 ≤ maxOver _ _
  simpa only [score, if_pos (And.intro shorter reconstructs)] using bounded

theorem deficiency_le_length (U : ConditionalAlgorithm) (feature source : BinString) :
    deficiency U feature source ≤ source.length := by
  apply maxOver_le
  intro residual _member
  unfold score
  split_ifs <;> omega

theorem deficiency_le_pred_length (U : ConditionalAlgorithm) (feature source : BinString) :
    deficiency U feature source ≤ source.length - 1 := by
  apply maxOver_le
  intro residual _member
  unfold score
  split_ifs <;> omega

theorem deficiency_zero_of_no_compression (U : ConditionalAlgorithm) (feature source : BinString)
    (absent : ∀ residual, ¬(feature.length + residual.length < source.length ∧ source ∈ U feature residual)) :
    deficiency U feature source = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply maxOver_le
  intro residual _member
  simp only [score, if_neg (absent residual), le_refl]

theorem positive_level_card_lt (U : ConditionalAlgorithm) (feature : BinString) (length threshold : Nat)
    (positive : 0 < threshold) : (level (deficiency U feature) length threshold).card < 2 ^ (length - threshold) := by
  let outputs := level (deficiency U feature) length threshold
  have witness : ∀ output : outputs, ∃ residual : BinString,
      residual.length < length - threshold ∧ output.val ∈ U feature residual := by
    intro output
    obtain ⟨sameLength, high⟩ := (mem_level _ _ _ _).mp output.property
    obtain ⟨residual, _shorter, runs, saving⟩ := residual_of_positive positive high
    exact ⟨residual, by omega, runs⟩
  choose residual bounded runs using witness
  let Programs := Σ width : Fin (length - threshold), List.Vector Bool width.val
  let encoding : outputs → Programs := fun output =>
    ⟨⟨(residual output).length, bounded output⟩, ⟨residual output, rfl⟩⟩
  have injective : Function.Injective encoding := by
    intro first second same
    have sameResidual : residual first = residual second := congrArg (fun program : Programs => program.2.val) same
    have secondRun := runs second
    rw [← sameResidual] at secondRun
    exact Subtype.ext (Part.mem_unique (runs first) secondRun)
  have counted := Fintype.card_le_of_injective encoding injective
  have programCount : Fintype.card Programs < 2 ^ (length - threshold) := by
    have summed : (∑ width ∈ Finset.range (length - threshold), (2 : Nat) ^ width) < 2 ^ (length - threshold) :=
      Nat.geomSum_lt (by decide) (fun width member => Finset.mem_range.mp member)
    simpa [Programs, Fintype.card_sigma, card_vector, Fin.sum_univ_eq_sum_range] using summed
  have outputCount : outputs.card ≤ Fintype.card Programs := by simpa using counted
  exact outputCount.trans_lt programCount

theorem deficiency_level_bound (U : ConditionalAlgorithm) (feature : BinString) (length threshold : Nat) :
    2 ^ threshold * (level (deficiency U feature) length threshold).card ≤ 2 ^ length := by
  by_cases zero : threshold = 0
  · subst threshold
    simp only [level, Nat.zero_le, Finset.filter_true, pow_zero, one_mul]
    rw [List.toFinset_card_of_nodup (bitstringsOfLength_nodup length), bitstringsOfLength_length]
  · by_cases small : threshold ≤ length
    · have counted := (positive_level_card_lt U feature length threshold (by omega)).le
      have multiplied := Nat.mul_le_mul_left (2 ^ threshold) counted
      simpa only [← pow_add, Nat.add_sub_of_le small] using multiplied
    · have empty : level (deficiency U feature) length threshold = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro source member
        obtain ⟨same, high⟩ := (mem_level _ _ _ _).mp member
        have limit := deficiency_le_length U feature source
        omega
      simp [empty]

abbrev ApproximationInput := (Nat × BinString) × BinString

def boundedScore (code : Nat.Partrec.Code) (stage : Nat) (feature source residual : BinString) : Nat :=
  if feature.length + residual.length < source.length ∧
      Nat.Partrec.Code.evaln stage code (Encodable.encode (feature, residual)) = some (Encodable.encode source)
  then source.length - residual.length - 1 else 0

def approximation (code : Nat.Partrec.Code) (stage : Nat) (feature source : BinString) : Nat :=
  maxOver (bitstringsUpTo source.length) (boundedScore code stage feature source)

theorem boundedScore_primrec (code : Nat.Partrec.Code) : Primrec fun input : ApproximationInput × BinString =>
    boundedScore code input.1.1.1 input.1.1.2 input.1.2 input.2 := by
  have stage : Primrec fun input : ApproximationInput × BinString => input.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have feature : Primrec fun input : ApproximationInput × BinString => input.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have source : Primrec fun input : ApproximationInput × BinString => input.1.2 :=
    Primrec.snd.comp Primrec.fst
  have evaluates := Nat.Partrec.Code.primrec_evaln.comp
    ((stage.pair (Primrec.const code)).pair (Primrec.encode.comp (feature.pair Primrec.snd)))
  have fits : PrimrecPred fun input : ApproximationInput × BinString =>
      input.1.1.2.length + input.2.length < input.1.2.length :=
    Primrec.nat_lt.comp
      (Primrec.nat_add.comp (Primrec.list_length.comp feature) (Primrec.list_length.comp Primrec.snd))
      (Primrec.list_length.comp source)
  have computes : PrimrecPred fun input : ApproximationInput × BinString =>
      Nat.Partrec.Code.evaln input.1.1.1 code (Encodable.encode (input.1.1.2, input.2)) =
        some (Encodable.encode input.1.2) :=
    Primrec.eq.comp evaluates (Primrec.option_some.comp (Primrec.encode.comp source))
  exact Primrec.ite (fits.and computes)
    (Primrec.nat_sub.comp
      (Primrec.nat_sub.comp (Primrec.list_length.comp source) (Primrec.list_length.comp Primrec.snd))
      (Primrec.const 1)) (Primrec.const 0)

theorem approximation_primrec (code : Nat.Partrec.Code) : Primrec fun input : ApproximationInput =>
    approximation code input.1.1 input.1.2 input.2 := by
  have candidates : Primrec fun input : ApproximationInput => bitstringsUpTo input.2.length :=
    bitstringsUpTo_primrec.comp (Primrec.list_length.comp Primrec.snd)
  have scored : Primrec fun input : ApproximationInput × (BinString × Nat) =>
      boundedScore code input.1.1.1 input.1.1.2 input.1.2 input.2.1 :=
    (boundedScore_primrec code).comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))
  have step : Primrec₂ fun (input : ApproximationInput) (state : BinString × Nat) =>
      max (boundedScore code input.1.1 input.1.2 input.2 state.1) state.2 :=
    (Primrec.nat_max.comp scored (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr candidates (Primrec.const 0) step).of_eq
    (fun input => by simp [approximation, maxOver, List.foldr_map])

theorem boundedScore_mono (code : Nat.Partrec.Code) (feature source residual : BinString) :
    Monotone (fun stage => boundedScore code stage feature source residual) := by
  intro before after later
  unfold boundedScore
  by_cases fits : feature.length + residual.length < source.length
  · by_cases found : Nat.Partrec.Code.evaln before code (Encodable.encode (feature, residual)) =
        some (Encodable.encode source)
    · have kept := Nat.Partrec.Code.evaln_mono later
        (show Encodable.encode source ∈ Nat.Partrec.Code.evaln before code (Encodable.encode (feature, residual)) from
          by simpa only [Option.mem_def] using found)
      have kept' := Option.mem_def.mp kept
      simp only [fits, true_and, found, kept', ite_true, le_refl]
    · simp only [fits, true_and, found, ite_false, Nat.zero_le]
  · simp only [fits, false_and, ite_false, le_refl]

theorem boundedScore_eventually_eq {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U) (feature source residual : BinString) :
    ∃ settled, ∀ stage, settled ≤ stage → boundedScore code stage feature source residual = score U feature source residual := by
  by_cases fits : feature.length + residual.length < source.length
  · by_cases reconstructs : source ∈ U feature residual
    · have computes : Encodable.encode source ∈ Nat.Partrec.Code.eval code (Encodable.encode (feature, residual)) := by
        rw [codeSpec]
        simpa [encodedConditionalAlgorithm] using Part.mem_map Encodable.encode reconstructs
      obtain ⟨settled, found⟩ := Nat.Partrec.Code.evaln_complete.mp computes
      refine ⟨settled, fun stage later => ?_⟩
      have kept := Nat.Partrec.Code.evaln_mono later found
      simp only [boundedScore, score, fits, reconstructs, true_and, Option.mem_def.mp kept, ite_true]
    · refine ⟨0, fun stage _later => ?_⟩
      have notFound : Nat.Partrec.Code.evaln stage code (Encodable.encode (feature, residual)) ≠
          some (Encodable.encode source) := by
        intro found
        have runs := Nat.Partrec.Code.evaln_sound (show Encodable.encode source ∈
          Nat.Partrec.Code.evaln stage code (Encodable.encode (feature, residual)) from by simpa only [Option.mem_def] using found)
        rw [codeSpec] at runs
        have actual : source ∈ U feature residual := by simpa [encodedConditionalAlgorithm] using runs
        exact reconstructs actual
      simp only [boundedScore, score, fits, reconstructs, notFound, true_and, ite_false]
  · exact ⟨0, fun stage _later => by simp only [boundedScore, score, fits, false_and, ite_false]⟩

theorem maxOver_eventually_eq {α : Type} (items : List α) (approximates : Nat → α → Nat) (value : α → Nat)
    (settles : ∀ item ∈ items, ∃ settled, ∀ stage, settled ≤ stage → approximates stage item = value item) :
    ∃ settled, ∀ stage, settled ≤ stage → maxOver items (approximates stage) = maxOver items value := by
  induction items with
  | nil => exact ⟨0, fun _ _ => rfl⟩
  | cons item rest ih =>
      obtain ⟨firstTime, first⟩ := settles item (by simp)
      obtain ⟨laterTime, later⟩ := ih (by intro other member; exact settles other (by simp [member]))
      refine ⟨max firstTime laterTime, fun stage large => ?_⟩
      change max (approximates stage item) (maxOver rest (approximates stage)) = max (value item) (maxOver rest value)
      rw [first stage ((le_max_left _ _).trans large), later stage ((le_max_right _ _).trans large)]

theorem approximation_mono (code : Nat.Partrec.Code) (feature source : BinString) :
    Monotone (fun stage => approximation code stage feature source) := by
  intro before after later
  exact maxOver_mono _ _ _ (by intro residual _member; exact boundedScore_mono code feature source residual later)

theorem approximation_eventually_eq {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U) (feature source : BinString) :
    ∃ settled, ∀ stage, settled ≤ stage → approximation code stage feature source = deficiency U feature source :=
  maxOver_eventually_eq _ _ _ (by intro residual _member; exact boundedScore_eventually_eq codeSpec feature source residual)

theorem deficiency_lowerSemicomputable {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U) (feature : BinString) :
    LowerSemicomputable (deficiency U feature) := by
  have inputs : Primrec fun input : Nat × BinString => ((input.1, feature), input.2) :=
    (Primrec.fst.pair (Primrec.const feature)).pair Primrec.snd
  refine ⟨fun stage source => approximation code stage feature source,
    ((approximation_primrec code).comp inputs).to_comp, approximation_mono code feature, ?_⟩
  exact approximation_eventually_eq codeSpec feature

/-- IC Theorem 5.1 over the shared partial interpreter. One effective code
is fixed before all feature programs. The rarity bound does not require
universality, a prefix domain, ideal minima, or a feature existing elsewhere. -/
theorem feature_deficiencies_are_uniform_tests (U : ConditionalAlgorithm) (effective : Partrec₂ U) :
    ∀ feature, UniformTest (deficiency U feature) := by
  obtain ⟨code, codeSpec⟩ := exists_conditional_algorithm_code effective
  intro feature
  exact ⟨deficiency_lowerSemicomputable codeSpec feature, deficiency_level_bound U feature⟩

end KolmogorovComplexity.FeatureTheory.Randomness
