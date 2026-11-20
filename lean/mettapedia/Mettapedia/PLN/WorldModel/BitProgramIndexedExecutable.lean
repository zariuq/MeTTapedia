import Mettapedia.PLN.WorldModel.BitProgramObservationLedger

/-!
# Finite evaluation of indexed stream evidence

An indexed history is resolved into the disjoint output prefixes that
answer its largest indicated position. Its finite evaluator adds the
existing fair-tape counts for those prefixes. A run only needs to reach
the positions actually mentioned in the evidence.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.BitProgramObservationLedger

open Filter MeasureTheory
open scoped ENNReal BigOperators
open Mettapedia.UniversalAI.UniversalPrediction.BitProgramJointLaw
open Mettapedia.UniversalAI.UniversalPrediction.BitProgramMixture
open Mettapedia.UniversalAI.TimeBoundedAIXI
  (bitstringsOfLength mem_bitstringsOfLength_self length_eq_of_mem_bitstringsOfLength)
open KolmogorovComplexity.FiniteBitStrings (bitstringsOfLength_nodup)

def horizon : List Report → Nat
  | [] => 0
  | report :: history => max (report.1 + 1) (horizon history)

theorem position_lt_horizon {report : Report} {history : List Report}
    (present : report ∈ history) : report.1 < horizon history := by
  induction history with
  | nil => cases present
  | cons first rest ih =>
    rcases List.mem_cons.mp present with rfl | later
    · exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
    · exact lt_of_lt_of_le (ih later) (le_max_right _ _)

private theorem exists_observed_word (history : List Report) (world : World)
    (consistent : world ∈ compatible history) :
    ∃ word, word.length = horizon history ∧ world ∈ observed word := by
  induction history with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons report history ih =>
    obtain ⟨word, seen⟩ := Set.mem_iUnion.mp consistent.1
    obtain ⟨past, length, witnessed⟩ := ih consistent.2
    by_cases within : horizon history ≤ report.1 + 1
    · refine ⟨word.val ++ [report.2], ?_, seen⟩
      simp [horizon, max_eq_left within, word.property]
    · exact ⟨past, length.trans (max_eq_right (le_of_not_ge within)).symm, witnessed⟩

private theorem emission_of_observed {word : List Bool} {world : World} {i : Nat}
    (within : i < word.length) (seen : world ∈ observed word) :
    world ∈ emission (i, word[i]) := by
  refine Set.mem_iUnion.mpr ⟨⟨word.take i, List.length_take_of_le within.le⟩, ?_⟩
  apply observed_mono _ seen
  rw [← List.take_succ_eq_append_getElem within]
  exact List.take_prefix _ _

private theorem emission_iff_get {word : List Bool} {world : World} {report : Report}
    (within : report.1 < word.length) (seen : world ∈ observed word) :
    world ∈ emission report ↔ word[report.1]? = some report.2 := by
  rcases report with ⟨i, b⟩
  have known := emission_of_observed within seen
  rw [List.getElem?_eq_getElem within, Option.some.injEq]
  constructor
  · intro reported
    by_contra different
    exact Set.disjoint_left.mp (emission_disjoint i different) known reported
  · intro same
    simpa only [same] using known

def matchingWords (history : List Report) : List (List Bool) :=
  (bitstringsOfLength (horizon history)).filter fun word =>
    history.all fun report => decide (word[report.1]? = some report.2)

theorem compatible_eq_union (history : List Report) :
    compatible history = ⋃ word ∈ (matchingWords history).toFinset, observed word := by
  ext world
  simp only [Set.mem_iUnion, List.mem_toFinset]
  constructor
  · intro consistent
    obtain ⟨word, length, seen⟩ := exists_observed_word history world consistent
    refine ⟨word, List.mem_filter.mpr ⟨?_, ?_⟩, seen⟩
    · simpa only [length] using mem_bitstringsOfLength_self word
    · rw [List.all_eq_true]
      intro report present
      have within : report.1 < word.length := length.symm ▸ position_lt_horizon present
      exact decide_eq_true ((emission_iff_get within seen).mp ((compatible_each _ _).mp consistent _ present))
  · rintro ⟨word, member, seen⟩
    obtain ⟨listed, agrees⟩ := List.mem_filter.mp member
    apply (compatible_each _ _).mpr
    intro report present
    have within : report.1 < word.length :=
      (length_eq_of_mem_bitstringsOfLength listed).symm ▸ position_lt_horizon present
    exact (emission_iff_get within seen).mpr
      (of_decide_eq_true (List.all_eq_true.mp agrees report present))

theorem evidence_mass (history : List Report) :
    worldPrior (compatible history) =
      ∑ word ∈ (matchingWords history).toFinset, mixture word := by
  have disjoint : Set.PairwiseDisjoint (↑(matchingWords history).toFinset) observed := by
    intro first firstMem second secondMem distinct
    have length (word : List Bool) (inside : word ∈ (matchingWords history).toFinset) :
        word.length = horizon history :=
      length_eq_of_mem_bitstringsOfLength (List.mem_filter.mp (List.mem_toFinset.mp inside)).1
    exact observed_disjoint ((length first firstMem).trans (length second secondMem).symm) distinct
  rw [compatible_eq_union, measure_biUnion_finset disjoint (fun word _ => measurable_observed word)]
  simp only [observed_mass]

def evidenceMassAt (history : List Report) (stage : Nat) : ℚ :=
  ((matchingWords history).map fun word => stageMass word stage).sum

theorem evidenceMassAt_mono (history : List Report) : Monotone (evidenceMassAt history) := by
  intro first later order
  have ordered (words : List (List Bool)) :
      (words.map fun word => stageMass word first).sum ≤
        (words.map fun word => stageMass word later).sum := by
    induction words with
    | nil => exact le_rfl
    | cons word words ih =>
      simpa only [List.map_cons, List.sum_cons] using add_le_add (stageMass_mono word order) ih
  exact ordered (matchingWords history)

private theorem list_sum_toFinset {R : Type*} [AddCommMonoid R] (f : List Bool → R)
    (words : List (List Bool)) (unique : words.Nodup) :
    ∑ word ∈ words.toFinset, f word = (words.map f).sum := by
  induction words with
  | nil => simp
  | cons word words ih =>
    rw [List.toFinset_cons, Finset.sum_insert (by simpa using (List.nodup_cons.mp unique).1),
      List.map_cons, List.sum_cons, ih (List.nodup_cons.mp unique).2]

theorem evidenceMassAt_tendsto (history : List Report) :
    Tendsto (fun stage => (evidenceMassAt history stage : ℝ)) atTop
      (nhds (worldPrior (compatible history)).toReal) := by
  have limit (words : List (List Bool)) :
      Tendsto (fun stage => (((words.map fun word => stageMass word stage).sum : ℚ) : ℝ)) atTop
        (nhds ((words.map fun word => (mixture word).toReal).sum)) := by
    induction words with
    | nil => simp
    | cons word words ih =>
      simpa only [List.map_cons, List.sum_cons, Rat.cast_add] using
        (stageMass_tendsto word).add ih
  have unique : (matchingWords history).Nodup := (bitstringsOfLength_nodup _).filter _
  rw [evidence_mass, ENNReal.toReal_sum (fun word _ => mixture.ne_top word),
    list_sum_toFinset _ _ unique]
  exact limit (matchingWords history)

theorem evidenceMassAt_le (history : List Report) (stage : Nat) :
    (evidenceMassAt history stage : ℝ) ≤ (worldPrior (compatible history)).toReal := by
  have ordered : Monotone (fun n => (evidenceMassAt history n : ℝ)) := by
    intro first later order
    change (evidenceMassAt history first : ℝ) ≤ (evidenceMassAt history later : ℝ)
    exact_mod_cast evidenceMassAt_mono history order
  exact ordered.ge_of_tendsto (evidenceMassAt_tendsto history) stage

def predictReportAt (history : List Report) (query : Report) (stage : Nat) : Option ℚ :=
  let total := evidenceMassAt history stage
  if total = 0 then none else some (evidenceMassAt (query :: history) stage / total)

theorem predictReportAt_tendsto (history : List Report) (query : Report)
    (positive : 0 < (worldPrior (compatible history)).toReal) :
    (∀ᶠ stage in atTop, (predictReportAt history query stage).isSome) ∧
    Tendsto (fun stage => ((predictReportAt history query stage).getD 0 : ℝ)) atTop
      (nhds ((worldPrior (compatible (query :: history))).toReal /
        (worldPrior (compatible history)).toReal)) := by
  have denominator := evidenceMassAt_tendsto history
  have ready : ∀ᶠ stage in atTop, evidenceMassAt history stage ≠ 0 :=
    ((tendsto_order.mp denominator).1 0 positive).mono fun stage supported zero => by
      simp [zero] at supported
  exact ⟨ready.mono (fun stage hn => by simp [predictReportAt, hn]),
    ((evidenceMassAt_tendsto (query :: history)).div denominator positive.ne').congr'
      (ready.mono (fun stage hn => by simp [predictReportAt, hn, Rat.cast_div]))⟩

/-! A second-position observation can answer a first-position query. -/
#guard predictReportAt [(1, false)] (0, false) 19 == some 1
#guard predictReportAt [(1, true), (1, false)] (0, false) 19 == none

end Mettapedia.PLN.WorldModel.BitProgramObservationLedger
