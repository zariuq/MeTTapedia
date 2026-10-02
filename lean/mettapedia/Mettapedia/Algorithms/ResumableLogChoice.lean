import Mettapedia.Algorithms.CertifiedLogScore
import Mettapedia.Algorithms.ResumableComparison

/-!
# Refining and resuming certified logarithmic decisions

Each new rational series enclosure is intersected with the previous enclosure.
This gives nested intervals without assuming a numerical oracle or monotonic
raw approximations. The resumable checker validates its earlier comparisons
against these computed intervals. Strict finite score separation is eventually
resolved; overlapping intervals retain unresolved comparison work.
-/

namespace Mettapedia.Algorithms.ResumableLogChoice

open Finset
open ResumableComparison

variable {C I : Type*} [Fintype I]

noncomputable def score (weight argument : C → I → ℚ) (c : C) : ℝ :=
  ∑ i, (weight c i : ℝ) * Real.log (argument c i : ℝ)

def lower (weight argument : C → I → ℚ) (c : C) : ℕ → ℚ
  | 0 => CertifiedLogScore.approximation (weight c) (argument c) 0 -
      CertifiedLogScore.radius (weight c) (argument c) 0
  | n + 1 => max (lower weight argument c n)
      (CertifiedLogScore.approximation (weight c) (argument c) (n + 1) -
        CertifiedLogScore.radius (weight c) (argument c) (n + 1))

def upper (weight argument : C → I → ℚ) (c : C) : ℕ → ℚ
  | 0 => CertifiedLogScore.approximation (weight c) (argument c) 0 +
      CertifiedLogScore.radius (weight c) (argument c) 0
  | n + 1 => min (upper weight argument c n)
      (CertifiedLogScore.approximation (weight c) (argument c) (n + 1) +
        CertifiedLogScore.radius (weight c) (argument c) (n + 1))

theorem raw_encloses (weight argument : C → I → ℚ) (c : C)
    (positive : ∀ i, 0 < argument c i) (n : ℕ) :
    ((CertifiedLogScore.approximation (weight c) (argument c) n -
        CertifiedLogScore.radius (weight c) (argument c) n : ℚ) : ℝ) ≤ score weight argument c ∧
    score weight argument c ≤
      ((CertifiedLogScore.approximation (weight c) (argument c) n +
        CertifiedLogScore.radius (weight c) (argument c) n : ℚ) : ℝ) := by
  have bounds := abs_le.mp (CertifiedLogScore.enclosure (weight c) (argument c) positive n)
  unfold score
  push_cast
  constructor <;> linarith

theorem encloses (weight argument : C → I → ℚ) (c : C)
    (positive : ∀ i, 0 < argument c i) (n : ℕ) :
    (lower weight argument c n : ℝ) ≤ score weight argument c ∧
      score weight argument c ≤ (upper weight argument c n : ℝ) := by
  induction n with
  | zero => exact raw_encloses weight argument c positive 0
  | succ n ih =>
      have raw := raw_encloses weight argument c positive (n + 1)
      simp only [lower, upper, Rat.cast_max, Rat.cast_min]
      exact ⟨max_le ih.1 raw.1, le_min ih.2 raw.2⟩

theorem lower_monotone (weight argument : C → I → ℚ) (c : C) :
    Monotone (lower weight argument c) :=
  monotone_nat_of_le_succ (fun _ => le_max_left _ _)

theorem upper_antitone (weight argument : C → I → ℚ) (c : C) :
    Antitone (upper weight argument c) :=
  antitone_nat_of_succ_le (fun _ => min_le_left _ _)

theorem raw_lower_le (weight argument : C → I → ℚ) (c : C) (n : ℕ) :
    CertifiedLogScore.approximation (weight c) (argument c) n -
      CertifiedLogScore.radius (weight c) (argument c) n ≤ lower weight argument c n := by
  cases n with
  | zero => rfl
  | succ n => exact le_max_right _ _

theorem upper_le_raw (weight argument : C → I → ℚ) (c : C) (n : ℕ) :
    upper weight argument c n ≤ CertifiedLogScore.approximation (weight c) (argument c) n +
      CertifiedLogScore.radius (weight c) (argument c) n := by
  cases n with
  | zero => rfl
  | succ n => exact min_le_right _ _

variable [DecidableEq C]

omit [DecidableEq C] in
/-- Increasing the numerical budget preserves all previously validated comparisons. -/
theorem valid_refines (all : List C) (weight argument : C → I → ℚ) (selected : C)
    (receipt : Receipt C) {old new : ℕ} (larger : old ≤ new)
    (valid : Valid all (fun c => lower weight argument c old)
      (fun c => upper weight argument c old) selected receipt) :
    Valid all (fun c => lower weight argument c new)
      (fun c => upper weight argument c new) selected receipt := by
  refine ⟨valid.1, valid.2.1, ?_⟩
  intro c member
  rcases valid.2.2 c member with same | ordered
  · exact Or.inl same
  · exact Or.inr ((upper_antitone weight argument c larger).trans
      (ordered.trans (lower_monotone weight argument selected larger)))

/-- Both numerical and comparison budgets are ordinary data. -/
def resume (all : List C) (weight argument : C → I → ℚ) (selected : C)
    (terms comparisonBudget : ℕ) (receipt : Receipt C) : Option (Receipt C) :=
  if (∀ c ∈ all, ∀ i, 0 < argument c i) then
    ResumableComparison.resume all (fun c => lower weight argument c terms)
      (fun c => upper weight argument c terms) selected comparisonBudget receipt
  else none

theorem completed_sound (all : List C) (weight argument : C → I → ℚ) (selected : C)
    (terms comparisonBudget : ℕ) (receipt output : Receipt C)
    (accepted : resume all weight argument selected terms comparisonBudget receipt = some output)
    (complete : output.pending = []) :
    selected ∈ all ∧ ∀ c ∈ all, score weight argument c ≤ score weight argument selected := by
  unfold resume at accepted
  split_ifs at accepted with positive
  exact ResumableComparison.completed_sound all _ _ selected comparisonBudget receipt output
    (score weight argument) (fun c member => encloses weight argument c (positive c member) terms)
    accepted complete

omit [DecidableEq C] in
/-- A strict score gap eventually separates the certified intervals. -/
theorem eventually_separates (weight argument : C → I → ℚ) (selected c : C)
    (positiveSelected : ∀ i, 0 < argument selected i)
    (positiveC : ∀ i, 0 < argument c i)
    (better : score weight argument c < score weight argument selected) :
    ∀ᶠ n : ℕ in Filter.atTop, upper weight argument c n ≤ lower weight argument selected n := by
  let tolerance := (score weight argument selected - score weight argument c) / 8
  have positive : 0 < tolerance := by dsimp [tolerance]; linarith
  have smallC := CertifiedLogScore.radius_eventually_small (weight c) (argument c)
    positiveC tolerance positive
  have smallSelected := CertifiedLogScore.radius_eventually_small (weight selected)
    (argument selected) positiveSelected tolerance positive
  filter_upwards [smallC, smallSelected] with n hc hs
  have cBound := abs_le.mp (CertifiedLogScore.enclosure (weight c) (argument c) positiveC n)
  have sBound := abs_le.mp
    (CertifiedLogScore.enclosure (weight selected) (argument selected) positiveSelected n)
  have rawOrder : (CertifiedLogScore.approximation (weight c) (argument c) n +
      CertifiedLogScore.radius (weight c) (argument c) n) ≤
        CertifiedLogScore.approximation (weight selected) (argument selected) n -
          CertifiedLogScore.radius (weight selected) (argument selected) n := by
    have realOrder :
        ((CertifiedLogScore.approximation (weight c) (argument c) n +
          CertifiedLogScore.radius (weight c) (argument c) n : ℚ) : ℝ) ≤
        ((CertifiedLogScore.approximation (weight selected) (argument selected) n -
          CertifiedLogScore.radius (weight selected) (argument selected) n : ℚ) : ℝ) := by
      push_cast
      dsimp [tolerance, score] at hc hs
      linarith [cBound.1, sBound.2]
    exact_mod_cast realOrder
  exact (upper_le_raw weight argument c n).trans
    (rawOrder.trans (raw_lower_le weight argument selected n))

omit [DecidableEq C] in
/-- A finite family with a strictly best score is eventually separated in full. -/
theorem eventually_all_pass (all : List C) (weight argument : C → I → ℚ)
    (selected : C) (positiveSelected : ∀ i, 0 < argument selected i)
    (positive : ∀ c ∈ all, ∀ i, 0 < argument c i)
    (strict : ∀ c ∈ all, c ≠ selected → score weight argument c < score weight argument selected) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ c ∈ all,
      passes (fun c => lower weight argument c n) (fun c => upper weight argument c n)
        selected c := by
  induction all with
  | nil => exact Filter.Eventually.of_forall (by simp)
  | cons c cs ih =>
      have tail := ih (fun d member => positive d (List.mem_cons_of_mem _ member))
        (fun d member => strict d (List.mem_cons_of_mem _ member))
      have head : ∀ᶠ n : ℕ in Filter.atTop,
          passes (fun c => lower weight argument c n) (fun c => upper weight argument c n)
            selected c := by
        by_cases same : c = selected
        · exact Filter.Eventually.of_forall (fun _ => Or.inl same)
        · filter_upwards [eventually_separates weight argument selected c positiveSelected
            (positive c List.mem_cons_self) (strict c List.mem_cons_self same)] with n ordered
          exact Or.inr ordered
      filter_upwards [head, tail] with n hn ht
      intro d member
      rcases List.mem_cons.mp member with rfl | member
      · exact hn
      · exact ht d member

/-- A valid retained prefix can be completed by increasing the numerical budget. -/
theorem eventually_resume_complete (all : List C) (weight argument : C → I → ℚ)
    (selected : C) (receipt : Receipt C) (old : ℕ)
    (valid : Valid all (fun c => lower weight argument c old)
      (fun c => upper weight argument c old) selected receipt)
    (positive : ∀ c ∈ all, ∀ i, 0 < argument c i)
    (strict : ∀ c ∈ all, c ≠ selected → score weight argument c < score weight argument selected) :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ output,
      resume all weight argument selected n receipt.pending.length receipt = some output ∧
        output.pending = [] := by
  filter_upwards [eventually_all_pass all weight argument selected (positive selected valid.1)
    positive strict, Filter.eventually_ge_atTop old] with n good larger
  have current := valid_refines all weight argument selected receipt larger valid
  refine ⟨advance (fun c => lower weight argument c n) (fun c => upper weight argument c n)
    selected receipt.pending.length receipt, ?_, ?_⟩
  · simp only [resume, if_pos positive, ResumableComparison.resume, if_pos current]
  · cases receipt with
    | mk checked pending =>
        apply advance_complete
        intro c member
        apply good c
        rw [← valid.2.1]
        exact List.mem_append_right _ member

end Mettapedia.Algorithms.ResumableLogChoice
