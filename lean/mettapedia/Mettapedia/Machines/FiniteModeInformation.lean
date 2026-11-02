import Mettapedia.Machines.BinaryModeInformation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases

/-!
# Finite-label mode and its future-addition information

The label universe is fixed and nonempty. Counts are natural-valued; mode
returns the smallest label with greatest count, or no label for the zero bag.
Signed differences from one fixed label remove a common count offset. The
occupancy observation is retained separately. This contract does not permit
extending the label universe, observing total counts, or deleting votes without
additional information.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ModeAggregation.FiniteInformation

abbrev Label (n : Nat) := Fin (n + 1)
abbrev Counts (n : Nat) := Label n → Nat

def rank {n : Nat} (counts : Counts n) (label : Label n) : Nat ×ₗ OrderDual (Label n) :=
  toLex (counts label, label)

def select {n : Nat} (counts : Counts n) : Option (Label n) :=
  (List.finRange (n + 1)).argmax (rank counts)

theorem rank_le {n : Nat} (counts : Counts n) (a b : Label n) :
    rank counts a ≤ rank counts b ↔ counts a ≤ counts b ∧ (counts a = counts b → b ≤ a) :=
  Prod.Lex.toLex_le_toLex'

theorem rank_injective {n : Nat} (counts : Counts n) : Function.Injective (rank counts) := by
  intro a b same
  exact congrArg (fun p : Nat ×ₗ OrderDual (Label n) => (ofLex p).2) same

theorem select_spec {n : Nat} (counts : Counts n) (winner : Label n) :
    select counts = some winner ↔ ∀ label,
      counts label ≤ counts winner ∧ (counts label = counts winner → winner ≤ label) := by
  constructor
  · intro selected label
    exact (rank_le counts label winner).mp (List.le_of_mem_argmax (by simp) selected)
  · intro maximal
    apply List.argmax_eq_some_iff.mpr
    refine ⟨by simp, fun label _ => (rank_le counts label winner).mpr (maximal label), ?_⟩
    intro label _ reverse
    have same := rank_injective counts
      (le_antisymm reverse ((rank_le counts label winner).mpr (maximal label)))
    subst label
    rfl

theorem select_ne_none {n : Nat} (counts : Counts n) : select counts ≠ none := by
  intro empty
  have noLabels := List.argmax_eq_none.mp empty
  have lengths := congrArg List.length noLabels
  simp at lengths

def mode {n : Nat} (counts : Counts n) : Option (Label n) :=
  if counts = 0 then none else select counts

theorem mode_none_iff {n : Nat} (counts : Counts n) : mode counts = none ↔ counts = 0 := by
  by_cases empty : counts = 0 <;> simp [mode, empty, select_ne_none]

theorem positive_of_nonzero {n : Nat} (counts : Counts n) (nonzero : counts ≠ 0) :
    ∃ label, 0 < counts label := by
  by_contra no
  push Not at no
  apply nonzero
  funext label
  have := no label
  exact Nat.eq_zero_of_le_zero this

theorem mode_spec {n : Nat} (counts : Counts n) (winner : Label n) :
    mode counts = some winner ↔ 0 < counts winner ∧ ∀ label,
      counts label ≤ counts winner ∧ (counts label = counts winner → winner ≤ label) := by
  constructor
  · intro selected
    have nonzero : counts ≠ 0 := by intro empty; simp [mode, empty] at selected
    have maximal := (select_spec counts winner).mp (by simpa [mode, nonzero] using selected)
    obtain ⟨label, positive⟩ := positive_of_nonzero counts nonzero
    exact ⟨lt_of_lt_of_le positive (maximal label).1, maximal⟩
  · rintro ⟨positive, maximal⟩
    have nonzero : counts ≠ 0 := by intro empty; simp [empty] at positive
    simpa [mode, nonzero] using (select_spec counts winner).mpr maximal

def differences {n : Nat} (counts : Counts n) : Label n → Int :=
  fun label => (counts label : Int) - (counts 0 : Int)

structure Summary (n : Nat) where
  differences : Label n → Int
  occupied : Bool

def summarize {n : Nat} (counts : Counts n) : Summary n := ⟨differences counts, decide (counts ≠ 0)⟩

def combine {n : Nat} (left right : Summary n) : Summary n :=
  ⟨left.differences + right.differences, left.occupied || right.occupied⟩

theorem differences_add {n : Nat} (left right : Counts n) :
    differences (left + right) = differences left + differences right := by
  funext label
  simp [differences]
  omega

theorem summarize_add {n : Nat} (left right : Counts n) :
    summarize (left + right) = combine (summarize left) (summarize right) := by
  have zero : left + right = 0 ↔ left = 0 ∧ right = 0 := by
    constructor
    · intro empty
      constructor
      · funext label
        change left label = 0
        have := congrFun empty label
        simp only [Pi.add_apply, Pi.zero_apply] at this
        omega
      · funext label
        change right label = 0
        have := congrFun empty label
        simp only [Pi.add_apply, Pi.zero_apply] at this
        omega
    · rintro ⟨rfl, rfl⟩; simp
  simp [summarize, combine, differences_add, zero]

theorem pairwise_differences {n : Nat} {left right : Counts n} (same : differences left = differences right)
    (a b : Label n) : (left a : Int) - left b = (right a : Int) - right b := by
  have ha := congrFun same a
  have hb := congrFun same b
  simp only [differences] at ha hb
  omega

theorem summary_preserves_mode {n : Nat} {left right : Counts n} (same : summarize left = summarize right) :
    mode left = mode right := by
  have diff := congrArg Summary.differences same
  have present := congrArg Summary.occupied same
  have zero : left = 0 ↔ right = 0 := by
    constructor
    · intro empty
      by_contra nonzero
      simp [summarize, empty, nonzero] at present
    · intro empty
      by_contra nonzero
      simp [summarize, empty, nonzero] at present
  cases result : mode left with
  | none =>
    have rightEmpty := zero.mp ((mode_none_iff left).mp result)
    simp [rightEmpty, mode]
  | some winner =>
    have first := (mode_spec left winner).mp result
    have nonzero : right ≠ 0 := by intro empty; have := zero.mpr empty; simp [this] at first
    obtain ⟨witness, positive⟩ := positive_of_nonzero right nonzero
    have compare (label : Label n) : right label ≤ right winner := by
      have delta := pairwise_differences diff label winner
      have := (first.2 label).1
      omega
    symm
    apply (mode_spec right winner).mpr
    refine ⟨lt_of_lt_of_le positive (compare witness), ?_⟩
    intro label
    refine ⟨compare label, ?_⟩
    intro tied
    apply (first.2 label).2
    have delta := pairwise_differences diff label winner
    omega

def SameFuture {n : Nat} (left right : Counts n) : Prop :=
  ∀ added : Counts n, mode (left + added) = mode (right + added)

theorem summary_sameFuture {n : Nat} {left right : Counts n} (same : summarize left = summarize right) :
    SameFuture left right := by
  intro added
  apply summary_preserves_mode
  rw [summarize_add, summarize_add, same]

/-! ## Constructive distinguishing additions -/

def mass {n : Nat} (counts : Counts n) : Nat := ∑ label, counts label

theorem count_le_mass {n : Nat} (counts : Counts n) (label : Label n) : counts label ≤ mass counts :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ label)

/-- Both selected labels exceed every other label in both stores. In `right`
they tie, so the smaller label wins. Their difference in `left` is retained. -/
def boost {n : Nat} (left right : Counts n) (a b : Label n) : Counts n :=
  fun label => if label = a then mass left + mass right + 1 + right b
    else if label = b then mass left + mass right + 1 + right a else 0

theorem boost_right {n : Nat} (left right : Counts n) (a b : Label n) (ordered : a < b) :
    mode (right + boost left right a b) = some a := by
  apply (mode_spec _ _).mpr
  have apart : b ≠ a := ne_of_gt ordered
  constructor
  · simp [boost]
  · intro label
    by_cases first : label = a
    · subst label; exact ⟨le_rfl, fun _ => le_rfl⟩
    · by_cases second : label = b
      · subst label
        simp only [Pi.add_apply, boost, if_neg apart, ↓reduceIte]
        constructor
        · omega
        · intro _; exact le_of_lt ordered
      · have bounded := count_le_mass right label
        simp only [Pi.add_apply, boost, if_neg first, if_neg second, ↓reduceIte]
        constructor <;> omega

theorem boost_left {n : Nat} (left right : Counts n) (a b : Label n) (ordered : a < b)
    (gap : (left a : Int) - left b < (right a : Int) - right b) :
    mode (left + boost left right a b) = some b := by
  apply (mode_spec _ _).mpr
  have apart : b ≠ a := ne_of_gt ordered
  constructor
  · simp [boost, apart]
  · intro label
    by_cases first : label = a
    · subst label
      simp only [Pi.add_apply, boost, if_neg apart, ↓reduceIte]
      constructor <;> omega
    · by_cases second : label = b
      · subst label; exact ⟨le_rfl, fun _ => le_rfl⟩
      · have bounded := count_le_mass left label
        simp only [Pi.add_apply, boost, if_neg first, if_neg second, if_neg apart, ↓reduceIte]
        constructor <;> omega

theorem sameFuture_ordered_differences {n : Nat} {left right : Counts n}
    (same : SameFuture left right) (a b : Label n) (ordered : a < b) :
    (left a : Int) - left b = (right a : Int) - right b := by
  have notLess : ¬ (left a : Int) - left b < (right a : Int) - right b := by
    intro gap
    have observe := same (boost left right a b)
    rw [boost_left left right a b ordered gap, boost_right left right a b ordered] at observe
    exact (ne_of_gt ordered) (Option.some.inj observe)
  have notGreater : ¬ (right a : Int) - right b < (left a : Int) - left b := by
    intro gap
    have observe := same (boost right left a b)
    rw [boost_right right left a b ordered, boost_left right left a b ordered gap] at observe
    exact (ne_of_lt ordered) (Option.some.inj observe)
  omega

theorem sameFuture_iff_summary {n : Nat} (left right : Counts n) :
    SameFuture left right ↔ summarize left = summarize right := by
  constructor
  · intro same
    have diff : differences left = differences right := by
      funext label
      by_cases zero : label = 0
      · subst label; simp [differences]
      · have ordered : (0 : Label n) < label := lt_of_le_of_ne (Fin.zero_le label) (Ne.symm zero)
        have gap := sameFuture_ordered_differences same 0 label ordered
        simp only [differences]
        omega
    have zero : left = 0 ↔ right = 0 := by
      have observe := same 0
      simp only [add_zero] at observe
      rw [← mode_none_iff, ← mode_none_iff, observe]
    exact congrArg₂ Summary.mk diff (by simp [zero])
  · exact summary_sameFuture

theorem every_future_summary_refines {n : Nat} {Code : Type} (encode : Counts n → Code)
    (decode : Code → Counts n → Option (Label n))
    (correct : ∀ counts added, decode (encode counts) added = mode (counts + added))
    {left right : Counts n} (same : encode left = encode right) : summarize left = summarize right := by
  apply (sameFuture_iff_summary left right).mp
  intro added
  rw [← correct, ← correct, same]

/-! ## A complete finite family of distinguishing tests -/

def testSuffixes {n : Nat} (left right : Counts n) : List (Counts n) :=
  0 :: (List.finRange (n + 1)).flatMap fun label =>
    [boost left right 0 label, boost right left 0 label]

theorem tests_complete {n : Nat} (left right : Counts n)
    (agree : ∀ added ∈ testSuffixes left right, mode (left + added) = mode (right + added)) :
    summarize left = summarize right := by
  have initial : mode left = mode right := by simpa using agree 0 (by simp [testSuffixes])
  have diff : differences left = differences right := by
    funext label
    by_cases zero : label = 0
    · subst label; simp [differences]
    · have ordered : (0 : Label n) < label := lt_of_le_of_ne (Fin.zero_le label) (Ne.symm zero)
      have first := agree (boost left right 0 label) (by
        apply List.mem_cons_of_mem
        exact List.mem_flatMap.mpr ⟨label, by simp, by simp⟩)
      have second := agree (boost right left 0 label) (by
        apply List.mem_cons_of_mem
        exact List.mem_flatMap.mpr ⟨label, by simp, by simp⟩)
      have notLess : ¬ (left 0 : Int) - left label < (right 0 : Int) - right label := by
        intro gap
        rw [boost_left left right 0 label ordered gap, boost_right left right 0 label ordered] at first
        exact zero (Option.some.inj first)
      have notGreater : ¬ (right 0 : Int) - right label < (left 0 : Int) - left label := by
        intro gap
        rw [boost_right right left 0 label ordered, boost_left right left 0 label ordered gap] at second
        exact zero (Option.some.inj second).symm
      simp only [differences]
      omega
  have zero : left = 0 ↔ right = 0 := by rw [← mode_none_iff, ← mode_none_iff, initial]
  exact congrArg₂ Summary.mk diff (by simp [zero])

def separator {n : Nat} (left right : Counts n) : Option (Counts n) :=
  (testSuffixes left right).find? fun added => decide (mode (left + added) ≠ mode (right + added))

theorem separator_sound {n : Nat} (left right added : Counts n)
    (found : separator left right = some added) : mode (left + added) ≠ mode (right + added) := by
  have passed := List.find?_some
    (p := fun delta : Counts n => decide (mode (left + delta) ≠ mode (right + delta))) found
  exact of_decide_eq_true passed

theorem separator_none_iff {n : Nat} (left right : Counts n) :
    separator left right = none ↔ summarize left = summarize right := by
  simp only [separator, List.find?_eq_none, decide_eq_true_eq, not_not]
  constructor
  · exact tests_complete left right
  · intro same added _
    exact summary_sameFuture same added

theorem test_count {n : Nat} (left right : Counts n) : (testSuffixes left right).length = 2 * (n + 1) + 1 := by
  have length (labels : List (Label n)) :
      (labels.flatMap fun label => [boost left right 0 label, boost right left 0 label]).length = 2 * labels.length := by
    induction labels with
    | nil => simp
    | cons label rest ih => simp [ih, Nat.mul_add, Nat.add_comm]; omega
  simp [testSuffixes, length]

/-! ## Executing the quotient and returning to the source fold -/

def readSummary {n : Nat} (summary : Summary n) : Option (Label n) :=
  if summary.occupied then
    (List.finRange (n + 1)).argmax (fun label =>
      (toLex (summary.differences label, label) : Int ×ₗ OrderDual (Label n)))
  else none

theorem readSummary_exact {n : Nat} (counts : Counts n) : readSummary (summarize counts) = mode counts := by
  by_cases empty : counts = 0
  · simp [readSummary, summarize, mode, empty]
  · cases selected : select counts with
    | none => exact False.elim (select_ne_none counts selected)
    | some winner =>
      have best := (select_spec counts winner).mp selected
      let score : Label n → Int ×ₗ OrderDual (Label n) := fun label => toLex (differences counts label, label)
      have maximal (label : Label n) : score label ≤ score winner := by
        apply Prod.Lex.toLex_le_toLex'.mpr
        have original := best label
        change ((counts label : Int) - counts 0 ≤ (counts winner : Int) - counts 0) ∧ _
        refine ⟨by omega, ?_⟩
        intro equal
        exact original.2 (by change (counts label : Int) - counts 0 = (counts winner : Int) - counts 0 at equal; omega)
      have result : (List.finRange (n + 1)).argmax score = some winner := by
        apply List.argmax_eq_some_iff.mpr
        refine ⟨by simp, fun label _ => maximal label, ?_⟩
        intro label _ reverse
        have equal := congrArg (fun pair : Int ×ₗ OrderDual (Label n) => (ofLex pair).2)
          (le_antisymm reverse (maximal label))
        change winner = label at equal
        subst label
        rfl
      simpa [readSummary, summarize, mode, empty, selected, score] using result

def histogramLabels {n : Nat} (labels : List (Label n)) : Counts n := fun label => labels.count label

theorem mode_labels_exact {n : Nat} (labels : List (Label n)) :
    (mode (histogramLabels labels)).map Fin.val = ModeAggregation.mode (labels.map Fin.val) := by
  cases result : mode (histogramLabels labels) with
  | none =>
    have emptyCounts := (mode_none_iff _).mp result
    have empty : labels = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro label present
      have positive := List.count_pos_iff.mpr present
      have zero := congrFun emptyCounts label
      change labels.count label = 0 at zero
      omega
    simp [empty, ModeAggregation.mode, ModeAggregation.readout]
  | some winner =>
    have winning := (mode_spec _ _).mp result
    simp only [Option.map_some]
    symm
    apply (ModeAggregation.mode_spec _ _).mpr
    refine ⟨List.mem_map.mpr ⟨winner, List.count_pos_iff.mp winning.1, rfl⟩, ?_⟩
    intro label present
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp present
    rw [List.count_map_of_injective _ _ Fin.val_injective,
      List.count_map_of_injective _ _ Fin.val_injective]
    exact winning.2 key

theorem sorted_source_from_summary {n : Nat} (labels : List (Label n)) :
    (readSummary (summarize (histogramLabels labels))).map Fin.val =
      SortedRun.sourceMode ((labels.map Fin.val).mergeSort (· ≤ ·)) := by
  rw [readSummary_exact, mode_labels_exact,
    SortedRun.sorted_source_is_histogram_readout, sparse_readout_exact]

/-- The anchor coordinate is known to be zero and need not be stored. -/
def compact {n : Nat} (counts : Counts n) : (Fin n → Int) × Bool :=
  (fun i => differences counts i.succ, decide (counts ≠ 0))

def expandCompact {n : Nat} (code : (Fin n → Int) × Bool) : Summary n :=
  ⟨Fin.cases 0 code.1, code.2⟩

theorem compact_roundtrip {n : Nat} (counts : Counts n) : expandCompact (compact counts) = summarize counts := by
  apply congrArg₂ Summary.mk
  · funext label
    refine Fin.cases ?_ (fun i => ?_) label
    · simp [compact, differences]
    · rfl
  · rfl

theorem compact_eq_iff_future {n : Nat} (left right : Counts n) :
    compact left = compact right ↔ SameFuture left right := by
  constructor
  · intro same
    apply summary_sameFuture
    rw [← compact_roundtrip, ← compact_roundtrip, same]
  · intro same
    have equal := (sameFuture_iff_summary left right).mp same
    exact congrArg (fun summary : Summary n => (fun i : Fin n => summary.differences i.succ, summary.occupied)) equal

namespace Controls

def first : Counts 2 := ![3, 1, 2]
def shifted : Counts 2 := ![8, 6, 7]

theorem common_offset_same_future : SameFuture first shifted := by
  apply summary_sameFuture
  apply congrArg₂ Summary.mk
  · funext label; fin_cases label <;> decide
  · decide

theorem winner_alone_loses_information :
    mode (![3, 1, 2] : Counts 2) = mode (![3, 1, 1] : Counts 2) ∧
    mode ((![3, 1, 2] : Counts 2) + ![0, 0, 2]) ≠
      mode ((![3, 1, 1] : Counts 2) + ![0, 0, 2]) := by decide

theorem extending_the_universe_distinguishes :
    summarize (![1, 1] : Counts 1) = summarize (![2, 2] : Counts 1) ∧
    mode (![1, 1, 2] : Counts 2) ≠ mode (![2, 2, 2] : Counts 2) := by
  constructor
  · apply congrArg₂ Summary.mk
    · funext label; fin_cases label <;> decide
    · decide
  · decide

theorem total_count_is_not_retained : mass first = 6 ∧ mass shifted = 21 := by decide

theorem separator_finds_a_lost_vote :
    (separator (![3, 1, 2] : Counts 2) ![3, 1, 1]).isSome = true := by decide

theorem separator_accepts_common_offset : (separator first shifted).isNone = true := by decide

end Controls
end Mettapedia.Machines.ModeAggregation.FiniteInformation
