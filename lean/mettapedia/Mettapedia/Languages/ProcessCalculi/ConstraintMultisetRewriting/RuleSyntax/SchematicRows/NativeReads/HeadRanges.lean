import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.BinaryCut
import Mathlib.Data.Prod.Lex

/-!
# Complete head/arity bands from the native binary cut

Sorted keys are a property of the captured view. The two intervals retain
unknown heads and exact rigid head/arity keys. Unknown query heads use the
whole view. No unknown row can silently disappear into a rigid bucket.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.HeadRanges

variable {Key : Type} [LinearOrder Key]

def Sorted (keys : Nat → Key) (size : Nat) : Prop :=
  ∀ i j, i ≤ j → j < size → keys i ≤ keys j

def lower (keys : Nat → Key) (size : Nat) (key : Key) : Nat :=
  BinaryCut.cut (fun i => decide (keys i < key)) size

def upper (keys : Nat → Key) (size : Nat) (key : Key) : Nat :=
  BinaryCut.cut (fun i => decide (keys i ≤ key)) size

theorem lower_prefix (keys : Nat → Key) (size : Nat) (sorted : Sorted keys size) (key : Key) :
    BinaryCut.Prefix (fun i => decide (keys i < key)) size := by
  intro i j before inside accepted
  exact decide_eq_true (lt_of_le_of_lt (sorted i j before inside) (of_decide_eq_true accepted))

theorem upper_prefix (keys : Nat → Key) (size : Nat) (sorted : Sorted keys size) (key : Key) :
    BinaryCut.Prefix (fun i => decide (keys i ≤ key)) size := by
  intro i j before inside accepted
  exact decide_eq_true ((sorted i j before inside).trans (of_decide_eq_true accepted))

theorem lower_iff (keys : Nat → Key) (size : Nat) (sorted : Sorted keys size) (key : Key)
    (i : Nat) (inside : i < size) : i < lower keys size key ↔ keys i < key := by
  exact (BinaryCut.before_iff _ _ (lower_prefix keys size sorted key) i inside).symm.trans
    (by simp only [decide_eq_true_eq])

theorem upper_iff (keys : Nat → Key) (size : Nat) (sorted : Sorted keys size) (key : Key)
    (i : Nat) (inside : i < size) : i < upper keys size key ↔ keys i ≤ key := by
  exact (BinaryCut.before_iff _ _ (upper_prefix keys size sorted key) i inside).symm.trans
    (by simp only [decide_eq_true_eq])

theorem lower_bound (keys : Nat → Key) (size : Nat) (sorted : Sorted keys size) (key : Key) :
    lower keys size key ≤ size := BinaryCut.cut_bounds _ _ (lower_prefix keys size sorted key)

theorem upper_bound (keys : Nat → Key) (size : Nat) (sorted : Sorted keys size) (key : Key) :
    upper keys size key ≤ size := BinaryCut.cut_bounds _ _ (upper_prefix keys size sorted key)

theorem lower_mono (keys : Nat → Key) (size : Nat) (sorted : Sorted keys size)
    (first second : Key) (ordered : first ≤ second) : lower keys size first ≤ lower keys size second := by
  by_contra reversed
  have inside : lower keys size second < size := by
    have bound := lower_bound keys size sorted first
    omega
  have before := (lower_iff keys size sorted first _ inside).mp (by omega)
  have impossible := (lower_iff keys size sorted second _ inside).mpr (lt_of_lt_of_le before ordered)
  exact (Nat.lt_irrefl _) impossible

theorem in_band_iff (keys : Nat → Key) (size : Nat) (sorted : Sorted keys size) (key : Key)
    (i : Nat) (inside : i < size) :
    lower keys size key ≤ i ∧ i < upper keys size key ↔ keys i = key := by
  constructor
  · rintro ⟨lower, upper⟩
    have atMost := (upper_iff keys size sorted key i inside).mp upper
    have atLeast : key ≤ keys i := by
      by_contra before
      have left := (lower_iff keys size sorted key i inside).mpr (lt_of_not_ge before)
      omega
    exact le_antisymm atMost atLeast
  · intro equal
    constructor
    · by_contra before
      have left := (lower_iff keys size sorted key i inside).mp (by omega)
      rw [equal] at left
      exact (lt_irrefl _) left
    · exact (upper_iff keys size sorted key i inside).mpr equal.le

def interval (low high : Nat) : List Nat := (List.range (high - low)).map (low + ·)

theorem mem_interval (low high i : Nat) : i ∈ interval low high ↔ low ≤ i ∧ i < high := by
  simp only [interval, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨offset, within, rfl⟩
    omega
  · rintro ⟨after, before⟩
    exact ⟨i - low, by omega, by omega⟩

abbrev HeadKey := Nat ×ₗ Nat

def twoRuns (keys : Nat → HeadKey) (size head arity : Nat) : List Nat :=
  interval 0 (lower keys size (toLex (1, 0))) ++
    interval (lower keys size (toLex (head, arity))) (upper keys size (toLex (head, arity)))

theorem two_runs_complete (keys : Nat → HeadKey) (size : Nat) (sorted : Sorted keys size)
    (head arity i : Nat) (inside : i < size)
    (possible : (ofLex (keys i)).1 = 0 ∨ keys i = toLex (head, arity)) :
    i ∈ twoRuns keys size head arity := by
  rw [twoRuns, List.mem_append, mem_interval, mem_interval]
  rcases possible with unknown | same
  · left
    refine ⟨Nat.zero_le _, (lower_iff keys size sorted _ i inside).mpr ?_⟩
    rw [Prod.Lex.lt_iff]
    left
    rw [unknown]
    change (0 : Nat) < 1
    omega
  · right
    exact (in_band_iff keys size sorted _ i inside).mpr same

theorem selected_range_is_complete (keys : Nat → HeadKey) (size : Nat) (sorted : Sorted keys size)
    (head arity i : Nat) (inside : i < size) :
    i ∈ (if head = 0 then List.range size else twoRuns keys size head arity) ↔
      head = 0 ∨ (ofLex (keys i)).1 = 0 ∨ keys i = toLex (head, arity) := by
  by_cases openHead : head = 0
  · simp [openHead, inside]
  · rw [if_neg openHead]
    simp only [openHead, false_or]
    constructor
    · intro member
      rw [twoRuns, List.mem_append, mem_interval, mem_interval] at member
      rcases member with unknown | exactKey
      · left
        have less := (lower_iff keys size sorted _ i inside).mp unknown.2
        rw [Prod.Lex.lt_iff] at less
        rcases less with first | ⟨_, impossible⟩
        · change (ofLex (keys i)).1 < 1 at first
          omega
        · exact False.elim (Nat.not_lt_zero _ impossible)
      · exact Or.inr ((in_band_iff keys size sorted _ i inside).mp exactKey)
    · exact two_runs_complete keys size sorted head arity i inside

#print axioms in_band_iff
#print axioms two_runs_complete
#print axioms selected_range_is_complete

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.HeadRanges
