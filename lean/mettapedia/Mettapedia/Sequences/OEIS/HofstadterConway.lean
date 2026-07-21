import Mathlib.Tactic
import Mettapedia.Sequences.OEIS.Basic

/-!
# The Hofstadter--Conway sequence

This module formalizes OEIS A004001 and its centered transform A004074.
The nested recurrence is named for Douglas Hofstadter and John Conway; the
OEIS entries were contributed by N. J. A. Sloane.
-/

namespace Mettapedia.Sequences.OEIS.HofstadterConway

/--
The recurrence together with the bounds needed to justify both recursive
indices.  Carrying the bounds in the construction makes totality explicit.
-/
def certifiedStep (n : Nat)
    (earlier : ∀ m < n, { value : Nat // 1 ≤ value ∧ value ≤ max 1 m }) :
    { value : Nat // 1 ≤ value ∧ value ≤ max 1 n } :=
  if small : n ≤ 2 then
    ⟨1, by simp⟩
  else
    let previous := earlier (n - 1) (by omega)
    have threeLe : 3 ≤ n := by omega
    have previousUpper : previous.1 ≤ n - 1 := by
      have bound := previous.2.2
      simpa [Nat.max_eq_right (by omega : 1 ≤ n - 1)] using bound
    have previousLt : previous.1 < n := by omega
    have remainderPositive : 1 ≤ n - previous.1 := by omega
    have remainderLt : n - previous.1 < n := Nat.sub_lt (by omega) previous.2.1
    let left := earlier previous.1 previousLt
    let right := earlier (n - previous.1) remainderLt
    have leftUpper : left.1 ≤ previous.1 := by
      have bound := left.2.2
      simpa [Nat.max_eq_right previous.2.1] using bound
    have rightUpper : right.1 ≤ n - previous.1 := by
      have bound := right.2.2
      simpa [Nat.max_eq_right remainderPositive] using bound
    ⟨left.1 + right.1, by
      constructor
      · omega
      · rw [Nat.max_eq_right (by omega : 1 ≤ n)]
        omega⟩

def certified (n : Nat) : { value : Nat // 1 ≤ value ∧ value ≤ max 1 n } :=
  Nat.strongRec certifiedStep n

/-- The Hofstadter--Conway sequence, indexed from one. -/
def value (n : Nat) : Nat := (certified n).1

theorem value_positive (n : Nat) : 1 ≤ value n :=
  (certified n).2.1

theorem value_le_max (n : Nat) : value n ≤ max 1 n :=
  (certified n).2.2

theorem value_le {n : Nat} (positive : 1 ≤ n) : value n ≤ n := by
  simpa [value, Nat.max_eq_right positive] using value_le_max n

theorem value_of_le_two {n : Nat} (small : n ≤ 2) : value n = 1 := by
  rw [value, certified, Nat.strongRec_eq]
  simp [certifiedStep, small]

theorem value_one : value 1 = 1 := value_of_le_two (by omega)

theorem value_two : value 2 = 1 := value_of_le_two (by omega)

theorem value_recurrence {n : Nat} (threeLe : 3 ≤ n) :
    value n = value (value (n - 1)) + value (n - value (n - 1)) := by
  have notSmall : ¬ n ≤ 2 := by omega
  rw [value, certified, Nat.strongRec_eq]
  simp only [certifiedStep, notSmall, ↓reduceDIte]
  rfl

/-- From the second term onward, the value is a valid earlier index. -/
theorem value_le_pred : ∀ n, 2 ≤ n → value n ≤ n - 1 := by
  intro n
  induction n using Nat.strongRec with
  | ind n earlier =>
      intro twoLe
      by_cases equalTwo : n = 2
      · subst n
        simp [value_two]
      · have threeLe : 3 ≤ n := by omega
        let previous := value (n - 1)
        have previousPositive : 1 ≤ previous := value_positive _
        have previousUpper : previous ≤ n - 1 := value_le (by omega)
        have previousLt : previous < n := by omega
        have remainderPositive : 1 ≤ n - previous := by omega
        have remainderLt : n - previous < n := Nat.sub_lt (by omega) previousPositive
        rw [value_recurrence threeLe]
        change value previous + value (n - previous) ≤ n - 1
        by_cases previousOne : previous = 1
        · have remainderTwo : 2 ≤ n - previous := by omega
          have rightUpper := earlier (n - previous) remainderLt remainderTwo
          have leftOne : value previous = 1 := by
            rw [previousOne, value_one]
          omega
        · have previousTwo : 2 ≤ previous := by omega
          have leftUpper := earlier previous previousLt previousTwo
          have rightUpper := value_le remainderPositive
          omega

/-- Exact source coordinates for OEIS A004001 in the pinned snapshot. -/
def sourceA004001 : EntrySource where
  oeisId := "A004001"
  snapshotRevision := "a6e0f22854cc1c307da428e9d6295093781df7fa"
  entrySha256 := "65acb0df8c1af28df20d508f848fb6466bae492803c845fed50f9e0be7d70dd3"
  offset := 1

/-- OEIS A004001 as an integer-valued sequence specification. -/
def specA004001 : SequenceSpec where
  offset := 1
  Domain := fun index => 1 ≤ index
  value := fun index => Int.ofNat (value index.toNat)

def formalizationA004001 : Formalization where
  source := sourceA004001
  spec := specA004001
  offsetMatches := rfl

/-- Exact source coordinates for OEIS A004074 in the pinned snapshot. -/
def sourceA004074 : EntrySource where
  oeisId := "A004074"
  snapshotRevision := "a6e0f22854cc1c307da428e9d6295093781df7fa"
  entrySha256 := "1abdde6939024ff63c709ac9922f60584bd27461c22b8e0e976903430ab9c46a"
  offset := 1

/-- OEIS A004074, the centered transform `2 * A004001(n) - n`. -/
def specA004074 : SequenceSpec where
  offset := 1
  Domain := fun index => 1 ≤ index
  value := fun index => 2 * Int.ofNat (value index.toNat) - index

def formalizationA004074 : Formalization where
  source := sourceA004074
  spec := specA004074
  offsetMatches := rfl

#print axioms value_recurrence

end Mettapedia.Sequences.OEIS.HofstadterConway
