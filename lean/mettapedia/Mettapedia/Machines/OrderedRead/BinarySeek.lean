import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# A logarithmic lower-bound seek in a ranked view

The monotone Boolean oracle says that the key at a rank is at or above the
requested lower bound. Ranks beyond the captured population are true
sentinels. A perfect-capacity bisection performs one probe per level and one
at a leaf, and returns the first true rank. The tariff counts oracle probes;
term comparison and the native rank-access representation have their own costs.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedRead.BinarySeek

def Increasing (test : Nat → Bool) : Prop :=
  ∀ first second, first ≤ second → test first = true → test second = true

def seek (test : Nat → Bool) : Nat → Nat → Nat × Nat
  | 0, start => if test start then (start, 1) else (start + 1, 1)
  | height + 1, start =>
      let middle := start + 2 ^ height
      let found := if test middle then seek test height start else seek test height middle
      (found.1, found.2 + 1)

theorem probes_exact (test : Nat → Bool) (height start : Nat) :
    (seek test height start).2 = height + 1 := by
  induction height generalizing start with
  | zero => cases tested : test start <;> simp [seek, tested]
  | succ height ih =>
      cases tested : test (start + 2 ^ height) <;> simp [seek, tested, ih]

theorem seek_correct (test : Nat → Bool) (increasing : Increasing test) (height start : Nat) :
    start ≤ (seek test height start).1 ∧ (seek test height start).1 ≤ start + 2 ^ height ∧
      (∀ rank, start ≤ rank → rank < (seek test height start).1 → test rank = false) ∧
      ((seek test height start).1 < start + 2 ^ height → test (seek test height start).1 = true) := by
  induction height generalizing start with
  | zero =>
      cases tested : test start with
      | true =>
          simp only [seek, if_pos tested, Nat.pow_zero]
          refine ⟨le_rfl, by omega, ?_, fun _ => tested⟩
          intro rank lower below
          omega
      | false =>
          have rejects : ¬ test start = true := by simp [tested]
          simp only [seek, if_neg rejects, Nat.pow_zero]
          refine ⟨by omega, le_rfl, ?_, ?_⟩
          · intro rank lower below
            have same : rank = start := by omega
            simpa only [same] using tested
          · intro impossible
            omega
  | succ height ih =>
      have positive : 0 < 2 ^ height := by positivity
      cases tested : test (start + 2 ^ height) with
      | true =>
          obtain ⟨lower, upper, before, atFound⟩ := ih start
          simp only [seek, tested, ↓reduceIte, pow_succ]
          refine ⟨lower, by omega, before, ?_⟩
          intro _
          by_cases inside : (seek test height start).1 < start + 2 ^ height
          · exact atFound inside
          · have same : (seek test height start).1 = start + 2 ^ height := by omega
            simpa only [same] using tested
      | false =>
          obtain ⟨lower, upper, before, atFound⟩ := ih (start + 2 ^ height)
          simp only [seek, tested, Bool.false_eq_true, ↓reduceIte, pow_succ]
          refine ⟨by omega, by omega, ?_, ?_⟩
          · intro rank old below
            by_cases earlier : rank < start + 2 ^ height
            · cases found : test rank with
              | false => rfl
              | true =>
                  have impossible := increasing rank (start + 2 ^ height) (by omega) found
                  rw [tested] at impossible
                  contradiction
            · exact before rank (by omega) below
          · intro inside
            exact atFound (by omega)

theorem seek_with_sentinel (test : Nat → Bool) (increasing : Increasing test)
    (height population : Nat) (covers : population ≤ 2 ^ height) (sentinel : test population = true) :
    (seek test height 0).1 ≤ population ∧
      (∀ rank, rank < population → test rank = true → (seek test height 0).1 ≤ rank) ∧
      ((seek test height 0).1 < population → test (seek test height 0).1 = true) := by
  obtain ⟨lower, upper, before, atFound⟩ := seek_correct test increasing height 0
  have bounded : (seek test height 0).1 ≤ population := by
    by_contra late
    have impossible := before population (Nat.zero_le _) (by omega)
    rw [sentinel] at impossible
    contradiction
  refine ⟨bounded, ?_, ?_⟩
  · intro rank inside matched
    by_contra late
    have impossible := before rank (Nat.zero_le _) (by omega)
    rw [matched] at impossible
    contradiction
  · intro inside
    exact atFound (by omega)

namespace Controls

theorem first_answer_after_logarithmic_seek :
    seek (fun rank => decide (37 ≤ rank)) 6 0 = (37, 7) := by decide

theorem absent_region_stops_at_the_captured_sentinel :
    seek (fun rank => decide (50 ≤ rank)) 6 0 = (50, 7) := by decide

theorem an_unordered_oracle_does_not_supply_the_seek_law :
    ¬ Increasing (fun rank => decide (rank = 1)) := by
  intro increasing
  have impossible := increasing 1 2 (by decide) (by decide)
  contradiction

end Controls

end Mettapedia.Machines.OrderedRead.BinarySeek
