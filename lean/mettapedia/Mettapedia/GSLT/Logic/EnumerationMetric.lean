import Mettapedia.GSLT.Logic.BudgetedObservations

/-!
# The first distinguishing test and its dyadic distance

This is the enumerated-observation form of Finding Mind, Definition 16.3.
The general weighted supremum is exactly `2^(-first)` when `first` is the
least distinguishing index. Surjective re-enumeration preserves the zero
kernel; preserving the numerical distance additionally requires prices.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Logic

universe u v

noncomputable def enumeratedTests {State : Type u} (reading : Nat → State → Prop) :
    BudgetedObservations State where
  Test := Nat
  holds := reading
  weight index := (1 / 2 : ℝ) ^ index
  positive _ := pow_pos (by norm_num) _
  bounded _ := pow_le_one₀ (by norm_num) (by norm_num)

theorem enumerated_distance_first {State : Type u} (reading : Nat → State → Prop)
    (left right : State) (first : Nat)
    (different : ¬ (reading first left ↔ reading first right))
    (before : ∀ index, index < first → (reading index left ↔ reading index right)) :
    (enumeratedTests reading).distance left right = (1 / 2 : ℝ) ^ first := by
  classical
  apply le_antisymm
  · apply ((enumeratedTests reading).distance_le_iff left right _).mpr
    refine ⟨(pow_pos (by norm_num : (0 : ℝ) < 1 / 2) first).le, ?_⟩
    intro index
    change Nat at index
    change (if reading index left ↔ reading index right then 0 else (1 / 2 : ℝ) ^ index) ≤ _
    by_cases earlier : index < first
    · rw [if_pos (before index earlier)]
      exact (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) first).le
    · have decreasing := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) ≤ 1) (Nat.le_of_not_gt earlier)
      split_ifs
      · exact (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) first).le
      · exact decreasing
  · have lower := (enumeratedTests reading).score_le_distance first left right
    change (if reading first left ↔ reading first right then 0 else (1 / 2 : ℝ) ^ first) ≤ _ at lower
    rwa [if_neg different] at lower

/-- Enumerating the same tests in a different order preserves equivalence.
No order or cost preservation is needed for this zero-kernel result. -/
theorem enumerated_zero_iff {State : Type u} {Test : Type v}
    (reading : Test → State → Prop) (enumeration : Nat → Test)
    (covers : Function.Surjective enumeration) (left right : State) :
    (enumeratedTests (fun index => reading (enumeration index))).distance left right = 0 ↔
      ∀ test, reading test left ↔ reading test right := by
  rw [BudgetedObservations.distance_eq_zero_iff]
  constructor
  · intro same test
    obtain ⟨index, rfl⟩ := covers test
    exact same index
  · intro same index
    exact same (enumeration index)

end Mettapedia.GSLT.Logic
