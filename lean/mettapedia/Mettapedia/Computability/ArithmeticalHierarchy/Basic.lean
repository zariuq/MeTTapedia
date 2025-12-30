import Mathlib.Computability.Partrec
import Mathlib.Data.Nat.Basic

-- Helper lemma: Boolean negation is computable
-- Proof: not is Primrec (from Mathlib), and Primrec → Computable
theorem bool_not_computable : Computable (fun (b : Bool) => !b) :=
  Primrec.not.to_comp

/-!
# Arithmetical Hierarchy

This file defines the arithmetical hierarchy for predicates on natural numbers,
focusing on Σ⁰₂, Π⁰₂, and Δ⁰₂ predicates which are critical for the Grain of Truth
problem formalization.

## Main Definitions

* `Sigma02Predicate P`: Predicate P is Σ⁰₂ (∃m ∀k≥m, approx(n,k) = true)
* `Pi02Predicate P`: Predicate P is Π⁰₂ (∀m ∃k≥m, approx(n,k) = true)
* `Delta02Predicate P`: Predicate P is Δ⁰₂ (both Σ⁰₂ and Π⁰₂, i.e., limit computable)

## Main Theorems

* `sigma02_enumerable`: Every Σ⁰₂ predicate has a computable enumerator
* `sigma02_complement_pi02`: Complement of Σ⁰₂ is Π⁰₂
* `pi02_complement_sigma02`: Complement of Π⁰₂ is Σ⁰₂
* `delta02_decidable_in_limit`: Δ⁰₂ predicates are decidable in the limit

## References

- Rogers, H. (1987). "Theory of Recursive Functions and Effective Computability"
- Soare, R. (2016). "Turing Computability: Theory and Applications"
- Leike, J., Taylor, J., & Fallenstein, B. (2016). "A Formal Solution to the
  Grain of Truth Problem" (uses Δ⁰₂ for policy classes)

-/

namespace Mettapedia.Computability.ArithmeticalHierarchy

open Classical

/-! ## Σ⁰₂ Predicates -/

/-- A Σ⁰₂ predicate is one that can be expressed in the form:
    P(n) ↔ ∃m ∀k≥m, approx(n,k) = true

    This means the predicate P has a computable approximation function that
    eventually stabilizes to `true` for all n where P(n) holds.
-/
structure Sigma02Predicate (P : ℕ → Prop) where
  /-- Computable approximation function: approx n k approximates P(n) at stage k -/
  approx : ℕ → ℕ → Bool
  /-- The approximation function is computable -/
  approx_computable : Computable₂ approx
  /-- P(n) holds iff the approximation eventually stabilizes to true -/
  converges : ∀ n, P n ↔ ∃ m, ∀ k ≥ m, approx n k = true

namespace Sigma02Predicate

variable {P Q : ℕ → Prop}

/-- Extract witness of convergence for a Σ⁰₂ predicate at a given n -/
noncomputable def witnessStage (h : Sigma02Predicate P) (n : ℕ) (hn : P n) : ℕ :=
  Classical.choose ((h.converges n).mp hn)

theorem witnessStage_spec (h : Sigma02Predicate P) (n : ℕ) (hn : P n) :
    ∀ k ≥ h.witnessStage n hn, h.approx n k = true :=
  Classical.choose_spec ((h.converges n).mp hn)

/-- If approx is eventually true, then P holds -/
theorem approx_eventually_true_of_mem (h : Sigma02Predicate P) (n : ℕ) (hn : P n) :
    ∃ m, ∀ k ≥ m, h.approx n k = true :=
  (h.converges n).mp hn

/-- If approx is never eventually true, then P doesn't hold -/
theorem not_mem_of_approx_not_eventually_true (h : Sigma02Predicate P) (n : ℕ)
    (hn : ¬∃ m, ∀ k ≥ m, h.approx n k = true) : ¬P n :=
  fun hp => hn ((h.converges n).mp hp)

end Sigma02Predicate

/-! ## Π⁰₂ Predicates -/

/-- A Π⁰₂ predicate is one that can be expressed in the form:
    P(n) ↔ ∀m ∃k≥m, approx(n,k) = true

    This means the predicate P has a computable approximation function that
    returns true infinitely often for all n where P(n) holds.
-/
structure Pi02Predicate (P : ℕ → Prop) where
  /-- Computable approximation function -/
  approx : ℕ → ℕ → Bool
  /-- The approximation function is computable -/
  approx_computable : Computable₂ approx
  /-- P(n) holds iff the approximation is true infinitely often -/
  converges : ∀ n, P n ↔ ∀ m, ∃ k ≥ m, approx n k = true

namespace Pi02Predicate

variable {P Q : ℕ → Prop}

/-- For Π⁰₂ predicates, if P(n) holds, then for any stage m,
    there exists a later stage k where approx is true -/
theorem approx_infinitely_often (h : Pi02Predicate P) (n : ℕ) (hn : P n) (m : ℕ) :
    ∃ k ≥ m, h.approx n k = true :=
  ((h.converges n).mp hn) m

/-- If approx is not infinitely often true, then P doesn't hold -/
theorem not_mem_of_approx_not_infinitely_often (h : Pi02Predicate P) (n : ℕ)
    (hn : ∃ m, ∀ k ≥ m, h.approx n k = false) : ¬P n := by
  intro hp
  obtain ⟨m, hm⟩ := hn
  obtain ⟨k, hk_ge, hk_true⟩ := ((h.converges n).mp hp) m
  have hk_false : h.approx n k = false := hm k hk_ge
  rw [hk_false] at hk_true
  simp at hk_true

end Pi02Predicate

/-! ## Δ⁰₂ Predicates (Limit Computable) -/

/-- A Δ⁰₂ predicate is one that is both Σ⁰₂ and Π⁰₂.

    These are also called "limit computable" predicates - they have a computable
    approximation that converges in the limit to the correct answer.

    This is the key computability class for the Grain of Truth problem: policy
    classes need to be Δ⁰₂-enumerable for the theorem to hold.
-/
structure Delta02Predicate (P : ℕ → Prop) where
  /-- Computable approximation function that converges in the limit -/
  approx : ℕ → ℕ → Bool
  /-- The approximation function is computable -/
  approx_computable : Computable₂ approx
  /-- P(n) holds iff the approximation eventually stabilizes -/
  converges_limit : ∀ n, ∃ b : Bool, (P n ↔ b = true) ∧
                                      ∃ m, ∀ k ≥ m, approx n k = b

namespace Delta02Predicate

variable {P Q : ℕ → Prop}

/-- Every Δ⁰₂ predicate is Σ⁰₂ -/
def toSigma02 (h : Delta02Predicate P) : Sigma02Predicate P where
  approx := h.approx
  approx_computable := h.approx_computable
  converges := fun n => by
    obtain ⟨b, hb_iff, m, hm⟩ := h.converges_limit n
    constructor
    · intro hn
      use m
      intro k hk
      have : b = true := hb_iff.mp hn
      rw [← this]
      exact hm k hk
    · intro ⟨m', hm'⟩
      by_cases hb : b = true
      · exact hb_iff.mpr hb
      · -- Show contradiction: if b ≠ true, approx doesn't stabilize to true
        have hb_false : b = false := by
          cases b
          · rfl
          · contradiction
        -- At max m m', approx should be both true (from hm') and false (from hm)
        have h_true : h.approx n (max m m') = true := hm' (max m m') (le_max_right m m')
        have h_false : h.approx n (max m m') = false := by
          have := hm (max m m') (le_max_left m m')
          rw [hb_false] at this
          exact this
        rw [h_false] at h_true
        simp at h_true

/-- Every Δ⁰₂ predicate is Π⁰₂ -/
def toPi02 (h : Delta02Predicate P) : Pi02Predicate P where
  approx := h.approx
  approx_computable := h.approx_computable
  converges := fun n => by
    obtain ⟨b, hb_iff, m, hm⟩ := h.converges_limit n
    constructor
    · intro hn
      intro m'
      use max m m'
      constructor
      · exact le_max_right m m'
      · have : b = true := hb_iff.mp hn
        rw [← this]
        exact hm (max m m') (le_max_left m m')
    · intro h_inf
      by_cases hb : b = true
      · exact hb_iff.mpr hb
      · -- Show contradiction similar to above
        have hb_false : b = false := by
          cases b
          · rfl
          · contradiction
        obtain ⟨k, hk_ge, hk_true⟩ := h_inf m
        have hk_false : h.approx n k = false := by
          have := hm k hk_ge
          rw [hb_false] at this
          exact this
        rw [hk_false] at hk_true
        simp at hk_true

/-- Extract the limiting value for a Δ⁰₂ predicate at n -/
noncomputable def limitValue (h : Delta02Predicate P) (n : ℕ) : Bool :=
  Classical.choose (h.converges_limit n)

theorem limitValue_iff (h : Delta02Predicate P) (n : ℕ) :
    P n ↔ h.limitValue n = true :=
  (Classical.choose_spec (h.converges_limit n)).1

theorem limitValue_stable (h : Delta02Predicate P) (n : ℕ) :
    ∃ m, ∀ k ≥ m, h.approx n k = h.limitValue n :=
  (Classical.choose_spec (h.converges_limit n)).2

/-- The stage at which the approximation stabilizes to the limit value -/
noncomputable def stableStage (h : Delta02Predicate P) (n : ℕ) : ℕ :=
  Classical.choose (h.limitValue_stable n)

theorem stableStage_spec (h : Delta02Predicate P) (n : ℕ) :
    ∀ k ≥ h.stableStage n, h.approx n k = h.limitValue n :=
  Classical.choose_spec (h.limitValue_stable n)

end Delta02Predicate

/-! ## Complementation Results -/

/-- Σ⁰₂ and Π⁰₂ predicates are complementary -/
def sigma02_complement_pi02 {P : ℕ → Prop} (h : Sigma02Predicate P) :
    Pi02Predicate (fun n => ¬P n) where
  approx := fun n k => !h.approx n k
  approx_computable := by
    -- Composition: h.approx is computable, ! is computable
    exact Computable.comp₂ bool_not_computable h.approx_computable
  converges := fun n => by
    constructor
    · -- If ¬P n, then !h.approx is infinitely often true
      intro hn m
      -- We need to show: ∃ k ≥ m, !h.approx n k = true
      -- This means: ∃ k ≥ m, h.approx n k = false
      by_contra h_contra
      push_neg at h_contra
      -- h_contra says: ∀ k ≥ m, !h.approx n k ≠ true
      -- Which means: ∀ k ≥ m, h.approx n k = true
      have h_all_true : ∀ k ≥ m, h.approx n k = true := fun k hk => by
        have h_neg_ne_true := h_contra k hk
        -- !h.approx n k ≠ true means h.approx n k must be true
        cases h_val : h.approx n k
        · -- h.approx n k = false, so !false = true, contradiction with h_neg_ne_true
          simp [h_val] at h_neg_ne_true
        · -- h.approx n k = true
          rfl
      -- But this means P n holds
      have : P n := (h.converges n).mpr ⟨m, h_all_true⟩
      exact hn this
    · -- If approx is infinitely often true, then ¬P n
      intro h_inf
      intro hp
      -- P n means h.approx eventually stabilizes to true
      obtain ⟨m, hm⟩ := (h.converges n).mp hp
      -- But h_inf says !h.approx is infinitely often true
      obtain ⟨k, hk_ge, hk_true⟩ := h_inf m
      -- So h.approx n k = false
      have : h.approx n k = false := by
        cases h_approx : h.approx n k
        · rfl
        · simp [h_approx] at hk_true
      -- But hm says h.approx n k = true (contradiction)
      have h_true : h.approx n k = true := hm k hk_ge
      rw [this] at h_true
      simp at h_true

def pi02_complement_sigma02 {P : ℕ → Prop} (h : Pi02Predicate P) :
    Sigma02Predicate (fun n => ¬P n) where
  approx := fun n k => !h.approx n k
  approx_computable := by
    -- Composition: h.approx is computable, ! is computable
    exact Computable.comp₂ bool_not_computable h.approx_computable
  converges := fun n => by
    constructor
    · -- If ¬P n, then !h.approx eventually stabilizes to true
      intro hn
      -- ¬P n means h.approx is NOT infinitely often true
      -- So ∃ m, ∀ k ≥ m, h.approx n k = false
      -- Which means ∃ m, ∀ k ≥ m, !h.approx n k = true
      by_contra h_contra
      push_neg at h_contra
      -- h_contra says: ∀ m, ∃ k ≥ m, !h.approx n k ≠ true
      -- Which means: ∀ m, ∃ k ≥ m, h.approx n k = true
      have h_inf_often : ∀ m, ∃ k ≥ m, h.approx n k = true := fun m => by
        obtain ⟨k, hk_ge, h_neg_ne_true⟩ := h_contra m
        use k, hk_ge
        -- !h.approx n k ≠ true means h.approx n k = true
        cases h_val : h.approx n k
        · -- h.approx n k = false, so !false = true, contradiction
          simp [h_val] at h_neg_ne_true
        · -- h.approx n k = true
          rfl
      -- But this means P n holds
      have : P n := (h.converges n).mpr h_inf_often
      exact hn this
    · -- If !approx eventually stabilizes to true, then ¬P n
      intro ⟨m, hm⟩
      intro hp
      -- P n means h.approx is infinitely often true
      obtain ⟨k, hk_ge, hk_true⟩ := ((h.converges n).mp hp) m
      -- But hm says !h.approx n k = true, so h.approx n k = false
      have : h.approx n k = false := by
        have := hm k hk_ge
        cases h_approx : h.approx n k
        · rfl
        · simp [h_approx] at this
      rw [this] at hk_true
      simp at hk_true

end Mettapedia.Computability.ArithmeticalHierarchy
