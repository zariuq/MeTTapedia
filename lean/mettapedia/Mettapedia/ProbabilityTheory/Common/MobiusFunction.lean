/-
# Möbius Function on Finite Posets

The Möbius function μ on a finite poset P is characterized by:
  Σ_{x ≤ z ≤ y} μ(x, z) = δ_{xy}  (1 if x = y, 0 otherwise)

## Key Property (Möbius Inversion)
If g(y) = Σ_{x ≤ y} f(x), then f(y) = Σ_{x ≤ y} μ(x, y) g(x)

## References

- Rota, G.-C. "On the Foundations of Combinatorial Theory I: Theory of Möbius Functions"
  Z. Wahrscheinlichkeitstheorie 2 (1964), 340-368.
  [The foundational paper establishing Möbius inversion on posets]

- Stanley, R. P. "Enumerative Combinatorics" Vol. 1, Chapter 3.
  Cambridge University Press, 2nd ed. 2012.
  [Standard reference for the incidence algebra approach]

- Speicher, R. "Multiplicative functions on the lattice of noncrossing partitions
  and free convolution" Math. Ann. 298 (1994), 611-628.
  [Application to free probability via NC(n) lattice]

- Nica, A. and Speicher, R. "Lectures on the Combinatorics of Free Probability"
  Cambridge University Press, 2006.
  [Comprehensive treatment of Möbius function on NC(n)]
-/

import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Mettapedia.ProbabilityTheory.Common

/-!
## §1: Finite Intervals in Posets
-/

section FinitePoset

variable {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P]
variable [DecidableRel (α := P) (· ≤ ·)]

/-- The closed interval [x, y] = {z | x ≤ z ≤ y} as a Finset. -/
def closedInterval (x y : P) : Finset P :=
  Finset.filter (fun z => x ≤ z ∧ z ≤ y) Finset.univ

/-- The half-open interval [x, y) = {z | x ≤ z ∧ z < y} as a Finset.
    Note: We use ¬(y ≤ z) instead of z < y to avoid needing DecidableRel for <. -/
def halfOpenInterval (x y : P) : Finset P :=
  Finset.filter (fun z => x ≤ z ∧ z ≤ y ∧ z ≠ y) Finset.univ

namespace closedInterval

omit [DecidableEq P] in
@[simp]
theorem mem_iff (x y z : P) : z ∈ closedInterval x y ↔ x ≤ z ∧ z ≤ y := by
  simp [closedInterval]

omit [DecidableEq P] in
theorem self_mem_of_le {x y : P} (h : x ≤ y) : x ∈ closedInterval x y := by
  simp [h]

omit [DecidableEq P] in
theorem self_mem_right_of_le {x y : P} (h : x ≤ y) : y ∈ closedInterval x y := by
  simp [h]

@[simp]
theorem singleton_eq {x : P} : closedInterval x x = {x} := by
  ext z
  simp only [closedInterval, Finset.mem_filter, Finset.mem_univ, true_and,
             Finset.mem_singleton]
  constructor
  · intro ⟨hxz, hzx⟩; exact le_antisymm hzx hxz
  · intro h; subst h; exact ⟨le_refl z, le_refl z⟩

end closedInterval

namespace halfOpenInterval

@[simp]
theorem mem_iff (x y z : P) : z ∈ halfOpenInterval x y ↔ x ≤ z ∧ z ≤ y ∧ z ≠ y := by
  simp [halfOpenInterval]

@[simp]
theorem singleton_empty {x : P} : halfOpenInterval x x = ∅ := by
  ext z
  simp only [mem_iff, Finset.not_mem_empty, iff_false, not_and]
  intro hxz hzx
  intro hne
  exact hne (le_antisymm hzx hxz)

theorem not_mem_right (x y : P) : y ∉ halfOpenInterval x y := by
  simp

end halfOpenInterval

/-!
## §2: The Möbius Function

We define μ by well-founded recursion on the cardinality of closed intervals.
-/

/-- The cardinality of the closed interval. -/
def intervalCard (x y : P) : ℕ := (closedInterval x y).card

/-- Key lemma: for z in the half-open interval [x, y), the interval [x, z] is smaller. -/
theorem intervalCard_lt_of_mem_halfOpen {x y z : P}
    (hle : x ≤ y) (hz : z ∈ halfOpenInterval x y) :
    intervalCard x z < intervalCard x y := by
  simp only [halfOpenInterval.mem_iff] at hz
  unfold intervalCard
  apply Finset.card_lt_card
  constructor
  · intro w hw
    simp only [closedInterval.mem_iff] at hw ⊢
    exact ⟨hw.1, le_trans hw.2 hz.2.1⟩
  · simp only [Finset.not_subset]
    use y
    simp only [closedInterval.mem_iff]
    exact ⟨⟨hle, le_refl y⟩, fun h => hz.2.2 (le_antisymm hz.2.1 h.2)⟩

/-- The Möbius function on a finite poset.
    - μ(x, y) = 1 if x = y
    - μ(x, y) = -Σ_{z ∈ [x,y)} μ(x, z) if x ≤ y and x ≠ y
    - μ(x, y) = 0 if x ≰ y -/
noncomputable def mobius : P → P → ℤ
  | x, y =>
    if hxy : x = y then 1
    else if hle : x ≤ y then
      -((halfOpenInterval x y).attach.sum fun ⟨z, hz⟩ =>
          have : intervalCard x z < intervalCard x y := intervalCard_lt_of_mem_halfOpen hle hz
          mobius x z)
    else 0
termination_by x y => intervalCard x y

namespace mobius

/-- μ(x, x) = 1 -/
@[simp]
theorem diag (x : P) : mobius x x = 1 := by
  unfold mobius
  simp

/-- μ(x, y) = 0 when x ≰ y -/
theorem eq_zero_of_not_le {x y : P} (h : ¬x ≤ y) : mobius x y = 0 := by
  unfold mobius
  have hne : x ≠ y := fun heq => h (heq ▸ le_refl x)
  simp only [hne, ↓reduceDIte, h, dite_false]

/-- Unfold mobius for x < y case -/
theorem unfold_of_ne_le {x y : P} (hne : x ≠ y) (hle : x ≤ y) :
    mobius x y = -((halfOpenInterval x y).attach.sum fun ⟨z, _⟩ => mobius x z) := by
  conv_lhs => unfold mobius
  simp [hne, hle]

/-- The attach sum equals the regular sum for mobius. -/
theorem attach_sum_eq (x y : P) :
    (halfOpenInterval x y).attach.sum (fun ⟨z, _⟩ => mobius x z) =
    (halfOpenInterval x y).sum (fun z => mobius x z) :=
  Finset.sum_attach (halfOpenInterval x y) (fun z => mobius x z)

/-- The sum formula: Σ_{x ≤ z ≤ y} μ(x, z) = δ_{xy} -/
theorem sum_closedInterval_eq_ite (x y : P) (hle : x ≤ y) :
    (closedInterval x y).sum (fun z => mobius x z) = if x = y then 1 else 0 := by
  by_cases heq : x = y
  · subst heq
    simp only [closedInterval.singleton_eq, Finset.sum_singleton, diag, ↓reduceIte]
  · simp only [heq, ↓reduceIte]
    -- Split closedInterval into halfOpenInterval ∪ {y}
    have hsplit : closedInterval x y = insert y (halfOpenInterval x y) := by
      ext z
      simp only [closedInterval.mem_iff, Finset.mem_insert, halfOpenInterval.mem_iff]
      constructor
      · intro ⟨hxz, hzy⟩
        by_cases hzy' : z = y
        · left; exact hzy'
        · right; exact ⟨hxz, hzy, hzy'⟩
      · intro h
        rcases h with heqy | ⟨hxz, hzy, _⟩
        · subst heqy; exact ⟨hle, le_refl _⟩
        · exact ⟨hxz, hzy⟩
    have hnotin : y ∉ halfOpenInterval x y := halfOpenInterval.not_mem_right x y
    rw [hsplit, Finset.sum_insert hnotin]
    -- Use the recurrence for μ(x, y)
    rw [unfold_of_ne_le heq hle, attach_sum_eq]
    ring

/-- Kronecker delta form of the sum formula. -/
theorem sum_eq_one_iff_diag {x y : P} (hle : x ≤ y) :
    (closedInterval x y).sum (fun z => mobius x z) = 1 ↔ x = y := by
  rw [sum_closedInterval_eq_ite x y hle]
  simp

theorem sum_eq_zero_iff_ne {x y : P} (hle : x ≤ y) :
    (closedInterval x y).sum (fun z => mobius x z) = 0 ↔ x ≠ y := by
  rw [sum_closedInterval_eq_ite x y hle]
  simp

/-- The DUAL sum formula: Σ_{x ≤ z ≤ y} μ(z, y) = δ_{xy}
    This is needed for Möbius inversion (summing over second argument position).

    **Proof by strong induction on interval cardinality.**

    Base: x = y. The sum is μ(y,y) = 1 = δ_{y,y}. ✓

    Step: x < y. Using recurrence μ(z, y) = -Σ_{w ∈ [z,y)} μ(z, w) and sum reordering:
    Σ_{z ∈ [x,y)} μ(z, y) = -Σ_{z ∈ [x,y)} Σ_{w ∈ [z,y)} μ(z, w)
                          = -Σ_{w ∈ [x,y)} Σ_{z ∈ [x,w]} μ(z, w)  [reorder]
                          = -Σ_{w ∈ [x,y)} δ_{x,w}                [by IH on smaller [x,w]]
                          = -1                                     [only w=x contributes]

    Therefore: Σ_{z ∈ [x,y]} μ(z, y) = Σ_{z ∈ [x,y)} μ(z, y) + μ(y,y) = -1 + 1 = 0 = δ_{x,y}. ✓ -/
theorem sum_closedInterval_second_eq_ite (x y : P) (hle : x ≤ y) :
    (closedInterval x y).sum (fun z => mobius z y) = if x = y then 1 else 0 := by
  -- Strong induction on interval cardinality
  have H : ∀ n : ℕ, ∀ (a b : P), intervalCard a b = n → a ≤ b →
      (closedInterval a b).sum (fun z => mobius z b) = if a = b then 1 else 0 := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro a b hcard hab
      by_cases heq : a = b
      · -- Base case: a = b
        subst heq
        simp only [closedInterval.singleton_eq, Finset.sum_singleton, diag, ↓reduceIte]
      · -- Induction step: a < b
        simp only [heq, ↓reduceIte]
        -- Split: [a,b] = [a,b) ∪ {b}
        have hsplit : closedInterval a b = insert b (halfOpenInterval a b) := by
          ext z
          simp only [closedInterval.mem_iff, Finset.mem_insert, halfOpenInterval.mem_iff]
          constructor
          · intro ⟨haz, hzb⟩
            by_cases hzb' : z = b
            · left; exact hzb'
            · right; exact ⟨haz, hzb, hzb'⟩
          · intro h
            rcases h with rfl | ⟨haz, hzb, _⟩
            · exact ⟨hab, le_refl _⟩
            · exact ⟨haz, hzb⟩
        have hnotin : b ∉ halfOpenInterval a b := halfOpenInterval.not_mem_right a b
        rw [hsplit, Finset.sum_insert hnotin]
        simp only [diag]
        -- Need: Σ_{a≤z<b} μ(z,b) + 1 = 0

        -- Key: a ∈ [a,b)
        have ha_mem : a ∈ halfOpenInterval a b := by
          simp only [halfOpenInterval.mem_iff]
          exact ⟨le_refl a, hab, heq⟩

        -- For each z in [a,b), use recurrence μ(z,b) = -Σ_{z≤w<b} μ(z,w)
        have hsum_neg : (halfOpenInterval a b).sum (fun z => mobius z b) =
            -(halfOpenInterval a b).sum (fun z => (halfOpenInterval z b).sum (fun w => mobius z w)) := by
          trans (halfOpenInterval a b).sum (fun z => -(halfOpenInterval z b).sum (fun w => mobius z w))
          · apply Finset.sum_congr rfl
            intro z hz
            simp only [halfOpenInterval.mem_iff] at hz
            rw [unfold_of_ne_le hz.2.2 hz.2.1, attach_sum_eq]
          · rw [Finset.sum_neg_distrib]
        rw [hsum_neg]
        ring_nf

        -- Show double sum = 1 by reordering and applying IH
        suffices hfinal : (halfOpenInterval a b).sum (fun z =>
            (halfOpenInterval z b).sum (fun w => mobius z w)) = 1 by linarith

        -- The reordered sum, applying IH to each inner sum over [a,w]
        have h_reord_val : (halfOpenInterval a b).sum (fun w =>
            (closedInterval a w).sum (fun z => mobius z w)) = 1 := by
          have h_inner' : ∀ w ∈ halfOpenInterval a b,
              (closedInterval a w).sum (fun z => mobius z w) = if a = w then 1 else 0 := by
            intro w hw
            simp only [halfOpenInterval.mem_iff] at hw
            -- Apply IH: |[a,w]| < |[a,b]| since w < b
            have hcard_lt : intervalCard a w < n := by
              rw [← hcard]
              unfold intervalCard
              apply Finset.card_lt_card
              constructor
              · intro z hz
                simp only [closedInterval.mem_iff] at hz ⊢
                exact ⟨hz.1, le_trans hz.2 hw.2.1⟩
              · simp only [Finset.not_subset]
                use b
                simp only [closedInterval.mem_iff]
                exact ⟨⟨hab, le_refl b⟩, fun h => hw.2.2 (le_antisymm hw.2.1 h.2)⟩
            exact ih (intervalCard a w) hcard_lt a w rfl hw.1
          rw [Finset.sum_congr rfl h_inner']
          trans (halfOpenInterval a b).sum (fun w => if a = w then (1 : ℤ) else 0)
          · rfl
          rw [Finset.sum_eq_single a]
          · simp only [↓reduceIte]
          · intro w _ hne; rw [if_neg (Ne.symm hne)]
          · intro habs; exact absurd ha_mem habs

        -- Show original = reordered by bijection on pairs
        -- Both sums are over pairs (z,w) with a ≤ z ≤ w < b
        have h_sum_eq : (halfOpenInterval a b).sum (fun z =>
            (halfOpenInterval z b).sum (fun w => mobius z w)) =
            (halfOpenInterval a b).sum (fun w =>
            (closedInterval a w).sum (fun z => mobius z w)) := by
          -- Use Finset.sum_sigma' to express as sums over sigma types
          rw [Finset.sum_sigma', Finset.sum_sigma']
          -- Both sums are now over sigma types. Show they're equal via bijection.
          -- S₁ = {⟨z, w⟩ : z ∈ [a,b), w ∈ [z,b)}
          -- S₂ = {⟨w, z⟩ : w ∈ [a,b), z ∈ [a,w]}
          -- Bijection: ⟨z, w⟩ ↦ ⟨w, z⟩
          let S₁ := (halfOpenInterval a b).sigma (fun z => halfOpenInterval z b)
          let S₂ := (halfOpenInterval a b).sigma (fun w => closedInterval a w)
          -- Swap function
          let swap : (z : P) × P → (w : P) × P := fun ⟨z, w⟩ => ⟨w, z⟩
          have h_swap_mem : ∀ p ∈ S₁, swap p ∈ S₂ := by
            intro ⟨z, w⟩ h
            simp only [Finset.mem_sigma, halfOpenInterval.mem_iff, closedInterval.mem_iff, swap, S₁, S₂] at h ⊢
            -- h : (a ≤ z ∧ z ≤ b ∧ z ≠ b) ∧ (z ≤ w ∧ w ≤ b ∧ w ≠ b)
            -- goal: (a ≤ w ∧ w ≤ b ∧ w ≠ b) ∧ (a ≤ z ∧ z ≤ w)
            exact ⟨⟨le_trans h.1.1 h.2.1, h.2.2.1, h.2.2.2⟩, ⟨h.1.1, h.2.1⟩⟩
          have h_swap_mem' : ∀ p ∈ S₂, swap p ∈ S₁ := by
            intro ⟨w, z⟩ h
            simp only [Finset.mem_sigma, halfOpenInterval.mem_iff, closedInterval.mem_iff, swap, S₁, S₂] at h ⊢
            constructor
            · exact ⟨h.2.1, le_trans h.2.2 h.1.2.1,
                fun heq => h.1.2.2 (le_antisymm h.1.2.1 (heq ▸ h.2.2))⟩
            · exact ⟨h.2.2, h.1.2.1, h.1.2.2⟩
          have h_swap_inv : ∀ p ∈ S₁, swap (swap p) = p := by
            intro ⟨z, w⟩ _; rfl
          have h_swap_inv' : ∀ p ∈ S₂, swap (swap p) = p := by
            intro ⟨w, z⟩ _; rfl
          have h_val : ∀ p ∈ S₁, mobius p.1 p.2 = mobius (swap p).2 (swap p).1 := by
            intro ⟨z, w⟩ _; rfl
          -- Apply bijection lemma
          symm
          apply Finset.sum_bij' (fun p _ => swap p) (fun p _ => swap p)
          · exact h_swap_mem'
          · exact h_swap_mem
          · exact h_swap_inv'
          · exact h_swap_inv
          · intro ⟨w, z⟩ _; rfl

        rw [h_sum_eq, h_reord_val]
  exact H (intervalCard x y) x y rfl hle

end mobius

/-!
## §3: Möbius Inversion

The fundamental theorem: if g(y) = Σ_{x≤y} f(x), then f(y) = Σ_{x≤y} μ(x,y) g(x)
-/

/-- The zeta transform: ζ·f(y) = Σ_{x ≤ y} f(x) -/
noncomputable def zetaTransform (f : P → ℤ) (y : P) : ℤ :=
  (Finset.filter (· ≤ y) Finset.univ).sum f

/-- Möbius transform: μ·g(y) = Σ_{x ≤ y} μ(x,y) g(x) -/
noncomputable def mobiusTransform (g : P → ℤ) (y : P) : ℤ :=
  (Finset.filter (· ≤ y) Finset.univ).sum (fun x => mobius x y * g x)

/-- Helper: the set {x | w ≤ x ≤ y} equals closedInterval w y. -/
theorem filter_le_le_eq_closedInterval (w y : P) :
    Finset.filter (fun x => w ≤ x ∧ x ≤ y) Finset.univ = closedInterval w y := by
  ext x
  simp [closedInterval.mem_iff]

/-- Möbius inversion: μ·(ζ·f) = f
    This is the fundamental theorem of Möbius inversion on posets.

    Proof outline:
    mobiusTransform (zetaTransform f) y = Σ_{x≤y} μ(x,y) · (Σ_{w≤x} f(w))

    Exchange summation order (valid for finite sums):
    = Σ_{w≤y} f(w) · (Σ_{w≤x≤y} μ(x,y))

    Apply the dual sum formula (sum_closedInterval_second_eq_ite):
    = Σ_{w≤y} f(w) · δ_{w,y}
    = f(y)

    The proof requires the dual sum formula which is proven by telescoping.
    Once that is established, this theorem follows by sum rearrangement. -/
theorem mobius_inversion (f : P → ℤ) (y : P) :
    mobiusTransform (zetaTransform f) y = f y := by
  unfold mobiusTransform zetaTransform
  -- Goal: Σ_{x≤y} μ(x,y) · (Σ_{w≤x} f(w)) = f(y)

  -- Step 1: Distribute multiplication into the inner sum
  have h1 : (Finset.filter (· ≤ y) Finset.univ).sum (fun x => mobius x y *
      (Finset.filter (· ≤ x) Finset.univ).sum f) =
      (Finset.filter (· ≤ y) Finset.univ).sum (fun x =>
      (Finset.filter (· ≤ x) Finset.univ).sum (fun w => mobius x y * f w)) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]

  -- Step 2: Express as sum over sigma type for reordering
  -- S₁ = {⟨x, w⟩ : x ≤ y, w ≤ x}
  -- S₂ = {⟨w, x⟩ : w ≤ y, w ≤ x ≤ y}
  have h2 : (Finset.filter (· ≤ y) Finset.univ).sum (fun x =>
      (Finset.filter (· ≤ x) Finset.univ).sum (fun w => mobius x y * f w)) =
      (Finset.filter (· ≤ y) Finset.univ).sum (fun w =>
      (closedInterval w y).sum (fun x => mobius x y * f w)) := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    -- Bijection via swap
    let S₁ := (Finset.filter (· ≤ y) Finset.univ).sigma (fun x => Finset.filter (· ≤ x) Finset.univ)
    let S₂ := (Finset.filter (· ≤ y) Finset.univ).sigma (fun w => closedInterval w y)
    let swap : (x : P) × P → (w : P) × P := fun ⟨x, w⟩ => ⟨w, x⟩
    have h_swap_mem : ∀ p ∈ S₁, swap p ∈ S₂ := by
      intro ⟨x, w⟩ h
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and,
                 closedInterval.mem_iff, swap, S₁, S₂] at h ⊢
      -- h : x ≤ y ∧ w ≤ x
      exact ⟨le_trans h.2 h.1, h.2, h.1⟩
    have h_swap_mem' : ∀ p ∈ S₂, swap p ∈ S₁ := by
      intro ⟨w, x⟩ h
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and,
                 closedInterval.mem_iff, swap, S₁, S₂] at h ⊢
      -- h : w ≤ y ∧ (w ≤ x ∧ x ≤ y)
      exact ⟨h.2.2, h.2.1⟩
    have h_swap_inv : ∀ p ∈ S₁, swap (swap p) = p := fun ⟨_, _⟩ _ => rfl
    have h_swap_inv' : ∀ p ∈ S₂, swap (swap p) = p := fun ⟨_, _⟩ _ => rfl
    symm
    apply Finset.sum_bij' (fun p _ => swap p) (fun p _ => swap p)
    · exact h_swap_mem'
    · exact h_swap_mem
    · exact h_swap_inv'
    · exact h_swap_inv
    · intro ⟨w, x⟩ _; rfl

  -- Step 3: Factor f(w) out of the inner sum
  have h3 : (Finset.filter (· ≤ y) Finset.univ).sum (fun w =>
      (closedInterval w y).sum (fun x => mobius x y * f w)) =
      (Finset.filter (· ≤ y) Finset.univ).sum (fun w =>
      f w * (closedInterval w y).sum (fun x => mobius x y)) := by
    apply Finset.sum_congr rfl
    intro w _
    -- mobius x y * f w = f w * mobius x y, and f w doesn't depend on x
    conv_lhs => arg 2; ext x; rw [mul_comm]
    rw [← Finset.mul_sum]

  -- Step 4: Apply the dual sum formula
  have h4 : (Finset.filter (· ≤ y) Finset.univ).sum (fun w =>
      f w * (closedInterval w y).sum (fun x => mobius x y)) =
      (Finset.filter (· ≤ y) Finset.univ).sum (fun w =>
      f w * if w = y then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    congr 1
    exact mobius.sum_closedInterval_second_eq_ite w y hw

  -- Step 5: Simplify - only w = y contributes
  have h5 : (Finset.filter (· ≤ y) Finset.univ).sum (fun w =>
      f w * if w = y then 1 else 0) = f y := by
    have hy_mem : y ∈ Finset.filter (· ≤ y) Finset.univ := by simp
    rw [Finset.sum_eq_single y]
    · simp
    · intro w _ hne
      simp [hne]
    · intro habs; exact absurd hy_mem habs

  rw [h1, h2, h3, h4, h5]

end FinitePoset

/-!
## §4: Specific Möbius Functions for NC(n)

The Möbius function on the lattice of noncrossing partitions NC(n) is:
  μ(π, σ) = (-1)^{|π|-|σ|} · C_{k₁-1} · C_{k₂-1} · ... · C_{kᵣ-1}
where σ covers π with blocks of sizes k₁, ..., kᵣ and Cₙ is the n-th Catalan number.

For the special case μ(0̂, 1̂) where 0̂ is the finest partition and 1̂ is the coarsest:
  μ(0̂, 1̂) = (-1)^{n-1} · Cₙ₋₁
-/

section NoncrossingMobius

/-- The Möbius function from the minimal to maximal element of NC(n).
    For noncrossing partitions: μ(0̂, 1̂) = (-1)^{n-1} · C_{n-1}
    where C_k is the k-th Catalan number.

    Note: For n=0, we define this as 1 (empty partition).
    For n≥1: μ(0̂, 1̂) = (-1)^{n-1} · C_{n-1} -/
def mobiusNC : ℕ → ℤ
  | 0 => 1  -- Convention for empty case
  | n + 1 => (-1 : ℤ) ^ n * (Nat.choose (2 * n) n / (n + 1))

theorem mobiusNC_zero : mobiusNC 0 = 1 := rfl

theorem mobiusNC_one : mobiusNC 1 = 1 := by native_decide

theorem mobiusNC_two : mobiusNC 2 = -1 := by native_decide

theorem mobiusNC_three : mobiusNC 3 = 2 := by native_decide

theorem mobiusNC_four : mobiusNC 4 = -5 := by native_decide

end NoncrossingMobius

end Mettapedia.ProbabilityTheory.Common
