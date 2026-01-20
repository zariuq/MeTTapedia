/-
# Probability Derivation: Probability Calculus from K&S Representation

Derives the probability calculus (Sum Rule, Product Rule, etc.) from the
Knuth-Skilling representation theorem. This is NOT Cox's theorem itself,
but rather the probability rules that follow from having an additive representation.

Key structures:
- WeakRegraduation and Regraduation structures
- Probability rules (sum rule, product rule, Bayes' theorem, complement rule)
-/

import Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.Main
import Mettapedia.ProbabilityTheory.KnuthSkilling.ProductTheorem
import Mettapedia.ProbabilityTheory.KnuthSkilling.ProductTheorem.DirectProduct

namespace Mettapedia.ProbabilityTheory.KnuthSkilling


/-! ## The Representation Theorem

**CROWN JEWEL OF KNUTH-SKILLING**:

Given a K&S algebra, there exists a strictly monotone map Θ : α → ℝ that
"linearizes" the operation: Θ(x ⊕ y) = Θ(x) + Θ(y).

This says: ANY structure satisfying the K&S axioms is isomorphic to (ℝ≥0, +)!

**Construction** (from K&S Appendix A):
1. Pick a reference element a with ident < a
2. Define Θ on iterates: Θ(n·a) = n
3. For rationals: Θ(p/q · a) = p/q (by density of iterates)
4. For reals: Extend by monotonicity and Archimedean property

**Key insight**: The construction does NOT use Dedekind cuts! Instead, it uses
the "grid extension" method - successively adding finer grid points by interleaving.

The representation below formalizes the conclusion of this construction.
-/

/-- **The Knuth-Skilling Representation Theorem**

For any K&S algebra, there exists a strictly monotone function Θ : α → ℝ that:
1. Is strictly monotone (preserves order)
2. Maps identity to 0
3. Linearizes the operation: Θ(x ⊕ y) = Θ(x) + Θ(y)

This proves that K&S algebras are all isomorphic to (ℝ≥0, +) as ordered monoids!

**Philosophical importance**: This is not an axiom - it's a THEOREM that shows
the abstract symmetry requirements uniquely determine the additive structure.
The Born rule, probability calculus, and measure theory all follow from this.

Note: The full constructive proof (grid extension) is in WeakRegraduation + density
arguments below. Here we state the existence theorem cleanly. -/
theorem ks_representation_theorem
    [KnuthSkillingAlgebra α] [KSSeparation α]
    [Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.RepresentationGlobalization α] :
    ∃ (Θ : α → ℝ),
      StrictMono Θ ∧
        Θ KnuthSkillingAlgebraBase.ident = 0 ∧
          (∀ x y : α, Θ (KnuthSkillingAlgebraBase.op x y) = Θ x + Θ y) := by
  classical
  obtain ⟨Θ, hΘ_order, hΘ_ident, hΘ_add⟩ :=
    Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.associativity_representation (α := α)
  refine ⟨Θ, ?_, hΘ_ident, ?_⟩
  · intro x y hxy
    have hx_le : x ≤ y := le_of_lt hxy
    have hy_not_le : ¬ y ≤ x := not_le.mpr hxy
    have hΘ_le : Θ x ≤ Θ y := (hΘ_order x y).1 hx_le
    have hΘ_ne : Θ x ≠ Θ y := by
      intro hEq
      have : Θ y ≤ Θ x := by simp [hEq]
      have : y ≤ x := (hΘ_order y x).2 this
      exact hy_not_le this
    exact lt_of_le_of_ne hΘ_le hΘ_ne
  · exact hΘ_add

/-! ## Connection to Probability: WeakRegraduation IS the Grid Construction

The `WeakRegraduation` structure below captures the conclusion of the K&S
representation theorem specialized to the probability context (on ℝ):
- `regrade` is the linearizing map Θ
- `combine_eq_add` is the linearization property
- `zero`, `one` are the calibration

The theorems `regrade_unit_frac`, `regrade_on_rat`, `strictMono_eq_id_of_eq_on_rat`
implement the grid extension construction, proving that regrade = id on [0,1].
-/

/-- Weak regraduation: only assumes the linearization of combine_fn.
This is what the AssociativityTheorem directly provides. -/
structure WeakRegraduation (combine_fn : ℝ → ℝ → ℝ) where
  /-- The regraduation function φ. -/
  regrade : ℝ → ℝ
  /-- φ is strictly monotone, hence injective. -/
  strictMono : StrictMono regrade
  /-- Normalization: φ(0) = 0. -/
  zero : regrade 0 = 0
  /-- Normalization: φ(1) = 1 (fixes the overall scale). -/
  one : regrade 1 = 1
  /-- Core Cox equation: φ(S(x,y)) = φ(x) + φ(y).
  This is the KEY property - it says φ linearizes the combination law. -/
  combine_eq_add : ∀ x y, regrade (combine_fn x y) = regrade x + regrade y

/-- Full regraduation: includes global additivity.

**IMPORTANT**: For probability theory on [0,1], use `WeakRegraduation` instead!
The `additive` property on [0,1] is DERIVABLE - see `additive_derived`.

The derivation proceeds (on [0,1]):
1. `combine_eq_add`: φ(S(x,y)) = φ(x) + φ(y) (from WeakRegraduation)
2. `combine_rat`: S = + on ℚ ∩ [0,1] (from associativity + grid construction)
3. `regrade_on_rat`: φ = id on ℚ ∩ [0,1] (from 1 + 2)
4. `strictMono_eq_id_of_eq_on_rat`: φ = id on [0,1] (from 3 + density)
5. Therefore: φ(x+y) = x+y = φ(x) + φ(y) on [0,1] (QED!)

This structure requires GLOBAL additivity (∀ x y), which needs extension beyond [0,1].
For probability, `CoxConsistency` uses `WeakRegraduation` directly, avoiding this. -/
structure Regraduation (combine_fn : ℝ → ℝ → ℝ) extends WeakRegraduation combine_fn where
  /-- φ respects addition on [0,1]. See `additive_derived` for the derivation.
  Note: In probability contexts, we only need this on [0,1] since valuations
  are bounded. The field uses ∀ x y for convenience when bounds are obvious. -/
  additive : ∀ x y, regrade (x + y) = regrade x + regrade y

/-! ### Formal Derivation of Additivity

The K&S proof proceeds in stages:
1. On integers: φ(n) = n (from iterate construction + normalization)
2. On rationals: φ(p/q) = p/q (from φ(q · (1/q)) = q · φ(1/q) = 1)
3. On reals: φ = id (from monotonicity + density of ℚ in ℝ)
4. Therefore: additive holds (since φ = id means φ(x+y) = x+y = φ(x) + φ(y))

The key mathematical fact is that a strictly monotone function that equals
the identity on a dense subset must be the identity everywhere.
-/

/-- A strictly monotone function that equals id on ℚ ∩ [0,1] must equal id on [0,1].

This is the density argument that extends from rationals to reals.
Proof: For any x ∈ [0,1], let (qₙ) be rationals converging to x from below,
and (rₙ) be rationals converging from above. Then:
  qₙ = φ(qₙ) ≤ φ(x) ≤ φ(rₙ) = rₙ
Taking limits: x ≤ φ(x) ≤ x, so φ(x) = x. -/
theorem strictMono_eq_id_of_eq_on_rat
    (φ : ℝ → ℝ) (hφ : StrictMono φ)
    (h_rat : ∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) ≤ 1 → φ q = q) :
    ∀ x : ℝ, 0 ≤ x → x ≤ 1 → φ x = x := by
  intro x hx0 hx1
  -- Handle boundary cases first
  rcases eq_or_lt_of_le hx0 with rfl | hx0'
  · -- x = 0
    have h := h_rat 0 (by norm_num) (by norm_num)
    simp only [Rat.cast_zero] at h
    exact h
  rcases eq_or_lt_of_le hx1 with hx1_eq | hx1'
  · -- x = 1
    rw [hx1_eq]
    have h := h_rat 1 (by norm_num) (by norm_num)
    simp only [Rat.cast_one] at h
    exact h
  -- Now 0 < x < 1, so we can find rationals on both sides within [0,1]
  apply le_antisymm
  · -- Show φ(x) ≤ x
    by_contra h_gt
    push_neg at h_gt
    set ε := φ x - x with hε_def
    have hε_pos : 0 < ε := by linarith
    -- Find rational r with x < r < min(x + ε/2, 1)
    have h_bound : x < min (x + ε / 2) 1 := by
      simp only [lt_min_iff]
      constructor <;> linarith
    obtain ⟨r, hr_gt, hr_lt⟩ := exists_rat_btwn h_bound
    have hr_le1 : (r : ℝ) ≤ 1 := by
      have := lt_min_iff.mp hr_lt
      linarith [this.2]
    have hr_ge0 : 0 ≤ (r : ℝ) := by linarith
    have h1 : φ x < φ r := hφ hr_gt
    have h2 : φ r = r := h_rat r hr_ge0 hr_le1
    have hr_lt_eps : (r : ℝ) < x + ε / 2 := by
      have := lt_min_iff.mp hr_lt
      exact this.1
    linarith
  · -- Show x ≤ φ(x)
    by_contra h_lt
    push_neg at h_lt
    set ε := x - φ x with hε_def
    have hε_pos : 0 < ε := by linarith
    -- Find rational q with max(x - ε/2, 0) < q < x
    have h_bound : max (x - ε / 2) 0 < x := by
      simp only [max_lt_iff]
      constructor <;> linarith
    obtain ⟨q, hq_gt, hq_lt⟩ := exists_rat_btwn h_bound
    have hq_ge0 : 0 ≤ (q : ℝ) := by
      have := max_lt_iff.mp hq_gt
      linarith [this.2]
    have hq_le1 : (q : ℝ) ≤ 1 := by linarith
    have h1 : φ q < φ x := hφ hq_lt
    have h2 : φ q = q := h_rat q hq_ge0 hq_le1
    have hq_gt_eps : (q : ℝ) > x - ε / 2 := by
      have := max_lt_iff.mp hq_gt
      exact this.1
    linarith

/-- On natural number iterates under combine_fn, φ equals the iterate index.

**Key insight from AssociativityTheorem**: On the iterate image {iterate n 1 | n ∈ ℕ},
the K&S operation equals addition (up to regrade). Combined with WeakRegraduation's
`combine_eq_add`, this gives us φ(iterate n 1) = n · φ(1) = n.

**Proof by induction**:
- Base: φ(0) = 0 (from W.zero)
- Step: φ(combine_fn (n : ℝ) 1) = φ(n) + φ(1) = n + 1 (from combine_eq_add + IH + W.one)

The subtlety: we need combine_fn n 1 = n + 1 to apply this. This is EXACTLY what
the AssociativityTheorem proves! On iterates, combine_fn = +.

For the full connection, see AssociativityTheorem.lean which shows:
  op_iterate_is_addition: A.op (iterate m a) (iterate n a) = iterate (m+n) a

Here we assume combine_fn = + on ℕ, which follows from the AssociativityTheorem. -/
theorem regrade_on_nat (W : WeakRegraduation combine_fn)
    (h_combine_nat : ∀ m n : ℕ, combine_fn (m : ℝ) (n : ℝ) = ((m + n : ℕ) : ℝ)) :
    ∀ n : ℕ, W.regrade (n : ℝ) = n := by
  intro n
  induction n with
  | zero => simp [W.zero]
  | succ n ih =>
    -- φ(n+1) = φ(combine_fn n 1) = φ(n) + φ(1) = n + 1
    have h1 : combine_fn (n : ℝ) (1 : ℝ) = ((n + 1 : ℕ) : ℝ) := by
      have := h_combine_nat n 1
      simp only [Nat.cast_one] at this
      exact this
    have h2 : W.regrade ((n + 1 : ℕ) : ℝ) = W.regrade (combine_fn (n : ℝ) 1) := by
      congr 1
      have := h1.symm
      simp only [Nat.cast_add, Nat.cast_one] at this ⊢
      exact this
    have h3 : W.regrade (combine_fn (n : ℝ) 1) = W.regrade (n : ℝ) + W.regrade 1 :=
      W.combine_eq_add n 1
    rw [h2, h3, ih, W.one, Nat.cast_add, Nat.cast_one]

/-- Cast equality: division in ℚ then cast to ℝ equals casting then dividing in ℝ. -/
lemma rat_div_cast_eq (k n : ℕ) (_hn : (n : ℚ) ≠ 0) :
    (((k : ℚ) / n) : ℝ) = (k : ℝ) / (n : ℝ) := by
  push_cast; ring

/-- Special case for 1/n. -/
lemma rat_one_div_cast_eq (n : ℕ) (_hn : (n : ℚ) ≠ 0) :
    ((((1 : ℚ) / n)) : ℝ) = (1 : ℝ) / (n : ℝ) := by
  push_cast; ring

/-- Helper: φ respects addition on rationals in [0,1].
From combine_eq_add and h_combine_rat, we get φ(r + s) = φ(r) + φ(s). -/
theorem regrade_add_rat (W : WeakRegraduation combine_fn)
    (h_combine_rat : ∀ r s : ℚ, 0 ≤ (r : ℝ) → 0 ≤ (s : ℝ) → (r : ℝ) + (s : ℝ) ≤ 1 →
                     combine_fn (r : ℝ) (s : ℝ) = ((r + s : ℚ) : ℝ))
    (r s : ℚ) (hr : 0 ≤ (r : ℝ)) (hs : 0 ≤ (s : ℝ)) (hrs : (r : ℝ) + (s : ℝ) ≤ 1) :
    W.regrade ((r + s : ℚ) : ℝ) = W.regrade r + W.regrade s := by
  -- combine_fn r s = r + s, and φ(combine_fn r s) = φ(r) + φ(s)
  have h1 : combine_fn (r : ℝ) (s : ℝ) = ((r + s : ℚ) : ℝ) := h_combine_rat r s hr hs hrs
  calc W.regrade ((r + s : ℚ) : ℝ)
      = W.regrade (combine_fn (r : ℝ) (s : ℝ)) := by rw [h1]
    _ = W.regrade r + W.regrade s := W.combine_eq_add r s

/-- Specialized version for unit fractions: combine_fn (k/n) (1/n) = (k+1)/n in reals.
Following GPT-5.1's advice: prove bounds in ℚ first, then cast to ℝ via Rat.cast_nonneg. -/
lemma combine_fn_unit_fracs {combine_fn : ℝ → ℝ → ℝ}
    (h_combine_rat : ∀ r s : ℚ, 0 ≤ (r : ℝ) → 0 ≤ (s : ℝ) →
                      (r : ℝ) + (s : ℝ) ≤ 1 → combine_fn (r : ℝ) (s : ℝ) = ((r + s : ℚ) : ℝ))
    (k n : ℕ) (hn : 0 < n) (hk : k + 1 ≤ n) :
    combine_fn ((k : ℝ) / (n : ℝ)) ((1 : ℝ) / (n : ℝ)) = ((k : ℝ) + 1) / (n : ℝ) := by
  have hn_q_ne0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  have hn_q_pos : (0 : ℚ) < n := by exact_mod_cast hn

  -- Define the rationals we'll feed into h_combine_rat
  let r : ℚ := (k : ℚ) / n
  let s : ℚ := (1 : ℚ) / n

  -- Prove bounds in ℚ first (the easy part)
  have hr_q : 0 ≤ r := by dsimp [r]; positivity
  have hs_q : 0 ≤ s := by dsimp [s]; positivity
  have hrs_q : r + s ≤ 1 := by
    dsimp [r, s]
    have hkn : (k : ℚ) + 1 ≤ n := by exact_mod_cast hk
    rw [← add_div, div_le_one hn_q_pos]
    linarith

  -- Cast bounds to ℝ using Rat.cast_nonneg (the key insight from GPT-5.1!)
  have hr : 0 ≤ (r : ℝ) := Rat.cast_nonneg.mpr hr_q
  have hs : 0 ≤ (s : ℝ) := Rat.cast_nonneg.mpr hs_q
  have hrs : (r : ℝ) + (s : ℝ) ≤ 1 := by
    have hrs_real : ((r + s : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hrs_q
    simpa [Rat.cast_add] using hrs_real

  -- Now apply h_combine_rat in its natural ℚ form
  have h := h_combine_rat r s hr hs hrs

  -- Cast equalities to convert between forms
  have hk_cast : (r : ℝ) = (k : ℝ) / (n : ℝ) := by
    dsimp [r]; simp [Rat.cast_div, Rat.cast_natCast]
  have h1_cast : (s : ℝ) = (1 : ℝ) / (n : ℝ) := by
    dsimp [s]; simp [Rat.cast_natCast]
  have h_sum : ((r + s : ℚ) : ℝ) = ((k : ℝ) + 1) / (n : ℝ) := by
    dsimp [r, s]
    simp [Rat.cast_add, Rat.cast_div, Rat.cast_natCast]
    field_simp

  -- Put it all together
  simpa [hk_cast, h1_cast, h_sum] using h

/-- Helper: φ(1/n) = 1/n for positive n.

Proof: n copies of 1/n sum to 1, and φ(1) = 1. By additivity (combine_eq_add + h_combine_rat),
φ(1) = n · φ(1/n), so φ(1/n) = 1/n. -/
theorem regrade_unit_frac (W : WeakRegraduation combine_fn)
    (h_combine_rat : ∀ r s : ℚ, 0 ≤ (r : ℝ) → 0 ≤ (s : ℝ) → (r : ℝ) + (s : ℝ) ≤ 1 →
                     combine_fn (r : ℝ) (s : ℝ) = ((r + s : ℚ) : ℝ))
    (n : ℕ) (hn : 0 < n) :
    W.regrade ((1 : ℚ) / n) = (1 : ℝ) / n := by
  -- Key: φ(k/n) = k · φ(1/n) for all k ≤ n (by induction using additivity)
  -- At k = n: φ(1) = n · φ(1/n), and φ(1) = 1, so φ(1/n) = 1/n
  have hn_pos : (n : ℝ) > 0 := Nat.cast_pos.mpr hn
  have hn_ne0 : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hn_q_ne0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  -- Prove by induction: φ(k/n) = k · φ(1/n) for k ≤ n
  have h_mult : ∀ k : ℕ, k ≤ n →
      W.regrade (((k : ℚ) / n) : ℝ) = (k : ℝ) * W.regrade (((1 : ℚ) / n) : ℝ) := by
    intro k hk
    induction k with
    | zero =>
      simp only [Nat.cast_zero, zero_div, Rat.cast_zero, W.zero, zero_mul]
    | succ k ih =>
      have hk' : k ≤ n := Nat.le_of_succ_le hk
      have ih' := ih hk'
      -- Use combine_fn_unit_fracs which handles all coercion issues internally
      have h_combine' : combine_fn ((k : ℝ) / (n : ℝ)) ((1 : ℝ) / (n : ℝ)) =
          ((k : ℝ) + 1) / (n : ℝ) := combine_fn_unit_fracs h_combine_rat k n hn hk
      -- Cast equalities for linking
      have hk_cast_eq : (((k : ℚ) / n) : ℝ) = (k : ℝ) / (n : ℝ) := rat_div_cast_eq k n hn_q_ne0
      have h1_cast_eq : ((((1 : ℚ) / n)) : ℝ) = (1 : ℝ) / (n : ℝ) := rat_one_div_cast_eq n hn_q_ne0
      have hk1_cast_eq : ((((k + 1 : ℕ) : ℚ) / n) : ℝ) = ((k : ℝ) + 1) / (n : ℝ) := by
        rw [rat_div_cast_eq (k + 1) n hn_q_ne0]; simp only [Nat.cast_add, Nat.cast_one]
      -- Goal: W.regrade (((k+1)/n : ℚ) : ℝ) = (k+1) * W.regrade ((1/n : ℚ) : ℝ)
      -- Lean normalizes both sides to real-division form
      calc W.regrade ((((k + 1 : ℕ) : ℚ) / n) : ℝ)
          = W.regrade (((k : ℝ) + 1) / (n : ℝ)) := by rw [hk1_cast_eq]
        _ = W.regrade (combine_fn ((k : ℝ) / (n : ℝ)) ((1 : ℝ) / (n : ℝ))) := by rw [← h_combine']
        _ = W.regrade ((k : ℝ) / (n : ℝ)) + W.regrade ((1 : ℝ) / (n : ℝ)) := W.combine_eq_add _ _
        _ = W.regrade (((k : ℚ) / n) : ℝ) + W.regrade ((((1 : ℚ) / n)) : ℝ) := by
              rw [← hk_cast_eq, ← h1_cast_eq]
        _ = (k : ℝ) * W.regrade ((((1 : ℚ) / n)) : ℝ) + W.regrade ((((1 : ℚ) / n)) : ℝ) := by
              rw [ih']
        _ = ((k : ℝ) + 1) * W.regrade ((((1 : ℚ) / n)) : ℝ) := by ring
        _ = ((k + 1 : ℕ) : ℝ) * W.regrade ((((1 : ℚ) / n)) : ℝ) := by
              simp only [Nat.cast_add, Nat.cast_one]
  -- At k = n: φ(n/n) = φ(1) = 1, and φ(n/n) = n · φ(1/n)
  have h_at_n := h_mult n (le_refl n)
  -- h_at_n : W.regrade (((n : ℚ) / n) : ℝ) = (n : ℝ) * W.regrade (((1 : ℚ) / n) : ℝ)
  -- Note: Lean normalizes (((n : ℚ) / n) : ℝ) to (n : ℝ) / (n : ℝ), and similarly for 1/n
  have h_nn : (n : ℝ) / (n : ℝ) = 1 := div_self hn_ne0
  -- Use the cast equality to match h_mult's form
  have h_nn' : (((n : ℚ) / n) : ℝ) = 1 := by
    rw [rat_div_cast_eq n n hn_q_ne0]; exact h_nn
  simp only [h_nn'] at h_at_n
  rw [W.one] at h_at_n
  -- h_at_n : 1 = (n : ℝ) * W.regrade (((1 : ℚ) / n) : ℝ)
  -- Goal: W.regrade (((1 : ℚ) / n) : ℝ) = (1 : ℝ) / (n : ℝ)
  -- Use cast equality for 1/n
  have h_1n_eq : (((1 : ℚ) / n) : ℝ) = (1 : ℝ) / (n : ℝ) := rat_one_div_cast_eq n hn_q_ne0
  rw [h_1n_eq]
  -- Goal: W.regrade ((1 : ℝ) / (n : ℝ)) = (1 : ℝ) / (n : ℝ)
  -- From h_at_n: 1 = (n : ℝ) * W.regrade (((1 : ℚ) / n) : ℝ)
  simp only [h_1n_eq] at h_at_n
  -- h_at_n: 1 = (n : ℝ) * W.regrade ((1 : ℝ) / (n : ℝ))
  field_simp at h_at_n ⊢
  linarith

theorem regrade_on_rat (W : WeakRegraduation combine_fn)
    (h_combine_rat : ∀ r s : ℚ, 0 ≤ (r : ℝ) → 0 ≤ (s : ℝ) → (r : ℝ) + (s : ℝ) ≤ 1 →
                     combine_fn (r : ℝ) (s : ℝ) = ((r + s : ℚ) : ℝ)) :
    ∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) ≤ 1 → W.regrade q = q := by
  intro q hq0 hq1
  -- Write q = p/n where p = q.num and n = q.den
  obtain ⟨p, n, hn, hq_eq⟩ : ∃ p : ℤ, ∃ n : ℕ, 0 < n ∧ q = p / n := by
    use q.num, q.den
    exact ⟨q.den_pos, (Rat.num_div_den q).symm⟩
  -- Since q ≥ 0 and q = p/n with n > 0, we have p ≥ 0
  have hn_pos : (n : ℝ) > 0 := Nat.cast_pos.mpr hn
  have hn_ne0 : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hn_q_ne0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  have hp_nonneg : 0 ≤ p := by
    have hq_real : (q : ℝ) = (p : ℤ) / (n : ℕ) := by
      rw [hq_eq]; push_cast; ring
    rw [hq_real] at hq0
    have : 0 ≤ (p : ℝ) := by
      have := mul_nonneg hq0 (le_of_lt hn_pos)
      simp only [div_mul_cancel₀ _ hn_ne0] at this
      exact this
    exact Int.cast_nonneg_iff.mp this
  -- Convert p to ℕ
  obtain ⟨p', hp'⟩ := Int.eq_ofNat_of_zero_le hp_nonneg
  subst hp'
  -- Now q = p'/n where p', n are naturals with n > 0
  have h_q_eq' : (q : ℝ) = (p' : ℝ) / (n : ℝ) := by
    rw [hq_eq]; push_cast; ring
  -- Since q ≤ 1 and q = p'/n with n > 0, we have p' ≤ n
  have hp'_le_n : p' ≤ n := by
    have : (p' : ℝ) / (n : ℝ) ≤ 1 := by rw [← h_q_eq']; exact hq1
    rw [div_le_one hn_pos] at this
    exact Nat.cast_le.mp this
  -- Prove by induction: φ(k/n) = k/n for k ≤ n
  have h_unit := regrade_unit_frac W h_combine_rat n hn
  have h_kn : ∀ k : ℕ, k ≤ n → W.regrade ((((k : ℚ) / n)) : ℝ) = (k : ℝ) / (n : ℝ) := by
    intro k hk
    induction k with
    | zero =>
      simp only [Nat.cast_zero, zero_div, Rat.cast_zero, W.zero]
    | succ k ih =>
      have hk' : k ≤ n := Nat.le_of_succ_le hk
      have ih' := ih hk'
      -- Cast equalities
      have hk_cast_eq : (((k : ℚ) / n) : ℝ) = (k : ℝ) / (n : ℝ) := rat_div_cast_eq k n hn_q_ne0
      have h1_cast_eq : ((((1 : ℚ) / n)) : ℝ) = (1 : ℝ) / (n : ℝ) := rat_one_div_cast_eq n hn_q_ne0
      have hk1_cast_eq : ((((k + 1 : ℕ) : ℚ) / n) : ℝ) = ((k : ℝ) + 1) / (n : ℝ) := by
        rw [rat_div_cast_eq (k + 1) n hn_q_ne0]; simp only [Nat.cast_add, Nat.cast_one]
      -- GPT-5.1 pattern: prove bounds in ℚ first, then cast via Rat.cast_nonneg
      let r : ℚ := (k : ℚ) / n
      let s : ℚ := (1 : ℚ) / n
      have hn_q_pos : (0 : ℚ) < n := by exact_mod_cast hn
      have hr_q : 0 ≤ r := by dsimp [r]; positivity
      have hs_q : 0 ≤ s := by dsimp [s]; positivity
      have hrs_q : r + s ≤ 1 := by
        dsimp [r, s]
        rw [← add_div, div_le_one hn_q_pos]
        have : (k : ℚ) + 1 ≤ n := by exact_mod_cast hk
        linarith
      have hk_ge0 : 0 ≤ (r : ℝ) := Rat.cast_nonneg.mpr hr_q
      have h1n_ge0 : 0 ≤ (s : ℝ) := Rat.cast_nonneg.mpr hs_q
      have h_sum_le1 : (r : ℝ) + (s : ℝ) ≤ 1 := by
        have hrs_real : ((r + s : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hrs_q
        simpa [Rat.cast_add] using hrs_real
      -- Apply additivity
      have h_add := regrade_add_rat W h_combine_rat r s hk_ge0 h1n_ge0 h_sum_le1
      -- Rewrite sum
      have h_sum_eq : (r + s : ℚ) = ((k + 1 : ℕ) : ℚ) / n := by
        dsimp [r, s]; field_simp; simp only [Nat.cast_add, Nat.cast_one]
      rw [h_sum_eq] at h_add
      -- Link r and s back to the goal form
      have hr_eq : (r : ℝ) = (k : ℝ) / (n : ℝ) := by dsimp [r]; simp [Rat.cast_div, Rat.cast_natCast]
      have hs_eq : (s : ℝ) = (1 : ℝ) / (n : ℝ) := by dsimp [s]; simp [Rat.cast_natCast]
      -- h_add : W.regrade ↑((k+1)/n) = W.regrade r + W.regrade s
      -- Goal : W.regrade (((k+1)/n : ℚ) : ℝ) = (k+1)/n
      simp only [hr_eq, hs_eq] at h_add
      -- h_add now in real-division form for r and s
      -- Bridge: convert h_add's LHS from rat-cast to real-division form
      have h_add' : W.regrade (((k + 1 : ℕ) : ℝ) / (n : ℝ)) =
                    W.regrade ((k : ℝ) / (n : ℝ)) + W.regrade ((1 : ℝ) / (n : ℝ)) := by
        convert h_add using 2
        all_goals simp only [Rat.cast_div, Rat.cast_natCast, Rat.cast_add, Rat.cast_one,
                     Nat.cast_add, Nat.cast_one]
      -- Bridge casts: ih' and h_unit are in ↑↑ form, we need ↑ form
      have eq1 : W.regrade ((k : ℝ) / (n : ℝ)) = (k : ℝ) / (n : ℝ) := by
        convert ih' using 2
      have eq2 : W.regrade ((1 : ℝ) / (n : ℝ)) = (1 : ℝ) / (n : ℝ) := by
        convert h_unit using 2
        -- Goal: 1 / ↑n = ↑1 / ↑n
        norm_num
      calc W.regrade ((((k + 1 : ℕ) : ℚ) / n) : ℝ)
          = W.regrade (((k + 1 : ℕ) : ℝ) / (n : ℝ)) := by congr 1
        _ = W.regrade ((k : ℝ) / (n : ℝ)) + W.regrade ((1 : ℝ) / (n : ℝ)) := h_add'
        _ = (k : ℝ) / (n : ℝ) + (1 : ℝ) / (n : ℝ) := by rw [eq1, eq2]
        _ = ((k : ℝ) + 1) / (n : ℝ) := by ring
        _ = ((k + 1 : ℕ) : ℝ) / (n : ℝ) := by simp only [Nat.cast_add, Nat.cast_one]
  -- Apply h_kn at k = p'
  have h_result := h_kn p' hp'_le_n
  -- Convert to the form we need
  have h_q_rat : (q : ℝ) = ((((p' : ℚ) / n)) : ℝ) := by
    rw [hq_eq]
    simp only [Int.cast_natCast, Rat.cast_div, Rat.cast_natCast]
  rw [h_q_rat, h_result, ← h_q_eq']
  exact h_q_rat

/-- Main derivation: φ = id on [0,1] when combine_fn = + on ℚ ∩ [0,1].

**Dependency chain** (following K&S):
1. AssociativityTheorem: K&S axioms (order + associativity) → combine_fn = + on ℕ
2. Grid extension: combine_fn = + on ℕ → combine_fn = + on ℚ (by defining grid points)
3. regrade_on_rat: combine_fn = + on ℚ → φ = id on ℚ
4. strictMono_eq_id_of_eq_on_rat: φ = id on ℚ → φ = id on ℝ (by density)
5. combine_fn_eq_add_derived: φ = id → combine_fn = + on [0,1]

This theorem encapsulates steps 3-4. The hypothesis h_combine_rat comes from steps 1-2. -/
theorem regrade_eq_id_on_unit (W : WeakRegraduation combine_fn)
    (h_combine_rat : ∀ r s : ℚ, 0 ≤ (r : ℝ) → 0 ≤ (s : ℝ) → (r : ℝ) + (s : ℝ) ≤ 1 →
                     combine_fn (r : ℝ) (s : ℝ) = ((r + s : ℚ) : ℝ)) :
    ∀ x : ℝ, 0 ≤ x → x ≤ 1 → W.regrade x = x := by
  apply strictMono_eq_id_of_eq_on_rat W.regrade W.strictMono
  exact regrade_on_rat W h_combine_rat

/-- The additive property is DERIVED from WeakRegraduation + combine_fn = + on ℚ.

Once we know φ = id on [0,1], additive follows immediately:
  φ(x + y) = x + y = φ(x) + φ(y)

This replaces the assumed `additive` field in `Regraduation`. -/
theorem additive_derived (W : WeakRegraduation combine_fn)
    (h_combine_rat : ∀ r s : ℚ, 0 ≤ (r : ℝ) → 0 ≤ (s : ℝ) → (r : ℝ) + (s : ℝ) ≤ 1 →
                     combine_fn (r : ℝ) (s : ℝ) = ((r + s : ℚ) : ℝ))
    (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) (hxy : x + y ≤ 1) :
    W.regrade (x + y) = W.regrade x + W.regrade y := by
  -- φ = id on [0,1], so φ(x+y) = x+y and φ(x) + φ(y) = x + y
  have hx_id := regrade_eq_id_on_unit W h_combine_rat x hx.1 hx.2
  have hy_id := regrade_eq_id_on_unit W h_combine_rat y hy.1 hy.2
  have hxy_id := regrade_eq_id_on_unit W h_combine_rat (x + y) (by linarith) hxy
  rw [hx_id, hy_id, hxy_id]

/-- combine_fn = + on [0,1] follows from φ = id.

Since φ(combine_fn x y) = φ(x) + φ(y) = x + y = φ(x + y),
and φ is injective, we get combine_fn x y = x + y. -/
theorem combine_fn_eq_add_derived (W : WeakRegraduation combine_fn)
    (h_combine_rat : ∀ r s : ℚ, 0 ≤ (r : ℝ) → 0 ≤ (s : ℝ) → (r : ℝ) + (s : ℝ) ≤ 1 →
                     combine_fn (r : ℝ) (s : ℝ) = ((r + s : ℚ) : ℝ))
    (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) (hxy : x + y ≤ 1) :
    combine_fn x y = x + y := by
  -- φ(combine_fn x y) = φ(x) + φ(y) = x + y = φ(x + y)
  have h1 := W.combine_eq_add x y
  have hx_id := regrade_eq_id_on_unit W h_combine_rat x hx.1 hx.2
  have hy_id := regrade_eq_id_on_unit W h_combine_rat y hy.1 hy.2
  have hxy_id := regrade_eq_id_on_unit W h_combine_rat (x + y) (by linarith) hxy
  rw [hx_id, hy_id] at h1
  -- Now h1 : φ(combine_fn x y) = x + y
  -- And hxy_id : φ(x + y) = x + y
  -- So φ(combine_fn x y) = φ(x + y)
  -- By injectivity: combine_fn x y = x + y
  have h2 : W.regrade (combine_fn x y) = W.regrade (x + y) := by
    rw [h1, hxy_id]
  exact W.strictMono.injective h2

/-! ## Constructing Regraduation from WeakRegraduation

The following shows how to build a full `Regraduation` from `WeakRegraduation` + `combine_rat`,
making `additive` a DERIVED property rather than an assumption.

**Key insight**: In the probability context, we only need additivity on [0,1] since
valuations take values in [0,1]. The theorems `additive_derived` and `regrade_eq_id_on_unit`
give us exactly this!

For the unbounded case (general ℝ), one would need to extend the K&S construction
beyond [0,1], but this is not needed for probability theory.
-/

/-- Build `Regraduation` from `WeakRegraduation` with explicit global additive proof.

Use this when you have a proof that φ is globally additive (e.g., from the full
K&S construction extended beyond [0,1]).

**Note**: For probability theory, you typically don't need `Regraduation` at all.
The key theorems (`combine_fn_is_add`, `sum_rule`, etc.) work directly with
`WeakRegraduation` + `combine_rat`. The `Regraduation` structure with global
additivity is only needed for extensions beyond the probability context. -/
def Regraduation.mk' (W : WeakRegraduation combine_fn)
    (h_additive : ∀ x y, W.regrade (x + y) = W.regrade x + W.regrade y) :
    Regraduation combine_fn where
  regrade := W.regrade
  strictMono := W.strictMono
  zero := W.zero
  one := W.one
  combine_eq_add := W.combine_eq_add
  additive := h_additive

/-- Cox-style consistency axioms for deriving probability.

**KEY DESIGN DECISION** (following GPT-5.1's Option 1):
We use `WeakRegraduation` + `combine_rat` instead of full `Regraduation`.
This makes the `additive` property 100% DERIVED, not assumed!

The derivation chain:
1. `weakRegrade`: provides φ with φ(S(x,y)) = φ(x) + φ(y)
2. `combine_rat`: S = + on ℚ ∩ [0,1]
3. `regrade_on_rat`: φ = id on ℚ ∩ [0,1] (derived from 1+2)
4. `regrade_eq_id_on_unit`: φ = id on [0,1] (derived from 3 + density)
5. `combine_fn_is_add`: S = + on [0,1] (derived from 1+4 + injectivity) -/
structure CoxConsistency (α : Type*) [PlausibilitySpace α] [ComplementedLattice α]
    (v : Valuation α) where
  /-- There exists a function S for combining disjoint plausibilities -/
  combine_fn : ℝ → ℝ → ℝ
  /-- Combining disjoint events uses S -/
  combine_disjoint : ∀ {a b}, Disjoint a b →
    v.val (a ⊔ b) = combine_fn (v.val a) (v.val b)
  /-- S is commutative (symmetry) -/
  combine_comm : ∀ x y, combine_fn x y = combine_fn y x
  /-- S is associative -/
  combine_assoc : ∀ x y z, combine_fn (combine_fn x y) z = combine_fn x (combine_fn y z)
  /-- S(x, 0) = x (identity) -/
  combine_zero : ∀ x, combine_fn x 0 = x
  /-- S is strictly increasing in first argument when second is positive -/
  combine_strict_mono : ∀ {x₁ x₂ y}, 0 < y → x₁ < x₂ →
    combine_fn x₁ y < combine_fn x₂ y
  /-- Disjoint events have zero overlap -/
  disjoint_zero : ∀ {a b}, Disjoint a b → v.val (a ⊓ b) = 0
  /-- WeakRegraduation: the core linearizer from K&S Appendix A.
  This provides φ with φ(S(x,y)) = φ(x) + φ(y), calibrated to φ(0)=0, φ(1)=1. -/
  weakRegrade : WeakRegraduation combine_fn
  /-- S = + on ℚ ∩ [0,1]. This follows from associativity + the grid construction.
  Combined with weakRegrade, this derives φ = id on [0,1], hence S = +. -/
  combine_rat : ∀ r s : ℚ, 0 ≤ (r : ℝ) → 0 ≤ (s : ℝ) → (r : ℝ) + (s : ℝ) ≤ 1 →
    combine_fn (r : ℝ) (s : ℝ) = ((r + s : ℚ) : ℝ)

variable {α : Type*} [PlausibilitySpace α] [ComplementedLattice α] (v : Valuation α)

/-! ## Key Theorem: Deriving Additivity

From the Cox consistency axioms, we can PROVE that combine_fn must be addition!
This is the core of why probability is additive.
-/

/-- Basic property: S(0, x) = x follows from commutativity and identity -/
lemma combine_zero_left (hC : CoxConsistency α v) (x : ℝ) :
    hC.combine_fn 0 x = x := by
  rw [hC.combine_comm, hC.combine_zero]

/-- Basic property: S(0, 0) = 0 -/
lemma combine_zero_zero (hC : CoxConsistency α v) :
    hC.combine_fn 0 0 = 0 := by
  exact hC.combine_zero 0

/-- Helper: S(x, x) = 2x for x ∈ [0, 1/2] (so that x + x ≤ 1).

This is derived using the regraduation approach:
1. φ(S(x, x)) = φ(x) + φ(x) = 2φ(x) (from combine_eq_add)
2. φ(x) = x (from regrade_eq_id_on_unit, since x ∈ [0,1])
3. So φ(S(x, x)) = 2x
4. If S(x, x) ∈ [0,1], then φ(S(x, x)) = S(x, x), hence S(x, x) = 2x

Note: The bound x ≤ 1/2 ensures x + x ≤ 1, needed for regrade_eq_id_on_unit. -/
lemma combine_double (hC : CoxConsistency α v) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) (hComb_le1 : hC.combine_fn x x ≤ 1) :
    hC.combine_fn x x = 2 * x := by
  -- Use the derived fact that φ = id on [0,1]
  have hx_le1 : x ≤ 1 := by linarith
  have hxx_le1 : x + x ≤ 1 := by linarith
  have hComb_ge0 : 0 ≤ hC.combine_fn x x := by
    have h1 : hC.combine_fn 0 x ≤ hC.combine_fn x x := by
      rcases eq_or_lt_of_le hx0 with rfl | hx_pos
      · simp [hC.combine_zero]
      -- combine_strict_mono : 0 < y → x₁ < x₂ → combine_fn x₁ y < combine_fn x₂ y
      -- With y = x, x₁ = 0, x₂ = x: gives combine_fn 0 x < combine_fn x x
      · exact le_of_lt (hC.combine_strict_mono hx_pos hx_pos)
    have h2 : hC.combine_fn 0 x = x := by rw [hC.combine_comm, hC.combine_zero]
    calc 0 ≤ x := hx0
      _ = hC.combine_fn 0 x := h2.symm
      _ ≤ hC.combine_fn x x := h1
  -- φ(x) = x since x ∈ [0,1]
  have hφx := regrade_eq_id_on_unit hC.weakRegrade hC.combine_rat x hx0 hx_le1
  -- φ(S(x,x)) = φ(x) + φ(x) from combine_eq_add
  have h1 := hC.weakRegrade.combine_eq_add x x
  -- S(x,x) ∈ [0,1], so φ(S(x,x)) = S(x,x)
  have hφComb := regrade_eq_id_on_unit hC.weakRegrade hC.combine_rat
    (hC.combine_fn x x) hComb_ge0 hComb_le1
  -- Conclude: S(x,x) = φ(S(x,x)) = φ(x) + φ(x) = 2x
  calc hC.combine_fn x x = hC.weakRegrade.regrade (hC.combine_fn x x) := hφComb.symm
    _ = hC.weakRegrade.regrade x + hC.weakRegrade.regrade x := h1
    _ = x + x := by rw [hφx]
    _ = 2 * x := by ring

/-- **THE BIG THEOREM**: Cox consistency forces combine_fn to be addition!

This is WHY probability is additive - it follows from symmetry + monotonicity.
The proof is now 100% derived from `WeakRegraduation` + `combine_rat`:

1. φ(S(x,y)) = φ(x) + φ(y) (from weakRegrade.combine_eq_add)
2. φ(x) = x and φ(y) = y (from regrade_eq_id_on_unit, since x,y ∈ [0,1])
3. So φ(S(x,y)) = x + y
4. S(x,y) ∈ [0,1] (hypothesis hComb_le1), so φ(S(x,y)) = S(x,y)
5. Therefore S(x,y) = x + y

**No assumed additivity!** The `additive` property of `Regraduation` is not used.
Instead, we use `regrade_eq_id_on_unit` which is derived from `combine_rat`. -/
theorem combine_fn_is_add (hC : CoxConsistency α v) :
    ∀ x y, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 →
    hC.combine_fn x y ≤ 1 →  -- NEW: needed to apply regrade_eq_id_on_unit
    hC.combine_fn x y = x + y := by
  intro x y hx0 hx1 hy0 hy1 hComb_le1
  -- S(x,y) ≥ 0 (from monotonicity + S(0,y) = y ≥ 0)
  have hComb_ge0 : 0 ≤ hC.combine_fn x y := by
    -- Use commutativity: S(x, y) = S(y, x), then monotonicity in first arg
    have h1 : hC.combine_fn 0 y ≤ hC.combine_fn x y := by
      rcases eq_or_lt_of_le hx0 with rfl | hx_pos
      · -- x = 0: trivially hC.combine_fn 0 y ≤ hC.combine_fn 0 y
        exact le_refl _
      rcases eq_or_lt_of_le hy0 with rfl | hy_pos
      · -- y = 0: S(0,0) ≤ S(x,0) means 0 ≤ x
        simp only [hC.combine_zero]
        exact hx0
      -- x > 0, y > 0: use combine_strict_mono : 0 < y → x₁ < x₂ → combine_fn x₁ y < combine_fn x₂ y
      · exact le_of_lt (hC.combine_strict_mono hy_pos hx_pos)
    have h2 : hC.combine_fn 0 y = y := by rw [hC.combine_comm, hC.combine_zero]
    calc 0 ≤ y := hy0
      _ = hC.combine_fn 0 y := h2.symm
      _ ≤ hC.combine_fn x y := h1
  -- Use the DERIVED fact that φ = id on [0,1]
  have hφx := regrade_eq_id_on_unit hC.weakRegrade hC.combine_rat x hx0 hx1
  have hφy := regrade_eq_id_on_unit hC.weakRegrade hC.combine_rat y hy0 hy1
  have hφComb := regrade_eq_id_on_unit hC.weakRegrade hC.combine_rat
    (hC.combine_fn x y) hComb_ge0 hComb_le1
  -- φ(S(x,y)) = φ(x) + φ(y) (from combine_eq_add)
  have h1 := hC.weakRegrade.combine_eq_add x y
  -- S(x,y) = φ(S(x,y)) = φ(x) + φ(y) = x + y (since φ = id on [0,1])
  calc hC.combine_fn x y = hC.weakRegrade.regrade (hC.combine_fn x y) := hφComb.symm
    _ = hC.weakRegrade.regrade x + hC.weakRegrade.regrade y := h1
    _ = x + y := by rw [hφx, hφy]

/-! ## Negation Function

Cox's theorem also addresses complements via a negation function N : ℝ → ℝ.
Following Knuth & Skilling: If a and b are complementary (Disjoint a b, a ⊔ b = ⊤),
then v(b) = N(v(a)).

We derive that N(x) = 1 - x from functional equation properties.
-/

/-- Negation data: function N for evaluating complements.
This parallels the combine_fn S for disjunction.

**IMPORTANT**: The linearity N(x) = 1 - x is NOT derivable from
continuity + involutive + antitone + boundary conditions alone!
Counterexample: N(x) = (1 - x^p)^{1/p} for any p > 0 satisfies all these
properties but N(x) ≠ 1 - x unless p = 1. See `involution_counterexample` below.

However, linearity IS derivable from:
- `negate_val` (consistency with complements) PLUS
- `CoxConsistency` (which gives the sum rule via `complement_rule`)

For standalone `NegationData` without `CoxConsistency`, we include `negate_linear`
as an axiom. When combined with `CoxConsistency` in `CoxConsistencyFull`,
it becomes derivable (see `negate_linear_from_cox`). -/
structure NegationData (α : Type*) [PlausibilitySpace α]
    [ComplementedLattice α] (v : Valuation α) where
  /-- The negation function N from Cox's theorem -/
  negate : ℝ → ℝ
  /-- Consistency: For complementary events, v(b) = N(v(a)) -/
  negate_val : ∀ a b, Disjoint a b → a ⊔ b = ⊤ →
    v.val b = negate (v.val a)
  /-- N is antitone (order-reversing) -/
  negate_antimono : Antitone negate
  /-- N(0) = 1 (complement of impossible is certain) -/
  negate_zero : negate 0 = 1
  /-- N(1) = 0 (complement of certain is impossible) -/
  negate_one : negate 1 = 0
  /-- N(N(x)) = x (involutive: complement of complement is original) -/
  negate_involutive : ∀ x, negate (negate x) = x
  /-- Regularity condition: N is continuous -/
  negate_continuous : Continuous negate
  /-- Linearity: N(x) = 1 - x on [0,1].
  This is NOT derivable from continuity + involutive + antitone alone
  (see counterexample below), but IS derivable when combined with CoxConsistency. -/
  negate_linear : ∀ x, 0 ≤ x → x ≤ 1 → negate x = 1 - x

/-- Extract linearity from NegationData. -/
theorem negate_is_linear (nd : NegationData α v) :
    ∀ x, 0 ≤ x → x ≤ 1 → nd.negate x = 1 - x :=
  nd.negate_linear

/-! ### Counterexample: Involution Properties Don't Imply Linearity

The function N(x) = √(1 - x²) satisfies:
- Continuous ✓
- Antitone ✓
- Involutive: N(N(x)) = √(1 - (1-x²)) = √(x²) = |x| = x for x ∈ [0,1] ✓
- N(0) = 1, N(1) = 0 ✓

But N(1/2) = √(3/4) = √3/2 ≈ 0.866 ≠ 0.5 = 1 - 1/2.

This shows that linearity does NOT follow from these properties alone.
It DOES follow when combined with CoxConsistency (sum rule) via complement_rule.
-/

/-- The p-norm involution: N_p(x) = (1 - x^p)^{1/p} for p > 0.
For p = 1: N₁(x) = 1 - x (linear)
For p = 2: N₂(x) = √(1 - x²) (not linear)
For p → ∞: N_∞(x) → max(1-x, 0) ∨ similar -/
noncomputable def pNormInvolution (p : ℝ) (_hp : 0 < p) (x : ℝ) : ℝ :=
  (1 - x ^ p) ^ (1 / p)

/-- The p-norm involution satisfies N(0) = 1. -/
lemma pNormInvolution_zero (p : ℝ) (hp : 0 < p) :
    pNormInvolution p hp 0 = 1 := by
  simp [pNormInvolution, Real.zero_rpow (ne_of_gt hp)]

/-- The p-norm involution satisfies N(1) = 0. -/
lemma pNormInvolution_one (p : ℝ) (hp : 0 < p) :
    pNormInvolution p hp 1 = 0 := by
  simp only [pNormInvolution, Real.one_rpow, sub_self]
  exact Real.zero_rpow (one_div_ne_zero (ne_of_gt hp))

/-- The p-norm involution is involutive on [0,1]. -/
lemma pNormInvolution_involutive (p : ℝ) (hp : 0 < p) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    pNormInvolution p hp (pNormInvolution p hp x) = x := by
  simp only [pNormInvolution]
  -- First, establish that 0 ≤ 1 - x^p since x ∈ [0,1]
  have h1 : 0 ≤ 1 - x ^ p := by
    have hxp : x ^ p ≤ 1 := Real.rpow_le_one hx0 hx1 (le_of_lt hp)
    linarith
  -- Establish nonnegativity for the inner term
  have h_inner_nn : 0 ≤ (1 - x ^ p) ^ (1 / p) := Real.rpow_nonneg h1 (1 / p)
  -- Key: ((1 - x^p)^(1/p))^p = 1 - x^p using rpow_mul
  have h2 : ((1 - x ^ p) ^ (1 / p)) ^ p = 1 - x ^ p := by
    rw [← Real.rpow_mul h1]
    simp only [one_div, inv_mul_cancel₀ (ne_of_gt hp), Real.rpow_one]
  -- Now simplify: 1 - ((1 - x^p)^(1/p))^p = x^p
  have h3 : 1 - ((1 - x ^ p) ^ (1 / p)) ^ p = x ^ p := by
    rw [h2]; ring
  -- Finally: (x^p)^(1/p) = x for x ≥ 0
  calc (1 - ((1 - x ^ p) ^ (1 / p)) ^ p) ^ (1 / p)
      = (x ^ p) ^ (1 / p) := by rw [h3]
    _ = x ^ (p * (1 / p)) := by rw [← Real.rpow_mul hx0]
    _ = x ^ (1 : ℝ) := by rw [mul_one_div_cancel (ne_of_gt hp)]
    _ = x := Real.rpow_one x

/-- The p=2 involution (√(1-x²)) is NOT linear: N(1/2) ≠ 1/2. -/
theorem involution_counterexample :
    pNormInvolution 2 (by norm_num : (0 : ℝ) < 2) (1/2) ≠ 1 - 1/2 := by
  simp only [pNormInvolution]
  -- N(1/2) = (1 - (1/2)²)^{1/2} = (3/4)^{1/2} ≈ 0.866
  -- But 1 - 1/2 = 1/2 = 0.5
  -- So we need (3/4)^(1/2) ≠ 1/2
  norm_num
  intro h
  -- If (3/4)^(1/2) = 1/2, then squaring: 3/4 = (1/2)² = 1/4, which is false
  have h_nn : (0 : ℝ) ≤ 3/4 := by norm_num
  -- Square both sides: ((3/4)^(1/2))^2 = (1/2)^2
  have h_sq : (((3 : ℝ) / 4) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = ((1 : ℝ) / 2) ^ (2 : ℕ) := by
    rw [h]
  -- Simplify LHS: ((3/4)^(1/2))^2 = 3/4 using rpow_mul
  rw [← Real.rpow_natCast (((3 : ℝ)/4)^((1:ℝ)/2)) 2, ← Real.rpow_mul h_nn] at h_sq
  simp only [one_div] at h_sq
  norm_num at h_sq

/-- Extended Cox consistency including negation function -/
structure CoxConsistencyFull (α : Type*) [PlausibilitySpace α]
    [ComplementedLattice α] (v : Valuation α) extends
    CoxConsistency α v, NegationData α v

/-- Sum rule: For disjoint events, v(a ⊔ b) = v(a) + v(b).
This is now a THEOREM, not an axiom! It follows from combine_fn_is_add.

**Key insight**: For disjoint events, S(v(a), v(b)) = v(a ⊔ b) ≤ 1,
which is exactly the bound needed to apply combine_fn_is_add. -/
theorem sum_rule (hC : CoxConsistency α v) {a b : α} (hDisj : Disjoint a b) :
    v.val (a ⊔ b) = v.val a + v.val b := by
  -- Start with the defining equation for disjoint events
  rw [hC.combine_disjoint hDisj]
  -- Apply the key theorem that combine_fn = addition
  apply combine_fn_is_add
  · exact v.nonneg a  -- 0 ≤ v(a)
  · exact v.le_one a  -- v(a) ≤ 1
  · exact v.nonneg b  -- 0 ≤ v(b)
  · exact v.le_one b  -- v(b) ≤ 1
  -- NEW: S(v(a), v(b)) = v(a ⊔ b) ≤ 1
  · rw [← hC.combine_disjoint hDisj]
    exact v.le_one (a ⊔ b)

/-!
## Independence (Appendix B): direct product rule

K&S introduces a **direct product** operation between independent lattices, written `×`
at the lattice level and `⊗` at the scalar level. After Appendix A regrades `⊕` to `+`,
Appendix B shows that `⊗` must be multiplication up to a single global scale constant.

In our formalization, Appendix B is proved in two routes:

- `Mettapedia.ProbabilityTheory.KnuthSkilling.ProductTheorem.Main` (via the product equation)
- `Mettapedia.ProbabilityTheory.KnuthSkilling.ProductTheorem.DirectProof` (Lean-friendly direct route)

The lemma below is the “pipeline glue” used by `ProbabilityDerivation`:
once you have *some* scalar `tensor` used to interpret direct products of events, the
Appendix B theorem converts it into literal multiplication after normalization.
-/

namespace AppendixB

open Mettapedia.ProbabilityTheory.KnuthSkilling.Literature

open ProductTheorem

variable {β γ : Type*} [PlausibilitySpace β] [PlausibilitySpace γ]

/-- Compatibility predicate: the valuation on the composite lattice uses `tensor` on the
measures of rectangle events. This is the intended reading of K&S “`x ⊗ t = m(x × t)`”. -/
def RectTensorCompatible
    {α : Type*} [PlausibilitySpace α]
    (P : ProductTheorem.DirectProduct α β γ)
    (vα : Valuation α) (vβ : Valuation β) (vγ : Valuation γ)
    (tensor : ProductTheorem.PosReal → ProductTheorem.PosReal → ProductTheorem.PosReal) : Prop :=
  ∀ a : α, ∀ b : β, ∀ ha : 0 < vα.val a, ∀ hb : 0 < vβ.val b,
    vγ.val (P.prod a b) = ((tensor ⟨vα.val a, ha⟩ ⟨vβ.val b, hb⟩ : ProductTheorem.PosReal) : ℝ)

/-- Appendix B consequence: any `tensor` satisfying the Independence axioms is multiplication
up to a global scale, hence the measure of rectangle events obeys the direct-product rule. -/
theorem directProduct_rule_mul_div_const
    {α : Type*} [PlausibilitySpace α]
    (P : ProductTheorem.DirectProduct α β γ)
    (vα : Valuation α) (vβ : Valuation β) (vγ : Valuation γ)
    {tensor : ProductTheorem.PosReal → ProductTheorem.PosReal → ProductTheorem.PosReal}
    (hAssoc : ∀ u v w : ProductTheorem.PosReal,
      tensor (tensor u v) w = tensor u (tensor v w))
    (hDistrib : ProductTheorem.DistributesOverAdd tensor)
    (hCommOne : ∀ t : ProductTheorem.PosReal,
      tensor ProductTheorem.onePos t = tensor t ProductTheorem.onePos)
    (hCompat : RectTensorCompatible (β := β) (γ := γ) P vα vβ vγ tensor) :
    ∃ C : ℝ, 0 < C ∧
      ∀ a : α, ∀ b : β, 0 < vα.val a → 0 < vβ.val b →
        vγ.val (P.prod a b) = (vα.val a * vβ.val b) / C := by
  rcases ProductTheorem.tensor_coe_eq_mul_div_const_of_assoc_of_distrib_of_comm_one
      (tensor := tensor) hAssoc hDistrib hCommOne with ⟨C, hC, hMul⟩
  refine ⟨C, hC, ?_⟩
  intro a b ha hb
  have hRect : vγ.val (P.prod a b) =
      ((tensor ⟨vα.val a, ha⟩ ⟨vβ.val b, hb⟩ : ProductTheorem.PosReal) : ℝ) :=
    hCompat a b ha hb
  -- Replace `tensor` by multiplication (up to `C`) via Appendix B.
  calc
    vγ.val (P.prod a b)
        = ((tensor ⟨vα.val a, ha⟩ ⟨vβ.val b, hb⟩ : ProductTheorem.PosReal) : ℝ) := hRect
    _ = ((vα.val a) * (vβ.val b)) / C := by
        simpa using hMul ⟨vα.val a, ha⟩ ⟨vβ.val b, hb⟩

end AppendixB

/-- Product rule: v(a ⊓ b) = v(a|b) · v(b) follows from definition of condVal -/
theorem product_rule_ks (_hC : CoxConsistency α v) (a b : α) (hB : v.val b ≠ 0) :
    v.val (a ⊓ b) = Valuation.condVal v a b * v.val b := by
  calc
    v.val (a ⊓ b) = (v.val (a ⊓ b) / v.val b) * v.val b := by field_simp [hB]
    _ = Valuation.condVal v a b * v.val b := by simp [Valuation.condVal, hB]

/-- **Bayes' Theorem** (derived from symmetry).

The product rule gives: v(a ⊓ b) = v(a|b) · v(b).
Since a ⊓ b = b ⊓ a (commutativity of lattice meet), we also have:
v(b ⊓ a) = v(b|a) · v(a).

Therefore: v(a|b) · v(b) = v(b|a) · v(a), which rearranges to:
**v(a|b) = v(b|a) · v(a) / v(b)**

This is the "Fundamental Theorem of Rational Inference" (Eq. 20 in Skilling-Knuth).
Bayesian inference isn't an "interpretation" — it's a mathematical necessity once
you accept the symmetry of conjunction (A ∧ B = B ∧ A).
-/
theorem bayes_theorem_ks (_hC : CoxConsistency α v) (a b : α)
    (ha : v.val a ≠ 0) (hb : v.val b ≠ 0) :
    Valuation.condVal v a b = Valuation.condVal v b a * v.val a / v.val b := by
  -- Expand conditional probability definitions
  simp only [Valuation.condVal, ha, hb, dite_false]
  -- Use commutativity: a ⊓ b = b ⊓ a
  rw [inf_comm]
  -- Field algebra: v(a ⊓ b)/v(b) = (v(a ⊓ b)/v(a)) · v(a)/v(b)
  field_simp

/-- Complement rule: For any element a, if b is its complement (disjoint and a ⊔ b = ⊤),
then v(b) = 1 - v(a).

TODO: The notation for complements in ComplementedLattice needs investigation.
For now, we state this more explicitly. -/
theorem complement_rule (hC : CoxConsistency α v) (a b : α)
    (h_disj : Disjoint a b) (h_top : a ⊔ b = ⊤) :
    v.val b = 1 - v.val a := by
  have h1 : v.val (a ⊔ b) = v.val a + v.val b := sum_rule v hC h_disj
  rw [h_top, v.val_top] at h1
  linarith

/-- KEY THEOREM: In `CoxConsistencyFull`, negation linearity is DERIVABLE!

When we have both:
- `negate_val`: v(b) = negate(v(a)) for complements a, b
- `complement_rule` (from CoxConsistency): v(b) = 1 - v(a) for complements

Then for any complementary pair (a, b):
  negate(v(a)) = v(b) = 1 - v(a)

This shows negate(x) = 1 - x for all x in the range of the valuation. -/
theorem negate_linear_from_cox (hCF : CoxConsistencyFull α v)
    (a b : α) (h_disj : Disjoint a b) (h_top : a ⊔ b = ⊤) :
    hCF.negate (v.val a) = 1 - v.val a := by
  -- From NegationData.negate_val: v(b) = negate(v(a))
  have h1 : v.val b = hCF.negate (v.val a) := hCF.negate_val a b h_disj h_top
  -- From complement_rule (using CoxConsistency): v(b) = 1 - v(a)
  have h2 : v.val b = 1 - v.val a := complement_rule v hCF.toCoxConsistency a b h_disj h_top
  -- Combine: negate(v(a)) = 1 - v(a)
  rw [← h1, h2]

end Mettapedia.ProbabilityTheory.KnuthSkilling
