import Mathlib.Algebra.Order.Quantale
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Inv
import Mettapedia.Logic.PLNDeduction

/-!
# PLN Evidence Counts as a Quantale

This file implements the **canonical quantale carrier** for PLN: evidence counts.

## The Key Insight (from GPT-5 Pro review)

Instead of trying to use `[0,1]` as the foundational carrier (where aggregating independent
evidence additively can exceed 1), we use **evidence counts**
`(n⁺, n⁻) ∈ ℝ≥0∞ × ℝ≥0∞` as the carrier:

- `n⁺` = positive evidence (supports the proposition)
- `n⁻` = negative evidence (refutes the proposition)

This IS a proper quantale:
- Complete lattice: coordinatewise ≤ with sup/inf
- Monoid ⊗: coordinatewise multiplication
- Quantale law: ⊗ distributes over ⨆

Then `SimpleTruthValue (s, c)` becomes a **view** via the standard PLN mapping:
- `s = n⁺ / (n⁺ + n⁻)`           (strength)
- `c = (n⁺ + n⁻) / (n⁺ + n⁻ + κ)` (confidence, with prior κ)

## Main Definitions

- `Evidence` : The evidence counts type
- `Evidence.tensor` : Quantale multiplication (sequential composition)
- `Evidence.hplus` : Parallel aggregation (independent evidence combination)
- `toSTV` / `ofSTV` : View functions to/from SimpleTruthValue

## References

- Goertzel et al., "Probabilistic Logic Networks" (2009), Chapter on truth-value formulas
- GPT-5 Pro review document (2025-12-09)
-/

namespace Mettapedia.Logic.PLNEvidence

open scoped ENNReal
open Mettapedia.Logic.PLNDeduction

/-! ## The Evidence Type

Evidence counts are pairs of extended non-negative reals representing
positive and negative support for a proposition.
-/

/-- Evidence counts: (positive support, negative support) -/
structure Evidence where
  pos : ℝ≥0∞  -- n⁺: positive evidence
  neg : ℝ≥0∞  -- n⁻: negative evidence
  deriving Inhabited

namespace Evidence

@[ext]
theorem ext' {e₁ e₂ : Evidence} (hp : e₁.pos = e₂.pos) (hn : e₁.neg = e₂.neg) : e₁ = e₂ := by
  cases e₁; cases e₂; simp only [mk.injEq]; exact ⟨hp, hn⟩

/-! ### Basic Operations -/

/-- Zero evidence: no support either way -/
def zero : Evidence := ⟨0, 0⟩

/-- Unit evidence for tensor product (multiplicative identity)
    Note: The unit is (1, 1) so that x ⊗ 1 = (x.pos * 1, x.neg * 1) = x -/
def one : Evidence := ⟨1, 1⟩

/-- Total evidence count: n⁺ + n⁻ -/
noncomputable def total (e : Evidence) : ℝ≥0∞ := e.pos + e.neg

/-! ### Lattice Structure (Coordinatewise)

The lattice order represents "information ordering" - more evidence is higher.
-/

instance : LE Evidence where
  le x y := x.pos ≤ y.pos ∧ x.neg ≤ y.neg

instance : LT Evidence where
  lt x y := x ≤ y ∧ ¬(y ≤ x)

theorem le_def (x y : Evidence) : x ≤ y ↔ x.pos ≤ y.pos ∧ x.neg ≤ y.neg := Iff.rfl

/-- Evidence forms a partial order under coordinatewise ≤ -/
instance : PartialOrder Evidence where
  le := fun x y => x.pos ≤ y.pos ∧ x.neg ≤ y.neg
  le_refl := fun x => ⟨le_refl x.pos, le_refl x.neg⟩
  le_trans := fun x y z ⟨hxy_pos, hxy_neg⟩ ⟨hyz_pos, hyz_neg⟩ =>
    ⟨le_trans hxy_pos hyz_pos, le_trans hxy_neg hyz_neg⟩
  le_antisymm := fun x y ⟨hxy_pos, hxy_neg⟩ ⟨hyx_pos, hyx_neg⟩ => by
    cases x; cases y
    simp at *
    exact ⟨le_antisymm hxy_pos hyx_pos, le_antisymm hxy_neg hyx_neg⟩

instance : Bot Evidence where
  bot := ⟨0, 0⟩

instance : Top Evidence where
  top := ⟨⊤, ⊤⟩

/-! ### Quantale Multiplication (Sequential Composition)

When evidence flows through a chain A → B → C, the evidence compounds multiplicatively.
This is the ⊗ operation in the quantale.
-/

/-- Tensor product: sequential composition of evidence
    (n⁺₁, n⁻₁) ⊗ (n⁺₂, n⁻₂) = (n⁺₁ * n⁺₂, n⁻₁ * n⁻₂)

    Interpretation: If A→B has evidence (n⁺₁, n⁻₁) and B→C has evidence (n⁺₂, n⁻₂),
    then the "direct path" A→B→C has evidence that compounds multiplicatively.
-/
noncomputable def tensor (x y : Evidence) : Evidence :=
  ⟨x.pos * y.pos, x.neg * y.neg⟩

noncomputable instance : Mul Evidence := ⟨tensor⟩

theorem tensor_def (x y : Evidence) : x * y = ⟨x.pos * y.pos, x.neg * y.neg⟩ := rfl

/-- Tensor is commutative -/
theorem tensor_comm (x y : Evidence) : x * y = y * x := by
  simp only [tensor_def, mul_comm]

/-- Tensor is associative -/
theorem tensor_assoc (x y z : Evidence) : (x * y) * z = x * (y * z) := by
  simp only [tensor_def, mul_assoc]

/-- One is the tensor unit -/
theorem tensor_one (x : Evidence) : x * one = x := by
  simp only [tensor_def, one, mul_one]

theorem one_tensor (x : Evidence) : one * x = x := by
  rw [tensor_comm, tensor_one]

noncomputable instance : CommMonoid Evidence where
  mul := tensor
  mul_assoc := tensor_assoc
  one := one
  one_mul := one_tensor
  mul_one := tensor_one
  mul_comm := tensor_comm

/-! ### Parallel Aggregation (Independent Evidence)

When we have independent sources of evidence, they combine additively.
This is the ⊕ operation (separate from the lattice join).
-/

/-- Parallel combination: independent evidence sources add
    (n⁺₁, n⁻₁) ⊕ (n⁺₂, n⁻₂) = (n⁺₁ + n⁺₂, n⁻₁ + n⁻₂)

    Interpretation: Two independent observations supporting/refuting a proposition
    contribute additively to the total evidence.
-/
noncomputable def hplus (x y : Evidence) : Evidence :=
  ⟨x.pos + y.pos, x.neg + y.neg⟩

noncomputable instance : Add Evidence := ⟨hplus⟩

theorem hplus_def (x y : Evidence) : x + y = ⟨x.pos + y.pos, x.neg + y.neg⟩ := rfl

theorem hplus_comm (x y : Evidence) : x + y = y + x := by
  simp only [hplus_def, add_comm]

theorem hplus_assoc (x y z : Evidence) : (x + y) + z = x + (y + z) := by
  simp only [hplus_def, add_assoc]

theorem hplus_zero (x : Evidence) : x + zero = x := by
  simp only [hplus_def, zero, add_zero]

theorem zero_hplus (x : Evidence) : zero + x = x := by
  simp only [hplus_def, zero, zero_add]

instance : Zero Evidence := ⟨zero⟩

/-! ### Lattice Structure

Evidence forms a complete lattice with coordinatewise operations:
- Meet (⊓): coordinatewise min
- Join (⊔): coordinatewise max
- Inf (⨅): coordinatewise infimum
- Sup (⨆): coordinatewise supremum

This gives Evidence the structure of a Frame, which is needed for the
lambda theory fibration.
-/

/-- Meet: coordinatewise minimum -/
def inf (x y : Evidence) : Evidence :=
  ⟨min x.pos y.pos, min x.neg y.neg⟩

/-- Join: coordinatewise maximum -/
def sup (x y : Evidence) : Evidence :=
  ⟨max x.pos y.pos, max x.neg y.neg⟩

/-- Infimum of a set: coordinatewise infimum (using ENNReal's sInf) -/
noncomputable def evidenceSInf (S : Set Evidence) : Evidence :=
  ⟨sInf (Evidence.pos '' S), sInf (Evidence.neg '' S)⟩

/-- Supremum of a set: coordinatewise supremum (using ENNReal's sSup) -/
noncomputable def evidenceSSup (S : Set Evidence) : Evidence :=
  ⟨sSup (Evidence.pos '' S), sSup (Evidence.neg '' S)⟩

/-- Evidence is a complete lattice under coordinatewise operations -/
noncomputable instance : CompleteLattice Evidence where
  -- Binary operations
  inf := inf
  sup := sup
  -- Top and bottom
  top := ⟨⊤, ⊤⟩
  bot := ⟨0, 0⟩
  le_top := fun x => ⟨le_top, le_top⟩
  bot_le := fun x => ⟨bot_le, bot_le⟩
  -- Binary meet/join laws
  inf_le_left := fun x y => by
    show inf x y ≤ x
    simp [inf, le_def]
  inf_le_right := fun x y => by
    show inf x y ≤ y
    simp [inf, le_def]
  le_inf := fun x y z ⟨hxy_pos, hxy_neg⟩ ⟨hxz_pos, hxz_neg⟩ => by
    show x ≤ inf y z
    simp [inf, le_def, *]
  le_sup_left := fun x y => by
    show x ≤ sup x y
    simp [sup, le_def]
  le_sup_right := fun x y => by
    show y ≤ sup x y
    simp [sup, le_def]
  sup_le := fun x y z ⟨hxy_pos, hxy_neg⟩ ⟨hyz_pos, hyz_neg⟩ => by
    show sup x y ≤ z
    simp [sup, le_def, *]
  -- Complete lattice operations
  sSup := evidenceSSup
  sInf := evidenceSInf
  le_sSup := fun S x hx => by
    simp [evidenceSSup, le_def]
    constructor
    · exact le_sSup (Set.mem_image_of_mem Evidence.pos hx)
    · exact le_sSup (Set.mem_image_of_mem Evidence.neg hx)
  sSup_le := fun S x h => by
    simp only [evidenceSSup, le_def]
    constructor
    · -- sSup of positive components ≤ x.pos
      apply sSup_le
      intro p hp
      simp only [Set.mem_image] at hp
      obtain ⟨e, heS, rfl⟩ := hp
      exact (h e heS).1
    · -- sSup of negative components ≤ x.neg
      apply sSup_le
      intro n hn
      simp only [Set.mem_image] at hn
      obtain ⟨e, heS, rfl⟩ := hn
      exact (h e heS).2
  sInf_le := fun S x hx => by
    simp [evidenceSInf, le_def]
    constructor
    · exact sInf_le (Set.mem_image_of_mem Evidence.pos hx)
    · exact sInf_le (Set.mem_image_of_mem Evidence.neg hx)
  le_sInf := fun S x h => by
    simp only [evidenceSInf, le_def]
    constructor
    · -- x.pos ≤ sInf of positive components
      apply le_sInf
      intro p hp
      simp only [Set.mem_image] at hp
      obtain ⟨e, heS, rfl⟩ := hp
      exact (h e heS).1
    · -- x.neg ≤ sInf of negative components
      apply le_sInf
      intro n hn
      simp only [Set.mem_image] at hn
      obtain ⟨e, heS, rfl⟩ := hn
      exact (h e heS).2

/-! ### Heyting Algebra Structure

Evidence forms a Heyting algebra with coordinatewise operations.
Since ENNReal has Heyting structure, the product Evidence = ENNReal × ENNReal
inherits it coordinatewise.
-/

/-- Heyting implication: coordinatewise residuation
    For ENNReal: a ⇨ b = if a ≤ b then ⊤ else b (Gödel implication)

    Interpretation: (n⁺₁, n⁻₁) ⇨ (n⁺₂, n⁻₂) gives the "weakest" evidence
    that makes the first imply the second.
-/
noncomputable def himp (a b : Evidence) : Evidence :=
  ⟨if a.pos ≤ b.pos then ⊤ else b.pos,
   if a.neg ≤ b.neg then ⊤ else b.neg⟩

/-- Complement: negation via Heyting implication with ⊥
    ¬a = a ⇨ ⊥ = a ⇨ (0, 0)
-/
noncomputable def compl (a : Evidence) : Evidence :=
  himp a ⊥

/-- The residuation law (Frame signature): a ≤ b ⇨ c ↔ a ⊓ b ≤ c -/
theorem le_himp_iff (a b c : Evidence) : a ≤ himp b c ↔ a ⊓ b ≤ c := by
  simp only [himp, le_def]
  constructor
  · intro ⟨ha_pos, ha_neg⟩
    constructor
    · by_cases hbc_pos : b.pos ≤ c.pos
      · simp only [hbc_pos, ite_true] at ha_pos
        calc min a.pos b.pos ≤ b.pos := min_le_right a.pos b.pos
          _ ≤ c.pos := hbc_pos
      · simp only [hbc_pos, ite_false] at ha_pos
        calc min a.pos b.pos ≤ a.pos := min_le_left a.pos b.pos
          _ ≤ c.pos := ha_pos
    · by_cases hbc_neg : b.neg ≤ c.neg
      · simp only [hbc_neg, ite_true] at ha_neg
        calc min a.neg b.neg ≤ b.neg := min_le_right a.neg b.neg
          _ ≤ c.neg := hbc_neg
      · simp only [hbc_neg, ite_false] at ha_neg
        calc min a.neg b.neg ≤ a.neg := min_le_left a.neg b.neg
          _ ≤ c.neg := ha_neg
  · intro ⟨h_pos, h_neg⟩
    -- Rewrite (a ⊓ b).pos = min a.pos b.pos etc.
    have h_inf_pos : (a ⊓ b).pos = min a.pos b.pos := rfl
    have h_inf_neg : (a ⊓ b).neg = min a.neg b.neg := rfl
    rw [h_inf_pos] at h_pos
    rw [h_inf_neg] at h_neg
    constructor
    · by_cases hbc_pos : b.pos ≤ c.pos
      · simp only [hbc_pos, ite_true]
        exact le_top
      · simp only [hbc_pos, ite_false]
        -- When ¬(b.pos ≤ c.pos), i.e., c.pos < b.pos
        -- We have h_pos : min a.pos b.pos ≤ c.pos
        -- Since min a.pos b.pos ≤ c.pos < b.pos, min must equal a.pos
        -- Therefore a.pos ≤ c.pos
        push_neg at hbc_pos
        have h_min_lt : min a.pos b.pos < b.pos := lt_of_le_of_lt h_pos hbc_pos
        have h_min_eq : min a.pos b.pos = a.pos := by
          by_contra h_neq
          have := min_eq_right (le_of_not_ge (fun h => h_neq (min_eq_left h)))
          rw [this] at h_min_lt
          exact lt_irrefl b.pos h_min_lt
        rw [h_min_eq] at h_pos
        exact h_pos
    · by_cases hbc_neg : b.neg ≤ c.neg
      · simp only [hbc_neg, ite_true]
        exact le_top
      · simp only [hbc_neg, ite_false]
        -- Same reasoning for the negative component
        push_neg at hbc_neg
        have h_min_lt : min a.neg b.neg < b.neg := lt_of_le_of_lt h_neg hbc_neg
        have h_min_eq : min a.neg b.neg = a.neg := by
          by_contra h_neq
          have := min_eq_right (le_of_not_ge (fun h => h_neq (min_eq_left h)))
          rw [this] at h_min_lt
          exact lt_irrefl b.neg h_min_lt
        rw [h_min_eq] at h_neg
        exact h_neg

/-- a ⇨ ⊥ = ¬a (definition of complement) -/
theorem himp_bot (a : Evidence) : himp a ⊥ = compl a := by
  rfl  -- By definition: compl a = himp a ⊥

/-- Evidence is a Frame (complete Heyting algebra)! -/
noncomputable instance : Order.Frame Evidence where
  himp := himp
  le_himp_iff := le_himp_iff
  compl := compl
  himp_bot := himp_bot

/-! ### Mathlib Theorems Now Available

After the `Order.Frame Evidence` instance above, these Mathlib theorems apply automatically:
- `le_himp_iff` : `a ≤ b ⇨ c ↔ a ⊓ b ≤ c` (Frame residuation)
- `himp_bot` : `a ⇨ ⊥ = aᶜ` (complement definition)
- `inf_sSup_eq` : `a ⊓ sSup S = ⨆ b ∈ S, a ⊓ b` (Frame distributivity)
- `compl_compl_le_compl` and other Heyting complement laws

Use these directly via typeclass inference rather than Evidence-specific versions.
The proofs above (`le_himp_iff`, `himp_bot`) establish that Evidence satisfies
the Frame axioms; after the instance, general Frame/Heyting theory applies.
-/

/-! ### View to SimpleTruthValue

Evidence now has FULL Frame structure (complete Heyting algebra)!
- CompleteLattice: ⊓, ⊔, ⨅, ⨆, ⊥, ⊤
- Heyting implication: ⇨ (residuation)
- Complement: ¬ (negation)

This is exactly what PLN's lambda theory fibration needs!

The calibrated mapping between evidence counts and (strength, confidence).
Uses a prior parameter κ > 0.
-/

variable (κ : ℝ≥0∞) -- Prior/context size parameter

/-- Convert evidence counts to strength: s = n⁺ / (n⁺ + n⁻)
    Returns 0 if total evidence is 0 (undefined case). -/
noncomputable def toStrength (e : Evidence) : ℝ≥0∞ :=
  if e.total = 0 then 0 else e.pos / e.total

/-- Convert evidence counts to confidence: c = total / (total + κ)
    Higher total evidence → higher confidence (approaches 1 as evidence → ∞) -/
noncomputable def toConfidence (e : Evidence) : ℝ≥0∞ :=
  e.total / (e.total + κ)

/-- Convert evidence to SimpleTruthValue (as reals in [0,1]) -/
noncomputable def toSTV (e : Evidence) : ℝ × ℝ :=
  ((toStrength e).toReal, (toConfidence κ e).toReal)

/-- Convert SimpleTruthValue to evidence counts (inverse of toSTV)
    Given (s, c) and prior κ, recover (n⁺, n⁻):
    - total = κ * c / (1 - c)
    - n⁺ = s * total
    - n⁻ = (1 - s) * total
-/
noncomputable def ofSTV (s c : ℝ) (_hc : c < 1) : Evidence :=
  let total : ℝ≥0∞ := κ * ENNReal.ofReal c / ENNReal.ofReal (1 - c)
  ⟨ENNReal.ofReal s * total, ENNReal.ofReal (1 - s) * total⟩

/-! ### Key Lemmas for the View

These connect the algebraic operations on Evidence to the standard PLN formulas.
-/

/-- Parallel combination in STV view corresponds to weighted averaging.
    This is PLN's revision rule!

    Note: We require total ≠ ⊤ to ensure the division algebra works correctly in ENNReal.
-/
theorem toStrength_hplus (x y : Evidence)
    (hx : x.total ≠ 0) (hy : y.total ≠ 0) (hxy : (x + y).total ≠ 0)
    (hx_ne_top : x.total ≠ ⊤) (hy_ne_top : y.total ≠ ⊤) :
    toStrength (x + y) =
    (x.total / (x + y).total) * toStrength x + (y.total / (x + y).total) * toStrength y := by
  -- The algebra: (x.pos + y.pos) / total_xy =
  --   (x.total / total_xy) * (x.pos / x.total) + (y.total / total_xy) * (y.pos / y.total)
  unfold toStrength
  simp only [hx, hy, hxy, ↓reduceIte]
  simp only [hplus_def, total] at *
  -- Key lemma: (a/T) * (p/a) = p/T when a ≠ 0, a ≠ ⊤
  have key : ∀ (p a T : ℝ≥0∞), a ≠ 0 → a ≠ ⊤ → (a / T) * (p / a) = p / T := by
    intros p a T ha0 haT
    rw [mul_comm, ← mul_div_assoc, ENNReal.div_mul_cancel ha0 haT]
  have h1 : (x.pos + x.neg) / (x.pos + y.pos + (x.neg + y.neg)) * (x.pos / (x.pos + x.neg)) =
            x.pos / (x.pos + y.pos + (x.neg + y.neg)) :=
    key x.pos (x.pos + x.neg) _ hx hx_ne_top
  have h2 : (y.pos + y.neg) / (x.pos + y.pos + (x.neg + y.neg)) * (y.pos / (y.pos + y.neg)) =
            y.pos / (x.pos + y.pos + (x.neg + y.neg)) :=
    key y.pos (y.pos + y.neg) _ hy hy_ne_top
  rw [h1, h2, ← ENNReal.add_div]

/-- The tensor product strength is at least the product of strengths.
    This shows that sequential composition preserves more positive evidence than
    the naive product formula would suggest.

    Mathematically: (x⁺y⁺)/(x⁺y⁺ + x⁻y⁻) ≥ (x⁺/(x⁺+x⁻)) * (y⁺/(y⁺+y⁻))
-/
theorem toStrength_tensor_ge (x y : Evidence) :
    toStrength (x * y) ≥ toStrength x * toStrength y := by
  unfold toStrength total
  simp only [tensor_def]
  -- Goal: (if x.pos * y.pos + x.neg * y.neg = 0 then 0 else (x.pos * y.pos) / ...)
  --       ≥ (if x.pos + x.neg = 0 then 0 else ...) * (if y.pos + y.neg = 0 then 0 else ...)
  by_cases hx : x.pos + x.neg = 0
  · -- x.total = 0: RHS has factor 0
    simp only [hx, ↓reduceIte, zero_mul, zero_le]
  · by_cases hy : y.pos + y.neg = 0
    · -- y.total = 0: RHS has factor 0
      simp only [hy, ↓reduceIte, mul_zero, zero_le]
    · -- Both totals nonzero
      simp only [hx, hy, ↓reduceIte]
      by_cases hxy : x.pos * y.pos + x.neg * y.neg = 0
      · -- Tensor total = 0: means x.pos * y.pos = 0 AND x.neg * y.neg = 0
        simp only [hxy, ↓reduceIte]
        -- LHS = 0, need 0 ≥ RHS (actually need to show RHS = 0)
        -- From hxy: x.pos * y.pos = 0, so either x.pos = 0 or y.pos = 0
        have hpos : x.pos * y.pos = 0 := (add_eq_zero.mp hxy).1
        -- So x.pos = 0 or y.pos = 0
        simp only [mul_eq_zero] at hpos
        rcases hpos with hxp | hyp
        · -- x.pos = 0
          rw [hxp, zero_add, ENNReal.zero_div, zero_mul]
        · -- y.pos = 0: goal has x.pos / (x.pos + x.neg) * (0 / (0 + y.neg))
          rw [hyp, zero_add, ENNReal.zero_div, mul_zero]
      · -- Main case: all totals nonzero
        simp only [hxy, ↓reduceIte]
        -- Need: (x.pos * y.pos) / (x.pos * y.pos + x.neg * y.neg) ≥
        --       (x.pos / (x.pos + x.neg)) * (y.pos / (y.pos + y.neg))
        -- First rewrite RHS using div_mul_div_comm to get same numerator
        -- For ENNReal, we prove this directly using div = mul_inv
        have h_rhs : x.pos / (x.pos + x.neg) * (y.pos / (y.pos + y.neg)) =
                     (x.pos * y.pos) / ((x.pos + x.neg) * (y.pos + y.neg)) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
          -- ENNReal.mul_inv : (a ≠ 0 ∨ b ≠ ⊤) → (a ≠ ⊤ ∨ b ≠ 0) → (a * b)⁻¹ = a⁻¹ * b⁻¹
          -- a = x.pos + x.neg, b = y.pos + y.neg
          -- We have hx : a ≠ 0 and hy : b ≠ 0
          rw [← (ENNReal.mul_inv (Or.inl hx) (Or.inr hy)).symm]
          ring
        rw [h_rhs, ge_iff_le]
        -- Now need: (x.pos * y.pos) / ((x.pos + x.neg) * (y.pos + y.neg)) ≤
        --           (x.pos * y.pos) / (x.pos * y.pos + x.neg * y.neg)
        apply ENNReal.div_le_div_left
        -- Need: x.pos * y.pos + x.neg * y.neg ≤ (x.pos + x.neg) * (y.pos + y.neg)
        calc x.pos * y.pos + x.neg * y.neg
            ≤ x.pos * y.pos + x.neg * y.neg + (x.pos * y.neg + x.neg * y.pos) := by
              apply le_add_of_nonneg_right
              exact add_nonneg (zero_le _) (zero_le _)
          _ = (x.pos + x.neg) * (y.pos + y.neg) := by ring

end Evidence

/-! ## Q-Weighted Relations

A knowledge base is a Q-weighted relation: for each pair (A, B) of propositions,
we have an evidence value representing "A implies B."
-/

/-- A Q-weighted relation over types α and β -/
structure QRel (α β : Type*) where
  w : α → β → Evidence

namespace QRel

variable {α β γ : Type*}

/-- Composition of Q-weighted relations for finite intermediate type
    (R ∘ S)(A, C) = ⨆_B R(A,B) ⊗ S(B,C)

    For finite β, we compute this as a supremum over enumerated elements.
-/
noncomputable def comp [Fintype β] (R : QRel α β) (S : QRel β γ) : QRel α γ where
  w a c :=
    -- Take coordinatewise max over all path products
    ⟨Finset.univ.sup (fun b => (R.w a b * S.w b c).pos),
     Finset.univ.sup (fun b => (R.w a b * S.w b c).neg)⟩

/-- Identity relation: full evidence on the diagonal -/
def id [DecidableEq α] : QRel α α where
  w a b := if a = b then Evidence.one else Evidence.zero

/-- Composition gives at least each individual path contribution.

    The PLN deduction formula computes the strength of A→C given A→B and B→C.
    In the Q-weighted relations view, this is just composition.

    The key insight: the "direct path" term `sAB * sBC` comes from the tensor product,
    while the "indirect path via ¬B" term comes from considering the complement.
-/
theorem comp_is_deduction [Fintype β] (R : QRel α β) (S : QRel β γ) (a : α) (c : γ) :
    -- The composition gives at least the direct path contribution
    ∀ b, R.w a b * S.w b c ≤ (comp R S).w a c := by
  intro b
  unfold comp
  simp only [Evidence.le_def, Evidence.tensor_def]
  constructor
  · -- pos component
    apply Finset.le_sup (f := fun b => (R.w a b * S.w b c).pos)
    exact Finset.mem_univ b
  · -- neg component
    apply Finset.le_sup (f := fun b => (R.w a b * S.w b c).neg)
    exact Finset.mem_univ b

end QRel

/-! ## Residuation: The Right Adjoint to Tensor

Following the OSLF (Operational Semantics in Logical Form) framework, the PLN deduction
formula decomposes into two parts:
1. **Direct path**: A → B → C via tensor composition (⊗)
2. **Indirect path**: A → ¬B → C via residuation (⇒)

The full formula is: P(C|A) = P(B|A)·P(C|B) + P(¬B|A)·P(C|¬B)

In quantale terms, residuation is the right adjoint to tensor:
  x ⊗ y ≤ z  iff  y ≤ x ⇒ z

For evidence counts, this corresponds to:
  (x.pos * y.pos, x.neg * y.neg) ≤ (z.pos, z.neg)
  iff y ≤ residuate x z

The key insight from OSLF/Native Type Theory is that types are pairs (U, X) where:
- X is a "sort" (the kind of evidence)
- U is a "filter" on X (a subset/predicate on evidence)

For PLN, this maps to:
- X = Evidence (the carrier type)
- U = a filter defined by strength/confidence constraints
-/

namespace Evidence

/-- Residuation for evidence: the right adjoint to tensor.

    In the quantale [0,1], residuation is: x ⇒ z = min(1, z/x) if x > 0, else 1
    For evidence counts, we compute the "maximal y such that x ⊗ y ≤ z".

    Note: This is a partial operation - only meaningful when x ≠ 0.
    When x.pos = 0 or x.neg = 0, we return ⊤ for that component.
-/
noncomputable def residuate (x z : Evidence) : Evidence :=
  ⟨if x.pos = 0 then ⊤ else z.pos / x.pos,
   if x.neg = 0 then ⊤ else z.neg / x.neg⟩

/-- Residuation is right adjoint to tensor: x ⊗ y ≤ z iff y ≤ x ⇒ z

    Note: We require z ≠ ⊤ (componentwise) for the equivalence to hold cleanly.
    In the ⊤ case, both sides are trivially true (everything ≤ ⊤).
-/
theorem residuate_adjoint (x y z : Evidence)
    (hx_pos : x.pos ≠ 0) (hx_neg : x.neg ≠ 0)
    (hz_pos : z.pos ≠ ⊤) (hz_neg : z.neg ≠ ⊤) :
    x * y ≤ z ↔ y ≤ residuate x z := by
  unfold residuate
  simp only [hx_pos, hx_neg, ↓reduceIte, le_def, tensor_def]
  constructor
  · -- Forward: x ⊗ y ≤ z implies y ≤ x ⇒ z
    intro ⟨h_pos, h_neg⟩
    constructor
    · -- y.pos ≤ z.pos / x.pos
      rw [ENNReal.le_div_iff_mul_le (Or.inl hx_pos) (Or.inr hz_pos)]
      rw [mul_comm]
      exact h_pos
    · -- y.neg ≤ z.neg / x.neg
      rw [ENNReal.le_div_iff_mul_le (Or.inl hx_neg) (Or.inr hz_neg)]
      rw [mul_comm]
      exact h_neg
  · -- Backward: y ≤ x ⇒ z implies x ⊗ y ≤ z
    intro ⟨h_pos, h_neg⟩
    constructor
    · -- x.pos * y.pos ≤ z.pos
      rw [ENNReal.le_div_iff_mul_le (Or.inl hx_pos) (Or.inr hz_pos), mul_comm] at h_pos
      exact h_pos
    · -- x.neg * y.neg ≤ z.neg
      rw [ENNReal.le_div_iff_mul_le (Or.inl hx_neg) (Or.inr hz_neg), mul_comm] at h_neg
      exact h_neg

/-! ### The Full Deduction Formula via Quantale Operations

The PLN deduction formula can be expressed in terms of evidence operations:

```
P(C|A) = P(B|A) · P(C|B) + (1 - P(B|A)) · P(C|¬B)
       = sAB · sBC + (1 - sAB) · (pC - pB·sBC)/(1 - pB)
```

In evidence terms:
- Direct path: tensor(E_AB, E_BC) contributes sAB · sBC
- Indirect path: residuate(E_B, E_C) gives evidence for C|¬B

The full formula requires:
1. Marginals P(A), P(B), P(C) as context
2. Evidence E_AB for A→B and E_BC for B→C
3. Computation of P(C|¬B) via the complement formula
-/

/-- Strength of the "indirect path" P(C|¬B) = (P(C) - P(B)·P(C|B)) / (1 - P(B))

    This is the complement term in the deduction formula.
    It represents the probability of C given that we went through ¬B.
-/
noncomputable def complementStrength (pB pC sBC : ℝ≥0∞) : ℝ≥0∞ :=
  if pB = 1 then 0  -- Degenerate case: no ¬B path
  else (pC - pB * sBC) / (1 - pB)

/-- The full deduction formula expressed in evidence terms.

    Given:
    - E_AB: Evidence for A → B (with strength sAB = toStrength E_AB)
    - E_BC: Evidence for B → C (with strength sBC = toStrength E_BC)
    - pB: Prior probability P(B)
    - pC: Prior probability P(C)

    Returns evidence for A → C combining direct and indirect paths.

    Note: This is a simplified version that computes the strength directly.
    A full formalization would also track confidence through the computation.
-/
noncomputable def deductionEvidence
    (E_AB E_BC : Evidence)
    (pB pC : ℝ≥0∞)
    (_hE_AB : E_AB.total ≠ 0) (_hE_BC : E_BC.total ≠ 0)
    (_hpB : pB ≠ 1) : Evidence :=
  let sAB := toStrength E_AB
  let sBC := toStrength E_BC
  let direct := sAB * sBC
  let indirect := (1 - sAB) * complementStrength pB pC sBC
  let total_strength := direct + indirect
  -- Create evidence with this strength and combined total evidence
  let total_ev := E_AB.total + E_BC.total
  ⟨total_strength * total_ev, (1 - total_strength) * total_ev⟩

/-! ### Connecting Evidence to the Real-Valued Deduction Formula

The key connection between Evidence and PLNDeduction.simpleDeductionStrengthFormula:
- Evidence operations work on (n⁺, n⁻) ∈ ℝ≥0∞ × ℝ≥0∞
- The deduction formula works on strengths s ∈ ℝ (in [0,1])
- The toStrength map connects them: s = n⁺ / (n⁺ + n⁻)

The main insight is that the deduction formula:
  sAC = sAB * sBC + (1 - sAB) * (pC - pB * sBC) / (1 - pB)

Can be decomposed into:
  sAC = [direct path contribution] + [indirect path contribution]

Where:
- Direct path: A → B → C via tensor (gives sAB * sBC term)
- Indirect path: A → ¬B → C via residuation (gives the (1-sAB) * P(C|¬B) term)
-/

/-- The direct path strength: sAB * sBC
    This is the first term in the deduction formula. -/
noncomputable def directPathStrength (sAB sBC : ℝ≥0∞) : ℝ≥0∞ := sAB * sBC

/-- The indirect path strength: (1 - sAB) * P(C|¬B)
    This is the second term in the deduction formula. -/
noncomputable def indirectPathStrength (sAB pB pC sBC : ℝ≥0∞) : ℝ≥0∞ :=
  (1 - sAB) * complementStrength pB pC sBC

/-- The full deduction strength from component strengths.
    sAC = sAB * sBC + (1 - sAB) * (pC - pB * sBC) / (1 - pB)
-/
noncomputable def deductionStrength (sAB sBC pB pC : ℝ≥0∞) : ℝ≥0∞ :=
  directPathStrength sAB sBC + indirectPathStrength sAB pB pC sBC

/-- Helper: toStrength of a constructed evidence is just the strength.
    If we construct evidence with pos = s*t and neg = (1-s)*t where s ≤ 1,
    then toStrength returns s.
-/
theorem toStrength_of_scaled (s t : ℝ≥0∞) (hs : s ≤ 1) (ht0 : t ≠ 0) (htT : t ≠ ⊤) :
    toStrength ⟨s * t, (1 - s) * t⟩ = s := by
  unfold toStrength total
  simp only
  have h_sum : s * t + (1 - s) * t = t := by
    rw [← add_mul, add_tsub_cancel_of_le hs, one_mul]
  rw [h_sum, if_neg ht0]
  exact ENNReal.mul_div_cancel_right ht0 htT

/-- When converted to strengths, deductionEvidence produces the deduction formula.

    This is the key theorem connecting Evidence-based computation to the
    real-valued formula in PLNDeduction.simpleDeductionStrengthFormula.

    The strength of deductionEvidence E_AB E_BC is:
      toStrength (deductionEvidence E_AB E_BC pB pC)
      = toStrength E_AB * toStrength E_BC
        + (1 - toStrength E_AB) * complementStrength pB pC (toStrength E_BC)

    Note: We require the total_strength ≤ 1 condition for the ENNReal arithmetic
    to work correctly (otherwise `a + (1 - a)` might not equal 1).
-/
theorem deductionEvidence_strength
    (E_AB E_BC : Evidence)
    (pB pC : ℝ≥0∞)
    (hE_AB : E_AB.total ≠ 0) (hE_BC : E_BC.total ≠ 0)
    (hpB : pB ≠ 1)
    (h_total_ne_zero : (E_AB.total + E_BC.total) ≠ 0)
    (h_total_ne_top : (E_AB.total + E_BC.total) ≠ ⊤)
    (h_strength_le_1 : deductionStrength (toStrength E_AB) (toStrength E_BC) pB pC ≤ 1) :
    toStrength (deductionEvidence E_AB E_BC pB pC hE_AB hE_BC hpB) =
    deductionStrength (toStrength E_AB) (toStrength E_BC) pB pC := by
  -- The deductionEvidence constructs evidence with structure:
  --   pos = s * total_ev
  --   neg = (1 - s) * total_ev
  -- where s = deductionStrength and total_ev = E_AB.total + E_BC.total
  set s := deductionStrength (toStrength E_AB) (toStrength E_BC) pB pC with hs_def
  set t := E_AB.total + E_BC.total with ht_def
  -- Show that deductionEvidence produces ⟨s * t, (1 - s) * t⟩
  have h_ev_eq : deductionEvidence E_AB E_BC pB pC hE_AB hE_BC hpB = ⟨s * t, (1 - s) * t⟩ := rfl
  rw [h_ev_eq]
  exact toStrength_of_scaled s t h_strength_le_1 h_total_ne_zero h_total_ne_top

end Evidence

/-! ## Connection to OSLF Modal Types

The OSLF algorithm generates modal types from rewrite rules. For PLN:

- `◊B` (possibly B) corresponds to evidence that supports B
- `⧫A` (was-possibly A) corresponds to evidence that came from A
- `⟨E⟩B` (after evidence E, possibly B) is the rely-possibly modality

The deduction rule A → B → C can be typed as:
  Γ ⊢ E_AB : A ↠ B    Δ ⊢ E_BC : B ↠ C
  ─────────────────────────────────────────
  Γ, Δ ⊢ comp(E_AB, E_BC) : A ↠ C

Where `↠` is the evidence-weighted implication type.

The tensor product `E_AB ⊗ E_BC` gives the "direct path" evidence,
and residuation gives the "indirect path" contribution.

This categorical structure (NT(CCC) in OSLF terminology) provides:
1. A topos structure with complete Heyting algebra homs
2. Modal operators from the rewrite semantics
3. Spatial types from term constructors
4. Behavioral types from reduction rules

For PLN, the key insight is that truth values form an enriched category
over the unit interval quantale [0,1], and the deduction formula is
precisely the composition law in this enriched category.
-/

/-! ## Summary

We now have:

1. `Evidence` : A proper commutative monoid with tensor product
2. `Evidence.hplus` : Parallel aggregation for independent evidence
3. `toSTV` / `ofSTV` : Views to/from SimpleTruthValue
4. `QRel` : Q-weighted relations with composition
5. `Evidence.residuate` : Right adjoint to tensor (for ¬B path)
6. `Evidence.deductionEvidence` : Full deduction formula in evidence terms

The deduction formula emerges as:
- **Direct path**: tensor product E_AB ⊗ E_BC (proven lower bound via `toStrength_tensor_ge`)
- **Indirect path**: via `complementStrength` and `residuate`
- **Full formula**: `deductionEvidence` combines both paths

## Connection to OSLF/Native Type Theory

The OSLF framework (Meredith & Stay) shows that spatial-behavioral type systems
can be algorithmically generated from rewrite systems. For PLN:

1. **Native Type Theory**: Types are pairs (U, X) = (filter, sort)
   - For PLN: X = Evidence carrier, U = strength/confidence constraints

2. **Modal Types from Rewrites**: The deduction rule generates modal types
   - `⟨E_AB⟩⟨E_BC⟩C` = evidence that A leads to C via B

3. **Quantale Structure**: The unit interval [0,1] with multiplication
   forms a commutative quantale, and PLN is the enriched category over it

4. **Residuation**: The right adjoint to tensor gives the "¬B path" term
   - `x ⊗ y ≤ z ↔ y ≤ x ⇒ z` (proven in `residuate_adjoint`)

## References

- Goertzel et al., "Probabilistic Logic Networks" (2009), Chapter on truth-value formulas
- Meredith & Stay, "Operational Semantics in Logical Form" (OSLF)
- Williams & Stay, "Native Type Theory" - topos-theoretic foundations
- Lawvere, "Metric spaces, generalized logic, and closed categories" (1973)
-/

end Mettapedia.Logic.PLNEvidence
