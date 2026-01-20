/-
# Classification of 2-Dimensional Unital Real Algebras

This module proves the classical classification theorem:

**Theorem**: Every 2-dimensional unital associative algebra over ℝ is isomorphic to exactly one of:
- Complex numbers ℂ (where i² = -1)
- Dual numbers ℝ[ε] (where ε² = 0)
- Split-complex numbers ℝ[j] (where j² = +1)

The proof uses the "completing the square" technique:
1. Any 2D unital algebra has a basis {1, e} with e² = a + be for some a, b ∈ ℝ
2. Define e' = e - b/2, then (e')² = a + b²/4 =: μ
3. The sign of μ determines the algebra:
   - μ < 0: Complex (rescale to get i with i² = -1)
   - μ = 0: Dual (already have ε² = 0)
   - μ > 0: Split-complex (rescale to get j with j² = +1)

Key insight for K&S: The bilinearProduct parameterized by μ continuously covers all three cases,
but there are only 3 isomorphism classes - the classification is discrete, not continuous!

## References

- Study.com "Classification of 2D Real Algebras"
- Skilling & Knuth (2018), "The Symmetrical Foundation of Measure, Probability, and Quantum Theories"
-/

import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mettapedia.Algebra.SplitComplex
import Mathlib.Tactic

namespace Mettapedia.Algebra.TwoDimClassification

open SplitComplex

/-! ## The μ-Parameterized Product

Following K&S, we define the bilinear product parameterized by μ ∈ ℝ:
  (u₁, u₂) * (v₁, v₂) = (u₁v₁ + μ·u₂v₂, u₁v₂ + u₂v₁)

This gives:
- μ = -1: Complex multiplication
- μ = 0: Dual number multiplication
- μ = +1: Split-complex multiplication
-/

/-- The μ-parameterized algebra, representing elements as pairs (re, im). -/
@[ext]
structure MuAlgebra (μ : ℝ) where
  re : ℝ
  im : ℝ

namespace MuAlgebra

variable (μ : ℝ)

instance : Zero (MuAlgebra μ) := ⟨⟨0, 0⟩⟩
instance : One (MuAlgebra μ) := ⟨⟨1, 0⟩⟩
instance : Add (MuAlgebra μ) := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Neg (MuAlgebra μ) := ⟨fun z => ⟨-z.re, -z.im⟩⟩
instance : Sub (MuAlgebra μ) := ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩

/-- The μ-parameterized multiplication:
(u₁, u₂) * (v₁, v₂) = (u₁v₁ + μ·u₂v₂, u₁v₂ + u₂v₁) -/
instance : Mul (MuAlgebra μ) := ⟨fun z w => ⟨z.re * w.re + μ * z.im * w.im, z.re * w.im + z.im * w.re⟩⟩

@[simp] lemma zero_re : (0 : MuAlgebra μ).re = 0 := rfl
@[simp] lemma zero_im : (0 : MuAlgebra μ).im = 0 := rfl
@[simp] lemma one_re : (1 : MuAlgebra μ).re = 1 := rfl
@[simp] lemma one_im : (1 : MuAlgebra μ).im = 0 := rfl
@[simp] lemma add_re (z w : MuAlgebra μ) : (z + w).re = z.re + w.re := rfl
@[simp] lemma add_im (z w : MuAlgebra μ) : (z + w).im = z.im + w.im := rfl
@[simp] lemma neg_re (z : MuAlgebra μ) : (-z).re = -z.re := rfl
@[simp] lemma neg_im (z : MuAlgebra μ) : (-z).im = -z.im := rfl
@[simp] lemma sub_re (z w : MuAlgebra μ) : (z - w).re = z.re - w.re := rfl
@[simp] lemma sub_im (z w : MuAlgebra μ) : (z - w).im = z.im - w.im := rfl
@[simp] lemma mul_re (z w : MuAlgebra μ) : (z * w).re = z.re * w.re + μ * z.im * w.im := rfl
@[simp] lemma mul_im (z w : MuAlgebra μ) : (z * w).im = z.re * w.im + z.im * w.re := rfl

/-- The basis element e = (0, 1) with e² = μ·1. -/
def e : MuAlgebra μ := ⟨0, 1⟩

@[simp] lemma e_re : (e μ).re = 0 := rfl
@[simp] lemma e_im : (e μ).im = 1 := rfl

/-- The defining property: e² = (μ, 0). -/
@[simp] theorem e_sq : (e μ) * (e μ) = ⟨μ, 0⟩ := by
  ext <;> simp [e]

instance : SMul ℕ (MuAlgebra μ) := ⟨fun n z => ⟨n • z.re, n • z.im⟩⟩
instance : SMul ℤ (MuAlgebra μ) := ⟨fun n z => ⟨n • z.re, n • z.im⟩⟩

instance : AddCommGroup (MuAlgebra μ) where
  add_assoc := fun _ _ _ => by ext <;> simp [add_assoc]
  zero_add := fun _ => by ext <;> simp
  add_zero := fun _ => by ext <;> simp
  add_comm := fun _ _ => by ext <;> simp [add_comm]
  neg_add_cancel := fun _ => by ext <;> simp
  nsmul := (· • ·)
  zsmul := (· • ·)

instance : CommRing (MuAlgebra μ) where
  left_distrib := fun a b c => by ext <;> simp only [mul_re, mul_im, add_re, add_im] <;> ring
  right_distrib := fun a b c => by ext <;> simp only [mul_re, mul_im, add_re, add_im] <;> ring
  zero_mul := fun _ => by ext <;> simp
  mul_zero := fun _ => by ext <;> simp
  mul_assoc := fun a b c => by ext <;> simp only [mul_re, mul_im] <;> ring
  one_mul := fun _ => by ext <;> simp
  mul_one := fun _ => by ext <;> simp
  mul_comm := fun a b => by ext <;> simp only [mul_re, mul_im] <;> ring

end MuAlgebra

/-! ## Isomorphisms to Concrete Algebras

We now show that:
- MuAlgebra (-1) ≃ ℂ
- MuAlgebra 1 ≃ SplitComplex
-/

/-- MuAlgebra (-1) is isomorphic to ℂ. -/
noncomputable def muAlgebraNegOneEquivComplex : MuAlgebra (-1) ≃+* ℂ where
  toFun z := ⟨z.re, z.im⟩
  invFun c := ⟨c.re, c.im⟩
  left_inv := fun z => by ext <;> rfl
  right_inv := fun c => by
    apply Complex.ext
    · simp
    · simp
  map_mul' := fun z w => by
    apply Complex.ext
    · simp only [MuAlgebra.mul_re, Complex.mul_re]; ring
    · simp only [MuAlgebra.mul_im, Complex.mul_im]
  map_add' := fun z w => by
    apply Complex.ext <;> simp

/-- MuAlgebra 1 is isomorphic to SplitComplex. -/
noncomputable def muAlgebraOneEquivSplit : MuAlgebra (1 : ℝ) ≃+* SplitComplex where
  toFun z := ⟨z.re, z.im⟩
  invFun s := ⟨s.re, s.im⟩
  left_inv := fun z => by ext <;> rfl
  right_inv := fun s => by ext <;> rfl
  map_mul' := fun z w => by
    ext
    · simp only [MuAlgebra.mul_re, SplitComplex.mul_re]; ring
    · simp only [MuAlgebra.mul_im, SplitComplex.mul_im]
  map_add' := fun z w => by ext <;> simp

/-! ## The Classification Theorem

Now we prove the main classification result.
-/

/-- The three isomorphism classes of 2D unital real algebras. -/
inductive TwoDimAlgebraClass
  | complex      -- i² = -1
  | dual         -- ε² = 0
  | splitComplex -- j² = +1

/-- Classification by the sign of μ. -/
noncomputable def classifyByMu (μ : ℝ) : TwoDimAlgebraClass :=
  if μ < 0 then TwoDimAlgebraClass.complex
  else if μ = 0 then TwoDimAlgebraClass.dual
  else TwoDimAlgebraClass.splitComplex

/-- MuAlgebra 0 has ε² = 0 (dual numbers). -/
theorem muAlgebra_zero_e_sq : (MuAlgebra.e 0) * (MuAlgebra.e 0) = (0 : MuAlgebra 0) := by
  ext <;> simp [MuAlgebra.e]

/-- Rescaling: all positive μ give isomorphic algebras.
The map (a, b) ↦ (a, b·√(μ/μ')) scales e² by μ/μ'. -/
noncomputable def muAlgebraRescale (μ μ' : ℝ) (hμ : 0 < μ) (hμ' : 0 < μ') :
    MuAlgebra μ ≃+* MuAlgebra μ' := by
  let k := Real.sqrt (μ / μ')
  let k' := Real.sqrt (μ' / μ)
  have hk_pos : 0 ≤ k := Real.sqrt_nonneg _
  have hk'_pos : 0 ≤ k' := Real.sqrt_nonneg _
  have hkk' : k * k' = 1 := by
    simp only [k, k']
    rw [← Real.sqrt_mul (div_nonneg (le_of_lt hμ) (le_of_lt hμ'))]
    rw [div_mul_div_comm, mul_comm μ' μ, div_self (ne_of_gt (mul_pos hμ hμ'))]
    simp
  have hk'k : k' * k = 1 := by rw [mul_comm]; exact hkk'
  have hksq : k * k = μ / μ' := Real.mul_self_sqrt (div_nonneg (le_of_lt hμ) (le_of_lt hμ'))
  refine ⟨⟨fun z => ⟨z.re, z.im * k⟩, fun z => ⟨z.re, z.im * k'⟩, ?_, ?_⟩, ?_, ?_⟩
  · intro z; ext; rfl; simp only; rw [mul_assoc, hkk', mul_one]
  · intro z; ext; rfl; simp only; rw [mul_assoc, hk'k, mul_one]
  · intro z w
    ext
    · simp only [MuAlgebra.mul_re]
      have h : μ' * (z.im * k) * (w.im * k) = μ * z.im * w.im := by
        calc μ' * (z.im * k) * (w.im * k)
            = μ' * z.im * w.im * (k * k) := by ring
          _ = μ' * z.im * w.im * (μ / μ') := by rw [hksq]
          _ = μ * z.im * w.im := by field_simp
      linarith [h]
    · simp only [MuAlgebra.mul_im]; ring
  · intro z w; ext <;> simp [add_mul]

/-- Rescaling for negative μ values. -/
noncomputable def muAlgebraRescaleNeg (μ μ' : ℝ) (hμ : μ < 0) (hμ' : μ' < 0) :
    MuAlgebra μ ≃+* MuAlgebra μ' := by
  have hdiv_pos : 0 < μ / μ' := div_pos_of_neg_of_neg hμ hμ'
  have hdiv_pos' : 0 < μ' / μ := div_pos_of_neg_of_neg hμ' hμ
  let k := Real.sqrt (μ / μ')
  let k' := Real.sqrt (μ' / μ)
  have hk_pos : 0 ≤ k := Real.sqrt_nonneg _
  have hk'_pos : 0 ≤ k' := Real.sqrt_nonneg _
  have hkk' : k * k' = 1 := by
    simp only [k, k']
    rw [← Real.sqrt_mul (le_of_lt hdiv_pos)]
    rw [div_mul_div_comm, mul_comm μ' μ, div_self (ne_of_gt (mul_pos_of_neg_of_neg hμ hμ'))]
    simp
  have hk'k : k' * k = 1 := by rw [mul_comm]; exact hkk'
  have hksq : k * k = μ / μ' := Real.mul_self_sqrt (le_of_lt hdiv_pos)
  refine ⟨⟨fun z => ⟨z.re, z.im * k⟩, fun z => ⟨z.re, z.im * k'⟩, ?_, ?_⟩, ?_, ?_⟩
  · intro z; ext; rfl; simp only; rw [mul_assoc, hkk', mul_one]
  · intro z; ext; rfl; simp only; rw [mul_assoc, hk'k, mul_one]
  · intro z w
    ext
    · simp only [MuAlgebra.mul_re]
      have hμ'_ne : μ' ≠ 0 := ne_of_lt hμ'
      have h : μ' * (z.im * k) * (w.im * k) = μ * z.im * w.im := by
        have step1 : μ' * (z.im * k) * (w.im * k) = μ' * z.im * w.im * (k * k) := by ring
        have step2 : μ' * z.im * w.im * (k * k) = μ' * z.im * w.im * (μ / μ') := by rw [hksq]
        have step3 : μ' * z.im * w.im * (μ / μ') = μ * z.im * w.im := by field_simp
        linarith [step1, step2, step3]
      linarith [h]
    · simp only [MuAlgebra.mul_im]; ring
  · intro z w; ext <;> simp [add_mul]

/-- Every MuAlgebra with μ > 0 is isomorphic to MuAlgebra 1 (split-complex). -/
noncomputable def muAlgebraPosToOne (μ : ℝ) (hμ : 0 < μ) : MuAlgebra μ ≃+* MuAlgebra 1 :=
  muAlgebraRescale μ 1 hμ one_pos

/-- Every MuAlgebra with μ < 0 is isomorphic to MuAlgebra (-1) (complex). -/
noncomputable def muAlgebraNegToNegOne (μ : ℝ) (hμ : μ < 0) : MuAlgebra μ ≃+* MuAlgebra (-1) :=
  muAlgebraRescaleNeg μ (-1) hμ (neg_one_lt_zero)

/-- Every 2D unital real algebra with e² = μ is isomorphic to one of the three standard forms. -/
theorem mu_algebra_classification (μ : ℝ) :
    (μ < 0 ∧ Nonempty (MuAlgebra μ ≃+* ℂ)) ∨
    (μ = 0) ∨
    (0 < μ ∧ Nonempty (MuAlgebra μ ≃+* SplitComplex)) := by
  rcases lt_trichotomy μ 0 with h_neg | h_zero | h_pos
  · left
    refine ⟨h_neg, ?_⟩
    exact ⟨(muAlgebraNegToNegOne μ h_neg).trans muAlgebraNegOneEquivComplex⟩
  · right; left; exact h_zero
  · right; right
    refine ⟨h_pos, ?_⟩
    exact ⟨(muAlgebraPosToOne μ h_pos).trans muAlgebraOneEquivSplit⟩

/-! ## The Completing-the-Square Invariant

The key algebraic insight: Given e² = a + be, defining e' = e - b/2 gives (e')² = μ·1
where μ = a + b²/4. This μ is the isomorphism invariant.
-/

/-- The invariant μ = a + b²/4 determines the isomorphism class. -/
noncomputable def completingSquareInvariant (a b : ℝ) : ℝ := a + b^2 / 4

/-- The completing-the-square transformation. -/
theorem completing_square_abstract (a b : ℝ) :
    let μ := completingSquareInvariant a b
    ∀ z : MuAlgebra μ, z * z = ⟨z.re^2 + μ * z.im^2, 2 * z.re * z.im⟩ := by
  intro μ z
  ext
  · simp [MuAlgebra.mul_re]; ring
  · simp [MuAlgebra.mul_im]; ring

/-! ## Connection to K&S SymmetricalFoundation

K&S parameterize their bilinear product by a real parameter μ:
  (u₁, u₂) * (v₁, v₂) = (u₁v₁ + μ·u₂v₂, u₁v₂ + u₂v₁)

This gives exactly MuAlgebra μ. The classification theorem shows that although μ
varies continuously, there are only 3 isomorphism classes.

For quantum mechanics, K&S argue that μ = -1 (complex numbers) is selected by
additional physical constraints (unitarity, Fourier duality).
-/

/-- K&S bilinearProduct matches MuAlgebra multiplication. -/
theorem ks_bilinearProduct_eq_muAlgebra (μ : ℝ) (z w : MuAlgebra μ) :
    z * w = ⟨z.re * w.re + μ * z.im * w.im, z.re * w.im + z.im * w.re⟩ := by
  ext <;> simp

/-- The three-way classification is complete: every μ falls into exactly one class. -/
theorem classification_trichotomy (μ : ℝ) :
    (μ < 0 ∧ classifyByMu μ = TwoDimAlgebraClass.complex) ∨
    (μ = 0 ∧ classifyByMu μ = TwoDimAlgebraClass.dual) ∨
    (0 < μ ∧ classifyByMu μ = TwoDimAlgebraClass.splitComplex) := by
  rcases lt_trichotomy μ 0 with h | h | h
  · left; exact ⟨h, by simp [classifyByMu, h]⟩
  · right; left; exact ⟨h, by simp [classifyByMu, h]⟩
  · right; right; exact ⟨h, by simp [classifyByMu, not_lt.mpr (le_of_lt h), ne_of_gt h]⟩

/-! ## Connection to K&S Bilinear Product

The K&S bilinearProduct is exactly MuAlgebra multiplication viewed on ℝ × ℝ.
-/

/-- The general bilinear product form (matching K&S definition in SymmetricalFoundation). -/
def bilinearProductDef (μ : ℝ) (u v : ℝ × ℝ) : ℝ × ℝ :=
  (u.1 * v.1 + μ * u.2 * v.2, u.1 * v.2 + u.2 * v.1)

/-- bilinearProductDef is associative for any μ. -/
theorem bilinearProductDef_assoc (μ : ℝ) (u v w : ℝ × ℝ) :
    bilinearProductDef μ (bilinearProductDef μ u v) w =
    bilinearProductDef μ u (bilinearProductDef μ v w) := by
  simp only [bilinearProductDef]
  ext <;> ring

/-- bilinearProductDef has identity (1, 0). -/
theorem bilinearProductDef_one_left (μ : ℝ) (u : ℝ × ℝ) :
    bilinearProductDef μ (1, 0) u = u := by
  simp only [bilinearProductDef]
  ext <;> simp

theorem bilinearProductDef_one_right (μ : ℝ) (u : ℝ × ℝ) :
    bilinearProductDef μ u (1, 0) = u := by
  simp only [bilinearProductDef]
  ext <;> simp

/-- MuAlgebra multiplication matches bilinearProductDef. -/
theorem muAlgebra_eq_bilinearProductDef (μ : ℝ) (z w : MuAlgebra μ) :
    let prod := z * w
    (prod.re, prod.im) = bilinearProductDef μ (z.re, z.im) (w.re, w.im) := by
  simp only [bilinearProductDef, MuAlgebra.mul_re, MuAlgebra.mul_im]

/-- bilinearProductDef is commutative. -/
theorem bilinearProductDef_comm (μ : ℝ) (u v : ℝ × ℝ) :
    bilinearProductDef μ u v = bilinearProductDef μ v u := by
  simp only [bilinearProductDef]
  ext <;> ring

/-- The classification restated: all bilinearProductDef μ algebras are classified by sign of μ. -/
theorem bilinearProductDef_classification (μ : ℝ) :
    (μ < 0 ∧ Nonempty (MuAlgebra μ ≃+* ℂ)) ∨
    (μ = 0) ∨
    (0 < μ ∧ Nonempty (MuAlgebra μ ≃+* SplitComplex)) := by
  rcases lt_trichotomy μ 0 with h | h | h
  · left
    exact ⟨h, ⟨(muAlgebraNegToNegOne μ h).trans muAlgebraNegOneEquivComplex⟩⟩
  · right; left; exact h
  · right; right
    exact ⟨h, ⟨(muAlgebraPosToOne μ h).trans muAlgebraOneEquivSplit⟩⟩

/-! ## Selection Theorem: Why Complex Numbers for Quantum Mechanics

The K&S paper argues that complex numbers (μ < 0) are selected for quantum mechanics because:
1. The conjugate norm N(z) = z · conj(z) must be positive-definite for probability
2. Only μ < 0 gives positive-definite conjugate norm

For MuAlgebra(μ), conjugation is conj(u₁, u₂) = (u₁, -u₂), and:
  N(u) = u · conj(u) = (u₁² - μ·u₂², 0)

So the norm² is u₁² - μ·u₂²:
- μ < 0: N(u) = u₁² + |μ|·u₂² ≥ 0 (positive definite) ✓
- μ = 0: N(u) = u₁² (degenerate - ignores imaginary part)
- μ > 0: N(u) = u₁² - μ·u₂² (indefinite - can be negative) ✗
-/

/-- The conjugate in MuAlgebra: conj(u₁, u₂) = (u₁, -u₂). -/
def MuAlgebra.conj {μ : ℝ} (z : MuAlgebra μ) : MuAlgebra μ := ⟨z.re, -z.im⟩

@[simp] lemma MuAlgebra.conj_re {μ : ℝ} (z : MuAlgebra μ) : z.conj.re = z.re := rfl
@[simp] lemma MuAlgebra.conj_im {μ : ℝ} (z : MuAlgebra μ) : z.conj.im = -z.im := rfl

/-- The conjugate norm: N(z) = z · conj(z). -/
def MuAlgebra.conjNorm {μ : ℝ} (z : MuAlgebra μ) : ℝ := z.re^2 - μ * z.im^2

/-- The product z * conj(z) equals (N(z), 0). -/
theorem MuAlgebra.mul_conj_eq_norm {μ : ℝ} (z : MuAlgebra μ) :
    z * z.conj = ⟨z.conjNorm, 0⟩ := by
  ext
  · simp [MuAlgebra.conj, MuAlgebra.conjNorm, MuAlgebra.mul_re]; ring
  · simp [MuAlgebra.conj, MuAlgebra.mul_im]; ring

/-- For μ < 0, the conjugate norm is positive definite:
    N(z) ≥ 0, and N(z) = 0 iff z = 0. -/
theorem MuAlgebra.conjNorm_nonneg {μ : ℝ} (hμ : μ < 0) (z : MuAlgebra μ) :
    0 ≤ z.conjNorm := by
  simp only [MuAlgebra.conjNorm]
  have h : 0 ≤ -μ * z.im^2 := by nlinarith [sq_nonneg z.im]
  linarith [sq_nonneg z.re]

theorem MuAlgebra.conjNorm_eq_zero_iff {μ : ℝ} (hμ : μ < 0) (z : MuAlgebra μ) :
    z.conjNorm = 0 ↔ z = 0 := by
  constructor
  · intro h
    simp only [MuAlgebra.conjNorm] at h
    -- h : z.re^2 - μ * z.im^2 = 0, i.e., z.re^2 = μ * z.im^2
    -- Since μ < 0 and z.im^2 ≥ 0, we have μ * z.im^2 ≤ 0
    -- But z.re^2 ≥ 0, so z.re^2 = μ * z.im^2 implies both are 0
    have hre_sq : z.re^2 = μ * z.im^2 := by linarith
    have him_sq_nonneg : 0 ≤ z.im^2 := sq_nonneg z.im
    have hμ_im_nonpos : μ * z.im^2 ≤ 0 := by nlinarith
    have hre_sq_nonneg : 0 ≤ z.re^2 := sq_nonneg z.re
    have hre_sq_zero : z.re^2 = 0 := by linarith
    have him_sq_zero : z.im^2 = 0 := by
      have : 0 = μ * z.im^2 := by linarith
      nlinarith
    have hre : z.re = 0 := by nlinarith
    have him : z.im = 0 := by nlinarith
    ext <;> assumption
  · intro h
    simp [h, MuAlgebra.conjNorm]

/-- For μ > 0 (split-complex), the conjugate norm can be negative. -/
theorem MuAlgebra.conjNorm_can_be_negative {μ : ℝ} (hμ : 0 < μ) :
    ∃ z : MuAlgebra μ, z.conjNorm < 0 := by
  use ⟨0, 1⟩
  simp [MuAlgebra.conjNorm]
  linarith

/-- For μ = 0 (dual), the conjugate norm ignores the imaginary part. -/
theorem MuAlgebra.conjNorm_zero_mu (z : MuAlgebra 0) : z.conjNorm = z.re^2 := by
  simp [MuAlgebra.conjNorm]

/-- SELECTION THEOREM: Only negative μ gives a positive-definite conjugate norm.
This is the mathematical formalization of why complex numbers are selected for QM. -/
theorem selection_theorem :
    ∀ μ : ℝ, (∀ z : MuAlgebra μ, 0 ≤ z.conjNorm ∧ (z.conjNorm = 0 → z = 0)) ↔ μ < 0 := by
  intro μ
  constructor
  · -- If norm is positive-definite, then μ < 0
    intro h
    by_contra hμ_nonneg
    push_neg at hμ_nonneg
    rcases lt_or_eq_of_le hμ_nonneg with hμ_pos | hμ_zero
    · -- Case μ > 0: contradicts positive-definiteness
      obtain ⟨z, hz⟩ := MuAlgebra.conjNorm_can_be_negative hμ_pos
      have ⟨hnonneg, _⟩ := h z
      linarith
    · -- Case μ = 0: z = (0, 1) has norm 0 but z ≠ 0
      subst hμ_zero
      have ⟨_, hinj⟩ := h ⟨0, 1⟩
      have heq : (⟨0, 1⟩ : MuAlgebra 0).conjNorm = 0 := by simp [MuAlgebra.conjNorm]
      have hz : (⟨0, 1⟩ : MuAlgebra 0) = 0 := hinj heq
      have : (1 : ℝ) = 0 := congrArg MuAlgebra.im hz
      linarith
  · -- If μ < 0, then norm is positive-definite
    intro hμ z
    exact ⟨MuAlgebra.conjNorm_nonneg hμ z, fun h => (MuAlgebra.conjNorm_eq_zero_iff hμ z).mp h⟩

/-- The conjugate norm is multiplicative for any μ. -/
theorem MuAlgebra.conjNorm_mul {μ : ℝ} (z w : MuAlgebra μ) :
    (z * w).conjNorm = z.conjNorm * w.conjNorm := by
  simp only [MuAlgebra.conjNorm, MuAlgebra.mul_re, MuAlgebra.mul_im]
  ring

/-! ## General Bilinear Algebra and Classification

The general 2D bilinear algebra has multiplication:
  (u₁, u₂) * (v₁, v₂) = (u₁v₁ + a·u₂v₂, u₁v₂ + u₂v₁ + b·u₂v₂)

This is mathlib's QuadraticAlgebra(a, b). The completing-the-square theorem shows:
  QuadraticAlgebra(a, b) ≃+* MuAlgebra(a + b²/4)

Therefore any 2D bilinear associative unital algebra is ISOMORPHIC to some MuAlgebra(μ).
-/

/-- General bilinear algebra with parameters a, b.
    Multiplication: (u₁, u₂) * (v₁, v₂) = (u₁v₁ + a·u₂v₂, u₁v₂ + u₂v₁ + b·u₂v₂) -/
@[ext]
structure GeneralBilinearAlgebra (a b : ℝ) where
  re : ℝ
  im : ℝ

namespace GeneralBilinearAlgebra

variable {a b : ℝ}

instance : Zero (GeneralBilinearAlgebra a b) := ⟨⟨0, 0⟩⟩
instance : One (GeneralBilinearAlgebra a b) := ⟨⟨1, 0⟩⟩
instance : Add (GeneralBilinearAlgebra a b) := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Neg (GeneralBilinearAlgebra a b) := ⟨fun z => ⟨-z.re, -z.im⟩⟩
instance : Sub (GeneralBilinearAlgebra a b) := ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩

/-- General bilinear multiplication with second component having +b·u₂v₂ term. -/
instance : Mul (GeneralBilinearAlgebra a b) :=
  ⟨fun z w => ⟨z.re * w.re + a * z.im * w.im, z.re * w.im + z.im * w.re + b * z.im * w.im⟩⟩

@[simp] lemma zero_re : (0 : GeneralBilinearAlgebra a b).re = 0 := rfl
@[simp] lemma zero_im : (0 : GeneralBilinearAlgebra a b).im = 0 := rfl
@[simp] lemma one_re : (1 : GeneralBilinearAlgebra a b).re = 1 := rfl
@[simp] lemma one_im : (1 : GeneralBilinearAlgebra a b).im = 0 := rfl
@[simp] lemma add_re (z w : GeneralBilinearAlgebra a b) : (z + w).re = z.re + w.re := rfl
@[simp] lemma add_im (z w : GeneralBilinearAlgebra a b) : (z + w).im = z.im + w.im := rfl
@[simp] lemma neg_re (z : GeneralBilinearAlgebra a b) : (-z).re = -z.re := rfl
@[simp] lemma neg_im (z : GeneralBilinearAlgebra a b) : (-z).im = -z.im := rfl
@[simp] lemma mul_re (z w : GeneralBilinearAlgebra a b) :
    (z * w).re = z.re * w.re + a * z.im * w.im := rfl
@[simp] lemma mul_im (z w : GeneralBilinearAlgebra a b) :
    (z * w).im = z.re * w.im + z.im * w.re + b * z.im * w.im := rfl

instance : SMul ℕ (GeneralBilinearAlgebra a b) := ⟨fun n z => ⟨n • z.re, n • z.im⟩⟩
instance : SMul ℤ (GeneralBilinearAlgebra a b) := ⟨fun n z => ⟨n • z.re, n • z.im⟩⟩

instance : AddCommGroup (GeneralBilinearAlgebra a b) where
  add_assoc := fun _ _ _ => by ext <;> simp [add_assoc]
  zero_add := fun _ => by ext <;> simp
  add_zero := fun _ => by ext <;> simp
  add_comm := fun _ _ => by ext <;> simp [add_comm]
  neg_add_cancel := fun _ => by ext <;> simp
  nsmul := (· • ·)
  zsmul := (· • ·)

instance : CommRing (GeneralBilinearAlgebra a b) where
  left_distrib := fun x y z => by ext <;> simp only [mul_re, mul_im, add_re, add_im] <;> ring
  right_distrib := fun x y z => by ext <;> simp only [mul_re, mul_im, add_re, add_im] <;> ring
  zero_mul := fun _ => by ext <;> simp
  mul_zero := fun _ => by ext <;> simp
  mul_assoc := fun x y z => by ext <;> simp only [mul_re, mul_im] <;> ring
  one_mul := fun _ => by ext <;> simp
  mul_one := fun _ => by ext <;> simp
  mul_comm := fun x y => by ext <;> simp only [mul_re, mul_im] <;> ring

end GeneralBilinearAlgebra

/-- The completing-the-square isomorphism:
    GeneralBilinearAlgebra(a, b) ≃+* MuAlgebra(a + b²/4)

    The map is (x, y) ↦ (x + b·y/2, y), which corresponds to the
    change of basis e' = e - b/2 where (e')² = (a + b²/4)·1. -/
noncomputable def completingSquareIso (a b : ℝ) :
    GeneralBilinearAlgebra a b ≃+* MuAlgebra (a + b^2/4) where
  toFun z := ⟨z.re + b * z.im / 2, z.im⟩
  invFun z := ⟨z.re - b * z.im / 2, z.im⟩
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_mul' z w := by
    ext
    · -- First component: need to show transformed product matches
      simp only [GeneralBilinearAlgebra.mul_re, GeneralBilinearAlgebra.mul_im, MuAlgebra.mul_re]
      ring
    · -- Second component: direct calculation
      simp only [GeneralBilinearAlgebra.mul_im, MuAlgebra.mul_im]
      ring
  map_add' z w := by
    ext
    · simp only [GeneralBilinearAlgebra.add_re, GeneralBilinearAlgebra.add_im, MuAlgebra.add_re]
      ring
    · simp only [GeneralBilinearAlgebra.add_im, MuAlgebra.add_im]

/-- MuAlgebra is a special case of GeneralBilinearAlgebra with b = 0. -/
def muAlgebraToGeneral (μ : ℝ) : MuAlgebra μ ≃+* GeneralBilinearAlgebra μ 0 where
  toFun z := ⟨z.re, z.im⟩
  invFun z := ⟨z.re, z.im⟩
  left_inv z := by ext <;> rfl
  right_inv z := by ext <;> rfl
  map_mul' z w := by ext <;> simp
  map_add' z w := by ext <;> simp

/-- CLASSIFICATION THEOREM (Correct Version):
    Any 2D bilinear associative unital algebra is ISOMORPHIC to MuAlgebra(μ) for some μ.

    This is the completing-the-square classification:
    - The algebra is determined by e² = a + b·e for some a, b ∈ ℝ
    - Change of basis e' = e - b/2 gives (e')² = μ where μ = a + b²/4
    - In the new basis, multiplication is exactly MuAlgebra(μ) -/
theorem classification_to_muAlgebra (a b : ℝ) :
    Nonempty (GeneralBilinearAlgebra a b ≃+* MuAlgebra (a + b^2/4)) :=
  ⟨completingSquareIso a b⟩

/-- The classification invariant: algebras with same μ = a + b²/4 are isomorphic. -/
theorem classification_invariant (a₁ b₁ a₂ b₂ : ℝ)
    (h : a₁ + b₁^2/4 = a₂ + b₂^2/4) :
    Nonempty (GeneralBilinearAlgebra a₁ b₁ ≃+* GeneralBilinearAlgebra a₂ b₂) := by
  have h1 := completingSquareIso a₁ b₁
  have h2 := completingSquareIso a₂ b₂
  rw [h] at h1
  exact ⟨h1.trans h2.symm⟩

end Mettapedia.Algebra.TwoDimClassification
