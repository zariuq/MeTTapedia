/-
# Split-Complex Numbers

The split-complex numbers (also called hyperbolic numbers, double numbers, or perplex numbers)
are the 2-dimensional real algebra with basis {1, j} where j² = +1 (not -1 like complex i).

This is the third of the three 2-dimensional unital real algebras:
- Complex: i² = -1 (μ = -1)
- Dual: ε² = 0 (μ = 0)
- Split-complex: j² = +1 (μ = +1)

## Key Properties

Unlike complex numbers:
- Split-complex numbers have zero divisors: (1+j)(1-j) = 1 - j² = 0
- They have nontrivial idempotents: e₊ = (1+j)/2, e₋ = (1-j)/2 with e₊² = e₊, e₋² = e₋
- The "norm" N(a + bj) = a² - b² can be negative
- They are isomorphic to ℝ × ℝ as rings (via the idempotent decomposition)

## References

- https://en.wikipedia.org/wiki/Split-complex_number
- Skilling & Knuth (2018), Section 4, Equation (19c)
-/

import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Mettapedia.Algebra

/-- The split-complex numbers, a 2D real algebra with j² = +1. -/
@[ext]
structure SplitComplex where
  re : ℝ  -- real part
  im : ℝ  -- "imaginary" part (coefficient of j)

namespace SplitComplex

/-- The split-imaginary unit j with j² = +1. -/
def j : SplitComplex := ⟨0, 1⟩

/-- Coercion from ℝ to SplitComplex. -/
@[coe] def ofReal (r : ℝ) : SplitComplex := ⟨r, 0⟩

instance : Coe ℝ SplitComplex := ⟨ofReal⟩

@[simp] theorem ofReal_re (r : ℝ) : (ofReal r).re = r := rfl
@[simp] theorem ofReal_im (r : ℝ) : (ofReal r).im = 0 := rfl
@[simp] theorem coe_re (r : ℝ) : (r : SplitComplex).re = r := rfl
@[simp] theorem coe_im (r : ℝ) : (r : SplitComplex).im = 0 := rfl

/-- Zero element. -/
instance : Zero SplitComplex := ⟨⟨0, 0⟩⟩

@[simp] theorem zero_re : (0 : SplitComplex).re = 0 := rfl
@[simp] theorem zero_im : (0 : SplitComplex).im = 0 := rfl

/-- One element. -/
instance : One SplitComplex := ⟨⟨1, 0⟩⟩

@[simp] theorem one_re : (1 : SplitComplex).re = 1 := rfl
@[simp] theorem one_im : (1 : SplitComplex).im = 0 := rfl

/-- Addition. -/
instance : Add SplitComplex := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩

@[simp] theorem add_re (z w : SplitComplex) : (z + w).re = z.re + w.re := rfl
@[simp] theorem add_im (z w : SplitComplex) : (z + w).im = z.im + w.im := rfl

/-- Negation. -/
instance : Neg SplitComplex := ⟨fun z => ⟨-z.re, -z.im⟩⟩

@[simp] theorem neg_re (z : SplitComplex) : (-z).re = -z.re := rfl
@[simp] theorem neg_im (z : SplitComplex) : (-z).im = -z.im := rfl

/-- Subtraction. -/
instance : Sub SplitComplex := ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩

@[simp] theorem sub_re (z w : SplitComplex) : (z - w).re = z.re - w.re := rfl
@[simp] theorem sub_im (z w : SplitComplex) : (z - w).im = z.im - w.im := rfl

/-- Multiplication: (a + bj)(c + dj) = (ac + bd) + (ad + bc)j
Note: j² = +1, so bd·j² = bd·1 = bd. -/
instance : Mul SplitComplex := ⟨fun z w => ⟨z.re * w.re + z.im * w.im, z.re * w.im + z.im * w.re⟩⟩

@[simp] theorem mul_re (z w : SplitComplex) : (z * w).re = z.re * w.re + z.im * w.im := rfl
@[simp] theorem mul_im (z w : SplitComplex) : (z * w).im = z.re * w.im + z.im * w.re := rfl

/-- Scalar multiplication by natural numbers. -/
instance : SMul ℕ SplitComplex := ⟨fun n z => ⟨n • z.re, n • z.im⟩⟩

@[simp] theorem nsmul_re (n : ℕ) (z : SplitComplex) : (n • z).re = n • z.re := rfl
@[simp] theorem nsmul_im (n : ℕ) (z : SplitComplex) : (n • z).im = n • z.im := rfl

/-- Scalar multiplication by integers. -/
instance : SMul ℤ SplitComplex := ⟨fun n z => ⟨n • z.re, n • z.im⟩⟩

@[simp] theorem zsmul_re (n : ℤ) (z : SplitComplex) : (n • z).re = n • z.re := rfl
@[simp] theorem zsmul_im (n : ℤ) (z : SplitComplex) : (n • z).im = n • z.im := rfl

/-- SplitComplex forms an additive commutative group. -/
instance instAddCommGroup : AddCommGroup SplitComplex where
  add_assoc := fun _ _ _ => by ext <;> simp [add_assoc]
  zero_add := fun _ => by ext <;> simp
  add_zero := fun _ => by ext <;> simp
  add_comm := fun _ _ => by ext <;> simp [add_comm]
  neg_add_cancel := fun _ => by ext <;> simp
  nsmul := (· • ·)
  zsmul := (· • ·)

/-- SplitComplex forms a commutative ring. -/
instance instCommRing : CommRing SplitComplex where
  __ := instAddCommGroup
  left_distrib := fun a b c => by ext <;> simp only [mul_re, mul_im, add_re, add_im] <;> ring
  right_distrib := fun a b c => by ext <;> simp only [mul_re, mul_im, add_re, add_im] <;> ring
  zero_mul := fun _ => by ext <;> simp
  mul_zero := fun _ => by ext <;> simp
  mul_assoc := fun a b c => by ext <;> simp only [mul_re, mul_im] <;> ring
  one_mul := fun _ => by ext <;> simp
  mul_one := fun _ => by ext <;> simp
  mul_comm := fun a b => by ext <;> simp only [mul_re, mul_im] <;> ring

/-- The key property: j² = 1. -/
@[simp] theorem j_sq : j * j = 1 := by ext <;> simp [j]

/-- j is not equal to 1. -/
theorem j_ne_one : j ≠ 1 := by intro h; have := congrArg SplitComplex.im h; simp [j] at this

/-- j is not equal to -1. -/
theorem j_ne_neg_one : j ≠ -1 := by intro h; have := congrArg SplitComplex.im h; simp [j] at this

/-- Scalar multiplication by reals. -/
instance : SMul ℝ SplitComplex := ⟨fun r z => ⟨r * z.re, r * z.im⟩⟩

@[simp] theorem smul_re (r : ℝ) (z : SplitComplex) : (r • z).re = r * z.re := rfl
@[simp] theorem smul_im (r : ℝ) (z : SplitComplex) : (r • z).im = r * z.im := rfl

/-- SplitComplex is an ℝ-module. -/
instance instModule : Module ℝ SplitComplex where
  one_smul := fun z => by ext <;> simp
  mul_smul := fun r s z => by ext <;> simp [mul_assoc]
  smul_zero := fun r => by ext <;> simp
  smul_add := fun r z w => by ext <;> simp [mul_add]
  add_smul := fun r s z => by ext <;> simp [add_mul]
  zero_smul := fun z => by ext <;> simp

/-- SplitComplex is an ℝ-algebra. -/
noncomputable instance instAlgebra : Algebra ℝ SplitComplex :=
  Algebra.ofModule
    (fun r x y => by ext <;> simp only [smul_re, smul_im, mul_re, mul_im] <;> ring)
    (fun r x y => by ext <;> simp only [smul_re, smul_im, mul_re, mul_im] <;> ring)

@[simp]
theorem algebraMap_apply (r : ℝ) : algebraMap ℝ SplitComplex r = ⟨r, 0⟩ := by
  simp only [Algebra.algebraMap_eq_smul_one]
  ext <;> simp

/-- The split-complex "norm" (hyperbolic norm): N(a + bj) = a² - b².
Unlike complex norm, this can be negative! -/
def norm (z : SplitComplex) : ℝ := z.re ^ 2 - z.im ^ 2

@[simp] theorem norm_def (z : SplitComplex) : norm z = z.re ^ 2 - z.im ^ 2 := rfl

/-- Norm is multiplicative: N(zw) = N(z)N(w). -/
theorem norm_mul (z w : SplitComplex) : norm (z * w) = norm z * norm w := by
  simp only [norm_def, mul_re, mul_im]
  ring

/-- The conjugate: conj(a + bj) = a - bj. -/
def conj (z : SplitComplex) : SplitComplex := ⟨z.re, -z.im⟩

@[simp] theorem conj_re (z : SplitComplex) : (conj z).re = z.re := rfl
@[simp] theorem conj_im (z : SplitComplex) : (conj z).im = -z.im := rfl

/-- z * conj(z) = norm(z). -/
theorem mul_conj (z : SplitComplex) : z * conj z = norm z := by
  ext
  · simp [norm]; ring
  · simp; ring

/-- The positive idempotent: e₊ = (1 + j)/2 with e₊² = e₊. -/
noncomputable def idempotentPos : SplitComplex := ⟨1/2, 1/2⟩

/-- The negative idempotent: e₋ = (1 - j)/2 with e₋² = e₋. -/
noncomputable def idempotentNeg : SplitComplex := ⟨1/2, -1/2⟩

/-- e₊ is idempotent. -/
theorem idempotentPos_sq : idempotentPos * idempotentPos = idempotentPos := by
  ext <;> simp [idempotentPos] <;> ring

/-- e₋ is idempotent. -/
theorem idempotentNeg_sq : idempotentNeg * idempotentNeg = idempotentNeg := by
  ext <;> simp [idempotentNeg] <;> ring

/-- e₊ * e₋ = 0 (orthogonal idempotents). -/
theorem idempotent_orthogonal : idempotentPos * idempotentNeg = 0 := by
  ext <;> simp [idempotentPos, idempotentNeg] <;> ring

/-- e₊ + e₋ = 1 (partition of unity). -/
theorem idempotent_sum : idempotentPos + idempotentNeg = 1 := by
  ext <;> simp [idempotentPos, idempotentNeg] <;> ring

/-- Zero divisor example: (1 + j)(1 - j) = 0. -/
theorem zero_divisor_example : (1 + j) * (1 - j) = 0 := by
  ext <;> simp [j]

/-- Split-complex numbers have zero divisors, hence are not a division ring. -/
theorem has_zero_divisors : ∃ (a b : SplitComplex), a ≠ 0 ∧ b ≠ 0 ∧ a * b = 0 := by
  use 1 + j, 1 - j
  refine ⟨?_, ?_, zero_divisor_example⟩
  · intro h; have := congrArg SplitComplex.im h; simp [j] at this
  · intro h; have := congrArg SplitComplex.im h; simp [j] at this

/-- The bilinearProduct from SymmetricalFoundation with μ = +1 gives split-complex multiplication. -/
theorem mul_eq_bilinearProduct (z w : SplitComplex) :
    z * w = ⟨z.re * w.re + 1 * z.im * w.im, z.re * w.im + z.im * w.re⟩ := by
  ext <;> simp

/-- Isomorphism with ℝ × ℝ (as rings). The map is z ↦ (z.re + z.im, z.re - z.im). -/
noncomputable def toRealProd : SplitComplex →+* ℝ × ℝ where
  toFun z := (z.re + z.im, z.re - z.im)
  map_one' := by simp
  map_mul' := fun z w => by
    simp only [mul_re, mul_im, Prod.mk_mul_mk]
    apply Prod.ext <;> ring
  map_zero' := by simp
  map_add' := fun z w => by simp only [add_re, add_im, Prod.mk_add_mk]; apply Prod.ext <;> ring

/-- The inverse map from ℝ × ℝ to SplitComplex. -/
noncomputable def ofRealProd : ℝ × ℝ →+* SplitComplex where
  toFun p := ⟨(p.1 + p.2) / 2, (p.1 - p.2) / 2⟩
  map_one' := by ext <;> simp
  map_mul' := fun p q => by
    ext <;> simp only [mul_re, mul_im, Prod.fst_mul, Prod.snd_mul] <;> ring
  map_zero' := by ext <;> simp
  map_add' := fun p q => by ext <;> simp <;> ring

/-- SplitComplex ≃ ℝ × ℝ as rings. -/
noncomputable def equivRealProd : SplitComplex ≃+* ℝ × ℝ where
  toFun := toRealProd
  invFun := ofRealProd
  left_inv := fun z => by ext <;> simp [toRealProd, ofRealProd]
  right_inv := fun p => by
    simp only [toRealProd, ofRealProd, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    apply Prod.ext <;> field_simp <;> ring
  map_mul' := toRealProd.map_mul'
  map_add' := toRealProd.map_add'

end SplitComplex

end Mettapedia.Algebra
