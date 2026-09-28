import Mettapedia.Algebra.AffineSummary
import Mettapedia.Algebra.ActionFold
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The affine monoid: action, matrices, powers, commuting submonoids

`Mettapedia.Algebra.AffineSummary` defines the coefficient monoid of
`x ↦ scale * x + offset` over a semiring `R`, which need not be commutative.
Multiplication follows execution order: `f * g` applies `f` first. Hence
`⟨a, b⟩ * ⟨c, d⟩ = ⟨c * a, c * b + d⟩`, and the identity is `⟨1, 0⟩`. This
module develops the structure theory of that monoid.

* **Right action.** `x <• f = f.act x`, so `x <• f <• g = x <• (f * g)`. All
  fold, bracketing and scan laws of `Mettapedia.Algebra.ActionFold` apply.
* **Homogeneous matrices.** `matrixHom` is an injective monoid homomorphism
  into the *opposite* of `Matrix (Fin 2) (Fin 2) R`, sending `⟨a, b⟩` to
  `!![a, b; 0, 1]`. States are columns `![x, 1]` and the first update is the
  rightmost factor: `(f * g).matrix = g.matrix * f.matrix`, and an ordered
  stream has matrix `M(last) * ⋯ * M(first)` (`matrix_list_prod`). Over a
  commutative semiring, the transpose gives an order-preserving homomorphism
  into the matrix monoid itself, acting on rows `![x, 1]` (`rowMatrixHom`).
* **Powers.** Over any semiring,
  `f ^ n = ⟨a ^ n, (∑ i ∈ range n, a ^ i) * b⟩` (`pow_eq`). Over a ring,
  `(a - 1) * (f ^ n).offset = (a ^ n - 1) * b`. Over `ℤ` with `a ≠ 1`, the
  offset is `(a ^ n - 1) / (a - 1) * b` with exact division. Translations
  give `n • b`; the ratio `-1` alternates between `0` and `b`.
  `ActionFold.npowBinRec_eq_pow` licenses computing `f ^ n` by squaring.
* **Commutation.** `commute_iff` characterizes commuting pairs. Over a
  commutative ring, `⟨a, b⟩` and `⟨c, d⟩` commute iff
  `(c - 1) * b = (a - 1) * d`. Translations form a commuting submonoid
  isomorphic to `(R, +)` (`translationHom_injective`,
  `mrange_translationHom`). Scalings commute over a commutative semiring, and
  homotheties with a common centre commute. A translation and a scaling need
  not commute (`translation_scaling_not_commute`).
* **Module version.** The additive core `AffineAction State` (an additive
  endomorphism plus an offset, over any additive monoid) is a monoid under
  the same execution-order law. `toActionHom` embeds the scalar monoid in it.

The laws concern exact arithmetic in `R`. Machine integers, overflow,
evaluation cost and effects are outside this module.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra

open scoped RightActions
open MulOpposite Finset

namespace AffineSummary

variable {R : Type*}

section Semiring

variable [Semiring R]

/-! ## Coordinates of products -/

theorem mul_eq_compose (f g : AffineSummary R) : f * g = f.compose g := rfl

theorem one_eq_identity : (1 : AffineSummary R) = identity := rfl

@[simp] theorem mk_mul_mk (a b c d : R) :
    (⟨a, b⟩ * ⟨c, d⟩ : AffineSummary R) = ⟨c * a, c * b + d⟩ := rfl

@[simp] theorem scale_one : (1 : AffineSummary R).scale = 1 := rfl

@[simp] theorem offset_one : (1 : AffineSummary R).offset = 0 := rfl

@[simp] theorem scale_mul (f g : AffineSummary R) : (f * g).scale = g.scale * f.scale := rfl

@[simp] theorem offset_mul (f g : AffineSummary R) :
    (f * g).offset = g.scale * f.offset + g.offset := rfl

@[simp] theorem act_one (x : R) : (1 : AffineSummary R).act x = x := act_identity x

/-- Execution order: `f * g` applies `f`, then `g`. -/
@[simp] theorem act_mul (f g : AffineSummary R) (x : R) :
    (f * g).act x = g.act (f.act x) := act_compose f g x

/-! ## The right action on states -/

/-- Affine summaries act on states on the right: `x <• f = f.act x`. -/
instance : MulAction (AffineSummary R)ᵐᵒᵖ R where
  smul f x := f.unop.act x
  one_smul := act_one
  mul_smul f g x := act_mul g.unop f.unop x

@[simp] theorem op_smul_eq_act (f : AffineSummary R) (x : R) : x <• f = f.act x := rfl

/-- The ordered run of the base module is the right action of the ordered
product. -/
theorem run_eq_op_smul (updates : List (AffineSummary R)) (x : R) :
    run updates x = x <• updates.prod :=
  ActionFold.foldl_op_smul updates x

/-! ## Homogeneous matrices -/

@[simp] theorem matrix_one : (1 : AffineSummary R).matrix = 1 := by
  rw [Matrix.one_fin_two]
  rfl

theorem matrix_mul (f g : AffineSummary R) : (f * g).matrix = g.matrix * f.matrix :=
  matrix_compose f g

/-- Homogeneous coordinates as a monoid homomorphism into the opposite
matrix monoid. Execution order `f * g` becomes the matrix product
`M g * M f`. -/
def matrixHom : AffineSummary R →* (Matrix (Fin 2) (Fin 2) R)ᵐᵒᵖ where
  toFun f := op f.matrix
  map_one' := by rw [matrix_one, op_one]
  map_mul' f g := by rw [matrix_mul, op_mul]

@[simp] theorem matrixHom_apply (f : AffineSummary R) : matrixHom f = op f.matrix := rfl

theorem matrixHom_injective : Function.Injective (matrixHom (R := R)) :=
  fun _ _ h => matrix_injective (op_injective h)

theorem matrix_pow (f : AffineSummary R) (n : ℕ) : (f ^ n).matrix = f.matrix ^ n := by
  simpa using congrArg unop (map_pow (matrixHom (R := R)) f n)

/-- The matrix of an ordered stream is the product of the item matrices in
reverse order: the first update is the rightmost factor. -/
theorem matrix_list_prod (l : List (AffineSummary R)) :
    l.prod.matrix = (l.map matrix).reverse.prod := by
  induction l with
  | nil => simp
  | cons f l ih => simp [matrix_mul, ih]

/-! ## Powers: constant items in closed form -/

@[simp] theorem scale_pow (f : AffineSummary R) (n : ℕ) : (f ^ n).scale = f.scale ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, scale_mul, ih, pow_succ']

theorem offset_pow (f : AffineSummary R) (n : ℕ) :
    (f ^ n).offset = (∑ i ∈ range n, f.scale ^ i) * f.offset := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, offset_mul, ih, geom_sum_succ, ← mul_assoc, add_mul, one_mul]

/-- **Closed form of a power**, over any semiring. -/
theorem pow_eq (f : AffineSummary R) (n : ℕ) :
    f ^ n = ⟨f.scale ^ n, (∑ i ∈ range n, f.scale ^ i) * f.offset⟩ :=
  AffineSummary.ext (scale_pow f n) (offset_pow f n)

theorem act_pow (f : AffineSummary R) (n : ℕ) (x : R) :
    (f ^ n).act x = f.scale ^ n * x + (∑ i ∈ range n, f.scale ^ i) * f.offset := by
  simp only [act, scale_pow, offset_pow]

/-! ## Translations and scalings -/

/-- The translation `x ↦ x + b`. -/
def translation (b : R) : AffineSummary R := ⟨1, b⟩

/-- The scaling `x ↦ a * x`. -/
def scaling (a : R) : AffineSummary R := ⟨a, 0⟩

@[simp] theorem translation_scale (b : R) : (translation b).scale = 1 := rfl

@[simp] theorem translation_offset (b : R) : (translation b).offset = b := rfl

@[simp] theorem scaling_scale (a : R) : (scaling a).scale = a := rfl

@[simp] theorem scaling_offset (a : R) : (scaling a).offset = 0 := rfl

@[simp] theorem act_translation (b x : R) : (translation b).act x = x + b := by
  simp [act, translation]

@[simp] theorem act_scaling (a x : R) : (scaling a).act x = a * x := by
  simp [act, scaling]

theorem translation_zero : translation (0 : R) = 1 := rfl

theorem translation_add (b c : R) :
    translation (b + c) = translation b * translation c := by
  ext <;> simp [translation]

theorem scaling_one : scaling (1 : R) = 1 := rfl

/-- Scalings compose in execution order: scale by `a`, then by `c`. -/
theorem scaling_mul (a c : R) : scaling (c * a) = scaling a * scaling c := by
  ext <;> simp [scaling]

theorem translation_pow (b : R) (n : ℕ) : translation b ^ n = translation (n • b) := by
  rw [pow_eq]
  ext <;> simp [translation, nsmul_eq_mul]

theorem scaling_pow (a : R) (n : ℕ) : scaling a ^ n = scaling (a ^ n) := by
  rw [pow_eq]
  ext <;> simp [scaling]

/-- Translations form a monoid isomorphic to `(R, +)`. -/
def translationHom : Multiplicative R →* AffineSummary R where
  toFun b := translation b.toAdd
  map_one' := translation_zero
  map_mul' b c := translation_add b.toAdd c.toAdd

theorem translationHom_injective : Function.Injective (translationHom (R := R)) :=
  fun _ _ h => Multiplicative.toAdd.injective (congrArg AffineSummary.offset h)

/-- The translation submonoid: exactly the summaries of scale `1`. -/
def translations : Submonoid (AffineSummary R) where
  carrier := {f | f.scale = 1}
  mul_mem' {f g} hf hg := by
    change g.scale * f.scale = 1
    rw [show f.scale = 1 from hf, show g.scale = 1 from hg, one_mul]
  one_mem' := rfl

theorem mem_translations {f : AffineSummary R} : f ∈ translations ↔ f.scale = 1 := Iff.rfl

theorem eq_translation_of_mem {f : AffineSummary R} (hf : f ∈ translations) :
    f = translation f.offset :=
  AffineSummary.ext hf rfl

/-- The translation submonoid is the image of `(R, +)`. With
`translationHom_injective`, it is isomorphic to `(R, +)`. -/
theorem mrange_translationHom : MonoidHom.mrange (translationHom (R := R)) = translations := by
  ext f
  constructor
  · rintro ⟨b, rfl⟩
    rfl
  · intro hf
    exact ⟨Multiplicative.ofAdd f.offset, (eq_translation_of_mem hf).symm⟩

/-- The scaling submonoid: exactly the summaries of offset `0`. -/
def scalings : Submonoid (AffineSummary R) where
  carrier := {f | f.offset = 0}
  mul_mem' {f g} hf hg := by
    change g.scale * f.offset + g.offset = 0
    rw [show f.offset = 0 from hf, show g.offset = 0 from hg, mul_zero, add_zero]
  one_mem' := rfl

theorem mem_scalings {f : AffineSummary R} : f ∈ scalings ↔ f.offset = 0 := Iff.rfl

/-! ## Commutation -/

/-- Commuting pairs, coordinate by coordinate. -/
theorem commute_iff (f g : AffineSummary R) :
    Commute f g ↔ g.scale * f.scale = f.scale * g.scale ∧
      g.scale * f.offset + g.offset = f.scale * g.offset + f.offset := by
  constructor
  · intro h
    exact ⟨congrArg scale h, congrArg offset h⟩
  · rintro ⟨hs, ho⟩
    exact AffineSummary.ext hs ho

/-- Translations commute: reordering a stream of translations is licensed. -/
theorem translations_commute :
    ∀ f ∈ translations (R := R), ∀ g ∈ translations (R := R), Commute f g := by
  intro f hf g hg
  rw [commute_iff, show f.scale = 1 from hf, show g.scale = 1 from hg]
  exact ⟨rfl, by rw [one_mul, one_mul, add_comm]⟩

theorem commute_translation (b c : R) : Commute (translation b) (translation c) :=
  translations_commute _ rfl _ rfl

/-- Scalings by commuting scalars commute. -/
theorem commute_scaling {a c : R} (h : Commute a c) : Commute (scaling a) (scaling c) := by
  rw [commute_iff]
  exact ⟨h.eq.symm, by simp⟩

end Semiring

section CommSemiring

variable [CommSemiring R]

/-- Over a commutative semiring, the transposed homogeneous matrix
`!![a, 0; b, 1]` is an order-preserving monoid homomorphism. States are rows
`![x, 1]` multiplied on the right, and the first update is the leftmost
factor. -/
def rowMatrixHom : AffineSummary R →* Matrix (Fin 2) (Fin 2) R where
  toFun f := f.matrix.transpose
  map_one' := by rw [matrix_one, Matrix.transpose_one]
  map_mul' f g := by rw [matrix_mul, Matrix.transpose_mul]

@[simp] theorem rowMatrixHom_apply (f : AffineSummary R) :
    rowMatrixHom f = f.matrix.transpose := rfl

/-- The row convention acts as the map. -/
theorem vecMul_rowMatrixHom (f : AffineSummary R) (x : R) :
    Matrix.vecMul ![x, 1] (rowMatrixHom f) = ![f.act x, 1] := by
  rw [rowMatrixHom_apply, Matrix.vecMul_transpose, matrix_act]

/-- Over a commutative semiring, scalings commute: reordering a stream of
scalings is licensed. -/
theorem scalings_commute :
    ∀ f ∈ scalings (R := R), ∀ g ∈ scalings (R := R), Commute f g := by
  intro f hf g hg
  rw [commute_iff, show f.offset = 0 from hf, show g.offset = 0 from hg]
  exact ⟨mul_comm _ _, by simp⟩

end CommSemiring

section Ring

variable [Ring R]

/-- Closed form of a power without division, over any ring. -/
theorem sub_one_mul_offset_pow (f : AffineSummary R) (n : ℕ) :
    (f.scale - 1) * (f ^ n).offset = (f.scale ^ n - 1) * f.offset := by
  rw [offset_pow, ← mul_assoc, mul_geom_sum]

/-- An update of ratio `-1`, such as `x ↦ b - x`, returns on even powers. -/
theorem offset_pow_of_scale_eq_neg_one (f : AffineSummary R) (h : f.scale = -1) (n : ℕ) :
    (f ^ n).offset = if Even n then 0 else f.offset := by
  rw [offset_pow, h, neg_one_geom_sum]
  split_ifs <;> simp

/-- The homothety with centre `p` and ratio `a`: `x ↦ p + a * (x - p)`. -/
def homothety (p a : R) : AffineSummary R := ⟨a, (1 - a) * p⟩

theorem act_homothety (p a x : R) : (homothety p a).act x = p + a * (x - p) := by
  simp only [act, homothety, sub_mul, one_mul, mul_sub]
  rw [sub_eq_add_neg, sub_eq_add_neg, add_left_comm]

end Ring

section CommRing

variable [CommRing R]

/-- **Commutation criterion.** Over a commutative ring, `⟨a, b⟩` and
`⟨c, d⟩` commute iff `(c - 1) * b = (a - 1) * d`. When neither map is a
translation, this says that both fix the same point. -/
theorem commute_iff_of_commRing (f g : AffineSummary R) :
    Commute f g ↔ (g.scale - 1) * f.offset = (f.scale - 1) * g.offset := by
  rw [commute_iff]
  constructor
  · rintro ⟨-, h⟩
    linear_combination h
  · intro h
    exact ⟨mul_comm _ _, by linear_combination h⟩

/-- Homotheties with a common centre commute. Scalings are the centre `0`. -/
theorem commute_homothety (p a c : R) : Commute (homothety p a) (homothety p c) := by
  rw [commute_iff_of_commRing]
  simp only [homothety]
  ring

end CommRing

/-- Integer closed form of a constant non-translation update, with exact
division. -/
theorem offset_pow_int (f : AffineSummary ℤ) (h : f.scale ≠ 1) (n : ℕ) :
    (f ^ n).offset = (f.scale ^ n - 1) / (f.scale - 1) * f.offset := by
  rw [offset_pow, ← mul_geom_sum, Int.mul_ediv_cancel_left _ (sub_ne_zero.mpr h)]

/-- A translation and a scaling need not commute: `x ↦ x + 1` then
`x ↦ 2 * x` differs from the reverse order. -/
theorem translation_scaling_not_commute :
    ¬ Commute (translation (1 : ℤ)) (scaling 2) := by
  rw [commute_iff_of_commRing]
  decide

end AffineSummary

/-! ## The additive core is a monoid -/

namespace AffineAction

variable {State : Type*} [AddMonoid State]

@[simp] theorem identity_compose (f : AffineAction State) : identity.compose f = f := by
  apply AffineAction.ext
  · ext x
    rfl
  · change f.linear 0 + f.offset = f.offset
    rw [map_zero, zero_add]

@[simp] theorem compose_identity (f : AffineAction State) : f.compose identity = f := by
  apply AffineAction.ext
  · ext x
    rfl
  · change f.offset + 0 = f.offset
    exact add_zero _

/-- The additive affine core is a monoid under execution-order
composition. -/
instance : Monoid (AffineAction State) where
  mul := compose
  one := identity
  mul_assoc := compose_assoc
  one_mul := identity_compose
  mul_one := compose_identity

theorem mul_eq_compose (f g : AffineAction State) : f * g = f.compose g := rfl

@[simp] theorem act_one (x : State) : (1 : AffineAction State).act x = x := act_identity x

/-- Execution order: `f * g` applies `f`, then `g`. -/
@[simp] theorem act_mul (f g : AffineAction State) (x : State) :
    (f * g).act x = g.act (f.act x) := act_compose f g x

/-- The additive core acts on states on the right. -/
instance : MulAction (AffineAction State)ᵐᵒᵖ State where
  smul f x := f.unop.act x
  one_smul := act_one
  mul_smul f g x := act_mul g.unop f.unop x

@[simp] theorem op_smul_eq_act (f : AffineAction State) (x : State) : x <• f = f.act x := rfl

end AffineAction

namespace AffineSummary

variable {R : Type*} [Semiring R]

/-- The scalar coefficient monoid embeds in the additive core. -/
def toActionHom : AffineSummary R →* AffineAction R where
  toFun := toAction
  map_one' := by
    apply AffineAction.ext
    · ext x
      exact one_mul x
    · rfl
  map_mul' := toAction_compose

@[simp] theorem toActionHom_apply (f : AffineSummary R) : toActionHom f = f.toAction := rfl

theorem toActionHom_injective : Function.Injective (toActionHom (R := R)) := by
  intro f g h
  apply AffineSummary.ext
  · have hlin : f.scale * 1 = g.scale * 1 :=
      congrArg (fun c : AffineAction R => c.linear 1) h
    simpa using hlin
  · exact congrArg AffineAction.offset h

end AffineSummary

end Mettapedia.Algebra
