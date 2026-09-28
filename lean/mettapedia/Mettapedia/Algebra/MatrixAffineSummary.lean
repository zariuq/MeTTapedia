import Mettapedia.Algebra.AffineMonoid
import Mathlib.Data.Matrix.Block

/-!
# Affine maps of finite-dimensional state over a semiring

A *linear state* fold step has the form `x ↦ M *ᵥ x + v` on `ι → R`. Here
`M : Matrix ι ι R`, `v : ι → R`, `ι` is any finite index type such as
`Fin n`, and `R` is any semiring, not necessarily commutative. Such steps are
the transitions of weighted automata. Examples are `(ℤ, +, *)` for exact
arithmetic, the tropical semiring for shortest paths (instantiated as edge
relaxation in `Mettapedia.GSLT.Dynamics.AffineFoldCompilation`), and the
Boolean semiring for reachability. `MatrixAffineSummary ι R` stores the two
coefficients. Its algebra is the scalar affine algebra of
`Mettapedia.Algebra.AffineMonoid`, one dimension up.

* **Monoid in execution order.** `f * g` applies `f` first, so
  `f * g = ⟨M_g * M_f, M_g *ᵥ v_f + v_g⟩` (`act_mul`, `linear_mul`,
  `offset_mul`).
* **Right action** on `ι → R`. Every law of `Mettapedia.Algebra.ActionFold`
  applies: fold exactness, bracketing independence, prefix and blocked scans,
  and the commuting-reorder license. `run_eq_prod_act` records the
  sequential form.
* **Block homogeneous matrices.** `homogeneousHom` is an injective monoid
  homomorphism into the opposite of `Matrix (ι ⊕ Unit) (ι ⊕ Unit) R`, with
  `f ↦ [[M, v], [0, 1]]`. It reverses order, as in the scalar case.
* **Additive core.** `toActionHom` embeds this monoid faithfully in the
  monoid `AffineAction (ι → R)` of additive endomorphisms with offsets.
* **Powers.** `(f ^ n).linear = M ^ n` and
  `(f ^ n).offset = (∑ i ∈ range n, M ^ i) *ᵥ v`.
* **Dimension one.** `ofScalar : AffineSummary R ≃* MatrixAffineSummary Unit R`.

These are laws of exact semiring arithmetic. Cost, numeric representation
and effects are outside this module.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra

open scoped RightActions
open MulOpposite Matrix Finset

/-- An affine map `x ↦ linear *ᵥ x + offset` of finite-dimensional state,
stored by its coefficients. -/
@[ext] structure MatrixAffineSummary (ι : Type*) (R : Type*) where
  linear : Matrix ι ι R
  offset : ι → R

namespace MatrixAffineSummary

variable {ι R : Type*} [Fintype ι] [Semiring R]

/-- Apply the map to a state vector. -/
def act (f : MatrixAffineSummary ι R) (x : ι → R) : ι → R := f.linear *ᵥ x + f.offset

/-- Execution-order composition: `f.compose g` applies `f`, then `g`. -/
def compose (f g : MatrixAffineSummary ι R) : MatrixAffineSummary ι R :=
  ⟨g.linear * f.linear, g.linear *ᵥ f.offset + g.offset⟩

@[simp] theorem act_compose (f g : MatrixAffineSummary ι R) (x : ι → R) :
    (f.compose g).act x = g.act (f.act x) := by
  simp only [act, compose, mulVec_add, mulVec_mulVec, add_assoc]

theorem compose_assoc (f g h : MatrixAffineSummary ι R) :
    (f.compose g).compose h = f.compose (g.compose h) := by
  apply MatrixAffineSummary.ext
  · simp [compose, Matrix.mul_assoc]
  · simp [compose, mulVec_add, mulVec_mulVec, add_assoc]

variable [DecidableEq ι]

/-- The identity map. -/
def identity : MatrixAffineSummary ι R := ⟨1, 0⟩

@[simp] theorem act_identity (x : ι → R) : (identity : MatrixAffineSummary ι R).act x = x := by
  simp [act, identity]

@[simp] theorem identity_compose (f : MatrixAffineSummary ι R) : identity.compose f = f := by
  apply MatrixAffineSummary.ext <;> simp [compose, identity]

@[simp] theorem compose_identity (f : MatrixAffineSummary ι R) : f.compose identity = f := by
  apply MatrixAffineSummary.ext <;> simp [compose, identity]

instance : Monoid (MatrixAffineSummary ι R) where
  mul := compose
  one := identity
  mul_assoc := compose_assoc
  one_mul := identity_compose
  mul_one := compose_identity

theorem mul_eq_compose (f g : MatrixAffineSummary ι R) : f * g = f.compose g := rfl

theorem one_eq_identity : (1 : MatrixAffineSummary ι R) = identity := rfl

@[simp] theorem linear_one : (1 : MatrixAffineSummary ι R).linear = 1 := rfl

@[simp] theorem offset_one : (1 : MatrixAffineSummary ι R).offset = 0 := rfl

@[simp] theorem linear_mul (f g : MatrixAffineSummary ι R) :
    (f * g).linear = g.linear * f.linear := rfl

@[simp] theorem offset_mul (f g : MatrixAffineSummary ι R) :
    (f * g).offset = g.linear *ᵥ f.offset + g.offset := rfl

@[simp] theorem act_one (x : ι → R) : (1 : MatrixAffineSummary ι R).act x = x :=
  act_identity x

/-- Execution order: `f * g` applies `f`, then `g`. -/
@[simp] theorem act_mul (f g : MatrixAffineSummary ι R) (x : ι → R) :
    (f * g).act x = g.act (f.act x) := act_compose f g x

/-! ## Right action and ordered runs -/

/-- The maps act on state vectors on the right: `x <• f = f.act x`. -/
instance : MulAction (MatrixAffineSummary ι R)ᵐᵒᵖ (ι → R) where
  smul f x := f.unop.act x
  one_smul := act_one
  mul_smul f g x := act_mul g.unop f.unop x

@[simp] theorem op_smul_eq_act (f : MatrixAffineSummary ι R) (x : ι → R) :
    x <• f = f.act x := rfl

omit [DecidableEq ι] in
/-- Ordered left fold of independently represented updates. -/
def run (updates : List (MatrixAffineSummary ι R)) (initial : ι → R) : ι → R :=
  updates.foldl (fun state update => update.act state) initial

/-- **Fold exactness** for linear-state updates. -/
theorem run_eq_prod_act (updates : List (MatrixAffineSummary ι R)) (initial : ι → R) :
    run updates initial = updates.prod.act initial :=
  ActionFold.foldl_op_smul updates initial

/-! ## Block homogeneous matrices -/

omit [DecidableEq ι] in
/-- The block homogeneous matrix `[[linear, offset], [0, 1]]`. -/
def homogeneous (f : MatrixAffineSummary ι R) : Matrix (ι ⊕ Unit) (ι ⊕ Unit) R :=
  fromBlocks f.linear (replicateCol Unit f.offset) 0 1

omit [DecidableEq ι] in
/-- The homogeneous matrix acts on the column `(x, 1)` as the map on `x`. -/
theorem homogeneous_mulVec (f : MatrixAffineSummary ι R) (x : ι → R) :
    f.homogeneous *ᵥ Sum.elim x (fun _ => 1) = Sum.elim (f.act x) (fun _ => 1) := by
  ext i
  cases i <;> simp [homogeneous, act, mulVec, dotProduct]

@[simp] theorem homogeneous_one : (1 : MatrixAffineSummary ι R).homogeneous = 1 := by
  simp [homogeneous, fromBlocks_one]

theorem homogeneous_mul (f g : MatrixAffineSummary ι R) :
    (f * g).homogeneous = g.homogeneous * f.homogeneous := by
  simp [homogeneous, fromBlocks_multiply, replicateCol_add, replicateCol_mulVec]

omit [Fintype ι] [DecidableEq ι] in
theorem homogeneous_injective : Function.Injective (homogeneous (ι := ι) (R := R)) := by
  intro f g h
  rw [homogeneous, homogeneous, fromBlocks_inj] at h
  exact MatrixAffineSummary.ext h.1 (replicateCol_injective h.2.1)

/-- Block homogeneous coordinates as a monoid homomorphism into the opposite
matrix monoid: execution order `f * g` becomes `H g * H f`. -/
def homogeneousHom : MatrixAffineSummary ι R →* (Matrix (ι ⊕ Unit) (ι ⊕ Unit) R)ᵐᵒᵖ where
  toFun f := op f.homogeneous
  map_one' := by rw [homogeneous_one, op_one]
  map_mul' f g := by rw [homogeneous_mul, op_mul]

theorem homogeneousHom_injective : Function.Injective (homogeneousHom (ι := ι) (R := R)) :=
  fun _ _ h => homogeneous_injective (op_injective h)

/-! ## The additive core -/

omit [DecidableEq ι] in
/-- Matrix-vector multiplication as an additive endomorphism of states. -/
def mulVecEnd (A : Matrix ι ι R) : AddMonoid.End (ι → R) where
  toFun x := A *ᵥ x
  map_zero' := mulVec_zero A
  map_add' := mulVec_add A

omit [DecidableEq ι] in
/-- Forget the matrix representation and keep the additive affine map. -/
def toAction (f : MatrixAffineSummary ι R) : AffineAction (ι → R) :=
  ⟨mulVecEnd f.linear, f.offset⟩

omit [DecidableEq ι] in
@[simp] theorem toAction_act (f : MatrixAffineSummary ι R) (x : ι → R) :
    f.toAction.act x = f.act x := rfl

/-- The linear-state monoid is a submonoid of the additive core. -/
def toActionHom : MatrixAffineSummary ι R →* AffineAction (ι → R) where
  toFun := toAction
  map_one' := by
    apply AffineAction.ext
    · refine AddMonoidHom.ext fun x => ?_
      exact one_mulVec x
    · rfl
  map_mul' f g := by
    apply AffineAction.ext
    · refine AddMonoidHom.ext fun x => ?_
      exact (mulVec_mulVec x g.linear f.linear).symm
    · rfl

theorem toActionHom_injective : Function.Injective (toActionHom (ι := ι) (R := R)) := by
  intro f g h
  apply MatrixAffineSummary.ext
  · ext i j
    have hcol : f.linear *ᵥ Pi.single j 1 = g.linear *ᵥ Pi.single j 1 :=
      congrArg (fun c : AffineAction (ι → R) => c.linear (Pi.single j 1)) h
    simpa [mulVec_single_one] using congrFun hcol i
  · exact congrArg AffineAction.offset h

/-! ## Powers -/

@[simp] theorem linear_pow (f : MatrixAffineSummary ι R) (n : ℕ) :
    (f ^ n).linear = f.linear ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, linear_mul, ih, pow_succ']

theorem offset_pow (f : MatrixAffineSummary ι R) (n : ℕ) :
    (f ^ n).offset = (∑ i ∈ range n, f.linear ^ i) *ᵥ f.offset := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, offset_mul, ih, mulVec_mulVec, geom_sum_succ, add_mulVec, one_mulVec]

/-- **Closed form of a power** of a linear-state update. -/
theorem pow_eq (f : MatrixAffineSummary ι R) (n : ℕ) :
    f ^ n = ⟨f.linear ^ n, (∑ i ∈ range n, f.linear ^ i) *ᵥ f.offset⟩ :=
  MatrixAffineSummary.ext (linear_pow f n) (offset_pow f n)

/-! ## Dimension one -/

/-- The scalar affine monoid is the one-dimensional linear-state monoid. -/
def ofScalar : AffineSummary R ≃* MatrixAffineSummary Unit R where
  toFun f := ⟨Matrix.of fun _ _ => f.scale, fun _ => f.offset⟩
  invFun g := ⟨g.linear () (), g.offset ()⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' f g := by
    apply MatrixAffineSummary.ext
    · ext i j
      simp [Matrix.mul_apply]
    · ext i
      simp [mulVec, dotProduct]

@[simp] theorem ofScalar_linear (f : AffineSummary R) :
    (ofScalar f).linear = Matrix.of fun _ _ => f.scale := rfl

@[simp] theorem ofScalar_offset (f : AffineSummary R) :
    (ofScalar f).offset = fun _ => f.offset := rfl

theorem ofScalar_act (f : AffineSummary R) (x : R) :
    (ofScalar f).act (fun _ => x) = fun _ => f.act x := by
  ext i
  simp [act, AffineSummary.act, mulVec, dotProduct]

end MatrixAffineSummary

end Mettapedia.Algebra
