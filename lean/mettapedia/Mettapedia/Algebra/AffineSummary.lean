import Mathlib.Algebra.Group.Hom.End
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Ordered affine summaries

Affine state updates have a representation-independent additive core and a
compact coefficient representation over any semiring. Composition follows
execution order: `first.compose second` applies `first` first. Consequently its
homogeneous matrix is `matrix second * matrix first`.

Associativity licenses regrouping an ordered stream, not permuting it. These
are laws of exact arithmetic; checked machine arithmetic needs a separate
realization. No running-time or floating-point equivalence is asserted.
-/

namespace Mettapedia.Algebra

/-- Additive endomorphism plus a translation, independent of continuity or
any particular scalar field. -/
@[ext] structure AffineAction (State : Type*) [AddMonoid State] where
  linear : AddMonoid.End State
  offset : State

namespace AffineAction

variable {State : Type*} [AddMonoid State]

def act (f : AffineAction State) (x : State) : State := f.linear x + f.offset

def compose (f g : AffineAction State) : AffineAction State :=
  ⟨g.linear.comp f.linear, g.linear f.offset + g.offset⟩

def identity : AffineAction State := ⟨AddMonoidHom.id State, 0⟩

@[simp] theorem act_compose (f g : AffineAction State) (x : State) :
    (f.compose g).act x = g.act (f.act x) := by
  change g.linear (f.linear x) + (g.linear f.offset + g.offset) =
    g.linear (f.linear x + f.offset) + g.offset
  rw [map_add, add_assoc]

@[simp] theorem act_identity (x : State) :
    (identity : AffineAction State).act x = x := by
  change x + 0 = x
  exact add_zero x

theorem compose_assoc (f g h : AffineAction State) :
    (f.compose g).compose h = f.compose (g.compose h) := by
  apply AffineAction.ext
  · rfl
  · change h.linear (g.linear f.offset + g.offset) + h.offset =
      h.linear (g.linear f.offset) + (h.linear g.offset + h.offset)
    rw [map_add, add_assoc]

end AffineAction

/-- A two-coefficient summary for `x ↦ scale * x + offset`. The number of
coefficients is fixed; their bit sizes need not be. -/
@[ext] structure AffineSummary (R : Type*) where
  scale : R
  offset : R
  deriving DecidableEq, Repr

namespace AffineSummary

variable {R : Type*} [Semiring R]

def act (f : AffineSummary R) (x : R) : R := f.scale * x + f.offset

def compose (f g : AffineSummary R) : AffineSummary R :=
  ⟨g.scale * f.scale, g.scale * f.offset + g.offset⟩

def identity : AffineSummary R := ⟨1, 0⟩

@[simp] theorem act_compose (f g : AffineSummary R) (x : R) :
    (f.compose g).act x = g.act (f.act x) := by
  simp [act, compose, mul_add, mul_assoc, add_assoc]

@[simp] theorem act_identity (x : R) :
    (identity : AffineSummary R).act x = x := by simp [act, identity]

theorem compose_assoc (f g h : AffineSummary R) :
    (f.compose g).compose h = f.compose (g.compose h) := by
  ext <;> simp [compose, mul_add, mul_assoc, add_assoc]

@[simp] theorem identity_compose (f : AffineSummary R) : identity.compose f = f := by
  ext <;> simp [identity, compose]

@[simp] theorem compose_identity (f : AffineSummary R) : f.compose identity = f := by
  ext <;> simp [identity, compose]

instance : Monoid (AffineSummary R) where
  one := identity
  mul := compose
  mul_assoc := compose_assoc
  one_mul := identity_compose
  mul_one := compose_identity

/-- The scalar representation realizes the additive core. -/
def toAction (f : AffineSummary R) : AffineAction R where
  linear := { toFun := fun x => f.scale * x
              map_zero' := mul_zero _
              map_add' := mul_add _ }
  offset := f.offset

@[simp] theorem toAction_act (f : AffineSummary R) (x : R) :
    f.toAction.act x = f.act x := rfl

theorem toAction_compose (f g : AffineSummary R) :
    (f.compose g).toAction = f.toAction.compose g.toAction := by
  apply AffineAction.ext
  · ext x
    exact mul_assoc _ _ _
  · rfl

/-- Homogeneous coordinates. This is a concrete two-by-two matrix, not a
definition of matrix multiplication in terms of affine composition. -/
def matrix (f : AffineSummary R) : Matrix (Fin 2) (Fin 2) R :=
  !![f.scale, f.offset; 0, 1]

theorem matrix_compose (f g : AffineSummary R) :
    (f.compose g).matrix = g.matrix * f.matrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, compose, Matrix.mul_apply, Fin.sum_univ_two]

theorem matrix_act (f : AffineSummary R) (x : R) :
    f.matrix.mulVec ![x, 1] = ![f.act x, 1] := by
  ext i
  fin_cases i <;> simp [matrix, act, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem matrix_injective : Function.Injective (matrix (R := R)) := by
  intro f g h
  have hs := congrArg (fun m => m 0 0) h
  have ho := congrArg (fun m => m 0 1) h
  exact AffineSummary.ext (by simpa [matrix] using hs) (by simpa [matrix] using ho)

/-- Ordered left fold of independently represented updates. -/
def run (updates : List (AffineSummary R)) (initial : R) : R :=
  updates.foldl (fun state update => update.act state) initial

theorem run_eq_summary (updates : List (AffineSummary R)) (initial : R) :
    run updates initial = updates.prod.act initial := by
  induction updates generalizing initial with
  | nil => change initial = (identity : AffineSummary R).act initial
           exact (act_identity initial).symm
  | cons f fs ih =>
      change run fs (f.act initial) = (f * fs.prod).act initial
      exact (ih _).trans (act_compose f fs.prod initial).symm

theorem run_append (before after : List (AffineSummary R)) (initial : R) :
    run (before ++ after) initial = run after (run before initial) := by
  simp [run, List.foldl_append]

theorem repeat_eq_power (update : AffineSummary R) (n : Nat) (initial : R) :
    run (List.replicate n update) initial = (update ^ n).act initial := by
  rw [run_eq_summary, List.prod_replicate]

/-- Reordering needs an additional commutation fact. -/
theorem swap_of_commute (f g : AffineSummary R)
    (h : f.compose g = g.compose f) (x : R) :
    g.act (f.act x) = f.act (g.act x) := by
  rw [← act_compose, h, act_compose]

/-- Associativity alone does not license changing the order. -/
theorem order_matters :
    (⟨2, 0⟩ : AffineSummary Int).act ((⟨1, 1⟩ : AffineSummary Int).act 0) ≠
    (⟨1, 1⟩ : AffineSummary Int).act ((⟨2, 0⟩ : AffineSummary Int).act 0) := by
  decide

end AffineSummary
end Mettapedia.Algebra
