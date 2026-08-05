import Mathlib.Tactic

/-!
# Proof-carrying frozen-cone specialization

This file isolates a semiring-polynomial core of frozen supercompilation for
predictive-coding networks.  An expression has static inputs, which are fixed
during an inner solve, and dynamic inputs, which may change on every settling
sweep.  `Expr.residualize` substitutes the static inputs and performs genuine
constant folding.  The resulting residual program preserves both values and
formal derivatives with respect to every dynamic input.

The transformation is intentionally nontrivial: static-only subexpressions
collapse to constants, while mixed subexpressions retain their dynamic data
dependencies.  The final fixture shows why a dynamic dependency may not be
misclassified as frozen even when the incorrectly cached program agrees at one
observed state.

The formalization was motivated by a frozen-supercompilation proposal for
predictive-coding networks.  It proves exact symbolic semantics, not a runtime
speedup or a floating-point equivalence claim.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
namespace FrozenConeSpecialization

universe uR uS uD

/-- A polynomial expression whose variables are partitioned into values fixed
during specialization and values that remain dynamic. -/
inductive Expr (R : Type uR) (Static : Type uS) (Dynamic : Type uD) where
  | const : R → Expr R Static Dynamic
  | static : Static → Expr R Static Dynamic
  | dynamic : Dynamic → Expr R Static Dynamic
  | add : Expr R Static Dynamic → Expr R Static Dynamic → Expr R Static Dynamic
  | mul : Expr R Static Dynamic → Expr R Static Dynamic → Expr R Static Dynamic
  deriving Repr

/-- A residual expression contains no static variables. -/
inductive ResidualExpr (R : Type uR) (Dynamic : Type uD) where
  | const : R → ResidualExpr R Dynamic
  | dynamic : Dynamic → ResidualExpr R Dynamic
  | add : ResidualExpr R Dynamic → ResidualExpr R Dynamic → ResidualExpr R Dynamic
  | mul : ResidualExpr R Dynamic → ResidualExpr R Dynamic → ResidualExpr R Dynamic
  deriving Repr

namespace Expr

variable {R : Type uR} {Static : Type uS} {Dynamic : Type uD}

def eval [Add R] [Mul R] (staticEnv : Static → R) (dynamicEnv : Dynamic → R) :
    Expr R Static Dynamic → R
  | .const value => value
  | .static index => staticEnv index
  | .dynamic index => dynamicEnv index
  | .add left right => eval staticEnv dynamicEnv left + eval staticEnv dynamicEnv right
  | .mul left right => eval staticEnv dynamicEnv left * eval staticEnv dynamicEnv right

/-- Whether an expression contains no dynamic variable. -/
def dynamicFree : Expr R Static Dynamic → Bool
  | .const _ => true
  | .static _ => true
  | .dynamic _ => false
  | .add left right => dynamicFree left && dynamicFree right
  | .mul left right => dynamicFree left && dynamicFree right

def formalDeriv [DecidableEq Dynamic] [Semiring R] (target : Dynamic) :
    Expr R Static Dynamic → Expr R Static Dynamic
  | .const _ => .const 0
  | .static _ => .const 0
  | .dynamic index => .const (if index = target then 1 else 0)
  | .add left right => .add (formalDeriv target left) (formalDeriv target right)
  | .mul left right =>
      .add (.mul (formalDeriv target left) right)
        (.mul left (formalDeriv target right))

end Expr

namespace ResidualExpr

variable {R : Type uR} {Dynamic : Type uD}

def eval [Add R] [Mul R] (dynamicEnv : Dynamic → R) : ResidualExpr R Dynamic → R
  | .const value => value
  | .dynamic index => dynamicEnv index
  | .add left right => eval dynamicEnv left + eval dynamicEnv right
  | .mul left right => eval dynamicEnv left * eval dynamicEnv right

/-- Constant-fold addition when both residual operands are already static. -/
def foldAdd [Add R] : ResidualExpr R Dynamic → ResidualExpr R Dynamic →
    ResidualExpr R Dynamic
  | .const left, .const right => .const (left + right)
  | left, right => .add left right

/-- Constant-fold multiplication when both residual operands are already static. -/
def foldMul [Mul R] : ResidualExpr R Dynamic → ResidualExpr R Dynamic →
    ResidualExpr R Dynamic
  | .const left, .const right => .const (left * right)
  | left, right => .mul left right

def formalDeriv [DecidableEq Dynamic] [Semiring R] (target : Dynamic) :
    ResidualExpr R Dynamic → ResidualExpr R Dynamic
  | .const _ => .const 0
  | .dynamic index => .const (if index = target then 1 else 0)
  | .add left right => .add (formalDeriv target left) (formalDeriv target right)
  | .mul left right =>
      .add (.mul (formalDeriv target left) right)
        (.mul left (formalDeriv target right))

@[simp] theorem eval_foldAdd [Add R] [Mul R] (dynamicEnv : Dynamic → R)
    (left right : ResidualExpr R Dynamic) :
    eval dynamicEnv (foldAdd left right) =
      eval dynamicEnv left + eval dynamicEnv right := by
  cases left <;> cases right <;> simp [foldAdd, eval]

@[simp] theorem eval_foldMul [Add R] [Mul R] (dynamicEnv : Dynamic → R)
    (left right : ResidualExpr R Dynamic) :
    eval dynamicEnv (foldMul left right) =
      eval dynamicEnv left * eval dynamicEnv right := by
  cases left <;> cases right <;> simp [foldMul, eval]

@[simp] theorem eval_formalDeriv_foldAdd [DecidableEq Dynamic] [Semiring R]
    (target : Dynamic) (dynamicEnv : Dynamic → R)
    (left right : ResidualExpr R Dynamic) :
    eval dynamicEnv (formalDeriv target (foldAdd left right)) =
      eval dynamicEnv (formalDeriv target left) +
        eval dynamicEnv (formalDeriv target right) := by
  cases left <;> cases right <;> simp [foldAdd, formalDeriv, eval]

@[simp] theorem eval_formalDeriv_foldMul [DecidableEq Dynamic] [Semiring R]
    (target : Dynamic) (dynamicEnv : Dynamic → R)
    (left right : ResidualExpr R Dynamic) :
    eval dynamicEnv (formalDeriv target (foldMul left right)) =
      eval dynamicEnv (formalDeriv target left) * eval dynamicEnv right +
        eval dynamicEnv left * eval dynamicEnv (formalDeriv target right) := by
  cases left <;> cases right <;> simp [foldMul, formalDeriv, eval]

end ResidualExpr

namespace Expr

variable {R : Type uR} {Static : Type uS} {Dynamic : Type uD}

/-- Substitute all static inputs and fold every newly static subexpression. -/
def residualize [Add R] [Mul R] (staticEnv : Static → R) :
    Expr R Static Dynamic → ResidualExpr R Dynamic
  | .const value => .const value
  | .static index => .const (staticEnv index)
  | .dynamic index => .dynamic index
  | .add left right =>
      ResidualExpr.foldAdd (residualize staticEnv left) (residualize staticEnv right)
  | .mul left right =>
      ResidualExpr.foldMul (residualize staticEnv left) (residualize staticEnv right)

/-- Frozen-cone specialization preserves the value for every dynamic state. -/
theorem eval_residualize [Add R] [Mul R] (staticEnv : Static → R)
    (dynamicEnv : Dynamic → R) (expr : Expr R Static Dynamic) :
    ResidualExpr.eval dynamicEnv (residualize staticEnv expr) =
      eval staticEnv dynamicEnv expr := by
  induction expr with
  | const => rfl
  | static => rfl
  | dynamic => rfl
  | add left right ihLeft ihRight =>
      simp [residualize, eval, ihLeft, ihRight]
  | mul left right ihLeft ihRight =>
      simp [residualize, eval, ihLeft, ihRight]

/-- Every dynamic-free cone is genuinely hoisted to one residual constant. -/
theorem residualize_eq_const_of_dynamicFree [Add R] [Mul R]
    (staticEnv : Static → R) (dynamicEnv : Dynamic → R)
    (expr : Expr R Static Dynamic) (hfree : expr.dynamicFree = true) :
    residualize staticEnv expr = .const (eval staticEnv dynamicEnv expr) := by
  induction expr with
  | const => rfl
  | static => rfl
  | dynamic =>
      simp [dynamicFree] at hfree
  | add left right ihLeft ihRight =>
      simp only [dynamicFree, Bool.and_eq_true] at hfree
      simp [residualize, eval, ResidualExpr.foldAdd,
        ihLeft hfree.1, ihRight hfree.2]
  | mul left right ihLeft ihRight =>
      simp only [dynamicFree, Bool.and_eq_true] at hfree
      simp [residualize, eval, ResidualExpr.foldMul,
        ihLeft hfree.1, ihRight hfree.2]

/-- Specialization preserves the value of every formal partial derivative with
respect to a dynamic input.  Thus polynomial credit carried by the residual
program is exactly the credit of the unspecialized program. -/
theorem eval_formalDeriv_residualize [DecidableEq Dynamic] [Semiring R]
    (target : Dynamic) (staticEnv : Static → R) (dynamicEnv : Dynamic → R)
    (expr : Expr R Static Dynamic) :
    ResidualExpr.eval dynamicEnv
        (ResidualExpr.formalDeriv target (residualize staticEnv expr)) =
      eval staticEnv dynamicEnv (formalDeriv target expr) := by
  induction expr with
  | const => simp [residualize, ResidualExpr.formalDeriv, formalDeriv,
      ResidualExpr.eval, eval]
  | static => simp [residualize, ResidualExpr.formalDeriv, formalDeriv,
      ResidualExpr.eval, eval]
  | dynamic index =>
      simp [residualize, ResidualExpr.formalDeriv, formalDeriv,
        ResidualExpr.eval, eval]
  | add left right ihLeft ihRight =>
      simp [residualize, formalDeriv, eval, ihLeft, ihRight]
  | mul left right ihLeft ihRight =>
      simp [residualize, formalDeriv, eval, ihLeft, ihRight, eval_residualize]

end Expr

/-! ## Positive and negative executable boundaries -/

namespace Fixture

inductive StaticVar where
  | frozenWeight
  deriving DecidableEq, Repr

inductive DynamicVar where
  | errorState
  deriving DecidableEq, Repr

open StaticVar DynamicVar

def staticEnv : StaticVar → ℤ
  | .frozenWeight => 2

def dynamicEnv (value : ℤ) : DynamicVar → ℤ
  | .errorState => value

def mixedProgram : Expr ℤ StaticVar DynamicVar :=
  .add (.mul (.static .frozenWeight) (.dynamic .errorState)) (.const 1)

def specializedProgram : ResidualExpr ℤ DynamicVar :=
  mixedProgram.residualize staticEnv

theorem specialization_is_nontrivial :
    specializedProgram =
      .add (.mul (.const 2) (.dynamic .errorState)) (.const 1) := rfl

theorem specialization_preserves_observed_value :
    ResidualExpr.eval (dynamicEnv 3) specializedProgram = 7 := by
  decide

theorem specialization_preserves_dynamic_credit :
    ResidualExpr.eval (dynamicEnv 3)
        (ResidualExpr.formalDeriv .errorState specializedProgram) = 2 := by
  decide

/-- An invalid specializer freezes the dynamic state at one observed value. -/
def misclassifiedProgram : ResidualExpr ℤ DynamicVar := .const 7

theorem misclassification_can_match_one_observation :
    ResidualExpr.eval (dynamicEnv 3) misclassifiedProgram =
      ResidualExpr.eval (dynamicEnv 3) specializedProgram := by
  decide

theorem misclassification_breaks_value_and_credit :
    ResidualExpr.eval (dynamicEnv 4) misclassifiedProgram ≠
        ResidualExpr.eval (dynamicEnv 4) specializedProgram ∧
      ResidualExpr.eval (dynamicEnv 3)
          (ResidualExpr.formalDeriv .errorState misclassifiedProgram) ≠
        ResidualExpr.eval (dynamicEnv 3)
          (ResidualExpr.formalDeriv .errorState specializedProgram) := by
  decide

end Fixture

#print axioms Expr.eval_residualize
#print axioms Expr.residualize_eq_const_of_dynamicFree
#print axioms Expr.eval_formalDeriv_residualize
#print axioms Fixture.specialization_is_nontrivial
#print axioms Fixture.misclassification_breaks_value_and_credit

end FrozenConeSpecialization
end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
