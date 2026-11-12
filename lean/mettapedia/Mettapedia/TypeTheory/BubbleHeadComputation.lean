import Mettapedia.TypeTheory.BubbleBetaTyping

/-!
# Computation at the head keeps types without being a conversion

A bubble's conversion is one rule set; the computation of programs may be another. This module
separates the positions where a computation step is harmless for typing from the positions where
it has to be a conversion of the bubble.

* `HeadStep comp` is a computation step at the root of a term or in the function of an
  application, repeatedly: the function is computed, the argument is passed as it is.
* `head_subject_reduction`: when every computation rule keeps the types its left side has in the
  bubble (`ComputationPreservesTypes`), a typed term keeps its type under a head step. No relation
  between the computation and the bubble's conversion is asked.
* A step inside an argument is the other case. There the type of the application mentions the
  argument, and the step has to be a conversion
  (`BubbleBetaTyping.Controls.computation_outside_conversion_breaks_types`).

So types may depend on arguments that are passed without being run. An argument that is still to
be run, in a position a type depends on, makes its computation part of the conversion.

## Controls

* `Controls.arith_head_beta`: in the arithmetic bubble, where β is not a conversion, a β step at
  the head keeps the type.
* `Controls.head_step_keeps_family_type`: with `h : Π (n : nat). Vec n`, the term
  `(λ (g : Π (n : nat). Vec n). g) h 0` is typed at `Vec 0`, and so is `h 0`, its reduct by a β step
  in the function of the application.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.BubbleHeadComputation

open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.BubbleTypingInside
open Mettapedia.TypeTheory.BubbleBetaTyping
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Expr

universe u v

section Core

variable {Base : Type u} {Const : Ty Base → Type v}

/-- A computation step at the head: at the root, or in the function of an application. -/
inductive HeadStep (comp : Expr Base Const → Expr Base Const → Prop) :
    Expr Base Const → Expr Base Const → Prop where
  | root {e e' : Expr Base Const} : comp e e' → HeadStep comp e e'
  | appFunction {f f' a : Expr Base Const} :
      HeadStep comp f f' → HeadStep comp (Expr.app f a) (Expr.app f' a)

/-- Every computation rule keeps the types that its left side has in the bubble. -/
def ComputationPreservesTypes (rules comp : Expr Base Const → Expr Base Const → Prop) : Prop :=
  ∀ (Γ : List (Expr Base Const)) (left right A : Expr Base Const), comp left right →
    HasTypeInside rules Γ left A → HasTypeInside rules Γ right A

/-- **Subject reduction at the head**, for a computation that need not be a conversion of the
bubble. -/
theorem head_subject_reduction {rules comp : Expr Base Const → Expr Base Const → Prop}
    (preserves : ComputationPreservesTypes rules comp) {Γ : List (Expr Base Const)}
    {e A : Expr Base Const} (typed : Typed (Convertible rules) Γ e A) :
    ∀ e' : Expr Base Const, HeadStep comp e e' → Typed (Convertible rules) Γ e' A := by
  induction typed with
  | var lookup =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule (.var lookup)
  | base b =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule (.base b)
  | prop =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule .prop
  | pi dA dB _ _ =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule (.pi dA dB)
  | lam dA db _ _ =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule (.lam dA db)
  | app df da ihf _ =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule (.app df da)
      | appFunction inner => exact .app (ihf _ inner) da
  | const τ c =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule (.const τ c)
  | tyFam b =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule (.tyFam b)
  | top =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule .top
  | bot =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule .bot
  | and dp dq _ _ =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule (.and dp dq)
  | or dp dq _ _ =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule (.or dp dq)
  | imp dp dq _ _ =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule (.imp dp dq)
  | not dp _ =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule (.not dp)
  | eq da db _ _ =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule (.eq da db)
  | all dA db _ _ =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule (.all dA db)
  | ex dA db _ _ =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule (.ex dA db)
  | move _ converted ih => exact fun e' step => .move (ih e' step) converted

/-- **Subject reduction along any number of head steps.** -/
theorem head_subject_reduction_star {rules comp : Expr Base Const → Expr Base Const → Prop}
    (preserves : ComputationPreservesTypes rules comp) {Γ : List (Expr Base Const)}
    {e e' A : Expr Base Const} (typed : HasTypeInside rules Γ e A)
    (reduced : Relation.ReflTransGen (HeadStep comp) e e') : HasTypeInside rules Γ e' A := by
  induction reduced with
  | refl => exact typed
  | tail _ step ih => exact head_subject_reduction preserves ih _ step

end Core

/-! ## Controls -/

namespace Controls

open Mettapedia.TypeTheory.BubbleConversion.Arith
open Mettapedia.TypeTheory.BubbleBetaTyping.Controls

/-- In the arithmetic bubble the β rule keeps types as a computation. -/
theorem arith_beta_computation : ComputationPreservesTypes Rule (Beta : AExpr → AExpr → Prop) := by
  intro Γ left right T rule typed
  cases rule with
  | contract A b a => exact arith_beta_keeps_type typed

/-- **In the arithmetic bubble, where β is not a conversion, β steps at the head keep the
type.** -/
theorem arith_head_beta {Γ : List AExpr} {e e' A : AExpr} (typed : HasTypeInside Rule Γ e A)
    (reduced : Relation.ReflTransGen (HeadStep Beta) e e') : HasTypeInside Rule Γ e' A :=
  head_subject_reduction_star arith_beta_computation typed reduced

/-- The type of the dependent function `h`. -/
def familyType : AExpr := Expr.pi natType (vec (bvar 0))

/-- `(λ (g : Π (n : nat). Vec n). g) h 0` is typed at `Vec 0` in the context
`h : Π (n : nat). Vec n`. -/
theorem wrapped_typed :
    HasTypeInside Rule familyContext
      (Expr.app (Expr.app (Expr.lam familyType (bvar 0)) (bvar 0)) zeroE) (vec zeroE) :=
  Typed.app (A := natType) (B := vec (bvar 0))
    (Typed.app (A := familyType) (B := familyType)
      (Typed.lam
        (Typed.pi (Typed.base ())
          (Typed.app (A := natType) (B := univ) (Typed.tyFam ())
            (Typed.var (Γ := natType :: familyContext) (i := 0) rfl)))
        (Typed.var (Γ := familyType :: familyContext) (i := 0) rfl))
      (Typed.var (Γ := familyContext) (i := 0) rfl))
    (Typed.const _ ArithConst.zero)

/-- **A β step in the function of an application keeps the dependent type**: `h 0` is typed at
`Vec 0` as the reduct of the wrapped term. -/
theorem head_step_keeps_family_type :
    HasTypeInside Rule familyContext (Expr.app (bvar 0) zeroE) (vec zeroE) :=
  arith_head_beta wrapped_typed
    (Relation.ReflTransGen.single
      (HeadStep.appFunction (HeadStep.root (Beta.contract familyType (bvar 0) (bvar 0)))))

end Controls

/-! ## Axiom audit -/

#print axioms head_subject_reduction
#print axioms head_subject_reduction_star
#print axioms Controls.arith_head_beta
#print axioms Controls.wrapped_typed
#print axioms Controls.head_step_keeps_family_type

end Mettapedia.TypeTheory.BubbleHeadComputation
