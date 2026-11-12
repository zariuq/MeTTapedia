import Mettapedia.TypeTheory.BubbleTypingInside
import Mettapedia.Logic.Relation.NormalFormDecision

/-!
# In the simple slice, conversion at types is identity

`SimpleSliceOfDependent` shows that the types of simple type theory are the expressions of the
dependent comparison core built from `prop`, base types and non-dependent function types
(`IsSimple`, `isSimple_iff_image`). This module records what that slice gives for conversion.

* **A simple type is a normal form** of every bubble none of whose rules has a simple type as its
  left-hand side (`simple_not_rewrite`): rules on terms do not step a simple type.
* **In a confluent bubble on terms, convertible simple types are identical**
  (`convertible_simple_eq`). The movement rule of `BubbleTypingInside.Typed` between two simple
  types is then the identity: no conversion evidence is ever needed at a simple type.
* For the arithmetic bubbles this holds outright (`Controls.arith_simple_types`).

## Controls (`Controls`)

`Vec (n + 0)` is not a simple type (`vec_not_simple`), and the recursion equations convert it with
the different type `Vec n` (`vec_converts`): conversion at types is a phenomenon of the dependent
part.

Scope: the comparison core. The hypothesis of confluence is named in `convertible_simple_eq`; the
arithmetic instance uses the bubbles' normal forms and no confluence hypothesis.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.SimpleSliceConversion

open _root_.Relation
open Mettapedia.Logic.Relation (IsNormal Confluent)
open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Expr

universe u v

section Core

variable {Base : Type u} {Const : Ty Base → Type v}

/-- **Rules on terms do not step a simple type.** -/
theorem simple_not_rewrite {rules : Expr Base Const → Expr Base Const → Prop}
    (onTerms : ∀ left right, rules left right → ¬ IsSimple left) {A A' : Expr Base Const}
    (step : Rewrite rules A A') : IsSimple A → False := by
  induction step with
  | root rule => exact onTerms _ _ rule
  | piDomain _ ih =>
      intro simple
      cases simple with
      | pi domain _ => exact ih domain
  | piBody _ ih =>
      intro simple
      cases simple with
      | pi _ body => exact ih body
  | lamDomain _ _ => intro simple; cases simple
  | lamBody _ _ => intro simple; cases simple
  | appFunction _ _ => intro simple; cases simple
  | appArgument _ _ => intro simple; cases simple
  | andLeft _ _ => intro simple; cases simple
  | andRight _ _ => intro simple; cases simple
  | orLeft _ _ => intro simple; cases simple
  | orRight _ _ => intro simple; cases simple
  | impLeft _ _ => intro simple; cases simple
  | impRight _ _ => intro simple; cases simple
  | notBody _ _ => intro simple; cases simple
  | eqLeft _ _ => intro simple; cases simple
  | eqRight _ _ => intro simple; cases simple
  | allDomain _ _ => intro simple; cases simple
  | allBody _ _ => intro simple; cases simple
  | exDomain _ _ => intro simple; cases simple
  | exBody _ _ => intro simple; cases simple

/-- **In a confluent bubble on terms, convertible simple types are identical.** -/
theorem convertible_simple_eq {rules : Expr Base Const → Expr Base Const → Prop}
    (confluent : Confluent (Rewrite rules))
    (onTerms : ∀ left right, rules left right → ¬ IsSimple left) {A B : Expr Base Const}
    (simpleA : IsSimple A) (simpleB : IsSimple B) (converted : Convertible rules A B) : A = B := by
  obtain ⟨common, fromA, fromB⟩ := confluent.eqvGen_iff_join.mp converted
  have atA : common = A :=
    IsNormal.reflTransGen_eq (fun _ step => simple_not_rewrite onTerms step simpleA) fromA
  have atB : common = B :=
    IsNormal.reflTransGen_eq (fun _ step => simple_not_rewrite onTerms step simpleB) fromB
  exact atA.symm.trans atB

end Core

/-! ## Controls -/

namespace Controls

open Mettapedia.TypeTheory.BubbleConversion.Arith

/-- The arithmetic normal forms leave simple types as they are. -/
theorem norm_simple (plus : Bool) {A : AExpr} (simple : IsSimple A) : Arith.norm plus A = A := by
  induction simple with
  | prop => rfl
  | base _ => rfl
  | pi _ _ ihDomain ihBody => simp only [Arith.norm, ihDomain, ihBody]

/-- **In the arithmetic bubbles, convertible simple types are identical.** -/
theorem arith_simple_types (plus : Bool) {A B : AExpr} (simpleA : IsSimple A) (simpleB : IsSimple B)
    (converted : Convertible (bubbleRules plus) A B) : A = B := by
  have same := (conv_iff_norm plus).mp converted
  rwa [norm_simple plus simpleA, norm_simple plus simpleB] at same

/-- A vector type is not a simple type. -/
theorem vec_not_simple (index : AExpr) : ¬ IsSimple (vec index) := by
  intro simple
  cases simple

/-- **A dependent type converts with a different type.** -/
theorem vec_converts :
    Convertible (bubbleRules false) (vec (addE (bvar 1) zeroE)) (vec (bvar 1)) ∧
      vec (addE (bvar 1) zeroE) ≠ vec (bvar 1) := by
  refine ⟨Relation.EqvGen.rel _ _ (Rewrite.appArgument (Rewrite.root (Rule.addZero (bvar 1)))), ?_⟩
  intro same
  simp [vec, addE] at same

end Controls

/-! ## Axiom audit -/

#print axioms simple_not_rewrite
#print axioms convertible_simple_eq
#print axioms Controls.arith_simple_types
#print axioms Controls.vec_not_simple
#print axioms Controls.vec_converts

end Mettapedia.TypeTheory.SimpleSliceConversion
