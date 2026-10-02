import Mathlib.ModelTheory.Semantics
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

/-!
# Unrestricted equational rewriting

Public source: Marton Hajdu, Laura Kovacs, and Michael Rawson, *Rewriting and
Inductive Reasoning*, 2024, Section 4, rule Rw and Definition 1,
https://arxiv.org/abs/2402.19199.

This reconstruction uses mathlib's first-order terms of arbitrary finite arity.
It formalizes substitution instances, rewriting at a single term occurrence,
semantic soundness of finite rewrite derivations, and equational derivability
for the Rw-only term fragment. Equations are required to hold in the model;
membership in a rule set alone is not a claim of validity. Reduction-order
restrictions, the full clausal ReC calculus, and its completeness are not modeled.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Saturation.Rewriting

open FirstOrder

universe u v w m

variable {L : Language.{u, v}} {Variables : Type w}

/-- A context has one distinguished term occurrence, at any finite depth. -/
inductive Context (L : Language.{u, v}) (Variables : Type w) : Type max u w where
  | hole : Context L Variables
  | app {n : Nat} (symbol : L.Functions n) (arguments : Fin n -> L.Term Variables)
      (position : Fin n) (inner : Context L Variables) : Context L Variables

def Context.fill : Context L Variables -> L.Term Variables -> L.Term Variables
  | .hole, term => term
  | .app symbol arguments position inner, term =>
    .func symbol (Function.update arguments position (inner.fill term))

theorem Context.realize_congr {Model : Type m} [L.Structure Model]
    (context : Context L Variables) (assignment : Variables -> Model)
    {left right : L.Term Variables}
    (equal : left.realize assignment = right.realize assignment) :
    (context.fill left).realize assignment = (context.fill right).realize assignment := by
  induction context with
  | hole => exact equal
  | app symbol arguments position inner ih =>
    simp only [Context.fill, Language.Term.realize_func]
    apply congrArg (Language.Structure.funMap symbol)
    funext i
    by_cases same : i = position
    · subst i
      simpa using ih
    · simp [Function.update_of_ne same]

structure Equation (L : Language.{u, v}) (Variables : Type w) where
  left : L.Term Variables
  right : L.Term Variables

def Equation.Valid (equation : Equation L Variables) (Model : Type m)
    [L.Structure Model] : Prop :=
  forall assignment : Variables -> Model,
    equation.left.realize assignment = equation.right.realize assignment

/-- An instance of Rw at a single term occurrence, with no ordering restriction. -/
inductive Rewrite (rules : Set (Equation L Variables)) :
    L.Term Variables -> L.Term Variables -> Prop where
  | rule (equation : Equation L Variables) (member : equation ∈ rules)
      (substitution : Variables -> L.Term Variables) (context : Context L Variables) :
      Rewrite rules (context.fill (equation.left.subst substitution))
        (context.fill (equation.right.subst substitution))

inductive Rewrites (rules : Set (Equation L Variables)) :
    L.Term Variables -> L.Term Variables -> Prop where
  | refl (term : L.Term Variables) : Rewrites rules term term
  | step {first middle last : L.Term Variables}
      (before : Rewrites rules first middle) (rewrite : Rewrite rules middle last) :
      Rewrites rules first last

theorem rewrite_sound {Model : Type m} [L.Structure Model]
    {rules : Set (Equation L Variables)}
    (valid : forall equation, equation ∈ rules -> equation.Valid Model)
    {left right : L.Term Variables} (rewrite : Rewrite rules left right)
    (assignment : Variables -> Model) :
    left.realize assignment = right.realize assignment := by
  cases rewrite with
  | rule equation member substitution context =>
    apply context.realize_congr assignment
    simpa only [Language.Term.realize_subst] using
      valid equation member (fun name => (substitution name).realize assignment)

theorem rewrites_sound {Model : Type m} [L.Structure Model]
    {rules : Set (Equation L Variables)}
    (valid : forall equation, equation ∈ rules -> equation.Valid Model)
    {left right : L.Term Variables} (derivation : Rewrites rules left right)
    (assignment : Variables -> Model) :
    left.realize assignment = right.realize assignment := by
  induction derivation with
  | refl => rfl
  | step _ rewrite ih => exact ih.trans (rewrite_sound valid rewrite assignment)

theorem rewrite_mono {rules more : Set (Equation L Variables)} (subset : rules ⊆ more)
    {left right : L.Term Variables} (rewrite : Rewrite rules left right) :
    Rewrite more left right := by
  cases rewrite with
  | rule equation member substitution context =>
    exact Rewrite.rule equation (subset member) substitution context

theorem rewrites_mono {rules more : Set (Equation L Variables)} (subset : rules ⊆ more)
    {left right : L.Term Variables} (derivation : Rewrites rules left right) :
    Rewrites more left right := by
  induction derivation with
  | refl => exact Rewrites.refl _
  | step _ rewrite ih => exact Rewrites.step ih (rewrite_mono subset rewrite)

/-- Equational derivability of the Rw-only term fragment: an additional equation
can be applied after an existing derivation. -/
theorem equational_derivability (rules : Set (Equation L Variables))
    (equation : Equation L Variables) (substitution : Variables -> L.Term Variables)
    (context : Context L Variables) (first : L.Term Variables)
    (derived : Rewrites rules first (context.fill (equation.left.subst substitution))) :
    Rewrites (insert equation rules) first (context.fill (equation.right.subst substitution)) := by
  exact Rewrites.step (rewrites_mono (Set.subset_insert equation rules) derived)
    (Rewrite.rule equation (by simp) substitution context)

namespace AdditionExample

def language : Language where
  Functions n := PLift (n = 2)
  Relations _ := Empty

instance naturalStructure : language.Structure Nat where
  funMap {n} symbol arguments := by
    have arity : n = 2 := symbol.down
    subst n
    exact arguments 0 + arguments 1
  RelMap symbol := nomatch symbol

def plus (left right : language.Term Nat) : language.Term Nat :=
  .func ⟨rfl⟩ ![left, right]

def associativity : Equation language Nat where
  left := plus (plus (.var 0) (.var 1)) (.var 2)
  right := plus (.var 0) (plus (.var 1) (.var 2))

theorem associativity_valid : associativity.Valid Nat := by
  intro assignment
  change (assignment 0 + assignment 1) + assignment 2 =
    assignment 0 + (assignment 1 + assignment 2)
  exact Nat.add_assoc _ _ _

theorem contextual_associativity (context : Context language Nat)
    (substitution : Nat -> language.Term Nat) (assignment : Nat -> Nat) :
    (context.fill (associativity.left.subst substitution)).realize assignment =
      (context.fill (associativity.right.subst substitution)).realize assignment := by
  apply rewrite_sound (rules := {associativity})
  · intro equation member
    have equal : equation = associativity := Set.mem_singleton_iff.mp member
    subst equation
    exact associativity_valid
  · exact Rewrite.rule associativity (by simp) substitution context

/-- Dropping a summand is not an equivalence-preserving rewrite. -/
theorem dropping_argument_invalid :
    ¬(Equation.mk (plus (.var 0) (.var 1)) (.var 0)).Valid Nat := by
  intro valid
  have impossible := valid (fun name => name)
  change 0 + 1 = 0 at impossible
  omega

end AdditionExample

end Mettapedia.Logic.Saturation.Rewriting
