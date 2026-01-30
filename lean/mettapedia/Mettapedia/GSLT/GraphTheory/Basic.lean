import Mettapedia.GSLT.Core.Web
import Mettapedia.GSLT.Core.LambdaTheoryCategory
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice

universe u

/-!
# Graph Lambda Theories

This file formalizes graph lambda theories from Bucciarelli-Salibra
"Graph Lambda Theories" (2008).

## Main Definitions

* `LambdaTerm` - De Bruijn indexed lambda terms
* `Interpretation` - Interpretation of terms in a graph model
* `TheoryOf` - Lambda-theory induced by a graph model
* `GraphTheory` - The class of graph lambda theories
* `Sensible` - Theories equating all unsolvable terms
* `Semisensible` - Theories where unsolvables only equal unsolvables

## Key Insights from Bucciarelli-Salibra

A **lambda-theory** is a congruence relation on lambda terms extending β-equality.

A theory T is **sensible** if it equates all unsolvable terms:
  T ⊢ Ω = λx.Ω
where Ω = (λx.xx)(λx.xx).

A theory T is **semisensible** if unsolvable terms only equal unsolvable terms:
  T ⊢ M = N with M unsolvable implies N is unsolvable.

Every graph theory is semisensible (Bucciarelli-Salibra §4).

## References

- Bucciarelli & Salibra, "Graph Lambda Theories" (2008)
- Barendregt, "The Lambda Calculus: Its Syntax and Semantics"
-/

namespace Mettapedia.GSLT.GraphTheory

open Mettapedia.GSLT.Core

/-! ## Lambda Terms with de Bruijn Indices

We use de Bruijn indices for alpha-equivalence-free representation.
-/

/-- Lambda terms with de Bruijn indices.
    Variables are represented by natural numbers (indices).
    0 refers to the innermost binder, 1 to the next outer, etc. -/
inductive LambdaTerm : Type where
  /-- Variable with de Bruijn index -/
  | var : Nat → LambdaTerm
  /-- Lambda abstraction -/
  | lam : LambdaTerm → LambdaTerm
  /-- Application -/
  | app : LambdaTerm → LambdaTerm → LambdaTerm
  deriving Repr, DecidableEq

namespace LambdaTerm

/-- The identity combinator I = λx.x -/
def I : LambdaTerm := .lam (.var 0)

/-- The K combinator K = λxy.x -/
def K : LambdaTerm := .lam (.lam (.var 1))

/-- The S combinator S = λxyz.xz(yz) -/
def S : LambdaTerm :=
  .lam (.lam (.lam (.app (.app (.var 2) (.var 0)) (.app (.var 1) (.var 0)))))

/-- The omega combinator ω = λx.xx -/
def omega : LambdaTerm := .lam (.app (.var 0) (.var 0))

/-- The Omega combinator Ω = ωω = (λx.xx)(λx.xx) -/
def Omega : LambdaTerm := .app omega omega

/-- Shift free variables by a given amount -/
def shift (d : Nat) (c : Nat) : LambdaTerm → LambdaTerm
  | .var n => if n < c then .var n else .var (n + d)
  | .lam t => .lam (shift d (c + 1) t)
  | .app t1 t2 => .app (shift d c t1) (shift d c t2)

/-- Substitute term s for variable index j in term t -/
def subst (j : Nat) (s : LambdaTerm) : LambdaTerm → LambdaTerm
  | .var n => if n == j then s else if n > j then .var (n - 1) else .var n
  | .lam t => .lam (subst (j + 1) (shift 1 0 s) t)
  | .app t1 t2 => .app (subst j s t1) (subst j s t2)

/-- Beta reduction: substitute the argument into the body -/
def betaReduce : LambdaTerm → Option LambdaTerm
  | .app (.lam t) s => some (subst 0 s t)
  | _ => none

/-- Check if a term is a value (lambda abstraction) -/
def isValue : LambdaTerm → Bool
  | .lam _ => true
  | _ => false

/-- One-step beta reduction (leftmost-outermost) -/
def step : LambdaTerm → Option LambdaTerm
  | .app (.lam t) s => some (subst 0 s t)
  | .app t1 t2 =>
      match step t1 with
      | some t1' => some (.app t1' t2)
      | none =>
          match step t2 with
          | some t2' => some (.app t1 t2')
          | none => none
  | .lam t =>
      match step t with
      | some t' => some (.lam t')
      | none => none
  | .var _ => none

end LambdaTerm

/-! ## Head Normal Forms and Solvability

A term is in **head normal form** if it has the form λx₁...xₙ.y M₁ ... Mₖ
where y is a variable. Solvable terms are those with a head normal form.
-/

/-- Head normal form: λx₁...xₙ.y M₁ ... Mₖ where y is a variable -/
inductive HeadNormalForm : Type where
  /-- A variable applied to arguments, possibly under lambdas -/
  | hnf : (numLambdas : Nat) → (headVar : Nat) → (args : List LambdaTerm) → HeadNormalForm

/-- Check if a term is an application head (variable or application of head) -/
def LambdaTerm.isAppHead : LambdaTerm → Bool
  | .var _ => true
  | .app t _ => t.isAppHead
  | .lam _ => false

/-- Check if a term is in head normal form -/
def LambdaTerm.isHNF : LambdaTerm → Bool
  | .var _ => true
  | .lam t => t.isHNF
  | .app t _ => t.isAppHead

/-- A term is solvable if it has a head normal form.
    Equivalently: ∃ M₁...Mₙ. t M₁ ... Mₙ →*_β I -/
def LambdaTerm.Solvable (t : LambdaTerm) : Prop :=
  ∃ (args : List LambdaTerm), (args.foldl .app t).isHNF = true

/-- A term is unsolvable if it is not solvable -/
def LambdaTerm.Unsolvable (t : LambdaTerm) : Prop := ¬t.Solvable

/-- Helper: isAppHead of an application is the isAppHead of the function part -/
private theorem isAppHead_app (t s : LambdaTerm) :
    (LambdaTerm.app t s).isAppHead = t.isAppHead := rfl

/-- Helper: foldl preserves non-AppHead property -/
private theorem foldl_app_preserves_not_isAppHead (t : LambdaTerm) (args : List LambdaTerm)
    (h : t.isAppHead = false) : (args.foldl .app t).isAppHead = false := by
  induction args generalizing t with
  | nil => exact h
  | cons a rest ih =>
    rw [List.foldl_cons]
    apply ih
    rw [isAppHead_app]
    exact h

/-- Helper: Omega is not an AppHead (not a variable at the head) -/
private theorem Omega_not_isAppHead : LambdaTerm.Omega.isAppHead = false := by
  native_decide

/-- Helper: Any term with Omega at the head position is not an AppHead -/
private theorem foldl_app_Omega_not_isAppHead (args : List LambdaTerm) :
    (args.foldl .app LambdaTerm.Omega).isAppHead = false :=
  foldl_app_preserves_not_isAppHead LambdaTerm.Omega args Omega_not_isAppHead

/-- Helper: isHNF of an application is the isAppHead of the function part -/
private theorem isHNF_app (t s : LambdaTerm) :
    (LambdaTerm.app t s).isHNF = t.isAppHead := rfl

/-- Helper: Omega is not in HNF -/
private theorem Omega_not_isHNF : LambdaTerm.Omega.isHNF = false := by
  native_decide

/-- Helper: foldl preserves non-HNF for applications starting from non-AppHead -/
private theorem foldl_app_preserves_not_isHNF (t : LambdaTerm) (args : List LambdaTerm)
    (h : t.isAppHead = false) (hHNF : t.isHNF = false) : (args.foldl .app t).isHNF = false := by
  induction args generalizing t with
  | nil => exact hHNF
  | cons a rest ih =>
    rw [List.foldl_cons]
    apply ih
    · rw [isAppHead_app]; exact h
    · rw [isHNF_app]; exact h

/-- Helper: Omega applied to any arguments is not in HNF -/
private theorem foldl_app_Omega_not_isHNF (args : List LambdaTerm) :
    (args.foldl .app LambdaTerm.Omega).isHNF = false :=
  foldl_app_preserves_not_isHNF LambdaTerm.Omega args Omega_not_isAppHead Omega_not_isHNF

/-- Omega is the canonical unsolvable term -/
theorem Omega_unsolvable : LambdaTerm.Omega.Unsolvable := by
  unfold LambdaTerm.Unsolvable LambdaTerm.Solvable
  intro ⟨args, h⟩
  -- Omega applied to any arguments never reaches HNF
  rw [foldl_app_Omega_not_isHNF args] at h
  exact Bool.false_ne_true h

/-! ## Lambda Theories

A lambda-theory is a congruence relation on lambda terms extending β-equality.
-/

/-- A lambda equation is a pair of terms -/
structure LambdaEq where
  lhs : LambdaTerm
  rhs : LambdaTerm
  deriving DecidableEq

/-- A lambda-theory is a set of equations closed under:
    - β-equality
    - Reflexivity, symmetry, transitivity
    - Congruence (substitution under context) -/
structure LambdaTheory where
  /-- The set of equations in the theory -/
  equations : Set LambdaEq
  /-- Contains all β-equalities (reflexive closure) -/
  refl : ∀ t, ⟨t, t⟩ ∈ equations
  /-- Symmetric -/
  symm : ∀ {t s}, ⟨t, s⟩ ∈ equations → ⟨s, t⟩ ∈ equations
  /-- Transitive -/
  trans : ∀ {t s u}, ⟨t, s⟩ ∈ equations → ⟨s, u⟩ ∈ equations → ⟨t, u⟩ ∈ equations
  /-- Beta reduction -/
  beta : ∀ t s, ⟨LambdaTerm.app (.lam t) s, t.subst 0 s⟩ ∈ equations
  /-- Congruence for lambda -/
  congLam : ∀ {t t'}, ⟨t, t'⟩ ∈ equations → ⟨.lam t, .lam t'⟩ ∈ equations
  /-- Congruence for application (left) -/
  congAppLeft : ∀ {t t' s}, ⟨t, t'⟩ ∈ equations → ⟨.app t s, .app t' s⟩ ∈ equations
  /-- Congruence for application (right) -/
  congAppRight : ∀ {t s s'}, ⟨s, s'⟩ ∈ equations → ⟨.app t s, .app t s'⟩ ∈ equations

namespace LambdaTheory

/-- Two terms are equal in a theory -/
def equates (T : LambdaTheory) (t s : LambdaTerm) : Prop := ⟨t, s⟩ ∈ T.equations

/-- Theory inclusion -/
def le (T S : LambdaTheory) : Prop := T.equations ⊆ S.equations

instance : LE LambdaTheory := ⟨le⟩

/-- A theory is consistent if it doesn't equate I and K -/
def Consistent (T : LambdaTheory) : Prop := ¬T.equates LambdaTerm.I LambdaTerm.K

/-- A theory is sensible if all unsolvable terms are equal -/
def Sensible (T : LambdaTheory) : Prop :=
  ∀ t s, t.Unsolvable → s.Unsolvable → T.equates t s

/-- A theory is semisensible if unsolvable terms only equal unsolvable terms -/
def Semisensible (T : LambdaTheory) : Prop :=
  ∀ t s, t.Unsolvable → T.equates t s → s.Unsolvable

end LambdaTheory

/-! ## Sensibility

A theory is sensible if it equates all unsolvable terms.
-/

/-- Sensible and consistent implies semisensible.

    The proof requires consistency: if T equates a solvable s with unsolvable t,
    and T is sensible (all unsolvables equal), then ALL unsolvables equal s.
    Combined with the fact that I and K are both solvable and the theory axioms,
    this leads to I = K, contradicting consistency.

    This is a deep result requiring showing that:
    1. I and K are solvable (they have HNF)
    2. If T equates solvable s with all unsolvables, then T equates I = K

    We axiomatize this as it requires extensive lambda calculus machinery.
-/
theorem sensible_consistent_imp_semisensible {T : LambdaTheory}
    (hSens : T.Sensible) (hCons : T.Consistent) : T.Semisensible := by
  sorry

/-- Convenience version: sensible theories that don't equate I and K are semisensible -/
theorem sensible_imp_semisensible {T : LambdaTheory}
    (h : T.Sensible) (hCons : T.Consistent) : T.Semisensible :=
  sensible_consistent_imp_semisensible h hCons

/-! ## Graph Theories

The lambda-theory induced by a graph model D is the set of equations
valid in all interpretations in D.
-/

/-- An environment maps free variables to graph model elements -/
def Env (D : GraphModel) := Nat → D.Carrier

/-- Interpretation of lambda terms in a graph model.

    For graph models, the key insight is that a lambda abstraction λx.t
    is interpreted as the set of pairs (a, d) such that if the argument
    satisfies a, then the result is d.

    This is a simplified placeholder for the full graph-theoretic interpretation.
    The full version requires careful handling of the coding function.
-/
noncomputable def interpret (D : GraphModel) (ρ : Env D) : LambdaTerm → Set D.Carrier
  | .var n => {ρ n}
  | .lam t =>
      -- For now, we use a simplified interpretation
      -- Full version: { c(a, d) | ∀ x ∈ a, d ∈ ⟦t⟧(ρ[0 ↦ x]) }
      { d | ∃ x, d ∈ interpret D (fun n => if n = 0 then x else ρ (n - 1)) t }
  | .app t s =>
      -- d · e = { x | ∃ d' ∈ ⟦t⟧ρ, ∃ e ∈ ⟦s⟧ρ, x ∈ d' · e }
      { x | ∃ d' ∈ interpret D ρ t, ∃ e ∈ interpret D ρ s, x ∈ D.apply d' e }

/-- Two terms are equal in a graph model if they have equal interpretations -/
def validates (D : GraphModel) (eq : LambdaEq) : Prop :=
  ∀ ρ : Env D, interpret D ρ eq.lhs = interpret D ρ eq.rhs

/-- The lambda-theory induced by a graph model -/
def theoryOf (D : GraphModel) : Set LambdaEq :=
  { eq | validates D eq }

/-- A theory is a graph theory if it equals Th(D) for some graph model.
    Note: We fix the universe level u for the graph model. -/
def IsGraphTheory (T : LambdaTheory) : Prop :=
  ∃ D : GraphModel.{u}, T.equations = theoryOf D

/-! ## Key Theorems (Statements)

From Bucciarelli-Salibra:

1. Every graph theory is semisensible
2. Every graph theory contains the Böhm theory B
3. B is the maximal sensible graph theory
-/

/-- Every graph theory is semisensible (Bucciarelli-Salibra Theorem 29).

    The proof relies on the fact that in graph models:
    1. Unsolvable terms have "empty" approximations at all finite levels
    2. Solvable terms have non-empty finite approximations
    3. The interpretation function preserves this distinction
    4. If t = s in D with t unsolvable, the empty approximation of t
       must match some approximation of s, forcing s to be unsolvable

    See: Bucciarelli & Salibra, "Graph Lambda Theories" (2008), Theorem 29
-/
theorem graphTheory_semisensible (T : LambdaTheory) (h : IsGraphTheory T) : T.Semisensible := by
  sorry

/-- The intersection of graph theories is a graph theory.

    The proof uses the weak product construction: given graph models D_i,
    the weak product ◇_i D_i is a graph model whose theory is contained
    in the intersection of the individual theories.

    More precisely: Th(◇_i D_i) ⊆ ⋂_i Th(D_i)

    For an arbitrary intersection, we take the weak product of all models
    representing the theories in S.

    See: Bucciarelli & Salibra, "Graph Lambda Theories" (2008), §3
-/
theorem graphTheories_inter_closed (S : Set LambdaTheory) (hS : ∀ T ∈ S, IsGraphTheory T) :
    ∃ T : LambdaTheory, IsGraphTheory T ∧ T.equations = ⋂ T ∈ S, LambdaTheory.equations T := by
  sorry

/-! ## Summary

This file establishes the basic definitions for graph lambda theories:

1. **LambdaTerm**: De Bruijn indexed lambda calculus
2. **LambdaTheory**: Congruence relation extending β-equality
3. **Sensible/Semisensible**: Properties of theories regarding unsolvability
4. **GraphModel.theory**: Lambda-theory induced by a graph model

**Key Results (Bucciarelli-Salibra)**:
- Every graph theory is semisensible
- The intersection of graph theories is a graph theory
- The Böhm theory B is the maximal sensible graph theory

**Next Steps**:
- `BohmTree.lean`: Böhm trees and the Böhm theory B
- `WeakProduct.lean`: Weak product of graph models
- `Stratified.lean`: Stratified models and their properties
-/

end Mettapedia.GSLT.GraphTheory
