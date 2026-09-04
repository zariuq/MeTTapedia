import Mettapedia.GSLT.LanguageDef.AtomlessBooleanTermProfileBridge

/-!
# First-order decision for atomless Boolean algebras

This module supplies the ordinary first-order source language that the finite
profile kernel was designed to decide.  Atomic formulas are equations between
Boolean-algebra terms; negation, conjunction, and existential quantification
form a functionally complete first-order language.  Its semantics quantifies
directly over an arbitrary Boolean-algebra carrier.

Compilation into cell-profile formulas is compositional.  The semantic
correspondence theorem is independent of atomlessness.  Atomlessness enters
only in the separate theorem that the executable finite-profile search agrees
with carrier quantification.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision

open Mettapedia.Foundations.Gunk
open Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityDecision
open Mettapedia.GSLT.LanguageDef.AtomlessBooleanProfileExtension
open Mettapedia.GSLT.LanguageDef.AtomlessBooleanTermProfileBridge

universe u

/-! ## Ordinary first-order syntax and cold semantics -/

/-- First-order formulas over the signature of Boolean algebras.  A binder
adds its variable at de Bruijn index zero. -/
inductive Formula : Nat -> Type where
  | equation {arity : Nat} (claim : Equation (Fin arity)) : Formula arity
  | falsum {arity : Nat} : Formula arity
  | conjunction {arity : Nat} (left right : Formula arity) : Formula arity
  | negation {arity : Nat} (body : Formula arity) : Formula arity
  | existsF {arity : Nat} (body : Formula (arity + 1)) : Formula arity
  deriving DecidableEq

/-- Independent carrier semantics for ordinary first-order formulas. -/
def Satisfies {B : Type u} [BooleanAlgebra B] :
    {arity : Nat} -> Formula arity -> (Fin arity -> B) -> Prop
  | _, .equation claim, valuation =>
      claim.left.eval valuation = claim.right.eval valuation
  | _, .falsum, _valuation => False
  | _, .conjunction left right, valuation =>
      Satisfies left valuation /\ Satisfies right valuation
  | _, .negation body, valuation => ¬ Satisfies body valuation
  | _, .existsF body, valuation =>
      exists value : B, Satisfies body (extendValuation value valuation)

/-! ## Compositional compilation to finite profile formulas -/

/-- Compile ordinary first-order syntax into the profile language. -/
def compile : {arity : Nat} -> Formula arity ->
    Mettapedia.GSLT.LanguageDef.AtomlessBooleanProfileDecision.Formula arity
  | _, .equation claim => equationFormula claim
  | _, .falsum => .falsum
  | _, .conjunction left right =>
      .conjunction (compile left) (compile right)
  | _, .negation body => .negation (compile body)
  | _, .existsF body => .existsF (compile body)

/-- Compilation preserves and reflects the independently defined carrier
semantics in every Boolean algebra. -/
theorem satisfies_compile_iff
    {B : Type u} [BooleanAlgebra B] :
    {arity : Nat} -> (formula : Formula arity) ->
      (valuation : Fin arity -> B) ->
      Mettapedia.GSLT.LanguageDef.AtomlessBooleanProfileDecision.Satisfies
          (compile formula) valuation <->
        Satisfies formula valuation
  | _, .equation claim, valuation =>
      satisfies_equationFormula_iff_eval_eq claim valuation
  | _, .falsum, _valuation => Iff.rfl
  | _, .conjunction left right, valuation => by
      exact and_congr (satisfies_compile_iff left valuation)
        (satisfies_compile_iff right valuation)
  | _, .negation body, valuation => by
      exact not_congr (satisfies_compile_iff body valuation)
  | _, .existsF body, valuation => by
      exact exists_congr fun value =>
        satisfies_compile_iff body (extendValuation value valuation)

/-! ## Executable open and closed decision -/

/-- Evaluate a source formula by compiling it and running finite profile
search. -/
def decideAt {arity : Nat} (formula : Formula arity)
    (profile : Profile arity) : Bool :=
  Mettapedia.GSLT.LanguageDef.AtomlessBooleanProfileDecision.decideAt
    (compile formula) profile

/-- Open decision is exact at every actual valuation in an atomless Boolean
algebra. -/
theorem decideAt_eq_true_iff_satisfies
    {B : Type u} [BooleanAlgebra B] (gunky : IsGunky B)
    {arity : Nat} (formula : Formula arity)
    (valuation : Fin arity -> B) :
    decideAt formula (profileOf valuation) = true <->
      Satisfies formula valuation :=
  (Mettapedia.GSLT.LanguageDef.AtomlessBooleanProfileDecision.decideAt_eq_true_iff_satisfies
    gunky (compile formula)
    valuation).trans (satisfies_compile_iff formula valuation)

/-- Canonical empty valuation for closed formulas. -/
def emptyValuation {B : Type u} : Fin 0 -> B := Fin.elim0

/-- Closed first-order decision. -/
def decideClosed (formula : Formula 0) : Bool :=
  decideAt formula (fun _cell => true)

/-- Closed decision is exact in every nontrivial atomless Boolean algebra. -/
theorem decideClosed_eq_true_iff_satisfies
    {B : Type u} [BooleanAlgebra B] [Nontrivial B]
    (gunky : IsGunky B) (formula : Formula 0) :
    decideClosed formula = true <->
      Satisfies formula (emptyValuation (B := B)) := by
  rw [decideClosed, decideAt,
    ← Mettapedia.GSLT.LanguageDef.AtomlessBooleanProfileDecision.empty_profile_eq_true
      (B := B)]
  exact decideAt_eq_true_iff_satisfies gunky formula emptyValuation

/-! ## Positive and negative first-order canaries -/

namespace Canary

def x : Term (Fin 1) := .atom 0

def equalsBottom : Equation (Fin 1) where
  left := x
  right := .bottom

def equalsTop : Equation (Fin 1) where
  left := x
  right := .top

/-- There is a proper nonzero Boolean-algebra element.  Unlike a bare
identity, this sentence detects the difference between atomless and two-point
semantic bases. -/
def properPartSentence : Formula 0 :=
  .existsF (.conjunction
    (.negation (.equation equalsBottom))
    (.negation (.equation equalsTop)))

theorem properPartSentence_decides_true :
    decideClosed properPartSentence = true := by
  decide

theorem properPartSentence_holds_in_atomless
    {B : Type u} [BooleanAlgebra B] [Nontrivial B]
    (gunky : IsGunky B) :
    Satisfies properPartSentence (emptyValuation (B := B)) :=
  (decideClosed_eq_true_iff_satisfies gunky properPartSentence).mp
    properPartSentence_decides_true

/-- The two-element Boolean algebra refutes the proper-part sentence. -/
theorem properPartSentence_fails_in_bool :
    ¬ Satisfies properPartSentence (emptyValuation (B := Bool)) := by
  rintro ⟨value, valueNotBottom, valueNotTop⟩
  cases value <;>
    simp [Satisfies, equalsBottom, equalsTop, x,
      Term.eval, extendValuation] at *

end Canary

#print axioms satisfies_compile_iff
#print axioms decideAt_eq_true_iff_satisfies
#print axioms decideClosed_eq_true_iff_satisfies
#print axioms Canary.properPartSentence_decides_true
#print axioms Canary.properPartSentence_holds_in_atomless
#print axioms Canary.properPartSentence_fails_in_bool

end Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision
