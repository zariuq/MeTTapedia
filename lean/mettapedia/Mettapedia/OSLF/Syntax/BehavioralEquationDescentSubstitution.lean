import Mettapedia.OSLF.Syntax.BehavioralEquationDescent

/-!
# Actual binding substitution for descended behavioral coalgebras

Constructor substitution is checked on complete local inputs, using each
argument's actual lifted substitution. A domain of environments is admitted
when it is closed under those lifts and its variable images satisfy the
independently computed variable behavior. Structural induction then proves
the operational substitution square on all raw terms and equation classes.
No arbitrary environment is declared a coalgebra map.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BehavioralEquationDescent

open FreeBindingTerms BindingEquationFamilyCongruence

universe u

variable {S : Signature} {Actions : S.Srt → Type u} (law : LocalLaw S Actions)

def substituteResult {Γ Δ : Ctx S} (environment : Sub S Γ Δ) {sort : S.Srt}
    (value : Result Actions Γ sort) : Result Actions Δ sort :=
  (bind environment value.1, fun action => (value.2 action).map (bind environment))

/-- Every head is transported under its own declared binder list. -/
def substituteArguments {Γ Δ : Ctx S} (environment : Sub S Γ Δ) :
    {arity : List (List S.Srt × S.Srt)} →
      FamilyArgs S (Result Actions) arity Γ → FamilyArgs S (Result Actions) arity Δ
  | _, .nil => .nil
  | _, .cons (bs := binders) head tail =>
    .cons (substituteResult (liftSub environment binders) head)
      (substituteArguments environment tail)

/-- This checks each local constructor clause independently of the whole
operational extension. Targets use the same actual positional substitution. -/
def ClauseSubstitutionCompatible : Prop :=
  ∀ {Γ Δ : Ctx S} (environment : Sub S Γ Δ) {sort : S.Srt}
    (operator : S.Op sort) (arguments : FamilyArgs S (Result Actions) (S.arity operator) Γ),
    law.operation operator (substituteArguments environment arguments) =
      fun action => (law.operation operator arguments action).map (bind environment)

abbrev EnvironmentDomain (S : Signature) := {Γ Δ : Ctx S} → Sub S Γ Δ → Prop

def LiftClosed (domain : EnvironmentDomain S) : Prop :=
  ∀ {Γ Δ : Ctx S} {environment : Sub S Γ Δ}, domain environment →
    ∀ binders, domain (liftSub environment binders)

/-- A variable image is tested against the actual independently formed
coalgebra; this obligation concerns inputs, not a global substitution law. -/
def VariableSubstitutionCompatible (domain : EnvironmentDomain S) : Prop :=
  ∀ {Γ Δ : Ctx S} {environment : Sub S Γ Δ}, domain environment →
    ∀ {sort : S.Srt} (position : Var Γ sort),
      coalgebra law (environment sort position) =
        fun action => (law.onVariable position action).map (bind environment)

variable {domain : EnvironmentDomain S}

mutual

/-- Actual operational substitution, derived from local clause and input
checks and lift closure. Every recursive binder preserves its context. -/
theorem coalgebra_bind (clauses : ClauseSubstitutionCompatible law)
    (closed : LiftClosed domain) (inputs : VariableSubstitutionCompatible law domain)
    {Γ Δ : Ctx S} (environment : Sub S Γ Δ) (admitted : domain environment) :
    ∀ {sort : S.Srt} (term : Term S Γ sort),
      coalgebra law (bind environment term) =
        fun action => (coalgebra law term action).map (bind environment)
  | _, .var position => inputs admitted position
  | _, .op operator arguments => by
    change law.operation operator (evaluateArgs law (bindArgs environment arguments)) =
      fun action => (law.operation operator (evaluateArgs law arguments) action).map (bind environment)
    rw [evaluateArgs_bind clauses closed inputs environment admitted]
    exact clauses environment operator (evaluateArgs law arguments)

theorem evaluateArgs_bind (clauses : ClauseSubstitutionCompatible law)
    (closed : LiftClosed domain) (inputs : VariableSubstitutionCompatible law domain)
    {Γ Δ : Ctx S} (environment : Sub S Γ Δ) (admitted : domain environment) :
    ∀ {arity : List (List S.Srt × S.Srt)} (arguments : Args S arity Γ),
      evaluateArgs law (bindArgs environment arguments) =
        substituteArguments environment (evaluateArgs law arguments)
  | _, .nil => rfl
  | _, .cons (bs := binders) head tail => by
    apply congrArg₂ FamilyArgs.cons
    · apply Prod.ext
      · change (evaluate law (bind (liftSub environment binders) head)).1 =
          bind (liftSub environment binders) (evaluate law head).1
        rw [evaluate_source, evaluate_source]
      · exact coalgebra_bind clauses closed inputs (liftSub environment binders)
          (closed admitted binders) head
    · exact evaluateArgs_bind clauses closed inputs environment admitted tail

end

variable {M : List (MetaArity S)} {family : EqAxiom S M → Prop}
  (constructors : ConstructorCompatible law family) (equations : EquationCompatible law family)

/-- The quotient's existing actual substitution is a coalgebra map exactly
on the independently admitted environments. -/
theorem quotientCoalgebra_bindQ (clauses : ClauseSubstitutionCompatible law)
    (closed : LiftClosed domain) (inputs : VariableSubstitutionCompatible law domain)
    {Γ Δ : Ctx S} (environment : Sub S Γ Δ) (admitted : domain environment)
    {sort : S.Srt} (value : Classes family Γ sort) (action : Actions sort) :
    quotientCoalgebra law constructors equations
        (BindingTermCongruenceQuotient.bindQ (BindingEquationFamilyModel.congruence family)
          environment value) action =
      (quotientCoalgebra law constructors equations value action).map
        (BindingTermCongruenceQuotient.bindQ (BindingEquationFamilyModel.congruence family)
          environment) := by
  induction value using Quotient.inductionOn with
  | _ term =>
    change (coalgebra law (bind environment term) action).map (project family) = _
    rw [coalgebra_bind law clauses closed inputs environment admitted]
    change ((coalgebra law term action).map (bind environment)).map (project family) =
      ((coalgebra law term action).map (project family)).map
        (BindingTermCongruenceQuotient.bindQ
          (BindingEquationFamilyModel.congruence family) environment)
    cases coalgebra law term action <;> rfl

/-- The complete quotient clone uses arbitrary quotient-valued environments.
Its operational compatibility is earned when the chosen representatives are
in the admitted input domain; no erased-existence witness is manufactured. -/
theorem quotientCoalgebra_substitute (clauses : ClauseSubstitutionCompatible law)
    (closed : LiftClosed domain) (inputs : VariableSubstitutionCompatible law domain)
    {Γ Δ : Ctx S}
    (environment : BindingSubstitutionAlgebra.Environment S (Classes family) Γ Δ)
    (admitted : domain
      (BindingTermCongruenceQuotient.representativeEnv
        (BindingEquationFamilyModel.congruence family) environment))
    {sort : S.Srt} (value : Classes family Γ sort) (action : Actions sort) :
    quotientCoalgebra law constructors equations
        ((BindingEquationFamilyModel.algebra family).substitution.substitute environment value) action =
      (quotientCoalgebra law constructors equations value action).map
        ((BindingEquationFamilyModel.algebra family).substitution.substitute environment) :=
  quotientCoalgebra_bindQ law constructors equations clauses closed inputs _ admitted value action

end Mettapedia.OSLF.Binding.BehavioralEquationDescent
