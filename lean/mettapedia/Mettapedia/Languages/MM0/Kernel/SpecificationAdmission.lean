import Mettapedia.Languages.MM0.Kernel.TheoryInvariant

/-!
# Aligning MM0 proof declarations with a fixed logical specification

These are resolved logical declarations, after source names and scopes have
been checked and assigned identifiers. Text parsing and name resolution are
separate obligations. I/O directives are not logical declarations.

Public proof declarations consume matching specification declarations in
order. Local definitions and proved theorems consume none. Local sorts,
primitive terms and axioms are forbidden. An omitted specification definition
body may be filled by any admitted body; a supplied body must match exactly
in this resolved representation. No byte-format acceptance theorem is claimed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel

instance termDeclDecidableEq : DecidableEq TermDecl := fun first second =>
  decidable_of_iff
    (first.arguments = second.arguments ∧ first.resultSort = second.resultSort ∧
      first.dependencies = second.dependencies)
    (by cases first; cases second; simp)

instance definitionBodyDecidableEq : DecidableEq Definition.Body := fun first second =>
  decidable_of_iff (first.dummies = second.dummies ∧ first.expression = second.expression)
    (by cases first; cases second; simp)

instance theoremDeclDecidableEq : DecidableEq TheoremDecl := fun first second =>
  decidable_of_iff
    (first.arguments = second.arguments ∧ first.hypotheses = second.hypotheses ∧
      first.conclusion = second.conclusion)
    (by cases first; cases second; simp)

inductive SpecificationEntry where
  | sort (index : Nat) (info : SortInfo)
  | term (index : Nat) (declaration : TermDecl)
  | definition (index : Nat) (declaration : TermDecl) (body : Option Definition.Body)
  | axiomDecl (index : Nat) (declaration : TheoremDecl)
  | theoremDecl (index : Nat) (declaration : TheoremDecl)

namespace SpecificationEntry

inductive Matches : SpecificationEntry → Admission → Prop where
  | sort (index : Nat) (info : SortInfo) : Matches (.sort index info) (.sort index info)
  | term (index : Nat) (declaration : TermDecl) :
      Matches (.term index declaration) (.term index declaration)
  | definition (index : Nat) (declaration : TermDecl)
      (expected : Option Definition.Body) (actual : Definition.Body) :
      (expected = none ∨ expected = some actual) →
      Matches (.definition index declaration expected) (.definition index declaration actual)
  | axiomDecl (index : Nat) (declaration : TheoremDecl) :
      Matches (.axiomDecl index declaration) (.axiomDecl index declaration)
  | theoremDecl (index : Nat) (declaration : TheoremDecl) (dummies : List Nat) (proof : ProofWitness) :
      Matches (.theoremDecl index declaration) (.theoremDecl index declaration dummies proof)

def checkMatch : SpecificationEntry → Admission → Bool
  | .sort index info, .sort actual stored => decide (index = actual ∧ info = stored)
  | .term index declaration, .term actual stored => decide (index = actual ∧ declaration = stored)
  | .definition index declaration expected, .definition actual stored body =>
      decide (index = actual ∧ declaration = stored ∧ (expected = none ∨ expected = some body))
  | .axiomDecl index declaration, .axiomDecl actual stored => decide (index = actual ∧ declaration = stored)
  | .theoremDecl index declaration, .theoremDecl actual stored _ _ =>
      decide (index = actual ∧ declaration = stored)
  | _, _ => false

theorem checkMatch_iff (entry : SpecificationEntry) (admission : Admission) :
    checkMatch entry admission = true ↔ Matches entry admission := by
  constructor
  · intro accepted
    cases entry <;> cases admission <;> simp only [checkMatch, decide_eq_true_eq] at accepted
    all_goals first
      | contradiction
      | (rcases accepted with ⟨rfl, rfl, rest⟩; exact .definition _ _ _ _ rest)
      | (rcases accepted with ⟨rfl, rfl⟩; constructor)
  · intro matched
    cases matched <;> simp_all [checkMatch]

end SpecificationEntry

structure ProofDeclaration where
  admission : Admission
  isLocal : Bool := false

namespace ProofDeclaration

inductive Auxiliary : Admission → Prop where
  | definition (index : Nat) (declaration : TermDecl) (body : Definition.Body) :
      Auxiliary (.definition index declaration body)
  | theoremDecl (index : Nat) (declaration : TheoremDecl) (dummies : List Nat) (proof : ProofWitness) :
      Auxiliary (.theoremDecl index declaration dummies proof)

def auxiliary : Admission → Bool
  | .definition .. | .theoremDecl .. => true
  | _ => false

theorem auxiliary_iff (admission : Admission) : auxiliary admission = true ↔ Auxiliary admission := by
  constructor
  · intro h
    cases admission <;> simp only [auxiliary] at h
    all_goals first | contradiction | exact .definition _ _ _ | exact .theoremDecl _ _ _ _
  · intro h
    cases h <;> rfl

end ProofDeclaration

namespace SpecificationAdmission

structure State where
  theory : Theory
  pending : List SpecificationEntry

inductive Step : State → ProofDeclaration → State → Prop where
  | auxiliary {before after : Theory} {pending : List SpecificationEntry} {admission : Admission} :
      ProofDeclaration.Auxiliary admission → Theory.Step before admission after →
      Step ⟨before, pending⟩ ⟨admission, true⟩ ⟨after, pending⟩
  | publicDecl {before after : Theory} {entry : SpecificationEntry}
      {pending : List SpecificationEntry} {admission : Admission} :
      SpecificationEntry.Matches entry admission → Theory.Step before admission after →
      Step ⟨before, entry :: pending⟩ ⟨admission, false⟩ ⟨after, pending⟩

/-- Specification consumption is checked before theory admission. -/
def pending? (pending : List SpecificationEntry) (declaration : ProofDeclaration) :
    Option (List SpecificationEntry) :=
  if declaration.isLocal then
      if ProofDeclaration.auxiliary declaration.admission then some pending else none
    else match pending with
      | [] => none
      | expected :: remaining =>
          if expected.checkMatch declaration.admission then some remaining else none

def step? (state : State) (declaration : ProofDeclaration) : Option State := do
  let pending ← pending? state.pending declaration
  let theory ← Theory.step? state.theory declaration.admission
  pure ⟨theory, pending⟩

theorem step_eq_some_iff (before after : State) (declaration : ProofDeclaration) :
    step? before declaration = some after ↔ Step before declaration after := by
  rcases before with ⟨theory, pending⟩
  rcases declaration with ⟨admission, localFlag⟩
  constructor
  · intro accepted
    cases localFlag with
    | true =>
        by_cases auxiliary : ProofDeclaration.auxiliary admission = true
        · cases next : Theory.step? theory admission with
          | none => simp [step?, pending?, auxiliary, next] at accepted
          | some newTheory =>
              have same : (⟨newTheory, pending⟩ : State) = after := by
                simpa [step?, pending?, auxiliary, next] using accepted
              subst after
              exact .auxiliary ((ProofDeclaration.auxiliary_iff _).mp auxiliary)
                ((Theory.step_eq_some_iff _ _ _).mp next)
        · simp [step?, pending?, auxiliary] at accepted
    | false =>
        cases pending with
        | nil => simp [step?, pending?] at accepted
        | cons expected remaining =>
            by_cases matched : expected.checkMatch admission = true
            · cases next : Theory.step? theory admission with
              | none => simp [step?, pending?, matched, next] at accepted
              | some newTheory =>
                  have same : (⟨newTheory, remaining⟩ : State) = after := by
                    simpa [step?, pending?, matched, next] using accepted
                  subst after
                  exact .publicDecl ((SpecificationEntry.checkMatch_iff _ _).mp matched)
                    ((Theory.step_eq_some_iff _ _ _).mp next)
            · simp [step?, pending?, matched] at accepted
  · intro checked
    cases checked with
    | auxiliary allowed admitted =>
        simp [step?, pending?, (ProofDeclaration.auxiliary_iff _).mpr allowed,
          (Theory.step_eq_some_iff _ _ _).mpr admitted]
    | publicDecl matched admitted =>
        simp [step?, pending?, (SpecificationEntry.checkMatch_iff _ _).mpr matched,
          (Theory.step_eq_some_iff _ _ _).mpr admitted]

theorem Step.theory_step {before after : State} {declaration : ProofDeclaration}
    (step : Step before declaration after) :
    Theory.Step before.theory declaration.admission after.theory := by
  cases step <;> assumption

theorem Step.wellFormed {before after : State} {declaration : ProofDeclaration}
    (step : Step before declaration after) (valid : Theory.WellFormed before.theory) :
    Theory.WellFormed after.theory := step.theory_step.wellFormed valid

/-- Every admitted axiom is exactly the next declared specification axiom. -/
theorem Step.axiom_from_specification {before after : State} {index : Nat}
    {declaration : TheoremDecl} {localFlag : Bool}
    (step : Step before ⟨.axiomDecl index declaration, localFlag⟩ after) :
    localFlag = false ∧ before.pending = .axiomDecl index declaration :: after.pending := by
  cases step with
  | auxiliary allowed _ => cases allowed
  | publicDecl matched _ => cases matched; exact ⟨rfl, rfl⟩

end SpecificationAdmission

end Mettapedia.Languages.MM0.Kernel
