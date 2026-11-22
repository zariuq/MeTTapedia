import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverPatterns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidNormalForm

/-!
# Availability of the actual contextual solver recognizers

The lemmas expose the implemented alternatives of the selector and connect
them to the same variable-spine recognizer and partial inverse used by its
runtime binding, imitation and flexible-pair cases.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverCaseAvailability

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualPatternFragment
open ContextualSolverSelect

variable {S : Signature} {V : Type} [DecidableEq V] [DecidableEq S.Srt]
  [∀ sort, DecidableEq (S.Op sort)] {source : V → MetaArity S}

private theorem orElse_none {α : Type} (first : Option α) (fallback : Unit → Option α) :
    first.orElse fallback = none ↔ first = none ∧ fallback () = none := by
  cases first <;> simp only [Option.orElse, reduceCtorEq, false_and, true_and]

theorem declined_parts {Γ : Ctx S} {sort : S.Srt} (left right : Term (signature S source) Γ sort)
    (declined : tryTerms left right = none) :
    tryReflexiveTerms left right = none ∧ ContextualBindingCase.tryTerms left right = none ∧
      tryFlexEquation (observe left, observe right) = none ∧ trySameTerms left right = none ∧
      tryRigidTerms left right = none ∧ tryRigidTerms right left = none := by
  simpa only [tryTerms, tryFreshTerms, orElse_none, Option.map_eq_none_iff] using declined

omit [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)] in
theorem rigid_available (identity : V) {Γ : Ctx S}
    (arguments : Args (signature S source) ((source identity).1.map fun sort => ([], sort)) Γ)
    (rho : Ren S (source identity).1 Γ)
    (recognized : VariableSpines.recognize (S := signature S source) (source identity).1 arguments = some rho)
    (operator : S.Op (source identity).2) (fields : Args (signature S source) (S.arity operator) Γ) :
    tryRigidTerms (Term.op (.inr (.mk identity)) arguments) (Term.op (.inl operator) fields) ≠ none := by
  intro declined
  simp only [tryRigidTerms] at declined
  split at declined
  · rename_i computed
    cases recognized.symm.trans computed
  · cases declined

omit [DecidableEq S.Srt] in
theorem same_hole_available (identity : V) {Γ : Ctx S}
    (arguments remaining : Args (signature S source) ((source identity).1.map fun sort => ([], sort)) Γ)
    (left right : Ren S (source identity).1 Γ)
    (firstSpine : VariableSpines.recognize (S := signature S source) (source identity).1 arguments = some left)
    (secondSpine : VariableSpines.recognize (S := signature S source) (source identity).1 remaining = some right) :
    trySameTerms (Term.op (.inr (.mk identity)) arguments) (Term.op (.inr (.mk identity)) remaining) ≠ none := by
  intro declined
  by_cases identical : arguments = remaining
  · subst remaining
    simp only [trySameTerms, Operator.key, dif_pos rfl] at declined
    cases declined
  · simp only [trySameTerms, Operator.key, dif_pos rfl, dif_neg identical] at declined
    split at declined
    · rename_i computed
      cases firstSpine.symm.trans computed
    · split at declined
      · rename_i computed
        cases secondSpine.symm.trans computed
      · cases declined

omit [∀ sort, DecidableEq (S.Op sort)] in
theorem different_hole_available (first second : V) (different : first ≠ second)
    (sorts : (source first).2 = (source second).2) {Γ : Ctx S}
    (arguments : Args (signature S source) ((source first).1.map fun sort => ([], sort)) Γ)
    (remaining : Args (signature S source) ((source second).1.map fun sort => ([], sort)) Γ)
    (left : Ren S (source first).1 Γ) (right : Ren S (source second).1 Γ)
    (firstSpine : VariableSpines.recognize (S := signature S source) (source first).1 arguments = some left)
    (secondSpine : VariableSpines.recognize (S := signature S source) (source second).1 remaining = some right) :
    tryFlexEquation (observe (Term.op (.inr (.mk first)) arguments),
      observe (Term.op (.inr (.mk second)) remaining)) ≠ none := by
  intro declined
  simp only [tryFlexEquation, observe, dif_pos different, dif_pos sorts, dite_true] at declined
  split at declined
  · rename_i computed
    cases firstSpine.symm.trans computed
  · split at declined
    · rename_i computed
      cases secondSpine.symm.trans computed
    · cases declined

omit [∀ sort, DecidableEq (S.Op sort)] in
theorem variable_binding_available (identity : V) {Γ : Ctx S}
    (arguments : Args (signature S source) ((source identity).1.map fun sort => ([], sort)) Γ)
    (rho : Ren S (source identity).1 Γ)
    (recognized : VariableSpines.recognize (S := signature S source) (source identity).1 arguments = some rho)
    (injective : ∀ sort, Function.Injective (rho sort))
    (formal : Var (source identity).1 (source identity).2) :
    ContextualBindingCase.tryLeft (Term.op (.inr (.mk identity)) arguments)
      (Term.var (S := signature S source) (rho _ formal)) ≠ none := by
  have distinct : RenamingSlots.check (S := signature S source) rho = true :=
    (RenamingSlots.check_iff (S := signature S source) rho).mpr injective
  have recovered : strengthenT (RenamingInverse.strengthener (S := signature S source) rho injective)
      (Term.var (S := signature S source) (rho _ formal)) = some (Term.var (S := signature S source) formal) := by
    exact strengthenT_rename (S := signature S source) _ (Term.var (S := signature S source) formal)
  have absent : identity ∉ support (Term.var (S := signature S source) formal) := by
    intro member
    cases member
  intro declined
  simp only [ContextualBindingCase.tryLeft] at declined
  split at declined
  · rename_i computed
    cases recognized.symm.trans computed
  · rename_i chosen computed
    have same : chosen = rho := Option.some.inj (computed.symm.trans recognized)
    subst chosen
    split at declined
    · split at declined
      · rename_i computed
        cases recovered.symm.trans computed
      · rename_i body computed
        have same : body = Term.var (S := signature S source) formal := Option.some.inj (computed.symm.trans recovered)
        subst body
        split at declined
        · cases declined
        · rename_i impossible
          exact impossible absent
    · rename_i impossible
      exact impossible distinct

theorem declined_equation {Γ : Ctx S} {sort : S.Srt}
    (left right : Term (signature S source) Γ sort) (declined : tryEquation (observe left, observe right) = none) :
    tryTerms left right = none := by
  simpa [tryEquation, observe] using declined

omit [∀ sort, DecidableEq (S.Op sort)] in
theorem declined_bindings {Γ : Ctx S} {sort : S.Srt} (left right : Term (signature S source) Γ sort)
    (declined : ContextualBindingCase.tryTerms left right = none) :
    ContextualBindingCase.tryLeft left right = none ∧ ContextualBindingCase.tryLeft right left = none := by
  simpa only [ContextualBindingCase.tryTerms, orElse_none, Option.map_eq_none_iff] using declined

theorem equation_available_of_flex {Γ Δ : Ctx S} {sort result : S.Srt}
    (left : Term (signature S source) Γ sort) (right : Term (signature S source) Δ result)
    (contexts : Γ = Δ) (sorts : sort = result)
    (available : tryFlexEquation (observe left, observe right) ≠ none) :
    tryEquation (observe left, observe right) ≠ none := by
  cases contexts
  cases sorts
  intro declined
  have termsDeclined := declined_equation left right declined
  exact available (declined_parts left right termsDeclined).2.2.1

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverCaseAvailability
