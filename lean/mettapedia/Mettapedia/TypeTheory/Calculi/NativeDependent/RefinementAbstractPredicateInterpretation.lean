import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractInterpretation

/-!
# Authored predicate readouts in local models

All predicates are evaluated using the actual local Heyting operations,
display quantifiers and ordinary proposition readouts. Image formation uses
existential truth, with no selection of a data inhabitant. Ordered primitive
arguments are checked against their complete mixed scope.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateModel ContextualPredicateModelScopes ContextualModelTelescopes
open External (bindResult)

universe a c s t m p
variable {S : Symbols.{a}} {C : CwfWithTerminal.{c, s, t, m}}
variable {localModel : LocalModel.{c, s, t, m, p} C}

namespace ModelData

variable (model : ModelData S C localModel) {n : Nat} (Γ : ModelScope C localModel n)

theorem evaluate_predicateAtom (symbol : S.PredicateSymbol)
    (arguments : Fin (S.predicateArity symbol) → TermExpr S n)
    (σ : C.toCwf.Sub Γ.1 (model.predicateParameters symbol).1)
    (evaluated : ∀ index, model.evaluateTerm Γ (arguments index) =
      some ((model.predicateParameters symbol).2.components σ index)) :
    model.evaluatePredicate Γ (.atom symbol arguments) = some (model.predicateAt symbol σ) := by
  have assembled := (ScopeData.assemble?_eq_some_iff _ _ σ).mpr evaluated
  change bindResult ((model.predicateParameters symbol).2.assemble?
    (fun index => model.evaluateTerm Γ (arguments index))) _ = _
  rw [assembled]
  rfl

@[simp] theorem evaluate_truth : model.evaluatePredicate Γ .truth = some ⊤ := rfl
@[simp] theorem evaluate_falsehood : model.evaluatePredicate Γ .falsehood = some ⊥ := rfl
@[simp] theorem evaluate_propositions : model.evaluateType Γ .propositions =
    some (localModel.propositions.omega Γ.1) := rfl

theorem evaluate_and (first second : PropExpr S n) (φ ψ : localModel.doctrine.Predicate Γ.1)
    (firstRead : model.evaluatePredicate Γ first = some φ)
    (secondRead : model.evaluatePredicate Γ second = some ψ) :
    model.evaluatePredicate Γ (.and first second) = some (φ ⊓ ψ) := by
  change bindResult (model.evaluatePredicate Γ first) (fun first =>
    bindResult (model.evaluatePredicate Γ second) (fun second => some (first ⊓ second))) = _
  rw [firstRead, secondRead]
  rfl

theorem evaluate_or (first second : PropExpr S n) (φ ψ : localModel.doctrine.Predicate Γ.1)
    (firstRead : model.evaluatePredicate Γ first = some φ)
    (secondRead : model.evaluatePredicate Γ second = some ψ) :
    model.evaluatePredicate Γ (.or first second) = some (φ ⊔ ψ) := by
  change bindResult (model.evaluatePredicate Γ first) (fun first =>
    bindResult (model.evaluatePredicate Γ second) (fun second => some (first ⊔ second))) = _
  rw [firstRead, secondRead]
  rfl

theorem evaluate_implies (first second : PropExpr S n) (φ ψ : localModel.doctrine.Predicate Γ.1)
    (firstRead : model.evaluatePredicate Γ first = some φ)
    (secondRead : model.evaluatePredicate Γ second = some ψ) :
    model.evaluatePredicate Γ (.implies first second) = some (φ ⇨ ψ) := by
  change bindResult (model.evaluatePredicate Γ first) (fun first =>
    bindResult (model.evaluatePredicate Γ second) (fun second => some (first ⇨ second))) = _
  rw [firstRead, secondRead]
  rfl

theorem evaluate_all (domain : TypeExpr S n) (predicate : PropExpr S (n + 1))
    (A : C.toCwf.Ty Γ.1) (φ : localModel.doctrine.Predicate (C.toCwf.ext Γ.1 A))
    (domainRead : model.evaluateType Γ domain = some A)
    (predicateRead : model.evaluatePredicate (Γ.snoc A) predicate = some φ) :
    model.evaluatePredicate Γ (.all domain predicate) =
      some (localModel.doctrine.all A φ) := by
  change bindResult (model.evaluateType Γ domain) (fun A =>
    bindResult (model.evaluatePredicate (Γ.snoc A) predicate)
      (fun φ => some (localModel.doctrine.all A φ))) = _
  rw [domainRead]
  change bindResult (model.evaluatePredicate (Γ.snoc A) predicate) _ = _
  rw [predicateRead]
  rfl

theorem evaluate_exists (domain : TypeExpr S n) (predicate : PropExpr S (n + 1))
    (A : C.toCwf.Ty Γ.1) (φ : localModel.doctrine.Predicate (C.toCwf.ext Γ.1 A))
    (domainRead : model.evaluateType Γ domain = some A)
    (predicateRead : model.evaluatePredicate (Γ.snoc A) predicate = some φ) :
    model.evaluatePredicate Γ (.exists domain predicate) =
      some (localModel.doctrine.some A φ) := by
  change bindResult (model.evaluateType Γ domain) (fun A =>
    bindResult (model.evaluatePredicate (Γ.snoc A) predicate)
      (fun φ => some (localModel.doctrine.some A φ))) = _
  rw [domainRead]
  change bindResult (model.evaluatePredicate (Γ.snoc A) predicate) _ = _
  rw [predicateRead]
  rfl

theorem evaluate_quote (predicate : PropExpr S n) (φ : localModel.doctrine.Predicate Γ.1)
    (predicateRead : model.evaluatePredicate Γ predicate = some φ) :
    model.evaluateTerm Γ (.quote predicate) = some ⟨localModel.propositions.omega Γ.1, localModel.propositions.quote φ⟩ := by
  change bindResult (model.evaluatePredicate Γ predicate)
    (fun φ => some (⟨localModel.propositions.omega Γ.1, localModel.propositions.quote φ⟩ : Value C.toCwf Γ.1)) = _
  rw [predicateRead]
  rfl

theorem evaluate_holds (term : TermExpr S n) (value : C.toCwf.Tm Γ.1 (localModel.propositions.omega Γ.1))
    (termRead : model.evaluateTerm Γ term = some ⟨localModel.propositions.omega Γ.1, value⟩) :
    model.evaluatePredicate Γ (.holds term) = some (localModel.propositions.holds value) := by
  change bindResult (check? (model.evaluateTerm Γ term) (localModel.propositions.omega Γ.1)) _ = _
  rw [termRead, check?_supplied]
  rfl

theorem evaluate_image (type : TypeExpr S n) (A : C.toCwf.Ty Γ.1)
    (typeRead : model.evaluateType Γ type = some A) :
    model.evaluatePredicate Γ (.image type) = some (localModel.doctrine.some A ⊤) := by
  change bindResult (model.evaluateType Γ type) _ = _
  rw [typeRead]
  rfl

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract
