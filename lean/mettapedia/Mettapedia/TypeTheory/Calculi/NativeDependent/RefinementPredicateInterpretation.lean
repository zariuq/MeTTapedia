import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementInterpretation

/-!
# Actual readouts for native predicates and refinements

Every readout follows from evaluation of the authored child syntax. The
refinement checks retain the supplied inhabitant and the actual predicate;
a failing predicate is rejected. No local generated-rule soundness is
assumed by these constructor calculations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

open _root_.CategoryTheory
open External (bindResult)
open NativeLocalTypeFormers PresheafNativePropositionReadout
open DisplayedPresheafComprehension
open Mettapedia.GSLT.Topos

universe u v
variable {S : Symbols.{v}} {C : Type u} [Category.{u} C]

namespace ModelData

variable (model : ModelData S C) {n : Nat} (Γ : Scope C n)

theorem evaluate_predicateAtom (symbol : S.PredicateSymbol)
    (arguments : Fin (S.predicateArity symbol) → TermExpr S n)
    (σ : Γ.1 ⟶ (model.predicateParameters symbol).1)
    (evaluated : ∀ index, model.evaluateTerm Γ (arguments index) =
      some ((model.predicateParameters symbol).2.components σ index)) :
    model.evaluatePredicate Γ (.atom symbol arguments) = some (model.predicateAt symbol σ) := by
  have assembled := (ScopeData.assemble?_eq_some_iff _ _ σ).mpr evaluated
  simp only [evaluatePredicate, evaluatePredicateLift, assembled, bindResult]

@[simp] theorem evaluate_truth : model.evaluatePredicate Γ .truth = some ⊤ := rfl
@[simp] theorem evaluate_falsehood : model.evaluatePredicate Γ .falsehood = some ⊥ := rfl
@[simp] theorem evaluate_propositions : model.evaluateType Γ .propositions =
    some (nativeOmega Γ.1) := rfl

theorem evaluate_and (first second : PropExpr S n) (φ ψ : Subfunctor Γ.1)
    (firstRead : model.evaluatePredicate Γ first = some φ)
    (secondRead : model.evaluatePredicate Γ second = some ψ) :
    model.evaluatePredicate Γ (.and first second) = some (φ ⊓ ψ) := by
  change bindResult (model.evaluatePredicate Γ first) (fun first =>
    bindResult (model.evaluatePredicate Γ second) (fun second => some (first ⊓ second))) = _
  rw [firstRead, secondRead]
  rfl

theorem evaluate_or (first second : PropExpr S n) (φ ψ : Subfunctor Γ.1)
    (firstRead : model.evaluatePredicate Γ first = some φ)
    (secondRead : model.evaluatePredicate Γ second = some ψ) :
    model.evaluatePredicate Γ (.or first second) = some (φ ⊔ ψ) := by
  change bindResult (model.evaluatePredicate Γ first) (fun first =>
    bindResult (model.evaluatePredicate Γ second) (fun second => some (first ⊔ second))) = _
  rw [firstRead, secondRead]
  rfl

theorem evaluate_implies (first second : PropExpr S n) (φ ψ : Subfunctor Γ.1)
    (firstRead : model.evaluatePredicate Γ first = some φ)
    (secondRead : model.evaluatePredicate Γ second = some ψ) :
    model.evaluatePredicate Γ (.implies first second) = some (himpPointwise φ ψ) := by
  change bindResult (model.evaluatePredicate Γ first) (fun first =>
    bindResult (model.evaluatePredicate Γ second) (fun second => some (himpPointwise first second))) = _
  rw [firstRead, secondRead]
  rfl

theorem evaluate_all (domain : TypeExpr S n) (predicate : PropExpr S (n + 1))
    (A : NativeType Γ.1) (φ : Subfunctor (totalSpace A.decoded))
    (domainRead : model.evaluateType Γ domain = some A)
    (predicateRead : model.evaluatePredicate (Γ.snoc A) predicate = some φ) :
    model.evaluatePredicate Γ (.all domain predicate) =
      some (forallAlong ((NativeModel C).toCwf.wk A) φ) := by
  change bindResult (model.evaluateType Γ domain) (fun A =>
    bindResult (model.evaluatePredicate (Γ.snoc A) predicate)
      (fun φ => some (forallAlong ((NativeModel C).toCwf.wk A) φ))) = _
  rw [domainRead]
  change bindResult (model.evaluatePredicate (Γ.snoc A) predicate) _ = _
  rw [predicateRead]
  rfl

theorem evaluate_exists (domain : TypeExpr S n) (predicate : PropExpr S (n + 1))
    (A : NativeType Γ.1) (φ : Subfunctor (totalSpace A.decoded))
    (domainRead : model.evaluateType Γ domain = some A)
    (predicateRead : model.evaluatePredicate (Γ.snoc A) predicate = some φ) :
    model.evaluatePredicate Γ (.exists domain predicate) =
      some (φ.image ((NativeModel C).toCwf.wk A)) := by
  change bindResult (model.evaluateType Γ domain) (fun A =>
    bindResult (model.evaluatePredicate (Γ.snoc A) predicate)
      (fun φ => some (φ.image ((NativeModel C).toCwf.wk A)))) = _
  rw [domainRead]
  change bindResult (model.evaluatePredicate (Γ.snoc A) predicate) _ = _
  rw [predicateRead]
  rfl

theorem evaluate_quote (predicate : PropExpr S n) (φ : Subfunctor Γ.1)
    (predicateRead : model.evaluatePredicate Γ predicate = some φ) :
    model.evaluateTerm Γ (.quote predicate) = some ⟨nativeOmega Γ.1, nativeQuote φ⟩ := by
  change bindResult (model.evaluatePredicate Γ predicate)
    (fun φ => some (⟨nativeOmega Γ.1, nativeQuote φ⟩ : NativeValue Γ.1)) = _
  rw [predicateRead]
  rfl

theorem evaluate_holds (term : TermExpr S n) (value : (nativeOmega Γ.1).decoded.sections)
    (termRead : model.evaluateTerm Γ term = some ⟨nativeOmega Γ.1, value⟩) :
    model.evaluatePredicate Γ (.holds term) = some (nativeHolds value) := by
  change bindResult (check? (model.evaluateTerm Γ term) (nativeOmega Γ.1)) _ = _
  rw [termRead, check?_supplied]
  rfl

theorem evaluate_image (type : TypeExpr S n) (A : NativeType Γ.1)
    (typeRead : model.evaluateType Γ type = some A) :
    model.evaluatePredicate Γ (.image type) = some (Subfunctor.range ((NativeModel C).toCwf.wk A)) := by
  change bindResult (model.evaluateType Γ type) _ = _
  rw [typeRead]
  rfl

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
