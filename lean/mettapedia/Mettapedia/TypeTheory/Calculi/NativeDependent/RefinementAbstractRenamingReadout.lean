import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractRenamingEvaluation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContexts

/-!
# Weakening and predicate restriction of actual evaluations

An assumption restricts every data value and predicate along its actual
guarded context inclusion. Weakening uses the actual comprehension projection.
Variable type lookup follows these maps through arbitrary mixed contexts.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract

open Mettapedia.TypeTheory.ContextualPredicateModel
open Mettapedia.TypeTheory.ContextualPredicateModelScopes
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualTypeOperations
open External (bindResult_eq_some_iff)

universe a c s t m p

variable {S : Symbols.{a}} {C : CwfWithTerminal.{c, s, t, m}}
  {localModel : LocalModel.{c, s, t, m, p} C}

namespace ModelData

variable (model : ModelData S C localModel) (stable : StrictPiSubstitution localModel.products)

include stable

theorem evaluateType_restrict {n : Nat} (Γ : ModelScope C localModel n) (guard : localModel.doctrine.Predicate Γ.1)
    (type : TypeExpr S n) (A : C.toCwf.Ty Γ.1)
    (evaluated : model.evaluateType Γ type = some A) :
    model.evaluateType (Γ.assume guard) type =
      some (C.toCwf.tySub A (localModel.assumptions.inclusion guard)) := by
  simpa only [TypeExpr.rename_identity, ModelRenaming.restrict] using
    model.evaluateType_rename stable type (Γ.assume guard) Γ id
      (ModelRenaming.restrict Γ guard) A evaluated

theorem evaluateTerm_restrict {n : Nat} (Γ : ModelScope C localModel n) (guard : localModel.doctrine.Predicate Γ.1)
    (term : TermExpr S n) (value : Value C.toCwf Γ.1)
    (evaluated : model.evaluateTerm Γ term = some value) :
    model.evaluateTerm (Γ.assume guard) term = some (value.substitute (localModel.assumptions.inclusion guard)) := by
  simpa only [TermExpr.rename_identity, ModelRenaming.restrict] using
    model.evaluateTerm_rename stable term (Γ.assume guard) Γ id
      (ModelRenaming.restrict Γ guard) value evaluated

theorem evaluatePredicate_restrict {n : Nat} (Γ : ModelScope C localModel n) (guard : localModel.doctrine.Predicate Γ.1)
    (predicate : PropExpr S n) (φ : localModel.doctrine.Predicate Γ.1)
    (evaluated : model.evaluatePredicate Γ predicate = some φ) :
    model.evaluatePredicate (Γ.assume guard) predicate = some (localModel.doctrine.reindex (localModel.assumptions.inclusion guard) φ) := by
  simpa only [PropExpr.rename_identity, ModelRenaming.restrict] using
    model.evaluatePredicate_rename stable predicate (Γ.assume guard) Γ id
      (ModelRenaming.restrict Γ guard) φ evaluated

theorem evaluatePredicate_weaken {n : Nat} (Γ : ModelScope C localModel n) (A : C.toCwf.Ty Γ.1)
    (predicate : PropExpr S n) (φ : localModel.doctrine.Predicate Γ.1)
    (evaluated : model.evaluatePredicate Γ predicate = some φ) :
    model.evaluatePredicate (Γ.snoc A) (predicate.rename Fin.succ) =
      some (localModel.doctrine.reindex (C.toCwf.wk A) φ) :=
  model.evaluatePredicate_rename stable predicate (Γ.snoc A) Γ Fin.succ
    (ModelRenaming.weaken Γ A) φ evaluated

omit stable

theorem evaluateContext_snoc_eq_some_iff {n : Nat} (context : ContextExpr S n)
    (type : TypeExpr S n) (result : ModelScope C localModel (n + 1)) :
    model.evaluateContext (.snoc context type) = some result ↔
      ∃ Γ A, model.evaluateContext context = some Γ ∧
        model.evaluateType Γ type = some A ∧ Γ.snoc A = result := by
  simp only [evaluateContext, bindResult_eq_some_iff, Option.some.injEq]
  constructor
  · rintro ⟨Γ, contextRead, A, typeRead, same⟩
    exact ⟨Γ, A, contextRead, typeRead, same⟩
  · rintro ⟨Γ, A, contextRead, typeRead, same⟩
    exact ⟨Γ, contextRead, A, typeRead, same⟩

theorem evaluateContext_assume_eq_some_iff {n : Nat} (context : ContextExpr S n)
    (predicate : PropExpr S n) (result : ModelScope C localModel n) :
    model.evaluateContext (.assume context predicate) = some result ↔
      ∃ Γ φ, model.evaluateContext context = some Γ ∧
        model.evaluatePredicate Γ predicate = some φ ∧ Γ.assume φ = result := by
  change External.bindResult (model.evaluateContext context)
    (fun Γ => External.bindResult (model.evaluatePredicate Γ predicate)
      (fun φ => some (Γ.assume φ))) = some result ↔ _
  simp only [bindResult_eq_some_iff, Option.some.injEq]
  constructor
  · rintro ⟨Γ, contextRead, φ, predicateRead, same⟩
    exact ⟨Γ, φ, contextRead, predicateRead, same⟩
  · rintro ⟨Γ, φ, contextRead, predicateRead, same⟩
    exact ⟨Γ, contextRead, φ, predicateRead, same⟩

set_option backward.isDefEq.respectTransparency false in
theorem evaluateContext_lookup (model : ModelData S C localModel)
    (stable : StrictPiSubstitution localModel.products) :
    {n : Nat} → (context : ContextExpr S n) → (Γ : ModelScope C localModel n) →
    model.evaluateContext context = some Γ → (index : Fin n) →
    model.evaluateType Γ (context.lookup index) = some (Γ.2.lookup index).1
  | _, .nil, Γ, _, index => Fin.elim0 index
  | _, .snoc context type, Γ, evaluated, index => by
      rcases (model.evaluateContext_snoc_eq_some_iff _ _ _).mp evaluated with
        ⟨previous, A, previousEvaluated, typeEvaluated, equality⟩
      cases equality
      cases index using Fin.cases with
      | zero =>
          exact model.evaluateType_rename stable type (previous.snoc A) previous Fin.succ
            (ModelRenaming.weaken previous A) A typeEvaluated
      | succ index =>
          exact model.evaluateType_rename stable (context.lookup index)
            (previous.snoc A) previous Fin.succ (ModelRenaming.weaken previous A)
            (previous.2.lookup index).1
            (model.evaluateContext_lookup stable context previous previousEvaluated index)
  | _, .assume context predicate, Γ, evaluated, index => by
      rcases (model.evaluateContext_assume_eq_some_iff _ _ _).mp evaluated with
        ⟨previous, φ, previousEvaluated, _, equality⟩
      cases equality
      exact model.evaluateType_restrict stable previous φ (context.lookup index)
        (previous.2.lookup index).1
        (model.evaluateContext_lookup stable context previous previousEvaluated index)

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract
