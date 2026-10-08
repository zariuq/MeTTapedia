import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractSubstitutionEvaluation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractRenamingReadout

/-!
# Context and binder readouts of authored substitutions

The model arrow of a composed or extended substitution is built from its
supplied component evaluations. Opening a binder is the actual comprehension
section. Context lookup interprets each authored variable type in the model
telescope, including its successive weakenings.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract

open Mettapedia.TypeTheory.ContextualPredicateModel
open Mettapedia.TypeTheory.ContextualPredicateModelScopes
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualTypeOperations

universe a c s t m p

variable {S : Symbols.{a}} {C : CwfWithTerminal.{c, s, t, m}}
  {localModel : LocalModel.{c, s, t, m, p} C}

namespace ModelSubstitution

attribute [local irreducible] TypeOver.extensionSubstitution

set_option backward.isDefEq.respectTransparency false in
def compose {model : ModelData S C localModel} (stable : StrictPiSubstitution localModel.products)
    {n k l : Nat} {Γ : ModelScope C localModel k} {Δ : ModelScope C localModel n} {Θ : ModelScope C localModel l}
    {first : Substitution S n k} {second : Substitution S k l}
    (earlier : ModelSubstitution model Γ Δ first)
    (later : ModelSubstitution model Θ Γ second) :
    ModelSubstitution model Θ Δ (composeSubstitution first second) where
  arrow := C.toCwf.compS earlier.arrow later.arrow
  readout index := by
    rw [composeSubstitution, Value.substitute_composition]
    exact model.evaluateTerm_substitute stable (first index) Θ Γ second later _
      (earlier.readout index)

set_option backward.isDefEq.respectTransparency false in
def extend {model : ModelData S C localModel} {n k : Nat} {Γ : ModelScope C localModel k} {Δ : ModelScope C localModel n}
    {substitution : Substitution S n k} (modelMap : ModelSubstitution model Γ Δ substitution)
    (A : C.toCwf.Ty Δ.1) (term : TermExpr S k)
    (value : C.toCwf.Tm Γ.1 (C.toCwf.tySub A modelMap.arrow))
    (evaluated : model.evaluateTerm Γ term = some ⟨_, value⟩) :
    ModelSubstitution model Γ (Δ.snoc A) (extendSubstitution substitution term) where
  arrow := C.toCwf.pair modelMap.arrow A value
  readout index := by
    cases index using Fin.cases with
    | zero =>
        change model.evaluateTerm Γ term = some
          ((Δ.2.snoc A).components (C.toCwf.pair modelMap.arrow A value) 0)
        rw [ContextualPredicateModelScopes.ScopeData.components_pair_zero]
        exact evaluated
    | succ index =>
        change model.evaluateTerm Γ (substitution index) = some
          ((Δ.2.snoc A).components (C.toCwf.pair modelMap.arrow A value) index.succ)
        rw [ContextualPredicateModelScopes.ScopeData.components_pair_succ]
        exact modelMap.readout index

set_option backward.isDefEq.respectTransparency false in
def openBinder {model : ModelData S C localModel} {n : Nat} (Γ : ModelScope C localModel n)
    (A : C.toCwf.Ty Γ.1) (term : TermExpr S n) (value : C.toCwf.Tm Γ.1 A)
    (evaluated : model.evaluateTerm Γ term = some ⟨A, value⟩) :
    ModelSubstitution model Γ (Γ.snoc A) (instantiate term) where
  arrow := selfExtend C.toCwf value
  readout index := by
    cases index using Fin.cases with
    | zero =>
        rw [instantiate_zero, evaluated]
        apply congrArg some
        apply Sigma.ext
        · change A = C.toCwf.tySub (C.toCwf.tySub A (C.toCwf.wk A))
            (selfExtend C.toCwf value)
          rw [← C.toCwf.tySub_comp, wk_selfExtend, C.toCwf.tySub_id]
        · exact (vz_selfExtend value).symm
    | succ index =>
        rw [instantiate_succ, ModelData.evaluateTerm, ModelData.evaluateTermLift, ContextualPredicateModelScopes.ScopeData.lookup_succ,
          ← Value.substitute_composition, wk_selfExtend, Value.substitute_identity]

end ModelSubstitution

namespace ModelData

variable (model : ModelData S C localModel)

theorem evaluateSubstitution_composition (stable : StrictPiSubstitution localModel.products)
    {n k l : Nat} (Γ : ModelScope C localModel k) (Δ : ModelScope C localModel n) (Θ : ModelScope C localModel l)
    (first : Substitution S n k) (second : Substitution S k l)
    (σ : C.toCwf.Sub Γ.1 Δ.1) (τ : C.toCwf.Sub Θ.1 Γ.1)
    (firstEvaluated : model.evaluateSubstitution Γ Δ first = some σ)
    (secondEvaluated : model.evaluateSubstitution Θ Γ second = some τ) :
    model.evaluateSubstitution Θ Δ (composeSubstitution first second) =
      some (C.toCwf.compS σ τ) :=
  ((ModelSubstitution.ofEvaluated model Γ Δ first σ firstEvaluated).compose stable
    (ModelSubstitution.ofEvaluated model Θ Γ second τ secondEvaluated)).evaluate

theorem evaluateType_instantiate (stable : StrictPiSubstitution localModel.products)
    {n : Nat} (Γ : ModelScope C localModel n) (A : C.toCwf.Ty Γ.1)
    (body : TypeExpr S (n + 1)) (B : C.toCwf.Ty (C.toCwf.ext Γ.1 A))
    (term : TermExpr S n) (value : C.toCwf.Tm Γ.1 A)
    (bodyEvaluated : model.evaluateType (Γ.snoc A) body = some B)
    (termEvaluated : model.evaluateTerm Γ term = some ⟨A, value⟩) :
    model.evaluateType Γ (body.substitute (instantiate term)) =
      some (C.toCwf.tySub B (selfExtend C.toCwf value)) :=
  model.evaluateType_substitute stable body Γ (Γ.snoc A) (instantiate term)
    (ModelSubstitution.openBinder Γ A term value termEvaluated) B bodyEvaluated

theorem evaluateTerm_instantiate (stable : StrictPiSubstitution localModel.products)
    {n : Nat} (Γ : ModelScope C localModel n) (A : C.toCwf.Ty Γ.1)
    (body : TermExpr S (n + 1)) (value : Value C.toCwf (C.toCwf.ext Γ.1 A))
    (term : TermExpr S n) (argument : C.toCwf.Tm Γ.1 A)
    (bodyEvaluated : model.evaluateTerm (Γ.snoc A) body = some value)
    (termEvaluated : model.evaluateTerm Γ term = some ⟨A, argument⟩) :
    model.evaluateTerm Γ (body.substitute (instantiate term)) =
      some (value.substitute (selfExtend C.toCwf argument)) :=
  model.evaluateTerm_substitute stable body Γ (Γ.snoc A) (instantiate term)
    (ModelSubstitution.openBinder Γ A term argument termEvaluated) value bodyEvaluated

theorem evaluatePredicate_instantiate (stable : StrictPiSubstitution localModel.products)
    {n : Nat} (Γ : ModelScope C localModel n) (A : C.toCwf.Ty Γ.1)
    (predicate : PropExpr S (n + 1)) (φ : localModel.doctrine.Predicate (Γ.snoc A).1)
    (term : TermExpr S n) (value : C.toCwf.Tm Γ.1 A)
    (predicateEvaluated : model.evaluatePredicate (Γ.snoc A) predicate = some φ)
    (termEvaluated : model.evaluateTerm Γ term = some ⟨A, value⟩) :
    model.evaluatePredicate Γ (predicate.substitute (instantiate term)) =
      some (localModel.doctrine.reindex (selfExtend C.toCwf value) φ) :=
  model.evaluatePredicate_substitute stable predicate Γ (Γ.snoc A) (instantiate term)
    (ModelSubstitution.openBinder Γ A term value termEvaluated) φ predicateEvaluated

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract
