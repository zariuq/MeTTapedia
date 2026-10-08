import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalSubstitutionEvaluation

/-!
# Context and binder readouts of authored substitutions

The model arrow of a composed or extended substitution is built from its
supplied component evaluations. Opening a binder is the actual comprehension
section. Context lookup interprets each authored variable type in the model
telescope, including its successive weakenings.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualTypeOperations

universe u c s t m

variable {S : Symbols.{u}} {C : CwfWithTerminal.{c, s, t, m}}

namespace ModelSubstitution

def compose {model : ModelData S C} (stable : StrictPiSubstitution model.products)
    {n k l : Nat} {Γ : Context C k} {Δ : Context C n} {Θ : Context C l}
    {first : Substitution S n k} {second : Substitution S k l}
    (earlier : ModelSubstitution model Γ Δ first)
    (later : ModelSubstitution model Θ Γ second) :
    ModelSubstitution model Θ Δ (composeSubstitution first second) where
  arrow := C.toCwf.compS earlier.arrow later.arrow
  readout index := by
    rw [composeSubstitution, Value.substitute_composition]
    exact model.evaluateTerm_substitute stable (first index) Θ Γ second later _
      (earlier.readout index)

def extend {model : ModelData S C} {n k : Nat} {Γ : Context C k} {Δ : Context C n}
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
        rw [Telescope.components_pair_zero]
        exact evaluated
    | succ index =>
        change model.evaluateTerm Γ (substitution index) = some
          ((Δ.2.snoc A).components (C.toCwf.pair modelMap.arrow A value) index.succ)
        rw [Telescope.components_pair_succ]
        exact modelMap.readout index

def openBinder {model : ModelData S C} {n : Nat} (Γ : Context C n)
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
        rw [instantiate_succ, ModelData.evaluateTerm, Telescope.variable_succ,
          ← Value.substitute_composition, wk_selfExtend, Value.substitute_identity]

end ModelSubstitution

namespace ModelData

variable (model : ModelData S C)

theorem evaluateContext_snoc {n : Nat} (context : ContextExpr S n) (type : TypeExpr S n)
    (Γ : Context C n) (A : C.toCwf.Ty Γ.1)
    (contextEvaluated : model.evaluateContext context = some Γ)
    (typeEvaluated : model.evaluateType Γ type = some A) :
    model.evaluateContext (.snoc context type) = some (Γ.snoc A) := by
  simp only [evaluateContext, contextEvaluated, typeEvaluated, bindResult_some]

theorem evaluateContext_snoc_eq_some_iff {n : Nat} (context : ContextExpr S n)
    (type : TypeExpr S n) (result : Context C (n + 1)) :
    model.evaluateContext (.snoc context type) = some result ↔
      ∃ Γ A, model.evaluateContext context = some Γ ∧
        model.evaluateType Γ type = some A ∧ Γ.snoc A = result := by
  simp only [evaluateContext, bindResult_eq_some_iff, Option.some.injEq]
  constructor
  · rintro ⟨Γ, contextRead, A, typeRead, same⟩
    exact ⟨Γ, A, contextRead, typeRead, same⟩
  · rintro ⟨Γ, A, contextRead, typeRead, same⟩
    exact ⟨Γ, contextRead, A, typeRead, same⟩

theorem evaluateContext_lookup (model : ModelData S C)
    (stable : StrictPiSubstitution model.products) :
    {n : Nat} → (context : ContextExpr S n) → (Γ : Context C n) →
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

theorem evaluateSubstitution_composition (stable : StrictPiSubstitution model.products)
    {n k l : Nat} (Γ : Context C k) (Δ : Context C n) (Θ : Context C l)
    (first : Substitution S n k) (second : Substitution S k l)
    (σ : C.toCwf.Sub Γ.1 Δ.1) (τ : C.toCwf.Sub Θ.1 Γ.1)
    (firstEvaluated : model.evaluateSubstitution Γ Δ first = some σ)
    (secondEvaluated : model.evaluateSubstitution Θ Γ second = some τ) :
    model.evaluateSubstitution Θ Δ (composeSubstitution first second) =
      some (C.toCwf.compS σ τ) :=
  ((ModelSubstitution.ofEvaluated model Γ Δ first σ firstEvaluated).compose stable
    (ModelSubstitution.ofEvaluated model Θ Γ second τ secondEvaluated)).evaluate

theorem evaluateType_instantiate (stable : StrictPiSubstitution model.products)
    {n : Nat} (Γ : Context C n) (A : C.toCwf.Ty Γ.1)
    (body : TypeExpr S (n + 1)) (B : C.toCwf.Ty (C.toCwf.ext Γ.1 A))
    (term : TermExpr S n) (value : C.toCwf.Tm Γ.1 A)
    (bodyEvaluated : model.evaluateType (Γ.snoc A) body = some B)
    (termEvaluated : model.evaluateTerm Γ term = some ⟨A, value⟩) :
    model.evaluateType Γ (body.substitute (instantiate term)) =
      some (C.toCwf.tySub B (selfExtend C.toCwf value)) :=
  model.evaluateType_substitute stable body Γ (Γ.snoc A) (instantiate term)
    (ModelSubstitution.openBinder Γ A term value termEvaluated) B bodyEvaluated

theorem evaluateTerm_instantiate (stable : StrictPiSubstitution model.products)
    {n : Nat} (Γ : Context C n) (A : C.toCwf.Ty Γ.1)
    (body : TermExpr S (n + 1)) (value : Value C.toCwf (C.toCwf.ext Γ.1 A))
    (term : TermExpr S n) (argument : C.toCwf.Tm Γ.1 A)
    (bodyEvaluated : model.evaluateTerm (Γ.snoc A) body = some value)
    (termEvaluated : model.evaluateTerm Γ term = some ⟨A, argument⟩) :
    model.evaluateTerm Γ (body.substitute (instantiate term)) =
      some (value.substitute (selfExtend C.toCwf argument)) :=
  model.evaluateTerm_substitute stable body Γ (Γ.snoc A) (instantiate term)
    (ModelSubstitution.openBinder Γ A term argument termEvaluated) value bodyEvaluated

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.External
