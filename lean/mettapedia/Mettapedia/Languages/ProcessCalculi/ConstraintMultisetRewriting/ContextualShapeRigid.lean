import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeErasure
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidSolver

/-!
# Successful rigid normalization preserves and reflects first-order shapes

The actual normalizer may reject scope or metadata inconsistencies that a
shape model deliberately ignores. On a successful normalization, its
retained equations nevertheless have exactly the same shape models as the
source queue, including every constructor's ordered binding fields.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeRigid

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualShapeErasure
open ContextualRigidSolver

variable {S : Signature} {V Next : Type} {source : V → MetaArity S}

theorem models_append (images : ShapeAssignment S V Next) (first second : Problem source) :
    ShapeModels images (first ++ second) ↔ ShapeModels images first ∧ ShapeModels images second := by
  simp only [ShapeModels, List.forall_mem_append]

theorem models_cons (images : ShapeAssignment S V Next) (pair : Equation (Observation S source)) (rest : Problem source) :
    ShapeModels images (pair :: rest) ↔
      evaluateObservation images pair.1 = evaluateObservation images pair.2 ∧ ShapeModels images rest := by
  simp only [ShapeModels, List.forall_mem_cons, evaluateObservation]

private theorem merge_some {first second : Option (Problem source)} {result : Problem source}
    (computed : merge first second = some result) :
    ∃ left right, first = some left ∧ second = some right ∧ result = left ++ right := by
  cases first with
  | none => cases computed
  | some left =>
      cases second with
      | none => cases computed
      | some right => exact ⟨left, right, rfl, rfl, (Option.some.inj computed).symm⟩

private theorem fin_cases_eq_iff {α : Type} {count : Nat} (first second : α) (left right : Fin count → α) :
    (Fin.cases first left : Fin (count + 1) → α) = (Fin.cases second right : Fin (count + 1) → α) ↔
      first = second ∧ left = right := by
  constructor
  · intro same
    exact ⟨congrFun same 0, funext fun index => congrFun same index.succ⟩
  · rintro ⟨rfl, rfl⟩
    rfl

variable [∀ sort, DecidableEq (S.Op sort)]

mutual
theorem terms_models (images : ShapeAssignment S V Next) :
    ∀ {Γ : Ctx S} {sort : S.Srt} (left right : Term (signature S source) Γ sort)
      {result : Problem source}, terms left right = some result →
        (ShapeModels images result ↔ evaluate images left = evaluate images right)
  | _, _, .op (.inr identity) args, right, result, computed => by
      have same : [(observe (Term.op (.inr identity) args), observe right)] = result := by
        simpa only [terms, Option.some.injEq] using computed
      subst result
      simp only [ShapeModels, List.forall_mem_singleton, observe]
  | _, _, .var position, .op (.inr identity) args, result, computed => by
      have same : [(observe (Term.var position), observe (Term.op (.inr identity) args))] = result := by
        simpa only [terms, Option.some.injEq] using computed
      subst result
      simp only [ShapeModels, List.forall_mem_singleton, observe]
  | _, _, .op (.inl operator) args, .op (.inr identity) remaining, result, computed => by
      have same : [(observe (Term.op (.inl operator) args), observe (Term.op (.inr identity) remaining))] = result := by
        simpa only [terms, Option.some.injEq] using computed
      subst result
      simp only [ShapeModels, List.forall_mem_singleton, observe]
  | _, _, .var first, .var second, result, computed => by
      by_cases same : first = second
      · have empty : [] = result := by simpa only [terms, if_pos same, Option.some.injEq] using computed
        subst result
        constructor
        · intro _
          rfl
        · intro _ pair member
          cases member
      · simp only [terms, if_neg same, reduceCtorEq] at computed
  | _, _, .var _, .op (.inl _) _, _, computed => by simp only [terms, reduceCtorEq] at computed
  | _, _, .op (.inl _) _, .var _, _, computed => by simp only [terms, reduceCtorEq] at computed
  | _, sort, .op (.inl first) left, .op (.inl second) right, result, computed => by
      by_cases same : first = second
      · subst second
        simp only [terms] at computed
        have fields := arguments_models images left right computed
        constructor
        · intro models
          exact congrArg (Mettapedia.Logic.LP.Term.app (σ := shapeSignature S Next) ⟨sort, first⟩) (fields.mp models)
        · intro equality
          exact fields.mpr (eq_of_heq (Mettapedia.Logic.LP.Term.app.inj equality).2)
      · simp only [terms, dif_neg same, reduceCtorEq] at computed
termination_by Γ sort left _right => 2 * termSize left
decreasing_by all_goals simp_all only [termSize]; omega

theorem arguments_models (images : ShapeAssignment S V Next) :
    ∀ {arities : List (MetaArity S)} {Γ : Ctx S} (left right : Args (signature S source) arities Γ)
      {result : Problem source}, arguments left right = some result →
        (ShapeModels images result ↔ evaluateArgs images left = evaluateArgs images right)
  | _, _, .nil, .nil, result, computed => by
      have empty : [] = result := by simpa only [arguments, Option.some.injEq] using computed
      subst result
      constructor
      · intro _
        rfl
      · intro _ pair member
        cases member
  | _, _, .cons first rest, .cons second remaining, result, computed => by
      simp only [arguments] at computed
      obtain ⟨head, tail, headComputed, tailComputed, rfl⟩ := merge_some computed
      rw [models_append, terms_models images first second headComputed,
        arguments_models images rest remaining tailComputed]
      exact (fin_cases_eq_iff (evaluate images first) (evaluate images second)
        (evaluateArgs images rest) (evaluateArgs images remaining)).symm
termination_by arities Γ left _right => 2 * argsSize left + 1
decreasing_by
  all_goals simp_all only [argsSize]
  · omega
  · have positive := termSize_pos first
    omega
end

variable [DecidableEq S.Srt]

theorem equation_models (images : ShapeAssignment S V Next) (pair : Equation (Observation S source))
    {result : Problem source} (computed : equation pair = some result) :
    ShapeModels images result ↔ evaluateObservation images pair.1 = evaluateObservation images pair.2 := by
  rcases pair with ⟨⟨Γ, sort, left⟩, ⟨Δ, output, right⟩⟩
  by_cases contexts : Γ = Δ
  · subst Δ
    by_cases sorts : sort = output
    · subst output
      exact terms_models images left right (by simpa only [equation, dite_true] using computed)
    · simp only [equation, dif_neg sorts, dite_true, reduceCtorEq] at computed
  · simp only [equation, dif_neg contexts, reduceCtorEq] at computed

theorem normalization_models (images : ShapeAssignment S V Next) :
    ∀ (problem : Problem source) {result : Problem source}, ContextualRigidSolver.normalize problem = some result →
      (ShapeModels images result ↔ ShapeModels images problem)
  | [], result, computed => by
      have empty : [] = result := by simpa only [ContextualRigidSolver.normalize, Option.some.injEq] using computed
      subst result
      rfl
  | pair :: rest, result, computed => by
      obtain ⟨head, tail, headComputed, tailComputed, rfl⟩ := merge_some computed
      rw [models_append, equation_models images pair headComputed, normalization_models images rest tailComputed,
        models_cons]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeRigid
