import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidSolver

/-!
# The actual rigid normalizer retains only typed flexible-root equations

Every residual equation has matching object-context and result-sort tags,
with a contextual hole at one of its roots. This invariant is proved from
the executable decomposition, including binding fields. Such a queue is a
fixed point of rigid normalization.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidNormalForm

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualRigidSolver

variable {S : Signature} {V : Type} {source : V → MetaArity S}

inductive EquationNormal (source : V → MetaArity S) : Equation (Observation S source) → Prop
  | flexLeft {Γ : Ctx S} {sort : S.Srt} (key : Operator source sort)
      (arguments : Args (signature S source) ((signature S source).arity (.inr key)) Γ)
      (right : Term (signature S source) Γ sort) :
      EquationNormal source (observe (Term.op (.inr key) arguments), observe right)
  | flexRight {Γ : Ctx S} {sort : S.Srt} (key : Operator source sort)
      (left : Term (signature S source) Γ sort)
      (arguments : Args (signature S source) ((signature S source).arity (.inr key)) Γ) :
      EquationNormal source (observe left, observe (Term.op (.inr key) arguments))

def ProblemNormal (problem : Problem source) : Prop := ∀ equation ∈ problem, EquationNormal source equation

theorem append_normal (first second : Problem source) :
    ProblemNormal (first ++ second) ↔ ProblemNormal first ∧ ProblemNormal second := by
  simp only [ProblemNormal, List.forall_mem_append]

theorem merge_normal {first second : Option (Problem source)} {result : Problem source}
    (computed : merge first second = some result)
    (left : ∀ problem, first = some problem → ProblemNormal problem)
    (right : ∀ problem, second = some problem → ProblemNormal problem) : ProblemNormal result := by
  cases first with
  | none => cases computed
  | some first =>
      cases second with
      | none => cases computed
      | some second =>
          have same : first ++ second = result := Option.some.inj computed
          exact same ▸ (append_normal first second).mpr ⟨left _ rfl, right _ rfl⟩

mutual
theorem terms_normal [∀ sort, DecidableEq (S.Op sort)] :
    ∀ {Γ : Ctx S} {sort : S.Srt} (left right : Term (signature S source) Γ sort)
      {result : Problem source}, terms left right = some result → ProblemNormal result
  | _, _, .op (.inr key) args, right, result, computed => by
      have same : [(observe (Term.op (.inr key) args), observe right)] = result := by
        simpa only [terms, Option.some.injEq] using computed
      subst result
      intro equation member
      have only := List.mem_singleton.mp member
      subst equation
      exact .flexLeft key args right
  | _, _, .var position, .op (.inr key) args, result, computed => by
      have same : [(observe (Term.var position), observe (Term.op (.inr key) args))] = result := by
        simpa only [terms, Option.some.injEq] using computed
      subst result
      intro equation member
      have only := List.mem_singleton.mp member
      subst equation
      exact .flexRight key (.var position) args
  | _, _, .op (.inl operator) args, .op (.inr key) remaining, result, computed => by
      have same : [(observe (Term.op (.inl operator) args), observe (Term.op (.inr key) remaining))] = result := by
        simpa only [terms, Option.some.injEq] using computed
      subst result
      intro equation member
      have only := List.mem_singleton.mp member
      subst equation
      exact .flexRight key (.op (.inl operator) args) remaining
  | _, _, .var first, .var second, result, computed => by
      by_cases same : first = second
      · have empty : [] = result := by simpa only [terms, if_pos same, Option.some.injEq] using computed
        subst result
        exact fun _ member => False.elim (List.not_mem_nil member)
      · simp only [terms, if_neg same, reduceCtorEq] at computed
  | _, _, .var _, .op (.inl _) _, _, computed => by simp only [terms, reduceCtorEq] at computed
  | _, _, .op (.inl _) _, .var _, _, computed => by simp only [terms, reduceCtorEq] at computed
  | _, _, .op (.inl first) left, .op (.inl second) right, _, computed => by
      by_cases same : first = second
      · subst second
        simp only [terms] at computed
        exact arguments_normal left right computed
      · simp only [terms, dif_neg same, reduceCtorEq] at computed
termination_by Γ sort left _right => 2 * termSize left
decreasing_by all_goals simp_all only [termSize]; omega

theorem arguments_normal [∀ sort, DecidableEq (S.Op sort)] :
    ∀ {arities : List (MetaArity S)} {Γ : Ctx S} (left right : Args (signature S source) arities Γ)
      {result : Problem source}, arguments left right = some result → ProblemNormal result
  | _, _, .nil, .nil, result, computed => by
      have empty : [] = result := by simpa only [arguments, Option.some.injEq] using computed
      subst result
      exact fun _ member => False.elim (List.not_mem_nil member)
  | _, _, .cons first rest, .cons second remaining, _, computed => by
      simp only [arguments] at computed
      apply merge_normal computed
      · exact fun _ recovered => terms_normal first second recovered
      · exact fun _ recovered => arguments_normal rest remaining recovered
termination_by arities Γ left _right => 2 * argsSize left + 1
decreasing_by
  all_goals simp_all only [argsSize]
  · omega
  · have positive := termSize_pos first
    omega
end

theorem equation_normal [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]
    (pair : Equation (Observation S source)) {result : Problem source}
    (computed : equation pair = some result) : ProblemNormal result := by
  rcases pair with ⟨⟨Γ, sort, left⟩, ⟨Δ, output, right⟩⟩
  by_cases contexts : Γ = Δ
  · subst Δ
    by_cases sorts : sort = output
    · subst output
      exact terms_normal left right (by simpa only [equation, dite_true] using computed)
    · simp only [equation, dif_neg sorts, dite_true, reduceCtorEq] at computed
  · simp only [equation, dif_neg contexts, reduceCtorEq] at computed

theorem normalization_normal [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)] :
    ∀ (problem : Problem source) {result : Problem source}, normalize problem = some result → ProblemNormal result
  | [], result, computed => by
      have empty : [] = result := by simpa only [ContextualRigidSolver.normalize, Option.some.injEq] using computed
      subst result
      exact fun _ member => False.elim (List.not_mem_nil member)
  | pair :: rest, _, computed => by
      apply merge_normal computed
      · exact fun _ recovered => equation_normal pair recovered
      · exact fun _ recovered => normalization_normal rest recovered

theorem equation_fixed [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)] :
    ∀ {pair : Equation (Observation S source)}, EquationNormal source pair → equation pair = some [pair]
  | _, .flexLeft key arguments right => by simp only [equation, observe, dite_true, terms]
  | _, .flexRight key (.var position) arguments => by simp only [equation, observe, dite_true, terms]
  | _, .flexRight key (.op (.inl operator) fields) arguments => by simp only [equation, observe, dite_true, terms]
  | _, .flexRight key (.op (.inr other) fields) arguments => by simp only [equation, observe, dite_true, terms]

theorem normalization_fixed [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)] :
    ∀ (problem : Problem source), ProblemNormal problem → normalize problem = some problem
  | [], _ => rfl
  | pair :: rest, normal => by
      rw [ContextualRigidSolver.normalize, equation_fixed (normal pair List.mem_cons_self), normalization_fixed rest
        (fun equation member => normal equation (List.mem_cons_of_mem _ member))]
      rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidNormalForm
