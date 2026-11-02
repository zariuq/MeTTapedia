import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternProblems
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidSolver

/-!
# Rigid decomposition preserves structural contextual patterns

The actual retained field equations inherit their pattern proofs, including
each field's binder prefix. Flexible equations remain explicit. Successful
normalization therefore preserves the solver fragment throughout a queue.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidPatterns

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualPatternFragment
open ContextualRigidSolver

variable {S : Signature} {V : Type} {source : V → MetaArity S}

theorem append_patterns (first second : Problem source) :
    ProblemPattern (first ++ second) ↔ ProblemPattern first ∧ ProblemPattern second := by
  simp only [ProblemPattern, List.forall_mem_append]

theorem merge_patterns {first second : Option (Problem source)} {result : Problem source}
    (computed : merge first second = some result)
    (left : ∀ problem, first = some problem → ProblemPattern problem)
    (right : ∀ problem, second = some problem → ProblemPattern problem) : ProblemPattern result := by
  cases first with
  | none => cases computed
  | some first =>
      cases second with
      | none => cases computed
      | some second =>
          have same : first ++ second = result := Option.some.inj computed
          exact same ▸ (append_patterns first second).mpr ⟨left _ rfl, right _ rfl⟩

mutual
theorem terms_patterns [∀ sort, DecidableEq (S.Op sort)] :
    ∀ {Γ : Ctx S} {sort : S.Srt} (left right : Term (signature S source) Γ sort)
      (_first : Pattern S source left) (_second : Pattern S source right)
      {result : Problem source}, terms left right = some result → ProblemPattern result
  | _, _, .op (.inr identity) args, right, first, second, result, computed => by
      have same : [(observe (Term.op (.inr identity) args), observe right)] = result := by
        simpa only [terms, Option.some.injEq] using computed
      subst result
      intro equation member
      have only := List.mem_singleton.mp member
      subst equation
      exact ⟨first, second⟩
  | _, _, .var position, .op (.inr identity) args, first, second, result, computed => by
      have same : [(observe (Term.var position), observe (Term.op (.inr identity) args))] = result := by
        simpa only [terms, Option.some.injEq] using computed
      subst result
      intro equation member
      have only := List.mem_singleton.mp member
      subst equation
      exact ⟨first, second⟩
  | _, _, .op (.inl operator) args, .op (.inr identity) remaining, first, second, result, computed => by
      have same : [(observe (Term.op (.inl operator) args), observe (Term.op (.inr identity) remaining))] = result := by
        simpa only [terms, Option.some.injEq] using computed
      subst result
      intro equation member
      have only := List.mem_singleton.mp member
      subst equation
      exact ⟨first, second⟩
  | _, _, .var first, .var second, _, _, result, computed => by
      by_cases same : first = second
      · have empty : [] = result := by simpa only [terms, if_pos same, Option.some.injEq] using computed
        subst result
        exact fun _ member => False.elim (List.not_mem_nil member)
      · simp only [terms, if_neg same, reduceCtorEq] at computed
  | _, _, .var _, .op (.inl _) _, _, _, _, computed => by simp only [terms, reduceCtorEq] at computed
  | _, _, .op (.inl _) _, .var _, _, _, _, computed => by simp only [terms, reduceCtorEq] at computed
  | _, _, .op (.inl first) left, .op (.inl second) right, leftPattern, rightPattern, _, computed => by
      by_cases same : first = second
      · subst second
        simp only [terms] at computed
        exact arguments_patterns left right
          (checkArgs_sound (S := S) (declaration := source) left
            (check_complete (S := S) (declaration := source) _ leftPattern))
          (checkArgs_sound (S := S) (declaration := source) right
            (check_complete (S := S) (declaration := source) _ rightPattern)) computed
      · simp only [terms, dif_neg same, reduceCtorEq] at computed
termination_by Γ sort left _right => 2 * termSize left
decreasing_by all_goals simp_all only [termSize]; omega

theorem arguments_patterns [∀ sort, DecidableEq (S.Op sort)] :
    ∀ {arities : List (MetaArity S)} {Γ : Ctx S} (left right : Args (signature S source) arities Γ)
      (_first : PatternArgs S source left) (_second : PatternArgs S source right)
      {result : Problem source}, arguments left right = some result → ProblemPattern result
  | _, _, .nil, .nil, _, _, result, computed => by
      have empty : [] = result := by simpa only [arguments, Option.some.injEq] using computed
      subst result
      exact fun _ member => False.elim (List.not_mem_nil member)
  | _, _, .cons first rest, .cons second remaining, leftPattern, rightPattern, _, computed => by
      have leftChecked : check first = true ∧ checkArgs rest = true := by
        simpa only [checkArgs, Bool.and_eq_true] using checkArgs_complete (S := S) (declaration := source) _ leftPattern
      have rightChecked : check second = true ∧ checkArgs remaining = true := by
        simpa only [checkArgs, Bool.and_eq_true] using checkArgs_complete (S := S) (declaration := source) _ rightPattern
      simp only [arguments] at computed
      apply merge_patterns computed
      · exact fun _ recovered => terms_patterns first second (check_sound first leftChecked.1)
          (check_sound second rightChecked.1) recovered
      · exact fun _ recovered => arguments_patterns rest remaining (checkArgs_sound rest leftChecked.2)
          (checkArgs_sound remaining rightChecked.2) recovered
termination_by arities Γ left _right => 2 * argsSize left + 1
decreasing_by
  all_goals simp_all only [argsSize]
  · omega
  · have positive := termSize_pos first
    omega
end

theorem equation_patterns [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]
    (pair : Equation (Observation S source)) (first : Pattern S source pair.1.2.2)
    (second : Pattern S source pair.2.2.2) {result : Problem source}
    (computed : equation pair = some result) : ProblemPattern result := by
  rcases pair with ⟨⟨Γ, sort, left⟩, ⟨Δ, output, right⟩⟩
  by_cases contexts : Γ = Δ
  · subst Δ
    by_cases sorts : sort = output
    · subst output
      exact terms_patterns left right first second (by simpa only [equation, dite_true] using computed)
    · simp only [equation, dif_neg sorts, dite_true, reduceCtorEq] at computed
  · simp only [equation, dif_neg contexts, reduceCtorEq] at computed

theorem normalization_patterns [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)] :
    ∀ (problem : Problem source), ProblemPattern problem →
      ∀ {result : Problem source}, normalize problem = some result → ProblemPattern result
  | [], _, result, computed => by
      have empty : [] = result := by simpa only [ContextualRigidSolver.normalize, Option.some.injEq] using computed
      subst result
      exact fun _ member => False.elim (List.not_mem_nil member)
  | pair :: rest, patterned, _, computed => by
      apply merge_patterns computed
      · exact fun _ recovered => equation_patterns pair (patterned pair List.mem_cons_self).1
          (patterned pair List.mem_cons_self).2 recovered
      · exact fun _ recovered => normalization_patterns rest
          (fun equation member => patterned equation (List.mem_cons_of_mem _ member)) recovered

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidPatterns
