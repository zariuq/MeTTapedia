import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActiveSupport

/-!
# Rigid normalization introduces no active declaration

Decomposition retains only the actual field equations, including their
binding contexts. Their support is bounded by the original equation support.
The resulting finite active roster and its candidate-image potential cannot
increase. No restriction on flexible application arguments is needed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidSupport

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualRigidSolver
open ContextualActiveSupport

variable {S : Signature} {V W : Type} {source : V → MetaArity S} {next : W → MetaArity S}

def BoundedProblem (allowed : V → Prop) (problem : Problem source) : Prop :=
  ∀ equation ∈ problem, Bounded allowed equation.1.2.2 ∧ Bounded allowed equation.2.2.2

theorem bounded_append (allowed : V → Prop) (first second : Problem source) :
    BoundedProblem allowed (first ++ second) ↔
      BoundedProblem allowed first ∧ BoundedProblem allowed second := by
  simp only [BoundedProblem, List.forall_mem_append]

theorem bounded_merge (allowed : V → Prop) {first second : Option (Problem source)}
    {result : Problem source} (computed : merge first second = some result)
    (left : ∀ problem, first = some problem → BoundedProblem allowed problem)
    (right : ∀ problem, second = some problem → BoundedProblem allowed problem) :
    BoundedProblem allowed result := by
  cases first with
  | none => cases computed
  | some first =>
      cases second with
      | none => cases computed
      | some second =>
          have same : first ++ second = result := Option.some.inj computed
          exact same ▸ (bounded_append allowed first second).mpr ⟨left _ rfl, right _ rfl⟩

mutual
theorem bounded_terms [∀ sort, DecidableEq (S.Op sort)] (allowed : V → Prop) :
    ∀ {Γ : Ctx S} {sort : S.Srt} (left right : Term (signature S source) Γ sort)
      (_first : Bounded allowed left) (_second : Bounded allowed right)
      {result : Problem source}, terms left right = some result → BoundedProblem allowed result
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
  | _, _, .var _, .op (.inl _) _, _, _, result, computed => by
      simp only [terms, reduceCtorEq] at computed
  | _, _, .op (.inl _) _, .var _, _, _, result, computed => by
      simp only [terms, reduceCtorEq] at computed
  | _, _, .op (.inl first) left, .op (.inl second) right, leftBound, rightBound, result, computed => by
      by_cases same : first = second
      · subst second
        simp only [terms] at computed
        exact bounded_arguments allowed left right leftBound rightBound computed
      · simp only [terms, dif_neg same, reduceCtorEq] at computed
termination_by Γ sort left _right => 2 * termSize left
decreasing_by all_goals simp_all only [termSize]; omega

theorem bounded_arguments [∀ sort, DecidableEq (S.Op sort)] (allowed : V → Prop) :
    ∀ {arities : List (MetaArity S)} {Γ : Ctx S}
      (left right : Args (signature S source) arities Γ)
      (_first : BoundedArgs allowed left) (_second : BoundedArgs allowed right)
      {result : Problem source}, arguments left right = some result → BoundedProblem allowed result
  | _, _, .nil, .nil, _, _, result, computed => by
      have empty : [] = result := by simpa only [arguments, Option.some.injEq] using computed
      subst result
      exact fun _ member => False.elim (List.not_mem_nil member)
  | _, _, .cons first rest, .cons second remaining, leftBound, rightBound, result, computed => by
      simp only [arguments] at computed
      apply bounded_merge allowed computed
      · intro problem recovered
        exact bounded_terms allowed first second
          (fun identity member => leftBound identity (List.mem_append_left _ member))
          (fun identity member => rightBound identity (List.mem_append_left _ member)) recovered
      · intro problem recovered
        exact bounded_arguments allowed rest remaining
          (fun identity member => leftBound identity (List.mem_append_right _ member))
          (fun identity member => rightBound identity (List.mem_append_right _ member)) recovered
termination_by arities Γ left _right => 2 * argsSize left + 1
decreasing_by
  all_goals simp_all only [argsSize]
  · omega
  · have positive := termSize_pos first
    omega
end

theorem bounded_equation [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]
    (allowed : V → Prop) (pair : Equation (Observation S source))
    (first : Bounded allowed pair.1.2.2) (second : Bounded allowed pair.2.2.2)
    {result : Problem source} (computed : equation pair = some result) : BoundedProblem allowed result := by
  rcases pair with ⟨⟨Γ, sort, left⟩, ⟨Δ, output, right⟩⟩
  by_cases contexts : Γ = Δ
  · subst Δ
    by_cases sorts : sort = output
    · subst output
      exact bounded_terms allowed left right first second (by
        simpa only [equation, dite_true] using computed)
    · simp only [equation, dif_neg sorts, dite_true, reduceCtorEq] at computed
  · simp only [equation, dif_neg contexts, reduceCtorEq] at computed

theorem bounded_normalize [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]
    (allowed : V → Prop) : ∀ (problem : Problem source), BoundedProblem allowed problem →
    ∀ {result : Problem source}, normalize problem = some result → BoundedProblem allowed result
  | [], _, result, computed => by
      have empty : [] = result := by simpa only [ContextualRigidSolver.normalize, Option.some.injEq] using computed
      subst result
      exact fun _ member => False.elim (List.not_mem_nil member)
  | pair :: rest, bounded, result, computed => by
      apply bounded_merge allowed computed
      · intro remaining recovered
        exact bounded_equation allowed pair (bounded pair List.mem_cons_self).1
          (bounded pair List.mem_cons_self).2 recovered
      · intro remaining recovered
        exact bounded_normalize allowed rest
          (fun equation member => bounded equation (List.mem_cons_of_mem _ member)) recovered

theorem normalization_active_subset [DecidableEq V] [DecidableEq S.Srt]
    [∀ sort, DecidableEq (S.Op sort)] {problem result : Problem source}
    (computed : normalize problem = some result) : active result ⊆ active problem := by
  have bounded : BoundedProblem (fun identity => identity ∈ active problem) problem := by
    intro equation member
    constructor
    · intro identity present
      exact (mem_active identity problem).mpr ⟨equation, member, .inl present⟩
    · intro identity present
      exact (mem_active identity problem).mpr ⟨equation, member, .inr present⟩
  have retained := bounded_normalize _ problem bounded computed
  intro identity present
  obtain ⟨equation, member, inside⟩ := (mem_active identity result).mp present
  exact inside.elim ((retained equation member).1 identity) ((retained equation member).2 identity)

theorem normalization_potential_le [DecidableEq V] [DecidableEq S.Srt]
    [∀ sort, DecidableEq (S.Op sort)] {problem result : Problem source}
    (computed : normalize problem = some result) (candidate : Assignment source next) :
    potential candidate (active result) ≤ potential candidate (active problem) :=
  potential_monotone candidate (normalization_active_subset computed)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidSupport
