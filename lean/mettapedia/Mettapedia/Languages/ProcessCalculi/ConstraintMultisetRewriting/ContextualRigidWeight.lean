import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualEquationWeight
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidSupport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualInterfacePotential

/-!
# Rigid normalization cannot increase structural solver measures

Decomposing equal rigid heads can add field equations, but their total
existing term size cannot exceed the source size. Active image and interface
potentials cannot increase either. These bounds hold for arbitrary flexible
applications, without treating residual equations as already solved.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidWeight

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualRigidSolver
open ContextualEquationWeight

variable {S : Signature} {V : Type} {source : V → MetaArity S}

theorem merge_weight {first second : Option (Problem source)} {result : Problem source}
    (computed : merge first second = some result) (left right : Nat)
    (firstBound : ∀ problem, first = some problem → weight problem ≤ left)
    (secondBound : ∀ problem, second = some problem → weight problem ≤ right) :
    weight result ≤ left + right := by
  cases first with
  | none => cases computed
  | some first =>
      cases second with
      | none => cases computed
      | some second =>
          have same : first ++ second = result := Option.some.inj computed
          rw [← same, weight_append]
          exact Nat.add_le_add (firstBound _ rfl) (secondBound _ rfl)

mutual
theorem terms_weight [∀ sort, DecidableEq (S.Op sort)] :
    ∀ {Γ : Ctx S} {sort : S.Srt} (left right : Term (signature S source) Γ sort)
      {result : Problem source}, terms left right = some result → weight result ≤ termSize left + termSize right
  | _, _, .op (.inr identity) args, right, result, computed => by
      have same : [(observe (Term.op (.inr identity) args), observe right)] = result := by
        simpa only [terms, Option.some.injEq] using computed
      subst result
      exact Nat.le_refl _
  | _, _, .var position, .op (.inr identity) args, result, computed => by
      have same : [(observe (Term.var position), observe (Term.op (.inr identity) args))] = result := by
        simpa only [terms, Option.some.injEq] using computed
      subst result
      exact Nat.le_refl _
  | _, _, .op (.inl operator) args, .op (.inr identity) remaining, result, computed => by
      have same : [(observe (Term.op (.inl operator) args), observe (Term.op (.inr identity) remaining))] = result := by
        simpa only [terms, Option.some.injEq] using computed
      subst result
      exact Nat.le_refl _
  | _, _, .var first, .var second, result, computed => by
      by_cases same : first = second
      · have empty : [] = result := by simpa only [terms, if_pos same, Option.some.injEq] using computed
        subst result
        exact Nat.zero_le _
      · simp only [terms, if_neg same, reduceCtorEq] at computed
  | _, _, .var _, .op (.inl _) _, _, computed => by simp only [terms, reduceCtorEq] at computed
  | _, _, .op (.inl _) _, .var _, _, computed => by simp only [terms, reduceCtorEq] at computed
  | _, _, .op (.inl first) left, .op (.inl second) right, result, computed => by
      by_cases same : first = second
      · subst second
        simp only [terms] at computed
        have bounded := arguments_weight left right computed
        simp only [termSize]
        omega
      · simp only [terms, dif_neg same, reduceCtorEq] at computed
termination_by Γ sort left _right => 2 * termSize left
decreasing_by all_goals simp_all only [termSize]; omega

theorem arguments_weight [∀ sort, DecidableEq (S.Op sort)] :
    ∀ {arities : List (MetaArity S)} {Γ : Ctx S} (left right : Args (signature S source) arities Γ)
      {result : Problem source}, arguments left right = some result → weight result ≤ argsSize left + argsSize right
  | _, _, .nil, .nil, result, computed => by
      have empty : [] = result := by simpa only [arguments, Option.some.injEq] using computed
      subst result
      exact Nat.le_refl _
  | _, _, .cons first rest, .cons second remaining, result, computed => by
      simp only [arguments] at computed
      have bounded := merge_weight computed (termSize first + termSize second) (argsSize rest + argsSize remaining)
        (fun _ recovered => terms_weight first second recovered)
        (fun _ recovered => arguments_weight rest remaining recovered)
      simp only [argsSize]
      omega
termination_by arities Γ left _right => 2 * argsSize left + 1
decreasing_by
  all_goals simp_all only [argsSize]
  · omega
  · have positive := termSize_pos first
    omega
end

theorem equation_weight [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]
    (pair : Equation (Observation S source)) {result : Problem source}
    (computed : equation pair = some result) : weight result ≤ equationSize pair := by
  rcases pair with ⟨⟨Γ, sort, left⟩, ⟨Δ, output, right⟩⟩
  by_cases contexts : Γ = Δ
  · subst Δ
    by_cases sorts : sort = output
    · subst output
      exact terms_weight left right (by simpa only [equation, dite_true] using computed)
    · simp only [equation, dif_neg sorts, dite_true, reduceCtorEq] at computed
  · simp only [equation, dif_neg contexts, reduceCtorEq] at computed

theorem normalization_weight [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)] :
    ∀ (problem : Problem source) {result : Problem source},
      normalize problem = some result → weight result ≤ weight problem
  | [], result, computed => by
      have empty : [] = result := by simpa only [ContextualRigidSolver.normalize, Option.some.injEq] using computed
      subst result
      exact Nat.le_refl _
  | pair :: rest, _, computed =>
      merge_weight computed (equationSize pair) (weight rest)
        (fun _ recovered => equation_weight pair recovered)
        (fun _ recovered => normalization_weight rest recovered)

theorem normalization_interface_cost [DecidableEq V] [DecidableEq S.Srt]
    [∀ sort, DecidableEq (S.Op sort)] {problem result : Problem source}
    (computed : normalize problem = some result) :
    ContextualInterfacePotential.cost source (ContextualActiveSupport.active result) ≤
      ContextualInterfacePotential.cost source (ContextualActiveSupport.active problem) :=
  ContextualInterfacePotential.monotone source (ContextualRigidSupport.normalization_active_subset computed)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidWeight
