import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualResidual
import Mettapedia.OSLF.Syntax.PartialRenaming

/-!
# Executable rigid normalization of contextual equations

Common rigid heads are decomposed recursively, including their bound fields.
Clashes are refused. An equation with a contextual hole at either root remains
explicit, even when its arguments are repeated or compound. Such a residual
is not a claim of either failure or completion.

The result preserves exactly the solutions into every later declaration frame.
The structural equality profile here adds no conversion equations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidSolver

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual

variable {S : Signature} {V W : Type}
  {source : V → MetaArity S} {target : W → MetaArity S}

def merge (first second : Option (Problem source)) : Option (Problem source) := do
  let left ← first
  let right ← second
  pure (left ++ right)

def ModelsResult (assignment : Assignment source target) : Option (Problem source) → Prop
  | none => False
  | some problem => Models assignment problem

theorem models_merge (assignment : Assignment source target) (first second : Option (Problem source)) :
    ModelsResult assignment (merge first second) ↔
      ModelsResult assignment first ∧ ModelsResult assignment second := by
  cases first <;> cases second <;> simp [merge, ModelsResult, models_append]

mutual
def terms [∀ sort, DecidableEq (S.Op sort)] : {Γ : Ctx S} → {sort : S.Srt} →
    Term (signature S source) Γ sort → Term (signature S source) Γ sort → Option (Problem source)
  | _, _, first@(.op (.inr _) _), second => some [(observe first, observe second)]
  | _, _, first, second@(.op (.inr _) _) => some [(observe first, observe second)]
  | _, _, .var first, .var second =>
      if first = second then some [] else none
  | _, _, .op (.inl first) left, .op (.inl second) right =>
      if same : first = second then arguments left (same.symm ▸ right) else none
  | _, _, _, _ => none
termination_by Γ sort first _second => 2 * termSize first
decreasing_by all_goals simp_all only [termSize]; omega

def arguments [∀ sort, DecidableEq (S.Op sort)] : {arities : List (List S.Srt × S.Srt)} →
    {Γ : Ctx S} → Args (signature S source) arities Γ → Args (signature S source) arities Γ →
      Option (Problem source)
  | _, _, .nil, .nil => some []
  | _, _, .cons first rest, .cons second remaining =>
      merge (terms first second) (arguments rest remaining)
termination_by arities Γ first _second => 2 * argsSize first + 1
decreasing_by
  all_goals simp_all only [argsSize]
  · omega
  · have positive := termSize_pos first
    omega
end

mutual
theorem models_terms [∀ sort, DecidableEq (S.Op sort)]
    (assignment : Assignment source target) : ∀ {Γ : Ctx S} {sort : S.Srt}
      (first second : Term (signature S source) Γ sort),
    ModelsResult assignment (terms first second) ↔ instantiate assignment first = instantiate assignment second
  | _, _, .op (.inr identity) args, second => by
      simp only [terms, ModelsResult]
      exact models_observed_iff assignment (.op (.inr identity) args) second
  | _, _, .var first, .op (.inr identity) args => by
      simp only [terms, ModelsResult]
      exact models_observed_iff assignment (.var first) (.op (.inr identity) args)
  | _, _, .op (.inl first) left, .op (.inr identity) right => by
      simp only [terms, ModelsResult]
      exact models_observed_iff assignment (.op (.inl first) left) (.op (.inr identity) right)
  | _, _, .var first, .var second => by
      simp only [terms]
      split_ifs with same
      · subst second
        simp [ModelsResult, Models]
      · simp [ModelsResult, instantiate, same]
  | _, _, .var _, .op (.inl _) _ => by simp [terms, ModelsResult, instantiate]
  | _, _, .op (.inl _) _, .var _ => by simp [terms, ModelsResult, instantiate]
  | _, _, .op (.inl first) left, .op (.inl second) right => by
      simp only [terms]
      split_ifs with same
      · subst second
        rw [models_arguments assignment left right]
        simp only [instantiate]
        constructor
        · exact congrArg (Term.op (S := signature S target) (.inl first))
        · intro equal
          exact eq_of_heq (Term.op.inj equal).2
      · simp only [ModelsResult, instantiate, false_iff]
        intro equal
        exact same (Sum.inl.inj (Term.op.inj equal).1)
termination_by Γ sort first _second => 2 * termSize first
decreasing_by all_goals simp_all only [termSize]; omega

theorem models_arguments [∀ sort, DecidableEq (S.Op sort)]
    (assignment : Assignment source target) : ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (first second : Args (signature S source) arities Γ),
    ModelsResult assignment (arguments first second) ↔
      instantiateArgs assignment first = instantiateArgs assignment second
  | _, _, .nil, .nil => by simp [arguments, ModelsResult, Models, instantiateArgs]
  | _, _, .cons first rest, .cons second remaining => by
      rw [arguments, models_merge, models_terms assignment first second,
        models_arguments assignment rest remaining]
      simp only [instantiateArgs]
      exact ⟨fun both => congrArg₂ Args.cons both.1 both.2, Args.cons.inj⟩
termination_by arities Γ first _second => 2 * argsSize first + 1
decreasing_by
  all_goals simp_all only [argsSize]
  · omega
  · have positive := termSize_pos first
    omega
end

/-- Metadata comparison precedes any cast of the existing terms. A context
or sort mismatch is a clash, even for identical closed constructor trees. -/
def equation [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]
    (pair : Equation (Observation S source)) : Option (Problem source) := by
  rcases pair with ⟨⟨Γ, sort, first⟩, ⟨Δ, result, second⟩⟩
  by_cases contexts : Γ = Δ
  · subst Δ
    by_cases sorts : sort = result
    · subst result
      exact terms first second
    · exact none
  · exact none

theorem models_equation [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]
    (assignment : Assignment source target) (pair : Equation (Observation S source)) :
    ModelsResult assignment (equation pair) ↔
      instantiateObservation assignment pair.1 = instantiateObservation assignment pair.2 := by
  rcases pair with ⟨⟨Γ, sort, first⟩, ⟨Δ, result, second⟩⟩
  dsimp only [equation]
  split_ifs with contexts sorts
  · subst Δ
    subst result
    rw [models_terms]
    exact ⟨congrArg observe, fun same => observe_injective same⟩
  · subst Δ
    simp only [ModelsResult, false_iff]
    intro same
    have inner := eq_of_heq (Sigma.mk.inj same).2
    exact sorts (congrArg Sigma.fst inner)
  · simp only [ModelsResult, false_iff]
    intro same
    exact contexts (congrArg Sigma.fst same)

def normalize [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)] :
    Problem source → Option (Problem source)
  | [] => some []
  | pair :: rest => merge (equation pair) (normalize rest)

theorem models_normalize [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]
    (assignment : Assignment source target) : ∀ problem : Problem source,
    ModelsResult assignment (normalize problem) ↔ Models assignment problem
  | [] => by simp [normalize, ModelsResult, Models]
  | pair :: rest => by
      rw [normalize, models_merge, models_equation, models_normalize assignment rest]
      simp only [Models, List.forall_mem_cons]

/-- Normalization is a genuine residual transformation: successful output
still has to be solved. Its proof covers all future declaration frames. -/
theorem normalization_reduction [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]
    {problem remaining : Problem source} (computed : normalize problem = some remaining) :
    Reduction problem (generator source) remaining := by
  have exactModels : ∀ {Variables : Type} (declaration : Variables → MetaArity S)
      (candidate : Assignment source declaration), Models candidate remaining ↔ Models candidate problem := by
    intro Variables declaration candidate
    have result := models_normalize candidate problem
    rw [computed] at result
    exact result
  constructor
  · intro Variables declaration residual solved
    simpa only [Assignment.compose_identity_right] using (exactModels declaration residual).mp solved
  · intro Variables declaration candidate solved
    exact ⟨candidate, (exactModels declaration candidate).mpr solved,
      fun identity => (instantiate_generator candidate identity).symm⟩

theorem refused_has_no_solution [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]
    {problem : Problem source} (computed : normalize problem = none)
    (assignment : Assignment source target) : ¬ Models assignment problem := by
  have result := models_normalize assignment problem
  rw [computed] at result
  exact result.not.mp id

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidSolver
