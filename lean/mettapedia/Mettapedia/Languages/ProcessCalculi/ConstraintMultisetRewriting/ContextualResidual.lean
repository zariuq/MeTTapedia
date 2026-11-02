import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameUnifier
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualObservationAction

/-!
# Contextual solving with explicit residual equations

A reduction may replace a declaration frame and leave equations at several
object contexts and sorts. Its residual problem is data on the existing terms.
Soundness and completeness quantify over assignments into any later frame;
factorization retains every original declaration, including unused outputs.

This contract does not assert that a residual problem is solved. In particular,
sequential reduction passes the actual residual equations to the next stage.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualResidual

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V W X Y : Type}
  {source : V → MetaArity S} {middle : W → MetaArity S}
  {target : X → MetaArity S} {next : Y → MetaArity S}

abbrev Problem (declaration : V → MetaArity S) := EquationStore (Observation S declaration)

def Models (assignment : Assignment source target) (problem : Problem source) : Prop :=
  ∀ equation ∈ problem,
    instantiateObservation assignment equation.1 = instantiateObservation assignment equation.2

def mapProblem (assignment : Assignment source target) (problem : Problem source) : Problem target :=
  problem.map fun equation =>
    (instantiateObservation assignment equation.1, instantiateObservation assignment equation.2)

theorem models_append (assignment : Assignment source target) (first second : Problem source) :
    Models assignment (first ++ second) ↔ Models assignment first ∧ Models assignment second := by
  simp only [Models, List.forall_mem_append]

theorem models_observed_iff (assignment : Assignment source target)
    {Γ : Ctx S} {sort : S.Srt} (left right : Term (signature S source) Γ sort) :
    Models assignment [(observe left, observe right)] ↔ instantiate assignment left = instantiate assignment right := by
  constructor
  · intro solved
    exact observe_injective (solved _ (List.mem_singleton_self _))
  · intro same equation member
    have only := List.mem_singleton.mp member
    subst equation
    exact congrArg observe same

theorem models_mapProblem (first : Assignment source middle) (second : Assignment middle target)
    (problem : Problem source) :
    Models second (mapProblem first problem) ↔ Models (Assignment.compose second first) problem := by
  constructor
  · intro solved equation member
    simpa only [instantiateObservation_comp] using
      solved _ (List.mem_map.mpr ⟨equation, member, rfl⟩)
  · intro solved equation member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    simpa only [instantiateObservation_comp] using solved original present

theorem models_compose {first : Assignment source middle} {problem : Problem source}
    (solved : Models first problem) (second : Assignment middle target) :
    Models (Assignment.compose second first) problem := by
  intro equation member
  simpa only [instantiateObservation_comp] using
    congrArg (instantiateObservation second) (solved equation member)

theorem models_of_components (candidate : Assignment source target) (answer : Assignment source middle)
    (residual : Assignment middle target)
    (components : ∀ identity, candidate identity = instantiate residual (answer identity))
    (problem : Problem source) :
    Models candidate problem ↔ Models residual (mapProblem answer problem) := by
  rw [models_mapProblem]
  have same : candidate = Assignment.compose residual answer := funext components
  rw [same]

structure Reduction (problem : Problem source) (answer : Assignment source middle)
    (remaining : Problem middle) : Prop where
  sound : ∀ {Variables : Type} (declaration : Variables → MetaArity S)
    (residual : Assignment middle declaration), Models residual remaining →
      Models (Assignment.compose residual answer) problem
  complete : ∀ {Variables : Type} (declaration : Variables → MetaArity S)
    (candidate : Assignment source declaration), Models candidate problem →
      ∃ residual : Assignment middle declaration, Models residual remaining ∧
        ∀ identity, candidate identity = instantiate residual (answer identity)

/-- Composition retains the intermediate problem, rather than replaying an
old derivation or assuming that residual equations were discharged. -/
theorem Reduction.compose {problem : Problem source} {remaining : Problem middle}
    {last : Problem target} {first : Assignment source middle} {second : Assignment middle target}
    (one : Reduction problem first remaining) (two : Reduction remaining second last) :
    Reduction problem (Assignment.compose second first) last := by
  constructor
  · intro Variables declaration residual solved
    have result := one.sound declaration (Assignment.compose residual second)
      (two.sound declaration residual solved)
    simpa only [Assignment.compose_associative] using result
  · intro Variables declaration candidate solved
    obtain ⟨throughFirst, remainingSolved, firstComponents⟩ := one.complete declaration candidate solved
    obtain ⟨throughSecond, lastSolved, secondComponents⟩ := two.complete declaration throughFirst remainingSolved
    refine ⟨throughSecond, lastSolved, fun identity => ?_⟩
    exact (firstComponents identity).trans
      (ContextualFrameUnifier.factor_terms throughFirst second throughSecond secondComponents (first identity))

theorem Reduction.finished_sound {problem : Problem source} {answer : Assignment source middle}
    (reduction : Reduction problem answer []) : Models answer problem := by
  have result := reduction.sound middle (generator middle) (by simp [Models])
  simpa only [Assignment.compose_identity_left] using result

def observeProblem {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S source) Γ sort)) : Problem source :=
  problem.map fun equation => (observe equation.1, observe equation.2)

theorem observeProblem_mapProblem (change : Assignment source target)
    {Γ : Ctx S} {sort : S.Srt} (problem : EquationStore (Term (signature S source) Γ sort)) :
    observeProblem (ContextualFrameUnifier.mapProblem change problem) =
      mapProblem change (observeProblem problem) := by
  simp only [observeProblem, ContextualFrameUnifier.mapProblem, mapProblem, List.map_map]
  rfl

theorem models_observeProblem (assignment : Assignment source target)
    {Γ : Ctx S} {sort : S.Srt} (problem : EquationStore (Term (signature S source) Γ sort)) :
    Models assignment (observeProblem problem) ↔ ContextualFrameUnifier.Models assignment problem := by
  constructor
  · intro solved equation member
    exact observe_injective (solved _ (List.mem_map.mpr ⟨equation, member, rfl⟩))
  · intro solved equation member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact congrArg observe (solved original present)

/-- Each independently proved principal frame case can solve a prefix of a
heterogeneous queue. All other equations are instantiated and retained. -/
theorem of_principal_prefix {Γ : Ctx S} {sort : S.Srt}
    {solved : EquationStore (Term (signature S source) Γ sort)}
    {answer : Assignment source middle} (principal : ContextualFrameUnifier.Principal solved answer)
    (remaining : Problem source) :
    Reduction (observeProblem solved ++ remaining) answer (mapProblem answer remaining) := by
  constructor
  · intro Variables declaration residual residualSolved
    apply (models_append _ _ _).mpr
    refine ⟨(models_observeProblem _ _).mpr ?_, (models_mapProblem answer residual remaining).mp residualSolved⟩
    exact ContextualFrameUnifier.models_compose principal.sound residual
  · intro Variables declaration candidate solvedAll
    obtain ⟨solvedPart, remainingSolved⟩ := (models_append _ _ _).mp solvedAll
    obtain ⟨residual, components⟩ := principal.factors declaration candidate
      ((models_observeProblem _ _).mp solvedPart)
    exact ⟨residual,
      (models_of_components candidate answer residual components remaining).mp remainingSolved, components⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualResidual
