import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualResidual

/-!
# Retaining unselected equations around a residual reduction

A worklist may select a later equation without losing the earlier ones.
Their actual terms are instantiated by the selected answer and retained.
The same construction applies across a change of declaration family.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualResidual

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V W : Type} {source : V → MetaArity S} {target : W → MetaArity S}

theorem Reduction.keep_left {problem : Problem source} {answer : Assignment source target}
    {remaining : Problem target} (reduction : Reduction problem answer remaining) (extra : Problem source) :
    Reduction (extra ++ problem) answer (mapProblem answer extra ++ remaining) := by
  constructor
  · intro Next next candidate solved
    obtain ⟨extraSolved, restSolved⟩ := (models_append _ _ _).mp solved
    exact (models_append _ _ _).mpr
      ⟨(models_mapProblem answer candidate extra).mp extraSolved,
        reduction.sound next candidate restSolved⟩
  · intro Next next candidate solved
    obtain ⟨extraSolved, restSolved⟩ := (models_append _ _ _).mp solved
    obtain ⟨residual, remainingSolved, components⟩ := reduction.complete next candidate restSolved
    exact ⟨residual, (models_append _ _ _).mpr
      ⟨(models_of_components candidate answer residual components extra).mp extraSolved, remainingSolved⟩,
      components⟩

theorem Reduction.keep_right {problem : Problem source} {answer : Assignment source target}
    {remaining : Problem target} (reduction : Reduction problem answer remaining) (extra : Problem source) :
    Reduction (problem ++ extra) answer (remaining ++ mapProblem answer extra) := by
  constructor
  · intro Next next candidate solved
    obtain ⟨restSolved, extraSolved⟩ := (models_append _ _ _).mp solved
    exact (models_append _ _ _).mpr
      ⟨reduction.sound next candidate restSolved,
        (models_mapProblem answer candidate extra).mp extraSolved⟩
  · intro Next next candidate solved
    obtain ⟨restSolved, extraSolved⟩ := (models_append _ _ _).mp solved
    obtain ⟨residual, remainingSolved, components⟩ := reduction.complete next candidate restSolved
    exact ⟨residual, (models_append _ _ _).mpr
      ⟨remainingSolved, (models_of_components candidate answer residual components extra).mp extraSolved⟩,
      components⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualResidual
