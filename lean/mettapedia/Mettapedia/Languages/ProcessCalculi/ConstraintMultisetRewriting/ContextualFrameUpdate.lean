import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualResidualContext

/-!
# Solver updates with an actual replacement declaration family

An update contains its new family, substitution and retained equation queue.
The reduction proof is established by the concrete solver case that builds
it. Composition acts on these same substitutions and queues. A fresh family
does not require a global supply of variable names or a finite sort carrier.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameUpdate

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual

variable {S : Signature} {V : Type} {source : V → MetaArity S}

structure Update (problem : Problem source) where
  Variables : Type
  equality : DecidableEq Variables
  declaration : Variables → MetaArity S
  answer : Assignment source declaration
  remaining : Problem declaration
  valid : Reduction problem answer remaining

def Update.then {problem : Problem source} (first : Update problem)
    (second : Update first.remaining) : Update problem where
  Variables := second.Variables
  equality := second.equality
  declaration := second.declaration
  answer := Assignment.compose second.answer first.answer
  remaining := second.remaining
  valid := first.valid.compose second.valid

def Update.keep_left {problem : Problem source} (update : Update problem)
    (extra : Problem source) : Update (extra ++ problem) where
  Variables := update.Variables
  equality := update.equality
  declaration := update.declaration
  answer := update.answer
  remaining := mapProblem update.answer extra ++ update.remaining
  valid := update.valid.keep_left extra

def Update.keep_right {problem : Problem source} (update : Update problem)
    (extra : Problem source) : Update (problem ++ extra) where
  Variables := update.Variables
  equality := update.equality
  declaration := update.declaration
  answer := update.answer
  remaining := update.remaining ++ mapProblem update.answer extra
  valid := update.valid.keep_right extra

def Update.swap {left right : Observation S source}
    (update : Update [(right, left)]) : Update [(left, right)] where
  Variables := update.Variables
  equality := update.equality
  declaration := update.declaration
  answer := update.answer
  remaining := update.remaining
  valid := by
    constructor
    · intro Next next candidate solved equation member
      have only := List.mem_singleton.mp member
      subst equation
      exact (update.valid.sound next candidate solved _ (List.mem_singleton_self _)).symm
    · intro Next next candidate solved
      apply update.valid.complete next candidate
      intro equation member
      have only := List.mem_singleton.mp member
      subst equation
      exact (solved _ (List.mem_singleton_self _)).symm

theorem Update.completed {problem : Problem source} (update : Update problem)
    (finished : update.remaining = []) : Models update.answer problem := by
  have reduced := update.valid
  rw [finished] at reduced
  exact reduced.finished_sound

theorem Update.factors {problem : Problem source} (update : Update problem)
    {Next : Type} (next : Next → MetaArity S) (candidate : Assignment source next)
    (solved : Models candidate problem) :
    ∃ residual : Assignment update.declaration next, Models residual update.remaining ∧
      ∀ identity, candidate identity = instantiate residual (update.answer identity) :=
  update.valid.complete next candidate solved

/-- Completed computed updates present all original solutions in every
future frame. A residual update needs its remaining equations and does not
have this unconditional factorization property. -/
theorem Update.completed_models_iff {problem : Problem source} (update : Update problem)
    (finished : update.remaining = []) {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment source next) :
    Models candidate problem ↔ ∃ residual : Assignment update.declaration next,
      ∀ identity, candidate identity = instantiate residual (update.answer identity) := by
  constructor
  · intro solved
    obtain ⟨residual, _, components⟩ := update.factors next candidate solved
    exact ⟨residual, components⟩
  · rintro ⟨residual, components⟩
    have same : candidate = Assignment.compose residual update.answer := funext components
    rw [same]
    exact update.valid.sound next residual (by simp [finished, Models])

/-- Completed executions of permuted equation queues have the same original
term instances even when the worklist creates different helper families. -/
theorem Update.completed_orders {firstProblem secondProblem : Problem source}
    (first : Update firstProblem) (second : Update secondProblem)
    (firstFinished : first.remaining = []) (secondFinished : second.remaining = [])
    (permutation : firstProblem.Perm secondProblem) :
    ∃ toSecond : Assignment first.declaration second.declaration,
      ∃ toFirst : Assignment second.declaration first.declaration,
        (∀ {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort),
          instantiate toSecond (instantiate first.answer term) = instantiate second.answer term) ∧
        (∀ {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort),
          instantiate toFirst (instantiate second.answer term) = instantiate first.answer term) := by
  have secondSolves : Models second.answer firstProblem :=
    fun equation member => second.completed secondFinished equation (permutation.mem_iff.mp member)
  have firstSolves : Models first.answer secondProblem :=
    fun equation member => first.completed firstFinished equation (permutation.mem_iff.mpr member)
  obtain ⟨toSecond, secondComponents⟩ :=
    (first.completed_models_iff firstFinished second.declaration second.answer).mp secondSolves
  obtain ⟨toFirst, firstComponents⟩ :=
    (second.completed_models_iff secondFinished first.declaration first.answer).mp firstSolves
  exact ⟨toSecond, toFirst,
    fun term => (ContextualFrameUnifier.factor_terms second.answer first.answer toSecond secondComponents term).symm,
    fun term => (ContextualFrameUnifier.factor_terms first.answer second.answer toFirst firstComponents term).symm⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameUpdate
