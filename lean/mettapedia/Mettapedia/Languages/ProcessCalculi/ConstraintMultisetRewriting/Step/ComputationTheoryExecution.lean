import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationTheoryMap
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationSupport

/-!
# Reusing a computation after a qualified change of theory

An old source path persists by rule inclusion and is realized by actual
firings in the new theory, from the transported complete initial state.
Keeping a completed answer additionally requires the scoped no-new-redex
license. A checked context footprint derives that license for fresh-name
extensions. These are re-realized runs: literal physical event identities
and an external scheduler's choices are not identified across theories.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationTheory

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open AlgebraicParallel NativeTypesOnTheStep.Computing ConversionCoherence
open ComputationProfile ComputationEvolution ComputationSupport

variable {Head L : Type} [UniverseLevel.LevelOrder L] {old next : Setting Head L}
  (inclusion : RulesSub old.R next.R) (nextQualified : Qualified next)
  (nextPresentation : SchemaPresentation next.R)
  {oldQualified : Qualified old} {oldPresentation : SchemaPresentation old.R}
  {source : ComputationProfile.Configuration (S := old)}

theorem execution_replays (execution : Execution oldQualified oldPresentation source) :
    ∃ run : (step next.levels Nat).toStep.Run (configuration inclusion source).state,
      ∃ profile : RunProfile nextQualified nextPresentation (configuration inclusion source) run,
        profile.execution.term = execution.term :=
  (full_runs_iff nextQualified nextPresentation (configuration := configuration inclusion source)).mp
    (steps_mono inclusion execution.reduces)

theorem completed_answer_replays
    (heads : ∀ {left right}, next.R.headEq left right → old.R.headEq left right)
    {value : Tm Head source.state.frame.arity}
    (roots : RootAgreementAt (old := old.R) (next := next.R) value)
    (answer : Answer old.R source.code value) :
    ∃ run : (step next.levels Nat).toStep.Run (configuration inclusion source).state,
      ∃ profile : RunProfile nextQualified nextPresentation (configuration inclusion source) run,
        profile.execution.term = value ∧ ConstructorSystem.Normal next.R profile.execution.term :=
  (full_answers_iff nextQualified nextPresentation (configuration := configuration inclusion source)).mp
    (answer_preserved inclusion nextPresentation heads roots answer)

theorem cached_answer_replays
    (heads : ∀ {left right}, next.R.headEq left right → old.R.headEq left right)
    {inner : Nat} (cache : Cache Head source.state.frame.arity inner)
    (checked : cache.check = true) (hole : Tm Head inner) (name : DeclName)
    (accepted : cache.scope hole name = true)
    (newRules : ∀ {n : Nat} {left right : Tm Head n}, next.R.computation.step left right →
      old.R.computation.step left right ∨ Uses name left)
    (answer : Answer old.R source.code (cache.context.plug hole)) :
    ∃ run : (step next.levels Nat).toStep.Run (configuration inclusion source).state,
      ∃ profile : RunProfile nextQualified nextPresentation (configuration inclusion source) run,
        profile.execution.term = cache.context.plug hole ∧
          ConstructorSystem.Normal next.R profile.execution.term :=
  completed_answer_replays inclusion nextQualified nextPresentation heads
    (cache.licenses_roots checked hole name accepted newRules) answer

theorem replayed_type_is_original
    {run : (step next.levels Nat).toStep.Run (configuration inclusion source).state}
    (profile : RunProfile nextQualified nextPresentation (configuration inclusion source) run) :
    Typed next.R source.state.frame.raw profile.execution.term (source.state.label source.active).1.code :=
  full_run_typed nextQualified nextPresentation profile

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationTheory

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationTheory.cached_answer_replays
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationTheory.replayed_type_is_original
