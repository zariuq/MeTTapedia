import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Directed

/-!
# Directed runs retain native effects and their original declared type

Forgetting the additional action policy leaves the exact full-program run:
the same firing word and the same endpoint. Every represented final code is
reached by directed reduction and has the initial row's declared type in the
initial context. The client supplies an actual restricted run, not a source
profile or a source-reduction certificate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Directed

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual ContextualDependentEta DependentFull
open NativeTypesOnTheStep.Computing ComputationProfile ComputationProgram

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
  (program : ComputationProgram.Program S.R) [DecidableRel S.R.headEq]
  (qualified : Qualified S)

def toFullProgramRun : {state : State S.R Nat} → (restricted program qualified).Run state →
    (ComputationProgram.restricted program qualified).Run state
  | _, .nil state => .nil state
  | _, .cons firing accepted rest =>
      .cons firing ⟨accepted.1, permitted_in_full_program program qualified accepted.2⟩
        (toFullProgramRun rest)

theorem toFullProgramRun_last {state : State S.R Nat} (run : (restricted program qualified).Run state) :
    (toFullProgramRun program qualified run).last = run.last := by
  induction run with
  | nil => rfl
  | cons _ _ _ ih => exact ih

theorem toFullProgramRun_word {state : State S.R Nat} (run : (restricted program qualified).Run state) :
    (toFullProgramRun program qualified run).word = run.word := by
  induction run with
  | nil => rfl
  | cons firing accepted rest ih => exact congrArg (List.cons _) ih

theorem run_reduces {configuration : ComputationProfile.Configuration (S := S)}
    (single : configuration.state.present = {configuration.active})
    (run : (restricted program qualified).Run configuration.state)
    {value : Tm Head configuration.state.frame.arity}
    (represented : Represents (S := S) value run.last) :
    StrongNormalization.ReducesStar S.R configuration.code value := by
  have initial : Represents (S := S) configuration.code configuration.state :=
    Computation.represents_configuration configuration single
  have observed := observed_runs_iff program qualified (fun term => term = value) initial
  obtain ⟨after, steps, same⟩ := observed.mpr ⟨run, value, represented, rfl⟩
  exact same ▸ steps

theorem run_keeps_type {configuration : ComputationProfile.Configuration (S := S)}
    (single : configuration.state.present = {configuration.active})
    (run : (restricted program qualified).Run configuration.state)
    {value : Tm Head configuration.state.frame.arity}
    (represented : Represents (S := S) value run.last) :
    Typed S.R configuration.state.frame.raw value (configuration.state.label configuration.active).1.code ∧
      Equal S.R configuration.state.frame.raw configuration.code value
        (configuration.state.label configuration.active).1.code :=
  qualified.subjectReduction configuration.state.frame.formed
    (DirectedAnswers.stepStar_of_reducesStar (run_reduces program qualified single run represented))
    (configuration.state.label configuration.active).2.typed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Directed

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Directed.toFullProgramRun_word
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Directed.run_reduces
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Directed.run_keeps_type
