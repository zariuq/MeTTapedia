import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.StepRewrites
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.DriverRewrites

/-!
# Native value-reaching executions are implemented by the finite source program

This direction does not assume strong normalization of the input or choose a
complete by-value strategy. Each actual directed reduction has an executable
source route. Reverse successful-trace interpretation is a separate theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.Completeness

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing
open RuleInstances

variable {dev : Definitions.Development} (built : Compiled dev)

theorem driver_member {rule : ProgramBinders.Equation MSig [] ()} (member : rule ∈ ContextRules.driver) :
    rule ∈ built.rules := RootRewrites.fixed_member built (by simp [ContextRules.fixed, member])

theorem evaluate_step {n : Nat} {before after : Tower.Tm n}
    (step : StrongNormalization.Reduces (Definitions.devPackage dev built.nativeRows) before after)
    (continuation : MClosed) :
    Steps built.rules (evaluateC (encodeTm before) continuation) (evaluateC (encodeTm after) continuation) :=
  (Relation.ReflTransGen.single (DriverRewrites.evaluate_seek (fun _ member => driver_member built member)
    (encodeTm before) continuation)).trans
    ((StepRewrites.directed_step built step (nodeC "hd-main-eval-next" [continuation])).trans
      (Relation.ReflTransGen.single (DriverRewrites.evaluate_next (fun _ member => driver_member built member) (encodeTm after) continuation)))

theorem evaluate_steps {n : Nat} {before after : Tower.Tm n}
    (steps : StrongNormalization.ReducesStar (Definitions.devPackage dev built.nativeRows) before after)
    (continuation : MClosed) :
    Steps built.rules (evaluateC (encodeTm before) continuation) (evaluateC (encodeTm after) continuation) := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact ih.trans (evaluate_step built step continuation)

theorem value_reached {before value : Tower.Tm 0}
    (steps : StrongNormalization.ReducesStar (Definitions.devPackage dev built.nativeRows) before value)
    (isValue : DirectedAnswers.Value value) : Steps built.rules (queryCode before) (doneC (encodeTm value)) :=
  (evaluate_steps built steps finishContinuation).trans
    ((Relation.ReflTransGen.single (DriverRewrites.evaluate_value (fun _ member => driver_member built member)
      (encodeTm value) finishContinuation)).trans
      ((DriverRewrites.value_runs (fun _ member => driver_member built member) isValue finishContinuation).trans
        (Relation.ReflTransGen.single (DriverRewrites.finish (fun _ member => driver_member built member) (encodeTm value)))))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.Completeness
