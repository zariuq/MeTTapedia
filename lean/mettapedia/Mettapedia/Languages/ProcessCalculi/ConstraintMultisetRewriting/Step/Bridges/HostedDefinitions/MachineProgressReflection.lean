import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.MachineProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.Completeness
import Mathlib.Order.WellFounded

/-! # Positive compiled reduction blocks also reflect closed-machine normalization -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.MachineProgress

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing
open ContextProgress (Terminates)

theorem positive_block {dev : Definitions.Development} (built : Compiled dev) {before after : Tower.Tm 0}
    (step : StrongNormalization.Reduces (Definitions.devPackage dev built.nativeRows) before after) :
    Relation.TransGen (ProgramBinders.Rewrites built.rules.get) (queryCode before) (queryCode after) := by
  have starts := DriverRewrites.evaluate_seek
    (fun _ member => Completeness.driver_member built member) (encodeTm before) finishContinuation
  have middle := StepRewrites.directed_step built step (nodeC "hd-main-eval-next" [finishContinuation])
  have last := DriverRewrites.evaluate_next
    (fun _ member => Completeness.driver_member built member) (encodeTm after) finishContinuation
  exact Relation.TransGen.head' starts (middle.tail last)

theorem normalization_reflected {dev : Definitions.Development} (built : Compiled dev)
    (term : Tower.Tm 0) (target : Terminates built (queryCode term)) :
    Acc (fun after before => StrongNormalization.Reduces
      (Definitions.devPackage dev built.nativeRows) before after) term := by
  have transfer : ∀ current,
      Acc (Relation.TransGen (fun after before => ProgramBinders.Rewrites built.rules.get before after)) current →
      ∀ term : Tower.Tm 0, current = queryCode term →
        Acc (fun after before => StrongNormalization.Reduces
          (Definitions.devPackage dev built.nativeRows) before after) term := by
    intro current accessible
    induction accessible with
    | intro current _ ih =>
        intro term represented
        refine .intro term ?_
        intro after reduced
        have descent : Relation.TransGen (fun after before => ProgramBinders.Rewrites built.rules.get before after)
            (queryCode after) current := by
          rw [represented]
          exact Relation.transGen_swap.mpr (positive_block built reduced)
        exact ih (queryCode after) descent after rfl
  exact transfer _ target.transGen term rfl

theorem normalization_iff {dev : Definitions.Development} (built : Compiled dev) (term : Tower.Tm 0) :
    Terminates built (queryCode term) ↔
      Acc (fun after before => StrongNormalization.Reduces
        (Definitions.devPackage dev built.nativeRows) before after) term :=
  ⟨normalization_reflected built term, evaluate_normalizes built term⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.MachineProgress
