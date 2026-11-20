import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.MachineProgressReflection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ExecutionControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Controls.ConvertibleArguments

/-! # A finite normal rejection and an actual answering computation with a diverging choice -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.MachineProgressControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open NativeTypesOnTheStep.Computing
open ExecutionControls

theorem normal_identity_finishes_all_internal_work :
    ContextProgress.Terminates built (queryCode identity) :=
  MachineProgress.evaluate_normalizes built identity
    (.intro identity fun output step => False.elim (identity_normal output step))

theorem value_reachability_is_not_a_progress_license :
    RuleInstances.Steps built.rules (queryCode Controls.ConvertibleArguments.delayedZero)
      (doneC (encodeTm (TowerVectorsModel.zeroC : Tower.Tm 0))) ∧
    ¬ ContextProgress.Terminates built (queryCode Controls.ConvertibleArguments.delayedZero) := by
  refine ⟨Completeness.value_reached built
    (.single (Controls.ConvertibleArguments.delayed_reduces_zero _)) .zero, ?_⟩
  intro terminates
  have source := MachineProgress.normalization_reflected built _ terminates
  have infinite : ¬ Acc (fun after before : Tower.Tm 0 => StrongNormalization.Reduces
      (Definitions.devPackage [] built.nativeRows) before after) Controls.ConvertibleArguments.delayedZero :=
    not_acc_iff_exists_descending_chain.mpr
      ⟨fun _ => Controls.ConvertibleArguments.delayedZero, rfl,
        fun _ => Controls.ConvertibleArguments.delayed_self_step _⟩
  exact infinite source

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.MachineProgressControls
