import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ValueProgramRuns

/-!
# Executions and boundaries of the compiled value worker

Pairs of data values succeed in the actual containing program. Pi terms are
outside this worker's value grammar and require the general-normal-form
extension. A forged private return frame can rewrite arbitrary data, showing
why an initialized call invariant is necessary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueWorkerControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Normalization
open SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing
open RuleBuilder

abbrev exampleValue : Tower.Tm 0 :=
  .pair TowerVectorsModel.zeroC (TowerVectorsModel.succC TowerVectorsModel.zeroC)

theorem pair_executes {dev : Definitions.Development} (built : Compiled dev) :
    RuleInstances.Steps built.rules (valueC (encodeTm exampleValue) finishContinuation)
      (doneC (encodeTm exampleValue)) :=
  (ValueWorker.compiled_success_iff built _ _).mpr
    ⟨rfl, exampleValue, .pair .zero (.succ .zero), rfl⟩

abbrev piTerm : Tower.Tm 0 := .pi (.const .anonymous) (.const .anonymous)

theorem pi_is_not_a_data_value : ¬ DirectedAnswers.Value piTerm := by
  intro value
  cases value

theorem pi_not_accepted_by_worker {dev : Definitions.Development} (built : Compiled dev)
    (result : MClosed) :
    ¬ RuleInstances.Steps built.rules (valueC (encodeTm piTerm) finishContinuation) (doneC result) := by
  intro run
  obtain ⟨same, value, isValue, encoded⟩ := ValueWorker.compiled_success_reflects built _ _ run
  have equal : piTerm = value := encodeTm_injective (same.symm.trans encoded)
  subst value
  exact pi_is_not_a_data_value isValue

theorem forged_internal_frame_rewrites (datum : MClosed) :
    ValueWorker.Step (resumeC datum (nodeC "hd-main-value-succ" [finishContinuation]))
      (resumeC (ValueContinuation.successor datum) finishContinuation) := by
  have step := RuleInstances.template (rows := ValueWorker.rules)
    (ContextRules.active (n := 2) "hd-resume" [slot 0, node "hd-main-value-succ" [slot 1]])
    (ContextRules.active "hd-resume"
      [node "prime-tm-app" [literal (encodeTm (.const TowerNumbersModel.succ : Tower.Tm 0)), slot 0], slot 1])
    (List.get_mem ValueWorker.rules ⟨3, by decide⟩) ![datum, finishContinuation]
  simpa [resumeC, activeC, ContextRules.active, ValueContinuation.successor] using step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueWorkerControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueWorkerControls.pair_executes
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueWorkerControls.pi_not_accepted_by_worker
