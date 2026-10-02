import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RuntimePathRefinement
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.AtomicResourceJoin
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationNormalization

/-!
# Funded events survive in the retained occurrence frame

The successor of an actual runtime firing retains every unselected source
occurrence. A second funded event whose endpoints and purse occurrences fit
that retained frame is therefore still enabled. The existing executable
completeness theorem constructs its actual catalogue candidate, preserving
its exact location and spend. This is an occurrence-resource condition;
equality of structural observations alone is not used to infer a step.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

theorem TraceComponentsCanonical.encodingCanonical
    {components : List RawTraceComponent} (canonical : TraceComponentsCanonical components) :
    (components.map RawTraceComponent.term).Forall RawCostTerm.EncodingCanonical := by
  apply canonical.normalized.imp
  intro term normalized
  exact normalized ▸ RawCostTerm.normalize_encodingCanonical term

/-- The entire decoded unselected frame occurs in the actual successor with
its original multiplicities. Produced code and purse tails only add terms. -/
theorem applyTracedStep_retained_le (components : List RawTraceComponent)
    (first : RawRuntimeStep) (eventId : Nat) :
    decodeRawConfig (eraseIndices (components.map RawTraceComponent.term)
        (first.participantIndices ++ first.selectedPurses.map RawIndexedPurse.index)) ≤
      decodeRawConfig ((applyTracedStep components first eventId).map RawTraceComponent.term) := by
  rw [applyTracedStep_terms, decodeRawConfig_stableKeySort,
    decodeRawConfig_append, decodeRawConfig_append]
  exact le_trans (Multiset.le_add_right _ _) (Multiset.le_add_right _ _)

/-- A funded event contained in the retained occurrence frame remains an
ordinary CostStep, with its original location and exact debit. -/
theorem CostedEvent.step_after_retained_frame
    (components : List RawTraceComponent) (first : RawRuntimeStep) (eventId : Nat)
    (event : CostedEvent String)
    (independent : event.consumed ≤ decodeRawConfig
      (eraseIndices (components.map RawTraceComponent.term)
        (first.participantIndices ++ first.selectedPurses.map RawIndexedPurse.index))) :
    CostStep
      (decodeRawConfig ((applyTracedStep components first eventId).map RawTraceComponent.term))
      event.location event.spend
      (decodeRawConfig ((applyTracedStep components first eventId).map RawTraceComponent.term) -
        event.consumed + event.produced) := by
  have fits := independent.trans (applyTracedStep_retained_le components first eventId)
  have step := event.toCostStepIn
    (decodeRawConfig ((applyTracedStep components first eventId).map RawTraceComponent.term) - event.consumed)
  rw [tsub_add_cancel_of_le fits] at step
  exact step

/-- Actual executable continuation is supplied by catalogue completeness,
not by evaluating the literal key or assuming an observation congruence. -/
theorem CostedEvent.runtime_after_retained_frame
    {components : List RawTraceComponent} {first : RawRuntimeStep}
    (canonical : TraceComponentsCanonical components)
    (supported : TraceComponentsWellFormed components)
    (enabled : first ∈ runtimeCostCandidatesFromConfig (components.map RawTraceComponent.term))
    (eventId : Nat) (event : CostedEvent String)
    (independent : event.consumed ≤ decodeRawConfig
      (eraseIndices (components.map RawTraceComponent.term)
        (first.participantIndices ++ first.selectedPurses.map RawIndexedPurse.index))) :
    RuntimeCostStepComplete
      ((applyTracedStep components first eventId).map RawTraceComponent.term)
      event.location event.spend
      (decodeRawConfig ((applyTracedStep components first eventId).map RawTraceComponent.term) -
        event.consumed + event.produced) := by
  have nextCanonical := applyTracedStep_canonical canonical enabled eventId
  exact costStep_complete_runtime_up_to_struct nextCanonical.rawConfig
    nextCanonical.encodingCanonical
    (applyTracedStep_wellFormed supported enabled eventId).toConfig
    (event.step_after_retained_frame components first eventId independent)

/-- Both firings are members of the real executable catalogue. The second
firing receives a fresh event ID and retains its exact requested labels. -/
theorem CostedEvent.two_firing_path_after_retained_frame
    {components : List RawTraceComponent} {first : RawRuntimeStep} {eventId : Nat}
    (canonical : TraceComponentsCanonical components)
    (supported : TraceComponentsWellFormed components)
    (bounded : TraceComponentsBefore eventId components)
    (enabled : first ∈ runtimeCostCandidatesFromConfig (components.map RawTraceComponent.term))
    (event : CostedEvent String)
    (independent : event.consumed ≤ decodeRawConfig
      (eraseIndices (components.map RawTraceComponent.term)
        (first.participantIndices ++ first.selectedPurses.map RawIndexedPurse.index))) :
    ∃ second,
      second ∈ runtimeCostCandidatesFromConfig
        ((applyTracedStep components first eventId).map RawTraceComponent.term) ∧
      decodeCostName second.location = event.location ∧
      decodeCostSig second.spend = event.spend ∧
      second.FrameExactFor ((applyTracedStep components first eventId).map RawTraceComponent.term) ∧
      ∃ path : CostPath eventId components (eventId + 1 + 1)
          (applyTracedStep (applyTracedStep components first eventId) second (eventId + 1)),
        path.depth = 2 ∧ path.steps = [first, second] := by
  obtain ⟨second, secondEnabled, located, spent, _represented, frame⟩ :=
    event.runtime_after_retained_frame canonical supported enabled eventId independent
  have nextSupported := applyTracedStep_wellFormed supported enabled eventId
  have nextBounded := applyTracedStep_before bounded first
  let path : CostPath eventId components (eventId + 1 + 1)
      (applyTracedStep (applyTracedStep components first eventId) second (eventId + 1)) :=
    .fire supported bounded first enabled
      (.fire nextSupported nextBounded second secondEnabled
        (.done (applyTracedStep_wellFormed nextSupported secondEnabled (eventId + 1))
          (applyTracedStep_before nextBounded second)))
  exact ⟨second, secondEnabled, located, spent, frame, path, rfl, rfl⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
