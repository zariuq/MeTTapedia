import Mettapedia.Languages.Metamath.MM2AssembledNormalExecutionCore
import Mettapedia.Languages.Metamath.MM2TransformationCanary
import Mettapedia.Languages.ProcessCalculi.MORK.CheckedAtomReplay

/-!
# Kernel-checked examples of assembled normal-proof execution

This optional audit module specializes the reusable theory in
`MM2AssembledNormalExecutionCore` to finite emitted programs.  It retains the
direct-import API for these examples and their checked replay certificates;
routine theory clients can import Core without replaying the examples.

The positive hypothesis and assertion examples run the actual normal machine
with source-derived scope rows and dynamic proof rows.  Their severed-source
controls retain the same submitted proof but remove its authorizing rows.
The ordered theorem example reaches proof-qualified action release, not
source-state admission; the conditional-availability example checks that this
slice cannot publish a failed earlier theorem.
-/

namespace Mettapedia.Languages.Metamath.MM2AssembledNormalExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2OrderedEventVerifier
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable
open Mettapedia.Languages.Metamath.MM2TransformationCanary
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.Metamath.SourceInferenceProjection

/-! ## Active-hypothesis calibration -/

theorem hypothesisCanaryProgram_nodup : hypothesisCanaryProgram.Nodup := by
  decide +kernel

theorem hypothesisCanaryProgram_supported_directives :
    cSupportedSourceExecFacts hypothesisCanaryProgram =
      normalProofMachineDirectives := by
  decide +kernel

theorem hypothesisCanaryProgram_raw_facts :
    cRawExecFacts hypothesisCanaryProgram = normalProofMachineRawFacts := by
  decide +kernel

/-- The actual assembled initial program, not a curated single-phase space,
satisfies the complete executable-to-authored realization invariant. -/
theorem hypothesisCanaryProgram_reflective_invariant :
    ReflectiveWorkQueueInvariant hypothesisCanaryProgram := by
  apply normalProofMachine_reflective_invariant hypothesisCanaryProgram
    hypothesisCanaryProgram_nodup
  · rw [hypothesisCanaryProgram_supported_directives]
    exact fun _ member => member
  · rw [hypothesisCanaryProgram_raw_facts]
    exact fun _ member => member

/-! ## Replay specifications for the two authored inventories -/

private def normalReplaySpec : CheckedAtomReplay.Spec where
  step := cReflectiveSourceWorkQueueStep .leaveInert
  run := cReflectiveSourceWorkQueueRunN .leaveInert
  runZero := by intro space; rfl
  runStep := by
    intro fuel used space next final moved tail
    simp only [cReflectiveSourceWorkQueueRunN, moved, tail]
  runStop := by
    intro space stop fuel
    cases fuel <;> simp only [cReflectiveSourceWorkQueueRunN, stop]
  check := normalProofMachineInvariantCheck
  checkRun := normalProofMachineRunInvariantCheck
  checkZero := by intro space here; exact here
  checkStep := by
    intro fuel space next here moved tail
    simp only [normalProofMachineRunInvariantCheck, here, moved, tail, Bool.true_and]
  checkStop := by
    intro space here stop fuel
    cases fuel <;> simp only [normalProofMachineRunInvariantCheck, here, stop, Bool.true_and]

private def authoredReplaySpec : CheckedAtomReplay.Spec where
  step := cReflectiveSourceWorkQueueStep .leaveInert
  run := cReflectiveSourceWorkQueueRunN .leaveInert
  runZero := by intro space; rfl
  runStep := by
    intro fuel used space next final moved tail
    simp only [cReflectiveSourceWorkQueueRunN, moved, tail]
  runStop := by
    intro space stop fuel
    cases fuel <;> simp only [cReflectiveSourceWorkQueueRunN, stop]
  check := authoredNormalVerifierInvariantCheck
  checkRun := authoredNormalVerifierRunInvariantCheck
  checkZero := by intro space here; exact here
  checkStep := by
    intro fuel space next here moved tail
    simp only [authoredNormalVerifierRunInvariantCheck, here, moved, tail, Bool.true_and]
  checkStop := by
    intro space here stop fuel
    cases fuel <;> simp only [authoredNormalVerifierRunInvariantCheck, here, stop, Bool.true_and]

/-! ## Continuous hypothesis execution and its severed-source control -/

set_option maxHeartbeats 0 in
kernel_atom_replay hypothesisReplay using normalReplaySpec for 35 from hypothesisCanaryProgram

theorem hypothesisCanary_run_invariant_check :
    normalProofMachineRunInvariantCheck 35 hypothesisCanaryProgram = true := by
  exact hypothesisReplay.invariant

/-- The entire positive hypothesis canary is now one continuous concrete run
whose every transition realizes an authored support-valued MM2 step. -/
def hypothesisCanary_adequateTrace :
    CReflectiveAdequateTrace .leaveInert 35 hypothesisCanaryProgram
      (cReflectiveSourceWorkQueueRunN .leaveInert 35
        hypothesisCanaryProgram).1 :=
  normalProofMachineAdequateTraceOfCheck 35 hypothesisCanaryProgram
    hypothesisCanary_run_invariant_check

def hypothesisCanary_supportNativeTypeTrace :
    ReflectiveSupportNativeTypeTrace .leaveInert
      hypothesisCanaryProgram.toFinset
      (cReflectiveSourceWorkQueueRunN .leaveInert 35
        hypothesisCanaryProgram).1.toFinset :=
  hypothesisCanary_adequateTrace.toSupportNativeTypeTrace

/-- The smallest admitted active-hypothesis proof reaches its exact terminal
observation in the real assembled space. -/
theorem hypothesisCanary_target_accepts :
    TargetAcceptsWithin hypothesisCanaryProgram acceptedFact 35 := by
  unfold TargetAcceptsWithin
  rw [hypothesisReplay.run]
  decide +kernel

/-- The positive canary therefore has an explicit continuous target run from
the emitted invocation program to a state containing acceptance. -/
theorem hypothesisCanary_has_reachable_terminal :
    ∃ final,
      CReflectiveReachable .leaveInert 35 hypothesisCanaryProgram final ∧
        acceptedFact ∈ final :=
  targetAcceptsWithin_has_reachable_terminal hypothesisCanary_target_accepts

/-- The same assembled positive run is classified step-by-step by OSLF over
the direct executable realization. -/
def hypothesisCanary_nativeTypeTraceWitness :
    TargetNativeTypeTraceWitness hypothesisCanaryProgram acceptedFact 35 :=
  targetAcceptsWithin_nativeTypeTraceWitness hypothesisCanary_target_accepts

set_option maxHeartbeats 0 in
kernel_atom_run severedHypothesisReplay using normalReplaySpec for 35 from severedProgram

/-- Removing the source hypothesis row while retaining the identical dynamic
proof input cannot manufacture the terminal observation. -/
theorem severedHypothesisCanary_does_not_accept :
    ¬ TargetAcceptsWithin severedProgram acceptedFact 35 := by
  unfold TargetAcceptsWithin
  rw [severedHypothesisReplay.run]
  decide +kernel

/-! ## One assembled assertion application -/

set_option maxHeartbeats 0 in
kernel_atom_replay assertionReplay using normalReplaySpec for 160 from assertionCanaryProgram

/-- The bounded assertion canary executes one hypothesis step and one genuine
assertion application in the same assembled program.  In particular, the
assertion phases consume the stack cell produced by the preceding hypothesis
step; no phase-local space is reconstructed between them. -/
theorem assertionCanary_target_accepts :
    TargetAcceptsWithin assertionCanaryProgram assertionAcceptedFact 160 := by
  unfold TargetAcceptsWithin
  rw [assertionReplay.run]
  decide +kernel

/-- The same 160-step assembled assertion run retains duplicate freedom and
the exact generated-exec whitelist at every visited state.  This is a finite,
replayable instance of the source-relative closure obligation; it does not
claim that hostile spaces containing forged verifier-internal rows are safe. -/
theorem assertionCanary_run_invariant_check :
    normalProofMachineRunInvariantCheck 160 assertionCanaryProgram = true := by
  exact assertionReplay.invariant

/-- The complete assertion canary is one continuous concrete run adequate to
the authored support-valued MM2 GSLT, including the intermediate stack cell
produced by the hypothesis phase and consumed by the assertion phases. -/
def assertionCanary_adequateTrace :
    CReflectiveAdequateTrace .leaveInert 160 assertionCanaryProgram
      (cReflectiveSourceWorkQueueRunN .leaveInert 160
        assertionCanaryProgram).1 :=
  normalProofMachineAdequateTraceOfCheck 160 assertionCanaryProgram
    assertionCanary_run_invariant_check

def assertionCanary_supportNativeTypeTrace :
    ReflectiveSupportNativeTypeTrace .leaveInert
      assertionCanaryProgram.toFinset
      (cReflectiveSourceWorkQueueRunN .leaveInert 160
        assertionCanaryProgram).1.toFinset :=
  assertionCanary_adequateTrace.toSupportNativeTypeTrace

/-- The assertion canary therefore supplies one concrete state-threaded run
through the assembled normal verifier, including terminal acceptance. -/
theorem assertionCanary_has_reachable_terminal :
    ∃ final,
      CReflectiveReachable .leaveInert 160 assertionCanaryProgram final ∧
        assertionAcceptedFact ∈ final :=
  targetAcceptsWithin_has_reachable_terminal assertionCanary_target_accepts

/-- The multi-phase assertion run is one OSLF-classified executable trace,
not a conjunction of singleton phase spaces. -/
def assertionCanary_nativeTypeTraceWitness :
    TargetNativeTypeTraceWitness assertionCanaryProgram assertionAcceptedFact
      160 :=
  targetAcceptsWithin_nativeTypeTraceWitness assertionCanary_target_accepts

set_option maxHeartbeats 0 in
kernel_atom_run severedAssertionReplay using normalReplaySpec for 160 from assertionSeveredProgram

/-- Removing the assertion lookup and execution rows while keeping the same
hypothesis and submitted proof cannot manufacture assertion acceptance. -/
theorem severedAssertionCanary_does_not_accept :
    ¬ TargetAcceptsWithin assertionSeveredProgram assertionAcceptedFact 160 := by
  unfold TargetAcceptsWithin
  rw [severedAssertionReplay.run]
  decide +kernel

/-! ## Ordered theorem event joined to the normal machine -/

private def orderedJoinOwner : Atom := stringAtom "ordered-join-owner"

private def orderedJoinSpan : LocatedByteSpan :=
  ⟨"ordered-join.mm", 0, 1⟩

private def orderedJoinLabel : LocatedName :=
  ⟨orderedJoinSpan, "ordered-join-theorem"⟩

private def orderedJoinTypecode : LocatedName :=
  ⟨orderedJoinSpan, "wff"⟩

private def orderedJoinBody : List LocatedName :=
  [⟨orderedJoinSpan, "ph"⟩]

private def orderedJoinProof : ProofPayload :=
  .normal [⟨orderedJoinSpan, "wph"⟩]

private def orderedJoinStatement : RawStatement :=
  .provable orderedJoinSpan orderedJoinLabel orderedJoinTypecode
    orderedJoinBody orderedJoinProof orderedJoinSpan orderedJoinSpan

private def orderedJoinObligation : TheoremObligation where
  site := orderedJoinSpan
  label := orderedJoinLabel
  formula := hypothesisFormula
  proof := orderedJoinProof

/-- One exact ordered theorem event, its decoder-derived proof rows, the
database-independent generated verifier, and a source-derived hypothesis
calibration row coexist in one MM2 space.  No phase state is reconstructed. -/
noncomputable def orderedTheoremNormalJoinProgram : List Atom :=
  (transformNormalVerifierSlice authoredMetamathVerifierGSLT
      ordinaryMM2Target).program ++
    [sourceEventStartRow orderedJoinOwner] ++
    sourceEventRows orderedJoinOwner [orderedJoinStatement] ++
    [sourceEventEndRow orderedJoinOwner [orderedJoinStatement]] ++
    sourcePreparedTheoremRows orderedJoinOwner 0 1 orderedJoinStatement
      hypothesisCanaryState orderedJoinObligation ++
    hypothesisLookupRows orderedJoinOwner hypothesisCanaryState

def orderedJoinAdmission : Atom :=
  sourceTheoremAdmittedAtom orderedJoinOwner 0 orderedJoinStatement (natAtom 0)

def orderedJoinActionRelease : Atom :=
  sourceTheoremActionReleaseAtom orderedJoinOwner 0 1 orderedJoinStatement
    (natAtom 0)

set_option maxHeartbeats 0 in
kernel_atom_replay orderedJoinReplay using authoredReplaySpec for 70 from orderedTheoremNormalJoinProgram

theorem orderedTheoremNormalJoin_run_exact :
    cReflectiveSourceWorkQueueRunN .leaveInert 70
      orderedTheoremNormalJoinProgram = (orderedJoinReplay.final, 43) :=
  orderedJoinReplay.run

theorem orderedTheoremNormalJoin_stopped_at_release :
    cReflectiveSourceWorkQueueStep .leaveInert orderedJoinReplay.final = none := by
  decide +kernel

/-- The ordered dispatcher, prepared-row gate, normal hypothesis machine,
terminal bridge, and proof-qualified action release form one continuous run.
The subsequent source-state mutation stage is not part of this slice. -/
theorem orderedTheoremNormalJoin_target_releases_action :
    TargetAcceptsWithin orderedTheoremNormalJoinProgram orderedJoinActionRelease
      70 := by
  unfold TargetAcceptsWithin
  rw [orderedJoinReplay.run]
  decide +kernel

/-- Proof completion alone cannot publish admission at this slice boundary. -/
theorem orderedTheoremNormalJoin_does_not_admit :
    ¬ TargetAcceptsWithin orderedTheoremNormalJoinProgram orderedJoinAdmission
      70 := by
  unfold TargetAcceptsWithin
  rw [orderedJoinReplay.run]
  decide +kernel

/-- Every state visited by the ordered-event plus normal-proof canary retains
the exact executable inventory generated from the authored verifier slice. -/
theorem orderedTheoremNormalJoin_run_invariant_check :
    authoredNormalVerifierRunInvariantCheck 70
      orderedTheoremNormalJoinProgram = true := by
  exact orderedJoinReplay.invariant

/-- The ordered-event normal-proof slice is one state-threaded concrete run
adequate to the authored support-valued MM2 GSLT.  This joins source dispatch,
normal proof execution, terminal success, and action release without
reconstructing a phase-local space. -/
noncomputable def orderedTheoremNormalJoin_adequateTrace :
    CReflectiveAdequateTrace .leaveInert 70
      orderedTheoremNormalJoinProgram
      (cReflectiveSourceWorkQueueRunN .leaveInert 70
        orderedTheoremNormalJoinProgram).1 :=
  authoredNormalVerifierAdequateTraceOfCheck 70
    orderedTheoremNormalJoinProgram
    orderedTheoremNormalJoin_run_invariant_check

noncomputable def orderedTheoremNormalJoin_supportNativeTypeTrace :
    ReflectiveSupportNativeTypeTrace .leaveInert
      orderedTheoremNormalJoinProgram.toFinset
      (cReflectiveSourceWorkQueueRunN .leaveInert 70
        orderedTheoremNormalJoinProgram).1.toFinset :=
  orderedTheoremNormalJoin_adequateTrace.toSupportNativeTypeTrace

/-- Ordered source dispatch, normal proof execution, and proof-qualified
action release coexist in one OSLF-classified executable trace. -/
noncomputable def orderedTheoremNormalJoin_nativeTypeTraceWitness :
    TargetNativeTypeTraceWitness orderedTheoremNormalJoinProgram
      orderedJoinActionRelease 70 :=
  targetAcceptsWithin_nativeTypeTraceWitness
    orderedTheoremNormalJoin_target_releases_action

/-- Without the decoder-derived prepared theorem bundle, the same source
event, proof input, hypothesis lookup, and verifier rules cannot release its
post-proof action. -/
noncomputable def orderedTheoremNormalJoinWithoutPreparedProgram : List Atom :=
  (transformNormalVerifierSlice authoredMetamathVerifierGSLT
      ordinaryMM2Target).program ++
    [sourceEventStartRow orderedJoinOwner] ++
    sourceEventRows orderedJoinOwner [orderedJoinStatement] ++
    [sourceEventEndRow orderedJoinOwner [orderedJoinStatement]] ++
    proofInputRows orderedJoinOwner (sourceProofOwnerAtom orderedJoinOwner 0)
      (theoremObligationProofInput orderedJoinObligation) ++
    hypothesisLookupRows orderedJoinOwner hypothesisCanaryState

set_option maxHeartbeats 0 in
kernel_atom_run unpreparedOrderedJoinReplay using authoredReplaySpec for 70 from orderedTheoremNormalJoinWithoutPreparedProgram

theorem orderedTheoremNormalJoin_without_prepared_does_not_release_action :
    ¬ TargetAcceptsWithin orderedTheoremNormalJoinWithoutPreparedProgram
      orderedJoinActionRelease 70 := by
  unfold TargetAcceptsWithin
  rw [unpreparedOrderedJoinReplay.run]
  decide +kernel

theorem orderedTheoremNormalJoin_without_prepared_does_not_admit :
    ¬ TargetAcceptsWithin orderedTheoremNormalJoinWithoutPreparedProgram
      orderedJoinAdmission 70 := by
  unfold TargetAcceptsWithin
  rw [unpreparedOrderedJoinReplay.run]
  decide +kernel

/-! ## Conditional theorem availability -/

private def conditionalOwner : Atom := stringAtom "conditional-owner"

private def invalidFirstProof : ProofPayload :=
  .normal [⟨orderedJoinSpan, "?"⟩]

private def invalidFirstStatement : RawStatement :=
  .provable orderedJoinSpan ⟨orderedJoinSpan, "invalid-first"⟩
    orderedJoinTypecode orderedJoinBody invalidFirstProof orderedJoinSpan
    orderedJoinSpan

private def invalidFirstObligation : TheoremObligation where
  site := orderedJoinSpan
  label := ⟨orderedJoinSpan, "invalid-first"⟩
  formula := hypothesisFormula
  proof := invalidFirstProof

private def invalidFirstAssertion : SourceAssertion :=
  sourceAssertion hypothesisCanaryState "invalid-first" hypothesisFormula

private def stateAfterInvalidFirst : SourceState :=
  { hypothesisCanaryState with
    usedLabels := hypothesisCanaryState.usedLabels ++ ["invalid-first"]
    assertions := hypothesisCanaryState.assertions ++ [invalidFirstAssertion] }

private def laterReferenceProof : ProofPayload :=
  .normal
    [⟨orderedJoinSpan, "wph"⟩, ⟨orderedJoinSpan, "invalid-first"⟩]

private def laterReferenceStatement : RawStatement :=
  .provable orderedJoinSpan ⟨orderedJoinSpan, "later-reference"⟩
    orderedJoinTypecode orderedJoinBody laterReferenceProof orderedJoinSpan
    orderedJoinSpan

private def laterReferenceObligation : TheoremObligation where
  site := orderedJoinSpan
  label := ⟨orderedJoinSpan, "later-reference"⟩
  formula := hypothesisFormula
  proof := laterReferenceProof

private def conditionalStatements : List RawStatement :=
  [invalidFirstStatement, laterReferenceStatement]

/-- Both unresolved theorem bundles are present, including the later proof's
reference to the earlier label.  The earlier assertion header remains wrapped
and can be published only by its proof-success continuation. -/
noncomputable def invalidThenReferenceProgram : List Atom :=
  (transformNormalVerifierSlice authoredMetamathVerifierGSLT
      ordinaryMM2Target).program ++
    [sourceEventStartRow conditionalOwner] ++
    sourceEventRows conditionalOwner conditionalStatements ++
    [sourceEventEndRow conditionalOwner conditionalStatements] ++
    sourcePreparedTheoremRows conditionalOwner 0 1 invalidFirstStatement
      hypothesisCanaryState invalidFirstObligation ++
    sourcePreparedTheoremRows conditionalOwner 1 2 laterReferenceStatement
      stateAfterInvalidFirst laterReferenceObligation ++
    hypothesisLookupRows conditionalOwner hypothesisCanaryState

set_option maxHeartbeats 0 in
kernel_atom_run invalidThenReferenceReplay using authoredReplaySpec for 160 from invalidThenReferenceProgram

/-- An invalid earlier theorem cannot become executable merely because the
later theorem names it.  In the one assembled run, its assertion header is
never published, source control never advances to the later statement, and
the later statement never becomes current. -/
theorem invalid_earlier_theorem_cannot_authorize_later_reference :
    let final :=
      (cReflectiveSourceWorkQueueRunN .leaveInert 160
        invalidThenReferenceProgram).1
    assertionHeaderRow conditionalOwner 0 invalidFirstAssertion ∉ final ∧
      sourceControlAtom conditionalOwner 1 ∉ final ∧
      sourceCurrentAtom conditionalOwner 1 2 laterReferenceStatement ∉ final := by
  simp only [invalidThenReferenceReplay.run]
  decide +kernel

#print axioms cReflectiveSourceWorkQueueRunN_reachable
#print axioms CReflectiveEventually.trans
#print axioms targetAcceptsWithin_has_reachable_terminal
#print axioms targetAcceptsWithin_has_eventual_terminal
#print axioms targetAcceptsWithin_nativeTypeTraceWitness
#print axioms hypothesisCanaryProgram_nodup
#print axioms hypothesisCanaryProgram_supported_directives
#print axioms hypothesisCanaryProgram_raw_facts
#print axioms hypothesisCanaryProgram_reflective_invariant
#print axioms normalProofMachineAdequateTraceOfCheck
#print axioms authoredNormalVerifierInvariantCheck_sound
#print axioms authoredNormalVerifierAdequateTraceOfCheck
#print axioms hypothesisCanary_run_invariant_check
#print axioms hypothesisCanary_adequateTrace
#print axioms hypothesisCanary_supportNativeTypeTrace
#print axioms normalHypothesisPhase_adequateTrace
#print axioms normalHypothesisPhase_supportNativeTypeTrace
#print axioms hypothesisCanary_target_accepts
#print axioms hypothesisCanary_has_reachable_terminal
#print axioms hypothesisCanary_nativeTypeTraceWitness
#print axioms severedHypothesisCanary_does_not_accept
#print axioms assertionCanary_target_accepts
#print axioms assertionCanary_run_invariant_check
#print axioms assertionCanary_adequateTrace
#print axioms assertionCanary_supportNativeTypeTrace
#print axioms assertionCanary_has_reachable_terminal
#print axioms assertionCanary_nativeTypeTraceWitness
#print axioms severedAssertionCanary_does_not_accept
#print axioms orderedTheoremNormalJoin_run_exact
#print axioms orderedTheoremNormalJoin_stopped_at_release
#print axioms orderedTheoremNormalJoin_target_releases_action
#print axioms orderedTheoremNormalJoin_does_not_admit
#print axioms orderedTheoremNormalJoin_run_invariant_check
#print axioms orderedTheoremNormalJoin_adequateTrace
#print axioms orderedTheoremNormalJoin_supportNativeTypeTrace
#print axioms orderedTheoremNormalJoin_nativeTypeTraceWitness
#print axioms orderedTheoremNormalJoin_without_prepared_does_not_release_action
#print axioms orderedTheoremNormalJoin_without_prepared_does_not_admit
#print axioms invalid_earlier_theorem_cannot_authorize_later_reference

end Mettapedia.Languages.Metamath.MM2AssembledNormalExecution
