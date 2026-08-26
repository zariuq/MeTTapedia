import Mettapedia.Languages.Metamath.MM2TransformationCanary

/-!
# Assembled normal-proof execution for the Metamath-to-MM2 transformation

The phase-local correspondence lemmas describe individual MM2 directives.
This module introduces the separate whole-program boundary: one finite MM2
space, one scheduler, and a state-threaded sequence in which every successor
is the next step's source.

The first closed instance is the active-hypothesis canary.  It runs the actual
database-independent normal machine together with source-derived scope rows
and dynamic proof rows.  The severed-source control executes the same proof
input without the authorizing hypothesis row and cannot produce acceptance.
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

/-- Exact target-side acceptance after at most `fuel` scheduler steps.  This
predicate contains no source proof tree or independent verifier result. -/
def TargetAcceptsWithin (program : List Atom) (accepted : Atom)
    (fuel : Nat) : Prop :=
  accepted ∈
    (cReflectiveSourceWorkQueueRunN .leaveInert fuel program).1

/-- Unbounded finite reachability for composition across proof-machine
macro-steps.  The witness retains the concrete step count, while clients do
not need to predict it before composing independently proved phases. -/
def CReflectiveEventually (policy : UnsupportedExecPolicy)
    (source target : List Atom) : Prop :=
  ∃ fuel, CReflectiveReachable policy fuel source target

theorem CReflectiveEventually.refl
    (policy : UnsupportedExecPolicy) (space : List Atom) :
    CReflectiveEventually policy space space :=
  ⟨0, .refl⟩

theorem CReflectiveEventually.step
    {policy : UnsupportedExecPolicy} {source middle target : List Atom}
    (step : cReflectiveSourceWorkQueueStep policy source = some middle)
    (tail : CReflectiveEventually policy middle target) :
    CReflectiveEventually policy source target := by
  rcases tail with ⟨fuel, tail⟩
  exact ⟨fuel + 1, .step step tail⟩

/-- Continuous assembled executions compose without rebuilding any
phase-local source state. -/
theorem CReflectiveEventually.trans
    {policy : UnsupportedExecPolicy} {source middle target : List Atom}
    (left : CReflectiveEventually policy source middle)
    (right : CReflectiveEventually policy middle target) :
    CReflectiveEventually policy source target := by
  rcases left with ⟨fuel, left⟩
  induction left with
  | refl => exact right
  | step step _ induction =>
      exact CReflectiveEventually.step step (induction right)

/-- The computable runner always supplies one genuine state-threaded path to
its returned state.  A stopped run uses `refl`; a live run records the exact
successor returned by the scheduler before continuing. -/
theorem cReflectiveSourceWorkQueueRunN_reachable
    (policy : UnsupportedExecPolicy) (fuel : Nat) (space : List Atom) :
    CReflectiveReachable policy fuel space
      (cReflectiveSourceWorkQueueRunN policy fuel space).1 := by
  induction fuel generalizing space with
  | zero => exact .refl
  | succ fuel induction =>
      simp only [cReflectiveSourceWorkQueueRunN]
      cases stepped : cReflectiveSourceWorkQueueStep policy space with
      | none => exact .refl
      | some next =>
          simp only
          exact .step stepped (induction next)

/-- Target acceptance is backed by one continuous run of the assembled
program; it is not a conjunction of separately constructed phase spaces. -/
theorem targetAcceptsWithin_has_reachable_terminal
    {program : List Atom} {accepted : Atom} {fuel : Nat}
    (accepts : TargetAcceptsWithin program accepted fuel) :
    ∃ final,
      CReflectiveReachable .leaveInert fuel program final ∧
        accepted ∈ final := by
  exact ⟨_, cReflectiveSourceWorkQueueRunN_reachable _ _ _, accepts⟩

theorem targetAcceptsWithin_has_eventual_terminal
    {program : List Atom} {accepted : Atom} {fuel : Nat}
    (accepts : TargetAcceptsWithin program accepted fuel) :
    ∃ final,
      CReflectiveEventually .leaveInert program final ∧
        accepted ∈ final := by
  rcases targetAcceptsWithin_has_reachable_terminal accepts with
    ⟨final, reachable, terminal⟩
  exact ⟨final, ⟨fuel, reachable⟩, terminal⟩

/-- Proof-relevant witness for a bounded target verdict.  The trace remains
data in `Type`; terminal membership is lifted rather than erasing the trace
behind proposition-level existence. -/
def TargetNativeTypeTraceWitness (program : List Atom) (accepted : Atom)
    (fuel : Nat) : Type :=
  Σ final : List Atom,
    ReflectiveNativeTypeTrace .leaveInert fuel program final ×
      PLift (accepted ∈ final)

/-- A bounded target verdict constructs one proof-relevant trace whose every
concrete list-machine step inhabits the exact native target type generated by
OSLF from that executable realization.  This is the actual assembled run,
not the phase-local proof family. -/
def targetAcceptsWithin_nativeTypeTraceWitness
    {program : List Atom} {accepted : Atom} {fuel : Nat}
    (accepts : TargetAcceptsWithin program accepted fuel) :
    TargetNativeTypeTraceWitness program accepted fuel :=
  ⟨_, cReflectiveSourceWorkQueueRunN_nativeTypeTrace
    .leaveInert fuel program, ⟨accepts⟩⟩

/-! ## First adequate concrete-to-authored induction case -/

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

/-- Replayable certificate that every state visited by a bounded normal-MM2
run satisfies the concrete-to-authored realization invariant. -/
def normalProofMachineRunInvariantCheck : Nat → List Atom → Bool
  | 0, space => normalProofMachineInvariantCheck space
  | fuel + 1, space =>
      normalProofMachineInvariantCheck space &&
        match cReflectiveSourceWorkQueueStep .leaveInert space with
        | none => true
        | some next => normalProofMachineRunInvariantCheck fuel next

/-- A successful bounded invariant certificate constructs one continuous,
proof-relevant adequate trace of the actual assembled queue execution. -/
def normalProofMachineAdequateTraceOfCheck
    (fuel : Nat) (source : List Atom)
    (accepted : normalProofMachineRunInvariantCheck fuel source = true) :
    CReflectiveAdequateTrace .leaveInert fuel source
      (cReflectiveSourceWorkQueueRunN .leaveInert fuel source).1 := by
  induction fuel generalizing source with
  | zero =>
      exact .refl
  | succ fuel induction =>
      rw [normalProofMachineRunInvariantCheck, Bool.and_eq_true] at accepted
      have currentInvariant :=
        normalProofMachineInvariantCheck_sound accepted.1
      simp only [cReflectiveSourceWorkQueueRunN]
      cases moved : cReflectiveSourceWorkQueueStep .leaveInert source with
      | none => exact .refl
      | some next =>
          simp only [moved] at accepted
          exact .step currentInvariant moved (induction next accepted.2)

theorem hypothesisCanary_run_invariant_check :
    normalProofMachineRunInvariantCheck 35 hypothesisCanaryProgram = true := by
  decide +kernel

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

/-- The generic active-hypothesis phase is one actual concrete scheduler
step carrying every obligation required to lift it to authored support-valued
MM2.  This is the first induction case for the eventual whole-proof adequacy
trace; it is stronger than merely observing that the phase fires. -/
def normalHypothesisPhase_adequateTrace
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackPosition nextStackPosition : Nat)
    (hypothesis : InferenceProjection.HypothesisView) :
    let atoms := normalHypothesisPhaseAtoms scopeOwner proofOwner proofPosition
      nextProofPosition stackPosition nextStackPosition hypothesis
    CReflectiveAdequateTrace .leaveInert 1 atoms
      (cFireReflectiveSourceExecFact atoms normalHypothesisDirective) := by
  let atoms := normalHypothesisPhaseAtoms scopeOwner proofOwner proofPosition
    nextProofPosition stackPosition nextStackPosition hypothesis
  exact .step
    (normalHypothesisPhase_reflective_invariant scopeOwner proofOwner
      proofPosition nextProofPosition stackPosition nextStackPosition
      hypothesis)
    (normalHypothesisPhase_cstep scopeOwner proofOwner proofPosition
      nextProofPosition stackPosition nextStackPosition hypothesis)
    .refl

/-- The same concrete hypothesis step is classified by OSLF over the authored
support-valued MM2 GSLT, with the concrete and authored successor supports
identified by the adequacy trace rather than by an assumed renderer. -/
def normalHypothesisPhase_supportNativeTypeTrace
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackPosition nextStackPosition : Nat)
    (hypothesis : InferenceProjection.HypothesisView) :
    let atoms := normalHypothesisPhaseAtoms scopeOwner proofOwner proofPosition
      nextProofPosition stackPosition nextStackPosition hypothesis
    ReflectiveSupportNativeTypeTrace .leaveInert atoms.toFinset
      (cFireReflectiveSourceExecFact atoms normalHypothesisDirective).toFinset :=
  (normalHypothesisPhase_adequateTrace scopeOwner proofOwner proofPosition
    nextProofPosition stackPosition nextStackPosition hypothesis).toSupportNativeTypeTrace

/-- The smallest admitted active-hypothesis proof reaches its exact terminal
observation in the real assembled space. -/
theorem hypothesisCanary_target_accepts :
    TargetAcceptsWithin hypothesisCanaryProgram acceptedFact 35 := by
  unfold TargetAcceptsWithin
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

/-- Removing the source hypothesis row while retaining the identical dynamic
proof input cannot manufacture the terminal observation. -/
theorem severedHypothesisCanary_does_not_accept :
    ¬ TargetAcceptsWithin severedProgram acceptedFact 35 := by
  unfold TargetAcceptsWithin
  decide +kernel

/-! ## One assembled assertion application -/

/-- The bounded assertion canary executes one hypothesis step and one genuine
assertion application in the same assembled program.  In particular, the
assertion phases consume the stack cell produced by the preceding hypothesis
step; no phase-local space is reconstructed between them. -/
theorem assertionCanary_target_accepts :
    TargetAcceptsWithin assertionCanaryProgram assertionAcceptedFact 160 := by
  unfold TargetAcceptsWithin
  decide +kernel

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

/-- Removing the assertion lookup and execution rows while keeping the same
hypothesis and submitted proof cannot manufacture assertion acceptance. -/
theorem severedAssertionCanary_does_not_accept :
    ¬ TargetAcceptsWithin assertionSeveredProgram assertionAcceptedFact 160 := by
  unfold TargetAcceptsWithin
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

/-- The ordered dispatcher, prepared-row gate, normal hypothesis machine,
terminal bridge, and conditional commit form one continuous scheduled run. -/
theorem orderedTheoremNormalJoin_target_admits :
    TargetAcceptsWithin orderedTheoremNormalJoinProgram orderedJoinAdmission
      70 := by
  unfold TargetAcceptsWithin
  decide +kernel

/-- Ordered source dispatch, normal proof execution, and conditional theorem
commit coexist in one OSLF-classified executable trace. -/
noncomputable def orderedTheoremNormalJoin_nativeTypeTraceWitness :
    TargetNativeTypeTraceWitness orderedTheoremNormalJoinProgram
      orderedJoinAdmission 70 :=
  targetAcceptsWithin_nativeTypeTraceWitness
    orderedTheoremNormalJoin_target_admits

/-- Removing only the decoder-derived prepared row leaves the same source
event, proof rows, hypothesis lookup, and verifier rules, but cannot admit the
theorem. -/
noncomputable def orderedTheoremNormalJoinWithoutPreparedProgram : List Atom :=
  (transformNormalVerifierSlice authoredMetamathVerifierGSLT
      ordinaryMM2Target).program ++
    [sourceEventStartRow orderedJoinOwner] ++
    sourceEventRows orderedJoinOwner [orderedJoinStatement] ++
    [sourceEventEndRow orderedJoinOwner [orderedJoinStatement]] ++
    proofInputRows orderedJoinOwner (sourceProofOwnerAtom orderedJoinOwner 0)
      (theoremObligationProofInput orderedJoinObligation) ++
    hypothesisLookupRows orderedJoinOwner hypothesisCanaryState

theorem orderedTheoremNormalJoin_without_prepared_does_not_admit :
    ¬ TargetAcceptsWithin orderedTheoremNormalJoinWithoutPreparedProgram
      orderedJoinAdmission 70 := by
  unfold TargetAcceptsWithin
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
#print axioms assertionCanary_has_reachable_terminal
#print axioms assertionCanary_nativeTypeTraceWitness
#print axioms severedAssertionCanary_does_not_accept
#print axioms orderedTheoremNormalJoin_target_admits
#print axioms orderedTheoremNormalJoin_nativeTypeTraceWitness
#print axioms orderedTheoremNormalJoin_without_prepared_does_not_admit
#print axioms invalid_earlier_theorem_cannot_authorize_later_reference

end Mettapedia.Languages.Metamath.MM2AssembledNormalExecution
