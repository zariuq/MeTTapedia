import Mettapedia.GSLT.LanguageDef.M0GCCoreLoopCorrespondence

/-!
# Chronological proof-record replay machine for M0GC

This module exposes proof replay as a deterministic small-step machine.  Each
successful nonterminal transition checks exactly one proof record through the
shared `cCoreReplayRecord?` operation and advances the admitted prefix by that
record.  A terminal-observation theorem proves exact agreement with the
previous recursive proof-prefix checker on every input.

Maturity boundary: this is a fully connected intermediate proof of concept.
It removes the atomic whole-replay step, but the admitted prefix is still a
Lean `Array`; it is not yet a bounded mutable target store, optimized ABI,
Pancake or Clight program, verified object code, OS, or hardware model.  Those
later representations must refine this chronology rather than replace it with
an unconnected implementation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.M0GCRecordReplayControlMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.M0GCWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplay
open Mettapedia.GSLT.LanguageDef.M0GCPhysicalTemplateAdequacy
open Mettapedia.GSLT.LanguageDef.M0GCGeneratedProfileQualification
open Mettapedia.GSLT.LanguageDef.M0GCNativeReplayAdequacy
open Mettapedia.GSLT.LanguageDef.M0GCCoreLoopCorrespondence

/-! ## Small-step control -/

/-- Parameters fixed throughout one chronological replay. -/
structure Configuration where
  profile : RuntimeProfile
  tables : RuleTables
  certificate : Certificate
  terms : TermState
  replayFuel : Nat

/-- Running states retain the unvisited suffix and the already admitted
prefix.  A terminal state distinguishes rejection (`none`) from the exact
accepted prefix (`some prefix`). -/
inductive ControlState where
  | running (remaining : List ProofNode) (admitted : CProofPrefixState)
  | halt (result : Option CProofPrefixState)
deriving DecidableEq, Repr

/-- A terminal replay result is observable only after halting. -/
def observe : ControlState → Option (Option CProofPrefixState)
  | .running _ _ => none
  | .halt result => some result

/-- One chronological control transition.  The nonempty running case invokes
the shared checker for exactly the head proof record. -/
def step (configuration : Configuration) : ControlState → ControlState
  | .running [] admitted => .halt (some admitted)
  | .running (proof :: proofs) admitted =>
      match cCoreReplayRecord? configuration.profile configuration.tables
          configuration.certificate configuration.terms
          configuration.replayFuel admitted proof with
      | none => .halt none
      | some next => .running proofs next
  | .halt result => .halt result

/-- Relational presentation for backend simulations. -/
def Transition (configuration : Configuration)
    (before after : ControlState) : Prop :=
  step configuration before = after

theorem transition_deterministic
    (configuration : Configuration)
    {before afterLeft afterRight : ControlState}
    (left : Transition configuration before afterLeft)
    (right : Transition configuration before afterRight) :
    afterLeft = afterRight := by
  unfold Transition at left right
  rw [← left, ← right]

@[simp] theorem step_halt (configuration : Configuration)
    (result : Option CProofPrefixState) :
    step configuration (.halt result) = .halt result := rfl

/-- Execute a fixed number of chronological transitions. -/
def runSteps (configuration : Configuration) :
    Nat → ControlState → ControlState
  | 0, state => state
  | fuel + 1, state => runSteps configuration fuel (step configuration state)

@[simp] theorem runSteps_halt (configuration : Configuration)
    (fuel : Nat) (result : Option CProofPrefixState) :
    runSteps configuration fuel (.halt result) = .halt result := by
  induction fuel with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      simp [runSteps, inductionHypothesis]

/-! ## Exact agreement with recursive replay -/

/-- One transition per proof record plus one terminal transition is sufficient,
and its result is exactly the recursive proof-prefix replay result. -/
theorem runSteps_sufficient (configuration : Configuration)
    (proofs : List ProofNode) (admitted : CProofPrefixState) :
    runSteps configuration (proofs.length + 1) (.running proofs admitted) =
      .halt
        (cCoreReplayLoop configuration.profile configuration.tables
          configuration.certificate configuration.terms
          configuration.replayFuel proofs admitted) := by
  induction proofs generalizing admitted with
  | nil => rfl
  | cons proof proofs inductionHypothesis =>
      cases recordResult :
          cCoreReplayRecord? configuration.profile configuration.tables
            configuration.certificate configuration.terms
            configuration.replayFuel admitted proof with
      | none =>
          simp [runSteps, step, cCoreReplayLoop, recordResult]
      | some next =>
          simp [runSteps, step, cCoreReplayLoop, recordResult,
            inductionHypothesis]

/-- Execute the statically sufficient number of chronological transitions. -/
def execute (configuration : Configuration) (proofs : List ProofNode)
    (admitted : CProofPrefixState) : Option CProofPrefixState :=
  match runSteps configuration (proofs.length + 1)
      (.running proofs admitted) with
  | .halt result => result
  | .running _ _ => none

/-- The small-step machine neither accepts more nor rejects more than the
recursive proof-prefix checker. -/
theorem execute_eq_cCoreReplayLoop (configuration : Configuration)
    (proofs : List ProofNode) (admitted : CProofPrefixState) :
    execute configuration proofs admitted =
      cCoreReplayLoop configuration.profile configuration.tables
        configuration.certificate configuration.terms
        configuration.replayFuel proofs admitted := by
  unfold execute
  rw [runSteps_sufficient]

/-- Successful chronological replay simulates the independently qualified
native result-identifier replay. -/
theorem execute_simulates_native
    (configuration : Configuration) {proofs : List ProofNode}
    {admitted finalPrefix : CProofPrefixState}
    {native : NativeProofState}
    (relation : PrefixResultRelation admitted native)
    (accepted : execute configuration proofs admitted = some finalPrefix) :
    ∃ finalNative,
      nativeReplayLoop configuration.profile configuration.tables
          configuration.certificate configuration.terms
          configuration.replayFuel proofs native = some finalNative ∧
      PrefixResultRelation finalPrefix finalNative := by
  apply cCoreReplayLoop_simulates_native relation
  rw [← execute_eq_cCoreReplayLoop]
  exact accepted

/-- If the qualified native model rejects, chronological replay rejects too. -/
theorem execute_rejected_of_native_rejected
    (configuration : Configuration) {proofs : List ProofNode}
    {admitted : CProofPrefixState} {native : NativeProofState}
    (relation : PrefixResultRelation admitted native)
    (nativeRejected :
      nativeReplayLoop configuration.profile configuration.tables
          configuration.certificate configuration.terms
          configuration.replayFuel proofs native = none) :
    execute configuration proofs admitted = none := by
  rw [execute_eq_cCoreReplayLoop]
  exact cCoreReplayLoop_rejected_of_native_rejected relation nativeRejected

/-! ## Positive and negative discriminators -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplayCanary

def configuration : Configuration :=
  { profile
    tables := M0GCCoreLoopCorrespondence.Canary.tables
    certificate
    terms := termState
    replayFuel := M0GCCoreLoopCorrespondence.Canary.canaryFuel }

/-- Positive one-record discriminator: the pair rule advances the empty
prefix by exactly its proof record. -/
theorem pair_record_accepts :
    cCoreReplayRecord? profile M0GCCoreLoopCorrespondence.Canary.tables
        certificate termState M0GCCoreLoopCorrespondence.Canary.canaryFuel
        {} proofNode =
      some M0GCCoreLoopCorrespondence.Canary.acceptedState := by
  rw [cCoreReplayRecord?_of
    (rule := pairRuleProfile) (argumentIds := [0, 1])
    (premiseReferences := []) (premiseConcreteIds := [])
    (argumentPatterns :=
      [M0GCLogicalReplayCanary.left, M0GCLogicalReplayCanary.right])
    (conclusion := M0GCLogicalReplayCanary.pair)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by
      simpa [M0GCCoreLoopCorrespondence.Canary.tables,
          M0GCCoreLoopCorrespondence.Canary.canaryFuel,
          M0GCNativeReplayAdequacy.Canary.tables,
          M0GCNativeReplayAdequacy.Canary.canaryFuel, proofNode] using
        M0GCIdentifierMatcherAdequacy.Canary.pair_rule_identifier_match)]
  rfl

/-- The chronological machine accepts the same nontrivial singleton proof. -/
theorem pair_machine_accepts :
    execute configuration certificate.proofs {} =
      some M0GCCoreLoopCorrespondence.Canary.acceptedState := by
  rw [execute_eq_cCoreReplayLoop]
  exact M0GCCoreLoopCorrespondence.Canary.pair_core_loop_accepts

/-- Negative chronology discriminator: a proof cannot cite its own result
before that proof has been admitted. -/
theorem current_proof_machine_rejected :
    execute
        { configuration with
          profile := futurePremiseProfile
          certificate := futurePremiseCertificate }
        futurePremiseCertificate.proofs {} = none := by
  rw [execute_eq_cCoreReplayLoop]
  exact M0GCCoreLoopCorrespondence.Canary.current_proof_reference_rejected

end Canary

#print axioms transition_deterministic
#print axioms runSteps_sufficient
#print axioms execute_eq_cCoreReplayLoop
#print axioms execute_simulates_native
#print axioms execute_rejected_of_native_rejected
#print axioms Canary.pair_record_accepts
#print axioms Canary.pair_machine_accepts
#print axioms Canary.current_proof_machine_rejected

end Mettapedia.GSLT.LanguageDef.M0GCRecordReplayControlMachine
