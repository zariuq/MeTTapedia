import Mettapedia.Languages.Metamath.MM2Transformation

/-!
# Compositional theory for assembled normal-proof execution

This module relates one state-threaded MM2 scheduler run to its reachable
states, authored support-valued semantics, and OSLF-generated native types.
Bounded target acceptance yields a concrete terminal witness; finite
reachability composes independently proved phases without reconstructing
their intermediate spaces.

Replayable invariant checks supply the concrete-to-authored adequacy
obligation at every visited state.  Their successful certificates construct
adequate traces, which transport to support-valued native type traces.  The
generic active-hypothesis phase provides a one-step instance of this transport.

These results concern the currently authored normal-verifier slice.  They
do not assert invariant preservation for arbitrary hostile spaces or a
complete Metamath verifier theorem.  Closed execution examples and their
kernel replay certificates are in `MM2AssembledNormalExecution`.
-/

namespace Mettapedia.Languages.Metamath.MM2AssembledNormalExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-! ## Bounded acceptance and compositional reachability -/

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

/-! ## Invariant certificates and concrete-to-authored adequacy -/

/-- Replayable certificate that every state visited by a bounded normal-MM2
run satisfies the concrete-to-authored realization invariant. -/
def normalProofMachineRunInvariantCheck : Nat → List Atom → Bool
  | 0, space => normalProofMachineInvariantCheck space
  | fuel + 1, space =>
      normalProofMachineInvariantCheck space &&
        match cReflectiveSourceWorkQueueStep .leaveInert space with
        | none => true
        | some next => normalProofMachineRunInvariantCheck fuel next

/-- Replayable invariant for the complete currently authored verifier slice:
the ordered event prelude and the normal proof machine share one scheduler and
one emitted rule inventory. -/
def authoredNormalVerifierInvariantCheck (space : List Atom) : Bool :=
  decide space.Nodup &&
    (cRawExecFacts space).all (fun raw =>
      decide (raw ∈ authoredNormalVerifierRawFacts))

theorem authoredNormalVerifierInvariantCheck_sound
    {space : List Atom}
    (accepted : authoredNormalVerifierInvariantCheck space = true) :
    ReflectiveWorkQueueInvariant space := by
  simp only [authoredNormalVerifierInvariantCheck, Bool.and_eq_true,
    List.all_eq_true, decide_eq_true_eq] at accepted
  exact authoredNormalVerifier_reflective_invariant space accepted.1
    accepted.2

def authoredNormalVerifierRunInvariantCheck : Nat → List Atom → Bool
  | 0, space => authoredNormalVerifierInvariantCheck space
  | fuel + 1, space =>
      authoredNormalVerifierInvariantCheck space &&
        match cReflectiveSourceWorkQueueStep .leaveInert space with
        | none => true
        | some next => authoredNormalVerifierRunInvariantCheck fuel next

/-- Successful replay of the combined inventory invariant constructs one
continuous adequate trace against the authored support-valued MM2 semantics. -/
def authoredNormalVerifierAdequateTraceOfCheck
    (fuel : Nat) (source : List Atom)
    (accepted : authoredNormalVerifierRunInvariantCheck fuel source = true) :
    CReflectiveAdequateTrace .leaveInert fuel source
      (cReflectiveSourceWorkQueueRunN .leaveInert fuel source).1 := by
  induction fuel generalizing source with
  | zero => exact .refl
  | succ fuel induction =>
      rw [authoredNormalVerifierRunInvariantCheck,
        Bool.and_eq_true] at accepted
      have currentInvariant :=
        authoredNormalVerifierInvariantCheck_sound accepted.1
      simp only [cReflectiveSourceWorkQueueRunN]
      cases moved : cReflectiveSourceWorkQueueStep .leaveInert source with
      | none => exact .refl
      | some next =>
          simp only [moved] at accepted
          exact .step currentInvariant moved (induction next accepted.2)

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

/-! ## Generic active-hypothesis transport -/

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

end Mettapedia.Languages.Metamath.MM2AssembledNormalExecution
