import Mettapedia.GSLT.LanguageDef.M0GCRecordReplayControlMachine

/-!
# Explicit-capacity chronological replay for M0GC

This module refines chronological proof-record replay with an explicit proof
store capacity.  Every successful record transition checks that one more
record fits, invokes the shared one-record validator, and retains the exact
admitted prefix.  Sufficient capacity is proved to make the bounded machine
observationally identical to the unbounded proof-prefix checker.

Maturity boundary: this is a fully connected intermediate proof of concept.
Capacity failure and storage growth are explicit, but the backing store is
still a persistent Lean `Array`, not a mutable byte/word heap with an ABI.
This is not yet Pancake, Clight, verified object code, an OS, or hardware.
Backend stores must refine this capacity discipline and terminal observation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.M0GCBoundedReplayControlMachine

open Mettapedia.GSLT.LanguageDef.M0GCWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplay
open Mettapedia.GSLT.LanguageDef.M0GCPhysicalTemplateAdequacy
open Mettapedia.GSLT.LanguageDef.M0GCNativeReplayAdequacy
open Mettapedia.GSLT.LanguageDef.M0GCCoreLoopCorrespondence

abbrev ReplayConfiguration :=
  Mettapedia.GSLT.LanguageDef.M0GCRecordReplayControlMachine.Configuration

/-! ## Explicit-capacity store -/

/-- A proof store carries its allocation bound separately from the admitted
records.  The executable update checks the bound rather than relying on a
proposition erased from the runtime state. -/
structure ProofStore where
  capacity : Nat
  admitted : CProofPrefixState
deriving DecidableEq, Repr

/-- The semantic invariant expected of every reachable store. -/
def ProofStore.WellFormed (store : ProofStore) : Prop :=
  store.admitted.processed.size ≤ store.capacity

/-- Check one proof record only when its result fits in the allocated store. -/
def replayRecord? (configuration : ReplayConfiguration)
    (store : ProofStore) (proof : ProofNode) : Option ProofStore :=
  if store.admitted.processed.size < store.capacity then
    match cCoreReplayRecord? configuration.profile configuration.tables
        configuration.certificate configuration.terms
        configuration.replayFuel store.admitted proof with
    | none => none
    | some next => some { store with admitted := next }
  else none

/-- Bounded-record acceptance implies acceptance by the shared one-record
checker with exactly the returned admitted prefix. -/
theorem replayRecord?_refines
    (configuration : ReplayConfiguration) {store next : ProofStore}
    {proof : ProofNode}
    (accepted : replayRecord? configuration store proof = some next) :
    cCoreReplayRecord? configuration.profile configuration.tables
        configuration.certificate configuration.terms
        configuration.replayFuel store.admitted proof =
      some next.admitted := by
  unfold replayRecord? at accepted
  by_cases room : store.admitted.processed.size < store.capacity
  · rw [if_pos room] at accepted
    cases recordResult :
        cCoreReplayRecord? configuration.profile configuration.tables
          configuration.certificate configuration.terms
          configuration.replayFuel store.admitted proof with
    | none => simp [recordResult] at accepted
    | some admitted =>
        simp [recordResult] at accepted
        subst next
        rfl
  · rw [if_neg room] at accepted
    contradiction

/-- Successful bounded replay preserves the allocation bound and grows the
admitted store by exactly one record. -/
theorem replayRecord?_wellFormed
    (configuration : ReplayConfiguration) {store next : ProofStore}
    {proof : ProofNode}
    (accepted : replayRecord? configuration store proof = some next) :
    next.WellFormed := by
  unfold replayRecord? at accepted
  by_cases room : store.admitted.processed.size < store.capacity
  · rw [if_pos room] at accepted
    cases recordResult :
        cCoreReplayRecord? configuration.profile configuration.tables
          configuration.certificate configuration.terms
          configuration.replayFuel store.admitted proof with
    | none => simp [recordResult] at accepted
    | some admitted =>
        simp [recordResult] at accepted
        subst next
        have shape := cCoreReplayRecord?_success_processed recordResult
        unfold ProofStore.WellFormed
        simp [shape]
        omega
  · rw [if_neg room] at accepted
    contradiction

/-- Capacity never changes during a successful record transition. -/
theorem replayRecord?_capacity
    (configuration : ReplayConfiguration) {store next : ProofStore}
    {proof : ProofNode}
    (accepted : replayRecord? configuration store proof = some next) :
    next.capacity = store.capacity := by
  unfold replayRecord? at accepted
  by_cases room : store.admitted.processed.size < store.capacity
  · rw [if_pos room] at accepted
    cases recordResult :
        cCoreReplayRecord? configuration.profile configuration.tables
          configuration.certificate configuration.terms
          configuration.replayFuel store.admitted proof with
    | none => simp [recordResult] at accepted
    | some admitted =>
        simp [recordResult] at accepted
        subst next
        rfl
  · rw [if_neg room] at accepted
    contradiction

/-! ## Recursive bounded reference -/

/-- Iterate bounded record replay over the chronological proof list. -/
def replayLoop (configuration : ReplayConfiguration) :
    List ProofNode → ProofStore → Option ProofStore
  | [], store => some store
  | proof :: proofs, store => do
      let next ← replayRecord? configuration store proof
      replayLoop configuration proofs next

/-- If the allocation can hold the initial admitted records plus every record
remaining, bounded replay has exactly the same admitted-prefix observation as
the unbounded checker. -/
theorem replayLoop_refines_of_capacity
    (configuration : ReplayConfiguration) (proofs : List ProofNode)
    (store : ProofStore)
    (enough :
      store.admitted.processed.size + proofs.length ≤ store.capacity) :
    Option.map ProofStore.admitted (replayLoop configuration proofs store) =
      cCoreReplayLoop configuration.profile configuration.tables
        configuration.certificate configuration.terms
        configuration.replayFuel proofs store.admitted := by
  induction proofs generalizing store with
  | nil => rfl
  | cons proof proofs inductionHypothesis =>
      have room : store.admitted.processed.size < store.capacity := by
        simp only [List.length_cons] at enough
        omega
      cases recordResult :
          cCoreReplayRecord? configuration.profile configuration.tables
            configuration.certificate configuration.terms
            configuration.replayFuel store.admitted proof with
      | none =>
          simp [replayLoop, replayRecord?, cCoreReplayLoop, room,
            recordResult]
      | some admitted =>
          have shape := cCoreReplayRecord?_success_processed recordResult
          have enoughTail :
              admitted.processed.size + proofs.length ≤ store.capacity := by
            rw [shape]
            simp only [Array.size_push, List.length_cons] at enough ⊢
            omega
          simpa [replayLoop, replayRecord?, cCoreReplayLoop, room,
              recordResult] using
            inductionHypothesis
              { capacity := store.capacity, admitted := admitted } enoughTail

/-! ## Bounded small-step machine -/

inductive ControlState where
  | running (remaining : List ProofNode) (store : ProofStore)
  | halt (result : Option ProofStore)
deriving DecidableEq, Repr

def observe : ControlState → Option (Option ProofStore)
  | .running _ _ => none
  | .halt result => some result

/-- One transition checks at most one proof record and one capacity guard. -/
def step (configuration : ReplayConfiguration) :
    ControlState → ControlState
  | .running [] store => .halt (some store)
  | .running (proof :: proofs) store =>
      match replayRecord? configuration store proof with
      | none => .halt none
      | some next => .running proofs next
  | .halt result => .halt result

def Transition (configuration : ReplayConfiguration)
    (before after : ControlState) : Prop :=
  step configuration before = after

theorem transition_deterministic
    (configuration : ReplayConfiguration)
    {before afterLeft afterRight : ControlState}
    (left : Transition configuration before afterLeft)
    (right : Transition configuration before afterRight) :
    afterLeft = afterRight := by
  unfold Transition at left right
  rw [← left, ← right]

@[simp] theorem step_halt (configuration : ReplayConfiguration)
    (result : Option ProofStore) :
    step configuration (.halt result) = .halt result := rfl

def runSteps (configuration : ReplayConfiguration) :
    Nat → ControlState → ControlState
  | 0, state => state
  | fuel + 1, state => runSteps configuration fuel (step configuration state)

@[simp] theorem runSteps_halt (configuration : ReplayConfiguration)
    (fuel : Nat) (result : Option ProofStore) :
    runSteps configuration fuel (.halt result) = .halt result := by
  induction fuel with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      simp [runSteps, inductionHypothesis]

theorem runSteps_sufficient (configuration : ReplayConfiguration)
    (proofs : List ProofNode) (store : ProofStore) :
    runSteps configuration (proofs.length + 1) (.running proofs store) =
      .halt (replayLoop configuration proofs store) := by
  induction proofs generalizing store with
  | nil => rfl
  | cons proof proofs inductionHypothesis =>
      cases recordResult : replayRecord? configuration store proof with
      | none => simp [runSteps, step, replayLoop, recordResult]
      | some next =>
          simp [runSteps, step, replayLoop, recordResult,
            inductionHypothesis]

def execute (configuration : ReplayConfiguration)
    (proofs : List ProofNode) (store : ProofStore) : Option ProofStore :=
  match runSteps configuration (proofs.length + 1)
      (.running proofs store) with
  | .halt result => result
  | .running _ _ => none

theorem execute_eq_replayLoop (configuration : ReplayConfiguration)
    (proofs : List ProofNode) (store : ProofStore) :
    execute configuration proofs store =
      replayLoop configuration proofs store := by
  unfold execute
  rw [runSteps_sufficient]

/-- Sufficient allocation makes the bounded small-step machine exactly the
unbounded proof-prefix checker after projecting away capacity metadata. -/
theorem execute_refines_of_capacity
    (configuration : ReplayConfiguration) (proofs : List ProofNode)
    (store : ProofStore)
    (enough :
      store.admitted.processed.size + proofs.length ≤ store.capacity) :
    Option.map ProofStore.admitted (execute configuration proofs store) =
      cCoreReplayLoop configuration.profile configuration.tables
        configuration.certificate configuration.terms
        configuration.replayFuel proofs store.admitted := by
  rw [execute_eq_replayLoop]
  exact replayLoop_refines_of_capacity configuration proofs store enough

/-! ## Positive and negative discriminators -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplayCanary

abbrev configuration : ReplayConfiguration :=
  Mettapedia.GSLT.LanguageDef.M0GCRecordReplayControlMachine.Canary.configuration

def emptyOneSlot : ProofStore :=
  { capacity := 1, admitted := {} }

def acceptedOneSlot : ProofStore :=
  { capacity := 1
    admitted := M0GCCoreLoopCorrespondence.Canary.acceptedState }

/-- Positive discriminator: one slot admits the one-record pair proof. -/
theorem pair_record_accepts :
    replayRecord? configuration emptyOneSlot proofNode =
      some acceptedOneSlot := by
  unfold replayRecord? emptyOneSlot acceptedOneSlot
  rw [if_pos (by simp)]
  change
    (match cCoreReplayRecord? profile
        M0GCCoreLoopCorrespondence.Canary.tables certificate termState
        M0GCCoreLoopCorrespondence.Canary.canaryFuel
        ({} : CProofPrefixState) proofNode with
      | none => none
      | some next =>
          some ({ capacity := 1, admitted := next } : ProofStore)) =
    some
      ({ capacity := 1
         admitted := M0GCCoreLoopCorrespondence.Canary.acceptedState } :
        ProofStore)
  rw [M0GCRecordReplayControlMachine.Canary.pair_record_accepts]

/-- The complete bounded small-step machine accepts the same pair proof. -/
theorem pair_machine_accepts :
    execute configuration certificate.proofs emptyOneSlot =
      some acceptedOneSlot := by
  rw [execute_eq_replayLoop]
  change replayLoop configuration [proofNode] emptyOneSlot =
    some acceptedOneSlot
  rw [replayLoop, pair_record_accepts]
  rfl

def emptyZeroSlot : ProofStore :=
  { capacity := 0, admitted := {} }

/-- Negative storage discriminator: an otherwise valid proof is rejected when
the explicit store has no room. -/
theorem zero_capacity_rejected :
    execute configuration certificate.proofs emptyZeroSlot = none := by
  rw [execute_eq_replayLoop]
  rfl

end Canary

#print axioms replayRecord?_refines
#print axioms replayRecord?_wellFormed
#print axioms replayLoop_refines_of_capacity
#print axioms transition_deterministic
#print axioms runSteps_sufficient
#print axioms execute_refines_of_capacity
#print axioms Canary.pair_record_accepts
#print axioms Canary.pair_machine_accepts
#print axioms Canary.zero_capacity_rejected

end Mettapedia.GSLT.LanguageDef.M0GCBoundedReplayControlMachine
