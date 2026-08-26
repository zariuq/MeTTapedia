import Mathlib.Tactic
import Mettapedia.GSLT.LanguageDef.ScopedAuthoritativeSlotCompilation

/-!
# Semantic activation protocol for the MeTTa abstract machine

This module states the activation boundary independently of any C layout.  An
activation carries an instruction position, authoritative scoped slots, a
rollback checkpoint, a complete live-root descriptor, an ordered compiled
choice continuation, and an exact fallback state.

Admission is executable and fails closed.  A checkpoint beyond the current
trail, an omitted live root, or an unsupported continuation occurrence rejects
the activation.  The ordered continuation compiler is proved to preserve the
source occurrence list exactly, so order, multiplicity, and duplicate
occurrences survive activation and escape.
-/

namespace Mettapedia.GSLT.LanguageDef.AuthoritativeMAMActivationProtocol

open FiniteEnvironmentCompilation
open AuthoritativeSlotTrailCompilation
open ScopedAuthoritativeSlotCompilation

universe uKey uValue uPosition uRoot uOccurrence uFallback uCode

/-! ## Precise roots -/

/-- Executable root coverage.  Root order is irrelevant to collection, but no
live occurrence may be absent from the declaration. -/
def rootsCoveredB [DecidableEq Root] (live declared : List Root) : Bool :=
  live.all fun root => decide (root ∈ declared)

theorem rootsCoveredB_eq_true_iff [DecidableEq Root]
    (live declared : List Root) :
    rootsCoveredB live declared = true ↔
      ∀ root ∈ live, root ∈ declared := by
  induction live with
  | nil => simp [rootsCoveredB]
  | cons head tail inductionHypothesis =>
      simp [rootsCoveredB]

/-- A root descriptor is representation data, not yet evidence of completeness. -/
structure RootDescriptor (Root : Type uRoot) where
  declared : List Root

/-- Admission upgrades one specific descriptor only after checking every
semantic live root.  Indexing by the proposed descriptor prevents accepted
evidence from being detached and attached to another declaration. -/
structure AdmittedRootDescriptor (live : List Root)
    (descriptor : RootDescriptor Root) : Type uRoot where
  complete : ∀ root ∈ live, root ∈ descriptor.declared

/-- Check a proposed root descriptor and retain the completeness proof in the
accepted result. -/
def admitRootDescriptor? [DecidableEq Root]
    (live : List Root) (descriptor : RootDescriptor Root) :
    Option (AdmittedRootDescriptor live descriptor) :=
  if covered : rootsCoveredB live descriptor.declared = true then
    some
      { complete :=
          (rootsCoveredB_eq_true_iff live descriptor.declared).1 covered }
  else
    none

/-- Omitting even one live root makes root admission fail. -/
theorem admitRootDescriptor?_eq_none_of_missing [DecidableEq Root]
    (live : List Root) (descriptor : RootDescriptor Root) (root : Root)
    (rootLive : root ∈ live) (rootMissing : root ∉ descriptor.declared) :
    admitRootDescriptor? live descriptor = none := by
  unfold admitRootDescriptor?
  split
  · next covered =>
      have complete :=
        (rootsCoveredB_eq_true_iff live descriptor.declared).1 covered
      exact False.elim (rootMissing (complete root rootLive))
  · rfl

/-- Roots retained by one slot payload.  Aliases contain slot coordinates, not
values; concrete values contribute their complete root family. -/
def payloadRoots
    (rootsOfValue : Value → List Root) :
    Option (SlotPayload inventory Value) → List Root
  | none => []
  | some (.alias _) => []
  | some (.value stored) => rootsOfValue stored

/-- Roots retained by the current authoritative slot cells. -/
def currentSlotRoots
    (state : State inventory (SlotPayload inventory Value))
    (rootsOfValue : Value → List Root) : List Root :=
  (List.ofFn state.slots).flatMap (payloadRoots rootsOfValue)

/-- Roots retained by overwritten values in the undo trail.  These values are
live because rollback may restore them. -/
def undoTrailRoots
    (state : State inventory (SlotPayload inventory Value))
    (rootsOfValue : Value → List Root) : List Root :=
  state.trail.flatMap fun entry => payloadRoots rootsOfValue entry.previous

/-! ## Ordered continuation compilation -/

/-- Compile every source occurrence in order.  Any unsupported occurrence
rejects the whole continuation rather than silently deleting it. -/
def compileChoices? (compileOne : Occurrence → Option Code) :
    List Occurrence → Option (List Code)
  | [] => some []
  | occurrence :: occurrences => do
      let code ← compileOne occurrence
      let rest ← compileChoices? compileOne occurrences
      pure (code :: rest)

/-- A locally sound occurrence compiler preserves the entire ordered source
list, including duplicate occurrences. -/
theorem compileChoices?_decode
    (compileOne : Occurrence → Option Code) (decode : Code → Occurrence)
    (sound : ∀ occurrence code,
      compileOne occurrence = some code → decode code = occurrence)
    (source : List Occurrence) (compiled : List Code)
    (accepted : compileChoices? compileOne source = some compiled) :
    compiled.map decode = source := by
  induction source generalizing compiled with
  | nil =>
      simp [compileChoices?] at accepted
      subst compiled
      rfl
  | cons occurrence source inductionHypothesis =>
      simp only [compileChoices?] at accepted
      cases compiledCode : compileOne occurrence with
      | none => simp [compiledCode] at accepted
      | some code =>
          cases compiledRest : compileChoices? compileOne source with
          | none => simp [compiledCode, compiledRest] at accepted
          | some rest =>
              simp [compiledCode, compiledRest] at accepted
              subst compiled
              simp [sound occurrence code compiledCode,
                inductionHypothesis rest compiledRest]

/-! ## Activation admission -/

/-- The semantic ingredients of one proposed activation.  This record is not a
mandate for one physical runtime structure: it only names the information that
every conforming representation must account for. -/
structure ActivationCandidate
    {Key : Type uKey} (inventory : Inventory Key) (Value : Type uValue)
    (Position : Type uPosition) (Root : Type uRoot)
    (Occurrence : Type uOccurrence) (Fallback : Type uFallback) where
  instructionPosition : Position
  state : State inventory (SlotPayload inventory Value)
  trailCheckpoint : Nat
  rootDescriptor : RootDescriptor Root
  sourceChoices : List Occurrence
  fallbackState : Fallback

/-- All semantically live roots in an activation, composed from current slot
values, rollback values, ordered continuation occurrences, and the fallback
state. -/
def ActivationCandidate.liveRoots
    (candidate : ActivationCandidate inventory Value Position Root
      Occurrence Fallback)
    (rootsOfValue : Value → List Root)
    (rootsOfChoice : Occurrence → List Root)
    (rootsOfFallback : Fallback → List Root) : List Root :=
  currentSlotRoots candidate.state rootsOfValue ++
    undoTrailRoots candidate.state rootsOfValue ++
    candidate.sourceChoices.flatMap rootsOfChoice ++
    rootsOfFallback candidate.fallbackState

/-- Checked activation evidence.  It retains the exact ordered compilation
receipt and the complete-root proof used at admission. -/
structure AdmittedActivation
    (candidate : ActivationCandidate inventory Value Position Root
      Occurrence Fallback)
    (rootsOfValue : Value → List Root)
    (rootsOfChoice : Occurrence → List Root)
    (rootsOfFallback : Fallback → List Root)
    (compileOne : Occurrence → Option Code) where
  checkpointValid : candidate.trailCheckpoint ≤ candidate.state.trail.length
  slotsValid : frameValid candidate.state.slots = true
  roots : AdmittedRootDescriptor
    (candidate.liveRoots rootsOfValue rootsOfChoice rootsOfFallback)
    candidate.rootDescriptor
  compiledChoices : List Code
  compiledChoicesReceipt :
    compileChoices? compileOne candidate.sourceChoices = some compiledChoices

/-- Admit an activation only when rollback, precise roots, and every ordered
continuation occurrence are simultaneously available. -/
def admitActivation? [DecidableEq Root]
    (candidate : ActivationCandidate inventory Value Position Root
      Occurrence Fallback)
    (rootsOfValue : Value → List Root)
    (rootsOfChoice : Occurrence → List Root)
    (rootsOfFallback : Fallback → List Root)
    (compileOne : Occurrence → Option Code) :
    Option (AdmittedActivation candidate rootsOfValue rootsOfChoice
      rootsOfFallback compileOne) :=
  if checkpointValid :
      candidate.trailCheckpoint ≤ candidate.state.trail.length then
    if slotsValid : frameValid candidate.state.slots = true then
      match admitRootDescriptor?
          (candidate.liveRoots rootsOfValue rootsOfChoice rootsOfFallback)
          candidate.rootDescriptor with
      | none => none
      | some roots =>
          match choiceReceipt : compileChoices? compileOne candidate.sourceChoices with
          | none => none
          | some compiledChoices =>
              some
                { checkpointValid := checkpointValid
                  slotsValid := slotsValid
                  roots := roots
                  compiledChoices := compiledChoices
                  compiledChoicesReceipt := choiceReceipt }
    else
      none
  else
    none

/-- Missing-root rejection propagates through whole-activation admission. -/
theorem admitActivation?_eq_none_of_missing_root [DecidableEq Root]
    (candidate : ActivationCandidate inventory Value Position Root
      Occurrence Fallback)
    (rootsOfValue : Value → List Root)
    (rootsOfChoice : Occurrence → List Root)
    (rootsOfFallback : Fallback → List Root)
    (compileOne : Occurrence → Option Code)
    (root : Root)
    (rootLive : root ∈
      candidate.liveRoots rootsOfValue rootsOfChoice rootsOfFallback)
    (rootMissing : root ∉ candidate.rootDescriptor.declared) :
    admitActivation? candidate rootsOfValue rootsOfChoice rootsOfFallback
      compileOne = none := by
  unfold admitActivation?
  split
  · split
    · cases admittedEq : admitRootDescriptor?
          (candidate.liveRoots rootsOfValue rootsOfChoice rootsOfFallback)
          candidate.rootDescriptor with
      | none => rfl
      | some admitted =>
          exfalso
          exact rootMissing (admitted.complete root rootLive)
    · rfl
  · rfl

/-- Invalid scoped aliases reject activation before any optimized execution. -/
theorem admitActivation?_eq_none_of_invalid_slots [DecidableEq Root]
    (candidate : ActivationCandidate inventory Value Position Root
      Occurrence Fallback)
    (rootsOfValue : Value → List Root)
    (rootsOfChoice : Occurrence → List Root)
    (rootsOfFallback : Fallback → List Root)
    (compileOne : Occurrence → Option Code)
    (invalid : frameValid candidate.state.slots = false) :
    admitActivation? candidate rootsOfValue rootsOfChoice rootsOfFallback
      compileOne = none := by
  simp [admitActivation?, invalid]

/-- Escape through an admitted continuation returns exactly the source ordered
occurrence list after decoding. -/
theorem AdmittedActivation.orderedChoices_exact
    {Key : Type uKey} {inventory : Inventory Key} {Value : Type uValue}
    {Position : Type uPosition} {Root : Type uRoot}
    {Occurrence : Type uOccurrence} {Fallback : Type uFallback}
    {Code : Type uCode}
    {candidate : ActivationCandidate inventory Value Position Root
      Occurrence Fallback}
    {rootsOfValue : Value → List Root}
    {rootsOfChoice : Occurrence → List Root}
    {rootsOfFallback : Fallback → List Root}
    {compileOne : Occurrence → Option Code}
    (activation : AdmittedActivation candidate rootsOfValue rootsOfChoice
      rootsOfFallback compileOne)
    (decode : Code → Occurrence)
    (sound : ∀ occurrence code,
      compileOne occurrence = some code → decode code = occurrence) :
    activation.compiledChoices.map decode = candidate.sourceChoices :=
  compileChoices?_decode compileOne decode sound candidate.sourceChoices
    activation.compiledChoices activation.compiledChoicesReceipt

/-- Consequently an admitted continuation preserves successor multiplicity. -/
theorem AdmittedActivation.orderedChoices_length
    {Key : Type uKey} {inventory : Inventory Key} {Value : Type uValue}
    {Position : Type uPosition} {Root : Type uRoot}
    {Occurrence : Type uOccurrence} {Fallback : Type uFallback}
    {Code : Type uCode}
    {candidate : ActivationCandidate inventory Value Position Root
      Occurrence Fallback}
    {rootsOfValue : Value → List Root}
    {rootsOfChoice : Occurrence → List Root}
    {rootsOfFallback : Fallback → List Root}
    {compileOne : Occurrence → Option Code}
    (activation : AdmittedActivation candidate rootsOfValue rootsOfChoice
      rootsOfFallback compileOne)
    (decode : Code → Occurrence)
    (sound : ∀ occurrence code,
      compileOne occurrence = some code → decode code = occurrence) :
    activation.compiledChoices.length = candidate.sourceChoices.length := by
  have exactOrder := activation.orderedChoices_exact decode sound
  simpa using congrArg List.length exactOrder

/-- The admitted undo checkpoint is operational: rollback cannot fail. -/
theorem AdmittedActivation.rollback_available
    {Key : Type uKey} {inventory : Inventory Key} {Value : Type uValue}
    {Position : Type uPosition} {Root : Type uRoot}
    {Occurrence : Type uOccurrence} {Fallback : Type uFallback}
    {Code : Type uCode}
    {candidate : ActivationCandidate inventory Value Position Root
      Occurrence Fallback}
    {rootsOfValue : Value → List Root}
    {rootsOfChoice : Occurrence → List Root}
    {rootsOfFallback : Fallback → List Root}
    {compileOne : Occurrence → Option Code}
    [DecidableEq Key]
    (activation : AdmittedActivation candidate rootsOfValue rootsOfChoice
      rootsOfFallback compileOne) :
    exists restored,
      rollbackTo? inventory candidate.trailCheckpoint candidate.state =
        some restored :=
  rollbackTo?_available inventory candidate.trailCheckpoint candidate.state
    activation.checkpointValid

/-- Every root retained by the current dense slots is declared. -/
theorem AdmittedActivation.currentSlotRoot_declared
    {Key : Type uKey} {inventory : Inventory Key} {Value : Type uValue}
    {Position : Type uPosition} {Root : Type uRoot}
    {Occurrence : Type uOccurrence} {Fallback : Type uFallback}
    {Code : Type uCode}
    {candidate : ActivationCandidate inventory Value Position Root
      Occurrence Fallback}
    {rootsOfValue : Value → List Root}
    {rootsOfChoice : Occurrence → List Root}
    {rootsOfFallback : Fallback → List Root}
    {compileOne : Occurrence → Option Code}
    (activation : AdmittedActivation candidate rootsOfValue rootsOfChoice
      rootsOfFallback compileOne)
    (root : Root)
    (live : root ∈ currentSlotRoots candidate.state rootsOfValue) :
    root ∈ candidate.rootDescriptor.declared := by
  apply activation.roots.complete root
  simp [ActivationCandidate.liveRoots, live]

/-- Every root retained for undo is declared. -/
theorem AdmittedActivation.undoTrailRoot_declared
    {Key : Type uKey} {inventory : Inventory Key} {Value : Type uValue}
    {Position : Type uPosition} {Root : Type uRoot}
    {Occurrence : Type uOccurrence} {Fallback : Type uFallback}
    {Code : Type uCode}
    {candidate : ActivationCandidate inventory Value Position Root
      Occurrence Fallback}
    {rootsOfValue : Value → List Root}
    {rootsOfChoice : Occurrence → List Root}
    {rootsOfFallback : Fallback → List Root}
    {compileOne : Occurrence → Option Code}
    (activation : AdmittedActivation candidate rootsOfValue rootsOfChoice
      rootsOfFallback compileOne)
    (root : Root)
    (live : root ∈ undoTrailRoots candidate.state rootsOfValue) :
    root ∈ candidate.rootDescriptor.declared := by
  apply activation.roots.complete root
  simp [ActivationCandidate.liveRoots, live]

/-- Every root retained by an ordered choice occurrence is declared. -/
theorem AdmittedActivation.choiceRoot_declared
    {Key : Type uKey} {inventory : Inventory Key} {Value : Type uValue}
    {Position : Type uPosition} {Root : Type uRoot}
    {Occurrence : Type uOccurrence} {Fallback : Type uFallback}
    {Code : Type uCode}
    {candidate : ActivationCandidate inventory Value Position Root
      Occurrence Fallback}
    {rootsOfValue : Value → List Root}
    {rootsOfChoice : Occurrence → List Root}
    {rootsOfFallback : Fallback → List Root}
    {compileOne : Occurrence → Option Code}
    (activation : AdmittedActivation candidate rootsOfValue rootsOfChoice
      rootsOfFallback compileOne)
    (root : Root)
    (live : root ∈ candidate.sourceChoices.flatMap rootsOfChoice) :
    root ∈ candidate.rootDescriptor.declared := by
  apply activation.roots.complete root
  simp [ActivationCandidate.liveRoots, live]

/-- Every root retained by exact fallback is declared. -/
theorem AdmittedActivation.fallbackRoot_declared
    {Key : Type uKey} {inventory : Inventory Key} {Value : Type uValue}
    {Position : Type uPosition} {Root : Type uRoot}
    {Occurrence : Type uOccurrence} {Fallback : Type uFallback}
    {Code : Type uCode}
    {candidate : ActivationCandidate inventory Value Position Root
      Occurrence Fallback}
    {rootsOfValue : Value → List Root}
    {rootsOfChoice : Occurrence → List Root}
    {rootsOfFallback : Fallback → List Root}
    {compileOne : Occurrence → Option Code}
    (activation : AdmittedActivation candidate rootsOfValue rootsOfChoice
      rootsOfFallback compileOne)
    (root : Root)
    (live : root ∈ rootsOfFallback candidate.fallbackState) :
    root ∈ candidate.rootDescriptor.declared := by
  apply activation.roots.complete root
  simp [ActivationCandidate.liveRoots, live]

/-! ## Exact escape -/

/-- The generic boundary representation produced when an admitted activation
escapes.  Dense slots are materialized once; choices are decoded in order; the
fallback state is retained exactly. -/
structure EscapeObservation (Key : Type uKey) (Value : Type uValue)
    (Occurrence : Type uOccurrence) (Fallback : Type uFallback) where
  environment : SourceEnvironment Key Value
  orderedChoices : List Occurrence
  fallbackState : Fallback

/-- Escape an admitted activation to the ordinary generic representation. -/
def AdmittedActivation.escape
    {Key : Type uKey} {inventory : Inventory Key} {Value : Type uValue}
    {Position : Type uPosition} {Root : Type uRoot}
    {Occurrence : Type uOccurrence} {Fallback : Type uFallback}
    {Code : Type uCode}
    {candidate : ActivationCandidate inventory Value Position Root
      Occurrence Fallback}
    {rootsOfValue : Value → List Root}
    {rootsOfChoice : Occurrence → List Root}
    {rootsOfFallback : Fallback → List Root}
    {compileOne : Occurrence → Option Code}
    [DecidableEq Key]
    (activation : AdmittedActivation candidate rootsOfValue rootsOfChoice
      rootsOfFallback compileOne)
    (outer : SourceEnvironment Key Value) (decode : Code → Occurrence) :
    EscapeObservation Key Value Occurrence Fallback :=
  { environment := fun key =>
      (readBoundary inventory outer candidate.state.slots key).getD none
    orderedChoices := activation.compiledChoices.map decode
    fallbackState := candidate.fallbackState }

/-- Checked escape performs exactly the scoped materialization licensed by the
activation's valid slot frame. -/
theorem AdmittedActivation.escape_materializes
    {Key : Type uKey} {inventory : Inventory Key} {Value : Type uValue}
    {Position : Type uPosition} {Root : Type uRoot}
    {Occurrence : Type uOccurrence} {Fallback : Type uFallback}
    {Code : Type uCode}
    {candidate : ActivationCandidate inventory Value Position Root
      Occurrence Fallback}
    {rootsOfValue : Value → List Root}
    {rootsOfChoice : Occurrence → List Root}
    {rootsOfFallback : Fallback → List Root}
    {compileOne : Occurrence → Option Code}
    [DecidableEq Key]
    (activation : AdmittedActivation candidate rootsOfValue rootsOfChoice
      rootsOfFallback compileOne)
    (outer : SourceEnvironment Key Value) (decode : Code → Occurrence) :
    materialize? inventory outer candidate.state.slots =
      some (activation.escape outer decode).environment := by
  simp [materialize?, activation.slotsValid, AdmittedActivation.escape]

/-- Checked escape preserves the source continuation's exact order and
multiplicity. -/
theorem AdmittedActivation.escape_choices_exact
    {Key : Type uKey} {inventory : Inventory Key} {Value : Type uValue}
    {Position : Type uPosition} {Root : Type uRoot}
    {Occurrence : Type uOccurrence} {Fallback : Type uFallback}
    {Code : Type uCode}
    {candidate : ActivationCandidate inventory Value Position Root
      Occurrence Fallback}
    {rootsOfValue : Value → List Root}
    {rootsOfChoice : Occurrence → List Root}
    {rootsOfFallback : Fallback → List Root}
    {compileOne : Occurrence → Option Code}
    [DecidableEq Key]
    (activation : AdmittedActivation candidate rootsOfValue rootsOfChoice
      rootsOfFallback compileOne)
    (outer : SourceEnvironment Key Value) (decode : Code → Occurrence)
    (sound : ∀ occurrence code,
      compileOne occurrence = some code → decode code = occurrence) :
    (activation.escape outer decode).orderedChoices =
      candidate.sourceChoices :=
  activation.orderedChoices_exact decode sound

/-- Checked escape transports the exact generic fallback state. -/
theorem AdmittedActivation.escape_fallback_exact
    {Key : Type uKey} {inventory : Inventory Key} {Value : Type uValue}
    {Position : Type uPosition} {Root : Type uRoot}
    {Occurrence : Type uOccurrence} {Fallback : Type uFallback}
    {Code : Type uCode}
    {candidate : ActivationCandidate inventory Value Position Root
      Occurrence Fallback}
    {rootsOfValue : Value → List Root}
    {rootsOfChoice : Occurrence → List Root}
    {rootsOfFallback : Fallback → List Root}
    {compileOne : Occurrence → Option Code}
    [DecidableEq Key]
    (activation : AdmittedActivation candidate rootsOfValue rootsOfChoice
      rootsOfFallback compileOne)
    (outer : SourceEnvironment Key Value) (decode : Code → Occurrence) :
    (activation.escape outer decode).fallbackState = candidate.fallbackState :=
  rfl

/-! ## Positive and negative witnesses -/

private def oneRegister : Inventory Unit where
  keys := [()]
  nodup := by decide

private def valueSlotState :
    State oneRegister (SlotPayload oneRegister Nat) :=
  { slots := fun _ => some (.value 7)
    trail := [] }

private def exampleCandidate :
    ActivationCandidate oneRegister Nat Nat Nat Nat Nat where
  instructionPosition := 4
  state := valueSlotState
  trailCheckpoint := 0
  rootDescriptor := { declared := [7, 101, 102, 9] }
  sourceChoices := [1, 1, 2]
  fallbackState := 9

private def rootsOfNat (value : Nat) : List Nat := [value]
private def rootsOfChoice (choice : Nat) : List Nat := [100 + choice]
private def compileChoice (choice : Nat) : Option Nat := some (choice + 10)
private def decodeChoice (code : Nat) : Nat := code - 10

private theorem compileChoice_sound (choice code : Nat)
    (compiled : compileChoice choice = some code) :
    decodeChoice code = choice := by
  simp [compileChoice] at compiled
  subst code
  simp [decodeChoice]

/-- The composed live-root list includes the current slot value, every ordered
choice occurrence (including duplicates), and the exact fallback state. -/
example :
    exampleCandidate.liveRoots rootsOfNat rootsOfChoice rootsOfNat =
      [7, 101, 101, 102, 9] := by
  decide

/-- Positive suspension witness: complete roots and a valid checkpoint admit a
duplicate-preserving ordered continuation. -/
example :
    (admitActivation? exampleCandidate rootsOfNat rootsOfChoice rootsOfNat
      compileChoice).isSome = true := by
  decide

private def admittedExample :
    AdmittedActivation exampleCandidate rootsOfNat rootsOfChoice rootsOfNat
      compileChoice :=
  (admitActivation? exampleCandidate rootsOfNat rootsOfChoice rootsOfNat
    compileChoice).get (by decide)

private def emptyOuter : SourceEnvironment Unit Nat := fun _ => none

/-- Positive escape witness: generic materialization, ordered duplicates, and
fallback state cross the boundary together. -/
example :
    let escaped := admittedExample.escape emptyOuter decodeChoice
    escaped.environment () = some 7 ∧
      escaped.orderedChoices = [1, 1, 2] ∧
      escaped.fallbackState = 9 := by
  decide

/-- The ordered compiler retains both equal occurrences, not merely one
representative. -/
example :
    compileChoices? compileChoice [1, 1, 2] = some [11, 11, 12] := by
  decide

/-- Negative root witness: one missing live value rejects admission. -/
example : admitRootDescriptor? [7, 8] { declared := [7] } = none := by
  decide

private def missingFallbackRootCandidate :
    ActivationCandidate oneRegister Nat Nat Nat Nat Nat :=
  { exampleCandidate with rootDescriptor := { declared := [7, 101, 102] } }

/-- A missing fallback root rejects the complete activation, not only the
standalone root sub-check. -/
example :
    admitActivation? missingFallbackRootCandidate rootsOfNat rootsOfChoice
      rootsOfNat compileChoice = none := by
  decide

private def cyclicSlotState :
    State oneRegister (SlotPayload oneRegister Nat) :=
  { slots := fun slot => some (.alias slot)
    trail := [] }

private def cyclicSlotCandidate :
    ActivationCandidate oneRegister Nat Nat Nat Nat Nat :=
  { exampleCandidate with
      state := cyclicSlotState
      rootDescriptor := { declared := [101, 102, 9] } }

/-- A cyclic alias frame is rejected even when every non-slot root is present. -/
example :
    admitActivation? cyclicSlotCandidate rootsOfNat rootsOfChoice rootsOfNat
      compileChoice = none := by
  decide

private def stateWithUndoRoot :
    State oneRegister (SlotPayload oneRegister Nat) :=
  { slots := fun _ => some (.value 7)
    trail :=
      [{ slot := ⟨0, by decide⟩, previous := some (.value 5) }] }

private def candidateWithUndoRoot :
    ActivationCandidate oneRegister Nat Nat Nat Nat Nat :=
  { exampleCandidate with
      state := stateWithUndoRoot
      rootDescriptor := { declared := [7, 5, 101, 102, 9] } }

/-- Rollback values are live roots too; the descriptor must retain them. -/
example :
    candidateWithUndoRoot.liveRoots rootsOfNat rootsOfChoice rootsOfNat =
      [7, 5, 101, 101, 102, 9] ∧
    (admitActivation? candidateWithUndoRoot rootsOfNat rootsOfChoice rootsOfNat
      compileChoice).isSome = true := by
  decide

private def futureCheckpointCandidate :
    ActivationCandidate oneRegister Nat Nat Nat Nat Nat :=
  { exampleCandidate with trailCheckpoint := 1 }

/-- Negative checkpoint witness: a future undo mark cannot activate. -/
example :
    admitActivation? futureCheckpointCandidate rootsOfNat rootsOfChoice
      rootsOfNat compileChoice = none := by
  decide

private def refusingCompiler (choice : Nat) : Option Nat :=
  if choice = 2 then none else some choice

/-- Negative continuation witness: an unsupported occurrence rejects the whole
ordered continuation; it is not silently dropped. -/
example : compileChoices? refusingCompiler [1, 2, 3] = none := by
  decide

#print axioms rootsCoveredB_eq_true_iff
#print axioms admitRootDescriptor?_eq_none_of_missing
#print axioms admitActivation?_eq_none_of_missing_root
#print axioms admitActivation?_eq_none_of_invalid_slots
#print axioms compileChoices?_decode
#print axioms AdmittedActivation.orderedChoices_exact
#print axioms AdmittedActivation.rollback_available
#print axioms AdmittedActivation.currentSlotRoot_declared
#print axioms AdmittedActivation.escape_materializes

end Mettapedia.GSLT.LanguageDef.AuthoritativeMAMActivationProtocol
