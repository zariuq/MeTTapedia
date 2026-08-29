import Mettapedia.GSLT.Core.TerminatingStreamingRowEmission

/-!
# Compact Appendix-B byte classifier as a GSLT stage

This is the dependency-light semantic core of compressed Metamath byte
handling.  A byte occurrence is classified into a target-owned row and then
dispatched into one compact proof-DAG action, a prefix update, or a fault.  It
does not decode a whole compressed proof into normal labels.

The module intentionally has no dependency on the full Metamath source reader
or MM2 runtime.  Those two later adapters owe exact comparison theorems:

* the source adapter compares `authoredOutcome` with the authored compressed
  decoder; and
* the target adapter maps `TargetRow` to the actual MM2 verifier row and proves
  firing in an assembled reflective program.

Keeping those adapters separate prevents either one from becoming the semantic
definition of the other.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.CompressedByteClassifierCore

open Mettapedia.GSLT
open Mettapedia.GSLT.ClassifierLowering
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.IndexedModalFunctor
open Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.RowEmission

/-! ## Source-owned compact state -/

/-- One byte occurrence.  Equal bytes at distinct source positions or owners
remain distinct inputs to the scanner. -/
structure ByteOccurrence (Owner : Type) where
  owner : Owner
  position : Nat
  byte : UInt8

/-- The compact least-significant-first representation of the Appendix-B
prefix.  The surrounding word cursor supplies ordering; this state retains the
history necessary for the next compact index. -/
inductive Phase where
  | between
  | open (reversePrefix : List Nat)
  | completed
deriving DecidableEq, Repr

namespace Phase

def reversePrefix : Phase -> List Nat
  | .between | .completed => []
  | .open digits => digits

end Phase

/-- The value of the retained bijective-base-five prefix. -/
def prefixValue : List Nat -> Nat
  | [] => 0
  | digit :: remaining => 5 * prefixValue remaining + digit

/-- The compact index selected by a terminal `A`--`T` byte. -/
def indexValue (reversePrefix : List Nat) (terminalDigit : Nat) : Nat :=
  20 * prefixValue reversePrefix + terminalDigit

/-- A compact scanner action names one DAG-level event, never an expanded
normal-label trace. -/
inductive Action where
  | step (index : Nat)
  | save
  | unknown
deriving DecidableEq, Repr

inductive Fault where
  | invalidByte (byte : UInt8)
  | saveOutsideCompleted (phase : Phase)
  | questionInsideOpenIndex (reversePrefix : List Nat)
  | incompleteOpenIndex (reversePrefix : List Nat)
deriving DecidableEq, Repr

inductive Outcome where
  | decoded (actions : List Action) (next : Phase)
  | fault (reason : Fault)
deriving DecidableEq, Repr

namespace Outcome

def actionCount : Outcome -> Nat
  | .decoded actions _ => actions.length
  | .fault _ => 0

end Outcome

/-- Completing a compact compressed stream has a distinct observation from
processing one of its bytes. -/
inductive FinalOutcome where
  | complete
  | fault (reason : Fault)
deriving DecidableEq, Repr

/-- The independently authored Appendix-B byte semantics. -/
def authoredOutcome (phase : Phase) (byte : UInt8) : Outcome :=
  let code := byte.toNat
  if 65 <= code && code <= 84 then
    .decoded [.step (indexValue phase.reversePrefix (code - 65))] .completed
  else if 85 <= code && code <= 89 then
    .decoded [] (.open ((code - 84) :: phase.reversePrefix))
  else if code = 90 then
    match phase with
    | .completed => .decoded [.save] .between
    | .between | .open _ => .fault (.saveOutsideCompleted phase)
  else if code = 63 then
    match phase with
    | .open reversePrefix => .fault (.questionInsideOpenIndex reversePrefix)
    | .between | .completed => .decoded [.unknown] .between
  else
    .fault (.invalidByte byte)

/-- The independently authored end-of-input rule.  An unfinished numeric
prefix is an explicit fault; it is never silently treated as a completed
proof action. -/
def finalize (phase : Phase) : FinalOutcome :=
  match phase with
  | .between | .completed => .complete
  | .open reversePrefix => .fault (.incompleteOpenIndex reversePrefix)

/-! ## Target-owned classification and rows -/

inductive ByteClass where
  | terminal (digit : Nat)
  | prefix (digit : Nat)
  | save
  | saveFault (phase : Phase)
  | question (phase : Phase)
  | questionOpenFault
  | invalid (byte : UInt8)
deriving DecidableEq, Repr

/-- An abstract public row vocabulary.  The MM2 adapter later maps these
constructors to the actual emitted MM2 row atoms. -/
inductive TargetRow where
  | terminalByte (code digit : Nat)
  | prefixByte (code digit : Nat)
  | saveRule
  | saveDisallowed (phase : Phase)
  | questionAllowed (phase : Phase)
  | questionOpenFaultRule
  | invalidByte (code : Nat)
deriving DecidableEq, Repr

/-- Classification of the explicit end-of-input event. -/
inductive EndClass where
  | complete
  | incomplete (reversePrefix : List Nat)
deriving DecidableEq, Repr

/-- Target-owned row vocabulary for stream completion. -/
inductive EndRow where
  | completeInput
  | incompleteOpenIndex (reversePrefix : List Nat)
deriving DecidableEq, Repr

namespace ByteClass

def row : ByteClass -> TargetRow
  | .terminal digit => .terminalByte (65 + digit) digit
  | .prefix digit => .prefixByte (84 + digit) digit
  | .save => .saveRule
  | .saveFault phase => .saveDisallowed phase
  | .question phase => .questionAllowed phase
  | .questionOpenFault => .questionOpenFaultRule
  | .invalid byte => .invalidByte byte.toNat

end ByteClass

namespace EndClass

def row : EndClass -> EndRow
  | .complete => .completeInput
  | .incomplete reversePrefix => .incompleteOpenIndex reversePrefix

end EndClass

/-- Target classification is independently written from `authoredOutcome`. -/
def classify (phase : Phase) (byte : UInt8) : ByteClass :=
  let code := byte.toNat
  if 65 <= code && code <= 84 then
    .terminal (code - 65)
  else if 85 <= code && code <= 89 then
    .prefix (code - 84)
  else if code = 90 then
    match phase with
    | .completed => .save
    | .between | .open _ => .saveFault phase
  else if code = 63 then
    match phase with
    | .open _ => .questionOpenFault
    | .between | .completed => .question phase
  else
    .invalid byte

/-- Target dispatch consumes the selected target class. -/
def dispatch (phase : Phase) (_byte : UInt8) : ByteClass -> Outcome
  | .terminal digit =>
      .decoded [.step (indexValue phase.reversePrefix digit)] .completed
  | .prefix digit =>
      .decoded [] (.open (digit :: phase.reversePrefix))
  | .save => .decoded [.save] .between
  | .saveFault failedPhase => .fault (.saveOutsideCompleted failedPhase)
  | .question _ => .decoded [.unknown] .between
  | .questionOpenFault =>
      .fault (.questionInsideOpenIndex phase.reversePrefix)
  | .invalid byte => .fault (.invalidByte byte)

/-- Target classification for the end-of-input event. -/
def classifyEnd : Phase -> EndClass
  | .between | .completed => .complete
  | .open reversePrefix => .incomplete reversePrefix

/-- Target dispatch for the end-of-input event. -/
def dispatchEnd (_phase : Phase) : EndClass -> FinalOutcome
  | .complete => .complete
  | .incomplete reversePrefix => .fault (.incompleteOpenIndex reversePrefix)

/-- Target classification and dispatch agree with the independently authored
source operation. -/
theorem authoredOutcome_eq_targetDispatch
    (phase : Phase) (byte : UInt8) :
    authoredOutcome phase byte = dispatch phase byte (classify phase byte) := by
  cases phase <;>
    unfold authoredOutcome classify dispatch Phase.reversePrefix
  all_goals
    by_cases terminalCase :
      (decide (65 <= byte.toNat) && decide (byte.toNat <= 84)) = true
    · simp [terminalCase]
    · by_cases prefixCase :
        (decide (85 <= byte.toNat) && decide (byte.toNat <= 89)) = true
      · simp [terminalCase, prefixCase]
      · by_cases saveCase : byte.toNat = 90
        · simp [saveCase]
        · by_cases questionCase : byte.toNat = 63
          · simp [questionCase]
          · simp [terminalCase, prefixCase, saveCase, questionCase]

/-- Target end classification and dispatch agree with the independently
authored end-of-input operation. -/
theorem finalize_eq_targetDispatch (phase : Phase) :
    finalize phase = dispatchEnd phase (classifyEnd phase) := by
  cases phase <;> rfl

/-- A compact byte transition names at most one DAG action.  This is the
anti-pre-expansion bound for compressed proofs. -/
theorem dispatch_actionCount_le_one
    (phase : Phase) (byte : UInt8) (byteClass : ByteClass) :
    (dispatch phase byte byteClass).actionCount <= 1 := by
  cases byteClass <;> simp [dispatch, Outcome.actionCount]

/-! ## GSLT realization -/

/-- One source request combines the byte occurrence with its compact phase. -/
structure Request (Owner : Type) where
  occurrence : ByteOccurrence Owner
  phase : Phase

/-- The actual supplied source operation, target classification, dispatch, and
row vocabulary form one reusable classifier-lowering stage. -/
def scannerStage (Owner : Type) :
    Stage (Request Owner) Outcome ByteClass TargetRow where
  authoredRun := fun request =>
    authoredOutcome request.phase request.occurrence.byte
  classify := fun request =>
    classify request.phase request.occurrence.byte
  dispatch := fun request byteClass =>
    dispatch request.phase request.occurrence.byte byteClass
  row := fun _ byteClass => byteClass.row
  dispatch_correct := by
    intro request
    exact (authoredOutcome_eq_targetDispatch request.phase request.occurrence.byte).symm

/-- The end-of-input operation is a second instance of the same reusable
classifier-lowering construction. -/
def finalizerStage : Stage Phase FinalOutcome EndClass EndRow where
  authoredRun := finalize
  classify := classifyEnd
  dispatch := dispatchEnd
  row := fun _ endClass => endClass.row
  dispatch_correct := by
    intro phase
    exact (finalize_eq_targetDispatch phase).symm

abbrev SourceTerm (Owner : Type) :=
  ClassifierLowering.SourceTerm (Request Owner) Outcome

abbrev TargetTerm (Owner : Type) :=
  ClassifierLowering.TargetTerm (Request Owner) Outcome ByteClass TargetRow

def sourceGSLT (Owner : Type) : GSLT :=
  ClassifierLowering.sourceGSLT (scannerStage Owner)

def targetGSLT (Owner : Type) : GSLT :=
  ClassifierLowering.targetGSLT (scannerStage Owner)

def finalizerSourceGSLT : GSLT :=
  ClassifierLowering.sourceGSLT finalizerStage

def finalizerTargetGSLT : GSLT :=
  ClassifierLowering.targetGSLT finalizerStage

def scannerRealization (Owner : Type) :
    OperationalRealization (sourceGSLT Owner) (targetGSLT Owner) :=
  ClassifierLowering.realization (scannerStage Owner)

def finalizerRealization :
    OperationalRealization finalizerSourceGSLT finalizerTargetGSLT :=
  ClassifierLowering.realization finalizerStage

/-- OSLF observes the compact scanner at macro-step scale after closure. -/
def scannerReachabilityNTT (Owner : Type) :
    ForwardModalPredicateTheory.Hom
      (oslfForwardModalObject (targetGSLT Owner).closure)
      (oslfForwardModalObject (sourceGSLT Owner).closure) :=
  ClassifierLowering.reachabilityNTT (scannerStage Owner)

/-- OSLF observes finalization at the same explicit macro-step scale. -/
def finalizerReachabilityNTT :
    ForwardModalPredicateTheory.Hom
      (oslfForwardModalObject finalizerTargetGSLT.closure)
      (oslfForwardModalObject finalizerSourceGSLT.closure) :=
  ClassifierLowering.reachabilityNTT finalizerStage

/-- Every authored byte step lowers to exactly classifier then dispatcher. -/
theorem scannerRealization_step_length
    (Owner : Type) (request : Request Owner) :
    ((scannerRealization Owner).mapStep
      (SourceStep.run (stage := scannerStage Owner) request)).length = 2 := by
  exact ClassifierLowering.realization_map_run_length (scannerStage Owner) request

/-- End-of-input also retains classifier then dispatcher, rather than becoming
a direct target verdict. -/
theorem finalizerRealization_step_length (phase : Phase) :
    (finalizerRealization.mapStep
      (SourceStep.run (stage := finalizerStage) phase)).length = 2 := by
  exact ClassifierLowering.realization_map_run_length finalizerStage phase

/-- The classified state carries the selected target row as an explicit
intermediate observation. -/
theorem scanner_classification_row
    (Owner : Type) (request : Request Owner) :
    TargetStep (scannerStage Owner) (.pending request)
      (.classified request
        (classify request.phase request.occurrence.byte)
        (classify request.phase request.occurrence.byte).row) :=
  ClassifierLowering.classified_row_exact (scannerStage Owner) request

/-! ## Terminating byte streams -/

/-- One target stream row retains both the target-owned byte classification
and the exact compact outcome it dispatches.  The outcome carries at most one
proof-DAG action, never a pre-expanded normal-label trace. -/
structure ScannerStreamRow where
  targetRow : TargetRow
  outcome : Outcome
deriving DecidableEq, Repr

/-- Forget only the compact action payload when selecting the next scanner
control state.  The row above retains that payload as an observation. -/
def outcomeDecision : Outcome ->
    Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.Decision Phase Fault
  | .decoded _ next => .continue next
  | .fault reason => .stop reason

/-- A stopping-aware stream instance of the reusable classifier lowering.
It consumes one compact byte at a time; a fault stops at that exact byte rather
than consuming or expanding the remaining compressed proof. -/
def scannerStreamStage (Owner : Type) :
    Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.Stage
      Phase (ByteOccurrence Owner) Fault ByteClass ScannerStreamRow where
  authoredRun := fun phase occurrence =>
    outcomeDecision (authoredOutcome phase occurrence.byte)
  classify := fun phase occurrence => classify phase occurrence.byte
  dispatch := fun phase occurrence byteClass =>
    outcomeDecision (dispatch phase occurrence.byte byteClass)
  row := fun phase occurrence byteClass =>
    { targetRow := byteClass.row
      outcome := dispatch phase occurrence.byte byteClass }
  dispatch_correct := by
    intro phase occurrence
    simp only [outcomeDecision]
    rw [authoredOutcome_eq_targetDispatch]

def scannerStreamSourceGSLT (Owner : Type) : GSLT :=
  Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.sourceGSLT
    (scannerStreamStage Owner)

def scannerStreamTargetGSLT (Owner : Type) : GSLT :=
  Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.targetGSLT
    (scannerStreamStage Owner)

def scannerStreamRealization (Owner : Type) :
    OperationalRealization (scannerStreamSourceGSLT Owner)
      (scannerStreamTargetGSLT Owner) :=
  Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.realization
    (scannerStreamStage Owner)

/-- OSLF observes the compact stopping scanner through the same closure-level
NTT arrow used for other GSLT-to-GSLT lowerings. -/
def scannerStreamReachabilityNTT (Owner : Type) :
    ForwardModalPredicateTheory.Hom
      (oslfForwardModalObject (scannerStreamTargetGSLT Owner).closure)
      (oslfForwardModalObject (scannerStreamSourceGSLT Owner).closure) :=
  Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.reachabilityNTT
    (scannerStreamStage Owner)

/-- The stream row preserves the exact one-byte compact action bound. -/
theorem scannerStreamRow_actionCount_le_one
    (Owner : Type) (phase : Phase) (occurrence : ByteOccurrence Owner) :
    ((scannerStreamStage Owner).row phase occurrence
      ((scannerStreamStage Owner).classify phase occurrence)).outcome.actionCount
        <= 1 := by
  exact dispatch_actionCount_le_one phase occurrence.byte
    (classify phase occurrence.byte)

private def streamTerminalACanary : ByteOccurrence Unit where
  owner := ()
  position := 0
  byte := UInt8.ofNat 65

private def streamInvalidCanary : ByteOccurrence Unit where
  owner := ()
  position := 1
  byte := UInt8.ofNat 48

/-- A compact `A` byte retains its first proof-DAG action in the classified
stream row. -/
theorem stream_terminal_A_row_carries_first_action :
    ((scannerStreamStage Unit).row .between streamTerminalACanary
      ((scannerStreamStage Unit).classify .between streamTerminalACanary)).outcome =
        .decoded [.step 0] .completed := by
  decide +kernel

/-- An invalid byte after a continuation prefix terminates the stream at that
occurrence.  It cannot be treated as a later normal-proof instruction. -/
theorem stream_invalid_prefix_byte_stops :
    (scannerStreamStage Unit).authoredRun (.open [1]) streamInvalidCanary =
      .stop (.invalidByte (UInt8.ofNat 48)) := by
  decide +kernel

/-- Even a stopping compact byte takes target classification then stopping
dispatch, preserving the byte occurrence in the terminal target state. -/
theorem stream_invalid_prefix_stop_path_has_two_steps :
    (Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.stopPath
      (scannerStreamStage Unit) (.open [1]) streamInvalidCanary []
      (.invalidByte (UInt8.ofNat 48)) (by decide)).length = 2 := by
  rfl

/-- A two-byte compact stream keeps the successful first byte, then stops at
the malformed second byte without consuming any invented suffix. -/
def compactStreamCanary :
    Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.StreamRun
      (scannerStreamStage Unit) .between [streamTerminalACanary, streamInvalidCanary] :=
  Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.runStream
    (scannerStreamStage Unit) .between [streamTerminalACanary, streamInvalidCanary]

theorem compactStreamCanary_endpoint :
    compactStreamCanary.endpoint =
      .stopped .completed streamInvalidCanary [] (.invalidByte (UInt8.ofNat 48)) := by
  rfl

theorem compactStreamCanary_source_length :
    compactStreamCanary.sourcePath.length = 2 := by
  rfl

theorem compactStreamCanary_target_length :
    compactStreamCanary.targetPath.length = 4 := by
  rfl

theorem compactStreamCanary_maps_exact :
    (scannerStreamRealization Unit).mapRoute compactStreamCanary.sourcePath =
      compactStreamCanary.targetPath :=
  compactStreamCanary.map_exact

/-- The same compact byte stream has an inspectable, occurrence-indexed row
artifact.  It is generated from the supplied scanner stage and retains the
stopping byte rather than expanding a proof trace. -/
def compactStreamRowArtifactCanary : Artifact (scannerStreamStage Unit) :=
  emit (scannerStreamStage Unit) 0 .between
    [streamTerminalACanary, streamInvalidCanary]

/-- The row artifact carries its own source and target GSLT paths.  This is the
reified data-transform instance used by later MM2 row adapters. -/
def compactStreamRowRunCanary :
    Run (scannerStreamStage Unit) .between
      [streamTerminalACanary, streamInvalidCanary] :=
  run (scannerStreamStage Unit) 0 .between
    [streamTerminalACanary, streamInvalidCanary]

theorem compactStreamRowArtifactCanary_events :
    compactStreamRowArtifactCanary.events =
      [eventAt (scannerStreamStage Unit) 0 .between streamTerminalACanary
         [streamInvalidCanary],
       eventAt (scannerStreamStage Unit) 1 .completed streamInvalidCanary []] := by
  rfl

/-- The malformed byte is retained as the exact stopping endpoint, with no
invented row for the unconsumed suffix. -/
theorem compactStreamRowArtifactCanary_endpoint :
    compactStreamRowArtifactCanary.endpoint =
      .stopped .completed streamInvalidCanary []
        (.invalidByte (UInt8.ofNat 48)) := by
  rfl

theorem compactStreamRowRunCanary_source_length :
    compactStreamRowRunCanary.sourcePath.length = 2 := by
  rfl

theorem compactStreamRowRunCanary_target_length :
    compactStreamRowRunCanary.targetPath.length = 4 := by
  rfl

theorem compactStreamRowRunCanary_maps_exact :
    (Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.realization
      (scannerStreamStage Unit)).mapRoute compactStreamRowRunCanary.sourcePath =
      compactStreamRowRunCanary.targetPath :=
  compactStreamRowRunCanary.map_exact

/-! ## Positive and negative controls -/

/-- A terminal byte selects its exact terminal-row family.  The explicit byte
equation keeps this pure semantic core independent of a byte-parser library. -/
theorem terminal_classification_row_exact
    (byte : UInt8) (digit : Nat)
    (terminalLower : 65 <= byte.toNat) (terminalUpper : byte.toNat <= 84)
    (byteValue : byte.toNat = 65 + digit) :
    (classify .between byte).row =
      .terminalByte (65 + digit) digit := by
  simp only [classify, ByteClass.row]
  have terminalByte :
      (decide (65 <= byte.toNat) && decide (byte.toNat <= 84)) = true := by
    simp [terminalLower, terminalUpper]
  rw [if_pos terminalByte, byteValue]
  have digitValue : 65 + digit - 65 = digit := Nat.add_sub_cancel_left 65 digit
  rw [digitValue]

/-- A prefix byte selects its exact prefix-row family. -/
theorem prefix_classification_row_exact
    (byte : UInt8) (digit : Nat) (byteValue : byte.toNat = 84 + digit)
    (notTerminal : ¬ (65 <= byte.toNat ∧ byte.toNat <= 84))
    (prefixLower : 85 <= byte.toNat) (prefixUpper : byte.toNat <= 89) :
    (classify .between byte).row =
      .prefixByte (84 + digit) digit := by
  simp only [classify, ByteClass.row]
  have noTerminal :
      ¬ ((decide (65 <= byte.toNat) && decide (byte.toNat <= 84)) = true) := by
    simp [notTerminal]
  have prefixByte :
      (decide (85 <= byte.toNat) && decide (byte.toNat <= 89)) = true := by
    simp [prefixLower, prefixUpper]
  rw [if_neg noTerminal, if_pos prefixByte, byteValue]
  have digitValue : 84 + digit - 84 = digit := Nat.add_sub_cancel_left 84 digit
  rw [digitValue]

/-- A concrete terminal control uses the first Appendix-B terminal byte. -/
theorem terminal_A_classification_row_exact :
    (classify .between (UInt8.ofNat 65)).row = .terminalByte 65 0 := by
  exact terminal_classification_row_exact (UInt8.ofNat 65) 0
    (by decide) (by decide) (by decide)

/-- A concrete prefix control uses the first Appendix-B prefix byte. -/
theorem prefix_U_classification_row_exact :
    (classify .between (UInt8.ofNat 85)).row = .prefixByte 85 1 := by
  exact prefix_classification_row_exact (UInt8.ofNat 85) 1
    (by decide) (by decide) (by decide) (by decide)

/-- A trailing continuation prefix is rejected at explicit end of input. -/
theorem trailing_prefix_is_incomplete (digits : List Nat) :
    finalize (.open digits) = .fault (.incompleteOpenIndex digits) :=
  rfl

/-- A completed stream is not rejected merely because it reaches end of input. -/
theorem completed_stream_finishes :
    finalize .completed = .complete :=
  rfl

/-- Negative control: an initial `Z` cannot take the successful-save branch. -/
theorem initial_save_is_not_success :
    classify .between (UInt8.ofNat 90) ≠ .save := by
  decide

/-- A minimal two-terminal compact spine emits its first action from the
between phase.  This is a source-semantic unit control, not a normal-proof
expansion. -/
theorem terminal_A_emits_first_action :
    authoredOutcome .between (UInt8.ofNat 65) =
      .decoded [.step 0] .completed := by
  decide

/-- The next terminal byte is interpreted against the completed compact
phase, retaining its distinct index. -/
theorem terminal_B_after_completed_emits_second_action :
    authoredOutcome .completed (UInt8.ofNat 66) =
      .decoded [.step 1] .completed := by
  decide

/-- An illegal byte after a continuation prefix remains a byte fault; it is
not coerced into a terminal action. -/
theorem illegal_byte_inside_prefix_is_fault :
    authoredOutcome (.open [1]) (UInt8.ofNat 48) =
      .fault (.invalidByte (UInt8.ofNat 48)) := by
  decide

/-- A save marker cannot interrupt an unfinished compact numeric index. -/
theorem save_inside_prefix_is_fault :
    authoredOutcome (.open [1]) (UInt8.ofNat 90) =
      .fault (.saveOutsideCompleted (.open [1])) := by
  decide

/-- A question byte outside an open index is an explicit compact unknown
action rather than an invalid-byte fault. -/
theorem question_between_emits_unknown_action :
    authoredOutcome .between (UInt8.ofNat 63) =
      .decoded [.unknown] .between := by
  decide

/-- Negative control: two distinct occurrence records cannot be silently
identified at the classified target boundary. -/
theorem different_occurrences_do_not_collapse
    {Owner : Type} {left right : ByteOccurrence Owner}
    (different : left ≠ right) (phase : Phase) :
    @TargetTerm.classified (Request Owner) Outcome ByteClass TargetRow
      { occurrence := left, phase := phase }
      (classify phase left.byte)
      (classify phase left.byte).row ≠
    @TargetTerm.classified (Request Owner) Outcome ByteClass TargetRow
      { occurrence := right, phase := phase }
      (classify phase right.byte)
      (classify phase right.byte).row := by
  intro equal
  have requestsEqual := ClassifierLowering.classified_input_injective equal
  apply different
  exact congrArg Request.occurrence requestsEqual

#print axioms authoredOutcome_eq_targetDispatch
#print axioms finalize_eq_targetDispatch
#print axioms dispatch_actionCount_le_one
#print axioms scannerRealization
#print axioms finalizerRealization
#print axioms scannerReachabilityNTT
#print axioms finalizerReachabilityNTT
#print axioms scannerRealization_step_length
#print axioms finalizerRealization_step_length
#print axioms scanner_classification_row
#print axioms scannerStreamStage
#print axioms scannerStreamRealization
#print axioms scannerStreamReachabilityNTT
#print axioms scannerStreamRow_actionCount_le_one
#print axioms stream_terminal_A_row_carries_first_action
#print axioms stream_invalid_prefix_byte_stops
#print axioms stream_invalid_prefix_stop_path_has_two_steps
#print axioms compactStreamCanary_endpoint
#print axioms compactStreamCanary_source_length
#print axioms compactStreamCanary_target_length
#print axioms compactStreamCanary_maps_exact
#print axioms compactStreamRowArtifactCanary_events
#print axioms compactStreamRowArtifactCanary_endpoint
#print axioms compactStreamRowRunCanary_source_length
#print axioms compactStreamRowRunCanary_target_length
#print axioms compactStreamRowRunCanary_maps_exact
#print axioms terminal_classification_row_exact
#print axioms prefix_classification_row_exact
#print axioms terminal_A_classification_row_exact
#print axioms prefix_U_classification_row_exact
#print axioms trailing_prefix_is_incomplete
#print axioms completed_stream_finishes
#print axioms initial_save_is_not_success
#print axioms terminal_A_emits_first_action
#print axioms terminal_B_after_completed_emits_second_action
#print axioms illegal_byte_inside_prefix_is_fault
#print axioms save_inside_prefix_is_fault
#print axioms question_between_emits_unknown_action
#print axioms different_occurrences_do_not_collapse

end Mettapedia.Languages.Metamath.CompressedByteClassifierCore
