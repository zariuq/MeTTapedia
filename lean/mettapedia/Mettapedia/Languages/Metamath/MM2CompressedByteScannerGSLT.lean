import Mettapedia.GSLT.Core.OperationalRealizationOSLF
import Mettapedia.Languages.Metamath.MM2CompressedProofByteSemanticsBridge

/-!
# Incremental Appendix-B byte scanner as a GSLT transformation

This module isolates the first executable compressed-proof stage.  It does
not expand compressed proofs: each source byte has one authored Appendix-B
outcome, while the target reaches that outcome through an explicit
classification row followed by a dispatch step.

The source outcome is independently compared with the existing authored
`decodeByte` function.  The target classification carries the exact public
MM2 row used by the corresponding verifier family.  Thus the two-step target
route is an implementation realization, rather than a second source decoder.
This module establishes the GSLT-level classifier route and its exact row
observations; the later theorem that those rows fire in an assembled reflective
MM2 program remains a separate execution seam.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.IndexedModalFunctor
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem

/-! ## Source-owned compact scanner state -/

/-- One source-byte occurrence.  Equal codepoints at different positions or
under different proof owners stay distinct before the enclosing word cursor
establishes their order. -/
structure ByteOccurrence where
  owner : Atom
  position : Nat
  byte : UInt8
deriving DecidableEq, Repr

/-- The source numeric accumulator is reified as its retained least-significant
first Appendix-B prefix.  This is source state, not an MM2 implementation
detail: it records the compact digit history needed for later heap lookup and
`Z` save transitions.  The enclosing word cursor establishes byte order, while
the request term below retains the owner and position of each byte occurrence. -/
inductive ScannerPhase where
  | between
  | open (reversePrefix : List Nat)
  | completed
deriving DecidableEq, Repr

namespace ScannerPhase

def reversePrefix : ScannerPhase -> List Nat
  | .between | .completed => []
  | .open digits => digits

def toSourcePhase : ScannerPhase -> CompressedPhase
  | .between => .betweenSteps
  | .open digits => .openIndex (compressedPrefixValue digits)
  | .completed => .justCompletedStep

def atom : ScannerPhase -> Atom
  | .between => .symbol "mm-compressed-between-steps"
  | .open _ => .symbol "mm-compressed-open-index"
  | .completed => .symbol "mm-compressed-just-completed-step"

end ScannerPhase

inductive ScannerFault where
  | invalidByte (byte : UInt8)
  | saveOutsideCompleted (phase : ScannerPhase)
  | questionInsideOpenIndex (reversePrefix : List Nat)
deriving DecidableEq, Repr

inductive ScannerOutcome where
  | decoded (actions : List CompressedAction) (next : ScannerPhase)
  | fault (reason : ScannerFault)
deriving DecidableEq, Repr

namespace ScannerOutcome

def toSourceResult : ScannerOutcome -> Option (List CompressedAction × CompressedPhase)
  | .decoded actions next => some (actions, next.toSourcePhase)
  | .fault _ => none

/-- The scanner's emitted action count.  A compact byte transition may name
one proof-DAG action, but it never unfolds that action into a normal proof
trace. -/
def actionCount : ScannerOutcome -> Nat
  | .decoded actions _ => actions.length
  | .fault _ => 0

end ScannerOutcome

/-- The source-owned one-byte Appendix-B action.  This definition is kept
separate from target classification and is compared below against the
pre-existing authored decoder. -/
def authoredOutcome (phase : ScannerPhase) (byte : UInt8) : ScannerOutcome :=
  let code := byte.toNat
  if 65 <= code ∧ code <= 84 then
    .decoded
      [.step (compressedIndexValue phase.reversePrefix (code - 65))]
      .completed
  else if 85 <= code ∧ code <= 89 then
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

/-- The compact scanner reification has exactly the authored raw decoder's
observable result. -/
theorem authoredOutcome_toSourceResult_eq_decodeByte
    (phase : ScannerPhase) (byte : UInt8) :
    (authoredOutcome phase byte).toSourceResult =
      decodeByte phase.toSourcePhase byte := by
  cases phase <;>
    simp only [authoredOutcome, ScannerOutcome.toSourceResult,
      ScannerPhase.toSourcePhase, ScannerPhase.reversePrefix,
      CompressedPhase.accumulator, compressedIndexValue, compressedPrefixValue,
      decodeByte]
  all_goals
    by_cases terminalCase : 65 <= byte.toNat ∧ byte.toNat <= 84
    · simp [terminalCase]
    · by_cases prefixCase : 85 <= byte.toNat ∧ byte.toNat <= 89
      · simp [terminalCase, prefixCase]
      · by_cases saveCase : byte.toNat = 90
        · simp [saveCase]
        · by_cases questionCase : byte.toNat = 63
          · simp [questionCase]
          · simp [terminalCase, prefixCase, saveCase, questionCase]

/-! ## Target-owned row classification -/

/-- The target retains the class selected from the byte before dispatching it.
The class determines an actual public row in the existing MM2 verifier. -/
inductive ByteClass where
  | terminal (digit : Nat)
  | prefix (digit : Nat)
  | save
  | saveFault (phase : ScannerPhase)
  | question (phase : ScannerPhase)
  | questionOpenFault
  | invalid (byte : UInt8)
deriving DecidableEq, Repr

namespace ByteClass

def row : ByteClass -> Atom
  | .terminal digit => compressedTerminalByteRow (65 + digit) digit
  | .prefix digit => compressedPrefixByteRow (84 + digit) digit
  | .save => compressedOwnedRuntimeRuleRow "save" compressedSaveRule
  | .saveFault phase => compressedSaveDisallowedPhaseRow phase.atom
  | .question phase => compressedQuestionAllowedPhaseRow phase.atom
  | .questionOpenFault =>
      compressedOwnedRuntimeRuleRow "question-open-fault"
        compressedQuestionOpenFaultRule
  | .invalid byte => compressedInvalidByteRow byte.toNat

end ByteClass

/-- Target classification is written independently of `authoredOutcome` and
uses the same public byte families that populate `compressedVerifierStaticRows`.
-/
def classifyByte (phase : ScannerPhase) (byte : UInt8) : ByteClass :=
  let code := byte.toNat
  if 65 <= code ∧ code <= 84 then
    .terminal (code - 65)
  else if 85 <= code ∧ code <= 89 then
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

/-- Dispatch is separate from classification.  It consumes no proof database
entry and creates no expanded normal-label trace. -/
def dispatchByte (phase : ScannerPhase) (_byte : UInt8) :
    ByteClass -> ScannerOutcome
  | .terminal digit =>
      .decoded [.step (compressedIndexValue phase.reversePrefix digit)] .completed
  | .prefix digit =>
      .decoded [] (.open (digit :: phase.reversePrefix))
  | .save => .decoded [.save] .between
  | .saveFault phase => .fault (.saveOutsideCompleted phase)
  | .question _ => .decoded [.unknown] .between
  | .questionOpenFault =>
      .fault (.questionInsideOpenIndex phase.reversePrefix)
  | .invalid byte => .fault (.invalidByte byte)

/-- One compact byte transition emits at most one DAG action.  In particular,
the byte-stage transformation cannot pre-expand a compressed proof. -/
theorem dispatchByte_actionCount_le_one
    (phase : ScannerPhase) (byte : UInt8) (byteClass : ByteClass) :
    (dispatchByte phase byte byteClass).actionCount <= 1 := by
  cases byteClass <;> simp [dispatchByte, ScannerOutcome.actionCount]

/-- The independently authored semantic action agrees exactly with the target
classification plus dispatch pair. -/
theorem authoredOutcome_eq_dispatch
    (phase : ScannerPhase) (byte : UInt8) :
    authoredOutcome phase byte =
      dispatchByte phase byte (classifyByte phase byte) := by
  cases phase <;>
    simp only [authoredOutcome, classifyByte, dispatchByte,
      ScannerPhase.reversePrefix, compressedIndexValue]
  all_goals
    by_cases terminalCase : 65 <= byte.toNat ∧ byte.toNat <= 84
    · simp [terminalCase]
    · by_cases prefixCase : 85 <= byte.toNat ∧ byte.toNat <= 89
      · simp [terminalCase, prefixCase]
      · by_cases saveCase : byte.toNat = 90
        · simp [saveCase]
        · by_cases questionCase : byte.toNat = 63
          · simp [questionCase]
          · simp [terminalCase, prefixCase, saveCase, questionCase]

/-! ## Two GSLTs and their path-valued realization -/

inductive SourceTerm where
  | request (occurrence : ByteOccurrence) (phase : ScannerPhase)
  | outcome (occurrence : ByteOccurrence) (outcome : ScannerOutcome)
deriving DecidableEq, Repr

inductive TargetTerm where
  | state (source : SourceTerm)
  | classified (source target : SourceTerm) (row : Atom)
deriving DecidableEq, Repr

inductive SourceStep : SourceTerm -> SourceTerm -> Prop where
  | run (occurrence : ByteOccurrence) (phase : ScannerPhase) :
      SourceStep (.request occurrence phase)
        (.outcome occurrence (authoredOutcome phase occurrence.byte))

/-- Target classification is independently determined by its own byte-class
and dispatch functions.  The source step is not mentioned here. -/
inductive TargetClassification : SourceTerm -> SourceTerm -> Prop where
  | classify (occurrence : ByteOccurrence) (phase : ScannerPhase) :
      TargetClassification (.request occurrence phase)
        (.outcome occurrence
          (dispatchByte phase occurrence.byte
            (classifyByte phase occurrence.byte)))

/-- The public MM2 inventory row that certifies a target classification.  The
row is derived from the target endpoints; it is not supplied by the source
proof or by a caller. -/
def targetClassificationRow : SourceTerm -> SourceTerm -> Option Atom
  | .request occurrence phase,
      .outcome outputOccurrence outcome =>
      if occurrence = outputOccurrence ∧
          dispatchByte phase occurrence.byte
              (classifyByte phase occurrence.byte) = outcome then
        some (classifyByte phase occurrence.byte).row
      else
        none
  | _, _ => none

/-- The row retained in an intermediate target state.  The fallback is never
reachable through `TargetClassification`; it makes the target carrier total
without manufacturing a row for an arbitrary pair of endpoints. -/
def classificationRow (source target : SourceTerm) : Atom :=
  match targetClassificationRow source target with
  | some row => row
  | none => .symbol "mm-no-classification-row"

/-- Every target classification has one exact verifier-row observation. -/
theorem targetClassificationRow_exact
    {source target : SourceTerm}
    (certificate : TargetClassification source target) :
    ∃ occurrence phase,
      source = .request occurrence phase ∧
      target = .outcome occurrence
        (dispatchByte phase occurrence.byte
          (classifyByte phase occurrence.byte)) ∧
      targetClassificationRow source target =
        some (classifyByte phase occurrence.byte).row := by
  cases certificate with
  | classify occurrence phase =>
      refine ⟨occurrence, phase, rfl, rfl, ?_⟩
      simp [targetClassificationRow]

/-- A classified target state retains the exact existing MM2 row selected by
its independently checkable classification, rather than the total carrier's
unreachable fallback. -/
theorem classificationRow_of_targetClassification
    {source target : SourceTerm}
    (certificate : TargetClassification source target) :
    ∃ occurrence phase,
      source = .request occurrence phase ∧
      target = .outcome occurrence
        (dispatchByte phase occurrence.byte
          (classifyByte phase occurrence.byte)) ∧
      classificationRow source target =
        (classifyByte phase occurrence.byte).row := by
  obtain ⟨occurrence, phase, sourceEqual, targetEqual, rowEqual⟩ :=
    targetClassificationRow_exact certificate
  refine ⟨occurrence, phase, sourceEqual, targetEqual, ?_⟩
  unfold classificationRow
  rw [rowEqual]

/-- Negative occurrence control: a classification row for one byte occurrence
cannot certify the same-looking byte at a different owner or position. -/
theorem targetClassificationRow_rejects_different_occurrence
    (left right : ByteOccurrence) (phase : ScannerPhase)
    (different : left ≠ right) :
    targetClassificationRow (.request left phase)
      (.outcome right
        (dispatchByte phase right.byte (classifyByte phase right.byte))) = none := by
  simp [targetClassificationRow, different]

inductive TargetStep : TargetTerm -> TargetTerm -> Prop where
  | classify {source target : SourceTerm}
      (certificate : TargetClassification source target) :
      TargetStep (.state source)
        (.classified source target (classificationRow source target))
  | dispatch {source target : SourceTerm}
      (certificate : TargetClassification source target) :
      TargetStep (.classified source target (classificationRow source target))
        (.state target)

def sourceGSLT : GSLT where
  Term := SourceTerm
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := SourceStep
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

def targetGSLT : GSLT where
  Term := TargetTerm
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := TargetStep
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

def mapTerm : SourceTerm -> TargetTerm
  | source => .state source

/-- A source transition supplies an independently checkable target
classification fact.  This proposition-valued bridge is deliberately proved
before it is lifted into the proof-relevant target execution path. -/
theorem sourceStep_has_targetClassification
    {source target : SourceTerm} :
    SourceStep source target -> TargetClassification source target := by
  intro step
  cases step with
  | run occurrence phase =>
      rw [authoredOutcome_eq_dispatch]
      exact TargetClassification.classify occurrence phase

/-- Target classification cannot invent a source outcome: it reconstructs the
authored source transition before either administrative target step runs. -/
theorem targetClassification_reflects_source
    {source target : SourceTerm} :
    TargetClassification source target -> SourceStep source target := by
  intro certificate
  cases certificate with
  | classify occurrence phase =>
      rw [← authoredOutcome_eq_dispatch]
      exact SourceStep.run occurrence phase

/-- One authored byte action lowers to two target steps: classification with
the concrete MM2 row, then dispatch. -/
def scannerRealization : OperationalRealization sourceGSLT targetGSLT where
  mapTerm := mapTerm
  mapEquiv := by
    intro left right equal
    subst right
    rfl
  mapStep := by
    intro source target step
    have certificate := sourceStep_has_targetClassification step
    exact .cons ⟨TargetStep.classify certificate⟩
      (.cons ⟨TargetStep.dispatch certificate⟩ (.refl _))

/-- The generated target route really has two administrative steps for every
source-owned byte occurrence. -/
theorem scannerRealization_step_length
    (occurrence : ByteOccurrence) (phase : ScannerPhase) :
    (scannerRealization.mapStep (SourceStep.run occurrence phase)).length = 2 := by
  rfl

/-- Every complete target classification/dispatch route starting at an image
request ends at the image of the one authorised source outcome. -/
theorem classified_dispatch_reflects_source
    {source target : SourceTerm}
    (certificate : TargetClassification source target) :
    sourceGSLT.Step source target :=
  targetClassification_reflects_source certificate

/-- OSLF sees this realization at the finite macro-step scale.  The closure
is explicit: this is not asserted to be the primitive target-step NTT. -/
def scannerReachabilityNTT :
    ForwardModalPredicateTheory.Hom
      (oslfForwardModalObject targetGSLT.closure)
      (oslfForwardModalObject sourceGSLT.closure) :=
  scannerRealization.closureOSLFPullback

/-! ## Exact MM2 row controls -/

/-- The terminal family maps directly to the verifier's terminal-byte row. -/
theorem terminal_classification_row_exact (digit : Nat) (bound : digit < 20) :
    (classifyByte .between (UInt8.ofNat (65 + digit))).row =
      compressedTerminalByteRow (65 + digit) digit := by
  simp only [classifyByte, ByteClass.row]
  have byteValue : (UInt8.ofNat (65 + digit)).toNat = 65 + digit := by
    simp
    omega
  rw [byteValue]
  rw [if_pos (by omega)]
  rw [show 65 + digit - 65 = digit by omega]

/-- The prefix family maps directly to the verifier's prefix-byte row. -/
theorem prefix_classification_row_exact
    (digit : Nat) (lower : 1 <= digit) (upper : digit <= 5) :
    (classifyByte .between (UInt8.ofNat (84 + digit))).row =
      compressedPrefixByteRow (84 + digit) digit := by
  simp only [classifyByte, ByteClass.row]
  have byteValue : (UInt8.ofNat (84 + digit)).toNat = 84 + digit := by
    simp
    omega
  rw [byteValue]
  rw [if_neg (by omega), if_pos (by omega)]
  rw [show 84 + digit - 84 = digit by omega]

/-- Negative control: a terminal byte cannot be classified as the adjacent
terminal row.  This rejects off-by-one target inventories. -/
theorem terminal_digit_mutation_rejected (digit : Nat) (bound : digit < 19) :
    classifyByte .between (UInt8.ofNat (65 + digit)) ≠ .terminal (digit + 1) := by
  rw [show classifyByte .between (UInt8.ofNat (65 + digit)) = .terminal digit by
    simp only [classifyByte]
    have byteValue : (UInt8.ofNat (65 + digit)).toNat = 65 + digit := by
      simp
      omega
    rw [byteValue]
    rw [if_pos (by omega)]
    rw [show 65 + digit - 65 = digit by omega]]
  intro equal
  injection equal with digitEqual
  omega

/-- Negative control: `Z` at the initial between-steps phase cannot take the
successful-save branch. -/
theorem initial_save_is_not_success :
    classifyByte .between (UInt8.ofNat 90) ≠ .save := by
  decide

#print axioms authoredOutcome_toSourceResult_eq_decodeByte
#print axioms authoredOutcome_eq_dispatch
#print axioms dispatchByte_actionCount_le_one
#print axioms targetClassificationRow_exact
#print axioms classificationRow_of_targetClassification
#print axioms targetClassificationRow_rejects_different_occurrence
#print axioms scannerRealization
#print axioms scannerRealization_step_length
#print axioms classified_dispatch_reflects_source
#print axioms scannerReachabilityNTT
#print axioms terminal_classification_row_exact
#print axioms prefix_classification_row_exact
#print axioms terminal_digit_mutation_rejected
#print axioms initial_save_is_not_success

end Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT
