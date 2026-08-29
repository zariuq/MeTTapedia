import Mettapedia.Languages.Metamath.MM2DataEncoding
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveExecution

/-!
# Incremental compressed Metamath proof execution in MM2

Compressed proof words remain compact source data.  This module interprets
their bytes inside the MM2 verifier: U--Y bytes extend a compact Appendix-B
prefix, A--T bytes select a heap entry, and Z saves the current proof-node
identity.  It never expands the whole compressed program into a normal-label
trace.

The current microkernel handles proof-valued heap entries, exact terminal
stack acceptance, and an occurrence-preserving bridge that delegates
assertion-valued heap entries to the ordinary normal-proof assertion machine
before resuming compact scanning.  Continuous composition with that normal
machine, strict faults for every hostile byte/reference shape, and
source-theorem reflection remain open obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-! ## Compact Appendix-B indices -/

/-- A step index remains logarithmic in its value.  Prefix digits are stored
least-significant first so another U--Y byte is a constant-size cons. -/
def compressedIndexCodeAtom
    (reversePrefixDigits : List Nat) (terminalDigit : Nat) : Atom :=
  .expression
    [.symbol "mm-compressed-index-code",
      listAtom natAtom reversePrefixDigits, natAtom terminalDigit]

/-- Mathematical value denoted by the compact target representation. -/
def compressedIndexValue
    (reversePrefixDigits : List Nat) (terminalDigit : Nat) : Nat :=
  20 * reversePrefixDigits.foldr (fun digit accumulator =>
    5 * accumulator + digit) 0 + terminalDigit

def compressedPrefixValue (reversePrefixDigits : List Nat) : Nat :=
  reversePrefixDigits.foldr (fun digit accumulator =>
    5 * accumulator + digit) 0

/-- Reversing the source-order prefix is representation-only: the target's
constant-time cons representation denotes exactly the source Appendix-B
left-to-right base-5 accumulator. -/
theorem compressedIndexValue_reverse_eq_sourceAccumulator
    (prefixDigits : List Nat) (terminalDigit : Nat) :
    compressedIndexValue prefixDigits.reverse terminalDigit =
      20 * prefixDigits.foldl
        (fun accumulator digit => 5 * accumulator + digit) 0 +
        terminalDigit := by
  simp [compressedIndexValue]

/-- A typed counter code separates the compact representation from the Atom
surface used by the MM2 program. -/
structure CompressedIndexCode where
  reversePrefixDigits : List Nat
  terminalDigit : Nat
deriving DecidableEq, Repr

namespace CompressedIndexCode

def Valid (code : CompressedIndexCode) : Prop :=
  (∀ digit ∈ code.reversePrefixDigits, 1 ≤ digit ∧ digit ≤ 5) ∧
    code.terminalDigit < 20

def value (code : CompressedIndexCode) : Nat :=
  compressedIndexValue code.reversePrefixDigits code.terminalDigit

def atom (code : CompressedIndexCode) : Atom :=
  compressedIndexCodeAtom code.reversePrefixDigits code.terminalDigit

/-- Structural decoder for the typed compact-code atom.  Validity is a
separate semantic property; decoding only recovers the two represented
fields. -/
def decodeCompressedIndexCodeAtom : Atom → Option CompressedIndexCode
  | .expression [.symbol tag, encodedPrefix, encodedTerminal] =>
      if tag = "mm-compressed-index-code" then do
        let reversePrefixDigits ←
          decodeListAtom decodeNatAtom encodedPrefix
        let terminalDigit ← decodeNatAtom encodedTerminal
        pure ⟨reversePrefixDigits, terminalDigit⟩
      else
        none
  | _ => none

@[simp] theorem decodeCompressedIndexCodeAtom_atom
    (code : CompressedIndexCode) :
    decodeCompressedIndexCodeAtom code.atom = some code := by
  rcases code with ⟨reversePrefixDigits, terminalDigit⟩
  simp [decodeCompressedIndexCodeAtom, atom, compressedIndexCodeAtom]

/-- Decode the natural number denoted by a compact-code atom. -/
def decodeCompressedIndexAtom (encoded : Atom) : Option Nat :=
  CompressedIndexCode.value <$> decodeCompressedIndexCodeAtom encoded

def zero : CompressedIndexCode where
  reversePrefixDigits := []
  terminalDigit := 0

/-- Increment the least-significant-first bijective-base-5 prefix. -/
def incrementReversePrefix : List Nat → List Nat
  | [] => [1]
  | digit :: digits =>
      if digit < 5 then
        (digit + 1) :: digits
      else
        1 :: incrementReversePrefix digits

theorem incrementReversePrefix_valid
    (digits : List Nat)
    (valid : ∀ digit ∈ digits, 1 ≤ digit ∧ digit ≤ 5) :
    ∀ digit ∈ incrementReversePrefix digits, 1 ≤ digit ∧ digit ≤ 5 := by
  induction digits with
  | nil =>
      simp [incrementReversePrefix]
  | cons head tail induction =>
      have headValid := valid head (by simp)
      have tailValid : ∀ digit ∈ tail, 1 ≤ digit ∧ digit ≤ 5 := by
        intro digit member
        exact valid digit (by simp [member])
      by_cases less : head < 5
      · intro digit member
        change digit ∈
          (if head < 5 then (head + 1) :: tail
            else 1 :: incrementReversePrefix tail) at member
        rw [if_pos less] at member
        rcases List.mem_cons.mp member with rfl | member
        · omega
        · exact tailValid digit member
      · have head_eq : head = 5 := by omega
        intro digit member
        change digit ∈
          (if head < 5 then (head + 1) :: tail
            else 1 :: incrementReversePrefix tail) at member
        rw [if_neg less] at member
        rcases List.mem_cons.mp member with rfl | member
        · omega
        · exact induction tailValid digit member

theorem incrementReversePrefix_value
    (digits : List Nat)
    (valid : ∀ digit ∈ digits, 1 ≤ digit ∧ digit ≤ 5) :
    compressedPrefixValue (incrementReversePrefix digits) =
      compressedPrefixValue digits + 1 := by
  induction digits with
  | nil =>
      rfl
  | cons head tail induction =>
      have headValid := valid head (by simp)
      have tailValid : ∀ digit ∈ tail, 1 ≤ digit ∧ digit ≤ 5 := by
        intro digit member
        exact valid digit (by simp [member])
      by_cases less : head < 5
      · change
          compressedPrefixValue
              (if head < 5 then (head + 1) :: tail
                else 1 :: incrementReversePrefix tail) =
            compressedPrefixValue (head :: tail) + 1
        rw [if_pos less]
        change
          5 * compressedPrefixValue tail + (head + 1) =
            5 * compressedPrefixValue tail + head + 1
        omega
      · have head_eq : head = 5 := by omega
        change
          compressedPrefixValue
              (if head < 5 then (head + 1) :: tail
                else 1 :: incrementReversePrefix tail) =
            compressedPrefixValue (head :: tail) + 1
        rw [if_neg less]
        change
          5 * compressedPrefixValue (incrementReversePrefix tail) + 1 =
            5 * compressedPrefixValue tail + head + 1
        rw [induction tailValid, head_eq]
        omega

def next (code : CompressedIndexCode) : CompressedIndexCode :=
  if code.terminalDigit < 19 then
    { code with terminalDigit := code.terminalDigit + 1 }
  else
    { reversePrefixDigits :=
        incrementReversePrefix code.reversePrefixDigits
      terminalDigit := 0 }

theorem zero_valid : zero.Valid := by
  simp [zero, Valid]

theorem zero_value : zero.value = 0 := by
  rfl

theorem next_valid {code : CompressedIndexCode} (valid : code.Valid) :
    code.next.Valid := by
  rcases valid with ⟨prefixValid, terminalValid⟩
  by_cases less : code.terminalDigit < 19
  · unfold next
    rw [if_pos less]
    change
      (∀ digit ∈ code.reversePrefixDigits, 1 ≤ digit ∧ digit ≤ 5) ∧
        code.terminalDigit + 1 < 20
    exact ⟨prefixValid, by omega⟩
  · have terminal_eq : code.terminalDigit = 19 := by omega
    unfold next
    rw [if_neg less]
    change
      (∀ digit ∈ incrementReversePrefix code.reversePrefixDigits,
          1 ≤ digit ∧ digit ≤ 5) ∧
        0 < 20
    exact
      ⟨incrementReversePrefix_valid code.reversePrefixDigits prefixValid,
        by omega⟩

theorem next_value {code : CompressedIndexCode} (valid : code.Valid) :
    code.next.value = code.value + 1 := by
  rcases valid with ⟨prefixValid, terminalValid⟩
  by_cases less : code.terminalDigit < 19
  · unfold next
    rw [if_pos less]
    unfold value compressedIndexValue
    dsimp
    omega
  · have terminal_eq : code.terminalDigit = 19 := by omega
    unfold next
    rw [if_neg less]
    unfold value compressedIndexValue
    dsimp
    rw [terminal_eq]
    change
      20 * compressedPrefixValue
          (incrementReversePrefix code.reversePrefixDigits) =
        20 * compressedPrefixValue code.reversePrefixDigits + 19 + 1
    rw [incrementReversePrefix_value code.reversePrefixDigits prefixValid]
    omega

/-- Canonical compact code for an internal natural-number position. -/
def ofNat : Nat → CompressedIndexCode
  | 0 => zero
  | position + 1 => (ofNat position).next

theorem ofNat_valid (position : Nat) : (ofNat position).Valid := by
  induction position with
  | zero => exact zero_valid
  | succ position induction =>
      exact next_valid induction

theorem ofNat_value (position : Nat) : (ofNat position).value = position := by
  induction position with
  | zero => exact zero_value
  | succ position induction =>
      rw [ofNat, next_value (ofNat_valid position), induction]

@[simp] theorem decodeCompressedIndexAtom_ofNat_atom (position : Nat) :
    decodeCompressedIndexAtom (ofNat position).atom = some position := by
  simp [decodeCompressedIndexAtom, ofNat_value]

end CompressedIndexCode

/-! ## Proof-occurrence surface -/

/-- Shared target surface for a hypothesis occurrence allocated by the
compressed header loader.  The surface-level form is reusable by executable
templates; `compressedHeaderOccurrenceAtom` below is its canonical typed
instance. -/
def compressedHeaderOccurrenceSurface
    (proofOwner headerPosition : Atom) : Atom :=
  .expression
    [.symbol "mm-compressed-header-occurrence", proofOwner, headerPosition]

/-- Canonical occurrence allocated by the source-indexed header item at
`headerPosition`. -/
def compressedHeaderOccurrenceAtom
    (proofOwner : Atom) (headerPosition : Nat) : Atom :=
  compressedHeaderOccurrenceSurface proofOwner
    (CompressedIndexCode.ofNat headerPosition).atom

/-- Shared target surface for an assertion occurrence allocated at one
compressed action position. -/
def compressedAssertionOccurrenceSurface
    (proofPosition assertionLabel : Atom) : Atom :=
  .expression
    [.symbol "mm-assertion-occurrence", proofPosition, assertionLabel]

/-- Canonical occurrence allocated by an assertion action at
`proofPosition`. -/
def compressedAssertionOccurrenceAtom
    (proofPosition : Nat) (assertionLabel : String) : Atom :=
  compressedAssertionOccurrenceSurface
    (CompressedIndexCode.ofNat proofPosition).atom
    (stringAtom assertionLabel)

theorem compressedIndexCode_zero_value :
    compressedIndexValue [] 0 = 0 := by
  rfl

theorem compressedIndexCode_twenty_value :
    compressedIndexValue [1] 0 = 20 := by
  rfl

def compressedIndexSuccessorRow
    (owner current next : Atom) : Atom :=
  .expression
    [.symbol "mm-compressed-index-successor", owner, current, next]

/-- Generate an exact finite successor spine without expanding any proof
action.  The construction is linear in the requested structural bound. -/
def compressedIndexSuccessorRowsFrom (owner : Atom) :
    Nat → CompressedIndexCode → List Atom
  | 0, _ => []
  | count + 1, current =>
      compressedIndexSuccessorRow owner current.atom current.next.atom ::
        compressedIndexSuccessorRowsFrom owner count current.next

def compressedIndexSuccessorRows (owner : Atom) (count : Nat) : List Atom :=
  compressedIndexSuccessorRowsFrom owner count CompressedIndexCode.zero

@[simp] theorem compressedIndexSuccessorRowsFrom_length
    (owner : Atom) (count : Nat) (current : CompressedIndexCode) :
    (compressedIndexSuccessorRowsFrom owner count current).length = count := by
  induction count generalizing current with
  | zero => rfl
  | succ count induction =>
      simp [compressedIndexSuccessorRowsFrom, induction]

@[simp] theorem compressedIndexSuccessorRows_length
    (owner : Atom) (count : Nat) :
    (compressedIndexSuccessorRows owner count).length = count := by
  simp [compressedIndexSuccessorRows]

def compressedStackOwner (proofOwner : Atom) : Atom :=
  .expression [.symbol "mm-compressed-stack-owner", proofOwner]

def compressedHeapOwner (proofOwner : Atom) : Atom :=
  .expression [.symbol "mm-compressed-heap-owner", proofOwner]

def compressedNodeOwner (proofOwner : Atom) : Atom :=
  .expression [.symbol "mm-compressed-node-owner", proofOwner]

/-! ## Verifier-owned byte classification -/

def compressedTerminalByteRow (byte terminalDigit : Nat) : Atom :=
  .expression
    [.symbol "mm-compressed-terminal-byte", natAtom byte,
      natAtom terminalDigit]

def compressedPrefixByteRow (byte prefixDigit : Nat) : Atom :=
  .expression
    [.symbol "mm-compressed-prefix-byte", natAtom byte,
      natAtom prefixDigit]

def compressedTerminalByteRows : List Atom :=
  (List.range 20).map fun digit =>
    compressedTerminalByteRow (65 + digit) digit

def compressedPrefixByteRows : List Atom :=
  (List.range 5).map fun offset =>
    compressedPrefixByteRow (85 + offset) (offset + 1)

private def compressedBetweenPhase : Atom :=
  .symbol "mm-compressed-between-steps"

private def compressedOpenPhase : Atom :=
  .symbol "mm-compressed-open-index"

private def compressedJustCompletedPhase : Atom :=
  .symbol "mm-compressed-just-completed-step"

private def compressedFinalPhaseRows : List Atom :=
  [.expression
      [.symbol "mm-compressed-final-phase", compressedBetweenPhase],
   .expression
      [.symbol "mm-compressed-final-phase", compressedJustCompletedPhase]]

/-! ## Canonical surface helpers -/

private def sinkSurface : Sink → Atom
  | .add atom => .expression [.symbol "+", atom]
  | .remove atom => .expression [.symbol "-", atom]
  | .head count atom =>
      .expression [.symbol "head", natAtom count, atom]
  | .tail count atom =>
      .expression [.symbol "tail", natAtom count, atom]

private def outputSurface (sinks : List Sink) : Atom :=
  .expression (.symbol "O" :: sinks.map sinkSurface)

private def inputSurface (patterns : List Atom) : Atom :=
  .expression (.symbol "," :: patterns)

private def compressedOwnedRuleTemplate (kind variableName : String) : Atom :=
  .expression
    [.symbol "mm-compressed-owned-runtime-rule", .symbol kind,
      .var variableName]

def compressedOwnedRuntimeRuleRow (kind : String) (rule : Atom) : Atom :=
  .expression [.symbol "mm-compressed-owned-runtime-rule", .symbol kind, rule]

private def compressedPrefixRuleCaptureTemplate : Atom :=
  compressedOwnedRuleTemplate "prefix" "compressed-prefix-rule"

private def compressedTerminalRuleCaptureTemplate : Atom :=
  compressedOwnedRuleTemplate "terminal" "compressed-terminal-rule"

private def compressedProofRuleCaptureTemplate : Atom :=
  compressedOwnedRuleTemplate "proof" "compressed-proof-rule"

private def compressedSaveRuleCaptureTemplate : Atom :=
  compressedOwnedRuleTemplate "save" "compressed-save-rule"

private def compressedAssertionLaunchRuleCaptureTemplate : Atom :=
  compressedOwnedRuleTemplate "assertion-launch" "compressed-assertion-launch-rule"

/-- Verifier-owned opaque assertion rejoin continuation.  Target-level
handoff transforms may require this row at the exact normal-result completion
boundary; compact source data never constructs the executable rule value. -/
def compressedAssertionRejoinRuleCaptureTemplate : Atom :=
  compressedOwnedRuleTemplate "assertion-rejoin" "compressed-assertion-rejoin-rule"

private def compressedAssertionResumeRuleCaptureTemplate : Atom :=
  compressedOwnedRuleTemplate "assertion-resume" "compressed-assertion-resume-rule"

private def compressedHeapLookupAdvanceRuleCaptureTemplate : Atom :=
  compressedOwnedRuleTemplate "lookup-advance" "compressed-lookup-advance-rule"

private def compressedHeapLookupFaultRuleCaptureTemplate : Atom :=
  compressedOwnedRuleTemplate "lookup-fault" "compressed-lookup-fault-rule"

private def compressedWordAdvanceRuleCaptureTemplate : Atom :=
  compressedOwnedRuleTemplate "word-advance" "compressed-word-advance-rule"

private def compressedAcceptRuleCaptureTemplate : Atom :=
  compressedOwnedRuleTemplate "accept" "compressed-accept-rule"

private def compressedIncompleteRuleCaptureTemplate : Atom :=
  compressedOwnedRuleTemplate "incomplete" "compressed-incomplete-rule"

private def compressedInvalidByteRuleCaptureTemplate : Atom :=
  compressedOwnedRuleTemplate "invalid-byte" "compressed-invalid-byte-rule"

private def compressedQuestionRuleCaptureTemplate : Atom :=
  compressedOwnedRuleTemplate "question" "compressed-question-rule"

private def compressedQuestionOpenFaultRuleCaptureTemplate : Atom :=
  compressedOwnedRuleTemplate "question-open-fault"
    "compressed-question-open-fault-rule"

private def compressedSaveFaultRuleCaptureTemplate : Atom :=
  compressedOwnedRuleTemplate "save-fault" "compressed-save-fault-rule"

/-! ## Incremental scanner and compact proof machine -/

private def compressedStartLocation : Atom :=
  .expression [.symbol "05", .symbol "mm-compressed-start"]

private def compressedPrefixLocation : Atom :=
  .expression [.symbol "06", .symbol "mm-compressed-prefix"]

private def compressedTerminalLocation : Atom :=
  .expression [.symbol "07", .symbol "mm-compressed-terminal"]

private def compressedInvalidByteLocation : Atom :=
  .expression [.symbol "07", .symbol "mm-compressed-invalid-byte"]

private def compressedQuestionOpenFaultLocation : Atom :=
  .expression [.symbol "07", .symbol "mm-compressed-question-open-fault"]

private def compressedQuestionLocation : Atom :=
  .expression [.symbol "07", .symbol "mm-compressed-question-step"]

private def compressedProofStepLocation : Atom :=
  .expression [.symbol "08", .symbol "mm-compressed-proof-step"]

private def compressedSaveLocation : Atom :=
  .expression [.symbol "09", .symbol "mm-compressed-save"]

private def compressedSaveFaultLocation : Atom :=
  .expression [.symbol "09", .symbol "mm-compressed-save-phase-fault"]

private def compressedWordAdvanceLocation : Atom :=
  .expression [.symbol "10", .symbol "mm-compressed-word-advance"]

private def compressedAcceptLocation : Atom :=
  .expression [.symbol "11", .symbol "mm-compressed-accept"]

private def compressedIncompleteLocation : Atom :=
  .expression [.symbol "11", .symbol "mm-compressed-incomplete"]

private def compressedHeapLookupAdvanceLocation : Atom :=
  .expression [.symbol "09", .symbol "mm-compressed-heap-lookup-advance"]

private def compressedHeapLookupFaultLocation : Atom :=
  .expression [.symbol "08", .symbol "mm-compressed-heap-lookup-fault"]

private def compressedStartSelf : Atom :=
  .expression
    [.symbol "exec", compressedStartLocation,
      .var "start-input", .var "start-output"]

private def compressedInitialControlTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-control", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "stack-position"]

private def compressedBodyWordTemplate : Atom :=
  .expression
    [.symbol "mm-row", stringAtom "compressed-body-word",
      .var "proof-owner", .var "word-position", .var "word"]

private def compressedMachineTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-machine", .var "scope-owner",
      .var "proof-owner", .var "heap-next", .var "node-next",
      .var "stack-position"]

private def compressedInitialScanTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-scan", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "word",
      compressedBetweenPhase, listAtom natAtom []]

private def compressedStartPatterns : List Atom :=
  [compressedStartSelf, compressedInitialControlTemplate,
   compressedBodyWordTemplate,
   compressedMachineTemplate]

private def compressedStartSinks : List Sink :=
  [.remove compressedInitialControlTemplate,
   .add compressedInitialScanTemplate]

def compressedStartRule : Atom :=
  .expression
    [.symbol "exec", compressedStartLocation,
      inputSurface compressedStartPatterns,
      outputSurface compressedStartSinks]

def compressedStartDirective : SourceExecFact where
  atom := compressedStartRule
  loc := compressedStartLocation
  rule :=
    { priority := 5
      name := "mm-compressed-start"
      input := .compat (mkPattern compressedStartPatterns)
      guards := []
      tmpl := mkTemplate compressedStartSinks }

theorem extract_compressedStartRule_exact :
    extractSupportedSourceExecFact compressedStartRule =
      some compressedStartDirective := by
  rfl

private def compressedByteScanTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-scan", .var "scope-owner",
      .var "proof-owner", .var "word-position",
      .expression
        [.symbol consTag, .var "compressed-byte", .var "remaining-bytes"],
      .var "compressed-phase", .var "reverse-prefix"]

private def compressedPrefixClassTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-prefix-byte", .var "compressed-byte",
      .var "prefix-digit"]

private def compressedPrefixNextScanTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-scan", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes",
      compressedOpenPhase,
      .expression
        [.symbol consTag, .var "prefix-digit", .var "reverse-prefix"]]

private def compressedPrefixSelf : Atom :=
  .expression
    [.symbol "exec", compressedPrefixLocation,
      .var "prefix-input", .var "prefix-output"]

private def compressedPrefixPatterns : List Atom :=
  [compressedPrefixSelf, compressedByteScanTemplate,
   compressedPrefixClassTemplate]

private def compressedPrefixSinks : List Sink :=
  [.add compressedPrefixSelf,
   .remove compressedByteScanTemplate,
   .add compressedPrefixNextScanTemplate]

def compressedPrefixRule : Atom :=
  .expression
    [.symbol "exec", compressedPrefixLocation,
      inputSurface compressedPrefixPatterns,
      outputSurface compressedPrefixSinks]

def compressedPrefixDirective : SourceExecFact where
  atom := compressedPrefixRule
  loc := compressedPrefixLocation
  rule :=
    { priority := 6
      name := "mm-compressed-prefix"
      input := .compat (mkPattern compressedPrefixPatterns)
      guards := []
      tmpl := mkTemplate compressedPrefixSinks }

theorem extract_compressedPrefixRule_exact :
    extractSupportedSourceExecFact compressedPrefixRule =
      some compressedPrefixDirective := by
  rfl

private def compressedInvalidByteClassTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-invalid-byte", .var "compressed-byte"]

private def compressedInvalidByteFaultTemplate : Atom :=
  .expression
    [.symbol "mm-proof-fault", .var "scope-owner", .var "proof-owner",
      .var "word-position", .symbol "compressed-invalid-byte",
      .var "compressed-byte", .var "compressed-phase",
      .var "reverse-prefix"]

private def compressedInvalidByteSelf : Atom :=
  .expression
    [.symbol "exec", compressedInvalidByteLocation,
      .var "invalid-byte-input", .var "invalid-byte-output"]

private def compressedInvalidBytePatterns : List Atom :=
  [compressedInvalidByteSelf, compressedByteScanTemplate,
   compressedInvalidByteClassTemplate]

private def compressedInvalidByteSinks : List Sink :=
  [.remove compressedByteScanTemplate,
   .add compressedInvalidByteFaultTemplate]

def compressedInvalidByteRule : Atom :=
  .expression
    [.symbol "exec", compressedInvalidByteLocation,
      inputSurface compressedInvalidBytePatterns,
      outputSurface compressedInvalidByteSinks]

def compressedInvalidByteDirective : SourceExecFact where
  atom := compressedInvalidByteRule
  loc := compressedInvalidByteLocation
  rule :=
    { priority := 7
      name := "mm-compressed-invalid-byte"
      input := .compat (mkPattern compressedInvalidBytePatterns)
      guards := []
      tmpl := mkTemplate compressedInvalidByteSinks }

theorem extract_compressedInvalidByteRule_exact :
    extractSupportedSourceExecFact compressedInvalidByteRule =
      some compressedInvalidByteDirective := by
  rfl

private def compressedTerminalClassTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-terminal-byte", .var "compressed-byte",
      .var "terminal-digit"]

private def compressedStepPendingTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-step-pending", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes",
      .expression
        [.symbol "mm-compressed-index-code", .var "reverse-prefix",
          .var "terminal-digit"]]

/-- Heap lookup is a bounded cursor walk.  Its target stays compact while the
cursor advances only through verifier-visible successor rows.  The current
heap frontier in `mm-compressed-machine` is therefore an explicit failure
boundary rather than an absence test. -/
private def compressedHeapLookupTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-heap-lookup", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes",
      .var "compressed-index",
      .var "heap-lookup-cursor"]

private def compressedHeapLookupInitialTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-heap-lookup", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes",
      .expression
        [.symbol "mm-compressed-index-code", .var "reverse-prefix",
          .var "terminal-digit"],
      compressedIndexCodeAtom [] 0]

private def compressedHeapLookupExactTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-heap-lookup", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes",
      .var "compressed-index", .var "compressed-index"]

private def compressedHeapLookupSuccessorTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-index-successor",
      .expression [.symbol "mm-compressed-heap-owner", .var "proof-owner"],
      .var "heap-lookup-cursor", .var "next-heap-lookup-cursor"]

private def compressedHeapLookupNextTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-heap-lookup", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes",
      .var "compressed-index", .var "next-heap-lookup-cursor"]

/-! ## Assertion-valued heap references

The normal assertion microkernel is reused through its public MM2 vocabulary.
Compact stack indices remain compact atoms; the normal machine treats those
indices parametrically and returns its result through an exact continuation.
-/

private def compressedAssertionLaunchLocation : Atom :=
  .expression [.symbol "08", .symbol "mm-compressed-proof-step-assertion"]

private def compressedAssertionRejoinLocation : Atom :=
  .expression [.symbol "32", .symbol "mm-compressed-assertion-rejoin"]

private def compressedAssertionResumeLocation : Atom :=
  .expression [.symbol "34", .symbol "mm-compressed-assertion-resume"]

private def compressedHeapAssertionTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-heap-assertion", .var "proof-owner",
      .var "compressed-index", .var "assertion-position",
      .var "assertion-label"]

private def compressedAssertionHeaderTemplate : Atom :=
  .expression
    [.symbol "mm-assertion-header", .var "scope-owner",
      .var "assertion-position", .var "assertion-label",
      .var "assertion-hypothesis-count"]

private def compressedAssertionPCTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-assertion-pc", .var "word-position",
      .var "remaining-bytes", .var "compressed-index"]

private def compressedAssertionNextPCTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-assertion-done",
      compressedAssertionPCTemplate]

private def compressedAssertionNormalControlTemplate : Atom :=
  .expression
    [.symbol "mm-normal-control", .var "scope-owner", .var "proof-owner",
      compressedAssertionPCTemplate, .var "stack-position"]

/-- The compact assertion bridge enters the existing normal assertion machine
at an occurrence-indexed normal control.  It asks the surrounding
verifier-owned activation layer to install that scheduler; compact source data
never carries an executable normal rule. -/
def compressedAssertionNormalReloadRequest : Atom :=
  .expression [.symbol "mm-reload-compressed-normal-dispatch",
    .var "proof-owner"]

private def compressedAssertionNormalLabelRowTemplate : Atom :=
  .expression
    [.symbol "mm-linked-row", stringAtom "normal-proof-label",
      .var "proof-owner", compressedAssertionPCTemplate,
      compressedAssertionNextPCTemplate, .var "assertion-label"]

private def compressedAssertionContextTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-assertion-context", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes",
      compressedAssertionPCTemplate, compressedAssertionNextPCTemplate,
      .var "assertion-label", .var "heap-next", .var "node-next"]

private def compressedAssertionResumeTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-assertion-resume", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes"]

private def compressedAssertionReturnedControlTemplate : Atom :=
  .expression
    [.symbol "mm-normal-control", .var "scope-owner", .var "proof-owner",
      compressedAssertionNextPCTemplate, .var "next-stack-position"]

private def compressedAssertionOccurrenceTemplate : Atom :=
  compressedAssertionOccurrenceSurface compressedAssertionPCTemplate
    (.var "assertion-label")

private def compressedAssertionReturnedStackTemplate : Atom :=
  .expression
    [.symbol "mm-stack-cell", .var "proof-owner", .var "stack-base",
      .var "result-formula", compressedAssertionOccurrenceTemplate]

private def compressedAssertionNormalStackSuccessorTemplate : Atom :=
  .expression
    [.symbol "mm-index-successor", .var "proof-owner", .var "stack-base",
      .var "next-stack-position"]

private def compressedNodeSuccessorTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-index-successor",
      .expression [.symbol "mm-compressed-node-owner", .var "proof-owner"],
      .var "node-next", .var "next-node"]

private def compressedAssertionResultNodeTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-node", .var "proof-owner", .var "node-next",
      .var "result-formula", compressedAssertionOccurrenceTemplate]

private def compressedAssertionResultStackTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-stack-cell", .var "proof-owner",
      .var "stack-base", .var "node-next"]

private def compressedAssertionReturnedMachineTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-machine", .var "scope-owner",
      .var "proof-owner", .var "heap-next", .var "next-node",
      .var "next-stack-position"]

private def compressedAssertionRejoinSelf : Atom :=
  .expression
    [.symbol "exec", compressedAssertionRejoinLocation,
      .var "assertion-rejoin-input", .var "assertion-rejoin-output"]

private def compressedAssertionRejoinPatterns : List Atom :=
  [compressedAssertionRejoinSelf, compressedAssertionContextTemplate,
   compressedAssertionReturnedControlTemplate,
   compressedAssertionReturnedStackTemplate,
   compressedAssertionNormalStackSuccessorTemplate,
   compressedNodeSuccessorTemplate,
   compressedAssertionNormalLabelRowTemplate,
   compressedAssertionResumeRuleCaptureTemplate]

private def compressedAssertionRejoinSinks : List Sink :=
  [.remove compressedAssertionContextTemplate,
   .remove compressedAssertionReturnedControlTemplate,
   .remove compressedAssertionNormalLabelRowTemplate,
   .add compressedAssertionReturnedMachineTemplate,
   .add compressedAssertionResultNodeTemplate,
   .add compressedAssertionResultStackTemplate,
   .add compressedAssertionResumeTemplate,
   .add (.var "compressed-assertion-resume-rule")]

def compressedAssertionRejoinRule : Atom :=
  .expression
    [.symbol "exec", compressedAssertionRejoinLocation,
      inputSurface compressedAssertionRejoinPatterns,
      outputSurface compressedAssertionRejoinSinks]

def compressedAssertionRejoinDirective : SourceExecFact where
  atom := compressedAssertionRejoinRule
  loc := compressedAssertionRejoinLocation
  rule :=
    { priority := 32
      name := "mm-compressed-assertion-rejoin"
      input := .compat (mkPattern compressedAssertionRejoinPatterns)
      guards := []
      tmpl := mkTemplate compressedAssertionRejoinSinks }

theorem extract_compressedAssertionRejoinRule_exact :
    extractSupportedSourceExecFact compressedAssertionRejoinRule =
      some compressedAssertionRejoinDirective := by
  rfl

private def compressedAssertionLaunchSelf : Atom :=
  .expression
    [.symbol "exec", compressedAssertionLaunchLocation,
      .var "assertion-launch-input", .var "assertion-launch-output"]

private def compressedAssertionLaunchPatterns : List Atom :=
  [compressedAssertionLaunchSelf, compressedStepPendingTemplate,
   compressedHeapLookupExactTemplate,
   compressedHeapAssertionTemplate, compressedMachineTemplate,
   compressedAssertionHeaderTemplate,
   compressedAssertionRejoinRuleCaptureTemplate]

private def compressedAssertionLaunchSinks : List Sink :=
  [.remove compressedStepPendingTemplate,
   .remove compressedHeapLookupExactTemplate,
   .remove compressedMachineTemplate,
   .add compressedAssertionContextTemplate,
   .add compressedAssertionNormalControlTemplate,
   .add compressedAssertionNormalLabelRowTemplate,
   .add compressedAssertionNormalReloadRequest,
   .add (.var "compressed-assertion-rejoin-rule")]

def compressedAssertionLaunchRule : Atom :=
  .expression
    [.symbol "exec", compressedAssertionLaunchLocation,
      inputSurface compressedAssertionLaunchPatterns,
      outputSurface compressedAssertionLaunchSinks]

def compressedAssertionLaunchDirective : SourceExecFact where
  atom := compressedAssertionLaunchRule
  loc := compressedAssertionLaunchLocation
  rule :=
    { priority := 8
      name := "mm-compressed-proof-step-assertion"
      input := .compat (mkPattern compressedAssertionLaunchPatterns)
      guards := []
      tmpl := mkTemplate compressedAssertionLaunchSinks }

theorem extract_compressedAssertionLaunchRule_exact :
    extractSupportedSourceExecFact compressedAssertionLaunchRule =
      some compressedAssertionLaunchDirective := by
  rfl

private def compressedTerminalSelf : Atom :=
  .expression
    [.symbol "exec", compressedTerminalLocation,
      .var "terminal-input", .var "terminal-output"]

private def compressedTerminalPatterns : List Atom :=
  [compressedTerminalSelf, compressedByteScanTemplate,
   compressedTerminalClassTemplate, compressedProofRuleCaptureTemplate,
   compressedAssertionLaunchRuleCaptureTemplate,
   compressedHeapLookupFaultRuleCaptureTemplate,
   compressedHeapLookupAdvanceRuleCaptureTemplate]

private def compressedTerminalSinks : List Sink :=
  [.remove compressedByteScanTemplate,
   .add (.var "compressed-proof-rule"),
   .add (.var "compressed-assertion-launch-rule"),
   .add (.var "compressed-lookup-fault-rule"),
   .add (.var "compressed-lookup-advance-rule"),
   .add compressedStepPendingTemplate,
   .add compressedHeapLookupInitialTemplate]

def compressedTerminalRule : Atom :=
  .expression
    [.symbol "exec", compressedTerminalLocation,
      inputSurface compressedTerminalPatterns,
      outputSurface compressedTerminalSinks]

def compressedTerminalDirective : SourceExecFact where
  atom := compressedTerminalRule
  loc := compressedTerminalLocation
  rule :=
    { priority := 7
      name := "mm-compressed-terminal"
      input := .compat (mkPattern compressedTerminalPatterns)
      guards := []
      tmpl := mkTemplate compressedTerminalSinks }

theorem extract_compressedTerminalRule_exact :
    extractSupportedSourceExecFact compressedTerminalRule =
      some compressedTerminalDirective := by
  rfl

private def compressedHeapProofTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-heap-proof", .var "proof-owner",
      .var "compressed-index", .var "node-id"]

private def compressedNodeTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-node", .var "proof-owner", .var "node-id",
      .var "node-formula", .var "node-occurrence"]

private def compressedStackSuccessorTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-index-successor",
      .expression [.symbol "mm-compressed-stack-owner", .var "proof-owner"],
      .var "stack-position", .var "next-stack-position"]

private def compressedNextMachineTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-machine", .var "scope-owner",
      .var "proof-owner", .var "heap-next", .var "node-next",
      .var "next-stack-position"]

private def compressedStackCellTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-stack-cell", .var "proof-owner",
      .var "stack-position", .var "node-id"]

/-- The normal assertion machine reads the same live proof occurrence through
its generic stack interface.  The compact node record remains authoritative;
this row is a representation view, not a second proof result. -/
private def compressedNormalStackCellTemplate : Atom :=
  .expression
    [.symbol "mm-stack-cell", .var "proof-owner",
      .var "stack-position", .var "node-formula", .var "node-occurrence"]

private def compressedResumedScanTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-scan", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes",
      compressedJustCompletedPhase, listAtom natAtom []]

private def compressedProofStepSelf : Atom :=
  .expression
    [.symbol "exec", compressedProofStepLocation,
      .var "proof-step-input", .var "proof-step-output"]

private def compressedProofStepPatterns : List Atom :=
  [compressedProofStepSelf, compressedStepPendingTemplate,
   compressedHeapLookupExactTemplate,
   compressedHeapProofTemplate,
   compressedNodeTemplate, compressedMachineTemplate,
   compressedStackSuccessorTemplate, compressedPrefixRuleCaptureTemplate,
   compressedTerminalRuleCaptureTemplate,
   compressedInvalidByteRuleCaptureTemplate,
   compressedQuestionRuleCaptureTemplate,
   compressedQuestionOpenFaultRuleCaptureTemplate]

private def compressedProofStepSinks : List Sink :=
  [.add compressedProofStepSelf,
   .add (.var "compressed-prefix-rule"),
   .add (.var "compressed-terminal-rule"),
   .add (.var "compressed-invalid-byte-rule"),
   .add (.var "compressed-question-rule"),
   .add (.var "compressed-question-open-fault-rule"),
   .remove compressedStepPendingTemplate,
   .remove compressedHeapLookupExactTemplate,
   .remove compressedMachineTemplate,
   .add compressedNextMachineTemplate,
   .add compressedStackCellTemplate,
   .add compressedNormalStackCellTemplate,
   .add compressedResumedScanTemplate]

def compressedProofStepRule : Atom :=
  .expression
    [.symbol "exec", compressedProofStepLocation,
      inputSurface compressedProofStepPatterns,
      outputSurface compressedProofStepSinks]

def compressedProofStepDirective : SourceExecFact where
  atom := compressedProofStepRule
  loc := compressedProofStepLocation
  rule :=
    { priority := 8
      name := "mm-compressed-proof-step"
      input := .compat (mkPattern compressedProofStepPatterns)
      guards := []
      tmpl := mkTemplate compressedProofStepSinks }

theorem extract_compressedProofStepRule_exact :
    extractSupportedSourceExecFact compressedProofStepRule =
      some compressedProofStepDirective := by
  rfl

/-! ## Total compact heap lookup on the generated frontier -/

private def compressedHeapLookupAtEndTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-heap-lookup", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes",
      .var "compressed-index", .var "heap-next"]

private def compressedHeapLookupFaultTemplate : Atom :=
  .expression
    [.symbol "mm-proof-fault", .var "scope-owner", .var "proof-owner",
      .var "word-position", .symbol "compressed-missing-heap-reference",
      .symbol "compressed-heap", .var "compressed-index", .var "heap-next"]

private def compressedHeapLookupFaultSelf : Atom :=
  .expression
    [.symbol "exec", compressedHeapLookupFaultLocation,
      .var "heap-lookup-fault-input", .var "heap-lookup-fault-output"]

private def compressedHeapLookupFaultPatterns : List Atom :=
  [compressedHeapLookupFaultSelf, compressedStepPendingTemplate,
   compressedHeapLookupAtEndTemplate, compressedMachineTemplate]

private def compressedHeapLookupFaultSinks : List Sink :=
  [.remove compressedStepPendingTemplate,
   .remove compressedHeapLookupAtEndTemplate,
   .remove compressedMachineTemplate,
   .add compressedHeapLookupFaultTemplate]

def compressedHeapLookupFaultRule : Atom :=
  .expression
    [.symbol "exec", compressedHeapLookupFaultLocation,
      inputSurface compressedHeapLookupFaultPatterns,
      outputSurface compressedHeapLookupFaultSinks]

def compressedHeapLookupFaultDirective : SourceExecFact where
  atom := compressedHeapLookupFaultRule
  loc := compressedHeapLookupFaultLocation
  rule :=
    { priority := 8
      name := "mm-compressed-heap-lookup-fault"
      input := .compat (mkPattern compressedHeapLookupFaultPatterns)
      guards := []
      tmpl := mkTemplate compressedHeapLookupFaultSinks }

theorem extract_compressedHeapLookupFaultRule_exact :
    extractSupportedSourceExecFact compressedHeapLookupFaultRule =
      some compressedHeapLookupFaultDirective := by
  rfl

private def compressedHeapLookupProofHandlerTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-owned-lookup-handler", .symbol "proof",
      .var "compressed-proof-handler"]

private def compressedHeapLookupAssertionHandlerTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-owned-lookup-handler", .symbol "assertion",
      .var "compressed-assertion-handler"]

private def compressedHeapLookupFaultHandlerTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-owned-lookup-handler", .symbol "fault",
      .var "compressed-lookup-fault-handler"]

/-- Verifier-owned opaque code values used to reinstall lookup consumers after
an unsuccessful cursor probe.  Guest/source rows never supply this table. -/
def compressedHeapLookupReloadRows : List Atom :=
  [.expression
      [.symbol "mm-compressed-owned-lookup-handler", .symbol "proof",
        compressedProofStepRule],
   .expression
      [.symbol "mm-compressed-owned-lookup-handler", .symbol "assertion",
        compressedAssertionLaunchRule],
   .expression
      [.symbol "mm-compressed-owned-lookup-handler", .symbol "fault",
        compressedHeapLookupFaultRule]]

private def compressedHeapLookupAdvanceSelf : Atom :=
  .expression
    [.symbol "exec", compressedHeapLookupAdvanceLocation,
      .var "heap-lookup-advance-input", .var "heap-lookup-advance-output"]

private def compressedHeapLookupAdvancePatterns : List Atom :=
  [compressedHeapLookupAdvanceSelf, compressedHeapLookupTemplate,
   compressedHeapLookupSuccessorTemplate,
   compressedHeapLookupProofHandlerTemplate,
   compressedHeapLookupAssertionHandlerTemplate,
   compressedHeapLookupFaultHandlerTemplate]

/-- Advancing the cursor reinstalls every lookup consumer that may have been
tried and removed at the previous cursor.  No proof rule is generated from
the source data; these are the fixed verifier-owned handlers. -/
private def compressedHeapLookupAdvanceSinks : List Sink :=
  [.add compressedHeapLookupAdvanceSelf,
   .add (.var "compressed-lookup-fault-handler"),
   .add (.var "compressed-proof-handler"),
   .add (.var "compressed-assertion-handler"),
   .remove compressedHeapLookupTemplate,
   .add compressedHeapLookupNextTemplate]

def compressedHeapLookupAdvanceRule : Atom :=
  .expression
    [.symbol "exec", compressedHeapLookupAdvanceLocation,
      inputSurface compressedHeapLookupAdvancePatterns,
      outputSurface compressedHeapLookupAdvanceSinks]

def compressedHeapLookupAdvanceDirective : SourceExecFact where
  atom := compressedHeapLookupAdvanceRule
  loc := compressedHeapLookupAdvanceLocation
  rule :=
    { priority := 9
      name := "mm-compressed-heap-lookup-advance"
      input := .compat (mkPattern compressedHeapLookupAdvancePatterns)
      guards := []
      tmpl := mkTemplate compressedHeapLookupAdvanceSinks }

theorem extract_compressedHeapLookupAdvanceRule_exact :
    extractSupportedSourceExecFact compressedHeapLookupAdvanceRule =
      some compressedHeapLookupAdvanceDirective := by
  rfl

private def compressedSaveScanTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-scan", .var "scope-owner",
      .var "proof-owner", .var "word-position",
      .expression [.symbol consTag, natAtom 90, .var "remaining-bytes"],
      compressedJustCompletedPhase, listAtom natAtom []]

private def compressedStackTopSuccessorTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-index-successor",
      .expression [.symbol "mm-compressed-stack-owner", .var "proof-owner"],
      .var "stack-top", .var "stack-position"]

private def compressedStackTopCellTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-stack-cell", .var "proof-owner",
      .var "stack-top", .var "node-id"]

private def compressedHeapSuccessorTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-index-successor",
      .expression [.symbol "mm-compressed-heap-owner", .var "proof-owner"],
      .var "heap-next", .var "next-heap-position"]

private def compressedSavedHeapTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-heap-proof", .var "proof-owner",
      .var "heap-next", .var "node-id"]

private def compressedSaveReceiptTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-save-receipt", .var "proof-owner",
      .var "heap-next", .var "node-id", .var "node-occurrence"]

private def compressedAfterSaveMachineTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-machine", .var "scope-owner",
      .var "proof-owner", .var "next-heap-position",
      .var "node-next", .var "stack-position"]

private def compressedAfterSaveScanTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-scan", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes",
      compressedBetweenPhase, listAtom natAtom []]

private def compressedSaveSelf : Atom :=
  .expression
    [.symbol "exec", compressedSaveLocation,
      .var "save-input", .var "save-output"]

private def compressedSavePatterns : List Atom :=
  [compressedSaveSelf, compressedSaveScanTemplate,
   compressedMachineTemplate,
   compressedStackTopSuccessorTemplate, compressedStackTopCellTemplate,
   compressedNodeTemplate, compressedHeapSuccessorTemplate,
   compressedPrefixRuleCaptureTemplate,
   compressedTerminalRuleCaptureTemplate,
   compressedProofRuleCaptureTemplate,
   compressedInvalidByteRuleCaptureTemplate,
   compressedQuestionRuleCaptureTemplate,
   compressedQuestionOpenFaultRuleCaptureTemplate]

private def compressedSaveSinks : List Sink :=
  [.add compressedSaveSelf,
   .add (.var "compressed-prefix-rule"),
   .add (.var "compressed-terminal-rule"),
   .add (.var "compressed-proof-rule"),
   .add (.var "compressed-invalid-byte-rule"),
   .add (.var "compressed-question-rule"),
   .add (.var "compressed-question-open-fault-rule"),
   .remove compressedSaveScanTemplate,
   .remove compressedMachineTemplate,
   .add compressedAfterSaveMachineTemplate,
   .add compressedAfterSaveScanTemplate,
   .add compressedSavedHeapTemplate,
   .add compressedSaveReceiptTemplate]

def compressedSaveRule : Atom :=
  .expression
    [.symbol "exec", compressedSaveLocation,
      inputSurface compressedSavePatterns,
      outputSurface compressedSaveSinks]

def compressedSaveDirective : SourceExecFact where
  atom := compressedSaveRule
  loc := compressedSaveLocation
  rule :=
    { priority := 9
      name := "mm-compressed-save"
      input := .compat (mkPattern compressedSavePatterns)
      guards := []
      tmpl := mkTemplate compressedSaveSinks }

theorem extract_compressedSaveRule_exact :
    extractSupportedSourceExecFact compressedSaveRule =
      some compressedSaveDirective := by
  rfl

private def compressedSaveDisallowedPhaseTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-save-disallowed-phase",
      .var "compressed-phase"]

private def compressedSaveFaultScanTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-scan", .var "scope-owner",
      .var "proof-owner", .var "word-position",
      .expression [.symbol consTag, natAtom 90, .var "remaining-bytes"],
      .var "compressed-phase", .var "reverse-prefix"]

private def compressedSaveFaultTemplate : Atom :=
  .expression
    [.symbol "mm-proof-fault", .var "scope-owner", .var "proof-owner",
      .var "word-position", .symbol "compressed-save-placement",
      natAtom 90, .var "compressed-phase", .var "reverse-prefix"]

private def compressedSaveFaultSelf : Atom :=
  .expression
    [.symbol "exec", compressedSaveFaultLocation,
      .var "save-fault-input", .var "save-fault-output"]

private def compressedSaveFaultPatterns : List Atom :=
  [compressedSaveFaultSelf, compressedSaveFaultScanTemplate,
   compressedSaveDisallowedPhaseTemplate]

private def compressedSaveFaultSinks : List Sink :=
  [.remove compressedSaveFaultScanTemplate,
   .add compressedSaveFaultTemplate]

def compressedSaveFaultRule : Atom :=
  .expression
    [.symbol "exec", compressedSaveFaultLocation,
      inputSurface compressedSaveFaultPatterns,
      outputSurface compressedSaveFaultSinks]

def compressedSaveFaultDirective : SourceExecFact where
  atom := compressedSaveFaultRule
  loc := compressedSaveFaultLocation
  rule :=
    { priority := 9
      name := "mm-compressed-save-phase-fault"
      input := .compat (mkPattern compressedSaveFaultPatterns)
      guards := []
      tmpl := mkTemplate compressedSaveFaultSinks }

theorem extract_compressedSaveFaultRule_exact :
    extractSupportedSourceExecFact compressedSaveFaultRule =
      some compressedSaveFaultDirective := by
  rfl

private def compressedEmptyScanTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-scan", .var "scope-owner",
      .var "proof-owner", .var "word-position", listAtom natAtom [],
      .var "compressed-phase", .var "reverse-prefix"]

private def compressedWordSuccessorTemplate : Atom :=
  .expression
    [.symbol "mm-index-successor", .var "proof-owner",
      .var "word-position", .var "next-word-position"]

private def compressedNextBodyWordTemplate : Atom :=
  .expression
    [.symbol "mm-row", stringAtom "compressed-body-word",
      .var "proof-owner", .var "next-word-position", .var "next-word"]

private def compressedNextWordScanTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-scan", .var "scope-owner",
      .var "proof-owner", .var "next-word-position", .var "next-word",
      .var "compressed-phase", .var "reverse-prefix"]

private def compressedWordAdvanceSelf : Atom :=
  .expression
    [.symbol "exec", compressedWordAdvanceLocation,
      .var "word-advance-input", .var "word-advance-output"]

private def compressedWordAdvancePatterns : List Atom :=
  [compressedWordAdvanceSelf, compressedEmptyScanTemplate,
   compressedWordSuccessorTemplate,
   compressedNextBodyWordTemplate, compressedPrefixRuleCaptureTemplate,
   compressedTerminalRuleCaptureTemplate,
   compressedProofRuleCaptureTemplate, compressedSaveRuleCaptureTemplate,
   compressedInvalidByteRuleCaptureTemplate,
   compressedQuestionRuleCaptureTemplate,
   compressedQuestionOpenFaultRuleCaptureTemplate,
   compressedSaveFaultRuleCaptureTemplate]

private def compressedWordAdvanceSinks : List Sink :=
  [.add compressedWordAdvanceSelf,
   .add (.var "compressed-prefix-rule"),
   .add (.var "compressed-terminal-rule"),
   .add (.var "compressed-proof-rule"),
   .add (.var "compressed-save-rule"),
   .add (.var "compressed-invalid-byte-rule"),
   .add (.var "compressed-question-rule"),
   .add (.var "compressed-question-open-fault-rule"),
   .add (.var "compressed-save-fault-rule"),
   .remove compressedEmptyScanTemplate,
   .add compressedNextWordScanTemplate]

def compressedWordAdvanceRule : Atom :=
  .expression
    [.symbol "exec", compressedWordAdvanceLocation,
      inputSurface compressedWordAdvancePatterns,
      outputSurface compressedWordAdvanceSinks]

def compressedWordAdvanceDirective : SourceExecFact where
  atom := compressedWordAdvanceRule
  loc := compressedWordAdvanceLocation
  rule :=
    { priority := 10
      name := "mm-compressed-word-advance"
      input := .compat (mkPattern compressedWordAdvancePatterns)
      guards := []
      tmpl := mkTemplate compressedWordAdvanceSinks }

theorem extract_compressedWordAdvanceRule_exact :
    extractSupportedSourceExecFact compressedWordAdvanceRule =
      some compressedWordAdvanceDirective := by
  rfl

private def compressedFinalPhaseTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-final-phase", .var "compressed-phase"]

private def compressedProofEndTemplate : Atom :=
  .expression
    [.symbol "mm-proof-end", .var "proof-owner",
      .var "next-word-position"]

private def compressedDescriptorTemplate : Atom :=
  .expression
    [.symbol "mm-proof", .var "scope-owner", .var "proof-owner",
      .symbol "compressed", .var "theorem-label", .var "expected-formula"]

private def compressedQuestionAllowedPhaseTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-question-allowed-phase",
      .var "compressed-phase"]

private def compressedQuestionScanTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-scan", .var "scope-owner",
      .var "proof-owner", .var "word-position",
      .expression [.symbol consTag, natAtom 63, .var "remaining-bytes"],
      .var "compressed-phase", listAtom natAtom []]

private def compressedQuestionOpenScanTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-scan", .var "scope-owner",
      .var "proof-owner", .var "word-position",
      .expression [.symbol consTag, natAtom 63, .var "remaining-bytes"],
      compressedOpenPhase, .var "reverse-prefix"]

private def compressedQuestionOccurrenceTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-question-occurrence", .var "proof-owner",
      .var "word-position", .var "remaining-bytes"]

private def compressedQuestionNodeTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-node", .var "proof-owner", .var "node-next",
      .var "expected-formula", compressedQuestionOccurrenceTemplate]

private def compressedQuestionStackTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-stack-cell", .var "proof-owner",
      .var "stack-position", .var "node-next"]

private def compressedQuestionNormalStackTemplate : Atom :=
  .expression
    [.symbol "mm-stack-cell", .var "proof-owner", .var "stack-position",
      .var "expected-formula", compressedQuestionOccurrenceTemplate]

private def compressedQuestionNextMachineTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-machine", .var "scope-owner",
      .var "proof-owner", .var "heap-next", .var "next-node",
      .var "next-stack-position"]

private def compressedQuestionResumedScanTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-scan", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes",
      compressedBetweenPhase, listAtom natAtom []]

private def compressedQuestionIncompleteTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-proof-incomplete", .var "scope-owner",
      .var "proof-owner", .var "word-position",
      compressedQuestionOccurrenceTemplate]

private def compressedQuestionSelf : Atom :=
  .expression
    [.symbol "exec", compressedQuestionLocation,
      .var "question-input", .var "question-output"]

private def compressedQuestionPatterns : List Atom :=
  [compressedQuestionSelf, compressedQuestionScanTemplate,
   compressedQuestionAllowedPhaseTemplate, compressedMachineTemplate,
   compressedNodeSuccessorTemplate, compressedStackSuccessorTemplate,
   compressedDescriptorTemplate, compressedPrefixRuleCaptureTemplate,
   compressedTerminalRuleCaptureTemplate,
   compressedInvalidByteRuleCaptureTemplate,
   compressedQuestionOpenFaultRuleCaptureTemplate]

private def compressedQuestionSinks : List Sink :=
  [.add compressedQuestionSelf,
   .add (.var "compressed-prefix-rule"),
   .add (.var "compressed-terminal-rule"),
   .add (.var "compressed-invalid-byte-rule"),
   .add (.var "compressed-question-open-fault-rule"),
   .remove compressedQuestionScanTemplate,
   .remove compressedMachineTemplate,
   .add compressedQuestionNextMachineTemplate,
   .add compressedQuestionNodeTemplate,
   .add compressedQuestionStackTemplate,
   .add compressedQuestionNormalStackTemplate,
   .add compressedQuestionResumedScanTemplate,
   .add compressedQuestionIncompleteTemplate]

def compressedQuestionRule : Atom :=
  .expression
    [.symbol "exec", compressedQuestionLocation,
      inputSurface compressedQuestionPatterns,
      outputSurface compressedQuestionSinks]

def compressedQuestionDirective : SourceExecFact where
  atom := compressedQuestionRule
  loc := compressedQuestionLocation
  rule :=
    { priority := 7
      name := "mm-compressed-question-step"
      input := .compat (mkPattern compressedQuestionPatterns)
      guards := []
      tmpl := mkTemplate compressedQuestionSinks }

theorem extract_compressedQuestionRule_exact :
    extractSupportedSourceExecFact compressedQuestionRule =
      some compressedQuestionDirective := by
  rfl

private def compressedQuestionOpenFaultTemplate : Atom :=
  .expression
    [.symbol "mm-proof-fault", .var "scope-owner", .var "proof-owner",
      .var "word-position", .symbol "compressed-question-in-open-index",
      natAtom 63, compressedOpenPhase, .var "reverse-prefix"]

private def compressedQuestionOpenFaultSelf : Atom :=
  .expression
    [.symbol "exec", compressedQuestionOpenFaultLocation,
      .var "question-open-input", .var "question-open-output"]

private def compressedQuestionOpenFaultPatterns : List Atom :=
  [compressedQuestionOpenFaultSelf, compressedQuestionOpenScanTemplate]

private def compressedQuestionOpenFaultSinks : List Sink :=
  [.remove compressedQuestionOpenScanTemplate,
   .add compressedQuestionOpenFaultTemplate]

def compressedQuestionOpenFaultRule : Atom :=
  .expression
    [.symbol "exec", compressedQuestionOpenFaultLocation,
      inputSurface compressedQuestionOpenFaultPatterns,
      outputSurface compressedQuestionOpenFaultSinks]

def compressedQuestionOpenFaultDirective : SourceExecFact where
  atom := compressedQuestionOpenFaultRule
  loc := compressedQuestionOpenFaultLocation
  rule :=
    { priority := 7
      name := "mm-compressed-question-open-fault"
      input := .compat (mkPattern compressedQuestionOpenFaultPatterns)
      guards := []
      tmpl := mkTemplate compressedQuestionOpenFaultSinks }

theorem extract_compressedQuestionOpenFaultRule_exact :
    extractSupportedSourceExecFact compressedQuestionOpenFaultRule =
      some compressedQuestionOpenFaultDirective := by
  rfl

private def compressedTerminalMachineTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-machine", .var "scope-owner",
      .var "proof-owner", .var "heap-next", .var "node-next",
      compressedIndexCodeAtom [] 1]

private def compressedRootStackTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-stack-cell", .var "proof-owner",
      compressedIndexCodeAtom [] 0, .var "root-node"]

private def compressedRootNodeTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-node", .var "proof-owner", .var "root-node",
      .var "expected-formula", .var "root-occurrence"]

private def compressedAcceptedTemplate : Atom :=
  .expression
    [.symbol "mm-accepted", .var "scope-owner", .var "proof-owner",
      .var "theorem-label", .var "expected-formula",
      .var "root-occurrence"]

private def compressedAcceptSelf : Atom :=
  .expression
    [.symbol "exec", compressedAcceptLocation,
      .var "accept-input", .var "accept-output"]

private def compressedAcceptPatterns : List Atom :=
  [compressedAcceptSelf, compressedEmptyScanTemplate,
   compressedFinalPhaseTemplate,
   compressedWordSuccessorTemplate, compressedProofEndTemplate,
   compressedDescriptorTemplate, compressedTerminalMachineTemplate,
   compressedRootStackTemplate, compressedRootNodeTemplate]

private def compressedAcceptSinks : List Sink :=
  [.remove compressedEmptyScanTemplate,
   .add compressedAcceptedTemplate]

def compressedAcceptRule : Atom :=
  .expression
    [.symbol "exec", compressedAcceptLocation,
      inputSurface compressedAcceptPatterns,
      outputSurface compressedAcceptSinks]

def compressedAcceptDirective : SourceExecFact where
  atom := compressedAcceptRule
  loc := compressedAcceptLocation
  rule :=
    { priority := 11
      name := "mm-compressed-accept"
      input := .compat (mkPattern compressedAcceptPatterns)
      guards := []
      tmpl := mkTemplate compressedAcceptSinks }

theorem extract_compressedAcceptRule_exact :
    extractSupportedSourceExecFact compressedAcceptRule =
      some compressedAcceptDirective := by
  rfl

private def compressedOpenEndScanTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-scan", .var "scope-owner",
      .var "proof-owner", .var "word-position", listAtom natAtom [],
      compressedOpenPhase, .var "reverse-prefix"]

private def compressedIncompleteFaultTemplate : Atom :=
  .expression
    [.symbol "mm-proof-fault", .var "scope-owner", .var "proof-owner",
      .var "word-position", .symbol "compressed-incomplete-index",
      .symbol "compressed-proof", .var "reverse-prefix",
      .symbol "end-of-proof"]

private def compressedIncompleteSelf : Atom :=
  .expression
    [.symbol "exec", compressedIncompleteLocation,
      .var "incomplete-input", .var "incomplete-output"]

private def compressedIncompletePatterns : List Atom :=
  [compressedIncompleteSelf, compressedOpenEndScanTemplate,
   compressedWordSuccessorTemplate,
   compressedProofEndTemplate]

private def compressedIncompleteSinks : List Sink :=
  [.remove compressedOpenEndScanTemplate,
   .add compressedIncompleteFaultTemplate]

def compressedIncompleteRule : Atom :=
  .expression
    [.symbol "exec", compressedIncompleteLocation,
      inputSurface compressedIncompletePatterns,
      outputSurface compressedIncompleteSinks]

def compressedIncompleteDirective : SourceExecFact where
  atom := compressedIncompleteRule
  loc := compressedIncompleteLocation
  rule :=
    { priority := 11
      name := "mm-compressed-incomplete"
      input := .compat (mkPattern compressedIncompletePatterns)
      guards := []
      tmpl := mkTemplate compressedIncompleteSinks }

theorem extract_compressedIncompleteRule_exact :
    extractSupportedSourceExecFact compressedIncompleteRule =
      some compressedIncompleteDirective := by
  rfl

private def compressedAssertionResumeSelf : Atom :=
  .expression
    [.symbol "exec", compressedAssertionResumeLocation,
      .var "assertion-resume-input", .var "assertion-resume-output"]

private def compressedAssertionResumedScanTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-scan", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes",
      compressedJustCompletedPhase, listAtom natAtom []]

private def compressedAssertionResumePatterns : List Atom :=
  [compressedAssertionResumeSelf, compressedAssertionResumeTemplate,
   compressedPrefixRuleCaptureTemplate,
   compressedTerminalRuleCaptureTemplate,
   compressedProofRuleCaptureTemplate,
   compressedAssertionLaunchRuleCaptureTemplate,
   compressedSaveRuleCaptureTemplate,
   compressedWordAdvanceRuleCaptureTemplate,
   compressedAcceptRuleCaptureTemplate,
   compressedIncompleteRuleCaptureTemplate,
   compressedInvalidByteRuleCaptureTemplate,
   compressedQuestionRuleCaptureTemplate,
   compressedQuestionOpenFaultRuleCaptureTemplate,
   compressedSaveFaultRuleCaptureTemplate]

private def compressedAssertionResumeSinks : List Sink :=
  [.remove compressedAssertionResumeTemplate,
   .add compressedAssertionResumedScanTemplate,
   .add (.var "compressed-prefix-rule"),
   .add (.var "compressed-terminal-rule"),
   .add (.var "compressed-proof-rule"),
   .add (.var "compressed-assertion-launch-rule"),
   .add (.var "compressed-save-rule"),
   .add (.var "compressed-word-advance-rule"),
   .add (.var "compressed-accept-rule"),
   .add (.var "compressed-incomplete-rule"),
   .add (.var "compressed-invalid-byte-rule"),
   .add (.var "compressed-question-rule"),
   .add (.var "compressed-question-open-fault-rule"),
   .add (.var "compressed-save-fault-rule")]

def compressedAssertionResumeRule : Atom :=
  .expression
    [.symbol "exec", compressedAssertionResumeLocation,
      inputSurface compressedAssertionResumePatterns,
      outputSurface compressedAssertionResumeSinks]

def compressedAssertionResumeDirective : SourceExecFact where
  atom := compressedAssertionResumeRule
  loc := compressedAssertionResumeLocation
  rule :=
    { priority := 34
      name := "mm-compressed-assertion-resume"
      input := .compat (mkPattern compressedAssertionResumePatterns)
      guards := []
      tmpl := mkTemplate compressedAssertionResumeSinks }

theorem extract_compressedAssertionResumeRule_exact :
    extractSupportedSourceExecFact compressedAssertionResumeRule =
      some compressedAssertionResumeDirective := by
  rfl

/-! ## Exact rule inventory -/

def compressedVerifierRules : List Atom :=
  [compressedStartRule, compressedPrefixRule, compressedInvalidByteRule,
   compressedQuestionOpenFaultRule, compressedQuestionRule,
   compressedTerminalRule,
   compressedProofStepRule, compressedAssertionLaunchRule,
   compressedHeapLookupAdvanceRule, compressedHeapLookupFaultRule,
   compressedSaveRule, compressedSaveFaultRule, compressedWordAdvanceRule,
   compressedAcceptRule, compressedIncompleteRule,
   compressedAssertionRejoinRule, compressedAssertionResumeRule]

def compressedVerifierDirectives : List SourceExecFact :=
  [compressedStartDirective, compressedPrefixDirective,
   compressedInvalidByteDirective, compressedQuestionOpenFaultDirective,
   compressedQuestionDirective, compressedTerminalDirective,
   compressedProofStepDirective,
   compressedAssertionLaunchDirective, compressedHeapLookupAdvanceDirective,
   compressedHeapLookupFaultDirective, compressedSaveDirective,
   compressedSaveFaultDirective, compressedWordAdvanceDirective,
   compressedAcceptDirective,
   compressedIncompleteDirective, compressedAssertionRejoinDirective,
   compressedAssertionResumeDirective]

theorem compressedVerifierRules_extract_exact :
    compressedVerifierRules.filterMap extractSupportedSourceExecFact =
      compressedVerifierDirectives := by
  rfl

/-- Opaque verifier-owned code values used to reinstall the incremental
scanner and the complete bounded heap-lookup service. -/
def compressedScannerRuleCaptureRows : List Atom :=
  [compressedOwnedRuntimeRuleRow "prefix" compressedPrefixRule,
   compressedOwnedRuntimeRuleRow "terminal" compressedTerminalRule,
   compressedOwnedRuntimeRuleRow "proof" compressedProofStepRule,
   compressedOwnedRuntimeRuleRow "assertion-launch" compressedAssertionLaunchRule,
   compressedOwnedRuntimeRuleRow "lookup-fault" compressedHeapLookupFaultRule,
   compressedOwnedRuntimeRuleRow "lookup-advance" compressedHeapLookupAdvanceRule,
   compressedOwnedRuntimeRuleRow "save" compressedSaveRule,
   compressedOwnedRuntimeRuleRow "word-advance" compressedWordAdvanceRule,
   compressedOwnedRuntimeRuleRow "accept" compressedAcceptRule,
   compressedOwnedRuntimeRuleRow "incomplete" compressedIncompleteRule,
   compressedOwnedRuntimeRuleRow "invalid-byte" compressedInvalidByteRule,
   compressedOwnedRuntimeRuleRow "question" compressedQuestionRule,
   compressedOwnedRuntimeRuleRow "question-open-fault"
     compressedQuestionOpenFaultRule,
   compressedOwnedRuntimeRuleRow "save-fault" compressedSaveFaultRule]

def compressedInvalidByteRow (byte : Nat) : Atom :=
  .expression [.symbol "mm-compressed-invalid-byte", natAtom byte]

/-- Strict Appendix-B profile: `?` is handled separately as an incomplete
proof action; every other byte outside `A` through `Z` is a parse fault. -/
def compressedInvalidByteRows : List Atom :=
  (List.range UInt8.size).filterMap fun byte =>
    if byte ≠ 63 ∧ (byte < 65 ∨ 90 < byte) then
      some (compressedInvalidByteRow byte)
    else
      none

def compressedQuestionAllowedPhaseRow (phase : Atom) : Atom :=
  .expression [.symbol "mm-compressed-question-allowed-phase", phase]

def compressedQuestionAllowedPhaseRows : List Atom :=
  [compressedQuestionAllowedPhaseRow (.symbol "mm-compressed-between-steps"),
   compressedQuestionAllowedPhaseRow
     (.symbol "mm-compressed-just-completed-step")]

def compressedSaveDisallowedPhaseRow (phase : Atom) : Atom :=
  .expression [.symbol "mm-compressed-save-disallowed-phase", phase]

def compressedSaveDisallowedPhaseRows : List Atom :=
  [compressedSaveDisallowedPhaseRow (.symbol "mm-compressed-between-steps"),
   compressedSaveDisallowedPhaseRow (.symbol "mm-compressed-open-index")]

/-- Opaque verifier-owned continuations across the normal-assertion seam. -/
def compressedAssertionContinuationCaptureRows : List Atom :=
  [compressedOwnedRuntimeRuleRow "assertion-rejoin" compressedAssertionRejoinRule,
   compressedOwnedRuntimeRuleRow "assertion-resume" compressedAssertionResumeRule]

/-- A verifier-owned composition seam for target-level surface transforms.
Both arguments are finite code inventories: source proof data never supplies
either the heap-lookup handlers or the scanner capture rows. -/
def compressedVerifierStaticRowsWithReloadRows
    (heapLookupReloadRows scannerCaptureRows : List Atom) : List Atom :=
  compressedTerminalByteRows ++ compressedPrefixByteRows ++
    compressedInvalidByteRows ++ compressedQuestionAllowedPhaseRows ++
      compressedSaveDisallowedPhaseRows ++ compressedFinalPhaseRows ++
        heapLookupReloadRows ++ scannerCaptureRows ++
          compressedAssertionContinuationCaptureRows

def compressedVerifierStaticRowsWithScannerCaptureRows
    (scannerCaptureRows : List Atom) : List Atom :=
  compressedVerifierStaticRowsWithReloadRows compressedHeapLookupReloadRows
    scannerCaptureRows

/-- Default verifier-owned compact runtime rows.  A later target-level
surface transform may replace only the opaque scanner capture family while
retaining every byte, phase, heap, and continuation row. -/
def compressedVerifierStaticRows : List Atom :=
  compressedVerifierStaticRowsWithScannerCaptureRows
    compressedScannerRuleCaptureRows

#print axioms extract_compressedStartRule_exact
#print axioms extract_compressedPrefixRule_exact
#print axioms extract_compressedInvalidByteRule_exact
#print axioms extract_compressedQuestionOpenFaultRule_exact
#print axioms extract_compressedQuestionRule_exact
#print axioms extract_compressedTerminalRule_exact
#print axioms extract_compressedProofStepRule_exact
#print axioms extract_compressedHeapLookupAdvanceRule_exact
#print axioms extract_compressedHeapLookupFaultRule_exact
#print axioms extract_compressedSaveRule_exact
#print axioms extract_compressedSaveFaultRule_exact
#print axioms extract_compressedWordAdvanceRule_exact
#print axioms extract_compressedAcceptRule_exact
#print axioms extract_compressedIncompleteRule_exact
#print axioms extract_compressedAssertionLaunchRule_exact
#print axioms extract_compressedAssertionRejoinRule_exact
#print axioms extract_compressedAssertionResumeRule_exact
#print axioms compressedVerifierRules_extract_exact

end Mettapedia.Languages.Metamath.MM2CompressedProofExecution
