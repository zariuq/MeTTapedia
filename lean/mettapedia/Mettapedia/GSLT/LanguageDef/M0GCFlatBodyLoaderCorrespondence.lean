import Mettapedia.GSLT.LanguageDef.M0GCWireFormat

/-!
# Flat-table binary-loader refinement for M0GC

The bounded M0GC C proof-certificate checker addresses five packed body tables
by a base offset, a fixed record width, and an index.  The canonical Lean wire
decoder instead consumes those tables sequentially.  This module isolates the
algorithmic question between them: does successful random-access table loading
produce exactly the same records as sequential decoding?

The main theorem answers yes.  It proves a forward simulation from successful
flat-table loading to the canonical sequential body reader, including exact
exhaustion when the declared body length matches the input length.  The proof
is not a comparison against a copied expected answer: it is parametric in the
input bytes and depends on fixed-width consumption laws for every record
reader.

Maturity boundary: this is a fully connected proof of concept for the M0GC
body-table layout.  It is not yet a semantics of C source, packed-structure
casts, pointer provenance, `size_t` overflow, allocation, file I/O, compiler
output, object code, an operating system, or hardware.  Header loading and the
original-byte checksum boundary remain separate refinements.  Consequently,
this module establishes binary-format parser refinement, not a verified C
program.
-/

namespace Mettapedia.GSLT.LanguageDef.M0GCFlatBodyLoaderCorrespondence

open Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCWireFormat

/-! ## Fixed-width readers -/

/-- A successful reader consumes exactly `width` bytes from its input. -/
def ConsumesExactly (read : Reader alpha) (width : Nat) : Prop :=
  ∀ input value rest,
    read input = some (value, rest) → rest = input.drop width

/-- Reader sequencing made explicit so fixed-width consumption composes. -/
def readerBind (read : Reader alpha) (next : alpha → Reader beta) :
    Reader beta := fun input =>
  (read input).bind fun valueAndRest =>
    next valueAndRest.1 valueAndRest.2

/-- A reader that returns a value without consuming input. -/
def readerPure (value : alpha) : Reader alpha :=
  fun input => some (value, input)

theorem ConsumesExactly.pure (value : alpha) :
    ConsumesExactly (readerPure value) 0 := by
  intro input output rest accepted
  simp only [readerPure, Option.some.injEq, Prod.mk.injEq] at accepted
  simpa using accepted.2.symm

theorem ConsumesExactly.bind
    {read : Reader alpha} {next : alpha → Reader beta}
    {firstWidth nextWidth : Nat}
    (firstExact : ConsumesExactly read firstWidth)
    (nextExact : ∀ value, ConsumesExactly (next value) nextWidth) :
    ConsumesExactly (readerBind read next) (firstWidth + nextWidth) := by
  intro input output rest accepted
  cases firstResult : read input with
  | none =>
      simp [readerBind, firstResult] at accepted
  | some pair =>
      rcases pair with ⟨value, suffix⟩
      have acceptedNext : next value suffix = some (output, rest) := by
        simpa [readerBind, firstResult] using accepted
      have suffixExact := firstExact input value suffix firstResult
      have restExact := nextExact value suffix output rest acceptedNext
      calc
        rest = suffix.drop nextWidth := restExact
        _ = (input.drop firstWidth).drop nextWidth := by rw [suffixExact]
        _ = input.drop (firstWidth + nextWidth) := by rw [List.drop_drop]

theorem readUInt16LE_consumesExactly :
    ConsumesExactly readUInt16LE 2 := by
  intro input value rest accepted
  rcases input with _ | ⟨byte0, input⟩
  · simp [readUInt16LE] at accepted
  rcases input with _ | ⟨byte1, suffix⟩
  · simp [readUInt16LE] at accepted
  simp only [readUInt16LE, Option.some.injEq, Prod.mk.injEq] at accepted
  simpa using accepted.2.symm

theorem readUInt32LE_consumesExactly :
    ConsumesExactly readUInt32LE 4 := by
  intro input value rest accepted
  rcases input with _ | ⟨byte0, input⟩
  · simp [readUInt32LE] at accepted
  rcases input with _ | ⟨byte1, input⟩
  · simp [readUInt32LE] at accepted
  rcases input with _ | ⟨byte2, input⟩
  · simp [readUInt32LE] at accepted
  rcases input with _ | ⟨byte3, suffix⟩
  · simp [readUInt32LE] at accepted
  simp only [readUInt32LE, Option.some.injEq, Prod.mk.injEq] at accepted
  simpa using accepted.2.symm

theorem readUInt64LE_consumesExactly :
    ConsumesExactly readUInt64LE 8 := by
  intro input value rest accepted
  rcases input with _ | ⟨byte0, input⟩
  · simp [readUInt64LE] at accepted
  rcases input with _ | ⟨byte1, input⟩
  · simp [readUInt64LE] at accepted
  rcases input with _ | ⟨byte2, input⟩
  · simp [readUInt64LE] at accepted
  rcases input with _ | ⟨byte3, input⟩
  · simp [readUInt64LE] at accepted
  rcases input with _ | ⟨byte4, input⟩
  · simp [readUInt64LE] at accepted
  rcases input with _ | ⟨byte5, input⟩
  · simp [readUInt64LE] at accepted
  rcases input with _ | ⟨byte6, input⟩
  · simp [readUInt64LE] at accepted
  rcases input with _ | ⟨byte7, suffix⟩
  · simp [readUInt64LE] at accepted
  simp only [readUInt64LE, Option.some.injEq, Prod.mk.injEq] at accepted
  simpa using accepted.2.symm

/-- The term reader expressed solely by composable fixed-width readers. -/
def composedTermReader : Reader TermNode :=
  readerBind readUInt16LE fun symbol =>
  readerBind readUInt16LE fun arity =>
  readerBind readUInt32LE fun childStart =>
  readerBind readUInt32LE fun reserved =>
  readerBind readUInt64LE fun termHash =>
  readerPure { symbol, arity, childStart, reserved, termHash }

theorem composedTermReader_eq_readTermNode :
    composedTermReader = readTermNode := by
  rfl

theorem readTermNode_consumesExactly :
    ConsumesExactly readTermNode 20 := by
  rw [← composedTermReader_eq_readTermNode]
  exact readUInt16LE_consumesExactly.bind fun _ =>
    readUInt16LE_consumesExactly.bind fun _ =>
    readUInt32LE_consumesExactly.bind fun _ =>
    readUInt32LE_consumesExactly.bind fun _ =>
    readUInt64LE_consumesExactly.bind fun _ => ConsumesExactly.pure _

/-- The proof reader expressed solely by composable fixed-width readers. -/
def composedProofReader : Reader ProofNode :=
  readerBind readUInt16LE fun opcode =>
  readerBind readUInt16LE fun rule =>
  readerBind readUInt16LE fun argumentCount =>
  readerBind readUInt16LE fun premiseCount =>
  readerBind readUInt32LE fun argumentStart =>
  readerBind readUInt32LE fun premiseStart =>
  readerBind readUInt32LE fun resultTerm =>
  readerBind readUInt32LE fun reserved =>
  readerBind readUInt64LE fun ruleFingerprint =>
  readerPure
    { opcode, rule, argumentCount, premiseCount, argumentStart, premiseStart,
      resultTerm, reserved, ruleFingerprint }

theorem composedProofReader_eq_readProofNode :
    composedProofReader = readProofNode := by
  rfl

theorem readProofNode_consumesExactly :
    ConsumesExactly readProofNode 32 := by
  rw [← composedProofReader_eq_readProofNode]
  exact readUInt16LE_consumesExactly.bind fun _ =>
    readUInt16LE_consumesExactly.bind fun _ =>
    readUInt16LE_consumesExactly.bind fun _ =>
    readUInt16LE_consumesExactly.bind fun _ =>
    readUInt32LE_consumesExactly.bind fun _ =>
    readUInt32LE_consumesExactly.bind fun _ =>
    readUInt32LE_consumesExactly.bind fun _ =>
    readUInt32LE_consumesExactly.bind fun _ =>
    readUInt64LE_consumesExactly.bind fun _ => ConsumesExactly.pure _

/-! ## Random-access table loading -/

/-- Read `count` fixed-width records at explicit offsets.  The returned suffix
of each record read is deliberately discarded: this models a flat table view,
not a sequential parser. -/
def readManyAt (read : Reader alpha) (width : Nat)
    (bytes : List UInt8) : Nat → Nat → Option (List alpha)
  | _, 0 => some []
  | offset, count + 1 => do
      let (head, _) ← read (bytes.drop offset)
      let tail ← readManyAt read width bytes (offset + width) count
      some (head :: tail)

/-- Generic flat-table refinement.  Successful reads at calculated offsets
are exactly the records returned by the sequential reader, and the sequential
suffix begins at the calculated end offset. -/
theorem readManyAt_refines_readMany
    {read : Reader alpha} {width : Nat}
    (fixedWidth : ConsumesExactly read width)
    (bytes : List UInt8) :
    ∀ offset count values,
      readManyAt read width bytes offset count = some values →
        readMany read count (bytes.drop offset) =
          some (values, bytes.drop (offset + width * count)) := by
  intro offset count
  induction count generalizing offset with
  | zero =>
      intro values accepted
      simp only [readManyAt, Option.some.injEq] at accepted
      subst values
      rfl
  | succ count inductionHypothesis =>
      intro values accepted
      cases firstResult : read (bytes.drop offset) with
      | none =>
          simp [readManyAt, firstResult] at accepted
      | some pair =>
          rcases pair with ⟨head, suffix⟩
          cases tailResult :
              readManyAt read width bytes (offset + width) count with
          | none =>
              simp [readManyAt, firstResult, tailResult] at accepted
          | some tail =>
              simp [readManyAt, firstResult, tailResult, Option.bind] at accepted
              subst values
              have suffixExact :=
                fixedWidth (bytes.drop offset) head suffix firstResult
              have tailRead := inductionHypothesis (offset + width) tail tailResult
              simp only [readMany, firstResult]
              rw [suffixExact, List.drop_drop]
              change
                (readMany read count (bytes.drop (offset + width))).bind
                    (fun result => some (head :: result.1, result.2)) = _
              rw [tailRead]
              simp [Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm]

/-! ## The five-table M0GC body -/

/-- Counts governing the five physical body tables. -/
structure BodyCounts where
  termCount : Nat
  childCount : Nat
  proofCount : Nat
  argumentCount : Nat
  premiseCount : Nat
deriving DecidableEq, Repr

/-- The physical body counts declared by an M0GC header. -/
def BodyCounts.ofHeader (header : Header) : BodyCounts :=
  { termCount := header.termCount.toNat
    childCount := header.childCount.toNat
    proofCount := header.proofCount.toNat
    argumentCount := header.argumentCount.toNat
    premiseCount := header.premiseReferenceCount.toNat }

def termTableOffset (_ : BodyCounts) : Nat := 0

def childTableOffset (counts : BodyCounts) : Nat :=
  20 * counts.termCount

def proofTableOffset (counts : BodyCounts) : Nat :=
  childTableOffset counts + 4 * counts.childCount

def argumentTableOffset (counts : BodyCounts) : Nat :=
  proofTableOffset counts + 32 * counts.proofCount

def premiseTableOffset (counts : BodyCounts) : Nat :=
  argumentTableOffset counts + 4 * counts.argumentCount

/-- Exact byte length of the five packed body tables. -/
def bodyByteLength (counts : BodyCounts) : Nat :=
  premiseTableOffset counts + 4 * counts.premiseCount

/-- The decoded contents of all five physical body tables. -/
structure BodyTables where
  terms : List TermNode
  children : List UInt32
  proofs : List ProofNode
  arguments : List UInt32
  premises : List UInt32
deriving DecidableEq, Repr

/-- Canonical sequential body decoding, factored out of `readCertificate`. -/
def readBodySequential (counts : BodyCounts) : Reader BodyTables :=
  fun input => do
    let (terms, rest1) ← readMany readTermNode counts.termCount input
    let (children, rest2) ←
      readMany readUInt32LE counts.childCount rest1
    let (proofs, rest3) ← readMany readProofNode counts.proofCount rest2
    let (arguments, rest4) ←
      readMany readUInt32LE counts.argumentCount rest3
    let (premises, rest) ←
      readMany readUInt32LE counts.premiseCount rest4
    some ({ terms, children, proofs, arguments, premises }, rest)

/-- Flat-table loading at the same bases used by the bounded C checker.  Exact
body length is checked before any table is admitted. -/
def readBodyFlat? (counts : BodyCounts)
    (bytes : List UInt8) : Option BodyTables :=
  if bytes.length = bodyByteLength counts then do
    let terms ←
      readManyAt readTermNode 20 bytes
        (termTableOffset counts) counts.termCount
    let children ←
      readManyAt readUInt32LE 4 bytes
        (childTableOffset counts) counts.childCount
    let proofs ←
      readManyAt readProofNode 32 bytes
        (proofTableOffset counts) counts.proofCount
    let arguments ←
      readManyAt readUInt32LE 4 bytes
        (argumentTableOffset counts) counts.argumentCount
    let premises ←
      readManyAt readUInt32LE 4 bytes
        (premiseTableOffset counts) counts.premiseCount
    some { terms, children, proofs, arguments, premises }
  else
    none

/-- The core five-table refinement theorem.  Its hypotheses are precisely the
successful random-access reads and exact-length gate performed by
`readBodyFlat?`; its conclusion is canonical sequential decoding with no
trailing body bytes. -/
theorem flatTableReads_refine_sequential
    (counts : BodyCounts) (bytes : List UInt8) (tables : BodyTables)
    (lengthExact : bytes.length = bodyByteLength counts)
    (termsRead :
      readManyAt readTermNode 20 bytes
          (termTableOffset counts) counts.termCount =
        some tables.terms)
    (childrenRead :
      readManyAt readUInt32LE 4 bytes
          (childTableOffset counts) counts.childCount =
        some tables.children)
    (proofsRead :
      readManyAt readProofNode 32 bytes
          (proofTableOffset counts) counts.proofCount =
        some tables.proofs)
    (argumentsRead :
      readManyAt readUInt32LE 4 bytes
          (argumentTableOffset counts) counts.argumentCount =
        some tables.arguments)
    (premisesRead :
      readManyAt readUInt32LE 4 bytes
          (premiseTableOffset counts) counts.premiseCount =
        some tables.premises) :
    readBodySequential counts bytes = some (tables, []) := by
  rcases tables with ⟨terms, children, proofs, arguments, premises⟩
  have termsSequential :=
    readManyAt_refines_readMany readTermNode_consumesExactly bytes
      (termTableOffset counts) counts.termCount terms termsRead
  have childrenSequential :=
    readManyAt_refines_readMany readUInt32LE_consumesExactly bytes
      (childTableOffset counts) counts.childCount children childrenRead
  have proofsSequential :=
    readManyAt_refines_readMany readProofNode_consumesExactly bytes
      (proofTableOffset counts) counts.proofCount proofs proofsRead
  have argumentsSequential :=
    readManyAt_refines_readMany readUInt32LE_consumesExactly bytes
      (argumentTableOffset counts) counts.argumentCount arguments
      argumentsRead
  have premisesSequential :=
    readManyAt_refines_readMany readUInt32LE_consumesExactly bytes
      (premiseTableOffset counts) counts.premiseCount premises
      premisesRead
  simp only [termTableOffset, Nat.zero_add, List.drop_zero] at termsSequential
  have bodyExhausted : bytes.drop (bodyByteLength counts) = [] := by
    rw [← lengthExact]
    exact List.drop_length
  rw [show 20 * counts.termCount = childTableOffset counts by rfl]
    at termsSequential
  rw [show childTableOffset counts + 4 * counts.childCount =
      proofTableOffset counts by rfl] at childrenSequential
  rw [show proofTableOffset counts + 32 * counts.proofCount =
      argumentTableOffset counts by rfl] at proofsSequential
  rw [show argumentTableOffset counts + 4 * counts.argumentCount =
      premiseTableOffset counts by rfl] at argumentsSequential
  rw [show premiseTableOffset counts + 4 * counts.premiseCount =
      bodyByteLength counts by rfl] at premisesSequential
  rw [bodyExhausted] at premisesSequential
  simp [readBodySequential, Option.bind, termsSequential, childrenSequential,
    proofsSequential, argumentsSequential, premisesSequential]

/-- Successful execution of the flat-body loader refines the canonical
sequential body decoder and leaves no trailing bytes. -/
theorem readBodyFlat?_refines_sequential
    (counts : BodyCounts) (bytes : List UInt8) (tables : BodyTables)
    (accepted : readBodyFlat? counts bytes = some tables) :
    readBodySequential counts bytes = some (tables, []) := by
  by_cases lengthExact : bytes.length = bodyByteLength counts
  · cases termsResult :
        readManyAt readTermNode 20 bytes
          (termTableOffset counts) counts.termCount with
    | none =>
        simp [readBodyFlat?, lengthExact, termsResult, Option.bind] at accepted
    | some terms =>
        cases childrenResult :
            readManyAt readUInt32LE 4 bytes
              (childTableOffset counts) counts.childCount with
        | none =>
            simp [readBodyFlat?, lengthExact, termsResult, childrenResult,
              Option.bind] at accepted
        | some children =>
            cases proofsResult :
                readManyAt readProofNode 32 bytes
                  (proofTableOffset counts) counts.proofCount with
            | none =>
                simp [readBodyFlat?, lengthExact, termsResult,
                  childrenResult, proofsResult, Option.bind] at accepted
            | some proofs =>
                cases argumentsResult :
                    readManyAt readUInt32LE 4 bytes
                      (argumentTableOffset counts) counts.argumentCount with
                | none =>
                    simp [readBodyFlat?, lengthExact, termsResult,
                      childrenResult, proofsResult, argumentsResult,
                      Option.bind] at accepted
                | some arguments =>
                    cases premisesResult :
                        readManyAt readUInt32LE 4 bytes
                          (premiseTableOffset counts) counts.premiseCount with
                    | none =>
                        simp [readBodyFlat?, lengthExact, termsResult,
                          childrenResult, proofsResult, argumentsResult,
                          premisesResult, Option.bind] at accepted
                    | some premises =>
                        simp [readBodyFlat?, lengthExact, termsResult,
                          childrenResult, proofsResult, argumentsResult,
                          premisesResult, Option.bind] at accepted
                        subst tables
                        exact flatTableReads_refine_sequential counts bytes
                          { terms, children, proofs, arguments, premises }
                          lengthExact termsResult childrenResult proofsResult
                          argumentsResult premisesResult
  · simp [readBodyFlat?, lengthExact] at accepted

/-! ## Executable discriminators -/

def canaryCounts : BodyCounts :=
  BodyCounts.ofHeader
    (headerOf canaryCertificate (fnv1a64 (encodeBody canaryCertificate)))

def canaryTables : BodyTables :=
  { terms := canaryCertificate.terms
    children := canaryCertificate.children
    proofs := canaryCertificate.proofs
    arguments := canaryCertificate.arguments
    premises := canaryCertificate.premises }

/-- Positive discriminator: the flat-table loader accepts the canonical body
and reconstructs every table. -/
theorem canary_flat_body_accepts :
    readBodyFlat? canaryCounts (encodeBody canaryCertificate) =
      some canaryTables := by
  decide

/-- Negative discriminator: exact-length loading rejects a truncated body. -/
theorem truncated_canary_body_rejected :
    readBodyFlat? canaryCounts (encodeBody canaryCertificate).dropLast =
      none := by
  decide

/-- Negative discriminator: exact-length loading rejects trailing bytes. -/
theorem trailing_canary_body_rejected :
    readBodyFlat? canaryCounts (encodeBody canaryCertificate ++ [0]) =
      none := by
  decide

#print axioms readTermNode_consumesExactly
#print axioms readProofNode_consumesExactly
#print axioms readManyAt_refines_readMany
#print axioms flatTableReads_refine_sequential
#print axioms readBodyFlat?_refines_sequential
#print axioms canary_flat_body_accepts
#print axioms truncated_canary_body_rejected
#print axioms trailing_canary_body_rejected

end Mettapedia.GSLT.LanguageDef.M0GCFlatBodyLoaderCorrespondence
