import Mettapedia.Languages.Metamath.MM2DataEncoding
import Mettapedia.Languages.Metamath.MM2Target
import Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
import Mettapedia.Languages.Metamath.SourceStateNativeTypes

/-!
# Ordered Metamath source events as ordinary MM2 data

This module is the source-data half of the Metamath-to-MM2 route.  It keeps
the source statement spine intact: every statement has an explicit position,
and every `$p` occurrence carries its still-unchecked normal or compressed
proof payload in that same event.

The transformation may reject lexical, statement, declaration, or scope
errors through the authored source pipeline.  It does not discharge theorem
obligations.  Proof checking belongs to the separately generated generic MM2
verifier, which must also validate directly authored event rows.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2SourceEventTransformation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2Transformation (MM2Target)
open Mettapedia.Languages.Metamath.SourceGSLTIncludeDAG
open Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceGSLTOperations
open Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface

/-! ## Exact source carriers -/

def byteAtom (byte : UInt8) : Atom := natAtom byte.toNat

def decodeByteAtom (atom : Atom) : Option UInt8 := do
  let value <- decodeNatAtom atom
  if value < UInt8.size then
    some (UInt8.ofNat value)
  else
    none

@[simp] theorem decodeByteAtom_byteAtom (byte : UInt8) :
    decodeByteAtom (byteAtom byte) = some byte := by
  simp [decodeByteAtom, byteAtom, UInt8.toNat_lt_size]

def locatedByteSpanAtom (span : LocatedByteSpan) : Atom :=
  .expression
    [.symbol "mm-source-span", stringAtom span.fileId,
      natAtom span.start, natAtom span.stop]

def decodeLocatedByteSpanAtom : Atom -> Option LocatedByteSpan
  | .expression
      [.symbol tag, encodedFile, encodedStart, encodedStop] =>
      if tag = "mm-source-span" then do
        let fileId <- decodeStringAtom encodedFile
        let start <- decodeNatAtom encodedStart
        let stop <- decodeNatAtom encodedStop
        pure { fileId, start, stop }
      else
        none
  | _ => none

@[simp] theorem decodeLocatedByteSpanAtom_locatedByteSpanAtom
    (span : LocatedByteSpan) :
    decodeLocatedByteSpanAtom (locatedByteSpanAtom span) = some span := by
  cases span
  simp [decodeLocatedByteSpanAtom, locatedByteSpanAtom]

def locatedNameAtom (name : LocatedName) : Atom :=
  .expression
    [.symbol "mm-source-name", locatedByteSpanAtom name.span,
      stringAtom name.name]

def decodeLocatedNameAtom : Atom -> Option LocatedName
  | .expression [.symbol tag, encodedSpan, encodedName] =>
      if tag = "mm-source-name" then do
        let span <- decodeLocatedByteSpanAtom encodedSpan
        let name <- decodeStringAtom encodedName
        pure { span, name }
      else
        none
  | _ => none

@[simp] theorem decodeLocatedNameAtom_locatedNameAtom (name : LocatedName) :
    decodeLocatedNameAtom (locatedNameAtom name) = some name := by
  cases name
  simp [decodeLocatedNameAtom, locatedNameAtom]

def locatedTokenAtom (token : LocatedToken) : Atom :=
  .expression
    [.symbol "mm-source-token", locatedByteSpanAtom token.span,
      listAtom byteAtom token.bytes]

def decodeLocatedTokenAtom : Atom -> Option LocatedToken
  | .expression [.symbol tag, encodedSpan, encodedBytes] =>
      if tag = "mm-source-token" then do
        let span <- decodeLocatedByteSpanAtom encodedSpan
        let bytes <- decodeListAtom decodeByteAtom encodedBytes
        pure { span, bytes }
      else
        none
  | _ => none

@[simp] theorem decodeLocatedTokenAtom_locatedTokenAtom
    (token : LocatedToken) :
    decodeLocatedTokenAtom (locatedTokenAtom token) = some token := by
  cases token
  simp [decodeLocatedTokenAtom, locatedTokenAtom,
    decodeListAtom_listAtom]

def proofPayloadAtom : ProofPayload -> Atom
  | .normal steps =>
      .expression
        [.symbol "mm-source-normal-proof",
          listAtom locatedNameAtom steps]
  | .compressed openParen header closeParen words =>
      .expression
        [.symbol "mm-source-compressed-proof",
          locatedByteSpanAtom openParen,
          listAtom locatedNameAtom header,
          locatedByteSpanAtom closeParen,
          listAtom locatedTokenAtom words]

def decodeProofPayloadAtom : Atom -> Option ProofPayload
  | .expression [.symbol tag, encodedSteps] =>
      if tag = "mm-source-normal-proof" then do
        let steps <- decodeListAtom decodeLocatedNameAtom encodedSteps
        pure (.normal steps)
      else
        none
  | .expression
      [.symbol tag, encodedOpen, encodedHeader, encodedClose,
        encodedWords] =>
      if tag = "mm-source-compressed-proof" then do
        let openParen <- decodeLocatedByteSpanAtom encodedOpen
        let header <- decodeListAtom decodeLocatedNameAtom encodedHeader
        let closeParen <- decodeLocatedByteSpanAtom encodedClose
        let words <- decodeListAtom decodeLocatedTokenAtom encodedWords
        pure (.compressed openParen header closeParen words)
      else
        none
  | _ => none

@[simp] theorem decodeProofPayloadAtom_proofPayloadAtom
    (proof : ProofPayload) :
    decodeProofPayloadAtom (proofPayloadAtom proof) = some proof := by
  cases proof <;>
    simp [decodeProofPayloadAtom, proofPayloadAtom,
      decodeListAtom_listAtom]

def rawStatementAtom : RawStatement -> Atom
  | .openScope site =>
      .expression [.symbol "mm-source-open-scope", locatedByteSpanAtom site]
  | .closeScope site =>
      .expression [.symbol "mm-source-close-scope", locatedByteSpanAtom site]
  | .constDecl site names terminator =>
      .expression
        [.symbol "mm-source-const", locatedByteSpanAtom site,
          listAtom locatedNameAtom names, locatedByteSpanAtom terminator]
  | .varDecl site names terminator =>
      .expression
        [.symbol "mm-source-var", locatedByteSpanAtom site,
          listAtom locatedNameAtom names, locatedByteSpanAtom terminator]
  | .djDecl site names terminator =>
      .expression
        [.symbol "mm-source-dv", locatedByteSpanAtom site,
          listAtom locatedNameAtom names, locatedByteSpanAtom terminator]
  | .floating site label typecode variableName terminator =>
      .expression
        [.symbol "mm-source-floating", locatedByteSpanAtom site,
          locatedNameAtom label, locatedNameAtom typecode,
          locatedNameAtom variableName, locatedByteSpanAtom terminator]
  | .essential site label typecode body terminator =>
      .expression
        [.symbol "mm-source-essential", locatedByteSpanAtom site,
          locatedNameAtom label, locatedNameAtom typecode,
          listAtom locatedNameAtom body, locatedByteSpanAtom terminator]
  | .axiomatic site label typecode body terminator =>
      .expression
        [.symbol "mm-source-axiom", locatedByteSpanAtom site,
          locatedNameAtom label, locatedNameAtom typecode,
          listAtom locatedNameAtom body, locatedByteSpanAtom terminator]
  | .provable site label typecode body proof separator terminator =>
      .expression
        [.symbol "mm-source-theorem", locatedByteSpanAtom site,
          locatedNameAtom label, locatedNameAtom typecode,
          listAtom locatedNameAtom body, proofPayloadAtom proof,
          locatedByteSpanAtom separator, locatedByteSpanAtom terminator]

def decodeRawStatementAtom : Atom -> Option RawStatement
  | .expression [.symbol tag, encodedSite] =>
      if tag = "mm-source-open-scope" then
        RawStatement.openScope <$> decodeLocatedByteSpanAtom encodedSite
      else if tag = "mm-source-close-scope" then
        RawStatement.closeScope <$> decodeLocatedByteSpanAtom encodedSite
      else
        none
  | .expression
      [.symbol tag, encodedSite, encodedNames, encodedTerminator] => do
      let site <- decodeLocatedByteSpanAtom encodedSite
      let names <- decodeListAtom decodeLocatedNameAtom encodedNames
      let terminator <- decodeLocatedByteSpanAtom encodedTerminator
      if tag = "mm-source-const" then
        pure (.constDecl site names terminator)
      else if tag = "mm-source-var" then
        pure (.varDecl site names terminator)
      else if tag = "mm-source-dv" then
        pure (.djDecl site names terminator)
      else
        none
  | .expression
      [.symbol tag, encodedSite, encodedLabel, encodedTypecode,
        encodedVariable, encodedTerminator] =>
      if tag = "mm-source-floating" then do
        let site <- decodeLocatedByteSpanAtom encodedSite
        let label <- decodeLocatedNameAtom encodedLabel
        let typecode <- decodeLocatedNameAtom encodedTypecode
        let variableName <- decodeLocatedNameAtom encodedVariable
        let terminator <- decodeLocatedByteSpanAtom encodedTerminator
        pure (.floating site label typecode variableName terminator)
      else if tag = "mm-source-essential" then do
        let site <- decodeLocatedByteSpanAtom encodedSite
        let label <- decodeLocatedNameAtom encodedLabel
        let typecode <- decodeLocatedNameAtom encodedTypecode
        let body <- decodeListAtom decodeLocatedNameAtom encodedVariable
        let terminator <- decodeLocatedByteSpanAtom encodedTerminator
        pure (.essential site label typecode body terminator)
      else if tag = "mm-source-axiom" then do
        let site <- decodeLocatedByteSpanAtom encodedSite
        let label <- decodeLocatedNameAtom encodedLabel
        let typecode <- decodeLocatedNameAtom encodedTypecode
        let body <- decodeListAtom decodeLocatedNameAtom encodedVariable
        let terminator <- decodeLocatedByteSpanAtom encodedTerminator
        pure (.axiomatic site label typecode body terminator)
      else
        none
  | .expression
      [.symbol tag, encodedSite, encodedLabel, encodedTypecode,
        encodedBody, encodedProof, encodedSeparator, encodedTerminator] =>
      if tag = "mm-source-theorem" then do
        let site <- decodeLocatedByteSpanAtom encodedSite
        let label <- decodeLocatedNameAtom encodedLabel
        let typecode <- decodeLocatedNameAtom encodedTypecode
        let body <- decodeListAtom decodeLocatedNameAtom encodedBody
        let proof <- decodeProofPayloadAtom encodedProof
        let separator <- decodeLocatedByteSpanAtom encodedSeparator
        let terminator <- decodeLocatedByteSpanAtom encodedTerminator
        pure (.provable site label typecode body proof separator terminator)
      else
        none
  | _ => none

@[simp] theorem decodeRawStatementAtom_rawStatementAtom
    (statement : RawStatement) :
    decodeRawStatementAtom (rawStatementAtom statement) = some statement := by
  cases statement <;>
    simp [decodeRawStatementAtom, rawStatementAtom,
      decodeListAtom_listAtom]

theorem rawStatementAtom_injective : Function.Injective rawStatementAtom := by
  intro left right equal
  have decoded := congrArg decodeRawStatementAtom equal
  simpa using decoded

/-! ## Ordered event stream -/

private def sourceEventRowsFrom (owner : Atom) :
    Nat → List RawStatement → List Atom
  | _, [] => []
  | position, statement :: statements =>
      linkedRow "source-statement" owner position (position + 1)
          (rawStatementAtom statement) ::
        sourceEventRowsFrom owner (position + 1) statements

def sourceEventRows (owner : Atom) (statements : List RawStatement) :
    List Atom :=
  sourceEventRowsFrom owner 0 statements

private theorem sourceEventRowsFrom_eq_mapIdx (owner : Atom)
    (offset : Nat) (statements : List RawStatement) :
    sourceEventRowsFrom owner offset statements =
      statements.mapIdx fun position statement =>
        linkedRow "source-statement" owner (offset + position)
          (offset + position + 1) (rawStatementAtom statement) := by
  induction statements generalizing offset with
  | nil => simp [sourceEventRowsFrom]
  | cons statement statements induction =>
      rw [List.mapIdx_cons]
      simp only [sourceEventRowsFrom, Nat.add_zero]
      congr 1
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        induction (offset + 1)

theorem sourceEventRows_eq_linkedRows (owner : Atom)
    (statements : List RawStatement) :
    sourceEventRows owner statements =
      linkedRows "source-statement" owner rawStatementAtom statements := by
  rw [sourceEventRows, sourceEventRowsFrom_eq_mapIdx]
  simp [linkedRows]

/-! ## Proof-neutral verifier input derived from statement events -/

/-- The proof owner for a theorem occurrence is determined only by source
identity and statement position.  It is not supplied by untrusted MM2 data. -/
def sourceProofOwnerAtom (owner : Atom) (position : Nat) : Atom :=
  .expression [.symbol "mm-source-proof-owner", owner, natAtom position]

/-- Convert a retained theorem obligation into the existing dynamic proof
input representation.  This strips source locations from labels and bytes,
but performs no proof lookup, stack execution, substitution, or DV check. -/
def theoremObligationProofInput (obligation : TheoremObligation) : ProofInput :=
  match obligation.proof with
  | .normal steps =>
      .normal obligation.label.name obligation.formula (steps.map (·.name))
  | .compressed _openParen header _closeParen words =>
      .compressed obligation.label.name obligation.formula
        (header.map (·.name)) (words.map (·.bytes))

/-- Exact prepared-theorem fact consumed by the ordered verifier.  The
complete raw statement is repeated so rows from distinct source occurrences
cannot be joined accidentally. -/
def sourcePreparedTheoremFact (owner : Atom) (position nextPosition : Nat)
    (statement : RawStatement) (proofOwner theoremLabel expected : Atom) : Atom :=
  .expression
    [.symbol "mm-source-theorem-prepared", owner, natAtom position,
      natAtom nextPosition, rawStatementAtom statement,
      proofOwner, theoremLabel, expected]

/-- Exact link from one unresolved source theorem occurrence to the dynamic
proof rows derived for it. -/
def sourcePreparedTheoremRow (owner : Atom) (position nextPosition : Nat)
    (statement : RawStatement) (obligation : TheoremObligation) : Atom :=
  sourcePreparedTheoremFact owner position nextPosition statement
    (sourceProofOwnerAtom owner position) (stringAtom obligation.label.name)
    (formulaAtom obligation.formula)

/-- The assertion header is the activation row consumed by the normal proof
machine.  Source transformation wraps it inertly; only successful theorem
commit publishes the enclosed header. -/
def sourcePreparedAssertionHeaderFact (owner : Atom) (position : Nat)
    (assertionHeader : Atom) : Atom :=
  .expression
    [.symbol "mm-source-theorem-assertion-header", owner, natAtom position,
      sourceProofOwnerAtom owner position, assertionHeader]

def sourcePreparedAssertionHeaderRow (owner : Atom) (position : Nat)
    (state : SourceState) (obligation : TheoremObligation) : Atom :=
  let assertion :=
    sourceAssertion state obligation.label.name obligation.formula
  sourcePreparedAssertionHeaderFact owner position
    (assertionHeaderRow owner state.assertions.length assertion)

/-- Supporting rows are harmless before admission because assertion execution
cannot start without the separately wrapped header.  Precomputing them is the
proof-neutral, database-as-data part of source transformation. -/
def sourcePreparedAssertionSupportRows (owner : Atom) (_position : Nat)
    (state : SourceState) (obligation : TheoremObligation) : List Atom :=
  let assertion :=
    sourceAssertion state obligation.label.name obligation.formula
  (assertionExecutionRowsFor owner state.assertions.length assertion).drop 1

def sourcePreparedTheoremRows (owner : Atom) (position nextPosition : Nat)
    (statement : RawStatement) (state : SourceState)
    (obligation : TheoremObligation) : List Atom :=
  sourcePreparedTheoremRow owner position nextPosition statement obligation ::
    proofInputRows owner (sourceProofOwnerAtom owner position)
      (theoremObligationProofInput obligation) ++
    [sourcePreparedAssertionHeaderRow owner position state obligation] ++
    sourcePreparedAssertionSupportRows owner position state obligation

/-- Derive verifier-owned proof syntax rows while replaying the same authored
declaration/scope fold used by source admission.  A theorem contributes rows
only after its statement is structurally accepted; its proof remains wholly
unchecked. -/
private def sourceDerivedProofRowsFrom (owner : Atom) :
    Nat → SourceState → List RawStatement → FoldResult (List Atom)
  | _, _, [] => .ok []
  | position, state, statement :: statements =>
      match applyStatement state statement with
      | .rejected rejection => .rejected rejection
      | .ok (next, obligations) =>
          match sourceDerivedProofRowsFrom owner (position + 1) next statements with
          | .rejected rejection => .rejected rejection
          | .ok rest =>
              match obligations with
              | [obligation] =>
                  .ok (sourcePreparedTheoremRows owner position (position + 1)
                    statement state obligation ++ rest)
              | _ => .ok rest

def sourceDerivedProofRows (owner : Atom) (statements : List RawStatement) :
    FoldResult (List Atom) :=
  sourceDerivedProofRowsFrom owner 0 initialState statements

/-- A successful structural fold guarantees that proof-neutral row derivation
also succeeds.  Both computations use the same ordered `applyStatement`
spine; this theorem does not establish any proof-validity proposition. -/
private theorem sourceDerivedProofRowsFrom_ok_of_foldStatements_ok
    (owner : Atom) (position : Nat) (state final : SourceState)
    (statements : List RawStatement) (obligations : List TheoremObligation)
    (accepted : foldStatements state statements = .ok (final, obligations)) :
    ∃ rows,
      sourceDerivedProofRowsFrom owner position state statements = .ok rows := by
  induction statements generalizing position state obligations with
  | nil =>
      exact ⟨[], rfl⟩
  | cons statement statements induction =>
      simp only [foldStatements] at accepted
      cases applied : applyStatement state statement with
      | rejected rejection =>
          simp only [applied] at accepted
          exact nomatch accepted
      | ok result =>
          obtain ⟨next, currentObligations⟩ := result
          simp only [applied] at accepted
          cases folded : foldStatements next statements with
          | rejected rejection =>
              simp only [folded] at accepted
              exact nomatch accepted
          | ok result =>
              obtain ⟨actualFinal, restObligations⟩ := result
              simp only [folded] at accepted
              obtain ⟨rfl, rfl⟩ := FoldResult.ok.inj accepted
              obtain ⟨rows, rowsEq⟩ :=
                induction (position + 1) next restObligations folded
              cases currentObligations with
              | nil =>
                  refine ⟨rows, ?_⟩
                  simp only [sourceDerivedProofRowsFrom, applied, rowsEq]
              | cons obligation tail =>
                  cases tail with
                  | nil =>
                      refine ⟨sourcePreparedTheoremRows owner position
                        (position + 1) statement state obligation ++ rows, ?_⟩
                      simp only [sourceDerivedProofRowsFrom, applied, rowsEq]
                  | cons nextObligation tail =>
                      refine ⟨rows, ?_⟩
                      simp only [sourceDerivedProofRowsFrom, applied, rowsEq]

theorem sourceDerivedProofRows_ok_of_foldStatements_ok
    (owner : Atom) (statements : List RawStatement)
    (final : SourceState) (obligations : List TheoremObligation)
    (accepted :
      foldStatements initialState statements = .ok (final, obligations)) :
    ∃ rows, sourceDerivedProofRows owner statements = .ok rows :=
  sourceDerivedProofRowsFrom_ok_of_foldStatements_ok owner 0 initialState
    final statements obligations accepted

/-- A source artifact begins with an explicit owner marker.  The generic
verifier, rather than the data producer, turns this inert marker into the
initial ordered-control state. -/
def sourceEventStartRow (owner : Atom) : Atom :=
  .expression [.symbol "mm-source-start", owner]

def decodeSourceEventStartRow (owner : Atom) : Atom -> Option Unit
  | .expression [.symbol tag, actualOwner] =>
      if tag = "mm-source-start" && actualOwner = owner then some () else none
  | _ => none

@[simp] theorem decodeSourceEventStartRow_sourceEventStartRow (owner : Atom) :
    decodeSourceEventStartRow owner (sourceEventStartRow owner) = some () := by
  simp [decodeSourceEventStartRow, sourceEventStartRow]

def sourceEventEndRow (owner : Atom) (statements : List RawStatement) : Atom :=
  .expression
    [.symbol "mm-source-end", owner, natAtom statements.length]

def decodeSourceEventEndRow (owner : Atom) : Atom → Option Nat
  | .expression [.symbol tag, actualOwner, encodedLength] => do
      if tag != "mm-source-end" || actualOwner != owner then
        none
      decodeNatAtom encodedLength
  | _ => none

@[simp] theorem decodeSourceEventEndRow_sourceEventEndRow
    (owner : Atom) (statements : List RawStatement) :
    decodeSourceEventEndRow owner (sourceEventEndRow owner statements) =
      some statements.length := by
  simp [decodeSourceEventEndRow, sourceEventEndRow]

/-- Decode one ordinary MM2 source-statement row.  The owner, family tag,
position, successor, and complete unresolved statement payload are all
checked. -/
def decodeSourceEventRow (owner : Atom) : Atom →
    Option (Nat × Nat × RawStatement)
  | .expression
      [.symbol tag, encodedFamily, actualOwner, encodedPosition,
        encodedNextPosition, encodedStatement] => do
      if tag != "mm-linked-row" || actualOwner != owner then
        none
      let family ← decodeStringAtom encodedFamily
      if family != "source-statement" then
        none
      let position ← decodeNatAtom encodedPosition
      let nextPosition ← decodeNatAtom encodedNextPosition
      let statement ← decodeRawStatementAtom encodedStatement
      pure (position, nextPosition, statement)
  | _ => none

@[simp] theorem decodeSourceEventRow_linkedRow (owner : Atom)
    (position nextPosition : Nat) (statement : RawStatement) :
    decodeSourceEventRow owner
        (linkedRow "source-statement" owner position nextPosition
          (rawStatementAtom statement)) =
      some (position, nextPosition, statement) := by
  simp [decodeSourceEventRow, linkedRow]

/-! ## Total validation of directly authored event data -/

/-- Decode a whole event stream from one expected source position.  Every
link and the unique final boundary are checked.  This is the structural
admission function used equally for transformed and directly authored MM2
event data. -/
private def decodeSourceEventRowsFrom (owner : Atom) :
    Nat → List Atom → Option (List RawStatement)
  | _, [] => none
  | expected, row :: rows =>
      match decodeSourceEventRow owner row with
      | some (position, nextPosition, statement) => do
          if position != expected || nextPosition != expected + 1 then
            none
          let statements ←
            decodeSourceEventRowsFrom owner (expected + 1) rows
          pure (statement :: statements)
      | none =>
          match rows with
          | _ :: _ => none
          | [] => do
              let finalPosition ← decodeSourceEventEndRow owner row
              if finalPosition = expected then some [] else none

/-- Decode and validate one complete ordered statement/event artifact. -/
def decodeSourceEventRows (owner : Atom) (rows : List Atom) :
    Option (List RawStatement) :=
  match rows with
  | [] => none
  | start :: rows => do
      let _ <- decodeSourceEventStartRow owner start
      decodeSourceEventRowsFrom owner 0 rows

private theorem decodeSourceEventRowsFrom_encoded (owner : Atom)
    (offset : Nat) (statements : List RawStatement) :
    decodeSourceEventRowsFrom owner offset
        (sourceEventRowsFrom owner offset statements ++
          [.expression
            [.symbol "mm-source-end", owner,
              natAtom (offset + statements.length)]]) =
      some statements := by
  induction statements generalizing offset with
  | nil =>
      simp [sourceEventRowsFrom, decodeSourceEventRowsFrom,
        decodeSourceEventEndRow, decodeSourceEventRow]
  | cons statement statements induction =>
      simp only [sourceEventRowsFrom, List.cons_append,
        decodeSourceEventRowsFrom, decodeSourceEventRow_linkedRow]
      rw [show offset + (statement :: statements).length =
          (offset + 1) + statements.length by
            simp [Nat.add_comm, Nat.add_left_comm]]
      simp [induction]

/-- Canonically transformed source events survive exact untrusted-input
validation, with every statement occurrence and unresolved proof payload
recovered in source order. -/
@[simp] theorem decodeSourceEventRows_encoded (owner : Atom)
    (statements : List RawStatement) :
    decodeSourceEventRows owner
        (sourceEventStartRow owner :: sourceEventRows owner statements ++
          [sourceEventEndRow owner statements]) =
      some statements := by
  simpa [decodeSourceEventRows, sourceEventRows, sourceEventEndRow] using
    decodeSourceEventRowsFrom_encoded owner 0 statements

/-- Public verifier outcomes are deliberately outside the source-event
vocabulary.  This recognizer is used only to state and test the proof-neutral
boundary; it does not assign operational meaning to an outcome. -/
def isVerifierTerminalObservation : Atom → Bool
  | .expression (.symbol tag :: _) =>
      tag == "mm-accepted" || tag == "mm-rejected" ||
        tag == "mm-fault" || tag == "mm-incomplete"
  | _ => false

/-- Initial verifier data is passive when it is neither a scheduler-visible
`exec` shell nor a terminal verdict.  This is an entry-boundary property, not
an assertion that all later verifier-owned control and stack rows are public
input. -/
def isProofNeutralInitialAtom (atom : Atom) : Bool :=
  (Mettapedia.Languages.ProcessCalculi.MORK.extractRawExecFact atom).isNone &&
    !(isVerifierTerminalObservation atom)

structure SourceEventArtifact where
  statements : List RawStatement
  finalState : SourceState
  obligations : List TheoremObligation
  rows : List Atom
deriving DecidableEq

def makeSourceEventArtifact (owner : Atom) (statements : List RawStatement)
    (finalState : SourceState) (obligations : List TheoremObligation) :
    SourceEventArtifact where
  statements
  finalState
  obligations
  rows := sourceEventStartRow owner :: sourceEventRows owner statements ++
    [sourceEventEndRow owner statements]

/-- Source-indexed characterization of one statement row. -/
def SourceEventRowFrom (owner : Atom) (statements : List RawStatement)
    (row : Atom) : Prop :=
  sourceEventStartRow owner = row \/
    (exists (position : Nat) (inBounds : position < statements.length),
      linkedRow "source-statement" owner position (position + 1)
        (rawStatementAtom statements[position]) = row) \/
    sourceEventEndRow owner statements = row

theorem mem_sourceEventArtifact_rows_iff (owner : Atom)
    (statements : List RawStatement) (finalState : SourceState)
    (obligations : List TheoremObligation) (row : Atom) :
    row ∈ (makeSourceEventArtifact owner statements finalState obligations).rows ↔
      SourceEventRowFrom owner statements row := by
  rw [show (makeSourceEventArtifact owner statements finalState obligations).rows =
      sourceEventStartRow owner ::
        linkedRows "source-statement" owner rawStatementAtom statements ++
        [sourceEventEndRow owner statements] by
    simp [makeSourceEventArtifact, sourceEventRows_eq_linkedRows]]
  simp [SourceEventRowFrom, mem_linkedRows_iff, eq_comm]

/-- Every statement occurrence in the artifact remains exactly decodable,
including the unresolved proof payload of a `$p` statement. -/
theorem decode_sourceEventRow_of_mem (owner : Atom)
    (statements : List RawStatement) (position : Nat)
    (inBounds : position < statements.length) :
    decodeSourceEventRow owner
        (linkedRow "source-statement" owner position (position + 1)
          (rawStatementAtom statements[position])) =
      some (position, position + 1, statements[position]) := by
  exact decodeSourceEventRow_linkedRow owner position (position + 1)
    statements[position]

/-- The proof-neutral source transformation cannot emit a pre-approved
theorem, rejection, fault, or incomplete verdict.  Its rows are only linked
source statements plus the source-end boundary. -/
theorem sourceEventArtifact_rows_have_no_terminal_observation
    (owner : Atom) (statements : List RawStatement)
    (finalState : SourceState) (obligations : List TheoremObligation)
    (row : Atom)
    (member :
      row ∈ (makeSourceEventArtifact owner statements finalState
        obligations).rows) :
    isVerifierTerminalObservation row = false := by
  have classified :=
    (mem_sourceEventArtifact_rows_iff owner statements finalState obligations
      row).mp member
  rcases classified with equal | ⟨position, inBounds, equal⟩ | equal
  · rw [← equal]
    simp [isVerifierTerminalObservation, sourceEventStartRow]
  · rw [← equal]
    simp [isVerifierTerminalObservation, linkedRow]
  · rw [← equal]
    simp [isVerifierTerminalObservation, sourceEventEndRow]

@[simp] theorem proofInputRows_all_proofNeutral
    (scopeOwner proofOwner : Atom) (proof : ProofInput) :
    (proofInputRows scopeOwner proofOwner proof).all
        isProofNeutralInitialAtom = true := by
  cases proof <;>
    simp [proofInputRows, proofInputTables, ProofInputTables.rows,
      indexedRows, linkedRows, linkedRow, indexedRow,
      isProofNeutralInitialAtom,
      Mettapedia.Languages.ProcessCalculi.MORK.extractRawExecFact,
      isVerifierTerminalObservation, indexSuccessorRows] <;>
    aesop

@[simp] theorem sourcePreparedTheoremRows_all_proofNeutral
    (owner : Atom) (position nextPosition : Nat)
    (statement : RawStatement) (state : SourceState)
    (obligation : TheoremObligation) :
    (sourcePreparedTheoremRows owner position nextPosition statement state
        obligation).all isProofNeutralInitialAtom = true := by
  rcases obligation with ⟨site, label, formula, proof⟩
  simp [sourcePreparedTheoremRows, sourcePreparedTheoremRow,
    sourcePreparedTheoremFact, sourcePreparedAssertionHeaderRow,
    sourcePreparedAssertionHeaderFact, sourcePreparedAssertionSupportRows,
    theoremObligationProofInput, assertionExecutionRowsFor,
    assertionHypothesisRows, assertionHypothesisRow,
    assertionHypothesisSuccessorRows, assertionHypothesisSuccessorRow,
    assertionDVHeaderRow, assertionDVPairRows, assertionDVPairRow,
    assertionDVSuccessorRows, assertionResultRow,
    isProofNeutralInitialAtom,
    Mettapedia.Languages.ProcessCalculi.MORK.extractRawExecFact,
    isVerifierTerminalObservation]
  all_goals aesop

private theorem sourceDerivedProofRowsFrom_all_proofNeutral
    (owner : Atom) (position : Nat) (state : SourceState)
    (statements : List RawStatement) (rows : List Atom)
    (derived :
      sourceDerivedProofRowsFrom owner position state statements = .ok rows) :
    rows.all isProofNeutralInitialAtom = true := by
  induction statements generalizing position state rows with
  | nil =>
      simp [sourceDerivedProofRowsFrom] at derived
      subst rows
      rfl
  | cons statement statements induction =>
      simp only [sourceDerivedProofRowsFrom] at derived
      cases applied : applyStatement state statement with
      | rejected rejection => simp [applied] at derived
      | ok result =>
          rcases result with ⟨next, obligations⟩
          simp only [applied] at derived
          cases recursive :
              sourceDerivedProofRowsFrom owner (position + 1) next statements with
          | rejected rejection => simp [recursive] at derived
          | ok rest =>
              simp only [recursive] at derived
              have restSafe := induction (position + 1) next rest recursive
              cases obligations with
              | nil =>
                  obtain rfl := FoldResult.ok.inj derived
                  exact restSafe
              | cons obligation tail =>
                  cases tail with
                  | nil =>
                      obtain rfl := FoldResult.ok.inj derived
                      simp [restSafe]
                  | cons nextObligation tail =>
                      obtain rfl := FoldResult.ok.inj derived
                      exact restSafe

/-- Proof rows recomputed from an admitted source stream cannot smuggle an
executable rule or a terminal observation into the initial space. -/
theorem sourceDerivedProofRows_all_proofNeutral
    (owner : Atom) (statements : List RawStatement) (rows : List Atom)
    (derived : sourceDerivedProofRows owner statements = .ok rows) :
    rows.all isProofNeutralInitialAtom = true :=
  sourceDerivedProofRowsFrom_all_proofNeutral owner 0 initialState statements
    rows derived

/-- The canonical public event envelope contains only inert source rows. -/
@[simp] theorem canonicalSourceEventRows_all_proofNeutral
    (owner : Atom) (statements : List RawStatement) :
    (sourceEventStartRow owner :: sourceEventRows owner statements ++
        [sourceEventEndRow owner statements]).all
      isProofNeutralInitialAtom = true := by
  simp [sourceEventRows_eq_linkedRows, linkedRows, linkedRow,
    sourceEventStartRow, sourceEventEndRow, isProofNeutralInitialAtom,
    Mettapedia.Languages.ProcessCalculi.MORK.extractRawExecFact,
    isVerifierTerminalObservation]
  all_goals aesop

@[simp] theorem makeSourceEventArtifact_statement_count
    (owner : Atom) (statements : List RawStatement)
    (finalState : SourceState) (obligations : List TheoremObligation) :
    (makeSourceEventArtifact owner statements finalState obligations).rows.length =
      statements.length + 2 := by
  simp [makeSourceEventArtifact, sourceEventRows_eq_linkedRows]

/-! ## Raw-source transformation -/

inductive SourceEventTransformResult where
  | ok (artifact : SourceEventArtifact)
  | error (error : PipelineError)
deriving DecidableEq

/-- Forget only the retained statement/event representation. -/
def SourceEventTransformResult.toPipelineResult :
    SourceEventTransformResult -> PipelineResult
  | SourceEventTransformResult.ok artifact =>
      PipelineResult.ok artifact.finalState artifact.obligations
  | SourceEventTransformResult.error err => PipelineResult.error err

/-- Transform an already segmented statement stream.  This runs only the
authored declaration/scope fold.  The resulting theorem obligations remain
unresolved and are encoded inside their original `$p` statement events. -/
def transformSegmentedSource (owner : Atom)
    (statements : List RawStatement) : SourceEventTransformResult :=
  match foldStatements initialState statements with
  | .rejected rejection => .error (.fold rejection)
  | .ok (state, obligations) =>
      if sourceStateComplete state then
        .ok (makeSourceEventArtifact owner statements state obligations)
      else
        match scopeSites statements [] with
        | site :: _ => .error (.fold ⟨site, .unclosedScope⟩)
        | [] => .error .incompleteSource

/-- The complete source-data transformation.  Parsing, include expansion,
and declaration gates may reject.  No normal or compressed proof machine is
invoked here. -/
def transformRawSource (owner : Atom) (files : FileMap)
    (policy : IncludePolicy) (root : String) (fuel : Nat := 100) :
    SourceEventTransformResult :=
  match expandDatabase files policy root fuel with
  | .rejected rejection => .error (.include rejection)
  | .ok spans =>
      match resolveTokens files spans with
      | none => .error .resolution
      | some tokens =>
          match segmentStatements tokens with
          | .rejected rejection => .error (.statement rejection)
          | .ok statements => transformSegmentedSource owner statements

/-- Erasing the additional ordered event artifact gives exactly the existing
authored raw-source pipeline result.  The transformation therefore cannot
silently accept, reject, or discharge a source occurrence differently. -/
theorem transformRawSource_toPipelineResult (owner : Atom) (files : FileMap)
    (policy : IncludePolicy) (root : String) (fuel : Nat := 100) :
    (transformRawSource owner files policy root fuel).toPipelineResult =
      runSource files policy root fuel := by
  simp only [transformRawSource, transformSegmentedSource, runSource]
  split
  · simp_all [SourceEventTransformResult.toPipelineResult]
  · split
    · simp_all [SourceEventTransformResult.toPipelineResult]
    · split
      · simp_all [SourceEventTransformResult.toPipelineResult]
      · split
        · simp_all [SourceEventTransformResult.toPipelineResult]
        · split
          · simp_all [SourceEventTransformResult.toPipelineResult,
              makeSourceEventArtifact]
          · split <;>
              simp_all [SourceEventTransformResult.toPipelineResult]

/-- A successful segmented transformation is exactly the accepted structural
fold, with identical statements and still-undischarged obligations. -/
theorem transformSegmentedSource_ok_inv (owner : Atom)
    (statements : List RawStatement) (artifact : SourceEventArtifact)
    (accepted : transformSegmentedSource owner statements = .ok artifact) :
    artifact.statements = statements ∧
      foldStatements initialState statements =
        .ok (artifact.finalState, artifact.obligations) ∧
      artifact.rows = sourceEventStartRow owner ::
        sourceEventRows owner statements ++
        [sourceEventEndRow owner statements] := by
  simp only [transformSegmentedSource] at accepted
  cases hfold : foldStatements initialState statements with
  | rejected rejection =>
      simp only [hfold] at accepted
      exact nomatch accepted
  | ok pair =>
      obtain ⟨state, obligations⟩ := pair
      simp only [hfold] at accepted
      cases hcomplete : sourceStateComplete state with
      | false =>
          rw [if_neg (by simp [hcomplete])] at accepted
          cases hsites : scopeSites statements [] with
          | nil => simp only [hsites] at accepted; exact nomatch accepted
          | cons site rest =>
              simp only [hsites] at accepted
              exact nomatch accepted
      | true =>
          simp only [hcomplete, ↓reduceIte] at accepted
          cases accepted
          exact ⟨rfl, rfl, rfl⟩

/-! ## Proof-neutrality of source elaboration -/

/-- Successful source elaboration of a `$p` statement is characterized only
by formula tagging and assertion insertion.  The submitted proof is retained
verbatim in the obligation; no proof predicate appears in the acceptance
conditions. -/
theorem applyStatement_provable_eq_ok_iff
    (state next : SourceState) (obligations : List TheoremObligation)
    (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (proof : ProofPayload) :
    applyStatement state
        (.provable site label typecode body proof separator terminator) =
        .ok (next, obligations) ↔
      ∃ symbols,
        tagBody state body = .ok symbols ∧
        insertAssertion? state label.name ⟨typecode.name, symbols⟩ =
          some next ∧
        obligations =
          [⟨site, label, ⟨typecode.name, symbols⟩, proof⟩] := by
  simp only [applyStatement]
  cases bodyResult : tagBody state body with
  | rejected rejection =>
      simp
  | ok symbols =>
      cases insertion :
          insertAssertion? state label.name ⟨typecode.name, symbols⟩ with
      | none => simp [insertion]
      | some inserted =>
          simp [insertion, eq_comm]

/-- Replacing an accepted theorem's proof payload cannot affect source
elaboration or the provisional next state.  It changes only the unresolved
obligation that the MM2 verifier must later check. -/
theorem applyStatement_provable_success_transport
    (state next : SourceState) (obligations : List TheoremObligation)
    (site separator terminator : LocatedByteSpan)
    (label typecode : LocatedName) (body : List LocatedName)
    (leftProof rightProof : ProofPayload)
    (accepted :
      applyStatement state
          (.provable site label typecode body leftProof separator terminator) =
        .ok (next, obligations)) :
    ∃ rightObligations,
      applyStatement state
          (.provable site label typecode body rightProof separator terminator) =
        .ok (next, rightObligations) := by
  obtain ⟨symbols, tagged, inserted, _⟩ :=
    (applyStatement_provable_eq_ok_iff state next obligations site separator
      terminator label typecode body leftProof).mp accepted
  refine ⟨[⟨site, label, ⟨typecode.name, symbols⟩, rightProof⟩], ?_⟩
  exact
    (applyStatement_provable_eq_ok_iff state next _ site separator terminator
      label typecode body rightProof).mpr ⟨symbols, tagged, inserted, rfl⟩

/-- Rendering is a target-owned surface stage after source transformation. -/
def renderSourceEventArtifact? (target : MM2Target)
    (artifact : SourceEventArtifact) :
    Option String :=
  target.render artifact.rows

theorem renderSourceEventArtifact_ne_of_target_render_ne
    (left right : MM2Target) (artifact : SourceEventArtifact)
    (different : left.render artifact.rows ≠ right.render artifact.rows) :
    renderSourceEventArtifact? left artifact ≠
      renderSourceEventArtifact? right artifact :=
  different

/-! ## Verifier-facing validation of untrusted event data -/

inductive SourceEventInputError where
  | encoding
  | structural (error : PipelineError)
deriving DecidableEq

/-- Recheck the ordered encoding and the declaration/scope discipline of an
event stream, whether transformed or directly authored.  Only the decoded
statements are returned.  In particular, the source fold's provisional state
is discarded: a later `$p` may become usable only after the generic MM2
verifier checks its proof. -/
def validateSourceEventInput (owner : Atom) (rows : List Atom) :
    Except SourceEventInputError (List RawStatement) :=
  match decodeSourceEventRows owner rows with
  | none => .error .encoding
  | some statements =>
      match transformSegmentedSource owner statements with
      | .error error => .error (.structural error)
      | .ok _ => .ok statements

/-- Admission normalizes every successfully decoded event stream back to the
canonical source-event envelope before it may share a space with verifier
rules.  Alternate surface encodings may decode, but their original atoms are
never executed. -/
theorem validateSourceEventInput_canonical_of_ok
    (owner : Atom) (rows : List Atom) (statements : List RawStatement)
    (accepted : validateSourceEventInput owner rows = .ok statements) :
    validateSourceEventInput owner
        (sourceEventStartRow owner :: sourceEventRows owner statements ++
          [sourceEventEndRow owner statements]) = .ok statements := by
  unfold validateSourceEventInput at accepted ⊢
  rw [decodeSourceEventRows_encoded]
  cases decoded : decodeSourceEventRows owner rows with
  | none => simp [decoded] at accepted
  | some actual =>
      simp only [decoded] at accepted
      cases transformed : transformSegmentedSource owner actual with
      | error error => simp [transformed] at accepted
      | ok artifact =>
          simp only [transformed] at accepted
          have actualEq : actual = statements := Except.ok.inj accepted
          subst actual
          simp [transformed]

/-- The only source-event input that may be composed with verifier-owned MM2
rules.  Constructing this boundary rechecks both the exact ordered event
encoding and the authored declaration/scope fold; carrying arbitrary atoms
beside a claimed owner is insufficient. -/
structure AdmittedSourceEventInput (owner : Atom) where
  rows : List Atom
  statements : List RawStatement
  validated : validateSourceEventInput owner rows = .ok statements
  canonical :
    rows = sourceEventStartRow owner :: sourceEventRows owner statements ++
      [sourceEventEndRow owner statements]
  derivedRows : List Atom
  derivedExact : sourceDerivedProofRows owner statements = .ok derivedRows

/-- The only data admitted to verifier composition consists of the exact
decoded event stream and proof-neutral rows recomputed from that stream.
Callers cannot append an executable rule, stack cell, index, or verdict. -/
def AdmittedSourceEventInput.initialRows {owner : Atom}
    (input : AdmittedSourceEventInput owner) : List Atom :=
  input.rows ++ input.derivedRows

/-- The executable entry boundary is exact: public rows have been decoded and
canonically re-encoded, and verifier-owned derived rows have been recomputed.
Consequently no caller-supplied `exec` shell or terminal verdict is present in
the initial data. -/
theorem AdmittedSourceEventInput.initialRows_all_proofNeutral
    {owner : Atom} (input : AdmittedSourceEventInput owner) :
    input.initialRows.all isProofNeutralInitialAtom = true := by
  have publicRows :=
    canonicalSourceEventRows_all_proofNeutral owner input.statements
  have derivedRows :=
    sourceDerivedProofRows_all_proofNeutral owner input.statements
      input.derivedRows input.derivedExact
  rw [AdmittedSourceEventInput.initialRows, input.canonical, List.all_append,
    publicRows, derivedRows]
  rfl

theorem AdmittedSourceEventInput.initialRows_no_exec_or_terminal
    {owner : Atom} (input : AdmittedSourceEventInput owner)
    (row : Atom) (member : row ∈ input.initialRows) :
    Mettapedia.Languages.ProcessCalculi.MORK.extractRawExecFact row = none ∧
      isVerifierTerminalObservation row = false := by
  have allRows := List.all_eq_true.mp input.initialRows_all_proofNeutral
  have safe := allRows row member
  simpa only [isProofNeutralInitialAtom, Bool.and_eq_true,
    Option.isNone_iff_eq_none, Bool.not_eq_true'] using safe

/-- Total admission for transformed or directly authored source-event rows. -/
def admitSourceEventInput (owner : Atom) (rows : List Atom) :
    Except SourceEventInputError (AdmittedSourceEventInput owner) :=
  match validated : validateSourceEventInput owner rows with
  | .error error => .error error
  | .ok statements =>
      match derived : sourceDerivedProofRows owner statements with
      | .rejected rejection => .error (.structural (.fold rejection))
      | .ok derivedRows =>
          let canonicalRows :=
            sourceEventStartRow owner :: sourceEventRows owner statements ++
              [sourceEventEndRow owner statements]
          .ok
            { rows := canonicalRows
              statements
              validated := by
                dsimp only [canonicalRows]
                exact validateSourceEventInput_canonical_of_ok owner rows
                  statements validated
              canonical := rfl
              derivedRows
              derivedExact := derived }

/-- A successfully transformed source artifact passes the same structural
validator used for directly authored MM2 event data.  The result is the exact
statement list, not a trusted database state. -/
theorem validateSourceEventInput_of_transformSegmentedSource_ok
    (owner : Atom) (statements : List RawStatement)
    (artifact : SourceEventArtifact)
    (transformed : transformSegmentedSource owner statements = .ok artifact) :
    validateSourceEventInput owner artifact.rows = .ok statements := by
  obtain ⟨statementEq, _, rowsEq⟩ :=
    transformSegmentedSource_ok_inv owner statements artifact transformed
  subst statementEq
  unfold validateSourceEventInput
  rw [rowsEq, decodeSourceEventRows_encoded]
  simp only
  rw [transformed]

/-- A successful source transform crosses the same typed admission boundary
as directly authored event data; no trusted shortcut exists for generated
rows. -/
theorem admitSourceEventInput_of_transformSegmentedSource_ok
    (owner : Atom) (statements : List RawStatement)
    (artifact : SourceEventArtifact)
    (transformed : transformSegmentedSource owner statements = .ok artifact) :
    ∃ input,
      admitSourceEventInput owner artifact.rows = .ok input ∧
        input.statements = statements := by
  have validated := validateSourceEventInput_of_transformSegmentedSource_ok
    owner statements artifact transformed
  obtain ⟨_, folded, _⟩ :=
    transformSegmentedSource_ok_inv owner statements artifact transformed
  obtain ⟨derivedRows, derived⟩ :=
    sourceDerivedProofRows_ok_of_foldStatements_ok owner statements
      artifact.finalState artifact.obligations folded
  unfold admitSourceEventInput
  split
  · rename_i error rejected
    rw [validated] at rejected
    exact nomatch rejected
  · rename_i decoded accepted
    have decodedEq : decoded = statements :=
      Except.ok.inj (accepted.symm.trans validated)
    subst decoded
    split
    · rename_i rejection rejected
      rw [derived] at rejected
      contradiction
    · rename_i actualDerived acceptedDerived
      have derivedRowsEq : actualDerived = derivedRows :=
        FoldResult.ok.inj (acceptedDerived.symm.trans derived)
      subst actualDerived
      exact ⟨_, rfl, rfl⟩

/-! ## Positive and negative controls -/

open Mettapedia.Languages.Metamath.SourceStateNativeTypes

/-- An accepted `$c` event is simultaneously exact target data and a genuine
inhabitant of the native type generated by OSLF from the authored Metamath
state calculus.  The source transformation does not assign declarations a
second, ad hoc operational meaning. -/
theorem constant_event_inhabits_source_native_type
    (owner : Atom) (site terminator : LocatedByteSpan)
    (names : List LocatedName) (target : SourceState)
    (applied :
      applyLocalPayload? (.declareConstants (names.map (·.name)))
        initialState = some target) :
    let statement := RawStatement.constDecl site names terminator
    linkedRow "source-statement" owner 0 1
        (rawStatementAtom statement) ∈ sourceEventRows owner [statement] ∧
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        SourceStateGSLT.theory).satisfies initialState
        (sourceStateExactTargetNativeType target).pred := by
  dsimp
  constructor
  · simp [sourceEventRows, sourceEventRowsFrom]
  · exact local_payload_inhabits_exact_target applied

private def fixtureOwner : Atom := stringAtom "fixture-source"

/-- The repository's small multi-file fixture transforms without checking its
carried theorem proof. -/
example :
    (match transformRawSource fixtureOwner fixtureFiles
        mmLean4CompatPolicy "root" with
      | .ok artifact => artifact.obligations.length == 1
      | .error _ => false) = true := by
  decide

private def unresolvedProofFiles : FileMap := fun name =>
  if name = "root" then
    some (ByteArray.mk #[36, 99, 32, 119, 32, 36, 46, 32,
      116, 104, 32, 36, 112, 32, 119, 32, 36, 61, 32, 63, 32, 36, 46])
  else
    none

/-- The source transform carries an unresolved `?` theorem occurrence.  It
does not turn declaration acceptance into theorem acceptance. -/
example :
    (match transformRawSource fixtureOwner unresolvedProofFiles
        mmLean4CompatPolicy "root" with
      | .ok artifact =>
          artifact.obligations.map (fun obligation => obligation.proof) ==
            [.normal [⟨⟨"root", 19, 20⟩, "?"⟩]]
      | .error _ => false) = true := by
  decide

/-- Directly authored byte data outside the UInt8 range is rejected by the
event decoder instead of being truncated. -/
example : decodeByteAtom (natAtom UInt8.size) = none := by
  simp [decodeByteAtom]

/-- A directly authored row cannot jump over an expected source position. -/
example (owner : Atom) (statement : RawStatement) :
    decodeSourceEventRows owner
        [sourceEventStartRow owner,
         linkedRow "source-statement" owner 0 2
          (rawStatementAtom statement),
         sourceEventEndRow owner [statement]] = none := by
  simp [decodeSourceEventRows, decodeSourceEventRowsFrom]

/-- Reordering two directly authored occurrences is rejected before source
or proof semantics are run. -/
example (owner : Atom) (first second : RawStatement) :
    decodeSourceEventRows owner
        [sourceEventStartRow owner,
         linkedRow "source-statement" owner 1 2
            (rawStatementAtom second),
         linkedRow "source-statement" owner 0 1
            (rawStatementAtom first),
         sourceEventEndRow owner [first, second]] = none := by
  simp [decodeSourceEventRows, decodeSourceEventRowsFrom]

/-- A terminal observation cannot be smuggled into a structurally admitted
source-event stream. -/
example (owner : Atom) :
    validateSourceEventInput owner
        [.expression [.symbol "mm-accepted", owner]] =
      .error .encoding := by
  simp [validateSourceEventInput, decodeSourceEventRows,
    decodeSourceEventRowsFrom, decodeSourceEventStartRow]

/-- A directly authored internal assertion index cannot cross the public
event-data decoder. -/
example (owner : Atom) :
    validateSourceEventInput owner
        [sourceEventStartRow owner,
          .expression [.symbol "mm-assertion-index", owner, natAtom 0],
          sourceEventEndRow owner []] =
      .error .encoding := by
  simp [validateSourceEventInput, decodeSourceEventRows,
    decodeSourceEventRowsFrom, decodeSourceEventRow]

/-- A directly authored scheduler rule cannot cross the public event-data
decoder, regardless of whether its body would be supported by MORK. -/
example (owner : Atom) :
    validateSourceEventInput owner
        [sourceEventStartRow owner,
          .expression
            [.symbol "exec", .symbol "forged", .symbol "input",
              .symbol "output"],
          sourceEventEndRow owner []] =
      .error .encoding := by
  simp [validateSourceEventInput, decodeSourceEventRows,
    decodeSourceEventRowsFrom, decodeSourceEventRow]

private def sameFormulaTheorem
    (site labelSpan typeSpan bodySpan proofSpan separator terminator :
      LocatedByteSpan) : RawStatement :=
  .provable site ⟨labelSpan, "th"⟩ ⟨typeSpan, "wff"⟩
    [⟨bodySpan, "x"⟩] (.normal [⟨proofSpan, "ax"⟩])
    separator terminator

/-- Two equal statement payloads at distinct source positions remain distinct
MM2 set elements. -/
example (owner : Atom) (statement : RawStatement) :
    linkedRow "source-statement" owner 0 1 (rawStatementAtom statement) ≠
      linkedRow "source-statement" owner 1 2 (rawStatementAtom statement) := by
  simp [linkedRow, natAtom]

/-- Normal and compressed theorem payloads cannot collapse to the same event
representation. -/
example (site labelSpan typeSpan bodySpan proofSpan separator terminator :
    LocatedByteSpan) :
    rawStatementAtom
        (sameFormulaTheorem site labelSpan typeSpan bodySpan proofSpan
          separator terminator) ≠
      rawStatementAtom
        (.provable site ⟨labelSpan, "th"⟩ ⟨typeSpan, "wff"⟩
          [⟨bodySpan, "x"⟩]
          (.compressed proofSpan [] proofSpan []) separator terminator) := by
  simp [sameFormulaTheorem, rawStatementAtom, proofPayloadAtom]

/-! Kernel audit -/

#print axioms decodeRawStatementAtom_rawStatementAtom
#print axioms rawStatementAtom_injective
#print axioms mem_sourceEventArtifact_rows_iff
#print axioms decodeSourceEventRow_linkedRow
#print axioms decodeSourceEventRows_encoded
#print axioms decode_sourceEventRow_of_mem
#print axioms sourceEventArtifact_rows_have_no_terminal_observation
#print axioms transformRawSource_toPipelineResult
#print axioms transformSegmentedSource_ok_inv
#print axioms applyStatement_provable_eq_ok_iff
#print axioms applyStatement_provable_success_transport
#print axioms sourceDerivedProofRows_ok_of_foldStatements_ok
#print axioms sourceDerivedProofRows_all_proofNeutral
#print axioms canonicalSourceEventRows_all_proofNeutral
#print axioms validateSourceEventInput_of_transformSegmentedSource_ok
#print axioms AdmittedSourceEventInput.initialRows_no_exec_or_terminal
#print axioms admitSourceEventInput_of_transformSegmentedSource_ok
#print axioms constant_event_inhabits_source_native_type

end Mettapedia.Languages.Metamath.MM2SourceEventTransformation
