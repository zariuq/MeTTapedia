import Mettapedia.Languages.Metamath.SourceGSLTIncludeDAG
import Mettapedia.Languages.Metamath.SourceGSLTState
import Mettapedia.Languages.Metamath.SourceGSLTStatementPlan

/-!
# Raw-source composition: expanded spans → statements → source operations

Tranche step 3 forward lane.  The include/source-DAG GSLT
(`SourceGSLTIncludeDAG`) ends at a located, comment-free, include-free
token stream whose spans keep file identity and byte offsets.  The
source-state GSLT (`SourceGSLTState`) begins at `LocalPayload`
operations guarded by `applyLocalPayload?`.  This module authors the
missing middle:

* **Resolution** — spans back to token bytes through the same `FileMap`
  the expansion read (`resolveTokens`); the step-1 provenance theorem
  guarantees resolution succeeds on expansion output.
* **Segmentation** (`segmentStatements`) — a single left-to-right pass
  grouping tokens into raw Metamath statements ([MM §4.1.3] shapes:
  `${`, `$}`, `$c…$.`, `$v…$.`, `$d…$.`, `label $f tc v $.`,
  `label $e …$.`, `label $a …$.`, `label $p … $= … $.` with the normal
  and compressed proof forms split at `(` per [MM §4.4.5]).  Token
  charset legality ([MM §4.1.1]: label tokens are letters, digits,
  `-`, `_`, `.`; math tokens are printable ASCII except `$`) is owned
  **here** — this is the parser-lane obligation the state gates
  deliberately delegate.  Every rejection carries the exact offending
  span.
* **Fold** (`foldStatements`) — statements to accepted source
  transitions: symbol tagging against the current declarations (a
  token is a variable occurrence exactly when actively declared `$v`,
  else a constant occurrence when declared `$c`, else rejected at its
  own span), then the source GSLT's own gates via `applyLocalPayload?`
  for the nine local operations and `insertAssertion?` for `$p`
  declarations.  Proof payloads are **carried, not checked**: each
  `$p` emits a chronologically ordered `TheoremObligation` for the
  step-4 lifecycle joints (`NormalTheoremStep` /
  `CompressedTheoremStep`), which demand proof-tree evidence this fold
  cannot and must not fabricate.

Kernel-reducibility discipline as in step 1: plain structural
recursions, pure-`List` spans, byte-level keyword dispatch — the whole
forward pipeline runs under `decide`/`rfl` in fixtures.  (Engineering
note: `ByteArray` content must be read as `bytes.data.toList` — the
`ByteArray.toList` wrapper is kernel-opaque.)

The statements retain **every** consumed token span — keyword, names,
`$=`, parentheses, terminator — so `RawStatement.tokenSpans` flattens a
segmentation back to the exact expanded span stream: the statement list
is the derivation witness, and reflection needs no separately authored
unparser (which would be a second syntax authority).
-/

set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition

open Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical (LocatedByteSpan tokenize)
open Mettapedia.Languages.Metamath.SourceGSLTIncludeDAG
open Mettapedia.Languages.Metamath.SourceGSLTOperations (SourceOperation)
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceGSLTStatementPlan
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceEncoding

/-! ## Token text and [MM §4.1.1] charsets -/

/-- ASCII token bytes to the token's text. -/
def tokenText (tok : List UInt8) : String :=
  String.ofList (tok.map fun b => Char.ofNat b.toNat)

/-- [MM §4.1.1] label charset: letters, digits, hyphen, underscore,
period. -/
def labelByte (b : UInt8) : Bool :=
  sourceStatementPlan.labelMembers.contains b.toNat

def labelBytesValid (tok : List UInt8) : Bool :=
  !tok.isEmpty && tok.all labelByte

/-- [MM §4.1.1] math-symbol charset: the 93 printable standard ASCII
characters other than space and `$`. -/
def mathByte (b : UInt8) : Bool :=
  sourceStatementPlan.mathMembers.contains b.toNat

def mathBytesValid (tok : List UInt8) : Bool :=
  !tok.isEmpty && tok.all mathByte

/-- Normal-proof step token: a label or the unknown-step marker `?`
([MM §4.4]). -/
def proofTokenValid (tok : List UInt8) : Bool :=
  labelBytesValid tok ||
    tok = sourceStatementPlan.unknownProof.codepoints.map UInt8.ofNat

/-- [MM §4.4.5] compressed-proof word charset: upper-case letters and
`?`. -/
def compressedWordByte (b : UInt8) : Bool :=
  sourceStatementPlan.compressedMembers.contains b.toNat

def compressedWordValid (tok : List UInt8) : Bool :=
  !tok.isEmpty && tok.all compressedWordByte

/-! ## Source-derived keyword bytes -/

private def planBytes (literal : CompiledLiteral) : List UInt8 :=
  literal.codepoints.map UInt8.ofNat

def constKeywordBytes : List UInt8 :=
  planBytes sourceStatementPlan.constantKeyword
def varKeywordBytes : List UInt8 :=
  planBytes sourceStatementPlan.variableKeyword
def djKeywordBytes : List UInt8 :=
  planBytes sourceStatementPlan.disjointKeyword
def floatKeywordBytes : List UInt8 :=
  planBytes sourceStatementPlan.floatingKeyword
def essentialKeywordBytes : List UInt8 :=
  planBytes sourceStatementPlan.essentialKeyword
def axiomKeywordBytes : List UInt8 :=
  planBytes sourceStatementPlan.axiomKeyword
def provableKeywordBytes : List UInt8 :=
  planBytes sourceStatementPlan.theoremKeyword
def proofSeparatorBytes : List UInt8 :=
  planBytes sourceStatementPlan.proofSeparator
def statementEndBytes : List UInt8 :=
  planBytes sourceStatementPlan.statementEnd
def scopeOpenBytes : List UInt8 :=
  planBytes sourceStatementPlan.scopeOpen
def scopeCloseBytes : List UInt8 :=
  planBytes sourceStatementPlan.scopeClose
def parenOpenBytes : List UInt8 :=
  planBytes sourceStatementPlan.parenOpen
def parenCloseBytes : List UInt8 :=
  planBytes sourceStatementPlan.parenClose

/-! ## Located carriers -/

/-- A token with its resolved bytes. -/
structure LocatedToken where
  span : LocatedByteSpan
  bytes : List UInt8
deriving DecidableEq, Repr

/-- A name-bearing token (label, math symbol, or proof step) with its
text and provenance. -/
structure LocatedName where
  span : LocatedByteSpan
  name : String
deriving DecidableEq, Repr

def LocatedToken.toName (tok : LocatedToken) : LocatedName :=
  ⟨tok.span, tokenText tok.bytes⟩

/-! ## Resolution against the file map -/

/-- Resolve each span to its token bytes.  `none` only when a span's
file is absent — impossible for expansion output by the step-1
provenance theorem. -/
def resolveTokens (files : FileMap) : List LocatedByteSpan →
    Option (List LocatedToken)
  | [] => some []
  | span :: rest =>
      match files span.fileId with
      | none => none
      | some content =>
          match resolveTokens files rest with
          | none => none
          | some tokens =>
              some (⟨span, spanBytes content.data.toList span⟩ :: tokens)

theorem resolveTokens_of_provenance (files : FileMap) :
    ∀ (spans : List LocatedByteSpan),
      (∀ s ∈ spans, ∃ bytes, files s.fileId = some bytes) →
      ∃ tokens, resolveTokens files spans = some tokens
  | [], _ => ⟨[], rfl⟩
  | span :: rest, h => by
      obtain ⟨bytes, hbytes⟩ := h span (List.Mem.head _)
      obtain ⟨tokens, htokens⟩ :=
        resolveTokens_of_provenance files rest
          (fun s hs => h s (List.Mem.tail _ hs))
      exact ⟨⟨span, spanBytes bytes.data.toList span⟩ :: tokens, by
        unfold resolveTokens
        rw [hbytes, htokens]⟩

/-! ## Raw statements -/

/-- Proof payload of a `$p` statement, carried for the step-4 joints.
Every consumed token's span is retained (parentheses included), so the
statement is an exact derivation witness — reflection recovers the
token stream from the statements, never from an authored unparser. -/
inductive ProofPayload where
  | normal (steps : List LocatedName)
  | compressed (openParen : LocatedByteSpan) (header : List LocatedName)
      (closeParen : LocatedByteSpan) (words : List LocatedToken)
deriving DecidableEq, Repr

/-- One raw Metamath statement with full provenance.  `site` is the
keyword token's span (the brace token's for scoping statements). -/
inductive RawStatement where
  | openScope (site : LocatedByteSpan)
  | closeScope (site : LocatedByteSpan)
  | constDecl (site : LocatedByteSpan) (names : List LocatedName)
      (terminator : LocatedByteSpan)
  | varDecl (site : LocatedByteSpan) (names : List LocatedName)
      (terminator : LocatedByteSpan)
  | djDecl (site : LocatedByteSpan) (names : List LocatedName)
      (terminator : LocatedByteSpan)
  | floating (site : LocatedByteSpan) (label typecode variableName : LocatedName)
      (terminator : LocatedByteSpan)
  | essential (site : LocatedByteSpan) (label typecode : LocatedName)
      (body : List LocatedName) (terminator : LocatedByteSpan)
  | axiomatic (site : LocatedByteSpan) (label typecode : LocatedName)
      (body : List LocatedName) (terminator : LocatedByteSpan)
  | provable (site : LocatedByteSpan) (label typecode : LocatedName)
      (body : List LocatedName) (proof : ProofPayload)
      (separator terminator : LocatedByteSpan)
deriving DecidableEq, Repr

/-- Token spans of a proof payload, in source order. -/
def ProofPayload.tokenSpans : ProofPayload → List LocatedByteSpan
  | .normal steps => steps.map (·.span)
  | .compressed openParen header closeParen words =>
      openParen :: header.map (·.span) ++
        closeParen :: words.map (·.span)

/-- Exact token spans of a statement, in source order — the derivation
witness carried by segmentation. -/
def RawStatement.tokenSpans : RawStatement → List LocatedByteSpan
  | .openScope site => [site]
  | .closeScope site => [site]
  | .constDecl site names terminator =>
      site :: names.map (·.span) ++ [terminator]
  | .varDecl site names terminator =>
      site :: names.map (·.span) ++ [terminator]
  | .djDecl site names terminator =>
      site :: names.map (·.span) ++ [terminator]
  | .floating site label typecode variableName terminator =>
      [label.span, site, typecode.span, variableName.span, terminator]
  | .essential site label typecode body terminator =>
      label.span :: site :: typecode.span ::
        body.map (·.span) ++ [terminator]
  | .axiomatic site label typecode body terminator =>
      label.span :: site :: typecode.span ::
        body.map (·.span) ++ [terminator]
  | .provable site label typecode body proof separator terminator =>
      label.span :: site :: typecode.span :: body.map (·.span) ++
        separator :: proof.tokenSpans ++ [terminator]

/-! ## Segmentation rejections -/

inductive StatementError where
  | missingLabel
  | danglingLabel
  | strayStatementTerminator
  | strayProofSeparator
  | unknownKeyword
  | invalidLabelToken
  | invalidMathToken
  | invalidProofToken
  | invalidCompressedWord
  | floatingArity
  | missingTypecode
  | missingProofSeparator
  | scopeInsideStatement
  | unterminatedStatement
deriving DecidableEq, Repr

structure StatementRejection where
  site : LocatedByteSpan
  error : StatementError
deriving DecidableEq, Repr

inductive SegResult (α : Type _) where
  | ok (value : α)
  | rejected (rejection : StatementRejection)
deriving DecidableEq, Repr

/-! ## The segmentation state machine

One mode per open statement shape; the recursion is structural on the
token list (exactly one token consumed per step). -/

inductive CollectKind where
  | constants
  | variables
  | disjoint
deriving DecidableEq, Repr

inductive SegMode where
  | top
  | pendingLabel (label : LocatedName)
  | collecting (kind : CollectKind) (site : LocatedByteSpan)
      (acc : List LocatedName)
  | floatBody (site : LocatedByteSpan) (label : LocatedName)
      (acc : List LocatedName)
  | essentialBody (site : LocatedByteSpan) (label : LocatedName)
      (acc : List LocatedName)
  | axiomBody (site : LocatedByteSpan) (label : LocatedName)
      (acc : List LocatedName)
  | provableBody (site : LocatedByteSpan) (label : LocatedName)
      (acc : List LocatedName)
  | proofDecide (site : LocatedByteSpan) (label : LocatedName)
      (formula : List LocatedName) (separator : LocatedByteSpan)
  | proofNormal (site : LocatedByteSpan) (label : LocatedName)
      (formula : List LocatedName) (separator : LocatedByteSpan)
      (acc : List LocatedName)
  | proofHeader (site : LocatedByteSpan) (label : LocatedName)
      (formula : List LocatedName) (separator openParen : LocatedByteSpan)
      (acc : List LocatedName)
  | proofWords (site : LocatedByteSpan) (label : LocatedName)
      (formula : List LocatedName)
      (separator openParen closeParen : LocatedByteSpan)
      (header : List LocatedName) (acc : List LocatedToken)
deriving DecidableEq, Repr

/-- Keyword classification for dispatch. -/
def isDollarHeaded (tok : List UInt8) : Bool :=
  match tok with
  | b :: _ => b = dollarByte
  | [] => false

/-- Split an accumulated formula into typecode and body. -/
def splitFormula (site : LocatedByteSpan) (acc : List LocatedName) :
    SegResult (LocatedName × List LocatedName) :=
  match acc.reverse with
  | [] => .rejected ⟨site, .missingTypecode⟩
  | typecode :: body => .ok (typecode, body)

/-- One segmentation step: consume `tok` in `mode`, producing emitted
statements (chronological) and the next mode. -/
def segmentStep (mode : SegMode) (tok : LocatedToken) :
    SegResult (List RawStatement × SegMode) :=
  match mode with
  | .top =>
      if tok.bytes = scopeOpenBytes then
        .ok ([.openScope tok.span], .top)
      else if tok.bytes = scopeCloseBytes then
        .ok ([.closeScope tok.span], .top)
      else if tok.bytes = constKeywordBytes then
        .ok ([], .collecting .constants tok.span [])
      else if tok.bytes = varKeywordBytes then
        .ok ([], .collecting .variables tok.span [])
      else if tok.bytes = djKeywordBytes then
        .ok ([], .collecting .disjoint tok.span [])
      else if statementKeyword tok.bytes then
        .rejected ⟨tok.span, .missingLabel⟩
      else if tok.bytes = statementEndBytes then
        .rejected ⟨tok.span, .strayStatementTerminator⟩
      else if tok.bytes = proofSeparatorBytes then
        .rejected ⟨tok.span, .strayProofSeparator⟩
      else if isDollarHeaded tok.bytes then
        .rejected ⟨tok.span, .unknownKeyword⟩
      else if labelBytesValid tok.bytes then
        .ok ([], .pendingLabel tok.toName)
      else
        .rejected ⟨tok.span, .invalidLabelToken⟩
  | .pendingLabel label =>
      if tok.bytes = floatKeywordBytes then
        .ok ([], .floatBody tok.span label [])
      else if tok.bytes = essentialKeywordBytes then
        .ok ([], .essentialBody tok.span label [])
      else if tok.bytes = axiomKeywordBytes then
        .ok ([], .axiomBody tok.span label [])
      else if tok.bytes = provableKeywordBytes then
        .ok ([], .provableBody tok.span label [])
      else
        .rejected ⟨tok.span, .danglingLabel⟩
  | .collecting kind site acc =>
      if tok.bytes = statementEndBytes then
        let names := acc.reverse
        match kind with
        | .constants => .ok ([.constDecl site names tok.span], .top)
        | .variables => .ok ([.varDecl site names tok.span], .top)
        | .disjoint => .ok ([.djDecl site names tok.span], .top)
      else if tok.bytes = scopeOpenBytes ∨ tok.bytes = scopeCloseBytes then
        .rejected ⟨tok.span, .scopeInsideStatement⟩
      else if isDollarHeaded tok.bytes then
        .rejected ⟨tok.span, .unknownKeyword⟩
      else if mathBytesValid tok.bytes then
        .ok ([], .collecting kind site (tok.toName :: acc))
      else
        .rejected ⟨tok.span, .invalidMathToken⟩
  | .floatBody site label acc =>
      if tok.bytes = statementEndBytes then
        match acc.reverse with
        | [typecode, variableName] =>
            .ok ([.floating site label typecode variableName tok.span],
              .top)
        | _ => .rejected ⟨site, .floatingArity⟩
      else if tok.bytes = scopeOpenBytes ∨ tok.bytes = scopeCloseBytes then
        .rejected ⟨tok.span, .scopeInsideStatement⟩
      else if isDollarHeaded tok.bytes then
        .rejected ⟨tok.span, .unknownKeyword⟩
      else if mathBytesValid tok.bytes then
        .ok ([], .floatBody site label (tok.toName :: acc))
      else
        .rejected ⟨tok.span, .invalidMathToken⟩
  | .essentialBody site label acc =>
      if tok.bytes = statementEndBytes then
        match splitFormula site acc with
        | .rejected r => .rejected r
        | .ok (typecode, body) =>
            .ok ([.essential site label typecode body tok.span], .top)
      else if tok.bytes = scopeOpenBytes ∨ tok.bytes = scopeCloseBytes then
        .rejected ⟨tok.span, .scopeInsideStatement⟩
      else if isDollarHeaded tok.bytes then
        .rejected ⟨tok.span, .unknownKeyword⟩
      else if mathBytesValid tok.bytes then
        .ok ([], .essentialBody site label (tok.toName :: acc))
      else
        .rejected ⟨tok.span, .invalidMathToken⟩
  | .axiomBody site label acc =>
      if tok.bytes = statementEndBytes then
        match splitFormula site acc with
        | .rejected r => .rejected r
        | .ok (typecode, body) =>
            .ok ([.axiomatic site label typecode body tok.span], .top)
      else if tok.bytes = scopeOpenBytes ∨ tok.bytes = scopeCloseBytes then
        .rejected ⟨tok.span, .scopeInsideStatement⟩
      else if isDollarHeaded tok.bytes then
        .rejected ⟨tok.span, .unknownKeyword⟩
      else if mathBytesValid tok.bytes then
        .ok ([], .axiomBody site label (tok.toName :: acc))
      else
        .rejected ⟨tok.span, .invalidMathToken⟩
  | .provableBody site label acc =>
      if tok.bytes = proofSeparatorBytes then
        .ok ([], .proofDecide site label acc tok.span)
      else if tok.bytes = statementEndBytes then
        .rejected ⟨site, .missingProofSeparator⟩
      else if tok.bytes = scopeOpenBytes ∨ tok.bytes = scopeCloseBytes then
        .rejected ⟨tok.span, .scopeInsideStatement⟩
      else if isDollarHeaded tok.bytes then
        .rejected ⟨tok.span, .unknownKeyword⟩
      else if mathBytesValid tok.bytes then
        .ok ([], .provableBody site label (tok.toName :: acc))
      else
        .rejected ⟨tok.span, .invalidMathToken⟩
  | .proofDecide site label formula separator =>
      if tok.bytes = parenOpenBytes then
        .ok ([], .proofHeader site label formula separator tok.span [])
      else if tok.bytes = statementEndBytes then
        -- an empty normal proof is representable only as `?`
        .rejected ⟨tok.span, .invalidProofToken⟩
      else if proofTokenValid tok.bytes then
        .ok ([], .proofNormal site label formula separator [tok.toName])
      else
        .rejected ⟨tok.span, .invalidProofToken⟩
  | .proofNormal site label formula separator acc =>
      if tok.bytes = statementEndBytes then
        match splitFormula site formula with
        | .rejected r => .rejected r
        | .ok (typecode, body) =>
            .ok ([.provable site label typecode body
              (.normal acc.reverse) separator tok.span], .top)
      else if proofTokenValid tok.bytes then
        .ok ([], .proofNormal site label formula separator
          (tok.toName :: acc))
      else
        .rejected ⟨tok.span, .invalidProofToken⟩
  | .proofHeader site label formula separator openParen acc =>
      if tok.bytes = parenCloseBytes then
        .ok ([], .proofWords site label formula separator openParen
          tok.span acc.reverse [])
      else if labelBytesValid tok.bytes then
        .ok ([], .proofHeader site label formula separator openParen
          (tok.toName :: acc))
      else
        .rejected ⟨tok.span, .invalidProofToken⟩
  | .proofWords site label formula separator openParen closeParen
      header acc =>
      if tok.bytes = statementEndBytes then
        -- an empty compressed proof body is not derivable ([MM §4.4.5])
        if acc.isEmpty then
          .rejected ⟨tok.span, .invalidCompressedWord⟩
        else
        match splitFormula site formula with
        | .rejected r => .rejected r
        | .ok (typecode, body) =>
            .ok ([.provable site label typecode body
              (.compressed openParen header closeParen acc.reverse)
              separator tok.span], .top)
      else if compressedWordValid tok.bytes then
        .ok ([], .proofWords site label formula separator openParen
          closeParen header (tok :: acc))
      else
        .rejected ⟨tok.span, .invalidCompressedWord⟩

/-- The mode's anchor span, for end-of-input rejections. -/
def SegMode.site : SegMode → Option LocatedByteSpan
  | .top => none
  | .pendingLabel label => some label.span
  | .collecting _ site _ => some site
  | .floatBody site _ _ => some site
  | .essentialBody site _ _ => some site
  | .axiomBody site _ _ => some site
  | .provableBody site _ _ => some site
  | .proofDecide site _ _ _ => some site
  | .proofNormal site _ _ _ _ => some site
  | .proofHeader site _ _ _ _ _ => some site
  | .proofWords site _ _ _ _ _ _ _ => some site

/-- Run the machine over the whole stream. -/
def segmentRun : List LocatedToken → SegMode → List RawStatement →
    SegResult (List RawStatement)
  | [], mode, acc =>
      match mode.site with
      | none => .ok acc.reverse
      | some site => .rejected ⟨site, .unterminatedStatement⟩
  | tok :: rest, mode, acc =>
      match segmentStep mode tok with
      | .rejected r => .rejected r
      | .ok (emitted, nextMode) =>
          segmentRun rest nextMode (emitted.reverse ++ acc)

/-- Segment a resolved token stream into raw statements. -/
def segmentStatements (tokens : List LocatedToken) :
    SegResult (List RawStatement) :=
  segmentRun tokens .top []

/-! ## The fold: statements through the source GSLT's own gates -/

inductive FoldError where
  | undeclaredSymbol
  | operationRejected (operation : SourceOperation)
  | unclosedScope
deriving DecidableEq, Repr

structure FoldRejection where
  site : LocatedByteSpan
  error : FoldError
deriving DecidableEq, Repr

inductive FoldResult (α : Type _) where
  | ok (value : α)
  | rejected (rejection : FoldRejection)
deriving DecidableEq, Repr

/-- A body token is a variable occurrence exactly while its `$v` declaration
is active, else a constant occurrence when declared `$c`; otherwise it is
rejected at its own span.  Global namespace disjointness makes the branch
order immaterial. -/
def tagSymbol (state : SourceState) (tok : LocatedName) :
    FoldResult Metamath.Verify.Sym :=
  if state.activeVariables.contains tok.name then
    .ok (.var tok.name)
  else if state.declaredConstants.contains tok.name then
    .ok (.const tok.name)
  else
    .rejected ⟨tok.span, .undeclaredSymbol⟩

def tagBody (state : SourceState) :
    List LocatedName → FoldResult (List Metamath.Verify.Sym)
  | [] => .ok []
  | tok :: rest =>
      match tagSymbol state tok with
      | .rejected r => .rejected r
      | .ok sym =>
          match tagBody state rest with
          | .rejected r => .rejected r
          | .ok syms => .ok (sym :: syms)

/-- A `$p` statement's carried obligation for the step-4 lifecycle
joints (`NormalTheoremStep` / `CompressedTheoremStep`), which demand
proof-tree evidence this fold cannot fabricate.  The declaration
effect (`insertAssertion?`) has already been applied when an
obligation is emitted. -/
structure TheoremObligation where
  site : LocatedByteSpan
  label : LocatedName
  formula : ConstantHeadedFormula
  proof : ProofPayload
deriving DecidableEq, Repr

/-- Apply one raw statement through the gates. -/
def applyStatement (state : SourceState) :
    RawStatement → FoldResult (SourceState × List TheoremObligation)
  | .openScope site =>
      match applyLocalPayload? .openScope state with
      | some next => .ok (next, [])
      | none => .rejected ⟨site, .operationRejected .openScope⟩
  | .closeScope site =>
      match applyLocalPayload? .closeScope state with
      | none => .rejected ⟨site, .operationRejected .closeScope⟩
      | some middle =>
          match applyLocalPayload? .completeBlock middle with
          | none => .rejected ⟨site, .operationRejected .completeBlock⟩
          | some next => .ok (next, [])
  | .constDecl site names _terminator =>
      match applyLocalPayload?
          (.declareConstants (names.map (·.name))) state with
      | some next => .ok (next, [])
      | none => .rejected ⟨site, .operationRejected .declareConstants⟩
  | .varDecl site names _terminator =>
      match applyLocalPayload?
          (.declareVariables (names.map (·.name))) state with
      | some next => .ok (next, [])
      | none => .rejected ⟨site, .operationRejected .declareVariables⟩
  | .djDecl site names _terminator =>
      match applyLocalPayload?
          (.declareDisjoint (names.map (·.name))) state with
      | some next => .ok (next, [])
      | none => .rejected ⟨site, .operationRejected .declareDisjoint⟩
  | .floating site label typecode variableName _terminator =>
      match applyLocalPayload?
          (.declareFloating label.name typecode.name variableName.name)
          state with
      | some next => .ok (next, [])
      | none => .rejected ⟨site, .operationRejected .declareFloating⟩
  | .essential site label typecode body _terminator =>
      match tagBody state body with
      | .rejected r => .rejected r
      | .ok syms =>
          match applyLocalPayload?
              (.declareEssential label.name ⟨typecode.name, syms⟩)
              state with
          | some next => .ok (next, [])
          | none =>
              .rejected ⟨site, .operationRejected .declareEssential⟩
  | .axiomatic site label typecode body _terminator =>
      match tagBody state body with
      | .rejected r => .rejected r
      | .ok syms =>
          match applyLocalPayload?
              (.declareAxiom label.name ⟨typecode.name, syms⟩) state with
          | some next => .ok (next, [])
          | none => .rejected ⟨site, .operationRejected .declareAxiom⟩
  | .provable site label typecode body proof _separator _terminator =>
      match tagBody state body with
      | .rejected r => .rejected r
      | .ok syms =>
          match insertAssertion? state label.name
              ⟨typecode.name, syms⟩ with
          | none =>
              .rejected ⟨site, .operationRejected
                (match proof with
                  | .normal _ => .checkTheoremNormal
                  | .compressed _ _ _ _ => .checkTheoremCompressed)⟩
          | some next =>
              .ok (next,
                [⟨site, label, ⟨typecode.name, syms⟩, proof⟩])

/-- Fold a statement list from a state, collecting `$p` obligations in
chronological order. -/
def foldStatements : SourceState → List RawStatement →
    FoldResult (SourceState × List TheoremObligation)
  | state, [] => .ok (state, [])
  | state, stmt :: rest =>
      match applyStatement state stmt with
      | .rejected r => .rejected r
      | .ok (next, obligations) =>
          match foldStatements next rest with
          | .rejected r => .rejected r
          | .ok (final, restObligations) =>
              .ok (final, obligations ++ restObligations)

/-! ## The composed pipeline -/

inductive PipelineError where
  | include (rejection : IncludeRejection)
  | resolution
  | statement (rejection : StatementRejection)
  | fold (rejection : FoldRejection)
  | incompleteSource
deriving DecidableEq, Repr

inductive PipelineResult where
  | ok (state : SourceState) (obligations : List TheoremObligation)
  | error (error : PipelineError)
deriving DecidableEq

/-- Scope-site scan over the statement stream: the spans of currently
unclosed `${` statements, innermost first. -/
def scopeSites : List RawStatement → List LocatedByteSpan →
    List LocatedByteSpan
  | [], stack => stack
  | .openScope site :: rest, stack => scopeSites rest (site :: stack)
  | .closeScope _ :: rest, stack => scopeSites rest stack.tail
  | _ :: rest, stack => scopeSites rest stack

/-- Whole forward composition: source DAG → located spans → include
expansion → statements → accepted source state, every stage carrying
exact provenance. -/
def runSource (files : FileMap) (policy : IncludePolicy)
    (root : String) (fuel : Nat := 100) : PipelineResult :=
  match expandDatabase files policy root fuel with
  | .rejected r => .error (.include r)
  | .ok spans =>
      match resolveTokens files spans with
      | none => .error .resolution
      | some tokens =>
          match segmentStatements tokens with
          | .rejected r => .error (.statement r)
          | .ok statements =>
              match foldStatements initialState statements with
              | .rejected r => .error (.fold r)
              | .ok (state, obligations) =>
                  if sourceStateComplete state then
                    .ok state obligations
                  else
                    match scopeSites statements [] with
                    | site :: _ =>
                        .error (.fold ⟨site, .unclosedScope⟩)
                    | [] => .error .incompleteSource

/-- The resolution stage never fails on expansion output: the step-1
provenance theorem supplies every span's file. -/
theorem runSource_no_resolution_failure
    (files : FileMap) (policy : IncludePolicy) (root : String)
    (fuel : Nat) :
    runSource files policy root fuel ≠ .error .resolution := by
  intro h
  simp only [runSource] at h
  cases hexp : expandDatabase files policy root fuel with
  | rejected r =>
      simp only [hexp] at h
      exact nomatch h
  | ok spans =>
      simp only [hexp] at h
      obtain ⟨tokens, htokens⟩ :=
        resolveTokens_of_provenance files spans
          (fun s hs =>
            (expandDatabase_provenance hexp s hs).imp
              fun bytes hb => hb.1)
      simp only [htokens] at h
      cases hseg : segmentStatements tokens with
      | rejected r =>
          simp only [hseg] at h
          exact nomatch h
      | ok statements =>
          simp only [hseg] at h
          cases hfold : foldStatements initialState statements with
          | rejected r =>
              simp only [hfold] at h
              exact nomatch h
          | ok pair =>
              obtain ⟨state, obligations⟩ := pair
              simp only [hfold] at h
              cases hcomplete : sourceStateComplete state with
              | false =>
                  rw [if_neg (by simp [hcomplete])] at h
                  cases hscan : scopeSites statements [] with
                  | nil => simp only [hscan] at h; exact nomatch h
                  | cons site rest =>
                      simp only [hscan] at h
                      exact nomatch h
              | true =>
                  simp only [hcomplete, ↓reduceIte] at h
                  exact nomatch h

/-! ## Acceptance validity end to end -/

theorem applyStatement_valid {state next : SourceState}
    {stmt : RawStatement} {obligations : List TheoremObligation}
    (h : applyStatement state stmt = .ok (next, obligations)) :
    sourceStateValid next = true := by
  cases stmt with
  | openScope site =>
      cases happ : applyLocalPayload? .openScope state with
      | none =>
          simp only [applyStatement, happ] at h
          exact nomatch h
      | some s =>
          simp only [applyStatement, happ] at h
          cases h
          exact applyLocalPayload?_valid happ
  | closeScope site =>
      cases happ : applyLocalPayload? .closeScope state with
      | none =>
          simp only [applyStatement, happ] at h
          exact nomatch h
      | some middle =>
          simp only [applyStatement, happ] at h
          cases hcomplete : applyLocalPayload? .completeBlock middle with
          | none =>
              simp only [hcomplete] at h
              exact nomatch h
          | some s =>
              simp only [hcomplete] at h
              cases h
              exact applyLocalPayload?_valid hcomplete
  | constDecl site names terminator =>
      cases happ : applyLocalPayload?
          (.declareConstants (names.map (·.name))) state with
      | none =>
          simp only [applyStatement, happ] at h
          exact nomatch h
      | some s =>
          simp only [applyStatement, happ] at h
          cases h
          exact applyLocalPayload?_valid happ
  | varDecl site names terminator =>
      cases happ : applyLocalPayload?
          (.declareVariables (names.map (·.name))) state with
      | none =>
          simp only [applyStatement, happ] at h
          exact nomatch h
      | some s =>
          simp only [applyStatement, happ] at h
          cases h
          exact applyLocalPayload?_valid happ
  | djDecl site names terminator =>
      cases happ : applyLocalPayload?
          (.declareDisjoint (names.map (·.name))) state with
      | none =>
          simp only [applyStatement, happ] at h
          exact nomatch h
      | some s =>
          simp only [applyStatement, happ] at h
          cases h
          exact applyLocalPayload?_valid happ
  | floating site label typecode variableName terminator =>
      cases happ : applyLocalPayload?
          (.declareFloating label.name typecode.name variableName.name)
          state with
      | none =>
          simp only [applyStatement, happ] at h
          exact nomatch h
      | some s =>
          simp only [applyStatement, happ] at h
          cases h
          exact applyLocalPayload?_valid happ
  | essential site label typecode body terminator =>
      cases htag : tagBody state body with
      | rejected r =>
          simp only [applyStatement, htag] at h
          exact nomatch h
      | ok syms =>
          simp only [applyStatement, htag] at h
          cases happ : applyLocalPayload?
              (.declareEssential label.name ⟨typecode.name, syms⟩)
              state with
          | none =>
              simp only [happ] at h
              exact nomatch h
          | some s =>
              simp only [happ] at h
              cases h
              exact applyLocalPayload?_valid happ
  | axiomatic site label typecode body terminator =>
      cases htag : tagBody state body with
      | rejected r =>
          simp only [applyStatement, htag] at h
          exact nomatch h
      | ok syms =>
          simp only [applyStatement, htag] at h
          cases happ : applyLocalPayload?
              (.declareAxiom label.name ⟨typecode.name, syms⟩) state with
          | none =>
              simp only [happ] at h
              exact nomatch h
          | some s =>
              simp only [happ] at h
              cases h
              exact applyLocalPayload?_valid happ
  | provable site label typecode body proof separator terminator =>
      cases htag : tagBody state body with
      | rejected r =>
          simp only [applyStatement, htag] at h
          exact nomatch h
      | ok syms =>
          simp only [applyStatement, htag] at h
          cases hins : insertAssertion? state label.name
              ⟨typecode.name, syms⟩ with
          | none =>
              simp only [hins] at h
              exact nomatch h
          | some s =>
              simp only [hins] at h
              cases h
              exact insertAssertion?_valid hins

theorem foldStatements_valid :
    ∀ {statements : List RawStatement} {state final : SourceState}
      {obligations : List TheoremObligation},
      sourceStateValid state = true →
      foldStatements state statements = .ok (final, obligations) →
      sourceStateValid final = true
  | [], state, final, obligations, hvalid, h => by
      simp only [foldStatements] at h
      cases h
      exact hvalid
  | stmt :: rest, state, final, obligations, hvalid, h => by
      simp only [foldStatements] at h
      cases happ : applyStatement state stmt with
      | rejected r =>
          simp only [happ] at h
          exact nomatch h
      | ok pair =>
          obtain ⟨next, stepObligations⟩ := pair
          simp only [happ] at h
          cases hrest : foldStatements next rest with
          | rejected r =>
              simp only [hrest] at h
              exact nomatch h
          | ok finalPair =>
              obtain ⟨final', restObligations⟩ := finalPair
              simp only [hrest] at h
              cases h
              exact foldStatements_valid
                (applyStatement_valid happ) hrest

/-- **Composed acceptance completeness**: the whole pipeline accepts only a
valid source state with no unmatched block and no pending block completion. -/
theorem runSource_ok_complete {files : FileMap} {policy : IncludePolicy}
    {root : String} {fuel : Nat} {state : SourceState}
    {obligations : List TheoremObligation}
    (h : runSource files policy root fuel = .ok state obligations) :
    sourceStateComplete state = true := by
  simp only [runSource] at h
  cases hexp : expandDatabase files policy root fuel with
  | rejected r =>
      simp only [hexp] at h
      exact nomatch h
  | ok spans =>
      simp only [hexp] at h
      cases hres : resolveTokens files spans with
      | none =>
          simp only [hres] at h
          exact nomatch h
      | some tokens =>
          simp only [hres] at h
          cases hseg : segmentStatements tokens with
          | rejected r =>
              simp only [hseg] at h
              exact nomatch h
          | ok statements =>
              simp only [hseg] at h
              cases hfold : foldStatements initialState statements with
              | rejected r =>
                  simp only [hfold] at h
                  exact nomatch h
              | ok pair =>
                  obtain ⟨final, obs⟩ := pair
                  simp only [hfold] at h
                  cases hcomplete : sourceStateComplete final with
                  | false =>
                      rw [if_neg (by simp [hcomplete])] at h
                      cases hscan : scopeSites statements [] with
                      | nil => simp only [hscan] at h; exact nomatch h
                      | cons site rest =>
                          simp only [hscan] at h
                          exact nomatch h
                  | true =>
                      simp only [hcomplete, ↓reduceIte] at h
                      exact (PipelineResult.ok.inj h).1 ▸ hcomplete

/-- Whatever source state the whole pipeline accepts is locally valid. -/
theorem runSource_ok_valid {files : FileMap} {policy : IncludePolicy}
    {root : String} {fuel : Nat} {state : SourceState}
    {obligations : List TheoremObligation}
    (h : runSource files policy root fuel = .ok state obligations) :
    sourceStateValid state = true := by
  have complete := runSource_ok_complete h
  simp [sourceStateComplete] at complete
  exact complete.1.1

/-- Scope accounting through the fold: the semantic scope stack's depth
tracks the statement-stream scan exactly, and readiness (no pending
block completions) is restored after every accepted statement. -/
theorem foldStatements_scopes :
    ∀ {statements : List RawStatement} {state final : SourceState}
      {obligations : List TheoremObligation}
      (stack : List LocatedByteSpan),
      foldStatements state statements = .ok (final, obligations) →
      state.scopes.length = stack.length →
      state.pendingBlockCompletions = 0 →
      final.scopes.length = (scopeSites statements stack).length ∧
        final.pendingBlockCompletions = 0
  | [], state, final, obligations, stack, h, hlen, hpend => by
      simp only [foldStatements] at h
      cases h
      exact ⟨hlen, hpend⟩
  | stmt :: rest, state, final, obligations, stack, h, hlen, hpend => by
      cases stmt with
      | openScope site =>
          simp only [foldStatements] at h
          cases happ : applyLocalPayload? .openScope state with
          | none => simp only [applyStatement, happ] at h; exact nomatch h
          | some next =>
              simp only [applyStatement, happ] at h
              cases hrest : foldStatements next rest with
              | rejected r => simp only [hrest] at h; exact nomatch h
              | ok finalPair =>
                  obtain ⟨final', restObs⟩ := finalPair
                  simp only [hrest] at h
                  cases h
                  have hdelta := openScope?_scopes_pending
                    (show openScope? state = some next from happ)
                  exact foldStatements_scopes (site :: stack) hrest
                    (by rw [hdelta.1, hlen]; rfl)
                    (by rw [hdelta.2]; exact hpend)
      | closeScope site =>
          simp only [foldStatements] at h
          cases happ : applyLocalPayload? .closeScope state with
          | none => simp only [applyStatement, happ] at h; exact nomatch h
          | some middle =>
              simp only [applyStatement, happ] at h
              cases hcomp : applyLocalPayload? .completeBlock middle with
              | none => simp only [hcomp] at h; exact nomatch h
              | some next =>
                  simp only [hcomp] at h
                  cases hrest : foldStatements next rest with
                  | rejected r => simp only [hrest] at h; exact nomatch h
                  | ok finalPair =>
                      obtain ⟨final', restObs⟩ := finalPair
                      simp only [hrest] at h
                      cases h
                      have h1 := closeScope?_scopes_pending
                        (show closeScope? state = some middle from happ)
                      have h2 := completeBlock?_scopes_pending
                        (show completeBlock? middle = some next from hcomp)
                      refine foldStatements_scopes stack.tail hrest ?_ ?_
                      · rw [h2.1]
                        have htail := List.length_tail (l := stack)
                        omega
                      · rw [h2.2, h1.2, hpend]
      | constDecl site names terminator =>
          simp only [foldStatements] at h
          cases happ : applyLocalPayload?
              (.declareConstants (names.map (·.name))) state with
          | none => simp only [applyStatement, happ] at h; exact nomatch h
          | some next =>
              simp only [applyStatement, happ] at h
              cases hrest : foldStatements next rest with
              | rejected r => simp only [hrest] at h; exact nomatch h
              | ok finalPair =>
                  obtain ⟨final', restObs⟩ := finalPair
                  simp only [hrest] at h
                  cases h
                  have hdelta := declareConstants?_scopes_pending
                    (show declareConstants? state (names.map (·.name)) =
                      some next from happ)
                  exact foldStatements_scopes (statements := rest) stack hrest
                    (by rw [hdelta.1]; exact hlen)
                    (by rw [hdelta.2]; exact hpend)
      | varDecl site names terminator =>
          simp only [foldStatements] at h
          cases happ : applyLocalPayload?
              (.declareVariables (names.map (·.name))) state with
          | none => simp only [applyStatement, happ] at h; exact nomatch h
          | some next =>
              simp only [applyStatement, happ] at h
              cases hrest : foldStatements next rest with
              | rejected r => simp only [hrest] at h; exact nomatch h
              | ok finalPair =>
                  obtain ⟨final', restObs⟩ := finalPair
                  simp only [hrest] at h
                  cases h
                  have hdelta := declareVariables?_scopes_pending
                    (show declareVariables? state (names.map (·.name)) =
                      some next from happ)
                  exact foldStatements_scopes (statements := rest) stack hrest
                    (by rw [hdelta.1]; exact hlen)
                    (by rw [hdelta.2]; exact hpend)
      | djDecl site names terminator =>
          simp only [foldStatements] at h
          cases happ : applyLocalPayload?
              (.declareDisjoint (names.map (·.name))) state with
          | none => simp only [applyStatement, happ] at h; exact nomatch h
          | some next =>
              simp only [applyStatement, happ] at h
              cases hrest : foldStatements next rest with
              | rejected r => simp only [hrest] at h; exact nomatch h
              | ok finalPair =>
                  obtain ⟨final', restObs⟩ := finalPair
                  simp only [hrest] at h
                  cases h
                  have hdelta := declareDisjoint?_scopes_pending
                    (show declareDisjoint? state (names.map (·.name)) =
                      some next from happ)
                  exact foldStatements_scopes (statements := rest) stack hrest
                    (by rw [hdelta.1]; exact hlen)
                    (by rw [hdelta.2]; exact hpend)
      | floating site label typecode variableName terminator =>
          simp only [foldStatements] at h
          cases happ : applyLocalPayload?
              (.declareFloating label.name typecode.name
                variableName.name) state with
          | none => simp only [applyStatement, happ] at h; exact nomatch h
          | some next =>
              simp only [applyStatement, happ] at h
              cases hrest : foldStatements next rest with
              | rejected r => simp only [hrest] at h; exact nomatch h
              | ok finalPair =>
                  obtain ⟨final', restObs⟩ := finalPair
                  simp only [hrest] at h
                  cases h
                  have hdelta := declareFloating?_scopes_pending
                    (show declareFloating? state label.name typecode.name
                      variableName.name = some next from happ)
                  exact foldStatements_scopes (statements := rest) stack hrest
                    (by rw [hdelta.1]; exact hlen)
                    (by rw [hdelta.2]; exact hpend)
      | essential site label typecode body terminator =>
          simp only [foldStatements] at h
          cases htag : tagBody state body with
          | rejected r =>
              simp only [applyStatement, htag] at h
              exact nomatch h
          | ok syms =>
              simp only [applyStatement, htag] at h
              cases happ : applyLocalPayload?
                  (.declareEssential label.name ⟨typecode.name, syms⟩)
                  state with
              | none => simp only [happ] at h; exact nomatch h
              | some next =>
                  simp only [happ] at h
                  cases hrest : foldStatements next rest with
                  | rejected r => simp only [hrest] at h; exact nomatch h
                  | ok finalPair =>
                      obtain ⟨final', restObs⟩ := finalPair
                      simp only [hrest] at h
                      cases h
                      have hdelta := declareEssential?_scopes_pending
                        (show declareEssential? state label.name
                          ⟨typecode.name, syms⟩ = some next from happ)
                      exact foldStatements_scopes (statements := rest) stack hrest
                        (by rw [hdelta.1]; exact hlen)
                        (by rw [hdelta.2]; exact hpend)
      | axiomatic site label typecode body terminator =>
          simp only [foldStatements] at h
          cases htag : tagBody state body with
          | rejected r =>
              simp only [applyStatement, htag] at h
              exact nomatch h
          | ok syms =>
              simp only [applyStatement, htag] at h
              cases happ : applyLocalPayload?
                  (.declareAxiom label.name ⟨typecode.name, syms⟩)
                  state with
              | none => simp only [happ] at h; exact nomatch h
              | some next =>
                  simp only [happ] at h
                  cases hrest : foldStatements next rest with
                  | rejected r => simp only [hrest] at h; exact nomatch h
                  | ok finalPair =>
                      obtain ⟨final', restObs⟩ := finalPair
                      simp only [hrest] at h
                      cases h
                      have hdelta := insertAssertion?_scopes_pending
                        (show insertAssertion? state label.name
                          ⟨typecode.name, syms⟩ = some next from happ)
                      exact foldStatements_scopes (statements := rest) stack hrest
                        (by rw [hdelta.1]; exact hlen)
                        (by rw [hdelta.2]; exact hpend)
      | provable site label typecode body proof separator terminator =>
          simp only [foldStatements] at h
          cases htag : tagBody state body with
          | rejected r =>
              simp only [applyStatement, htag] at h
              exact nomatch h
          | ok syms =>
              simp only [applyStatement, htag] at h
              cases hins : insertAssertion? state label.name
                  ⟨typecode.name, syms⟩ with
              | none => simp only [hins] at h; exact nomatch h
              | some next =>
                  simp only [hins] at h
                  cases hrest : foldStatements next rest with
                  | rejected r => simp only [hrest] at h; exact nomatch h
                  | ok finalPair =>
                      obtain ⟨final', restObs⟩ := finalPair
                      simp only [hrest] at h
                      cases h
                      have hdelta := insertAssertion?_scopes_pending hins
                      exact foldStatements_scopes (statements := rest) stack hrest
                        (by rw [hdelta.1]; exact hlen)
                        (by rw [hdelta.2]; exact hpend)

/-- **The site-less fallback never fires**: incompleteness always has
an unclosed `${` to blame, by the scope-accounting invariant — every
rejection of the composed pipeline carries an exact source position. -/
theorem runSource_no_incompleteSource
    (files : FileMap) (policy : IncludePolicy) (root : String)
    (fuel : Nat) :
    runSource files policy root fuel ≠ .error .incompleteSource := by
  intro h
  simp only [runSource] at h
  cases hexp : expandDatabase files policy root fuel with
  | rejected r => simp only [hexp] at h; exact nomatch h
  | ok spans =>
      simp only [hexp] at h
      cases hres : resolveTokens files spans with
      | none => simp only [hres] at h; exact nomatch h
      | some tokens =>
          simp only [hres] at h
          cases hseg : segmentStatements tokens with
          | rejected r => simp only [hseg] at h; exact nomatch h
          | ok statements =>
              simp only [hseg] at h
              cases hfold : foldStatements initialState statements with
              | rejected r => simp only [hfold] at h; exact nomatch h
              | ok pair =>
                  obtain ⟨final, obs⟩ := pair
                  simp only [hfold] at h
                  cases hcomplete : sourceStateComplete final with
                  | true =>
                      simp only [hcomplete, ↓reduceIte] at h
                      exact nomatch h
                  | false =>
                      rw [if_neg (by simp [hcomplete])] at h
                      cases hscan : scopeSites statements [] with
                      | cons site rest =>
                          simp only [hscan] at h
                          exact nomatch h
                      | nil =>
                          obtain ⟨hlen, hpend⟩ :=
                            foldStatements_scopes [] hfold rfl rfl
                          rw [hscan] at hlen
                          have hscopes : final.scopes = [] :=
                            List.eq_nil_of_length_eq_zero hlen
                          have hvalid :=
                            foldStatements_valid initialState_valid hfold
                          rw [show sourceStateComplete final = true by
                            simp [sourceStateComplete, hvalid, hscopes,
                              hpend]] at hcomplete
                          exact nomatch hcomplete

/-! ## Reflection: exact witness recovery

The segmentation retains every consumed span, so the statement list
recovers the token-span stream exactly.  The invariant is the open
statement's consumed spans, in source order. -/

/-- Spans already consumed by the currently open statement, in source
order. -/
def SegMode.pendingSpans : SegMode → List LocatedByteSpan
  | .top => []
  | .pendingLabel label => [label.span]
  | .collecting _ site acc =>
      site :: (acc.reverse.map (·.span))
  | .floatBody site label acc =>
      label.span :: site :: (acc.reverse.map (·.span))
  | .essentialBody site label acc =>
      label.span :: site :: (acc.reverse.map (·.span))
  | .axiomBody site label acc =>
      label.span :: site :: (acc.reverse.map (·.span))
  | .provableBody site label acc =>
      label.span :: site :: (acc.reverse.map (·.span))
  | .proofDecide site label formula separator =>
      label.span :: site :: (formula.reverse.map (·.span)) ++ [separator]
  | .proofNormal site label formula separator acc =>
      label.span :: site :: (formula.reverse.map (·.span)) ++
        separator :: (acc.reverse.map (·.span))
  | .proofHeader site label formula separator openParen acc =>
      label.span :: site :: (formula.reverse.map (·.span)) ++
        separator :: openParen :: (acc.reverse.map (·.span))
  | .proofWords site label formula separator openParen closeParen
      header acc =>
      label.span :: site :: (formula.reverse.map (·.span)) ++
        separator :: openParen :: (header.map (·.span)) ++
        closeParen :: (acc.reverse.map (·.span))

theorem SegMode.pendingSpans_of_site_none {mode : SegMode}
    (h : mode.site = none) : mode.pendingSpans = [] := by
  cases mode <;> first | rfl | exact nomatch h

theorem splitFormula_ok {site : LocatedByteSpan} {acc : List LocatedName}
    {typecode : LocatedName} {body : List LocatedName}
    (h : splitFormula site acc = .ok (typecode, body)) :
    acc.reverse = typecode :: body := by
  unfold splitFormula at h
  cases hrev : acc.reverse with
  | nil => rw [hrev] at h; exact nomatch h
  | cons t b =>
      rw [hrev] at h
      cases h
      rfl

set_option linter.unusedSimpArgs false in
/-- One accepted segmentation step conserves spans: what the step emits
plus what remains pending is what was pending plus the consumed
token.  (The per-mode closers share one uniform simp set; the
unused-argument linter is scoped off for exactly this proof.) -/
theorem segmentStep_spans {mode : SegMode} {tok : LocatedToken}
    {emitted : List RawStatement} {next : SegMode}
    (h : segmentStep mode tok = .ok (emitted, next)) :
    emitted.flatMap RawStatement.tokenSpans ++ next.pendingSpans =
      mode.pendingSpans ++ [tok.span] := by
  cases mode with
  | top =>
      simp only [segmentStep] at h
      repeat' split at h
      all_goals cases h
      all_goals
        simp [SegMode.pendingSpans, RawStatement.tokenSpans,
          LocatedToken.toName]
  | pendingLabel label =>
      simp only [segmentStep] at h
      repeat' split at h
      all_goals cases h
      all_goals
        simp [SegMode.pendingSpans, RawStatement.tokenSpans,
          LocatedToken.toName]
  | collecting kind site acc =>
      simp only [segmentStep] at h
      repeat' split at h
      all_goals cases h
      all_goals
        simp [SegMode.pendingSpans, RawStatement.tokenSpans,
          LocatedToken.toName]
  | floatBody site label acc =>
      simp only [segmentStep] at h
      by_cases hterm : tok.bytes = statementEndBytes
      · rw [if_pos hterm] at h
        cases hrev : acc.reverse with
        | nil =>
            rw [hrev] at h
            exact nomatch h
        | cons typecode rest1 =>
            cases rest1 with
            | nil =>
                rw [hrev] at h
                exact nomatch h
            | cons variableName rest2 =>
                cases rest2 with
                | nil =>
                    rw [hrev] at h
                    cases h
                    simp [SegMode.pendingSpans, RawStatement.tokenSpans,
                      hrev]
                | cons w rest3 =>
                    rw [hrev] at h
                    exact nomatch h
      · rw [if_neg hterm] at h
        repeat' split at h
        all_goals cases h
        all_goals
          simp [SegMode.pendingSpans, RawStatement.tokenSpans,
            LocatedToken.toName]
  | essentialBody site label acc =>
      simp only [segmentStep] at h
      by_cases hterm : tok.bytes = statementEndBytes
      · rw [if_pos hterm] at h
        cases hsp : splitFormula site acc with
        | rejected r =>
            simp only [hsp] at h
            exact nomatch h
        | ok pair =>
            obtain ⟨typecode, body⟩ := pair
            simp only [hsp] at h
            cases h
            simp [SegMode.pendingSpans, RawStatement.tokenSpans,
              splitFormula_ok hsp]
      · rw [if_neg hterm] at h
        repeat' split at h
        all_goals cases h
        all_goals
          simp [SegMode.pendingSpans, RawStatement.tokenSpans,
            LocatedToken.toName]
  | axiomBody site label acc =>
      simp only [segmentStep] at h
      by_cases hterm : tok.bytes = statementEndBytes
      · rw [if_pos hterm] at h
        cases hsp : splitFormula site acc with
        | rejected r =>
            simp only [hsp] at h
            exact nomatch h
        | ok pair =>
            obtain ⟨typecode, body⟩ := pair
            simp only [hsp] at h
            cases h
            simp [SegMode.pendingSpans, RawStatement.tokenSpans,
              splitFormula_ok hsp]
      · rw [if_neg hterm] at h
        repeat' split at h
        all_goals cases h
        all_goals
          simp [SegMode.pendingSpans, RawStatement.tokenSpans,
            LocatedToken.toName]
  | provableBody site label acc =>
      simp only [segmentStep] at h
      repeat' split at h
      all_goals cases h
      all_goals
        simp [SegMode.pendingSpans, RawStatement.tokenSpans,
          LocatedToken.toName]
  | proofDecide site label formula separator =>
      simp only [segmentStep] at h
      repeat' split at h
      all_goals cases h
      all_goals
        simp [SegMode.pendingSpans, RawStatement.tokenSpans,
          LocatedToken.toName]
  | proofNormal site label formula separator acc =>
      simp only [segmentStep] at h
      by_cases hterm : tok.bytes = statementEndBytes
      · rw [if_pos hterm] at h
        cases hsp : splitFormula site formula with
        | rejected r =>
            simp only [hsp] at h
            exact nomatch h
        | ok pair =>
            obtain ⟨typecode, body⟩ := pair
            simp only [hsp] at h
            cases h
            simp [SegMode.pendingSpans, RawStatement.tokenSpans,
              ProofPayload.tokenSpans, splitFormula_ok hsp]
      · rw [if_neg hterm] at h
        repeat' split at h
        all_goals cases h
        all_goals
          simp [SegMode.pendingSpans, RawStatement.tokenSpans,
            LocatedToken.toName]
  | proofHeader site label formula separator openParen acc =>
      simp only [segmentStep] at h
      repeat' split at h
      all_goals cases h
      all_goals
        simp [SegMode.pendingSpans, RawStatement.tokenSpans,
          LocatedToken.toName]
  | proofWords site label formula separator openParen closeParen
      header acc =>
      simp only [segmentStep] at h
      by_cases hterm : tok.bytes = statementEndBytes
      · rw [if_pos hterm] at h
        by_cases hacc : acc.isEmpty
        · rw [if_pos hacc] at h
          exact nomatch h
        · rw [if_neg hacc] at h
          cases hsp : splitFormula site formula with
          | rejected r =>
              simp only [hsp] at h
              exact nomatch h
          | ok pair =>
              obtain ⟨typecode, body⟩ := pair
              simp only [hsp] at h
              cases h
              simp [SegMode.pendingSpans, RawStatement.tokenSpans,
                ProofPayload.tokenSpans, splitFormula_ok hsp]
      · rw [if_neg hterm] at h
        repeat' split at h
        all_goals cases h
        all_goals
          simp [SegMode.pendingSpans, RawStatement.tokenSpans,
            LocatedToken.toName]

/-- Run-level span conservation. -/
theorem segmentRun_spans :
    ∀ (tokens : List LocatedToken) (mode : SegMode)
      (acc statements : List RawStatement),
      segmentRun tokens mode acc = .ok statements →
      statements.flatMap RawStatement.tokenSpans =
        (acc.reverse.flatMap RawStatement.tokenSpans) ++
          (mode.pendingSpans ++ tokens.map (·.span))
  | [], mode, acc, statements, h => by
      simp only [segmentRun] at h
      cases hsite : mode.site with
      | none =>
          simp only [hsite] at h
          cases h
          simp [SegMode.pendingSpans_of_site_none hsite]
      | some site =>
          simp only [hsite] at h
          exact nomatch h
  | tok :: rest, mode, acc, statements, h => by
      simp only [segmentRun] at h
      cases hstep : segmentStep mode tok with
      | rejected r =>
          simp only [hstep] at h
          exact nomatch h
      | ok pair =>
          obtain ⟨emitted, nextMode⟩ := pair
          simp only [hstep] at h
          have hrec := segmentRun_spans rest nextMode
            (emitted.reverse ++ acc) statements h
          have hstepSpans := segmentStep_spans hstep
          have key : List.flatMap RawStatement.tokenSpans emitted ++
              (nextMode.pendingSpans ++ List.map (·.span) rest) =
              mode.pendingSpans ++ (tok.span :: List.map (·.span) rest) := by
            rw [← List.append_assoc, hstepSpans, List.append_assoc,
              List.singleton_append]
          rw [hrec]
          simp only [List.reverse_append, List.reverse_reverse,
            List.flatMap_append, List.append_assoc, List.map_cons, key]

/-- **Exact witness recovery**: an accepted segmentation flattens back
to precisely the input span stream.  The statements are the derivation
witness; no unparser exists or is needed. -/
theorem segmentStatements_tokenSpans {tokens : List LocatedToken}
    {statements : List RawStatement}
    (h : segmentStatements tokens = .ok statements) :
    statements.flatMap RawStatement.tokenSpans = tokens.map (·.span) := by
  have := segmentRun_spans tokens .top [] statements h
  simpa [SegMode.pendingSpans] using this

/-- Every span a statement carries is an input token's span. -/
theorem segmentStatements_span_provenance {tokens : List LocatedToken}
    {statements : List RawStatement}
    (h : segmentStatements tokens = .ok statements) :
    ∀ st ∈ statements, ∀ sp ∈ st.tokenSpans,
      sp ∈ tokens.map (·.span) := by
  intro st hst sp hsp
  rw [← segmentStatements_tokenSpans h]
  exact List.mem_flatMap.mpr ⟨st, hst, hsp⟩

/-- Resolution preserves the span stream. -/
theorem resolveTokens_spans (files : FileMap) :
    ∀ {spans : List LocatedByteSpan} {tokens : List LocatedToken},
      resolveTokens files spans = some tokens →
      tokens.map (·.span) = spans
  | [], tokens, h => by
      simp only [resolveTokens] at h
      cases h
      rfl
  | span :: rest, tokens, h => by
      simp only [resolveTokens] at h
      cases hfile : files span.fileId with
      | none => simp only [hfile] at h; exact nomatch h
      | some content =>
          simp only [hfile] at h
          cases hrest : resolveTokens files rest with
          | none => simp only [hrest] at h; exact nomatch h
          | some tokens' =>
              simp only [hrest] at h
              cases h
              simp [resolveTokens_spans files hrest]

/-! ## Obligation provenance through the fold -/

/-- Every obligation an accepted statement emits sites inside that
statement's own spans. -/
theorem applyStatement_obligations {state next : SourceState}
    {stmt : RawStatement} {obligations : List TheoremObligation}
    (h : applyStatement state stmt = .ok (next, obligations)) :
    ∀ ob ∈ obligations, ob.site ∈ stmt.tokenSpans := by
  cases stmt with
  | openScope site =>
      cases happ : applyLocalPayload? .openScope state with
      | none => simp only [applyStatement, happ] at h; exact nomatch h
      | some s =>
          simp only [applyStatement, happ] at h
          cases h
          intro ob hob
          exact nomatch hob
  | closeScope site =>
      cases happ : applyLocalPayload? .closeScope state with
      | none => simp only [applyStatement, happ] at h; exact nomatch h
      | some middle =>
          simp only [applyStatement, happ] at h
          cases hcomplete : applyLocalPayload? .completeBlock middle with
          | none => simp only [hcomplete] at h; exact nomatch h
          | some s =>
              simp only [hcomplete] at h
              cases h
              intro ob hob
              exact nomatch hob
  | constDecl site names terminator =>
      cases happ : applyLocalPayload?
          (.declareConstants (names.map (·.name))) state with
      | none => simp only [applyStatement, happ] at h; exact nomatch h
      | some s =>
          simp only [applyStatement, happ] at h
          cases h
          intro ob hob
          exact nomatch hob
  | varDecl site names terminator =>
      cases happ : applyLocalPayload?
          (.declareVariables (names.map (·.name))) state with
      | none => simp only [applyStatement, happ] at h; exact nomatch h
      | some s =>
          simp only [applyStatement, happ] at h
          cases h
          intro ob hob
          exact nomatch hob
  | djDecl site names terminator =>
      cases happ : applyLocalPayload?
          (.declareDisjoint (names.map (·.name))) state with
      | none => simp only [applyStatement, happ] at h; exact nomatch h
      | some s =>
          simp only [applyStatement, happ] at h
          cases h
          intro ob hob
          exact nomatch hob
  | floating site label typecode variableName terminator =>
      cases happ : applyLocalPayload?
          (.declareFloating label.name typecode.name variableName.name)
          state with
      | none => simp only [applyStatement, happ] at h; exact nomatch h
      | some s =>
          simp only [applyStatement, happ] at h
          cases h
          intro ob hob
          exact nomatch hob
  | essential site label typecode body terminator =>
      cases htag : tagBody state body with
      | rejected r =>
          simp only [applyStatement, htag] at h
          exact nomatch h
      | ok syms =>
          simp only [applyStatement, htag] at h
          cases happ : applyLocalPayload?
              (.declareEssential label.name ⟨typecode.name, syms⟩)
              state with
          | none => simp only [happ] at h; exact nomatch h
          | some s =>
              simp only [happ] at h
              cases h
              intro ob hob
              exact nomatch hob
  | axiomatic site label typecode body terminator =>
      cases htag : tagBody state body with
      | rejected r =>
          simp only [applyStatement, htag] at h
          exact nomatch h
      | ok syms =>
          simp only [applyStatement, htag] at h
          cases happ : applyLocalPayload?
              (.declareAxiom label.name ⟨typecode.name, syms⟩) state with
          | none => simp only [happ] at h; exact nomatch h
          | some s =>
              simp only [happ] at h
              cases h
              intro ob hob
              exact nomatch hob
  | provable site label typecode body proof separator terminator =>
      cases htag : tagBody state body with
      | rejected r =>
          simp only [applyStatement, htag] at h
          exact nomatch h
      | ok syms =>
          simp only [applyStatement, htag] at h
          cases hins : insertAssertion? state label.name
              ⟨typecode.name, syms⟩ with
          | none => simp only [hins] at h; exact nomatch h
          | some s =>
              simp only [hins] at h
              cases h
              intro ob hob
              rcases List.mem_singleton.mp hob with rfl
              simp [RawStatement.tokenSpans]

theorem foldStatements_obligations :
    ∀ {statements : List RawStatement} {state final : SourceState}
      {obligations : List TheoremObligation},
      foldStatements state statements = .ok (final, obligations) →
      ∀ ob ∈ obligations, ∃ st ∈ statements, ob.site ∈ st.tokenSpans
  | [], state, final, obligations, h => by
      simp only [foldStatements] at h
      cases h
      intro ob hob
      exact nomatch hob
  | stmt :: rest, state, final, obligations, h => by
      simp only [foldStatements] at h
      cases happ : applyStatement state stmt with
      | rejected r =>
          simp only [happ] at h
          exact nomatch h
      | ok pair =>
          obtain ⟨next, stepObligations⟩ := pair
          simp only [happ] at h
          cases hrest : foldStatements next rest with
          | rejected r =>
              simp only [hrest] at h
              exact nomatch h
          | ok finalPair =>
              obtain ⟨final', restObligations⟩ := finalPair
              simp only [hrest] at h
              cases h
              intro ob hob
              rcases List.mem_append.mp hob with hstep | htail
              · exact ⟨stmt, List.Mem.head _,
                  applyStatement_obligations happ ob hstep⟩
              · obtain ⟨st, hst, hsp⟩ :=
                  foldStatements_obligations hrest ob htail
                exact ⟨st, List.Mem.tail _ hst, hsp⟩

/-- **End-to-end obligation provenance**: every `$p` obligation the
composed pipeline carries sites at a genuine token of a genuine file of
the source DAG — steps 1 and 3 compose without splicing. -/
theorem runSource_obligation_provenance {files : FileMap}
    {policy : IncludePolicy} {root : String} {fuel : Nat}
    {state : SourceState} {obligations : List TheoremObligation}
    (h : runSource files policy root fuel = .ok state obligations) :
    ∀ ob ∈ obligations, ∃ bytes,
      files ob.site.fileId = some bytes ∧
        ob.site ∈ tokenize ob.site.fileId bytes := by
  simp only [runSource] at h
  cases hexp : expandDatabase files policy root fuel with
  | rejected r =>
      simp only [hexp] at h
      exact nomatch h
  | ok spans =>
      simp only [hexp] at h
      cases hres : resolveTokens files spans with
      | none =>
          simp only [hres] at h
          exact nomatch h
      | some tokens =>
          simp only [hres] at h
          cases hseg : segmentStatements tokens with
          | rejected r =>
              simp only [hseg] at h
              exact nomatch h
          | ok statements =>
              simp only [hseg] at h
              cases hfold : foldStatements initialState statements with
              | rejected r =>
                  simp only [hfold] at h
                  exact nomatch h
              | ok pair =>
                  obtain ⟨final, obs⟩ := pair
                  simp only [hfold] at h
                  cases hcomplete : sourceStateComplete final with
                  | false =>
                      rw [if_neg (by simp [hcomplete])] at h
                      cases hscan : scopeSites statements [] with
                      | nil => simp only [hscan] at h; exact nomatch h
                      | cons site rest =>
                          simp only [hscan] at h
                          exact nomatch h
                  | true =>
                      simp only [hcomplete, ↓reduceIte] at h
                      intro ob hob
                      have hob' : ob ∈ obs := by
                        simpa [(PipelineResult.ok.inj h).2] using hob
                      obtain ⟨st, hst, hsp⟩ :=
                        foldStatements_obligations hfold ob hob'
                      have hmem : ob.site ∈ tokens.map (·.span) :=
                        segmentStatements_span_provenance hseg st hst _ hsp
                      rw [resolveTokens_spans files hres] at hmem
                      exact expandDatabase_provenance hexp _ hmem

/-! ## Kernel-checked calibration

A two-file database exercising every statement form: constants,
variables, an included floating hypothesis, an axiom, a scoped `$d`, a
normal-proof theorem, and scope close.  All checks are kernel `decide`
— the entire forward pipeline reduces. -/

/-- `root`: `$c w $. $v x y $. $[ defs.mm $] ax1 $a w x $. ${ $d x y $.
th1 $p w x $= wx ax1 $. $}`; `defs.mm`: `wx $f w x $.`. -/
def fixtureFiles : FileMap := fun n =>
  if n = "root" then
    some (ByteArray.mk #[36, 99, 32, 119, 32, 36, 46, 32, 36, 118, 32,
      120, 32, 121, 32, 36, 46, 32, 36, 91, 32, 100, 101, 102, 115, 46,
      109, 109, 32, 36, 93, 32, 97, 120, 49, 32, 36, 97, 32, 119, 32,
      120, 32, 36, 46, 32, 36, 123, 32, 36, 100, 32, 120, 32, 121, 32,
      36, 46, 32, 116, 104, 49, 32, 36, 112, 32, 119, 32, 120, 32, 36,
      61, 32, 119, 120, 32, 97, 120, 49, 32, 36, 46, 32, 36, 125])
  else if n = "defs.mm" then
    some (ByteArray.mk #[119, 120, 32, 36, 102, 32, 119, 32, 120, 32,
      36, 46])
  else none

/-- Positive: the whole pipeline accepts, with the exact final state
and the single carried `$p` obligation. -/
def fixtureCheck : Bool :=
  match runSource fixtureFiles mmLean4CompatPolicy "root" with
  | .ok state obligations =>
      state.declaredConstants == ["w"] &&
      state.declaredVariables == ["x", "y"] &&
      state.usedLabels == ["wx", "ax1", "th1"] &&
      state.activeHypotheses ==
        [HypothesisView.floating "wx" "w" "x"] &&
      state.activeDistinctVariables == [] &&
      state.scopes.isEmpty &&
      state.pendingBlockCompletions == 0 &&
      (obligations.map fun ob => ob.label.name) == ["th1"] &&
      (obligations.map fun ob => ob.formula) ==
        [⟨"w", [.var "x"]⟩] &&
      (obligations.map fun ob => ob.proof) ==
        [.normal [⟨⟨"root", 73, 75⟩, "wx"⟩, ⟨⟨"root", 76, 79⟩, "ax1"⟩]]
  | .error _ => false

example : fixtureCheck = true := by decide

/-- Reflection sanity on the fixture: the segmented statements flatten
back to exactly the expanded span stream — the statements are the
derivation witness, with no unparser. -/
def fixtureWitnessCheck : Bool :=
  match expandDatabase fixtureFiles mmLean4CompatPolicy "root" with
  | .rejected _ => false
  | .ok spans =>
      match resolveTokens fixtureFiles spans with
      | none => false
      | some tokens =>
          match segmentStatements tokens with
          | .rejected _ => false
          | .ok statements =>
              (statements.flatMap RawStatement.tokenSpans) == spans

example : fixtureWitnessCheck = true := by decide

/-- Negative: a source ending with an open block is rejected at the
global completion gate, at the innermost unclosed `${`'s own span —
matching the authored block production and mm-lean4's `unclosedBlock`
verdict, with exact-position provenance. -/
example :
    runSource (fun n =>
        if n = "root" then some (ByteArray.mk #[36, 123]) else none)
      mmLean4CompatPolicy "root" =
      .error (.fold ⟨⟨"root", 0, 2⟩, .unclosedScope⟩) := by decide

/-- Positive boundary: nested, balanced empty blocks are complete. -/
example :
    runSource (fun n =>
        if n = "root" then
          some (ByteArray.mk #[36, 123, 32, 36, 123, 32,
            36, 125, 32, 36, 125])
        else none)
      mmLean4CompatPolicy "root" =
      .ok initialState [] := by decide

/-- Negative: `$f` without a label is rejected at the keyword's span. -/
example :
    runSource (fun n =>
        if n = "root" then
          some (ByteArray.mk #[36, 102, 32, 119, 32, 120, 32, 36, 46])
        else none)
      mmLean4CompatPolicy "root" =
      .error (.statement ⟨⟨"root", 0, 2⟩, .missingLabel⟩) := by decide

/-- Negative: an undeclared body symbol is rejected at its own span
(`q` in `ax1 $a w q $.`). -/
example :
    runSource (fun n =>
        if n = "root" then
          some (ByteArray.mk #[36, 99, 32, 119, 32, 36, 46, 32, 97,
            120, 49, 32, 36, 97, 32, 119, 32, 113, 32, 36, 46])
        else none)
      mmLean4CompatPolicy "root" =
      .error (.fold ⟨⟨"root", 17, 18⟩, .undeclaredSymbol⟩) := by decide

/-- Negative: a `$f` with one math token is rejected as an arity
violation at the keyword's span. -/
example :
    runSource (fun n =>
        if n = "root" then
          some (ByteArray.mk #[36, 99, 32, 119, 32, 36, 46, 32, 36,
            118, 32, 120, 32, 36, 46, 32, 102, 49, 32, 36, 102, 32,
            119, 32, 36, 46])
        else none)
      mmLean4CompatPolicy "root" =
      .error (.statement ⟨⟨"root", 19, 21⟩, .floatingArity⟩) := by
  decide

/-- Negative: redeclaring a constant is rejected by the gate at the
second `$c` site (global-namespace uniqueness). -/
example :
    runSource (fun n =>
        if n = "root" then
          some (ByteArray.mk #[36, 99, 32, 119, 32, 36, 46, 32, 36, 99,
            32, 119, 32, 36, 46])
        else none)
      mmLean4CompatPolicy "root" =
      .error (.fold ⟨⟨"root", 8, 10⟩,
        .operationRejected .declareConstants⟩) := by decide

/-- Negative: a would-be label containing `$` is charset-rejected at
its own span ([MM §4.1.1]). -/
example :
    runSource (fun n =>
        if n = "root" then
          some (ByteArray.mk #[97, 36, 98, 32, 36, 97, 32, 119, 32, 36,
            46])
        else none)
      mmLean4CompatPolicy "root" =
      .error (.statement ⟨⟨"root", 0, 3⟩, .invalidLabelToken⟩) := by
  decide

/-- Negative: a stray statement terminator. -/
example :
    runSource (fun n =>
        if n = "root" then some (ByteArray.mk #[36, 46]) else none)
      mmLean4CompatPolicy "root" =
      .error (.statement ⟨⟨"root", 0, 2⟩,
        .strayStatementTerminator⟩) := by decide

/-- Negative: an include of a missing file reports the step-1
rejection through the composed pipeline. -/
def missingIncludeCheck : Bool :=
  match runSource (fun n =>
      if n = "root" then
        some (ByteArray.mk #[36, 91, 32, 103, 104, 111, 115, 116, 32,
          36, 93])
      else none)
    mmLean4CompatPolicy "root" with
  | .error (.include r) =>
      match r.error with
      | .missingFile _ => true
      | _ => false
  | _ => false

example : missingIncludeCheck = true := by decide

/-- Positive (kernel-checked): an empty balanced block is accepted and
returns exactly the empty state. -/
example :
    runSource (fun n =>
        if n = "root" then
          some (ByteArray.mk #[36, 123, 32, 36, 125])
        else none)
      mmLean4CompatPolicy "root" = .ok initialState [] := by decide

/-- Negative (kernel-checked): a stray `$}` is rejected by the gate at
its own span. -/
example :
    runSource (fun n =>
        if n = "root" then some (ByteArray.mk #[36, 125]) else none)
      mmLean4CompatPolicy "root" =
      .error (.fold ⟨⟨"root", 0, 2⟩,
        .operationRejected .closeScope⟩) := by decide

/-- Negative (kernel-checked): with one inner block closed, the
unterminated **outer** `${` is the reported site. -/
example :
    runSource (fun n =>
        if n = "root" then
          some (ByteArray.mk #[36, 123, 32, 36, 123, 32, 36, 125])
        else none)
      mmLean4CompatPolicy "root" =
      .error (.fold ⟨⟨"root", 0, 2⟩, .unclosedScope⟩) := by decide

end Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
