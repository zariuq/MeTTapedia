import Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
import Mettapedia.Languages.Metamath.SourceGSLTStatementPlan

/-!
# The policy-indexed include / source-DAG GSLT

[MM §4.1.2] specifies preprocessing: comments and file inclusion.  The
governing sentences, verbatim from the book:

* "The token `$(` begins a comment and `$)` ends a comment. … they may
  not contain the 2-character sequences `$(` or `$)` (comments do not
  nest).  Comments are ignored (treated like white space) for the
  purpose of parsing, e.g., `$( $[ $)` is a comment."
* "A file inclusion command consists of `$[` followed by a file name
  followed by `$]`.  It is only allowed in the outermost scope … and
  must not be inside a statement … The file name may not contain a `$`
  or white space.  The file must exist."
* "Only the first reference to a given file is included; any later
  references to the same file (whether in the top-level file or in
  included files) cause the inclusion command to be ignored (treated
  like white space). … A file self-reference is ignored, as is any
  reference to the top-level file (to avoid loops)."

The common verifiers (metamath.exe, metamath-knife, mm-lean4) diverge
from the last sentence at exactly one point: a reference to a file that
is **currently being processed** (a self-reference or an include cycle)
is *rejected*, not ignored; mm-lean4's include driver checks its
`processing` set before its `seen` set and raises
`includeCycleDetected`.  A reference to a file already *fully* processed
is ignored by book and verifiers alike.

Per the ratified design, this module authors **one** include GSLT with a
policy toggle confined to that single branch:

* `bookSpecPolicy` — cyclic/self references are ignored ([MM §4.1.2]);
* `mmLean4CompatPolicy` — cyclic/self references are rejected with exact
  provenance (the refinement and verdict-matrix profile).

Everything else — comment stripping at token level, include-directive
recognition, outermost-scope and not-inside-statement gating
(complete token-boundary tracking, shared with mm-lean4's repaired scanner),
first-reference semantics via a `seen` set, chronological expansion, and
exact rejection provenance — is shared.  Expansion never splices text:
every emitted token is a located span of its *own* file
(`expandFile_provenance`), so file identity and byte offsets remain
proof-relevant evidence downstream.

Depth is bounded by explicit fuel, mirroring mm-lean4's
`ModeConfig.maxIncludeDepth` (default 100); with first-reference
suppression every acyclic run needs fuel no deeper than the number of
distinct files.

Positive and negative calibration fixtures close the module, including
the canonical self-include shape (metamath-test `test28`): accepted with
suppression by the book profile, rejected with exact site provenance by
the compatibility profile — and `expandFile_compat_ok` proves the two
profiles coincide on every input the compatibility profile accepts.
-/

namespace Mettapedia.Languages.Metamath.SourceGSLTIncludeDAG

open Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
open Mettapedia.Languages.Metamath.SourceGSLT
open Mettapedia.Languages.Metamath.SourceGSLTStatementPlan

/-! ## Byte-level token classification -/

private def planBytes (literal : CompiledLiteral) : List UInt8 :=
  literal.codepoints.map UInt8.ofNat

def dollarByte : UInt8 := UInt8.ofNat dollarCodepoint
def commentOpenBytes : List UInt8 :=
  planBytes sourceStatementPlan.commentOpen
def commentCloseBytes : List UInt8 :=
  planBytes sourceStatementPlan.commentClose
def includeOpenBytes : List UInt8 :=
  planBytes sourceStatementPlan.includeOpen
def includeCloseBytes : List UInt8 :=
  planBytes sourceStatementPlan.includeClose
def scopeOpenBytes : List UInt8 :=
  planBytes sourceStatementPlan.scopeOpen
def scopeCloseBytes : List UInt8 :=
  planBytes sourceStatementPlan.scopeClose
def statementEndBytes : List UInt8 :=
  planBytes sourceStatementPlan.statementEnd

/-- The four label-bearing statement keywords used after a preceding label:
`$f`, `$e`, `$a`, and `$p`.  This classifier belongs to statement dispatch;
the include-placement scanner uses complete token-boundary tracking below. -/
def statementKeyword (tok : List UInt8) : Bool :=
  tok = planBytes sourceStatementPlan.floatingKeyword ||
    tok = planBytes sourceStatementPlan.essentialKeyword ||
    tok = planBytes sourceStatementPlan.axiomKeyword ||
    tok = planBytes sourceStatementPlan.theoremKeyword

/-- [MM §4.1.2] "they may not contain the 2-character sequences `$(` or
`$)`" — adjacent-byte search for either sequence. -/
def containsCommentSeq : List UInt8 → Bool
  | a :: b :: rest =>
      [a, b] = commentOpenBytes || [a, b] = commentCloseBytes ||
        containsCommentSeq (b :: rest)
  | _ => false

/-- [MM §4.1.2] "The file name may not contain a `$` or white space." A
token never contains white space, so only the `$` constraint remains,
plus nonemptiness. -/
def validIncludePath (tok : List UInt8) : Bool :=
  !tok.isEmpty && !tok.contains dollarByte

/-- ASCII path token to file identifier. -/
def pathString (tok : List UInt8) : String :=
  String.ofList (tok.map fun b => Char.ofNat b.toNat)

/-- Bytes of a located span, sliced from a pure byte list (kernel-reducible,
unlike `ByteArray.extract`). -/
def spanBytes (bytes : List UInt8) (span : LocatedByteSpan) : List UInt8 :=
  (bytes.drop span.start).take (span.stop - span.start)

/-! ## Rejection provenance -/

inductive IncludeError where
  | unterminatedComment
  | unexpectedCommentClose
  | commentSequenceInComment
  | unterminatedInclude
  | unexpectedIncludeClose
  | invalidIncludePath
  | includeInInnerScope
  | includeInsideStatement
  | missingFile (path : String)
  | cyclicReference (path : String)
  | fuelExhausted (path : String)
deriving DecidableEq, Repr

/-- Every rejection names the exact located span responsible. -/
structure IncludeRejection where
  site : LocatedByteSpan
  error : IncludeError
deriving DecidableEq, Repr

inductive ExpandResult (α : Type _) where
  | ok (value : α)
  | rejected (rejection : IncludeRejection)
deriving DecidableEq, Repr

def ExpandResult.bind : ExpandResult α → (α → ExpandResult β) →
    ExpandResult β
  | .rejected r, _ => .rejected r
  | .ok a, f => f a

@[simp] theorem ExpandResult.bind_ok {α β : Type _} (a : α)
    (f : α → ExpandResult β) : (ExpandResult.ok a).bind f = f a := rfl

@[simp] theorem ExpandResult.bind_rejected {α β : Type _}
    (r : IncludeRejection) (f : α → ExpandResult β) :
    (ExpandResult.rejected r).bind f = .rejected r := rfl

def ExpandResult.bindPair : ExpandResult (α × β) →
    (α → β → ExpandResult γ) → ExpandResult γ
  | .rejected r, _ => .rejected r
  | .ok (a, b), f => f a b

@[simp] theorem ExpandResult.bindPair_ok {α β γ : Type _} (a : α) (b : β)
    (f : α → β → ExpandResult γ) :
    (ExpandResult.ok (a, b)).bindPair f = f a b := rfl

@[simp] theorem ExpandResult.bindPair_rejected {α β γ : Type _}
    (r : IncludeRejection) (f : α → β → ExpandResult γ) :
    (ExpandResult.rejected r).bindPair f = .rejected r := rfl

/-! ## Phase A — comment stripping at token level

Comment delimiters are themselves tokens ([MM §4.1.1] keywords), so
comments are removed from the *token stream*: no byte-level splicing,
and surviving tokens keep their exact file spans. -/

def stripComments (bytes : List UInt8) :
    List LocatedByteSpan → Bool → LocatedByteSpan →
    ExpandResult (List LocatedByteSpan)
  | [], false, _ => .ok []
  | [], true, openSite => .rejected ⟨openSite, .unterminatedComment⟩
  | tok :: rest, false, openSite =>
      if spanBytes bytes tok = commentOpenBytes then
        stripComments bytes rest true tok
      else if spanBytes bytes tok = commentCloseBytes then
        .rejected ⟨tok, .unexpectedCommentClose⟩
      else
        match stripComments bytes rest false openSite with
        | .ok toks => .ok (tok :: toks)
        | .rejected r => .rejected r
  | tok :: rest, true, openSite =>
      if spanBytes bytes tok = commentCloseBytes then
        stripComments bytes rest false openSite
      else if (spanBytes bytes tok = commentOpenBytes ||
          containsCommentSeq (spanBytes bytes tok) : Bool) then
        .rejected ⟨tok, .commentSequenceInComment⟩
      else
        stripComments bytes rest true openSite

/-- Surviving tokens are a subsequence of the input stream. -/
theorem stripComments_subset {bytes : List UInt8} :
    ∀ {toks : List LocatedByteSpan} {inComment : Bool}
      {openSite : LocatedByteSpan} {out : List LocatedByteSpan},
      stripComments bytes toks inComment openSite = .ok out →
      ∀ t ∈ out, t ∈ toks
  | [], false, _, _, h => by
      cases h
      intro t ht
      exact nomatch ht
  | [], true, _, _, h => nomatch h
  | tok :: rest, false, openSite, out, h => by
      unfold stripComments at h
      by_cases hopen : spanBytes bytes tok = commentOpenBytes
      · rw [if_pos hopen] at h
        intro t ht
        exact List.Mem.tail _ (stripComments_subset h t ht)
      · rw [if_neg hopen] at h
        by_cases hclose : spanBytes bytes tok = commentCloseBytes
        · rw [if_pos hclose] at h
          exact nomatch h
        · rw [if_neg hclose] at h
          cases hrec : stripComments bytes rest false openSite with
          | ok toks =>
              rw [hrec] at h
              cases h
              intro t ht
              rcases List.mem_cons.mp ht with rfl | htail
              · exact List.Mem.head _
              · exact List.Mem.tail _ (stripComments_subset hrec t htail)
          | rejected r =>
              rw [hrec] at h
              exact nomatch h
  | tok :: rest, true, openSite, out, h => by
      unfold stripComments at h
      by_cases hclose : spanBytes bytes tok = commentCloseBytes
      · rw [if_pos hclose] at h
        intro t ht
        exact List.Mem.tail _ (stripComments_subset h t ht)
      · rw [if_neg hclose] at h
        by_cases hbad : (spanBytes bytes tok = commentOpenBytes ||
            containsCommentSeq (spanBytes bytes tok) : Bool)
        · rw [if_pos hbad] at h
          exact nomatch h
        · rw [if_neg hbad] at h
          intro t ht
          exact List.Mem.tail _ (stripComments_subset h t ht)

/-! ## Phase B — include-directive recognition

Scope depth is tracked through `${` / `$}` tokens.  Statement placement is
tracked from the first non-scope token through `$.`: this covers the opening
keywords of `$c`, `$v`, and `$d` as well as the labels that open `$f`, `$e`,
`$a`, and `$p`.  This is the book's complete statement boundary, shared with
the repaired mm-lean4 include scanner. -/

inductive SourceItem where
  | token (span : LocatedByteSpan)
  | include_ (path : String) (site : LocatedByteSpan)
deriving DecidableEq, Repr

/-- Scope-depth transition for one non-include token. -/
def nextScopeDepth (tb : List UInt8) (scopeDepth : Nat) : Nat :=
  if tb = scopeOpenBytes then scopeDepth + 1
  else if tb = scopeCloseBytes then scopeDepth - 1
  else scopeDepth

/-- Inside-a-statement transition for one non-include token.

[MM §4.1.2] an inclusion "must not be inside a statement".  Every
statement runs from its opening token to its `$.`: `$c`, `$v`, and `$d`
open with their keyword, while `$f`, `$e`, `$a`, and `$p` open with their
label — so the only tokens that leave us *between* statements are the
terminator and the two scope brackets.  Comments are already removed at
this stage, so no other token can appear outside a statement.

Note this is deliberately stronger than `statementKeyword`, which names
only the label-bearing keywords and is used for statement dispatch
elsewhere. -/
def nextInStatement (tb : List UInt8) (_inStatement : Bool) : Bool :=
  if tb = statementEndBytes then false
  else if tb = scopeOpenBytes then false
  else if tb = scopeCloseBytes then false
  else true

def segmentIncludes (bytes : List UInt8) :
    List LocatedByteSpan → Nat → Bool → ExpandResult (List SourceItem)
  | [], _, _ => .ok []
  | tok :: rest, scopeDepth, inStatement =>
      if spanBytes bytes tok = includeOpenBytes then
        if scopeDepth ≠ 0 then
          .rejected ⟨tok, .includeInInnerScope⟩
        else if inStatement then
          .rejected ⟨tok, .includeInsideStatement⟩
        else
          match rest with
          | pathTok :: closeTok :: rest' =>
              if (validIncludePath (spanBytes bytes pathTok) &&
                  (spanBytes bytes closeTok = includeCloseBytes : Bool) :
                  Bool) then
                (segmentIncludes bytes rest' 0 false).bind fun items =>
                  .ok (.include_ (pathString (spanBytes bytes pathTok))
                    tok :: items)
              else
                .rejected ⟨tok, .invalidIncludePath⟩
          | _ => .rejected ⟨tok, .unterminatedInclude⟩
      else if spanBytes bytes tok = includeCloseBytes then
        .rejected ⟨tok, .unexpectedIncludeClose⟩
      else
        (segmentIncludes bytes rest
            (nextScopeDepth (spanBytes bytes tok) scopeDepth)
            (nextInStatement (spanBytes bytes tok) inStatement)).bind
          fun items => .ok (.token tok :: items)

/-! ### Negative boundary: the book's placement rule for `$[`

[MM §4.1.2] a file-inclusion command "is only allowed in the outermost
scope ... and must not be inside a statement (e.g., it may not occur
between the label of a `$a` statement and its `$.`)", and included files
"may not include incomplete statements".  The segmentation stage enforces
exactly that, rejecting at the offending span with its own reason — the
two theorems below state each rejection universally, so no accepted
expansion can contain a misplaced include. -/

/-- An include opener inside a statement is rejected at that exact span. -/
theorem segmentIncludes_rejects_insideStatement {bytes : List UInt8}
    {tok : LocatedByteSpan} {rest : List LocatedByteSpan}
    (hopen : spanBytes bytes tok = includeOpenBytes) :
    segmentIncludes bytes (tok :: rest) 0 true =
      .rejected ⟨tok, .includeInsideStatement⟩ := by
  unfold segmentIncludes
  simp [hopen]

/-- An include opener in an inner scope is rejected at that exact span,
whatever the statement state. -/
theorem segmentIncludes_rejects_innerScope {bytes : List UInt8}
    {tok : LocatedByteSpan} {rest : List LocatedByteSpan}
    {scopeDepth : Nat} {inStatement : Bool}
    (hopen : spanBytes bytes tok = includeOpenBytes)
    (hscope : scopeDepth ≠ 0) :
    segmentIncludes bytes (tok :: rest) scopeDepth inStatement =
      .rejected ⟨tok, .includeInInnerScope⟩ := by
  unfold segmentIncludes
  simp [hopen, hscope]

/-- Inversion: whenever a successful segmentation meets an include
opener, it was at the outermost scope and between statements.  Applied at
each step of the recursion, this says no accepted expansion ever contains
a misplaced include — the placement rule is structural, not a check that
some other path could bypass. -/
theorem segmentIncludes_include_wellPlaced {bytes : List UInt8}
    {tok : LocatedByteSpan} {rest : List LocatedByteSpan}
    {scopeDepth : Nat} {inStatement : Bool} {items : List SourceItem}
    (hopen : spanBytes bytes tok = includeOpenBytes)
    (hok : segmentIncludes bytes (tok :: rest) scopeDepth inStatement =
      .ok items) :
    scopeDepth = 0 ∧ inStatement = false := by
  by_cases hscope : scopeDepth = 0
  · subst hscope
    by_cases hstmt : inStatement = true
    · subst hstmt
      rw [segmentIncludes_rejects_insideStatement hopen] at hok
      exact nomatch hok
    · exact ⟨rfl, by simpa using hstmt⟩
  · rw [segmentIncludes_rejects_innerScope hopen hscope] at hok
    exact nomatch hok

/-- Emitted plain tokens are a subsequence of the input stream. -/
theorem segmentIncludes_subset {bytes : List UInt8} :
    ∀ {toks : List LocatedByteSpan} {scopeDepth : Nat} {inStatement : Bool}
      {items : List SourceItem},
      segmentIncludes bytes toks scopeDepth inStatement = .ok items →
      ∀ t, SourceItem.token t ∈ items → t ∈ toks
  | [], _, _, _, h => by
      cases h
      intro t ht
      exact nomatch ht
  | tok :: rest, scopeDepth, inStatement, items, h => by
      unfold segmentIncludes at h
      by_cases hinc : spanBytes bytes tok = includeOpenBytes
      · rw [if_pos hinc] at h
        by_cases hscope : scopeDepth ≠ 0
        · rw [if_pos hscope] at h
          exact nomatch h
        · rw [if_neg hscope] at h
          by_cases hstmt : inStatement
          · rw [if_pos hstmt] at h
            exact nomatch h
          · rw [if_neg hstmt] at h
            match rest, h with
            | [], h => exact nomatch h
            | [_], h => exact nomatch h
            | pathTok :: closeTok :: rest', h =>
                replace h :
                    (if (validIncludePath (spanBytes bytes pathTok) &&
                        (spanBytes bytes closeTok = includeCloseBytes :
                          Bool) : Bool) = true then
                      (segmentIncludes bytes rest' 0 false).bind
                        fun items =>
                          ExpandResult.ok
                            (SourceItem.include_
                              (pathString (spanBytes bytes pathTok))
                              tok :: items)
                    else
                      ExpandResult.rejected
                        ⟨tok, IncludeError.invalidIncludePath⟩) =
                    ExpandResult.ok items := h
                by_cases hvalid : (validIncludePath
                    (spanBytes bytes pathTok) &&
                    (spanBytes bytes closeTok = includeCloseBytes :
                      Bool) : Bool)
                · rw [if_pos hvalid] at h
                  cases hrec : segmentIncludes bytes rest' 0 false with
                  | ok items' =>
                      rw [hrec] at h
                      simp only [ExpandResult.bind_ok] at h
                      cases h
                      intro t ht
                      rcases List.mem_cons.mp ht with heq | htail
                      · exact nomatch heq
                      · exact List.Mem.tail _ (List.Mem.tail _
                          (List.Mem.tail _
                            (segmentIncludes_subset hrec t htail)))
                  | rejected r =>
                      rw [hrec] at h
                      exact nomatch h
                · rw [if_neg hvalid] at h
                  exact nomatch h
      · rw [if_neg hinc] at h
        by_cases hclose : spanBytes bytes tok = includeCloseBytes
        · rw [if_pos hclose] at h
          exact nomatch h
        · rw [if_neg hclose] at h
          cases hrec : segmentIncludes bytes rest
              (nextScopeDepth (spanBytes bytes tok) scopeDepth)
              (nextInStatement (spanBytes bytes tok) inStatement) with
          | ok items' =>
              rw [hrec] at h
              simp only [ExpandResult.bind_ok] at h
              cases h
              intro t ht
              rcases List.mem_cons.mp ht with heq | htail
              · cases heq
                exact List.Mem.head _
              · exact List.Mem.tail _ (segmentIncludes_subset hrec t htail)
          | rejected r =>
              rw [hrec] at h
              exact nomatch h

/-! ## Phase C — per-file front end -/

/-- The source DAG: file identifiers to raw bytes. -/
def FileMap : Type := String → Option ByteArray

/-- Tokenize, strip comments, and recognize include directives for one
file.  `site` is the include site that requested this file (the root
file supplies a synthetic site), giving `missingFile` exact
provenance. -/
def filePipeline (files : FileMap) (path : String)
    (site : LocatedByteSpan) : ExpandResult (List SourceItem) :=
  match files path with
  | none => .rejected ⟨site, .missingFile path⟩
  | some bytes =>
      (stripComments bytes.data.toList
        (tokenizeIncrementally path bytes) false site).bind
        fun stripped => segmentIncludes bytes.data.toList stripped 0 false

/-! ## Phase D — policy-indexed expansion over the DAG -/

inductive CyclicReferencePolicy where
  | ignore
  | reject
deriving DecidableEq, Repr

structure IncludePolicy where
  cyclic : CyclicReferencePolicy
deriving DecidableEq, Repr

/-- [MM §4.1.2] profile: "A file self-reference is ignored, as is any
reference to the top-level file (to avoid loops)." -/
def bookSpecPolicy : IncludePolicy := ⟨.ignore⟩

/-- Common-verifier profile: a reference to a file currently being
processed is rejected (mm-lean4 `includeCycleDetected`; metamath.exe and
metamath-knife agree).  References to fully processed files are ignored
by both profiles. -/
def mmLean4CompatPolicy : IncludePolicy := ⟨.reject⟩

/-- Run a file's item list in order through an abstract file expander:
chronology is concatenation order, and emitted tokens keep their
original file spans.  Parametric in the expander so the recursive knot
is tied by `expandFile` alone. -/
def runItems
    (expander : List String → String → LocatedByteSpan →
      ExpandResult (List LocatedByteSpan × List String))
    (seen : List String) (items : List SourceItem) :
    ExpandResult (List LocatedByteSpan × List String) :=
  List.rec
    (motive := fun _ => List String →
      ExpandResult (List LocatedByteSpan × List String))
    (fun seen => .ok ([], seen))
    (fun item _rest recRest seen =>
      match item with
      | .token span =>
          (recRest seen).bindPair fun spans seen' =>
            .ok (span :: spans, seen')
      | .include_ path site =>
          (expander seen path site).bindPair fun spans seen' =>
            (recRest seen').bindPair fun spans' seen'' =>
              .ok (spans ++ spans', seen''))
    items seen

@[simp] theorem runItems_nil (expander) (seen : List String) :
    runItems expander seen [] = .ok ([], seen) := rfl

@[simp] theorem runItems_token (expander) (seen : List String)
    (span : LocatedByteSpan) (rest : List SourceItem) :
    runItems expander seen (.token span :: rest) =
      (runItems expander seen rest).bindPair fun spans seen' =>
        .ok (span :: spans, seen') := rfl

@[simp] theorem runItems_include (expander) (seen : List String)
    (path : String) (site : LocatedByteSpan) (rest : List SourceItem) :
    runItems expander seen (.include_ path site :: rest) =
      (expander seen path site).bindPair fun spans seen' =>
        (runItems expander seen' rest).bindPair fun spans' seen'' =>
          .ok (spans ++ spans', seen'') := rfl

/-- Expand one file.  `processing` is the include call stack (cycle
detection), `seen` the fully processed set (first-reference semantics);
mm-lean4's driver consults them in exactly this order. -/
def expandFile (files : FileMap) (policy : IncludePolicy) (fuel : Nat)
    (processing seen : List String) (path : String)
    (site : LocatedByteSpan) :
    ExpandResult (List LocatedByteSpan × List String) :=
  Nat.rec
    (motive := fun _ => List String → List String → String →
      LocatedByteSpan → ExpandResult (List LocatedByteSpan × List String))
    (fun _ _ path site => .rejected ⟨site, .fuelExhausted path⟩)
    (fun _fuel recFuel processing seen path site =>
      if path ∈ processing then
        match policy.cyclic with
        | .ignore => .ok ([], seen)
        | .reject => .rejected ⟨site, .cyclicReference path⟩
      else if path ∈ seen then
        .ok ([], seen)
      else
        (filePipeline files path site).bind fun items =>
          (runItems (fun seen' p s => recFuel (path :: processing) seen' p s)
              seen items).bindPair fun spans seen' =>
            .ok (spans, path :: seen'))
    fuel processing seen path site

theorem expandFile_zero (files : FileMap) (policy : IncludePolicy)
    (processing seen : List String) (path : String)
    (site : LocatedByteSpan) :
    expandFile files policy 0 processing seen path site =
      .rejected ⟨site, .fuelExhausted path⟩ := rfl

theorem expandFile_succ (files : FileMap) (policy : IncludePolicy)
    (fuel : Nat) (processing seen : List String) (path : String)
    (site : LocatedByteSpan) :
    expandFile files policy (fuel + 1) processing seen path site =
      (if path ∈ processing then
        match policy.cyclic with
        | .ignore => .ok ([], seen)
        | .reject => .rejected ⟨site, .cyclicReference path⟩
      else if path ∈ seen then
        .ok ([], seen)
      else
        (filePipeline files path site).bind fun items =>
          (runItems
              (fun seen' p s =>
                expandFile files policy fuel (path :: processing) seen' p s)
              seen items).bindPair fun spans seen' =>
            .ok (spans, path :: seen')) := rfl

/-- Expand a database from its top-level file.  Default fuel mirrors
mm-lean4's `maxIncludeDepth`. -/
def expandDatabase (files : FileMap) (policy : IncludePolicy)
    (root : String) (fuel : Nat := 100) :
    ExpandResult (List LocatedByteSpan) :=
  (expandFile files policy fuel [] [] root ⟨root, 0, 0⟩).bindPair
    fun spans _ => .ok spans

/-! ## Policy agreement

The two profiles differ in exactly one branch, so every run the
compatibility profile accepts is reproduced verbatim by the book
profile.  The converse fails precisely on cyclic references — witnessed
by the self-include fixtures below. -/

/-- Item runs transport along pointwise agreement of expanders. -/
theorem runItems_congr_ok
    {e₁ e₂ : List String → String → LocatedByteSpan →
      ExpandResult (List LocatedByteSpan × List String)}
    (hpt : ∀ seen path site r, e₁ seen path site = .ok r →
      e₂ seen path site = .ok r) :
    ∀ {seen : List String} {items : List SourceItem}
      {r : List LocatedByteSpan × List String},
      runItems e₁ seen items = .ok r → runItems e₂ seen items = .ok r
  | seen, [], r, h => h
  | seen, .token span :: rest, r, h => by
      rw [runItems_token] at h ⊢
      cases hrec : runItems e₁ seen rest with
      | rejected rej => rw [hrec] at h; exact nomatch h
      | ok pair =>
          obtain ⟨spans, seen'⟩ := pair
          rw [hrec] at h
          rw [runItems_congr_ok hpt hrec]
          exact h
  | seen, .include_ path site :: rest, r, h => by
      rw [runItems_include] at h ⊢
      cases hexp : e₁ seen path site with
      | rejected rej => rw [hexp] at h; exact nomatch h
      | ok pair =>
          obtain ⟨spans, seen'⟩ := pair
          rw [hexp] at h
          rw [hpt seen path site _ hexp]
          simp only [ExpandResult.bindPair_ok] at h ⊢
          cases hrec : runItems e₁ seen' rest with
          | rejected rej => rw [hrec] at h; exact nomatch h
          | ok pair' =>
              obtain ⟨spans', seen''⟩ := pair'
              rw [hrec] at h
              rw [runItems_congr_ok hpt hrec]
              exact h

/-- Every accepted compatibility-profile expansion is reproduced by the
book profile, with identical output and identical `seen` chronology. -/
theorem expandFile_compat_ok (files : FileMap) :
    ∀ (fuel : Nat) (processing seen : List String) (path : String)
      (site : LocatedByteSpan) {r : List LocatedByteSpan × List String},
      expandFile files mmLean4CompatPolicy fuel processing seen path site =
        .ok r →
      expandFile files bookSpecPolicy fuel processing seen path site =
        .ok r := by
  intro fuel
  induction fuel with
  | zero =>
      intro processing seen path site r h
      rw [expandFile_zero] at h
      exact nomatch h
  | succ fuel ih =>
      intro processing seen path site r h
      rw [expandFile_succ] at h ⊢
      by_cases hproc : path ∈ processing
      · rw [if_pos hproc] at h
        exact nomatch h
      · rw [if_neg hproc] at h ⊢
        by_cases hseen : path ∈ seen
        · rw [if_pos hseen] at h ⊢
          exact h
        · rw [if_neg hseen] at h ⊢
          cases hpipe : filePipeline files path site with
          | rejected rej =>
              simp only [hpipe, ExpandResult.bind_rejected] at h
              exact nomatch h
          | ok items =>
              simp only [hpipe, ExpandResult.bind_ok] at h ⊢
              cases hrun : runItems
                  (fun seen' p s => expandFile files mmLean4CompatPolicy
                    fuel (path :: processing) seen' p s) seen items with
              | rejected rej =>
                  simp only [hrun, ExpandResult.bindPair_rejected] at h
                  exact nomatch h
              | ok pair =>
                  obtain ⟨spans, seen'⟩ := pair
                  rw [runItems_congr_ok
                    (fun seen'' p s r' h' =>
                      ih (path :: processing) seen'' p s h') hrun]
                  simp only [hrun, ExpandResult.bindPair_ok] at h
                  simp only [ExpandResult.bindPair_ok]
                  exact h

theorem expandDatabase_compat_ok {files : FileMap} {root : String}
    {fuel : Nat} {spans : List LocatedByteSpan}
    (h : expandDatabase files mmLean4CompatPolicy root fuel = .ok spans) :
    expandDatabase files bookSpecPolicy root fuel = .ok spans := by
  unfold expandDatabase at h ⊢
  cases hfile : expandFile files mmLean4CompatPolicy fuel [] [] root
      ⟨root, 0, 0⟩ with
  | rejected r =>
      simp only [hfile, ExpandResult.bindPair_rejected] at h
      exact nomatch h
  | ok pair =>
      obtain ⟨spans', seen'⟩ := pair
      simp only [hfile, ExpandResult.bindPair_ok] at h
      rw [expandFile_compat_ok files fuel [] [] root ⟨root, 0, 0⟩ hfile]
      simp only [ExpandResult.bindPair_ok]
      exact h

/-! ## Provenance soundness

Expansion never splices bytes: every emitted span is a genuine token of
its own file's tokenization.  File identity and offsets therefore remain
usable as evidence by every later stage. -/

theorem tokenizeListFrom_fileId {fileId : String} :
    ∀ {bytes : List UInt8} {cursor : Nat} {mode : ScanMode}
      {span : LocatedByteSpan},
      span ∈ tokenizeListFrom fileId cursor mode bytes →
      span.fileId = fileId
  | [], cursor, mode, span => by
      intro hmem
      unfold tokenizeListFrom at hmem
      cases mode with
      | separator => exact nomatch hmem
      | token start =>
          rcases List.mem_singleton.mp hmem with rfl
          rfl
  | byte :: bytes, cursor, mode, span => by
      intro hmem
      unfold tokenizeListFrom at hmem
      by_cases hws : sourceWhitespace byte
      · rw [if_pos hws] at hmem
        cases mode with
        | separator => exact tokenizeListFrom_fileId hmem
        | token start =>
            rcases List.mem_cons.mp hmem with rfl | htail
            · rfl
            · exact tokenizeListFrom_fileId htail
      · rw [if_neg hws] at hmem
        cases mode with
        | separator => exact tokenizeListFrom_fileId hmem
        | token start => exact tokenizeListFrom_fileId hmem

theorem tokenize_fileId {fileId : String} {bytes : ByteArray}
    {span : LocatedByteSpan} (hmem : span ∈ tokenize fileId bytes) :
    span.fileId = fileId := by
  have hlist : span ∈ tokenizeListFrom fileId 0 .separator
      bytes.data.toList := by
    have heq := tokenizeListFrom_drop_eq_tokenizeFrom fileId bytes 0
      .separator (Nat.zero_le _)
    unfold tokenize at hmem
    rw [← heq] at hmem
    simpa using hmem
  exact tokenizeListFrom_fileId hlist

/-- Tokens delivered by a file's pipeline are genuine tokens of that
file. -/
theorem filePipeline_provenance {files : FileMap} {path : String}
    {site : LocatedByteSpan} {items : List SourceItem}
    (h : filePipeline files path site = .ok items) :
    ∀ t, SourceItem.token t ∈ items →
      ∃ bytes, files t.fileId = some bytes ∧
        t ∈ tokenize t.fileId bytes := by
  intro t ht
  unfold filePipeline at h
  cases hfetch : files path with
  | none =>
      simp only [hfetch] at h
      exact nomatch h
  | some bytes =>
      simp only [hfetch] at h
      cases hstrip : stripComments bytes.data.toList
          (tokenizeIncrementally path bytes) false site with
      | rejected rej =>
          simp only [hstrip, ExpandResult.bind_rejected] at h
          exact nomatch h
      | ok stripped =>
          simp only [hstrip, ExpandResult.bind_ok] at h
          have hsub := segmentIncludes_subset h t ht
          have hsub' := stripComments_subset hstrip t hsub
          rw [tokenizeIncrementally_eq_tokenize] at hsub'
          have hfid := tokenize_fileId hsub'
          refine ⟨bytes, ?_, ?_⟩
          · rw [hfid]; exact hfetch
          · rw [hfid]; exact hsub'

/-- Item runs emit only expander-emitted or pipeline-supplied tokens,
uniformly in a span predicate. -/
theorem runItems_provenance
    {P : LocatedByteSpan → Prop}
    {expander : List String → String → LocatedByteSpan →
      ExpandResult (List LocatedByteSpan × List String)}
    (hexp : ∀ seen path site r, expander seen path site = .ok r →
      ∀ s ∈ r.1, P s) :
    ∀ {seen : List String} {items : List SourceItem}
      {r : List LocatedByteSpan × List String},
      runItems expander seen items = .ok r →
      (∀ t, SourceItem.token t ∈ items → P t) →
      ∀ s ∈ r.1, P s
  | seen, [], r, h, _ => by
      cases h
      intro s hs
      exact nomatch hs
  | seen, .token span :: rest, r, h, hitems => by
      rw [runItems_token] at h
      cases hrec : runItems expander seen rest with
      | rejected rej => rw [hrec] at h; exact nomatch h
      | ok pair =>
          obtain ⟨spans, seen'⟩ := pair
          rw [hrec] at h
          cases h
          intro s hs
          rcases List.mem_cons.mp hs with rfl | htail
          · exact hitems s (List.Mem.head _)
          · exact runItems_provenance hexp hrec
              (fun t ht => hitems t (List.Mem.tail _ ht)) s htail
  | seen, .include_ path site :: rest, r, h, hitems => by
      rw [runItems_include] at h
      cases hexp' : expander seen path site with
      | rejected rej => rw [hexp'] at h; exact nomatch h
      | ok pair =>
          obtain ⟨spans, seen'⟩ := pair
          rw [hexp'] at h
          simp only [ExpandResult.bindPair_ok] at h
          cases hrec : runItems expander seen' rest with
          | rejected rej => rw [hrec] at h; exact nomatch h
          | ok pair' =>
              obtain ⟨spans', seen''⟩ := pair'
              rw [hrec] at h
              cases h
              intro s hs
              rcases List.mem_append.mp hs with hleft | hright
              · exact hexp seen path site _ hexp' s hleft
              · exact runItems_provenance hexp hrec
                  (fun t ht => hitems t (List.Mem.tail _ ht)) s hright

/-- Every span an accepted expansion emits is a token of its own file. -/
theorem expandFile_provenance (files : FileMap) (policy : IncludePolicy) :
    ∀ (fuel : Nat) (processing seen : List String) (path : String)
      (site : LocatedByteSpan) {r : List LocatedByteSpan × List String},
      expandFile files policy fuel processing seen path site = .ok r →
      ∀ s ∈ r.1, ∃ bytes, files s.fileId = some bytes ∧
        s ∈ tokenize s.fileId bytes := by
  intro fuel
  induction fuel with
  | zero =>
      intro processing seen path site r h
      rw [expandFile_zero] at h
      exact nomatch h
  | succ fuel ih =>
      intro processing seen path site r h
      rw [expandFile_succ] at h
      by_cases hproc : path ∈ processing
      · rw [if_pos hproc] at h
        cases hpol : policy.cyclic with
        | ignore =>
            rw [hpol] at h
            cases h
            intro s hs
            exact nomatch hs
        | reject => rw [hpol] at h; exact nomatch h
      · rw [if_neg hproc] at h
        by_cases hseen : path ∈ seen
        · rw [if_pos hseen] at h
          cases h
          intro s hs
          exact nomatch hs
        · rw [if_neg hseen] at h
          cases hpipe : filePipeline files path site with
          | rejected rej =>
              simp only [hpipe, ExpandResult.bind_rejected] at h
              exact nomatch h
          | ok items =>
              simp only [hpipe, ExpandResult.bind_ok] at h
              cases hrun : runItems
                  (fun seen' p s => expandFile files policy fuel
                    (path :: processing) seen' p s) seen items with
              | rejected rej =>
                  simp only [hrun, ExpandResult.bindPair_rejected] at h
                  exact nomatch h
              | ok pair =>
                  obtain ⟨spans, seen'⟩ := pair
                  simp only [hrun, ExpandResult.bindPair_ok] at h
                  cases h
                  intro s hs
                  exact runItems_provenance
                    (fun seen'' p s' r' h' =>
                      ih (path :: processing) seen'' p s' h')
                    hrun (filePipeline_provenance hpipe) s hs

theorem expandDatabase_provenance {files : FileMap}
    {policy : IncludePolicy} {root : String} {fuel : Nat}
    {spans : List LocatedByteSpan}
    (h : expandDatabase files policy root fuel = .ok spans) :
    ∀ s ∈ spans, ∃ bytes, files s.fileId = some bytes ∧
      s ∈ tokenize s.fileId bytes := by
  unfold expandDatabase at h
  cases hfile : expandFile files policy fuel [] [] root ⟨root, 0, 0⟩ with
  | rejected r =>
      simp only [hfile, ExpandResult.bindPair_rejected] at h
      exact nomatch h
  | ok pair =>
      obtain ⟨spans', seen'⟩ := pair
      simp only [hfile, ExpandResult.bindPair_ok] at h
      cases h
      exact expandFile_provenance files policy fuel [] [] root ⟨root, 0, 0⟩
        hfile

/-! ## Calibration fixtures

Concrete byte-level databases, evaluated by kernel `decide`. -/

set_option maxRecDepth 100000

/-- Stage probe: the incremental scanner reduces in the kernel. -/
example :
    tokenizeIncrementally "z"
      (ByteArray.mk #[36, 91, 32, 115, 32, 36, 93]) =
      [⟨"z", 0, 2⟩, ⟨"z", 3, 4⟩, ⟨"z", 5, 7⟩] := rfl

/-- Stage probe: comment stripping reduces. -/
example :
    stripComments [36, 91, 32, 115, 32, 36, 93]
      [⟨"z", 0, 2⟩, ⟨"z", 3, 4⟩, ⟨"z", 5, 7⟩] false ⟨"z", 0, 0⟩ =
      .ok [⟨"z", 0, 2⟩, ⟨"z", 3, 4⟩, ⟨"z", 5, 7⟩] := rfl

/-- Stage probe: include segmentation reduces. -/
example :
    segmentIncludes [36, 91, 32, 115, 32, 36, 93]
      [⟨"z", 0, 2⟩, ⟨"z", 3, 4⟩, ⟨"z", 5, 7⟩] 0 false =
      .ok [.include_ "s" ⟨"z", 0, 2⟩] := rfl

/-- Positive boundary: a completed `$d x y $.` returns to outer statement
scope, so the following include is recognized as a complete directive. -/
example :
    segmentIncludes
      [36, 100, 32, 120, 32, 121, 32, 36, 46, 32,
       36, 91, 32, 115, 32, 36, 93]
      [⟨"z", 0, 2⟩, ⟨"z", 3, 4⟩, ⟨"z", 5, 6⟩, ⟨"z", 7, 9⟩,
       ⟨"z", 10, 12⟩, ⟨"z", 13, 14⟩, ⟨"z", 15, 17⟩]
      0 false =
      .ok [.token ⟨"z", 0, 2⟩, .token ⟨"z", 3, 4⟩,
        .token ⟨"z", 5, 6⟩, .token ⟨"z", 7, 9⟩,
        .include_ "s" ⟨"z", 10, 12⟩] := rfl

/-- Basic inclusion: `root` = `"$[ sub $] q"`, `sub` = `"p"`. -/
def basicFiles : FileMap := fun n =>
  if n = "root" then
    some (ByteArray.mk #[36, 91, 32, 115, 117, 98, 32, 36, 93, 32, 113])
  else if n = "sub" then some (ByteArray.mk #[112])
  else none

/-- Positive: the included file's token appears at the include site,
carrying its own file identity and offsets; the host token follows. -/
example :
    expandDatabase basicFiles mmLean4CompatPolicy "root" =
      .ok [⟨"sub", 0, 1⟩, ⟨"root", 10, 11⟩] := rfl

/-- A root whose include sits between `$d` and its terminator:
`$c a $. $d x $[ sub $] $.`. -/
def insideDjStatementFiles : FileMap := fun n =>
  if n = "root" then
    some (ByteArray.mk #[36, 99, 32, 97, 32, 36, 46, 32, 36, 100, 32,
      120, 32, 36, 91, 32, 115, 117, 98, 32, 36, 93, 32, 36, 46])
  else if n = "sub" then some (ByteArray.mk #[121])
  else none

/-- A root whose include sits inside a label-bearing statement:
`ax $a x $[ sub $]`. -/
def insideAxiomStatementFiles : FileMap := fun n =>
  if n = "root" then
    some (ByteArray.mk #[97, 120, 32, 36, 97, 32, 120, 32, 36, 91, 32,
      115, 117, 98, 32, 36, 93])
  else if n = "sub" then some (ByteArray.mk #[121])
  else none

/-- Negative: an include between `$d` and its `$.` is rejected at its own
span, under both ratified policies. -/
example :
    expandDatabase insideDjStatementFiles bookSpecPolicy "root" =
      .rejected ⟨⟨"root", 13, 15⟩, .includeInsideStatement⟩ := rfl

example :
    expandDatabase insideDjStatementFiles mmLean4CompatPolicy "root" =
      .rejected ⟨⟨"root", 13, 15⟩, .includeInsideStatement⟩ := rfl

/-- Negative: an include inside a label-bearing statement is likewise
rejected at its own span, under both ratified policies. -/
example :
    expandDatabase insideAxiomStatementFiles bookSpecPolicy "root" =
      .rejected ⟨⟨"root", 8, 10⟩, .includeInsideStatement⟩ := rfl

example :
    expandDatabase insideAxiomStatementFiles mmLean4CompatPolicy "root" =
      .rejected ⟨⟨"root", 8, 10⟩, .includeInsideStatement⟩ := rfl

/-- Positive: the book profile agrees on the cycle-free database
(instance of `expandDatabase_compat_ok`). -/
example :
    expandDatabase basicFiles bookSpecPolicy "root" =
      .ok [⟨"sub", 0, 1⟩, ⟨"root", 10, 11⟩] := rfl

/-- The canonical self-include database (metamath-test `test28` shape):
`s` = `"$[ s $]"`. -/
def selfIncludeFiles : FileMap := fun n =>
  if n = "s" then some (ByteArray.mk #[36, 91, 32, 115, 32, 36, 93])
  else none

/-- Stage probe: file expansion reduces, threading `processing` and
`seen`. -/
example :
    expandFile selfIncludeFiles bookSpecPolicy 2 [] [] "s" ⟨"s", 0, 0⟩ =
      .ok ([], ["s"]) := rfl

/-- Positive ([MM §4.1.2]): "A file self-reference is ignored". -/
example :
    expandDatabase selfIncludeFiles bookSpecPolicy "s" = .ok [] := rfl

/-- Negative (compatibility profile): the self-reference is rejected
with the exact `$[` site in the exact file. -/
example :
    expandDatabase selfIncludeFiles mmLean4CompatPolicy "s" =
      .rejected ⟨⟨"s", 0, 2⟩, .cyclicReference "s"⟩ := rfl

/-- A comment hides an include: `c` = `"$( $[ s $) p"`; the referenced
file does not even exist, and neither profile consults it
([MM §4.1.2]: "`$( $[ $)` is a comment"). -/
def commentFiles : FileMap := fun n =>
  if n = "c" then
    some (ByteArray.mk #[36, 40, 32, 36, 91, 32, 115, 32, 36, 41, 32, 112])
  else none

example :
    expandDatabase commentFiles mmLean4CompatPolicy "c" =
      .ok [⟨"c", 11, 12⟩] := rfl

/-- Negative: an include in an inner scope is rejected at the `$[`
site. -/
def innerScopeFiles : FileMap := fun n =>
  if n = "b" then
    some (ByteArray.mk
      #[36, 123, 32, 36, 91, 32, 115, 32, 36, 93, 32, 36, 125])
  else none

example :
    expandDatabase innerScopeFiles mmLean4CompatPolicy "b" =
      .rejected ⟨⟨"b", 3, 5⟩, .includeInInnerScope⟩ := rfl

/-- First-reference semantics, shared by both profiles: `root` includes
`a` twice; the second reference is ignored ([MM §4.1.2]: "Only the first
reference to a given file is included"). -/
def repeatFiles : FileMap := fun n =>
  if n = "root" then
    some (ByteArray.mk
      #[36, 91, 32, 97, 32, 36, 93, 32, 36, 91, 32, 97, 32, 36, 93])
  else if n = "a" then some (ByteArray.mk #[120])
  else none

example :
    expandDatabase repeatFiles mmLean4CompatPolicy "root" =
      .ok [⟨"a", 0, 1⟩] := rfl

example :
    expandDatabase repeatFiles bookSpecPolicy "root" =
      .ok [⟨"a", 0, 1⟩] := rfl

end Mettapedia.Languages.Metamath.SourceGSLTIncludeDAG
