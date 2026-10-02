import Mettapedia.Languages.Metamath.InferenceOneShotByteLog
import Mettapedia.Languages.Metamath.SourceGSLTParserDefinition
import Mettapedia.GSLT.Parsing.SeparatorPlan
import Mettapedia.GSLT.Parsing.PresentationExprSemantics
import Mettapedia.GSLT.Parsing.SeparatorPlanCorrespondence
import Init.Data.ByteArray.Lemmas
import Metamath.Verify.ParserState

/-!
# Raw-byte lexical characterization for the Metamath source GSLT

This module puts the authored scannerless presentation and mm-lean4's
incremental byte loop on a common, implementation-neutral carrier: file-aware
half-open byte spans.  The canonical scanner is total by construction, while
`TokenizesFrom` is an independent relational characterization used for
functionality and correspondence proofs.

Comments deliberately remain in this whitespace-token stream.  The source
GSLT later recognizes and erases complete comment blocks as `skip`; mm-lean4
submits the same block's tokens through `feedToken`.  Keeping those operations
separate prevents comment erasure from becoming an unproved lexer shortcut.

The source separator class is specialized by mm-lean4's existing `ModeConfig`:
the default, zar, sound, and knife modes use the five book separators; exe and
permissive additionally separate vertical tab.  Other parser-policy flags
remain with the structural/comment checker rather than the byte scanner.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical

open Metamath.Verify
open Mettapedia.Languages.Metamath.SourceGSLT
open Mettapedia.Languages.Metamath.SourceGSLTParserDefinition
open Mettapedia.Languages.Metamath.InferenceOneShotByteLog
open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler
open Mettapedia.GSLT.Parsing.SeparatorPlan
open Mettapedia.GSLT.Parsing.PresentationExprSemantics
open Mettapedia.GSLT.Parsing.SeparatorPlanCorrespondence

/-! ## Source-owned whitespace authority -/

/-- The book's byte-separator predicate and the authored source GSLT use
exactly the same five Appendix-E whitespace codepoints. -/
theorem isWhitespace_iff_sourceMember (byte : UInt8) :
    isWhitespace byte = true ↔ byte.toNat ∈ whitespaceCodepoints := by
  simp only [isWhitespace, Bool.or_eq_true, beq_iff_eq,
    whitespaceCodepoints, List.mem_cons, List.not_mem_nil, or_false]
  rw [show (32 : Nat) = ' '.toUInt8.toNat by rfl,
      show (9 : Nat) = '\t'.toUInt8.toNat by rfl,
      show (13 : Nat) = '\r'.toUInt8.toNat by rfl,
      show (10 : Nat) = '\n'.toUInt8.toNat by rfl,
      show (12 : Nat) = (0x0c : UInt8).toNat by rfl]
  simp only [UInt8.toNat_inj]
  aesop

/-- The specialization plan accepted from the authored scannerless
presentation.  Its separator class is not supplied independently. -/
def metamathSeparatorPlan : Plan :=
  { definitionName := "token-separator", separatorClass := "whitespace" }

/-- Specialize the authored separator class using mm-lean4's existing mode
configuration.  The book presentation is unchanged except that modes which
admit vertical tab add its one class-membership fact. -/
def parserPresentationForMode (config : ModeConfig) : Presentation :=
  { parserPresentation with
    members := lexicalMembers ++
      members "whitespace"
        (if config.allowVerticalTabWhitespace then [11] else []) }

@[simp] theorem parserPresentationForMode_default :
    parserPresentationForMode {} = parserPresentation := by
  simp [parserPresentationForMode, parserPresentation, members]

theorem metamathSeparatorPlan_compiles (config : ModeConfig := {}) :
    compile? (parserPresentationForMode config) "token-separator" =
      some metamathSeparatorPlan := by
  rfl

def tokenSeparatorDefinition : Definition :=
  { name := "token-separator"
    body := .alt (.class metamathSeparatorPlan.separatorClass) .eof }

theorem tokenSeparatorDefinition_find (config : ModeConfig := {}) :
    (parserPresentationForMode config).definitions.find? (fun candidate =>
      candidate.name == "token-separator") =
        some tokenSeparatorDefinition := by
  rfl

theorem tokenSeparatorDefinition_mem (config : ModeConfig := {}) :
    tokenSeparatorDefinition ∈ (parserPresentationForMode config).definitions :=
  List.mem_of_find?_eq_some (tokenSeparatorDefinition_find config)

/-- The generic separator compiler selects this exact authored definition,
and its native separator branch preserves and reflects the definition's
proof-relevant span semantics. -/
theorem planStep_separator_iff_tokenSeparatorDefinition
    (input : List Nat) (cursor : Nat) (config : ModeConfig := {}) :
    decideAt (parserPresentationForMode config) metamathSeparatorPlan input cursor =
        .separator ↔
      Nonempty (RecognizesAt (parserPresentationForMode config) input
        tokenSeparatorDefinition.body cursor (cursor + 1)) := by
  rcases compile?_separator_correspondence
      (metamathSeparatorPlan_compiles config) input cursor with
    ⟨definition, selected, _, _, correspondence⟩
  have definitionEq : tokenSeparatorDefinition = definition :=
    Option.some.inj ((tokenSeparatorDefinition_find config).symm.trans selected)
  subst definition
  exact correspondence

/-- EOF preservation/reflection for the same exact compiled definition. -/
theorem planStep_eof_iff_tokenSeparatorDefinition
    (input : List Nat) (cursor : Nat)
    (cursorBound : cursor ≤ input.length) (config : ModeConfig := {}) :
    decideAt (parserPresentationForMode config) metamathSeparatorPlan input cursor = .eof ↔
      Nonempty (RecognizesAt (parserPresentationForMode config) input
        tokenSeparatorDefinition.body cursor cursor) := by
  rcases compile?_eof_correspondence
      (metamathSeparatorPlan_compiles config) input cursor cursorBound with
    ⟨definition, selected, _, _, correspondence⟩
  have definitionEq : tokenSeparatorDefinition = definition :=
    Option.some.inj ((tokenSeparatorDefinition_find config).symm.trans selected)
  subst definition
  exact correspondence

/-- The exact lexical membership fact selected by the plan. -/
theorem metamathWhitespaceMember_iff (codepoint : Nat) (config : ModeConfig := {}) :
    ({ className := metamathSeparatorPlan.separatorClass, codepoint } :
        ClassMember) ∈ (parserPresentationForMode config).members ↔
      codepoint ∈ whitespaceCodepoints ∨
        (config.allowVerticalTabWhitespace = true ∧ codepoint = 11) := by
  cases enabled : config.allowVerticalTabWhitespace <;>
    simp [parserPresentationForMode, metamathSeparatorPlan, lexicalMembers, enabled]

/-- Executable whitespace decision whose data source is the extracted
scannerless-presentation plan rather than the production parser. -/
def sourceWhitespace (byte : UInt8) (config : ModeConfig := {}) : Bool :=
  classContains (parserPresentationForMode config) metamathSeparatorPlan.separatorClass
    byte.toNat

/-- Independently compiled source-class membership agrees with the runtime
mode's separator predicate on every byte. -/
theorem sourceWhitespace_eq_modeWhitespace (byte : UInt8) (config : ModeConfig := {}) :
    sourceWhitespace byte config = config.isWhitespace byte := by
  rw [Bool.eq_iff_iff]
  unfold sourceWhitespace
  rw [classContains_eq_true_iff, metamathWhitespaceMember_iff _ config]
  simp only [ModeConfig.isWhitespace, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  rw [isWhitespace_iff_sourceMember]
  rw [show (11 : Nat) = (11 : UInt8).toNat by rfl, UInt8.toNat_inj]

/-- The default mode specializes to the original five book separators. -/
theorem sourceWhitespace_eq_isWhitespace (byte : UInt8) :
    sourceWhitespace byte = isWhitespace byte := by
  rw [sourceWhitespace_eq_modeWhitespace]
  simp [ModeConfig.isWhitespace]

/-- Positive presentation-semantics boundary: an authored whitespace byte
derives the selected separator definition at its exact one-byte span. -/
def tokenSeparatorWhitespaceDerivation
    {input : List Nat} {cursor : Nat} {byte : UInt8}
    (lookup : input[cursor]? = some byte.toNat)
    (config : ModeConfig := {})
    (space : sourceWhitespace byte config = true) :
    DefinitionDerivation (parserPresentationForMode config) input "token-separator"
      cursor (cursor + 1) :=
  { definition := tokenSeparatorDefinition
    member := tokenSeparatorDefinition_mem config
    nameEq := rfl
    derivation := .altLeft <| .classMember lookup <|
      classContains_eq_true_iff (parserPresentationForMode config)
        metamathSeparatorPlan.separatorClass byte.toNat |>.mp <| by
          exact space }

/-- Positive EOF boundary: the same authored definition recognizes EOF
without consuming a byte. -/
def tokenSeparatorEofDerivation (input : List Nat) (config : ModeConfig := {}) :
    DefinitionDerivation (parserPresentationForMode config) input "token-separator"
      input.length input.length :=
  { definition := tokenSeparatorDefinition
    member := tokenSeparatorDefinition_mem config
    nameEq := rfl
    derivation := .altRight (.eof rfl) }

/-- Negative presentation-semantics boundary: a present non-whitespace byte
cannot derive the separator expression. -/
theorem tokenSeparatorNonWhitespace_isEmpty
    {input : List Nat} {cursor : Nat} {byte : UInt8}
    (lookup : input[cursor]? = some byte.toNat)
    (config : ModeConfig := {})
    (notSpace : sourceWhitespace byte config = false) :
    IsEmpty (RecognizesAt (parserPresentationForMode config) input
      tokenSeparatorDefinition.body cursor (cursor + 1)) := by
  constructor
  intro derivation
  cases derivation with
  | altLeft left =>
      cases left with
      | classMember derivedLookup member =>
          have codepointEq : _ := Option.some.inj (derivedLookup.symm.trans lookup)
          subst_vars
          have present :=
            (classContains_eq_true_iff (parserPresentationForMode config)
              metamathSeparatorPlan.separatorClass byte.toNat).2 member
          change classContains (parserPresentationForMode config)
            metamathSeparatorPlan.separatorClass byte.toNat = false at notSpace
          rw [notSpace] at present
          cases present
  | altRight right =>
      cases right

/-! ## Canonical located spans -/

/-- A file-aware half-open source span.  The bytes remain external so the
same span data can index a whole-file GSLT derivation, an incremental parser
run, and an include-resolved source DAG without copying token payloads. -/
structure LocatedByteSpan where
  fileId : String
  start : Nat
  stop : Nat
deriving DecidableEq, Repr

def LocatedByteSpan.tokenBytes
    (span : LocatedByteSpan) (bytes : ByteArray) : List UInt8 :=
  (bytes.extract span.start span.stop).toList

/-- Normalize an implementation token origin to global half-open coordinates.
For carried chunks these coordinates describe a physical source span only
under the later contiguous-chunk premise; this definition alone does not
assert that arbitrary caller-supplied arrays came from one file. -/
def normalizedOriginSpan
    (fileId : String) : TokenOrigin → LocatedByteSpan
  | .current base _ start stop =>
      { fileId, start := base + start, stop := base + stop }
  | .carried oldBase _ start base _ stop =>
      { fileId, start := oldBase + start, stop := base + stop }
  | .trailing parserOffset eofOffset token =>
      { fileId, start := parserOffset + token.start, stop := eofOffset }

def normalizedCallSpan
    (fileId : String) (call : TokenCall) : LocatedByteSpan :=
  normalizedOriginSpan fileId call.origin

/-! ## Total canonical scanner and independent relation -/

/-- Residual state of the whitespace tokenizer.  A token start is a physical
file offset, not an offset into a particular input chunk. -/
inductive ScanMode where
  | separator
  | token (start : Nat)
deriving DecidableEq, Repr

/-- Streaming state for the source-owned tokenizer.  Completed spans are kept
in reverse order so every byte step is allocation-bounded and constant-time;
the sole reversal occurs at the observation boundary. -/
structure IncrementalScanState where
  cursor : Nat
  mode : ScanMode
  completedRev : List LocatedByteSpan
deriving DecidableEq, Repr

def initialIncrementalState : IncrementalScanState :=
  { cursor := 0, mode := .separator, completedRev := [] }

/-- Language-neutral state update after a compiled separator decision. -/
def applySeparatorDecision (fileId : String) (state : IncrementalScanState) :
    Decision → IncrementalScanState
  | .separator =>
      match state.mode with
      | .separator => { state with cursor := state.cursor + 1 }
      | .token start =>
          { cursor := state.cursor + 1
            mode := .separator
            completedRev :=
              { fileId, start, stop := state.cursor } :: state.completedRev }
  | .content =>
      match state.mode with
      | .separator =>
          { state with cursor := state.cursor + 1, mode := .token state.cursor }
      | .token _ => { state with cursor := state.cursor + 1 }
  | .eof => state

/-- One byte transition, driven only by the authored whitespace class. -/
def scanStep (fileId : String) (state : IncrementalScanState)
    (byte : UInt8) (config : ModeConfig := {}) : IncrementalScanState :=
  applySeparatorDecision fileId state <|
    if sourceWhitespace byte config then .separator else .content

/-- The generic plan compiler's decision on a singleton byte is exactly the
classifier used by the streaming scanner. -/
theorem decideAt_singleton_eq_sourceDecision
    (byte : UInt8) (config : ModeConfig := {}) :
    decideAt (parserPresentationForMode config) metamathSeparatorPlan [byte.toNat] 0 =
      (if sourceWhitespace byte config then .separator else .content) := by
  simp [decideAt, sourceWhitespace]
  rfl

/-- The plan-driven byte step and the efficient streaming step are literally
the same transition after classification.  This is the executable fusion
joint from the authored `token-separator` expression to the scanner. -/
theorem scanStep_eq_planStep (fileId : String)
    (state : IncrementalScanState) (byte : UInt8) (config : ModeConfig := {}) :
    scanStep fileId state byte config =
      applySeparatorDecision fileId state
        (decideAt (parserPresentationForMode config) metamathSeparatorPlan [byte.toNat] 0) := by
  rw [scanStep, decideAt_singleton_eq_sourceDecision byte config]

/-- Run the incremental source scanner over a byte list. -/
def scanRun (fileId : String) (state : IncrementalScanState)
    (bytes : List UInt8) (config : ModeConfig := {}) : IncrementalScanState :=
  bytes.foldl (fun current byte => scanStep fileId current byte config) state

/-- The one-byte transition advances the physical cursor exactly once. -/
@[simp] theorem scanStep_cursor (fileId : String)
    (state : IncrementalScanState) (byte : UInt8) (config : ModeConfig := {}) :
    (scanStep fileId state byte config).cursor = state.cursor + 1 := by
  unfold scanStep
  by_cases space : sourceWhitespace byte config = true
  · rw [if_pos space]
    rcases state with ⟨cursor, mode, completedRev⟩
    cases mode <;> rfl
  · rw [if_neg space]
    rcases state with ⟨cursor, mode, completedRev⟩
    cases mode <;> rfl

/-- Cursor accounting for an arbitrary chunk. -/
theorem scanRun_cursor (fileId : String) (state : IncrementalScanState)
    (bytes : List UInt8) (config : ModeConfig := {}) :
    (scanRun fileId state bytes config).cursor = state.cursor + bytes.length := by
  induction bytes generalizing state with
  | nil => rfl
  | cons byte bytes inductionHypothesis =>
      change (scanRun fileId (scanStep fileId state byte config) bytes config).cursor = _
      rw [inductionHypothesis, scanStep_cursor fileId state byte config]
      simp only [List.length_cons]
      omega

/-- Chunking changes neither state nor emitted spans.  This state-action law
is the reusable streaming pivot: every partition of the same byte sequence
has the same result, including partitions made inside a token. -/
theorem scanRun_append (fileId : String) (state : IncrementalScanState)
    (left right : List UInt8) (config : ModeConfig := {}) :
    scanRun fileId state (left ++ right) config =
      scanRun fileId (scanRun fileId state left config) right config := by
  simp [scanRun, List.foldl_append]

/-- EOF contribution at an arbitrary absolute cursor. -/
def eofSpansAt (fileId : String) (cursor : Nat) :
    ScanMode → List LocatedByteSpan
  | .separator => []
  | .token start => [{ fileId, start, stop := cursor }]

/-- Structurally recursive forward tokenizer over one chunk.  This clear
specification is used only in proofs; `scanRun` is the efficient stateful
implementation. -/
def tokenizeListFrom (fileId : String) (cursor : Nat) (mode : ScanMode)
    (bytes : List UInt8) (config : ModeConfig := {}) : List LocatedByteSpan :=
  match bytes with
  | [] => eofSpansAt fileId cursor mode
  | byte :: bytes =>
      if sourceWhitespace byte config then
        match mode with
        | .separator => tokenizeListFrom fileId (cursor + 1) .separator bytes config
        | .token start =>
            { fileId, start, stop := cursor } ::
              tokenizeListFrom fileId (cursor + 1) .separator bytes config
      else
        match mode with
        | .separator =>
            tokenizeListFrom fileId (cursor + 1) (.token cursor) bytes config
        | .token start =>
            tokenizeListFrom fileId (cursor + 1) (.token start) bytes config

/-- Observe completed spans and flush a possible final token at EOF. -/
def finalizeScan (fileId : String) (state : IncrementalScanState) :
    List LocatedByteSpan :=
  state.completedRev.reverse ++ eofSpansAt fileId state.cursor state.mode

def tokenizeIncrementally (fileId : String) (bytes : ByteArray) (config : ModeConfig := {}) :
    List LocatedByteSpan :=
  finalizeScan fileId (scanRun fileId initialIncrementalState bytes.data.toList config)

/-- The efficient reverse-accumulating fold refines the clear forward
tokenizer for every initial scanner state. -/
theorem finalizeScan_scanRun
    (fileId : String) (state : IncrementalScanState) (bytes : List UInt8)
    (config : ModeConfig := {}) :
    finalizeScan fileId (scanRun fileId state bytes config) =
      state.completedRev.reverse ++
        tokenizeListFrom fileId state.cursor state.mode bytes config := by
  induction bytes generalizing state with
  | nil => rfl
  | cons byte bytes inductionHypothesis =>
      change finalizeScan fileId
          (scanRun fileId (scanStep fileId state byte config) bytes config) = _
      rw [inductionHypothesis]
      conv_rhs => rw [tokenizeListFrom.eq_def]
      rcases state with ⟨cursor, mode, completedRev⟩
      unfold scanStep
      by_cases space : sourceWhitespace byte config = true
      · rw [if_pos space]
        cases mode <;>
          simp_all [applySeparatorDecision]
      · rw [if_neg space]
        cases mode <;>
          simp_all [applySeparatorDecision]

/-- Independent relational characterization of the scanner from an arbitrary
cursor and residual mode.  The root judgment always begins at cursor zero in
`separator` mode; arbitrary interior indices exist only to make composition
and chunk proofs structural. -/
inductive TokenizesFrom (fileId : String) (bytes : ByteArray) (config : ModeConfig := {}) :
    Nat → ScanMode → List LocatedByteSpan → Prop where
  | endSeparator (cursor : Nat)
      (atEnd : ¬ cursor < bytes.size) :
      TokenizesFrom fileId bytes config cursor .separator []
  | endToken (cursor start : Nat)
      (atEnd : ¬ cursor < bytes.size) :
      TokenizesFrom fileId bytes config cursor (.token start)
        [{ fileId, start, stop := bytes.size }]
  | whitespaceSeparator
      (cursor : Nat) (spans : List LocatedByteSpan)
      (inBounds : cursor < bytes.size)
      (isSpace : sourceWhitespace bytes[cursor] config = true)
      (rest : TokenizesFrom fileId bytes config (cursor + 1) .separator spans) :
      TokenizesFrom fileId bytes config cursor .separator spans
  | whitespaceToken
      (cursor start : Nat) (spans : List LocatedByteSpan)
      (inBounds : cursor < bytes.size)
      (isSpace : sourceWhitespace bytes[cursor] config = true)
      (rest : TokenizesFrom fileId bytes config (cursor + 1) .separator spans) :
      TokenizesFrom fileId bytes config cursor (.token start)
        ({ fileId, start, stop := cursor } :: spans)
  | nonWhitespaceSeparator
      (cursor : Nat) (spans : List LocatedByteSpan)
      (inBounds : cursor < bytes.size)
      (notSpace : sourceWhitespace bytes[cursor] config = false)
      (rest : TokenizesFrom fileId bytes config (cursor + 1)
        (.token cursor) spans) :
      TokenizesFrom fileId bytes config cursor .separator spans
  | nonWhitespaceToken
      (cursor start : Nat) (spans : List LocatedByteSpan)
      (inBounds : cursor < bytes.size)
      (notSpace : sourceWhitespace bytes[cursor] config = false)
      (rest : TokenizesFrom fileId bytes config (cursor + 1)
        (.token start) spans) :
      TokenizesFrom fileId bytes config cursor (.token start) spans

/-- Total scanner paired with its relational derivation.  Existence is
therefore a construction, not a corpus assumption or a later theorem about an
optional implementation result. -/
def tokenizeFrom (fileId : String) (bytes : ByteArray)
    (cursor : Nat) (mode : ScanMode) (config : ModeConfig := {}) :
    { spans : List LocatedByteSpan //
      TokenizesFrom fileId bytes config cursor mode spans } :=
  if inBounds : cursor < bytes.size then
    if isSpace : sourceWhitespace bytes[cursor] config then
      match mode with
      | .separator =>
          let rest := tokenizeFrom fileId bytes (cursor + 1) .separator config
          ⟨rest.1,
            .whitespaceSeparator cursor rest.1 inBounds isSpace rest.2⟩
      | .token start =>
          let rest := tokenizeFrom fileId bytes (cursor + 1) .separator config
          ⟨{ fileId, start, stop := cursor } :: rest.1,
            .whitespaceToken cursor start rest.1
              inBounds isSpace rest.2⟩
    else
      have notSpace : sourceWhitespace bytes[cursor] config = false :=
        Bool.eq_false_of_not_eq_true isSpace
      match mode with
      | .separator =>
          let rest := tokenizeFrom fileId bytes (cursor + 1) (.token cursor) config
          ⟨rest.1,
            .nonWhitespaceSeparator cursor rest.1
              inBounds notSpace rest.2⟩
      | .token start =>
          let rest := tokenizeFrom fileId bytes (cursor + 1) (.token start) config
          ⟨rest.1,
            .nonWhitespaceToken cursor start rest.1
              inBounds notSpace rest.2⟩
  else
    match mode with
    | .separator => ⟨[], .endSeparator cursor inBounds⟩
    | .token start =>
        ⟨[{ fileId, start, stop := bytes.size }],
          .endToken cursor start inBounds⟩
termination_by bytes.size - cursor

def tokenize (fileId : String) (bytes : ByteArray) (config : ModeConfig := {}) :
    List LocatedByteSpan :=
  (tokenizeFrom fileId bytes 0 .separator config).1

/-- The clear list tokenizer and the independent byte-array relation's total
constructor compute the same spans on every valid suffix. -/
theorem tokenizeListFrom_drop_eq_tokenizeFrom
    (fileId : String) (bytes : ByteArray) (cursor : Nat) (mode : ScanMode)
    (cursorBound : cursor ≤ bytes.size) (config : ModeConfig := {}) :
    tokenizeListFrom fileId cursor mode (bytes.data.toList.drop cursor) config =
      (tokenizeFrom fileId bytes cursor mode config).1 := by
  rw [tokenizeFrom]
  by_cases inBounds : cursor < bytes.size
  · simp only [dif_pos inBounds]
    have listBound : cursor < bytes.data.toList.length := by
      simpa using inBounds
    rw [List.drop_eq_getElem_cons listBound]
    have getEq : bytes.data.toList[cursor]'listBound =
        bytes.get cursor inBounds := by
      rw [Array.getElem_toList]
      exact (ByteArray.getElem_eq_getElem_data (a := bytes) (i := cursor)).symm
    rw [getEq]
    conv_lhs => rw [tokenizeListFrom.eq_def]
    by_cases space : sourceWhitespace (bytes.get cursor inBounds) config = true
    · have rhsSpace : sourceWhitespace bytes[cursor] config = true := space
      simp only [if_pos space]
      cases mode with
      | separator =>
          split
          · exact tokenizeListFrom_drop_eq_tokenizeFrom fileId bytes
              (cursor + 1) .separator (by omega) config
          · rename_i rhsNotSpace
            exact (rhsNotSpace rhsSpace).elim
      | token start =>
          split
          · exact congrArg ({ fileId, start, stop := cursor } :: ·) <|
              tokenizeListFrom_drop_eq_tokenizeFrom fileId bytes
                (cursor + 1) .separator (by omega) config
          · rename_i rhsNotSpace
            exact (rhsNotSpace rhsSpace).elim
    · have rhsNotSpace : ¬ sourceWhitespace bytes[cursor] config = true := space
      simp only [if_neg space]
      cases mode with
      | separator =>
          split
          · rename_i rhsSpace
            exact (rhsNotSpace rhsSpace).elim
          · exact tokenizeListFrom_drop_eq_tokenizeFrom fileId bytes
              (cursor + 1) (.token cursor) (by omega) config
      | token start =>
          split
          · rename_i rhsSpace
            exact (rhsNotSpace rhsSpace).elim
          · exact tokenizeListFrom_drop_eq_tokenizeFrom fileId bytes
              (cursor + 1) (.token start) (by omega) config
  · have cursorEq : cursor = bytes.size :=
      Nat.le_antisymm cursorBound (Nat.le_of_not_gt inBounds)
    subst cursor
    have dropNil : bytes.data.toList.drop bytes.size = [] :=
      List.drop_eq_nil_iff.mpr (by
        simp)
    rw [dropNil, tokenizeListFrom.eq_def]
    simp only [dif_neg inBounds]
    cases mode <;> rfl
termination_by bytes.size - cursor
decreasing_by
  all_goals omega

/-- Consequently the append-respecting fold computes the unique relational
tokenization of every byte array. -/
theorem tokenizeIncrementally_eq_tokenize (fileId : String)
    (bytes : ByteArray) (config : ModeConfig := {}) :
    tokenizeIncrementally fileId bytes config = tokenize fileId bytes config := by
  unfold tokenizeIncrementally tokenize
  rw [finalizeScan_scanRun fileId initialIncrementalState bytes.data.toList config]
  simp only [initialIncrementalState, List.reverse_nil, List.nil_append]
  exact tokenizeListFrom_drop_eq_tokenizeFrom fileId bytes 0 .separator
    (Nat.zero_le _) config

def Tokenizes (fileId : String) (bytes : ByteArray)
    (spans : List LocatedByteSpan) (config : ModeConfig := {}) : Prop :=
  TokenizesFrom fileId bytes config 0 .separator spans

/-- Positive existence boundary: every byte array has a canonical relational
tokenization, including malformed Metamath sources.  Malformation is handled
by later comment/structural/checker stages rather than partial lexing. -/
theorem tokenize_derives (fileId : String) (bytes : ByteArray) (config : ModeConfig := {}) :
    Tokenizes fileId bytes (tokenize fileId bytes config) config :=
  (tokenizeFrom fileId bytes 0 .separator config).2

/-- The append-respecting implementation itself carries a derivation in the
independent source-owned relation. -/
theorem tokenizeIncrementally_derives
    (fileId : String) (bytes : ByteArray) (config : ModeConfig := {}) :
    Tokenizes fileId bytes (tokenizeIncrementally fileId bytes config) config := by
  rw [tokenizeIncrementally_eq_tokenize fileId bytes config]
  exact tokenize_derives fileId bytes config

/-- Every relational derivation has exactly the output constructed by the
total scanner.  This is the functionality crux used to turn later
implementation soundness into equality with the canonical tokenization. -/
theorem TokenizesFrom.eq_tokenizeFrom
    {fileId : String} {bytes : ByteArray}
    {config : ModeConfig}
    {cursor : Nat} {mode : ScanMode}
    {spans : List LocatedByteSpan}
    (derivation : TokenizesFrom fileId bytes config cursor mode spans) :
    spans = (tokenizeFrom fileId bytes cursor mode config).1 := by
  induction derivation with
  | endSeparator cursor atEnd =>
      rw [tokenizeFrom]
      simp only [dif_neg atEnd]
  | endToken cursor start atEnd =>
      rw [tokenizeFrom]
      simp only [dif_neg atEnd]
  | whitespaceSeparator cursor spans inBounds isSpace rest inductionHypothesis =>
      rw [tokenizeFrom]
      simp only [dif_pos inBounds, dif_pos isSpace]
      exact inductionHypothesis
  | whitespaceToken cursor start spans inBounds isSpace rest inductionHypothesis =>
      rw [tokenizeFrom]
      simp only [dif_pos inBounds, dif_pos isSpace]
      exact congrArg ({ fileId, start, stop := cursor } :: ·) inductionHypothesis
  | nonWhitespaceSeparator cursor spans inBounds notSpace rest inductionHypothesis =>
      rw [tokenizeFrom]
      have notTrue : ¬ sourceWhitespace bytes[cursor] config = true := by
        simp only [notSpace, Bool.false_eq_true, not_false_eq_true]
      simp only [dif_pos inBounds, dif_neg notTrue]
      exact inductionHypothesis
  | nonWhitespaceToken cursor start spans inBounds notSpace rest inductionHypothesis =>
      rw [tokenizeFrom]
      have notTrue : ¬ sourceWhitespace bytes[cursor] config = true := by
        simp only [notSpace, Bool.false_eq_true, not_false_eq_true]
      simp only [dif_pos inBounds, dif_neg notTrue]
      exact inductionHypothesis

/-- The raw-byte tokenization relation is functional. -/
theorem Tokenizes.functional
    {fileId : String} {bytes : ByteArray}
    {config : ModeConfig}
    {left right : List LocatedByteSpan}
    (leftDerivation : Tokenizes fileId bytes left config)
    (rightDerivation : Tokenizes fileId bytes right config) :
    left = right := by
  rw [leftDerivation.eq_tokenizeFrom, rightDerivation.eq_tokenizeFrom]

/-! ## The shipped byte loop cannot invent lexical calls -/

/-- Interpret only scanner states whose pending token is backed by the current
whole-file byte array.  Carried states deliberately have no interpretation
here; their chunk-independent normalization is proved at the later streaming
layer. -/
def currentScanMode? : ParserState.FeedState → Option ScanMode
  | .ws => some .separator
  | .token (.this start) => some (.token start)
  | .token (.old _ _ _) => none

/-- Every token call made by a one-shot production feed is a chronological
prefix of the source-owned tokenization for that same mode.  `feedToken` may
reject malformed structural input early, in which case the fused scanner/parser
intentionally stops before lexing the remaining bytes. -/
theorem feedTrace_normalizedSpans_prefix
    {fileId : String} {bytes : ByteArray} {cursor : Nat}
    {scan : ParserState.FeedState} {before final : ParserState}
    {calls : List TokenCall} {mode : ScanMode}
    (trace : FeedTrace 0 bytes cursor scan before final calls)
    (current : currentScanMode? scan = some mode) :
    calls.map (normalizedCallSpan fileId) <+:
      (tokenizeFrom fileId bytes cursor mode before.db.config).1 := by
  induction trace generalizing mode with
  | endWs cursor before atEnd =>
      simp only [currentScanMode?, Option.some.injEq] at current
      subst mode
      rw [tokenizeFrom]
      simp only [dif_neg atEnd]
      exact List.prefix_refl []
  | endCurrent cursor start before atEnd =>
      simp only [currentScanMode?, Option.some.injEq] at current
      subst mode
      rw [tokenizeFrom]
      simp only [dif_neg atEnd]
      exact List.nil_prefix
  | endCarried cursor oldBase start oldBytes before atEnd =>
      simp [currentScanMode?] at current
  | whitespaceWs cursor before final calls inBounds isSpace rest ih =>
      simp only [currentScanMode?, Option.some.injEq] at current
      subst mode
      have sourceSpace : sourceWhitespace bytes[cursor] before.db.config = true := by
        rw [sourceWhitespace_eq_modeWhitespace _ before.db.config]
        exact isSpace
      rw [tokenizeFrom]
      simp only [dif_pos inBounds, dif_pos sourceSpace]
      have result := ih rfl
      have configEq := ParserState.updateLine_db_config before (0 + cursor) bytes[cursor]!
      have spansEq := congrArg
        (fun config => (tokenizeFrom fileId bytes (cursor + 1) .separator config).1)
        configEq
      rw [spansEq] at result
      exact result
  | currentStop cursor start before error previousConsumed
      inBounds isSpace tokenError =>
      simp only [currentScanMode?, Option.some.injEq] at current
      subst mode
      have sourceSpace : sourceWhitespace bytes[cursor] before.db.config = true := by
        rw [sourceWhitespace_eq_modeWhitespace _ before.db.config]
        exact isSpace
      rw [tokenizeFrom]
      simp only [dif_pos inBounds, dif_pos sourceSpace]
      simp [normalizedCallSpan, normalizedOriginSpan, currentCall]
  | currentContinue cursor start before final calls
      inBounds isSpace tokenOk rest ih =>
      simp only [currentScanMode?, Option.some.injEq] at current
      subst mode
      have sourceSpace : sourceWhitespace bytes[cursor] before.db.config = true := by
        rw [sourceWhitespace_eq_modeWhitespace _ before.db.config]
        exact isSpace
      rw [tokenizeFrom]
      simp only [dif_pos inBounds, dif_pos sourceSpace,
        List.map_cons, List.cons_prefix_cons]
      constructor
      · simp [normalizedCallSpan, normalizedOriginSpan, currentCall]
      · have result := ih rfl
        have configEq : (afterCurrentLine 0 bytes start cursor before).db.config =
            before.db.config := by simp [afterCurrentLine, currentCall]
        have spansEq := congrArg
          (fun config => (tokenizeFrom fileId bytes (cursor + 1) .separator config).1)
          configEq
        rw [spansEq] at result
        exact result
  | carriedStop cursor oldBase start oldBytes before error previousConsumed
      inBounds isSpace tokenError =>
      simp [currentScanMode?] at current
  | carriedContinue cursor oldBase start oldBytes before final calls
      inBounds isSpace tokenOk rest ih =>
      simp [currentScanMode?] at current
  | nonWhitespaceWs cursor before final calls inBounds notSpace rest ih =>
      simp only [currentScanMode?, Option.some.injEq] at current
      subst mode
      have sourceNotSpace : sourceWhitespace bytes[cursor] before.db.config = false := by
        rw [sourceWhitespace_eq_modeWhitespace _ before.db.config]
        exact notSpace
      have notTrue : ¬ sourceWhitespace bytes[cursor] before.db.config = true := by
        simp [sourceNotSpace]
      rw [tokenizeFrom]
      simp only [dif_pos inBounds, dif_neg notTrue]
      exact ih rfl
  | nonWhitespaceToken cursor oldToken before final calls
      inBounds notSpace rest ih =>
      cases oldToken with
      | this start =>
          simp only [currentScanMode?, Option.some.injEq] at current
          subst mode
          have sourceNotSpace : sourceWhitespace bytes[cursor] before.db.config = false := by
            rw [sourceWhitespace_eq_modeWhitespace _ before.db.config]
            exact notSpace
          have notTrue : ¬ sourceWhitespace bytes[cursor] before.db.config = true := by
            simp [sourceNotSpace]
          rw [tokenizeFrom]
          simp only [dif_pos inBounds, dif_neg notTrue]
          exact ih rfl
      | old oldBase start oldBytes =>
          simp [currentScanMode?] at current

/-- The pending span contributed by EOF finalization. -/
def eofSpans (fileId : String) (bytes : ByteArray) :
    ScanMode → List LocatedByteSpan
  | .separator => []
  | .token start => [{ fileId, start, stop := bytes.size }]

/-- Exact one-shot representation of the source scanner's residual mode in
the shipped parser state. -/
def finalCharpAgrees (bytes : ByteArray) (mode : ScanMode)
    (charp : CharParser) : Prop :=
  match mode with
  | .separator => charp = .ws
  | .token start => charp = .token 0 (ByteSliceT.mk bytes start)

/-- A residual token begins inside the current whole-file byte array. -/
def modeStartBound (bytes : ByteArray) : ScanMode → Prop
  | .separator => True
  | .token start => start ≤ bytes.size

/-- A successful whole-file feed retains either no pending token or a token
slice of that same array.  This physical-buffer fact is independent of the
mode's choice of separators. -/
theorem feedTrace_finalCharp
    {bytes : ByteArray} {cursor : Nat}
    {scan : ParserState.FeedState} {before final : ParserState}
    {calls : List TokenCall} {mode : ScanMode}
    (trace : FeedTrace 0 bytes cursor scan before final calls)
    (current : currentScanMode? scan = some mode)
    (modeBound : modeStartBound bytes mode)
    (errorFree : final.db.error? = none) :
    ∃ finalMode,
      finalCharpAgrees bytes finalMode final.charp ∧
      modeStartBound bytes finalMode := by
  induction trace generalizing mode with
  | endWs cursor before atEnd =>
      exact ⟨.separator, rfl, trivial⟩
  | endCurrent cursor start before atEnd =>
      simp only [currentScanMode?, Option.some.injEq] at current
      subst mode
      exact ⟨.token start, rfl, modeBound⟩
  | endCarried cursor oldBase start oldBytes before atEnd =>
      simp [currentScanMode?] at current
  | whitespaceWs cursor before final calls inBounds isSpace rest ih =>
      exact ih rfl trivial errorFree
  | currentStop cursor start before error previousConsumed
      inBounds isSpace tokenError =>
      simp [stopWithConsumed] at errorFree
  | currentContinue cursor start before final calls
      inBounds isSpace tokenOk rest ih =>
      exact ih rfl trivial errorFree
  | carriedStop cursor oldBase start oldBytes before error previousConsumed
      inBounds isSpace tokenError =>
      simp [currentScanMode?] at current
  | carriedContinue cursor oldBase start oldBytes before final calls
      inBounds isSpace tokenOk rest ih =>
      simp [currentScanMode?] at current
  | nonWhitespaceWs cursor before final calls inBounds notSpace rest ih =>
      exact ih rfl (Nat.le_of_lt inBounds) errorFree
  | nonWhitespaceToken cursor oldToken before final calls
      inBounds notSpace rest ih =>
      cases oldToken with
      | this start =>
          simp only [currentScanMode?, Option.some.injEq] at current
          subst mode
          exact ih rfl modeBound errorFree
      | old oldBase start oldBytes =>
          simp [currentScanMode?] at current

/-- The initial whole-file feed has a physically bounded residual token in
every mode, including modes whose separator policy extends the book's. -/
theorem feedAllLogged_finalCharp
    (bytes : ByteArray) (config : ModeConfig := {})
    (errorFree :
      (feedAllLogged (initialState config) 0 bytes).final.db.error? = none) :
    ∃ finalMode,
      finalCharpAgrees bytes finalMode
          (feedAllLogged (initialState config) 0 bytes).final.charp ∧
      modeStartBound bytes finalMode := by
  let run := feedAllLogged (initialState config) 0 bytes
  cases run.trace with
  | ws final calls initialChar feed =>
      exact feedTrace_finalCharp feed rfl trivial errorFree
  | carried oldBase token final calls initialChar feed =>
      have defaultWs : (initialState config).charp = .ws := rfl
      rw [defaultWs] at initialChar
      cases initialChar

/-- If the fused structural parser has not stopped with an error, its calls
followed by the uniquely determined EOF flush equal the complete source
tokenization for the same mode. -/
theorem feedTrace_normalizedSpans_complete
    {fileId : String} {bytes : ByteArray} {cursor : Nat}
    {scan : ParserState.FeedState} {before final : ParserState}
    {calls : List TokenCall} {mode : ScanMode}
    (trace : FeedTrace 0 bytes cursor scan before final calls)
    (current : currentScanMode? scan = some mode)
    (modeBound : modeStartBound bytes mode)
    (errorFree : final.db.error? = none) :
    ∃ finalMode,
      finalCharpAgrees bytes finalMode final.charp ∧
      modeStartBound bytes finalMode ∧
      calls.map (normalizedCallSpan fileId) ++
          eofSpans fileId bytes finalMode =
        (tokenizeFrom fileId bytes cursor mode before.db.config).1 := by
  induction trace generalizing mode with
  | endWs cursor before atEnd =>
      simp only [currentScanMode?, Option.some.injEq] at current
      subst mode
      refine ⟨.separator, rfl, trivial, ?_⟩
      rw [tokenizeFrom]
      simp [atEnd, eofSpans]
  | endCurrent cursor start before atEnd =>
      simp only [currentScanMode?, Option.some.injEq] at current
      subst mode
      refine ⟨.token start, rfl, modeBound, ?_⟩
      rw [tokenizeFrom]
      simp [atEnd, eofSpans]
  | endCarried cursor oldBase start oldBytes before atEnd =>
      simp [currentScanMode?] at current
  | whitespaceWs cursor before final calls inBounds isSpace rest ih =>
      simp only [currentScanMode?, Option.some.injEq] at current
      subst mode
      obtain ⟨finalMode, finalCharp, finalBound, callsEq⟩ :=
        ih rfl trivial errorFree
      refine ⟨finalMode, finalCharp, finalBound, ?_⟩
      have sourceSpace : sourceWhitespace bytes[cursor] before.db.config = true := by
        rw [sourceWhitespace_eq_modeWhitespace _ before.db.config]
        exact isSpace
      rw [tokenizeFrom]
      simp only [dif_pos inBounds, dif_pos sourceSpace]
      have configEq := ParserState.updateLine_db_config before (0 + cursor) bytes[cursor]!
      have spansEq := congrArg
        (fun config => (tokenizeFrom fileId bytes (cursor + 1) .separator config).1)
        configEq
      rw [spansEq] at callsEq
      exact callsEq
  | currentStop cursor start before error previousConsumed
      inBounds isSpace tokenError =>
      simp [stopWithConsumed] at errorFree
  | currentContinue cursor start before final calls
      inBounds isSpace tokenOk rest ih =>
      simp only [currentScanMode?, Option.some.injEq] at current
      subst mode
      obtain ⟨finalMode, finalCharp, finalBound, callsEq⟩ :=
        ih rfl trivial errorFree
      refine ⟨finalMode, finalCharp, finalBound, ?_⟩
      have sourceSpace : sourceWhitespace bytes[cursor] before.db.config = true := by
        rw [sourceWhitespace_eq_modeWhitespace _ before.db.config]
        exact isSpace
      rw [tokenizeFrom]
      simp only [dif_pos inBounds, dif_pos sourceSpace, List.map_cons,
        List.cons_append]
      have configEq : (afterCurrentLine 0 bytes start cursor before).db.config =
          before.db.config := by simp [afterCurrentLine, currentCall]
      have spansEq := congrArg
        (fun config => (tokenizeFrom fileId bytes (cursor + 1) .separator config).1)
        configEq
      rw [spansEq] at callsEq
      rw [callsEq]
      simp [normalizedCallSpan, normalizedOriginSpan, currentCall]
  | carriedStop cursor oldBase start oldBytes before error previousConsumed
      inBounds isSpace tokenError =>
      simp [currentScanMode?] at current
  | carriedContinue cursor oldBase start oldBytes before final calls
      inBounds isSpace tokenOk rest ih =>
      simp [currentScanMode?] at current
  | nonWhitespaceWs cursor before final calls inBounds notSpace rest ih =>
      simp only [currentScanMode?, Option.some.injEq] at current
      subst mode
      obtain ⟨finalMode, finalCharp, finalBound, callsEq⟩ :=
        ih rfl (Nat.le_of_lt inBounds) errorFree
      refine ⟨finalMode, finalCharp, finalBound, ?_⟩
      have sourceNotSpace : sourceWhitespace bytes[cursor] before.db.config = false := by
        rw [sourceWhitespace_eq_modeWhitespace _ before.db.config]
        exact notSpace
      have notTrue : ¬ sourceWhitespace bytes[cursor] before.db.config = true := by
        simp [sourceNotSpace]
      rw [tokenizeFrom]
      simp only [dif_pos inBounds, dif_neg notTrue]
      exact callsEq
  | nonWhitespaceToken cursor oldToken before final calls
      inBounds notSpace rest ih =>
      cases oldToken with
      | this start =>
          simp only [currentScanMode?, Option.some.injEq] at current
          subst mode
          obtain ⟨finalMode, finalCharp, finalBound, callsEq⟩ :=
            ih rfl modeBound errorFree
          refine ⟨finalMode, finalCharp, finalBound, ?_⟩
          have sourceNotSpace : sourceWhitespace bytes[cursor] before.db.config = false := by
            rw [sourceWhitespace_eq_modeWhitespace _ before.db.config]
            exact notSpace
          have notTrue : ¬ sourceWhitespace bytes[cursor] before.db.config = true := by
            simp [sourceNotSpace]
          rw [tokenizeFrom]
          simp only [dif_pos inBounds, dif_neg notTrue]
          exact callsEq
      | old oldBase start oldBytes =>
          simp [currentScanMode?] at current

/-- The one-shot ingress starts in current-buffer whitespace mode, so the
all-mode prefix property needs no additional scanner-state premise. -/
theorem feedAllLogged_normalizedSpans_prefix
    (fileId : String) (bytes : ByteArray) (config : ModeConfig := {}) :
    let run := feedAllLogged (initialState config) 0 bytes
    run.calls.map (normalizedCallSpan fileId) <+:
      tokenize fileId bytes config := by
  let run := feedAllLogged (initialState config) 0 bytes
  change run.calls.map (normalizedCallSpan fileId) <+:
    (tokenizeFrom fileId bytes 0 .separator config).1
  cases run.trace with
  | ws final calls initialChar feed =>
      exact feedTrace_normalizedSpans_prefix feed rfl
  | carried oldBase token final calls initialChar feed =>
      have defaultWs : (initialState config).charp = .ws := rfl
      rw [defaultWs] at initialChar
      cases initialChar

/-- Exact all-mode one-shot feed characterization whenever the fused
structural parser reaches EOF without an earlier error. -/
theorem feedAllLogged_normalizedSpans_complete
    (fileId : String) (bytes : ByteArray) (config : ModeConfig := {})
    (errorFree :
      (feedAllLogged (initialState config) 0 bytes).final.db.error? = none) :
    ∃ finalMode,
      finalCharpAgrees bytes finalMode
          (feedAllLogged (initialState config) 0 bytes).final.charp ∧
      modeStartBound bytes finalMode ∧
      (feedAllLogged (initialState config) 0 bytes).calls.map
            (normalizedCallSpan fileId) ++
          eofSpans fileId bytes finalMode =
        tokenize fileId bytes config := by
  let run := feedAllLogged (initialState config) 0 bytes
  change ∃ finalMode,
    finalCharpAgrees bytes finalMode run.final.charp ∧
    modeStartBound bytes finalMode ∧
    run.calls.map (normalizedCallSpan fileId) ++
        eofSpans fileId bytes finalMode =
      (tokenizeFrom fileId bytes 0 .separator config).1
  cases run.trace with
  | ws final calls initialChar feed =>
      exact feedTrace_normalizedSpans_complete feed rfl trivial errorFree
  | carried oldBase token final calls initialChar feed =>
      have defaultWs : (initialState config).charp = .ws := rfl
      rw [defaultWs] at initialChar
      cases initialChar

/-- Under a successful EOF result, the production `done` phase emits exactly
the residual span described by the source scanner mode. -/
theorem doneTrace_normalizedSpans_eq_eof
    {fileId : String} {bytes : ByteArray} {before : ParserState}
    {db : DB} {calls : List TokenCall} {mode : ScanMode}
    (trace : DoneTrace before bytes.size db calls)
    (agrees : finalCharpAgrees bytes mode before.charp)
    (modeBound : modeStartBound bytes mode)
    (errorFree : db.error? = none) :
    calls.map (normalizedCallSpan fileId) = eofSpans fileId bytes mode := by
  cases trace with
  | priorError priorError =>
      have errorFalse : before.db.error = false := by
        simp [DB.error, errorFree]
      rw [errorFalse] at priorError
      cases priorError
  | whitespace noPriorError charpWhitespace =>
      cases mode with
      | separator => rfl
      | token start =>
          simp only [finalCharpAgrees] at agrees
          rw [charpWhitespace] at agrees
          cases agrees
  | trailingError parserOffset token noPriorError charpToken tokenError =>
      have errorFalse :
          (trailingCall parserOffset bytes.size token before).after.db.error =
            false := by
        simp [DB.error, errorFree]
      rw [errorFalse] at tokenError
      cases tokenError
  | trailingClose parserOffset token noPriorError charpToken tokenOk =>
      cases mode with
      | separator =>
          simp only [finalCharpAgrees] at agrees
          rw [charpToken] at agrees
          cases agrees
      | token start =>
          simp only [finalCharpAgrees] at agrees
          rw [charpToken] at agrees
          injection agrees with parserOffsetEq tokenEq
          subst parserOffset
          subst token
          change start ≤ bytes.size at modeBound
          simp [normalizedCallSpan, normalizedOriginSpan, trailingCall,
            eofSpans, ByteSliceT.mk, ByteArray.toByteSlice,
            ByteSlice.start, modeBound]

/-- Successful EOF completion implies that the incoming parser state was
already error-free; `done` never clears a prior error. -/
theorem doneTrace_before_errorFree
    {before : ParserState} {eofOffset : Nat} {db : DB}
    {calls : List TokenCall}
    (trace : DoneTrace before eofOffset db calls)
    (errorFree : db.error? = none) :
    before.db.error? = none := by
  cases trace with
  | priorError priorError => exact errorFree
  | whitespace noPriorError charpWhitespace =>
      cases prior : before.db.error? with
      | none => rfl
      | some interrupt => simp [DB.error, prior] at noPriorError
  | trailingError parserOffset token noPriorError charpToken tokenError =>
      cases prior : before.db.error? with
      | none => rfl
      | some interrupt => simp [DB.error, prior] at noPriorError
  | trailingClose parserOffset token noPriorError charpToken tokenOk =>
      cases prior : before.db.error? with
      | none => rfl
      | some interrupt => simp [DB.error, prior] at noPriorError

/-- On every source accepted through EOF by the shipped one-shot parser,
its exact chronological token-call spans equal the tokenization extracted
from the authored scannerless presentation specialized to the same mode. -/
theorem checkBytesCoreLogged_normalizedSpans_complete
    (fileId : String) (bytes : ByteArray) (config : ModeConfig := {})
    (errorFree : (checkBytesCoreLogged bytes config).db.error? = none) :
    (checkBytesCoreLogged bytes config).calls.map
        (normalizedCallSpan fileId) = tokenize fileId bytes config := by
  let feedRun := feedAllLogged (initialState config) 0 bytes
  let doneRun := doneLogged feedRun.final bytes.size
  change doneRun.db.error? = none at errorFree
  change (feedRun.calls ++ doneRun.calls).map
      (normalizedCallSpan fileId) = tokenize fileId bytes config
  have feedErrorFree : feedRun.final.db.error? = none :=
    doneTrace_before_errorFree doneRun.trace errorFree
  obtain ⟨finalMode, finalCharp, finalBound, feedCalls⟩ :=
    feedAllLogged_normalizedSpans_complete fileId bytes config feedErrorFree
  have doneCalls :
      doneRun.calls.map (normalizedCallSpan fileId) =
        eofSpans fileId bytes finalMode :=
    doneTrace_normalizedSpans_eq_eof doneRun.trace finalCharp finalBound
      errorFree
  rw [List.map_append, doneCalls]
  exact feedCalls

/-- Raw-byte fusion theorem: in every mode and on every successful input,
mm-lean4's shipped one-shot byte/parser loop emits exactly the spans computed
by the native append-respecting scanner generated from the mode-specialized
authored separator definition.  No token-list equality premise or second
lexical authority appears in the statement. -/
theorem checkBytesCoreLogged_eq_incrementalGSLTScanner
    (fileId : String) (bytes : ByteArray) (config : ModeConfig := {})
    (errorFree : (checkBytesCoreLogged bytes config).db.error? = none) :
    (checkBytesCoreLogged bytes config).calls.map
        (normalizedCallSpan fileId) = tokenizeIncrementally fileId bytes config := by
  rw [tokenizeIncrementally_eq_tokenize fileId bytes config]
  exact checkBytesCoreLogged_normalizedSpans_complete
    fileId bytes config errorFree

/-- Positive calibration: one ASCII token is retained at its exact physical
span. -/
theorem oneToken_positive :
    Tokenizes "one-token" "x".toUTF8
      [{ fileId := "one-token", start := 0, stop := 1 }] := by
  exact TokenizesFrom.nonWhitespaceSeparator 0
    [{ fileId := "one-token", start := 0, stop := 1 }]
    (by decide)
    (by rw [sourceWhitespace_eq_isWhitespace]; decide)
    (TokenizesFrom.endToken 1 0 (by decide))

/-- Negative calibration: a non-whitespace byte cannot yield the empty token
stream. -/
theorem oneToken_not_empty :
    ¬ Tokenizes "one-token" "x".toUTF8 [] := by
  intro emptyDerivation
  have unique := Tokenizes.functional emptyDerivation oneToken_positive
  cases unique

/-- The book-oriented modes do not turn vertical tab into a separator. -/
theorem verticalTab_strictModes_content :
    sourceWhitespace 11 = false ∧
    sourceWhitespace 11 .zar = false ∧
    sourceWhitespace 11 .sound = false ∧
    sourceWhitespace 11 .knife = false := by
  decide +kernel

/-- The executable-compatible and permissive modes admit vertical tab. -/
theorem verticalTab_extendedModes_separator :
    sourceWhitespace 11 .exe = true ∧
    sourceWhitespace 11 .permissive = true := by
  decide +kernel

private def verticalTabBetweenLetters : ByteArray := ByteArray.mk #[97, 11, 98]

/-- A mode port changes actual source scanning, not merely its classifier:
exe and permissive split the two letter spans around vertical tab. -/
theorem verticalTab_extendedModes_twoSpans :
    tokenizeIncrementally "vertical-tab" verticalTabBetweenLetters .exe =
      [{ fileId := "vertical-tab", start := 0, stop := 1 },
       { fileId := "vertical-tab", start := 2, stop := 3 }] ∧
    tokenizeIncrementally "vertical-tab" verticalTabBetweenLetters .permissive =
      [{ fileId := "vertical-tab", start := 0, stop := 1 },
       { fileId := "vertical-tab", start := 2, stop := 3 }] := by
  decide +kernel

/-- Negative scanner control: the book mode keeps vertical tab inside one
token and cannot produce the executable-mode pair of spans. -/
theorem verticalTab_default_not_twoSpans :
    tokenizeIncrementally "vertical-tab" verticalTabBetweenLetters =
      [{ fileId := "vertical-tab", start := 0, stop := 3 }] ∧
    tokenizeIncrementally "vertical-tab" verticalTabBetweenLetters ≠
      [{ fileId := "vertical-tab", start := 0, stop := 1 },
       { fileId := "vertical-tab", start := 2, stop := 3 }] := by
  decide +kernel

end Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
