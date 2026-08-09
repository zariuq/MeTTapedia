import Mettapedia.Languages.Metamath.SourceGSLTCheckerAlignment
import Mettapedia.Languages.Metamath.SourceGSLTIncludeDAG
import Mettapedia.Languages.Metamath.SourceGSLTCompressedParserComposition
import Mettapedia.Languages.Metamath.SourceGSLTLexicalClosure
import Metamath.ParserOperations

/-!
# Reader-trace binding for the Metamath source GSLT

This module derives the same-buffer lexical binding between the authored
raw-byte/comment pipeline and the token calls made by mm-lean4's shipped
reader.  The reader trace is observed; ordered token equality is not supplied
as a premise.

The first layer is a fusion theorem.  The source specification tokenizes and
then removes complete comments, while the implementation scans bytes and
feeds tokens in one pass.  A successful source-side comment pass and the
reader's proof-relevant call chain determine the same surviving occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.SourceGSLTReaderTraceBinding

open Metamath.Verify
open Mettapedia.GSLT.LanguageDef.GrammarInferenceExtraction
open Mettapedia.Languages.Metamath.InferenceOneShotByteLog
open Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
open Mettapedia.Languages.Metamath.SourceGSLTIncludeDAG
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.Metamath.SourceGSLTCheckerAlignment
open Mettapedia.Languages.Metamath.SourceGSLTCompressedMMLean4
open Mettapedia.Languages.Metamath.SourceGSLTCompressedParserComposition
open Mettapedia.Languages.Metamath.SourceGSLTDerivationCorrespondence
open Mettapedia.Languages.Metamath.SourceGSLTLexicalClosure
open Mettapedia.Languages.Metamath.ByteSliceForInSupport

private def tokenOfCall (call : TokenCall) : ByteSlice :=
  InferenceOneShotByteLog.Raw.TokenOrigin.token call.origin

/-- The byte content submitted by one production-reader call. -/
def callBytes (call : TokenCall) : List UInt8 :=
  sliceBytes (tokenOfCall call)

/-- Whether the production token parser is currently suspended inside one
Metamath comment.  Successful source runs never nest comments, so a Boolean
is the exact source-side state needed by `stripComments`. -/
def readerInComment : TokenParser → Bool
  | .comment _ => true
  | .includePath resume _ => readerInComment resume
  | .includeClose resume _ _ => readerInComment resume
  | _ => false

private theorem readerInComment_withDB (state : ParserState) (f : DB → DB) :
    readerInComment (state.withDB f).tokp = readerInComment state.tokp := by
  rfl

private theorem readerInComment_label (state : ParserState) (position : Pos)
    (token : ByteSlice) (outside : readerInComment state.tokp = false) :
    readerInComment (state.label position token).tokp = false := by
  rcases labelResult : toLabel token with ⟨ok, name⟩
  cases ok with
  | false =>
      simpa [ParserState.label, labelResult, ParserState.mkErrorFromEvidence,
        ParserState.withDB] using outside
  | true => simp [ParserState.label, labelResult, readerInComment]

private theorem readerInComment_sym (state : ParserState) (position : Pos)
    (token : ByteSlice) (kind : String → Object)
    (outside : readerInComment state.tokp = false) :
    readerInComment (state.sym position token kind).tokp = false := by
  unfold ParserState.sym
  by_cases endToken : token.eqArray "$.".toAscii = true
  · simp [endToken, readerInComment]
  · rw [if_neg endToken]
    unfold ParserState.withMath
    rcases mathResult : toMath token with ⟨ok, name⟩
    cases ok with
    | false =>
        simpa [mathResult, ParserState.mkErrorFromEvidence,
          ParserState.withDB] using outside
    | true => simpa [mathResult, ParserState.withDB] using outside

private theorem readerInComment_feedProof (state : ParserState)
    (token : ByteSlice) (proof : ProofState)
    (outside : readerInComment state.tokp = false) :
    readerInComment (state.feedProof token proof).tokp = false := by
  cases execution : ParserState.feedProof.go state token proof with
  | ok next =>
      simp [ParserState.feedProof, execution, ParserState.withAt_tokp,
        readerInComment]
  | error failure =>
      simpa [ParserState.feedProof, execution, ParserState.withAt_tokp,
        ParserState.mkErrorFromEvidence, ParserState.withDB] using outside

private theorem readerInComment_feedTokens (state : ParserState)
    (symbols : Array Sym) (parser : TokensParser)
    (outside : readerInComment state.tokp = false) :
    readerInComment (state.feedTokens symbols parser).tokp = false := by
  cases parser with
  | mk kind position label =>
      by_cases hasHead : Formula.hasConstHead symbols = true
      · cases kind with
        | float =>
            by_cases floatShape : Formula.isFloatShape symbols = true
            · simp [ParserState.feedTokens, hasHead, floatShape,
                ParserState.withAt_tokp, readerInComment,
                ParserState.withDB]
            · simpa [ParserState.feedTokens, hasHead, floatShape,
                ParserState.withAt_tokp, ParserState.mkErrorFromEvidence,
                ParserState.withDB] using outside
        | ess =>
            cases scopeGate : ParserState.topLevelEssViolation? state.db with
            | none =>
                simp [ParserState.feedTokens, hasHead, scopeGate,
                  ParserState.withAt_tokp, readerInComment,
                  ParserState.withDB]
            | some failure =>
                simpa [ParserState.feedTokens, hasHead, scopeGate,
                    ParserState.withAt_tokp,
                    ParserState.mkErrorFromEvidence, ParserState.withDB]
                  using outside
        | ax =>
            simp [ParserState.feedTokens, hasHead,
              ParserState.withAt_tokp, readerInComment,
              ParserState.withDB]
        | thm =>
            cases frameResult : state.db.trimFrame' symbols with
            | error failure =>
                simpa [ParserState.feedTokens, hasHead, frameResult,
                    ParserState.withAt_tokp,
                    ParserState.mkErrorFromEvidence, ParserState.withDB]
                  using outside
            | ok frame =>
                by_cases interrupted : state.db.interrupt = true
                · simpa [ParserState.feedTokens, hasHead, frameResult,
                    interrupted, ParserState.withAt_tokp,
                    ParserState.withDB] using outside
                · simp [ParserState.feedTokens, hasHead, frameResult,
                    interrupted, ParserState.withAt_tokp,
                    ParserState.resumeThm, readerInComment]
      · simpa [ParserState.feedTokens, hasHead,
          ParserState.withAt_tokp, ParserState.mkErrorFromEvidence,
          ParserState.withDB] using outside

private theorem readerInComment_djvarsLoopAux (names : Array String)
    (state : ParserState) (position : Pos) (token : String) (index : Nat)
    (outside : readerInComment state.tokp = false) :
    readerInComment
      (ParserState.djvars_loop_aux names state position token index).tokp =
        false := by
  unfold ParserState.djvars_loop_aux
  by_cases inBounds : index < names.size
  · simp only [inBounds, dite_true]
    by_cases duplicate : names[index] == token
    · simp only [duplicate, if_true]
      simpa [ParserState.mkErrorFromEvidence, ParserState.withDB] using outside
    · simp only [duplicate]
      exact readerInComment_djvarsLoopAux names
        (state.withDB fun database => database.withDJ fun pairs =>
          pairs.push (if names[index] < token then (names[index], token)
            else (token, names[index])))
        position token (index + 1)
        (by simpa [ParserState.withDB] using outside)
  · simp [inBounds, readerInComment]
termination_by names.size - index
decreasing_by omega

private theorem readerInComment_djvarsLoop (names : Array String)
    (state : ParserState) (position : Pos) (token : String)
    (outside : readerInComment state.tokp = false) :
    readerInComment
      (ParserState.djvars_loop names state position token).tokp = false := by
  unfold ParserState.djvars_loop
  cases violation : state.db.djvarsScopeViolation? token with
  | some failure =>
      simpa [violation, ParserState.mkErrorFromEvidence,
        ParserState.withDB] using outside
  | none =>
      exact readerInComment_djvarsLoopAux names state position token 0 outside

private theorem readerInComment_feedToken_include
    (state : ParserState) (offset : Nat) (token : ByteSlice)
    (outside : readerInComment state.tokp = false)
    (notCommentOpen : token.eqArray "$(".toAscii ≠ true)
    (includeOpen : token.eqArray "$[".toAscii = true) :
    readerInComment (state.feedToken offset token).tokp = false := by
  have commentOpenFalse : token.eqArray "$(".toAscii = false := by
    cases result : token.eqArray "$(".toAscii <;> simp_all
  cases modeEq : state.tokp
  case comment inner => simp [readerInComment, modeEq] at outside
  case start =>
    cases gate : includeDirectiveViolation? state.db.config
        state.db.scopes.size false offset <;>
      simp [ParserState.feedToken, modeEq, commentOpenFalse, includeOpen,
        gate, readerInComment, ParserState.mkErrorFromEvidence,
        ParserState.withDB]
  case includePath resume position =>
    have resumeOutside : readerInComment resume = false := by
      simpa [modeEq, readerInComment] using outside
    cases gate : includeDirectiveViolation? state.db.config
        state.db.scopes.size true offset <;>
      simp [ParserState.feedToken, modeEq, commentOpenFalse, includeOpen,
        gate, readerInComment, resumeOutside,
        ParserState.mkErrorFromEvidence, ParserState.withDB]
  case includeClose resume position path =>
    have resumeOutside : readerInComment resume = false := by
      simpa [modeEq, readerInComment] using outside
    cases gate : includeDirectiveViolation? state.db.config
        state.db.scopes.size true offset <;>
      simp [ParserState.feedToken, modeEq, commentOpenFalse, includeOpen,
        gate, readerInComment, resumeOutside,
        ParserState.mkErrorFromEvidence, ParserState.withDB]
  all_goals
    cases gate : includeDirectiveViolation? state.db.config
        state.db.scopes.size true offset <;>
      simp [ParserState.feedToken, modeEq, commentOpenFalse, includeOpen,
        gate, readerInComment, ParserState.mkErrorFromEvidence,
        ParserState.withDB]

/-- Outside a comment, every non-opener token leaves the production parser
outside comment mode.  This theorem is about the shipped `feedToken`; helper
operations are unfolded only far enough to prove that none can manufacture a
comment wrapper. -/
theorem readerInComment_feedToken_outside_of_notOpen
    (state : ParserState) (offset : Nat) (token : ByteSlice)
    (outside : readerInComment state.tokp = false)
    (notCommentOpen : token.eqArray "$(".toAscii ≠ true) :
    readerInComment (state.feedToken offset token).tokp = false := by
  have commentOpenFalse : token.eqArray "$(".toAscii = false := by
    cases result : token.eqArray "$(".toAscii <;> simp_all
  by_cases includeOpen : token.eqArray "$[".toAscii = true
  · exact readerInComment_feedToken_include state offset token outside
      notCommentOpen includeOpen
  · cases modeEq : state.tokp
    case comment inner => simp [readerInComment, modeEq] at outside
    case start =>
      simp only [ParserState.feedToken, modeEq, commentOpenFalse,
        includeOpen, Bool.false_eq_true, if_false]
      by_cases command : token.len == 2 && token[0]! == '$'.toUInt8
      · rw [if_pos command]
        split <;> try rfl
        · simpa [ParserState.withDB] using outside
        · simpa [ParserState.withDB] using outside
        exact readerInComment_label state (state.mkPos offset) token outside
      · rw [if_neg command]
        exact readerInComment_label state (state.mkPos offset) token outside
    case const seen =>
      simp only [ParserState.feedToken, modeEq, commentOpenFalse,
        includeOpen, Bool.false_eq_true, if_false]
      by_cases endToken : token.eqArray "$.".toAscii = true
      · rw [if_pos endToken]
        cases seen with
        | false =>
            simpa [ParserState.mkErrorFromEvidence,
              ParserState.withDB] using outside
        | true => rfl
      · rw [if_neg endToken]
        rfl
    case var seen =>
      simp only [ParserState.feedToken, modeEq, commentOpenFalse,
        includeOpen, Bool.false_eq_true, if_false]
      by_cases endToken : token.eqArray "$.".toAscii = true
      · rw [if_pos endToken]
        cases seen with
        | false =>
            simpa [ParserState.mkErrorFromEvidence,
              ParserState.withDB] using outside
        | true => rfl
      · rw [if_neg endToken]
        rfl
    case djvars names =>
      simp only [ParserState.feedToken, modeEq, commentOpenFalse,
        includeOpen, Bool.false_eq_true, if_false]
      by_cases endToken : token.eqArray "$.".toAscii = true
      · by_cases tooShort : names.size ≤ 1
        · simpa [endToken, tooShort, ParserState.mkErrorFromEvidence,
            ParserState.withDB] using outside
        · simp [endToken, tooShort, readerInComment]
      · rw [if_neg endToken]
        unfold ParserState.withMath
        rcases mathResult : toMath token with ⟨ok, name⟩
        cases ok with
        | false =>
            simpa [mathResult, ParserState.mkErrorFromEvidence,
              ParserState.withDB] using outside
        | true =>
            exact readerInComment_djvarsLoop names state
              (state.mkPos offset) name outside
    case math symbols parser =>
      simp only [ParserState.feedToken, modeEq, commentOpenFalse,
        includeOpen, Bool.false_eq_true, if_false]
      by_cases delimiter : token.eqArray parser.k.delim = true
      · rw [if_pos delimiter]
        exact readerInComment_feedTokens state symbols parser outside
      · rw [if_neg delimiter]
        unfold ParserState.withMath
        rcases mathResult : toMath token with ⟨ok, name⟩
        cases ok with
        | false =>
            simpa [mathResult, ParserState.mkErrorFromEvidence,
              ParserState.withDB] using outside
        | true =>
            cases objectResult : state.db.find? name with
            | none =>
                cases violation : state.db.mathSymbolViolation? name <;>
                  simpa [objectResult, ParserState.mkErrorFromEvidence,
                    ParserState.withDB] using outside
            | some object =>
                cases object with
                | const name => simp [objectResult, readerInComment]
                | var objectName =>
                    by_cases active : state.db.isActiveVar name = true
                    · simp [objectResult, active, readerInComment]
                    · simpa [objectResult, active,
                        ParserState.mkErrorFromEvidence,
                        ParserState.withDB] using outside
                | hyp essential formula label =>
                    cases violation : state.db.mathSymbolViolation? name <;>
                      simpa [objectResult, violation,
                        ParserState.mkErrorFromEvidence,
                        ParserState.withDB] using outside
                | assert formula frame label =>
                    cases violation : state.db.mathSymbolViolation? name <;>
                      simpa [objectResult, violation,
                        ParserState.mkErrorFromEvidence,
                        ParserState.withDB] using outside
    case label position label =>
      simp only [ParserState.feedToken, modeEq, commentOpenFalse,
        includeOpen, Bool.false_eq_true, if_false]
      by_cases command : token.len == 2 && token[0]! == '$'.toUInt8
      · rw [if_pos command]
        split <;> try rfl
        simpa [ParserState.mkErrorFromEvidence,
          ParserState.withDB] using outside
      · simpa [command, ParserState.mkErrorFromEvidence,
          ParserState.withDB] using outside
    case includePath resume position =>
      have resumeOutside : readerInComment resume = false := by
        simpa [modeEq, readerInComment] using outside
      simp only [ParserState.feedToken, modeEq, commentOpenFalse,
        includeOpen, Bool.false_eq_true, if_false]
      by_cases closeToken : token.eqArray "$]".toAscii = true
      · simpa [closeToken, ParserState.mkErrorFromEvidence,
          ParserState.withDB] using outside
      · rw [if_neg closeToken]
        cases pathResult : ParserState.normalizeIncludePath
            state.db.config.literalIncludePaths state.sourceFile
            (ParserState.includePathFromToken token).1 with
        | error failure =>
            simpa [ParserState.mkErrorFromEvidence,
              ParserState.withDB] using outside
        | ok path =>
            by_cases closesInline :
                (ParserState.includePathFromToken token).2 = true <;>
              simp [closesInline, readerInComment, resumeOutside,
                ParserState.requestInclude]
    case includeClose resume position path =>
      have resumeOutside : readerInComment resume = false := by
        simpa [modeEq, readerInComment] using outside
      simp only [ParserState.feedToken, modeEq, commentOpenFalse,
        includeOpen, Bool.false_eq_true, if_false]
      by_cases closeToken : token.eqArray "$]".toAscii = true
      · simp [closeToken, resumeOutside, ParserState.requestInclude]
      · simpa [closeToken, ParserState.mkErrorFromEvidence,
          ParserState.withDB] using outside
    case proof proof =>
      simp only [ParserState.feedToken, modeEq, commentOpenFalse,
        includeOpen, Bool.false_eq_true, if_false]
      let cleared : ParserState := { state with tokp := default }
      by_cases endToken : token.eqArray "$.".toAscii = true
      · rw [if_pos endToken]
        have finished :=
          Metamath.ParserOps.finishProof_tokp_start cleared proof
        rw [finished]
        rfl
      · rw [if_neg endToken]
        exact readerInComment_feedProof cleared token proof (by rfl)

/-- The literal comment opener is the unique transition from an outside mode
to a comment wrapper, and it suspends the exact prior mode. -/
theorem feedToken_commentOpen
    (state : ParserState) (offset : Nat) (token : ByteSlice)
    (outside : readerInComment state.tokp = false)
    (isOpen : token.eqArray "$(".toAscii = true) :
    (state.feedToken offset token).tokp = .comment state.tokp := by
  cases modeEq : state.tokp
  case comment inner => simp [readerInComment, modeEq] at outside
  all_goals simp [ParserState.feedToken, modeEq, isOpen]

/-- A closing delimiter restores the exact parser mode suspended by the
comment opener. -/
theorem feedToken_commentClose
    (state : ParserState) (offset : Nat) (token : ByteSlice)
    (inner : TokenParser)
    (commentMode : state.tokp = .comment inner)
    (isClose : token.eqArray "$)".toAscii = true) :
    (state.feedToken offset token).tokp = inner := by
  simp [ParserState.feedToken, commentMode, isClose]

/-- A token that is neither comment delimiter leaves the complete suspended
comment mode unchanged. -/
theorem feedToken_commentInterior
    (state : ParserState) (offset : Nat) (token : ByteSlice)
    (inner : TokenParser)
    (commentMode : state.tokp = .comment inner)
    (notClose : token.eqArray "$)".toAscii ≠ true)
    (notOpen : token.eqArray "$(".toAscii ≠ true) :
    (state.feedToken offset token).tokp = .comment inner := by
  simp [ParserState.feedToken, commentMode, notClose, notOpen]

/-- The production delimiter test is exactly the source comment-open byte
word; no string conversion participates in the comparison. -/
theorem callCommentOpen_iff (call : TokenCall) :
    (tokenOfCall call).eqArray "$(".toAscii = true ↔
      callBytes call = commentOpenBytes := by
  unfold callBytes
  rw [eqArray_true_iff, commentOpen_toAscii]
  rfl

/-- The analogous exact characterization of the comment-close delimiter. -/
theorem callCommentClose_iff (call : TokenCall) :
    (tokenOfCall call).eqArray "$)".toAscii = true ↔
      callBytes call = commentCloseBytes := by
  unfold callBytes
  rw [eqArray_true_iff]
  change sliceBytes (tokenOfCall call) = [36, 41] ↔ _
  rfl

/-! ## Proof-relevant token-call chronology -/

/-- The exact parser-mode chronology of a list of production `feedToken`
calls.  It records the mode before the first call, the transition performed
by every call, and the mode after the final call. -/
inductive CallModeTrace :
    TokenParser → List TokenCall → TokenParser → Type where
  | nil (mode : TokenParser) : CallModeTrace mode [] mode
  | cons {initial final : TokenParser} {calls : List TokenCall}
      (call : TokenCall)
      (beforeEq : call.before.tokp = initial)
      (tail : CallModeTrace call.after.tokp calls final) :
      CallModeTrace initial (call :: calls) final

/-- Agreement between the source comment bit and the production parser mode.
The inside case also records that the suspended mode is itself outside a
comment, ruling out a silently nested wrapper. -/
inductive CommentModeAgrees : Bool → TokenParser → Prop where
  | outside {mode : TokenParser}
      (modeOutside : readerInComment mode = false) :
      CommentModeAgrees false mode
  | inside {inner : TokenParser}
      (innerOutside : readerInComment inner = false) :
      CommentModeAgrees true (.comment inner)

/-- Concatenating adjacent call chronologies preserves every intermediate
mode transition. -/
def CallModeTrace.append
    {initial middle final : TokenParser}
    {left right : List TokenCall}
    (leftTrace : CallModeTrace initial left middle)
    (rightTrace : CallModeTrace middle right final) :
    CallModeTrace initial (left ++ right) final :=
  match leftTrace with
  | .nil _ => rightTrace
  | .cons call beforeEq tail =>
      .cons call beforeEq (tail.append rightTrace)

/-- The structurally complete byte-loop trace carries the exact parser-mode
chronology of all calls it made. -/
noncomputable def FeedTrace.callModeTrace
    {base : Nat} {bytes : ByteArray} {cursor : Nat}
    {scan : ParserState.FeedState} {before final : ParserState}
    {calls : List TokenCall}
    (trace : FeedTrace base bytes cursor scan before final calls) :
    CallModeTrace before.tokp calls final.tokp := by
  induction trace with
  | endWs => exact .nil _
  | endCurrent => exact .nil _
  | endCarried => exact .nil _
  | whitespaceWs cursor before final calls inBounds isSpace rest ih =>
      simpa using ih
  | currentStop cursor start before error previousConsumed
      inBounds isSpace tokenError =>
      refine .cons (currentCall base bytes start cursor before) rfl ?_
      simpa [stopWithConsumed, afterCurrentLine] using
        (CallModeTrace.nil
          (currentCall base bytes start cursor before).after.tokp)
  | currentContinue cursor start before final calls
      inBounds isSpace tokenOk rest ih =>
      refine .cons (currentCall base bytes start cursor before) rfl ?_
      simpa [afterCurrentLine] using ih
  | carriedStop cursor oldBase start oldBytes before error previousConsumed
      inBounds isSpace tokenError =>
      refine .cons
        (carriedCall oldBase oldBytes start base bytes cursor before) rfl ?_
      simpa [stopWithConsumed, afterCarriedLine] using
        (CallModeTrace.nil
          (carriedCall oldBase oldBytes start base bytes cursor before).after.tokp)
  | carriedContinue cursor oldBase start oldBytes before final calls
      inBounds isSpace tokenOk rest ih =>
      refine .cons
        (carriedCall oldBase oldBytes start base bytes cursor before) rfl ?_
      simpa [afterCarriedLine] using ih
  | nonWhitespaceWs cursor before final calls inBounds notSpace rest ih =>
      exact ih
  | nonWhitespaceToken cursor oldToken before final calls
      inBounds notSpace rest ih =>
      exact ih

/-- `feedAll` preserves the same exact call chronology across its possible
carried-token entry state. -/
noncomputable def FeedAllTrace.callModeTrace
    {before final : ParserState} {base : Nat} {bytes : ByteArray}
    {calls : List TokenCall}
    (trace : FeedAllTrace before base bytes final calls) :
    CallModeTrace before.tokp calls final.tokp := by
  cases trace with
  | ws final calls initialChar feed => exact FeedTrace.callModeTrace feed
  | carried oldBase token final calls initialChar feed =>
      simpa using FeedTrace.callModeTrace feed

/-- EOF finalization makes either no call or exactly its recorded trailing
call, so it also supplies a complete mode chronology. -/
noncomputable def DoneTrace.callModeTrace
    {before : ParserState} {eofOffset : Nat} {database : DB}
    {calls : List TokenCall}
    (trace : DoneTrace before eofOffset database calls) :
    Σ finalMode, CallModeTrace before.tokp calls finalMode := by
  cases trace with
  | priorError => exact ⟨before.tokp, .nil _⟩
  | whitespace => exact ⟨before.tokp, .nil _⟩
  | trailingError parserOffset token =>
      let call := trailingCall parserOffset eofOffset token before
      exact ⟨call.after.tokp, .cons call rfl (.nil _)⟩
  | trailingClose parserOffset token =>
      let call := trailingCall parserOffset eofOffset token before
      exact ⟨call.after.tokp, .cons call rfl (.nil _)⟩

/-- The complete production core run therefore determines, rather than
assumes, a call-by-call parser-mode trace from the initial `start` mode. -/
noncomputable def checkBytesCoreLogged_callModeTrace
    (bytes : ByteArray) (config : ModeConfig := {}) :
    Σ finalMode,
      CallModeTrace .start (checkBytesCoreLogged bytes config).calls
        finalMode := by
  let run := checkBytesCoreLogged bytes config
  have feedTrace := FeedAllTrace.callModeTrace run.feedRun.trace
  obtain ⟨finalMode, doneTrace⟩ :=
    DoneTrace.callModeTrace run.doneRun.trace
  refine ⟨finalMode, ?_⟩
  rw [run.calls_eq]
  exact feedTrace.append doneTrace

/-- One call's submitted byte slice is the content of its normalized source
span in the same whole-file buffer. -/
def CallContentAgrees (fileId : String) (bytes : ByteArray)
    (call : TokenCall) : Prop :=
  callBytes call =
    spanBytes bytes.data.toList (normalizedCallSpan fileId call)

/-- A one-shot scanner state contains no carried chunk and, when it contains a
current token, its start precedes the live cursor. -/
def OneShotScanAt (cursor : Nat) : ParserState.FeedState → Prop
  | .ws => True
  | .token (.this start) => start ≤ cursor
  | .token (.old ..) => False

private theorem currentCall_contentAgrees
    (fileId : String) (bytes : ByteArray) (start stop : Nat)
    (before : ParserState) (startLe : start ≤ stop)
    (stopLe : stop ≤ bytes.size) :
    CallContentAgrees fileId bytes
      (currentCall 0 bytes start stop before) := by
  unfold CallContentAgrees callBytes tokenOfCall currentCall
    normalizedCallSpan normalizedOriginSpan
  simp only [Raw.TokenOrigin.token, Nat.zero_add]
  change
    sliceBytes
        (sliceOfSpan bytes
          { fileId := fileId, start := start, stop := stop }) =
      spanBytes bytes.data.toList
        { fileId := fileId, start := start, stop := stop }
  exact sliceBytes_sliceOfSpan ⟨startLe, stopLe⟩

/-- Every call in a one-shot feed trace points into the same byte buffer and
submits exactly the bytes at its normalized span. -/
theorem FeedTrace.callContentsAgree
    {fileId : String} {bytes : ByteArray} {cursor : Nat}
    {scan : ParserState.FeedState} {before final : ParserState}
    {calls : List TokenCall}
    (trace : FeedTrace 0 bytes cursor scan before final calls)
    (oneShot : OneShotScanAt cursor scan) :
    ∀ call ∈ calls, CallContentAgrees fileId bytes call := by
  induction trace with
  | endWs => simp
  | endCurrent => simp
  | endCarried => exact False.elim oneShot
  | whitespaceWs cursor before final calls inBounds isSpace rest ih =>
      exact ih trivial
  | currentStop cursor start before error previousConsumed
      inBounds isSpace tokenError =>
      intro call member
      have callEq : call = currentCall 0 bytes start cursor before := by
        simpa using member
      subst call
      exact currentCall_contentAgrees fileId bytes start cursor before
        oneShot (Nat.le_of_lt inBounds)
  | currentContinue cursor start before final calls
      inBounds isSpace tokenOk rest ih =>
      intro call member
      rcases List.mem_cons.mp member with callEq | tailMember
      · subst call
        exact currentCall_contentAgrees fileId bytes start cursor before
          oneShot (Nat.le_of_lt inBounds)
      · exact ih trivial call tailMember
  | carriedStop => exact False.elim oneShot
  | carriedContinue => exact False.elim oneShot
  | nonWhitespaceWs cursor before final calls inBounds notSpace rest ih =>
      exact ih (Nat.le_succ cursor)
  | nonWhitespaceToken cursor oldToken before final calls
      inBounds notSpace rest ih =>
      cases oldToken with
      | this start =>
          exact ih (Nat.le_trans oneShot (Nat.le_succ cursor))
      | old oldBase start oldBytes => exact False.elim oneShot

/-- The one-shot feed phase's complete call list is physically backed by the
same input buffer. -/
theorem feedAllLogged_callContentsAgree
    (fileId : String) (bytes : ByteArray) (config : ModeConfig := {}) :
    ∀ call ∈ (feedAllLogged (initialState config) 0 bytes).calls,
      CallContentAgrees fileId bytes call := by
  let run := feedAllLogged (initialState config) 0 bytes
  cases run.trace with
  | ws final calls initialChar feed =>
      exact
        Mettapedia.Languages.Metamath.SourceGSLTReaderTraceBinding.FeedTrace.callContentsAgree
          feed trivial
  | carried oldBase token final calls initialChar feed =>
      have initialWhitespace : (initialState config).charp = .ws := rfl
      rw [initialWhitespace] at initialChar
      cases initialChar

private theorem trailingCall_contentAgrees
    (fileId : String) (bytes : ByteArray) (start : Nat)
    (before : ParserState) (startLe : start ≤ bytes.size) :
    CallContentAgrees fileId bytes
      (trailingCall 0 bytes.size (ByteSliceT.mk bytes start) before) := by
  unfold CallContentAgrees callBytes tokenOfCall trailingCall
    normalizedCallSpan normalizedOriginSpan
  simp only [Raw.TokenOrigin.token, Nat.zero_add]
  have startEq : (ByteSliceT.mk bytes start).start = start := by
    simp [ByteSliceT.mk, ByteArray.toByteSlice, startLe]
    rfl
  have sliceEq :
      (ByteSliceT.mk bytes start).toSlice =
        sliceOfSpan bytes
          { fileId := fileId, start := start, stop := bytes.size } := by
    unfold ByteSliceT.mk ByteSliceT.toSlice sliceOfSpan ByteSlice.mk
    simp [ByteArray.toByteSlice, startLe]
  rw [startEq, sliceEq]
  change
    sliceBytes
        (sliceOfSpan bytes
          { fileId := fileId, start := start, stop := bytes.size }) =
      spanBytes bytes.data.toList
        { fileId := fileId, start := start, stop := bytes.size }
  exact sliceBytes_sliceOfSpan ⟨startLe, Nat.le_refl _⟩

/-- Successful EOF finalization's optional trailing call is backed by the
same whole-file buffer. -/
theorem DoneTrace.callContentsAgree
    {fileId : String} {bytes : ByteArray} {before : ParserState}
    {database : DB} {calls : List TokenCall} {mode : ScanMode}
    (trace : DoneTrace before bytes.size database calls)
    (agrees : finalCharpAgrees bytes mode before.charp)
    (modeBound : modeStartBound bytes mode)
    (errorFree : database.error? = none) :
    ∀ call ∈ calls, CallContentAgrees fileId bytes call := by
  cases trace with
  | priorError priorError =>
      have noPriorError : before.db.error = false := by
        simp [DB.error, errorFree]
      rw [noPriorError] at priorError
      cases priorError
  | whitespace noPriorError charpWhitespace => simp
  | trailingError parserOffset token noPriorError charpToken tokenError =>
      have noTokenError :
          (trailingCall parserOffset bytes.size token before).after.db.error =
            false := by
        simp [DB.error, errorFree]
      rw [noTokenError] at tokenError
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
          intro call member
          have callEq :
              call = trailingCall 0 bytes.size (ByteSliceT.mk bytes start)
                before := by
            simpa using member
          subst call
          exact trailingCall_contentAgrees fileId bytes start before modeBound

/-- Every token call in a successful one-shot core run is a physical slice of
the exact input byte array. -/
theorem checkBytesCoreLogged_callContentsAgree
    (fileId : String) (bytes : ByteArray) (config : ModeConfig := {})
    (errorFree : (checkBytesCoreLogged bytes config).db.error? = none) :
    ∀ call ∈ (checkBytesCoreLogged bytes config).calls,
      CallContentAgrees fileId bytes call := by
  let run := checkBytesCoreLogged bytes config
  change run.db.error? = none at errorFree
  change ∀ call ∈ run.calls, CallContentAgrees fileId bytes call
  have doneErrorFree : run.doneRun.db.error? = none := by
    simpa [run.db_eq] using errorFree
  have feedErrorFree : run.feedRun.final.db.error? = none :=
    doneTrace_before_errorFree run.doneRun.trace doneErrorFree
  obtain ⟨finalMode, finalCharp, finalBound, _⟩ :=
    feedAllLogged_normalizedSpans_complete fileId bytes config feedErrorFree
  intro call member
  rw [run.calls_eq] at member
  rcases List.mem_append.mp member with feedMember | doneMember
  · exact feedAllLogged_callContentsAgree fileId bytes config call feedMember
  · exact
      Mettapedia.Languages.Metamath.SourceGSLTReaderTraceBinding.DoneTrace.callContentsAgree
        run.doneRun.trace finalCharp finalBound doneErrorFree call doneMember

/-- Located call data reconstructed from the reader trace. -/
def locatedCall (fileId : String) (call : TokenCall) : LocatedToken :=
  { span := normalizedCallSpan fileId call
    bytes := callBytes call }

/-- Located token data reconstructed from an authored scanner span. -/
def locatedSpan (bytes : ByteArray) (span : LocatedByteSpan) : LocatedToken :=
  { span
    bytes := spanBytes bytes.data.toList span }

/-- Located version of the production reader's existing significant-token
filter.  It erases comment openers and every call made while the parser is
suspended inside a comment, retaining all other occurrences unchanged. -/
def significantLocatedCall? (fileId : String) (call : TokenCall) :
    Option LocatedToken :=
  match call.before.tokp with
  | .comment _ => none
  | _ =>
      if (tokenOfCall call).eqArray "$(".toAscii then none
      else some (locatedCall fileId call)

private theorem significantLocatedCall?_outside_open
    (fileId : String) (call : TokenCall)
    (outside : readerInComment call.before.tokp = false)
    (isOpen : (tokenOfCall call).eqArray "$(".toAscii = true) :
    significantLocatedCall? fileId call = none := by
  cases modeEq : call.before.tokp
  case comment inner => simp [readerInComment, modeEq] at outside
  all_goals simp [significantLocatedCall?, modeEq, isOpen]

private theorem significantLocatedCall?_outside_notOpen
    (fileId : String) (call : TokenCall)
    (outside : readerInComment call.before.tokp = false)
    (notOpen : (tokenOfCall call).eqArray "$(".toAscii ≠ true) :
    significantLocatedCall? fileId call = some (locatedCall fileId call) := by
  cases modeEq : call.before.tokp
  case comment inner => simp [readerInComment, modeEq] at outside
  all_goals simp [significantLocatedCall?, modeEq, notOpen]

@[simp] private theorem significantLocatedCall?_comment
    (fileId : String) (call : TokenCall) (inner : TokenParser)
    (commentMode : call.before.tokp = .comment inner) :
    significantLocatedCall? fileId call = none := by
  simp [significantLocatedCall?, commentMode]

private theorem locatedCall_eq_locatedSpan
    (fileId : String) (bytes : ByteArray) (call : TokenCall)
    (content : CallContentAgrees fileId bytes call) :
    locatedCall fileId call =
      locatedSpan bytes (normalizedCallSpan fileId call) := by
  cases call
  simp [locatedCall, locatedSpan, CallContentAgrees] at content ⊢
  exact content

/-- **Comment-erasure fusion.** Whenever the source comment GSLT accepts the
same located call stream, the production reader's significant-call filter is
exactly its located output.  The proof follows the actual call-mode trace;
no token ledger or reconstructed parser is supplied. -/
theorem CallModeTrace.significantLocatedCalls_eq_stripComments
    {fileId : String} {bytes : ByteArray}
    {initial final : TokenParser} {calls : List TokenCall}
    {sourceMode : Bool} {openSite : LocatedByteSpan}
    {output : List LocatedByteSpan}
    (trace : CallModeTrace initial calls final)
    (modeAgreement : CommentModeAgrees sourceMode initial)
    (contents : ∀ call ∈ calls, CallContentAgrees fileId bytes call)
    (stripped : stripComments bytes.data.toList
      (calls.map (normalizedCallSpan fileId)) sourceMode openSite =
        .ok output) :
    calls.filterMap (significantLocatedCall? fileId) =
      output.map (locatedSpan bytes) := by
  induction trace generalizing sourceMode openSite output with
  | nil mode =>
      cases modeAgreement with
      | outside modeOutside =>
          simp [stripComments] at stripped
          subst output
          rfl
      | inside innerOutside =>
          simp [stripComments] at stripped
  | @cons initial final calls call beforeEq tail inductionHypothesis =>
      have headContent : CallContentAgrees fileId bytes call :=
        contents call (by simp)
      have tailContents :
          ∀ next ∈ calls, CallContentAgrees fileId bytes next := by
        intro next member
        exact contents next (by simp [member])
      simp only [List.map_cons] at stripped
      cases modeAgreement with
      | outside initialOutside =>
          have beforeOutside :
              readerInComment call.before.tokp = false := by
            rw [beforeEq]
            exact initialOutside
          by_cases openBytes : callBytes call = commentOpenBytes
          · have spanOpen :
                spanBytes bytes.data.toList
                    (normalizedCallSpan fileId call) = commentOpenBytes := by
              rw [← headContent]
              exact openBytes
            have tokenOpen :
                (tokenOfCall call).eqArray "$(".toAscii = true :=
              (callCommentOpen_iff call).2 openBytes
            simp only [stripComments, spanOpen, if_true] at stripped
            have afterEq : call.after.tokp = .comment initial := by
              rw [call.after_eq]
              simpa [beforeEq] using
                feedToken_commentOpen call.before
                  call.origin.parserOffset call.origin.token
                  beforeOutside tokenOpen
            have tailMode : CommentModeAgrees true call.after.tokp := by
              rw [afterEq]
              exact .inside initialOutside
            have tailEquality := inductionHypothesis tailMode tailContents stripped
            rw [List.filterMap_cons,
              significantLocatedCall?_outside_open fileId call
                beforeOutside tokenOpen]
            exact tailEquality
          · have spanOpen :
                spanBytes bytes.data.toList
                    (normalizedCallSpan fileId call) ≠ commentOpenBytes := by
              intro equality
              exact openBytes (headContent.trans equality)
            by_cases closeBytes : callBytes call = commentCloseBytes
            · have spanClose :
                  spanBytes bytes.data.toList
                      (normalizedCallSpan fileId call) = commentCloseBytes := by
                rw [← headContent]
                exact closeBytes
              rw [stripComments, if_neg spanOpen, if_pos spanClose] at stripped
              cases stripped
            · have spanClose :
                  spanBytes bytes.data.toList
                      (normalizedCallSpan fileId call) ≠ commentCloseBytes := by
                intro equality
                exact closeBytes (headContent.trans equality)
              rw [stripComments, if_neg spanOpen, if_neg spanClose] at stripped
              cases tailStrip : stripComments bytes.data.toList
                  (calls.map (normalizedCallSpan fileId)) false openSite with
              | rejected rejection =>
                  rw [tailStrip] at stripped
                  cases stripped
              | ok tailOutput =>
                  rw [tailStrip] at stripped
                  cases stripped
                  have tokenNotOpen :
                      (tokenOfCall call).eqArray "$(".toAscii ≠ true := by
                    intro tokenOpen
                    exact openBytes ((callCommentOpen_iff call).1 tokenOpen)
                  have afterOutside :
                      readerInComment call.after.tokp = false := by
                    rw [call.after_eq]
                    exact readerInComment_feedToken_outside_of_notOpen
                      call.before call.origin.parserOffset call.origin.token
                      beforeOutside tokenNotOpen
                  have tailEquality := inductionHypothesis
                    (.outside afterOutside) tailContents tailStrip
                  rw [List.filterMap_cons,
                    significantLocatedCall?_outside_notOpen fileId call
                      beforeOutside tokenNotOpen,
                    tailEquality,
                    locatedCall_eq_locatedSpan fileId bytes call headContent]
                  rfl
      | @inside inner innerOutside =>
          have beforeComment : call.before.tokp = .comment inner := by
            exact beforeEq
          by_cases closeBytes : callBytes call = commentCloseBytes
          · have spanClose :
                spanBytes bytes.data.toList
                    (normalizedCallSpan fileId call) = commentCloseBytes := by
              rw [← headContent]
              exact closeBytes
            have tokenClose :
                (tokenOfCall call).eqArray "$)".toAscii = true :=
              (callCommentClose_iff call).2 closeBytes
            simp only [stripComments, spanClose, if_true] at stripped
            have afterEq : call.after.tokp = inner := by
              rw [call.after_eq]
              exact feedToken_commentClose call.before
                call.origin.parserOffset call.origin.token inner
                beforeComment tokenClose
            have tailMode : CommentModeAgrees false call.after.tokp := by
              rw [afterEq]
              exact .outside innerOutside
            have tailEquality := inductionHypothesis tailMode tailContents stripped
            rw [List.filterMap_cons,
              significantLocatedCall?_comment fileId call inner beforeComment]
            exact tailEquality
          · have spanClose :
                spanBytes bytes.data.toList
                    (normalizedCallSpan fileId call) ≠ commentCloseBytes := by
              intro equality
              exact closeBytes (headContent.trans equality)
            rw [stripComments, if_neg spanClose] at stripped
            by_cases badInterior :
                (spanBytes bytes.data.toList
                    (normalizedCallSpan fileId call) = commentOpenBytes ||
                  containsCommentSeq
                    (spanBytes bytes.data.toList
                      (normalizedCallSpan fileId call)) : Bool)
            · rw [if_pos badInterior] at stripped
              cases stripped
            · rw [if_neg badInterior] at stripped
              have spanNotOpen :
                  spanBytes bytes.data.toList
                      (normalizedCallSpan fileId call) ≠ commentOpenBytes := by
                intro equality
                apply badInterior
                simp [equality]
              have tokenNotClose :
                  (tokenOfCall call).eqArray "$)".toAscii ≠ true := by
                intro tokenClose
                exact closeBytes ((callCommentClose_iff call).1 tokenClose)
              have tokenNotOpen :
                  (tokenOfCall call).eqArray "$(".toAscii ≠ true := by
                intro tokenOpen
                exact spanNotOpen <| by
                  rw [← headContent]
                  exact (callCommentOpen_iff call).1 tokenOpen
              have afterEq : call.after.tokp = .comment inner := by
                rw [call.after_eq]
                exact feedToken_commentInterior call.before
                  call.origin.parserOffset call.origin.token inner
                  beforeComment tokenNotClose tokenNotOpen
              have tailMode : CommentModeAgrees true call.after.tokp := by
                rw [afterEq]
                exact .inside innerOutside
              have tailEquality := inductionHypothesis
                tailMode tailContents stripped
              rw [List.filterMap_cons,
                significantLocatedCall?_comment fileId call inner beforeComment]
              exact tailEquality

/-- The shipped slice-to-string loop is exactly the source composition's
bytewise token text. -/
theorem byteSlice_toString_eq_tokenText (slice : ByteSlice) :
    slice.toString = tokenText (sliceBytes slice) := by
  unfold ByteSlice.toString
  change ByteSlice.forIn (m := Id) slice ""
      (fun c s => pure (ForInStep.yield
        (s.push (Char.ofUInt8 c)))) = _
  rw [byteSlice_forIn_yield slice
    (fun c s => pure (ForInStep.yield (s.push (Char.ofUInt8 c))))
    (fun c s => s.push (Char.ofUInt8 c)) (by intros; rfl) ""]
  rw [← SourceGSLTCompressedMMLean4.sliceBytes_eq_sliceList]
  have characterAgreement : ∀ byte : UInt8,
      Char.ofUInt8 byte = Metamath.Verify.uint8ToChar byte := by
    intro byte
    apply Char.ext
    rfl
  simp_rw [characterAgreement]
  change (sliceBytes slice).foldl
      (fun text byte => text.push (Metamath.Verify.uint8ToChar byte)) "" =
    tokenText (sliceBytes slice)
  simpa using foldl_push_eq_tokenText (sliceBytes slice) ""

/-- Mapping retained located calls to text recovers the production reader's
existing significant-token observation one call at a time. -/
theorem significantLocatedCall?_text
    (fileId : String) (call : TokenCall) :
    (significantLocatedCall? fileId call).map
        (fun token => tokenText token.bytes) =
      significantToken? call := by
  change (significantLocatedCall? fileId call).map
      (fun token => tokenText token.bytes) =
    (match call.before.tokp with
    | .comment _ => none
    | _ =>
        if (tokenOfCall call).eqArray "$(".toAscii then none
        else some (tokenOfCall call).toString)
  cases modeEq : call.before.tokp
  case comment inner =>
    simp [significantLocatedCall?, modeEq]
  all_goals
    by_cases isOpen : (tokenOfCall call).eqArray "$(".toAscii = true
    · simp [significantLocatedCall?, modeEq, isOpen]
    · simp [significantLocatedCall?, modeEq, isOpen,
        locatedCall, callBytes, byteSlice_toString_eq_tokenText]

/-- The same per-call fact commutes over an arbitrary chronological list. -/
theorem significantLocatedCalls_text
    (fileId : String) (calls : List TokenCall) :
    (calls.filterMap (significantLocatedCall? fileId)).map
        (fun token => tokenText token.bytes) =
      calls.filterMap significantToken? := by
  rw [List.map_filterMap]
  apply congrArg (fun selector => calls.filterMap selector)
  funext call
  exact significantLocatedCall?_text fileId call

/-- **Constructed monolithic same-source binding.** If the source comment
GSLT accepts the authored scanner output and the shipped core reader accepts
the same byte array, its retained located calls are exactly that source
output. -/
theorem checkBytesCoreLogged_significantLocatedCalls_eq_stripComments
    (fileId : String) (bytes : ByteArray) (config : ModeConfig := {})
    (errorFree : (checkBytesCoreLogged bytes config).db.error? = none)
    {openSite : LocatedByteSpan} {output : List LocatedByteSpan}
    (stripped : stripComments bytes.data.toList
      (tokenizeIncrementally fileId bytes) false openSite = .ok output) :
    (checkBytesCoreLogged bytes config).calls.filterMap
        (significantLocatedCall? fileId) =
      output.map (locatedSpan bytes) := by
  obtain ⟨finalMode, modeTrace⟩ :=
    checkBytesCoreLogged_callModeTrace bytes config
  have spanEquality := checkBytesCoreLogged_eq_incrementalGSLTScanner
    fileId bytes config errorFree
  rw [← spanEquality] at stripped
  exact modeTrace.significantLocatedCalls_eq_stripComments
    (.outside rfl)
    (checkBytesCoreLogged_callContentsAgree fileId bytes config errorFree)
    stripped

/-- **Exact raw same-buffer binding.** On successful input, the shipped
reader's chronological calls, including comment tokens, are exactly the
located occurrences generated from the authored raw-byte scanner.  Both span
identity and token content are derived; no ordered-token equality is supplied
to this theorem. -/
theorem checkBytesCoreLogged_locatedCalls_eq_incrementalScanner
    (fileId : String) (bytes : ByteArray) (config : ModeConfig := {})
    (errorFree : (checkBytesCoreLogged bytes config).db.error? = none) :
    (checkBytesCoreLogged bytes config).calls.map (locatedCall fileId) =
      (tokenizeIncrementally fileId bytes).map (locatedSpan bytes) := by
  have spans := checkBytesCoreLogged_eq_incrementalGSLTScanner
    fileId bytes config errorFree
  rw [← spans]
  simp only [List.map_map]
  apply List.map_congr_left
  intro call member
  have content := checkBytesCoreLogged_callContentsAgree
    fileId bytes config errorFree call member
  cases call
  simp [locatedCall, locatedSpan, CallContentAgrees] at content ⊢
  exact content

private theorem PublicGateTrace.coreErrorFree
    {core final : DB} (trace : PublicGateTrace core final)
    (finalErrorFree : final.error? = none) :
    core.error? = none := by
  cases trace with
  | priorError priorError => exact False.elim (priorError finalErrorFree)
  | accepted accepted gate => exact accepted
  | rejected accepted gate => exact accepted

private theorem checkBytesLogged_coreRun_eq
    (bytes : ByteArray) (config : ModeConfig := {}) :
    (checkBytesLogged bytes config).coreRun =
      checkBytesCoreLogged bytes config := by
  simp only [checkBytesLogged]
  split
  · split <;> rfl
  · rfl

/-- The public consistency gate preserves the exact raw same-buffer call
sequence; it neither inserts nor removes lexical occurrences. -/
theorem checkBytesLogged_locatedCalls_eq_incrementalScanner
    (fileId : String) (bytes : ByteArray) (config : ModeConfig := {})
    (errorFree : (checkBytesLogged bytes config).db.error? = none) :
    (checkBytesLogged bytes config).calls.map (locatedCall fileId) =
      (tokenizeIncrementally fileId bytes).map (locatedSpan bytes) := by
  rw [checkBytesLogged_calls_eq_core bytes config]
  have coreErrorFree :
      (checkBytesLogged bytes config).coreRun.db.error? = none :=
    Mettapedia.Languages.Metamath.SourceGSLTReaderTraceBinding.PublicGateTrace.coreErrorFree
      (checkBytesLogged bytes config).gateTrace errorFree
  rw [checkBytesLogged_coreRun_eq bytes config] at coreErrorFree ⊢
  exact checkBytesCoreLogged_locatedCalls_eq_incrementalScanner
    fileId bytes config coreErrorFree

/-- The public consistency gate preserves the constructed comment-erased
same-source binding as well as the raw call stream. -/
theorem checkBytesLogged_significantLocatedCalls_eq_stripComments
    (fileId : String) (bytes : ByteArray) (config : ModeConfig := {})
    (errorFree : (checkBytesLogged bytes config).db.error? = none)
    {openSite : LocatedByteSpan} {output : List LocatedByteSpan}
    (stripped : stripComments bytes.data.toList
      (tokenizeIncrementally fileId bytes) false openSite = .ok output) :
    (checkBytesLogged bytes config).calls.filterMap
        (significantLocatedCall? fileId) =
      output.map (locatedSpan bytes) := by
  rw [checkBytesLogged_calls_eq_core bytes config]
  have coreErrorFree :
      (checkBytesLogged bytes config).coreRun.db.error? = none :=
    Mettapedia.Languages.Metamath.SourceGSLTReaderTraceBinding.PublicGateTrace.coreErrorFree
      (checkBytesLogged bytes config).gateTrace errorFree
  rw [checkBytesLogged_coreRun_eq bytes config] at coreErrorFree ⊢
  exact checkBytesCoreLogged_significantLocatedCalls_eq_stripComments
    fileId bytes config coreErrorFree stripped

/-- Textual corollary used by the existing lowering API: the production
reader's significant token ledger is derived from the source comment pass
over the same bytes. -/
theorem loggedSignificantTokens_eq_stripComments
    (fileId : String) (bytes : ByteArray)
    (errorFree : (checkBytesLogged bytes).db.error? = none)
    {openSite : LocatedByteSpan} {output : List LocatedByteSpan}
    (stripped : stripComments bytes.data.toList
      (tokenizeIncrementally fileId bytes) false openSite = .ok output) :
    loggedSignificantTokens bytes =
      output.map (fun span =>
        tokenText (spanBytes bytes.data.toList span)) := by
  have locatedEquality :=
    checkBytesLogged_significantLocatedCalls_eq_stripComments
      fileId bytes {} errorFree stripped
  have textEquality := congrArg
    (List.map fun token : LocatedToken => tokenText token.bytes)
    locatedEquality
  rw [significantLocatedCalls_text] at textEquality
  simpa [loggedSignificantTokens, loggedSignificantCalls,
    significantCall?, List.map_filterMap, Function.comp_def,
    locatedSpan] using textEquality

/-! ## Statement-segmentation text conservation

The source segmenter already retains every consumed span.  For the
same-buffer join we also need the corresponding text statement: the
semantic token image stored by a partially built statement is exactly the
text consumed so far.  This is a state invariant of the existing segmenter,
not a separately authored unparser. -/

/-- Token text already consumed by the currently open statement, in source
order. -/
def pendingTokenStrings : SegMode → List String
  | .top => []
  | .pendingLabel label => [label.name]
  | .collecting kind _ acc =>
      (match kind with
      | .constants => "$c"
      | .variables => "$v"
      | .disjoint => "$d") :: acc.reverse.map (·.name)
  | .floatBody _ label acc =>
      label.name :: "$f" :: acc.reverse.map (·.name)
  | .essentialBody _ label acc =>
      label.name :: "$e" :: acc.reverse.map (·.name)
  | .axiomBody _ label acc =>
      label.name :: "$a" :: acc.reverse.map (·.name)
  | .provableBody _ label acc =>
      label.name :: "$p" :: acc.reverse.map (·.name)
  | .proofDecide _ label formula _ =>
      label.name :: "$p" :: formula.reverse.map (·.name) ++ ["$="]
  | .proofNormal _ label formula _ acc =>
      label.name :: "$p" :: formula.reverse.map (·.name) ++
        "$=" :: acc.reverse.map (·.name)
  | .proofHeader _ label formula _ _ acc =>
      label.name :: "$p" :: formula.reverse.map (·.name) ++
        "$=" :: "(" :: acc.reverse.map (·.name)
  | .proofWords _ label formula _ _ _ header acc =>
      label.name :: "$p" :: formula.reverse.map (·.name) ++
        "$=" :: "(" :: header.map (·.name) ++
          ")" :: acc.reverse.map (fun token => tokenText token.bytes)

private theorem tokenText_constKeywordBytes :
    tokenText constKeywordBytes = "$c" := rfl
private theorem tokenText_varKeywordBytes :
    tokenText varKeywordBytes = "$v" := rfl
private theorem tokenText_djKeywordBytes :
    tokenText djKeywordBytes = "$d" := rfl
private theorem tokenText_floatKeywordBytes :
    tokenText floatKeywordBytes = "$f" := rfl
private theorem tokenText_essentialKeywordBytes :
    tokenText essentialKeywordBytes = "$e" := rfl
private theorem tokenText_axiomKeywordBytes :
    tokenText axiomKeywordBytes = "$a" := rfl
private theorem tokenText_provableKeywordBytes :
    tokenText provableKeywordBytes = "$p" := rfl
private theorem tokenText_proofSeparatorBytes :
    tokenText proofSeparatorBytes = "$=" := rfl
private theorem tokenText_statementEndBytes :
    tokenText SourceGSLTRawSourceComposition.statementEndBytes = "$." := rfl
private theorem tokenText_scopeOpenBytes :
    tokenText SourceGSLTRawSourceComposition.scopeOpenBytes = "${" := rfl
private theorem tokenText_scopeCloseBytes :
    tokenText SourceGSLTRawSourceComposition.scopeCloseBytes = "$}" := rfl
private theorem tokenText_parenOpenBytes :
    tokenText parenOpenBytes = "(" := rfl
private theorem tokenText_parenCloseBytes :
    tokenText parenCloseBytes = ")" := rfl

private theorem splitFormula_tokenStrings_ok
    {site : LocatedByteSpan} {acc : List LocatedName}
    {typecode : LocatedName} {body : List LocatedName}
    (h : splitFormula site acc = .ok (typecode, body)) :
    (acc.map (·.name)).reverse = typecode.name :: body.map (·.name) := by
  have mapped := congrArg (List.map fun name : LocatedName => name.name)
    (splitFormula_ok h)
  simpa using mapped

set_option linter.unusedSimpArgs false in
/-- One accepted segmentation step conserves token text: emitted statement
text followed by the open statement's residual text is exactly the prior
residual followed by the token just consumed. -/
theorem segmentStep_tokenStrings {mode : SegMode} {tok : LocatedToken}
    {emitted : List RawStatement} {next : SegMode}
    (h : segmentStep mode tok = .ok (emitted, next)) :
    emitted.flatMap RawStatement.tokenStrings ++ pendingTokenStrings next =
      pendingTokenStrings mode ++ [tokenText tok.bytes] := by
  cases mode <;> simp only [segmentStep] at h
  all_goals repeat' split at h
  all_goals cases h
  all_goals
    simp_all [pendingTokenStrings, RawStatement.tokenStrings,
      ProofPayload.tokenStrings, LocatedToken.toName,
      tokenText_constKeywordBytes, tokenText_varKeywordBytes,
      tokenText_djKeywordBytes, tokenText_floatKeywordBytes,
      tokenText_essentialKeywordBytes, tokenText_axiomKeywordBytes,
      tokenText_provableKeywordBytes, tokenText_proofSeparatorBytes,
      tokenText_statementEndBytes, tokenText_scopeOpenBytes,
      tokenText_scopeCloseBytes, tokenText_parenOpenBytes,
      tokenText_parenCloseBytes, splitFormula_tokenStrings_ok]
  all_goals
    have splitNames := splitFormula_tokenStrings_ok (by assumption)
    simp [splitNames]

private theorem pendingTokenStrings_of_site_none {mode : SegMode}
    (h : mode.site = none) : pendingTokenStrings mode = [] := by
  cases mode <;> first | rfl | exact nomatch h

/-- Run-level token-text conservation for the existing one-pass statement
segmenter. -/
theorem segmentRun_tokenStrings :
    ∀ (tokens : List LocatedToken) (mode : SegMode)
      (acc statements : List RawStatement),
      segmentRun tokens mode acc = .ok statements →
      statements.flatMap RawStatement.tokenStrings =
        (acc.reverse.flatMap RawStatement.tokenStrings) ++
          (pendingTokenStrings mode ++
            tokens.map (fun token => tokenText token.bytes))
  | [], mode, acc, statements, h => by
      simp only [segmentRun] at h
      cases hsite : mode.site with
      | none =>
          simp only [hsite] at h
          cases h
          simp [pendingTokenStrings_of_site_none hsite]
      | some site =>
          simp only [hsite] at h
          exact nomatch h
  | tok :: rest, mode, acc, statements, h => by
      simp only [segmentRun] at h
      cases hstep : segmentStep mode tok with
      | rejected rejection =>
          simp only [hstep] at h
          exact nomatch h
      | ok pair =>
          obtain ⟨emitted, nextMode⟩ := pair
          simp only [hstep] at h
          have recursive := segmentRun_tokenStrings rest nextMode
            (emitted.reverse ++ acc) statements h
          have stepText := segmentStep_tokenStrings hstep
          have key : emitted.flatMap RawStatement.tokenStrings ++
              (pendingTokenStrings nextMode ++
                rest.map (fun token => tokenText token.bytes)) =
              pendingTokenStrings mode ++
                (tokenText tok.bytes ::
                  rest.map (fun token => tokenText token.bytes)) := by
            rw [← List.append_assoc, stepText, List.append_assoc,
              List.singleton_append]
          rw [recursive]
          simp only [List.reverse_append, List.reverse_reverse,
            List.flatMap_append, List.append_assoc, List.map_cons, key]

/-- Accepted segmentation recovers exactly the input token-text stream. -/
theorem segmentStatements_tokenStrings {tokens : List LocatedToken}
    {statements : List RawStatement}
    (h : segmentStatements tokens = .ok statements) :
    statements.flatMap RawStatement.tokenStrings =
      tokens.map (fun token => tokenText token.bytes) := by
  have conserved := segmentRun_tokenStrings tokens .top [] statements h
  simpa [pendingTokenStrings] using conserved

/-- **Constructed statement-ledger binding.** If the source comment pass and
statement segmenter accept the significant occurrences obtained from one
byte array, the source-owned classified statement stream serializes to the
exact significant-token ledger consumed by the shipped reader.  No token
agreement proposition is supplied. -/
theorem pipelineSource_ledger_eq_loggedSignificantTokens
    (fileId : String) (bytes : ByteArray)
    (errorFree : (checkBytesLogged bytes).db.error? = none)
    {openSite : LocatedByteSpan} {output : List LocatedByteSpan}
    {statements : List RawStatement}
    (stripped : stripComments bytes.data.toList
      (tokenizeIncrementally fileId bytes) false openSite = .ok output)
    (segmented : segmentStatements (output.map (locatedSpan bytes)) =
      .ok statements) :
    (pipelineSource statements).ledger.tokens =
      loggedSignificantTokens bytes := by
  rw [pipelineSource_ledger, segmentStatements_tokenStrings segmented,
    loggedSignificantTokens_eq_stripComments fileId bytes errorFree stripped]
  simp [locatedSpan, Function.comp_def]

/-- The same constructed equality yields the exact typed lowering to the
shipped reader trace. -/
theorem pipelineSource_typedLoweringCertificate
    (fileId : String) (bytes : ByteArray)
    (errorFree : (checkBytesLogged bytes).db.error? = none)
    {openSite : LocatedByteSpan} {output : List LocatedByteSpan}
    {statements : List RawStatement}
    (stripped : stripComments bytes.data.toList
      (tokenizeIncrementally fileId bytes) false openSite = .ok output)
    (segmented : segmentStatements (output.map (locatedSpan bytes)) =
      .ok statements) :
    TypedLoweringCertificate bytes (pipelineSource statements) :=
  typedLoweringCertificate_iff.mpr
    (pipelineSource_ledger_eq_loggedSignificantTokens fileId bytes
      errorFree stripped segmented)

/-! ## Kernel-reduced boundaries -/

private def bindingFixtureBytes : ByteArray :=
  ByteArray.mk #[36, 99, 32, 119, 102, 102, 32, 36, 46]

private def bindingFixtureSpans : List LocatedByteSpan :=
  [⟨"binding-fixture", 0, 2⟩, ⟨"binding-fixture", 3, 6⟩,
    ⟨"binding-fixture", 7, 9⟩]

private def bindingFixtureStatements : List RawStatement :=
  [.constDecl ⟨"binding-fixture", 0, 2⟩
    [⟨⟨"binding-fixture", 3, 6⟩, "wff"⟩]
    ⟨"binding-fixture", 7, 9⟩]

set_option maxRecDepth 100000 in
/-- Positive boundary: the source pipeline constructs a typed lowering for a
small complete database directly from the production reader's byte trace. -/
example (errorFree : (checkBytesLogged bindingFixtureBytes).db.error? = none) :
    TypedLoweringCertificate bindingFixtureBytes
    (pipelineSource bindingFixtureStatements) := by
  apply pipelineSource_typedLoweringCertificate
    "binding-fixture" bindingFixtureBytes
  · exact errorFree
  · show stripComments bindingFixtureBytes.data.toList
        (tokenizeIncrementally "binding-fixture" bindingFixtureBytes)
        false ⟨"binding-fixture", 0, 0⟩ = .ok bindingFixtureSpans
    rfl
  · show segmentStatements
        (bindingFixtureSpans.map (locatedSpan bindingFixtureBytes)) =
          .ok bindingFixtureStatements
    rfl

/-- A source ledger different from the production reader's ledger cannot
carry the exact typed lowering certificate. -/
theorem no_typedLoweringCertificate_of_ledger_ne
    {bytes : ByteArray} {source : ClassifiedSource}
    (different : source.ledger.tokens ≠ loggedSignificantTokens bytes) :
    ¬ TypedLoweringCertificate bytes source := by
  intro certificate
  exact different (typedLoweringCertificate_iff.mp certificate)

private def forgedFixtureSource : ClassifiedSource :=
  { identity := "forged-binding-fixture"
    tokens := [keywordToken "$v"] }

set_option maxRecDepth 100000 in
/-- Negative boundary: changing the source ledger while retaining the same
bytes is rejected by the typed lowering relation. -/
example (errorFree : (checkBytesLogged bindingFixtureBytes).db.error? = none) :
    ¬ TypedLoweringCertificate bindingFixtureBytes
    forgedFixtureSource := by
  intro forgedCertificate
  have forgedEquality :=
    typedLoweringCertificate_iff.mp forgedCertificate
  have sourceEquality := pipelineSource_ledger_eq_loggedSignificantTokens
    "binding-fixture" bindingFixtureBytes errorFree
    (openSite := ⟨"binding-fixture", 0, 0⟩)
    (output := bindingFixtureSpans)
    (statements := bindingFixtureStatements) rfl rfl
  have different : forgedFixtureSource.ledger.tokens ≠
      (pipelineSource bindingFixtureStatements).ledger.tokens := by
    decide
  exact different (forgedEquality.trans sourceEquality.symm)

end Mettapedia.Languages.Metamath.SourceGSLTReaderTraceBinding
