import Mettapedia.Languages.Metamath.InferenceNormalParserTrace

/-!
# Byte-origin ledgers for normal Metamath proofs

This module begins the bridge from the one-shot `checkBytes` parser loop to
`ExactNormalParserTrace`.  The first boundary is theorem ingress: a successful
`$=` delimiter must expose the exact `trimFrame'` result, unchanged
pre-insertion database, and canonical `mkProofState` installed by the live
parser.

The include-aware IO driver and compressed proof actions are separate
obligations. The normal ledger is not sufficient for corpora whose theorems
use compressed proofs. A later whole-input soundness theorem must also require
a `prefixCertified` parser configuration. No theorem in this module infers
erased proof tokens from a final database.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.InferenceNormalByteLedger

open Mettapedia.Languages.Metamath.MMLean4Bridge
open Metamath.Verify
open Metamath.PrefixProvenance (NormalTokensOK)
open Mettapedia.Languages.Metamath.InferenceNormalParserTrace
  (ExactNormalParserTrace)

/-- Successful theorem-token processing exposes the exact trimmed frame and
canonical initial proof state installed by `feedTokens`. -/
theorem feedTokens_thm_success_exact
    (s : ParserState) (formula : RuntimeFormula) (pos : Pos) (label : String)
    (hsuccess :
      (s.feedTokens formula ⟨.thm, pos, label⟩).db.error? = none) :
    ∃ frame,
      s.db.trimFrame' formula = .ok frame ∧
      s.db.interrupt = false ∧
      (s.feedTokens formula ⟨.thm, pos, label⟩).db = s.db ∧
      (s.feedTokens formula ⟨.thm, pos, label⟩).tokp =
        .proof (s.db.mkProofState pos label formula frame) := by
  cases hhead : formula.hasConstHead with
  | false =>
      have hbad :
          (s.feedTokens formula ⟨.thm, pos, label⟩).db.error? ≠ none := by
        simp only [ParserState.feedTokens, hhead]
        apply Metamath.ParserLoopInduction.withAt_preserves_error
        exact
          Metamath.ParserLoopInduction.ParserState_mkErrorFromEvidence_sets_error
            s pos (.scopeDecl .firstSymbolNotConstant)
      exact (hbad hsuccess).elim
  | true =>
      cases htrim : s.db.trimFrame' formula with
      | error error =>
          have hbad :
              (s.feedTokens formula ⟨.thm, pos, label⟩).db.error? ≠ none := by
            simp only [ParserState.feedTokens, hhead, htrim]
            apply Metamath.ParserLoopInduction.withAt_preserves_error
            exact
              Metamath.ParserLoopInduction.ParserState_mkErrorFromEvidence_sets_error
                s pos (.scopeDecl error)
          exact (hbad hsuccess).elim
      | ok frame =>
          cases hinterrupt : s.db.interrupt with
          | false =>
              have hfeedEq :
                  s.feedTokens formula ⟨.thm, pos, label⟩ =
                    ParserState.withAt label (fun _ =>
                      s.resumeThm pos label formula frame) := by
                simp [ParserState.feedTokens, hhead, htrim, hinterrupt]
              have htokp :
                  (s.feedTokens formula ⟨.thm, pos, label⟩).tokp =
                    .proof (s.db.mkProofState pos label formula frame) := by
                simp [ParserState.feedTokens, hhead, htrim, hinterrupt,
                  ParserState.resumeThm, ParserState.withAt_tokp]
              have hdb :
                  (s.feedTokens formula ⟨.thm, pos, label⟩).db = s.db := by
                rw [hfeedEq]
                have ⟨_innerSuccess, hAtDb⟩ :=
                  Metamath.ParserOps.withAt_success_eq label
                    (fun _ => s.resumeThm pos label formula frame) (by
                      simpa [hfeedEq] using hsuccess)
                rw [hAtDb]
                rfl
              exact ⟨frame, rfl, rfl, hdb, htokp⟩
          | true =>
              have hbad :
                  (s.feedTokens formula ⟨.thm, pos, label⟩).db.error? ≠ none := by
                simp only [ParserState.feedTokens, hhead, htrim, hinterrupt]
                apply Metamath.ParserLoopInduction.withAt_preserves_error
                simp [ParserState.withDB]
              exact (hbad hsuccess).elim

/-- The live `$=` `feedToken` event exposes the same exact trimming and
proof-state equations as its `feedTokens` branch. -/
theorem feedToken_math_thm_delim_exact
    (s : ParserState) (offset : Nat) (token : ByteSlice)
    (formula : RuntimeFormula) (pos : Pos) (label : String)
    (hparser : s.tokp = .math formula ⟨.thm, pos, label⟩)
    (hnotComment : token.eqArray "$(".toAscii = false)
    (hnotInclude : token.eqArray "$[".toAscii = false)
    (hdelimiter : token.eqArray TokensKind.thm.delim = true)
    (hsuccess : (s.feedToken offset token).db.error? = none) :
    ∃ frame,
      s.db.trimFrame' formula = .ok frame ∧
      s.db.interrupt = false ∧
      (s.feedToken offset token).db = s.db ∧
      (s.feedToken offset token).tokp =
        .proof (s.db.mkProofState pos label formula frame) := by
  have hfeedSuccess :
      (s.feedTokens formula ⟨.thm, pos, label⟩).db.error? = none := by
    simpa [ParserState.feedToken, hparser, hnotComment, hnotInclude,
      hdelimiter] using hsuccess
  obtain ⟨frame, htrim, hinterrupt, hdb, hproof⟩ :=
    feedTokens_thm_success_exact s formula pos label hfeedSuccess
  refine ⟨frame, htrim, hinterrupt, ?_, ?_⟩
  · simpa [ParserState.feedToken, hparser, hnotComment, hnotInclude,
      hdelimiter] using hdb
  · simpa [ParserState.feedToken, hparser, hnotComment, hnotInclude,
      hdelimiter] using hproof

/-- The post-delimiter parser state itself is a valid proof-ledger anchor: its
database has the same trimming result and its token parser contains the
canonical proof state built from that database. -/
theorem feedToken_math_thm_delim_anchor_exact
    (s : ParserState) (offset : Nat) (token : ByteSlice)
    (formula : RuntimeFormula) (pos : Pos) (label : String)
    (hparser : s.tokp = .math formula ⟨.thm, pos, label⟩)
    (hnotComment : token.eqArray "$(".toAscii = false)
    (hnotInclude : token.eqArray "$[".toAscii = false)
    (hdelimiter : token.eqArray TokensKind.thm.delim = true)
    (hsuccess : (s.feedToken offset token).db.error? = none) :
    ∃ frame,
      (s.feedToken offset token).db.trimFrame' formula = .ok frame ∧
      (s.feedToken offset token).tokp =
        .proof ((s.feedToken offset token).db.mkProofState
          pos label formula frame) ∧
      (s.feedToken offset token).db = s.db := by
  obtain ⟨frame, htrim, _hinterrupt, hdb, hproof⟩ :=
    feedToken_math_thm_delim_exact s offset token formula pos label
      hparser hnotComment hnotInclude hdelimiter hsuccess
  refine ⟨frame, ?_, ?_, hdb⟩
  · rw [hdb]
    exact htrim
  · simpa [hdb] using hproof

/-- Negative calibration: a theorem delimiter whose frame trimming fails
cannot be a successful parser event. -/
theorem feedToken_math_thm_delim_rejects_trim_error
    (s : ParserState) (offset : Nat) (token : ByteSlice)
    (formula : RuntimeFormula) (pos : Pos) (label : String)
    (error : ScopeDeclError)
    (hparser : s.tokp = .math formula ⟨.thm, pos, label⟩)
    (hnotComment : token.eqArray "$(".toAscii = false)
    (hnotInclude : token.eqArray "$[".toAscii = false)
    (hdelimiter : token.eqArray TokensKind.thm.delim = true)
    (htrim : s.db.trimFrame' formula = .error error) :
    (s.feedToken offset token).db.error? ≠ none := by
  intro hsuccess
  obtain ⟨frame, hframe, _hinterrupt, _hdb, _hproof⟩ :=
    feedToken_math_thm_delim_exact s offset token formula pos label
      hparser hnotComment hnotInclude hdelimiter hsuccess
  rw [htrim] at hframe
  contradiction

/-! ## Proof-relevant local ledger -/

/-- One exact successful transition after normal proof mode has begun. -/
structure NormalTokenStep
    (anchor : ParserState) (before : RuntimeProofState)
    (token : ByteSlice) (after : RuntimeProofState) : Type where
  success : (anchor.feedProof token before).db.error? = none
  result : (anchor.feedProof token before).tokp = .proof after
  before_normal : before.ptp = .normal
  token_not_unknown : ¬ token.eqArray "?".toAscii

/-- Every retained normal-token step remains in normal proof mode. -/
theorem NormalTokenStep.after_normal
    {anchor : ParserState} {before after : RuntimeProofState}
    {token : ByteSlice}
    (step : NormalTokenStep anchor before token after) :
    after.ptp = .normal := by
  have executed :=
    Mettapedia.Languages.Metamath.InferenceNormalParserTrace.normalFeedProof_extracts_step
      anchor token before after step.success step.result step.before_normal
        step.token_not_unknown
  exact (Metamath.PrefixProvenance.stepNormal_preserves_ptp
    anchor.db before after (toLabel token).2 executed).trans
      step.before_normal

/-- The first ordinary proof label changes the canonical proof state from
`.start` to `.normal`.  This is the first-token counterpart of
`NormalTokenStep.after_normal`. -/
theorem feedProof_first_normal_after_normal
    (anchor : ParserState) (token : ByteSlice)
    (before after : RuntimeProofState)
    (success : (anchor.feedProof token before).db.error? = none)
    (result : (anchor.feedProof token before).tokp = .proof after)
    (before_start : before.ptp = .start)
    (token_not_open : ¬ token.eqArray "(".toAscii)
    (token_not_unknown : ¬ token.eqArray "?".toAscii) :
    after.ptp = .normal := by
  obtain ⟨actual, go_ok, actual_result⟩ :=
    Metamath.PrefixTraceCompressed.feedProof_success_go_ok
      anchor token before success
  have actual_eq : after = actual := by
    rw [result] at actual_result
    exact TokenParser.proof.inj actual_result
  subst actual
  have go_normal :
      ParserState.feedProof.goNormal anchor token
        {before with ptp := .normal} = .ok after := by
    unfold ParserState.feedProof.go at go_ok
    simpa [before_start, token_not_open] using go_ok
  have executed :=
    Metamath.PrefixProvenance.goNormal_extracts_stepNormal
      anchor token {before with ptp := .normal} after go_normal
        token_not_unknown
  exact (Metamath.PrefixProvenance.stepNormal_preserves_ptp
    anchor.db {before with ptp := .normal} after (toLabel token).2
      executed).trans rfl

/-- Exact successful normal-token transitions in source order. Unlike the
propositional `NormalTokensOK`, this family retains each token and intermediate
proof state as constructor data. -/
inductive NormalTokenSteps (anchor : ParserState) :
    RuntimeProofState → List ByteSlice → RuntimeProofState → Type where
  | nil (state : RuntimeProofState) : NormalTokenSteps anchor state [] state
  | cons {before final : RuntimeProofState} {rest : List ByteSlice}
      (token : ByteSlice) (middle : RuntimeProofState)
      (head : NormalTokenStep anchor before token middle)
      (tail : NormalTokenSteps anchor middle rest final) :
      NormalTokenSteps anchor before (token :: rest) final

/-- Erase proof-relevant steps to the established parser invariant. -/
def NormalTokenSteps.toNormalTokensOK
    {s : ParserState} {initial final : RuntimeProofState}
    {tokens : List ByteSlice} :
    NormalTokenSteps s initial tokens final → NormalTokensOK s initial tokens final
  | .nil _ => rfl
  | .cons token middle head tail =>
      ⟨middle, head.success, head.result, head.before_normal,
        head.token_not_unknown, tail.toNormalTokensOK⟩

/-- A single successful transition as a one-token ledger. -/
def NormalTokenSteps.one
    {s : ParserState} {initial final : RuntimeProofState}
    (token : ByteSlice)
    (step : NormalTokenStep s initial token final) :
    NormalTokenSteps s initial [token] final :=
  .cons token final step (.nil final)

/-- The proof transition computation depends on the parser state only through
its database. This permits byte-traversal states to share one fixed
pre-insertion proof anchor without equating their line or token-parser fields. -/
theorem feedProof_go_eq_of_db_eq
    (left right : ParserState) (token : ByteSlice)
    (before : RuntimeProofState) (hdb : left.db = right.db) :
    ParserState.feedProof.go left token before =
      ParserState.feedProof.go right token before := by
  unfold ParserState.feedProof.go ParserState.feedProof.goNormal
  rw [hdb]

/-- Successful proof observations can be replayed against any parser state
with the same database. Only the database is rebased; no equality of line,
character-parser, or token-parser state is asserted. -/
theorem feedProof_success_result_rebase
    (left right : ParserState) (token : ByteSlice)
    (before after : RuntimeProofState) (hdb : left.db = right.db)
    (success : (left.feedProof token before).db.error? = none)
    (result : (left.feedProof token before).tokp = .proof after) :
    (right.feedProof token before).db.error? = none ∧
      (right.feedProof token before).tokp = .proof after := by
  obtain ⟨actual, hgoLeft, hactual⟩ :=
    Metamath.PrefixTraceCompressed.feedProof_success_go_ok
      left token before success
  have hafter : after = actual := by
    rw [result] at hactual
    exact TokenParser.proof.inj hactual
  subst actual
  have hgoRight : ParserState.feedProof.go right token before = .ok after := by
    rw [← feedProof_go_eq_of_db_eq left right token before hdb]
    exact hgoLeft
  have hleftDb :=
    Metamath.ParserOps.feedProof_success_db left token before success
  have hleftNoError : left.db.error? = none := by
    rw [← hleftDb]
    exact success
  have hrightNoError : right.db.error? = none := by
    rw [← hdb]
    exact hleftNoError
  constructor
  · unfold ParserState.feedProof
    simp [hgoRight, ParserState.withAt, hrightNoError]
  · unfold ParserState.feedProof
    simp [hgoRight, ParserState.withAt_tokp]

/-- The database projection of `withAt` depends only on the inner database. -/
theorem withAt_db_eq_of_inner_db_eq
    (label : String) (left right : Unit → ParserState)
    (hdb : (left ()).db = (right ()).db) :
    (ParserState.withAt label left).db =
      (ParserState.withAt label right).db := by
  rcases hleft : left () with ⟨leftDB, leftTokp, leftCharp,
    leftLine, leftLinePos, leftSource⟩
  rcases hright : right () with ⟨rightDB, rightTokp, rightCharp,
    rightLine, rightLinePos, rightSource⟩
  simp only [hleft, hright] at hdb
  subst rightDB
  cases herror : leftDB.error? with
  | none =>
      simp [ParserState.withAt, hleft, hright, herror]
  | some error =>
      rcases error with ⟨error, index⟩
      cases error <;>
        simp [ParserState.withAt, hleft, hright, herror,
          ParserState.withDB]

/-- Parser error construction has equal database projections when its input
databases are equal. -/
theorem mkErrorFromEvidence_db_eq_of_db_eq
    (left right : ParserState) (pos : Pos) (evidence : ErrorEvidence)
    (hdb : left.db = right.db) :
    (left.mkErrorFromEvidence pos evidence).db =
      (right.mkErrorFromEvidence pos evidence).db := by
  simp [ParserState.mkErrorFromEvidence, ParserState.withDB, hdb]

/-- Final proof checking has the same database result when rebased between
parser states with equal databases. -/
theorem finishProof_db_eq_of_db_eq
    (left right : ParserState) (proof : RuntimeProofState)
    (hdb : left.db = right.db) :
    (left.finishProof proof).db = (right.finishProof proof).db := by
  rcases proof with ⟨pos, label, formula, frame, heap, stack, mode⟩
  unfold ParserState.finishProof
  apply withAt_db_eq_of_inner_db_eq
  cases mode with
  | start =>
      exact mkErrorFromEvidence_db_eq_of_db_eq
        { left with tokp := .start } { right with tokp := .start }
        pos (.proofCheck .proofParseError) hdb
  | preload =>
      exact mkErrorFromEvidence_db_eq_of_db_eq
        { left with tokp := .start } { right with tokp := .start }
        pos (.proofCheck .proofParseError) hdb
  | normal =>
      simp only [Id.run]
      split
      · split
        · simp [hdb, ParserState.withDB]
        · exact mkErrorFromEvidence_db_eq_of_db_eq
            { left with tokp := .start } { right with tokp := .start }
            pos (.theoremFinality
              (.theoremClaimMismatch formula stack[0]!)) hdb
      · exact mkErrorFromEvidence_db_eq_of_db_eq
          { left with tokp := .start } { right with tokp := .start }
          pos (.theoremFinality
            (.theoremMoreThanOneStackElement stack.size)) hdb
  | compressed count =>
      cases count with
      | zero =>
          simp only [Id.run]
          split
          · split
            · simp [hdb, ParserState.withDB]
            · exact mkErrorFromEvidence_db_eq_of_db_eq
                { left with tokp := .start } { right with tokp := .start }
                pos (.theoremFinality
                  (.theoremClaimMismatch formula stack[0]!)) hdb
          · exact mkErrorFromEvidence_db_eq_of_db_eq
              { left with tokp := .start } { right with tokp := .start }
              pos (.theoremFinality
                (.theoremMoreThanOneStackElement stack.size)) hdb
      | succ count =>
          exact mkErrorFromEvidence_db_eq_of_db_eq
            { left with tokp := .start } { right with tokp := .start }
            pos (.proofCheck .proofParseError) hdb

/-- In particular, successful final proof checking transfers to a fixed
pre-insertion anchor with the same database. -/
theorem finishProof_success_rebase
    (left right : ParserState) (proof : RuntimeProofState)
    (hdb : left.db = right.db)
    (success : (left.finishProof proof).db.error? = none) :
    (right.finishProof proof).db.error? = none := by
  rw [← finishProof_db_eq_of_db_eq left right proof hdb]
  exact success

/-- In proof mode, an ordinary token is passed exactly to `feedProof` after
the live token-parser field is cleared. -/
theorem feedToken_proof_step_exact
    (live : ParserState) (offset : Nat) (token : ByteSlice)
    (before : RuntimeProofState)
    (hparser : live.tokp = .proof before)
    (notComment : token.eqArray "$(".toAscii = false)
    (notInclude : token.eqArray "$[".toAscii = false)
    (notFinish : token.eqArray "$.".toAscii = false) :
    live.feedToken offset token =
      ({ live with tokp := default }.feedProof token before) := by
  simp [ParserState.feedToken, hparser, notComment, notInclude, notFinish]

/-- An observed live proof-token transition becomes a fixed-anchor normal
step when the live and anchor databases agree. -/
def NormalTokenStep.ofFeedToken
    (anchor live : ParserState) (offset : Nat) (token : ByteSlice)
    (before after : RuntimeProofState)
    (hdb : live.db = anchor.db)
    (hparser : live.tokp = .proof before)
    (notComment : token.eqArray "$(".toAscii = false)
    (notInclude : token.eqArray "$[".toAscii = false)
    (notFinish : token.eqArray "$.".toAscii = false)
    (success : (live.feedToken offset token).db.error? = none)
    (result : (live.feedToken offset token).tokp = .proof after)
    (beforeNormal : before.ptp = .normal)
    (notUnknown : ¬ token.eqArray "?".toAscii) :
    NormalTokenStep anchor before token after := by
  let cleared : ParserState := { live with tokp := default }
  have hclearedDB : cleared.db = anchor.db := by
    simpa [cleared] using hdb
  have hexact := feedToken_proof_step_exact live offset token before
    hparser notComment notInclude notFinish
  have hfeedSuccess : (cleared.feedProof token before).db.error? = none := by
    rw [← hexact]
    exact success
  have hfeedResult :
      (cleared.feedProof token before).tokp = .proof after := by
    rw [← hexact]
    exact result
  have hrebase := feedProof_success_result_rebase cleared anchor token
    before after hclearedDB hfeedSuccess hfeedResult
  exact
    { success := hrebase.1
      result := hrebase.2
      before_normal := beforeNormal
      token_not_unknown := notUnknown }

/-- In proof mode, the `$.' token is passed exactly to `finishProof` after the
live token-parser field is cleared. -/
theorem feedToken_proof_finish_exact
    (live : ParserState) (offset : Nat) (token : ByteSlice)
    (proof : RuntimeProofState)
    (hparser : live.tokp = .proof proof)
    (notComment : token.eqArray "$(".toAscii = false)
    (notInclude : token.eqArray "$[".toAscii = false)
    (isFinish : token.eqArray "$.".toAscii = true) :
    live.feedToken offset token =
      ({ live with tokp := default }.finishProof proof) := by
  simp [ParserState.feedToken, hparser, notComment, notInclude, isFinish]

/-- A successful live `$.' event transfers both final-check success and the
exact post-insertion database to the fixed pre-insertion anchor. -/
theorem feedToken_proof_finish_rebase
    (anchor live : ParserState) (offset : Nat) (token : ByteSlice)
    (proof : RuntimeProofState)
    (hdb : live.db = anchor.db)
    (hparser : live.tokp = .proof proof)
    (notComment : token.eqArray "$(".toAscii = false)
    (notInclude : token.eqArray "$[".toAscii = false)
    (isFinish : token.eqArray "$.".toAscii = true)
    (success : (live.feedToken offset token).db.error? = none) :
    (anchor.finishProof proof).db.error? = none ∧
      (live.feedToken offset token).db = (anchor.finishProof proof).db := by
  let cleared : ParserState := { live with tokp := default }
  have hclearedDB : cleared.db = anchor.db := by
    simpa [cleared] using hdb
  have hexact := feedToken_proof_finish_exact live offset token proof
    hparser notComment notInclude isFinish
  have hfinishSuccess : (cleared.finishProof proof).db.error? = none := by
    rw [← hexact]
    exact success
  constructor
  · exact finishProof_success_rebase cleared anchor proof
      hclearedDB hfinishSuccess
  · rw [hexact]
    exact finishProof_db_eq_of_db_eq cleared anchor proof hclearedDB

/-- Extend a ledger on the right, so the newly observed token remains last. -/
def NormalTokenSteps.snoc
    {s : ParserState} {initial middle final : RuntimeProofState}
    {tokens : List ByteSlice} {token : ByteSlice}
    (before : NormalTokenSteps s initial tokens middle)
    (last : NormalTokenStep s middle token final) :
    NormalTokenSteps s initial (tokens ++ [token]) final :=
  match before with
  | .nil _ => .cons token final last (.nil final)
  | .cons headToken next head tail =>
      .cons headToken next head (tail.snoc last)

/-- A nonempty normal proof ledger anchored to the pre-insertion parser state.
All source-order and target data are ordinary fields so heterogeneous theorem
events can be retained together by a whole-input traversal. -/
structure NormalTokenLedger : Type where
  anchor : ParserState
  pos : Pos
  targetLabel : String
  targetFormula : RuntimeFormula
  targetFrame : RuntimeFrame
  trim_origin : anchor.db.trimFrame' targetFormula = .ok targetFrame
  firstToken : ByteSlice
  afterFirst : RuntimeProofState
  first_success :
    (anchor.feedProof firstToken
      (anchor.db.mkProofState pos targetLabel targetFormula targetFrame)).db.error? = none
  first_not_open : ¬ firstToken.eqArray "(".toAscii
  first_not_unknown : ¬ firstToken.eqArray "?".toAscii
  first_result :
    (anchor.feedProof firstToken
      (anchor.db.mkProofState pos targetLabel targetFormula targetFrame)).tokp =
        .proof afterFirst
  remainingTokens : List ByteSlice
  final : RuntimeProofState
  remaining : NormalTokenSteps anchor afterFirst remainingTokens final

/-- The initial proof state is computed from retained parser data. -/
def NormalTokenLedger.initial (ledger : NormalTokenLedger) : RuntimeProofState :=
  ledger.anchor.db.mkProofState ledger.pos ledger.targetLabel
    ledger.targetFormula ledger.targetFrame

/-- Start a ledger with the first normal proof token. -/
def NormalTokenLedger.start
    (anchor : ParserState) (pos : Pos) (targetLabel : String)
    (targetFormula : RuntimeFormula) (targetFrame : RuntimeFrame)
    (firstToken : ByteSlice) (afterFirst : RuntimeProofState)
    (trimOrigin : anchor.db.trimFrame' targetFormula = .ok targetFrame)
    (firstSuccess :
      (anchor.feedProof firstToken
        (anchor.db.mkProofState pos targetLabel targetFormula targetFrame)).db.error? = none)
    (firstNotOpen : ¬ firstToken.eqArray "(".toAscii)
    (firstNotUnknown : ¬ firstToken.eqArray "?".toAscii)
    (firstResult :
      (anchor.feedProof firstToken
        (anchor.db.mkProofState pos targetLabel targetFormula targetFrame)).tokp =
          .proof afterFirst) : NormalTokenLedger where
  anchor := anchor
  pos := pos
  targetLabel := targetLabel
  targetFormula := targetFormula
  targetFrame := targetFrame
  trim_origin := trimOrigin
  firstToken := firstToken
  afterFirst := afterFirst
  first_success := firstSuccess
  first_not_open := firstNotOpen
  first_not_unknown := firstNotUnknown
  first_result := firstResult
  remainingTokens := []
  final := afterFirst
  remaining := .nil afterFirst

/-- A successful first normal token determines and retains its intermediate
proof state without accepting that state as an independent input. -/
def NormalTokenLedger.startOfSuccess
    (anchor : ParserState) (pos : Pos) (targetLabel : String)
    (targetFormula : RuntimeFormula) (targetFrame : RuntimeFrame)
    (firstToken : ByteSlice)
    (trimOrigin : anchor.db.trimFrame' targetFormula = .ok targetFrame)
    (firstSuccess :
      (anchor.feedProof firstToken
        (anchor.db.mkProofState pos targetLabel targetFormula targetFrame)).db.error? = none)
    (firstNotOpen : ¬ firstToken.eqArray "(".toAscii)
    (firstNotUnknown : ¬ firstToken.eqArray "?".toAscii) :
    NormalTokenLedger := by
  cases hgo : ParserState.feedProof.go anchor firstToken
      (anchor.db.mkProofState pos targetLabel targetFormula targetFrame) with
  | error error =>
      have hbad :
          (anchor.feedProof firstToken
            (anchor.db.mkProofState pos targetLabel targetFormula targetFrame)).db.error? ≠
              none := by
        unfold ParserState.feedProof
        simp only [hgo]
        apply Metamath.ParserLoopInduction.withAt_preserves_error
        exact
          Metamath.ParserLoopInduction.ParserState_mkErrorFromEvidence_sets_error
            anchor pos error.evidence
      exact (hbad firstSuccess).elim
  | ok afterFirst =>
      have hresult :
          (anchor.feedProof firstToken
            (anchor.db.mkProofState pos targetLabel targetFormula targetFrame)).tokp =
              .proof afterFirst := by
        unfold ParserState.feedProof
        simp [hgo, ParserState.withAt_tokp]
      exact .start anchor pos targetLabel targetFormula targetFrame firstToken
        afterFirst trimOrigin firstSuccess firstNotOpen firstNotUnknown hresult

/-- Execute and retain the first normal token, deriving the target frame from
the anchor database. Failure, compressed entry, and unknown entry return
`none` rather than manufacturing evidence. -/
def NormalTokenLedger.tryStart
    (anchor : ParserState) (pos : Pos) (targetLabel : String)
    (targetFormula : RuntimeFormula) (firstToken : ByteSlice) :
    Option NormalTokenLedger :=
  match htrim : anchor.db.trimFrame' targetFormula with
  | .error _ => none
  | .ok targetFrame =>
      if firstOpen : firstToken.eqArray "(".toAscii then
        none
      else if firstUnknown : firstToken.eqArray "?".toAscii then
        none
      else
        let initial :=
          anchor.db.mkProofState pos targetLabel targetFormula targetFrame
        let observed := anchor.feedProof firstToken initial
        match herror : observed.db.error? with
        | some _ => none
        | none =>
            match hresult : observed.tokp with
            | .proof afterFirst =>
                some (.start anchor pos targetLabel targetFormula targetFrame
                  firstToken afterFirst htrim
                  (by simpa [observed, initial] using herror)
                  (by simpa using firstOpen)
                  (by simpa using firstUnknown)
                  (by simpa [observed, initial] using hresult))
            | _ => none

/-- Extend the remaining proof-token ledger in exact observation order. -/
def NormalTokenLedger.snoc
    (ledger : NormalTokenLedger) (token : ByteSlice)
    (final : RuntimeProofState)
    (last : NormalTokenStep ledger.anchor ledger.final token final) :
    NormalTokenLedger where
  anchor := ledger.anchor
  pos := ledger.pos
  targetLabel := ledger.targetLabel
  targetFormula := ledger.targetFormula
  targetFrame := ledger.targetFrame
  trim_origin := ledger.trim_origin
  firstToken := ledger.firstToken
  afterFirst := ledger.afterFirst
  first_success := ledger.first_success
  first_not_open := ledger.first_not_open
  first_not_unknown := ledger.first_not_unknown
  first_result := ledger.first_result
  remainingTokens := ledger.remainingTokens ++ [token]
  final := final
  remaining := ledger.remaining.snoc last

/-- Execute and retain one additional normal token at the right edge of a
ledger. -/
def NormalTokenLedger.trySnoc
    (ledger : NormalTokenLedger) (token : ByteSlice) :
    Option NormalTokenLedger :=
  match hnormal : ledger.final.ptp with
  | .normal =>
      if hunknown : token.eqArray "?".toAscii then
        none
      else
        let observed := ledger.anchor.feedProof token ledger.final
        match herror : observed.db.error? with
        | some _ => none
        | none =>
            match hresult : observed.tokp with
            | .proof final =>
                let last : NormalTokenStep ledger.anchor ledger.final token final :=
                  { success := by simpa [observed] using herror
                    result := by simpa [observed] using hresult
                    before_normal := hnormal
                    token_not_unknown := by simpa using hunknown }
                some (ledger.snoc token final last)
            | _ => none
  | _ => none

/-- Forget only the Type-level packaging, preserving the exact canonical
initial state and exact submitted token sequence. -/
def NormalTokenLedger.toExactNormalParserTrace (ledger : NormalTokenLedger) :
    ExactNormalParserTrace ledger.anchor ledger.pos ledger.targetLabel
      ledger.targetFormula ledger.targetFrame ledger.firstToken
      ledger.remainingTokens ledger.initial ledger.afterFirst ledger.final where
  initial_eq := rfl
  first_success := by simpa [NormalTokenLedger.initial] using ledger.first_success
  first_not_open := ledger.first_not_open
  first_not_unknown := ledger.first_not_unknown
  first_result := by simpa [NormalTokenLedger.initial] using ledger.first_result
  remaining := ledger.remaining.toNormalTokensOK

/-- A ledger fixes its trimmed target frame uniquely. -/
theorem NormalTokenLedger.targetFrame_eq_of_trim_origin
    (ledger : NormalTokenLedger) (otherFrame : RuntimeFrame)
    (otherOrigin : ledger.anchor.db.trimFrame' ledger.targetFormula = .ok otherFrame) :
    ledger.targetFrame = otherFrame := by
  rw [ledger.trim_origin] at otherOrigin
  exact Except.ok.inj otherOrigin

/-- Negative calibration: a ledger cannot carry a frame contradicting its live
trimming equation. -/
theorem NormalTokenLedger.excludes_wrong_trim
    (ledger : NormalTokenLedger)
    (wrong : ledger.anchor.db.trimFrame' ledger.targetFormula ≠
      .ok ledger.targetFrame) : False :=
  wrong ledger.trim_origin

/-- Negative calibration: compressed proof entry cannot inhabit the normal
ledger's first-token boundary. -/
theorem NormalTokenLedger.excludes_compressed_first
    (ledger : NormalTokenLedger)
    (isOpen : ledger.firstToken.eqArray "(".toAscii) : False :=
  ledger.first_not_open isOpen

end Mettapedia.Languages.Metamath.InferenceNormalByteLedger
