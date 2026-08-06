import Mettapedia.Languages.Metamath.MMLean4Bridge

/-!
# Exact byte-loop event logging for the pure Metamath checker

This module instruments the existing `ParserState.feed`, `feedAll`, and `done`
control flow without replacing `feedToken`.  Each logged call retains the live
parser states immediately before and after that exact `feedToken` invocation.
Erasure theorems identify the instrumented results with the uninstrumented
checker on successful and failing inputs alike.

The generic log distinguishes tokens completed in the current chunk, tokens
carried from an earlier chunk, and the final token flushed by `done`.  A
trailing event records the parser offset actually used by `done`; it does not
claim that this offset is the physical start of the token.  This module does
not assert a physical source-span theorem.  Such a theorem can be stated for
the one-shot `checkBytesCore` route, whose initial character parser is `.ws`
and whose single `feedAll` call starts at byte offset zero.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.InferenceOneShotByteLog.Raw

open Metamath.Verify

/-! ## Exact token-call data -/

/-- The three call sites at which the byte loop can submit a token.

The fields are the raw data used by the corresponding branch.  In particular,
the carried-token constructor retains both chunk bases and both backing byte
arrays; it does not assume that arbitrary callers supplied contiguous chunks.
-/
inductive TokenOrigin where
  | current (base : Nat) (bytes : ByteArray) (start stop : Nat)
  | carried (oldBase : Nat) (oldBytes : ByteArray) (start : Nat)
      (base : Nat) (bytes : ByteArray) (stop : Nat)
  | trailing (parserOffset eofOffset : Nat) (token : ByteSliceT)

/-- The exact natural-number argument passed to `feedToken`. -/
def TokenOrigin.parserOffset : TokenOrigin → Nat
  | .current base _ start _ => base + start
  | .carried oldBase _ start _ _ _ => oldBase + start
  | .trailing parserOffset _ _ => parserOffset

/-- The exact byte slice passed to `feedToken`. -/
def TokenOrigin.token : TokenOrigin → ByteSlice
  | .current _ bytes start stop =>
      ByteSlice.mk bytes start (stop - start)
  | .carried _ oldBytes start _ bytes stop =>
      ByteSlice.mk
        (bytes.copySlice 0 oldBytes oldBytes.size stop false)
        start (oldBytes.size - start + stop)
  | .trailing _ _ token => token.toSlice

/-- Whether a call came from a token carried between chunks. -/
def TokenOrigin.isCarried : TokenOrigin → Bool
  | .carried .. => true
  | _ => false

/-- Whether a call was the final flush performed by `done`. -/
def TokenOrigin.isTrailing : TokenOrigin → Bool
  | .trailing .. => true
  | _ => false

/-- One actual invocation of `ParserState.feedToken`.

`after` is the raw result of the token call.  It intentionally precedes the
byte loop's subsequent line update and consumed-byte error rewrite.
-/
structure TokenCall : Type where
  origin : TokenOrigin
  before : ParserState
  after : ParserState
  after_eq : after = before.feedToken origin.parserOffset origin.token

/-- Result of the instrumented recursive byte loop. -/
structure FeedRun : Type where
  state : ParserState
  calls : List TokenCall

/-! ## Instrumented `feed` and `feedAll` -/

/-- Branch-for-branch instrumentation of `ParserState.feed`.

Calls are stored in execution order.  On a token error, the final state keeps
the checker's exact `i + 1` consumed-byte marker rather than an absolute source
offset.
-/
def feedLogged (base : Nat) (bytes : ByteArray) (i : Nat)
    (scan : ParserState.FeedState) (state : ParserState) : FeedRun :=
  if _h : i < bytes.size then
    let c := bytes[i]
    if isWhitespace c then
      match scan with
      | .ws =>
          feedLogged base bytes (i + 1) .ws
            (state.updateLine (base + i) c)
      | .token oldToken =>
          let origin := match oldToken with
            | .this start => TokenOrigin.current base bytes start i
            | .old oldBase start oldBytes =>
                TokenOrigin.carried oldBase oldBytes start base bytes i
          let after := state.feedToken origin.parserOffset origin.token
          let call : TokenCall := {
            origin := origin
            before := state
            after := after
            after_eq := rfl
          }
          let afterLine := after.updateLine (base + i) c
          match herror : afterLine.db.error? with
          | some ⟨error, _consumed⟩ =>
              { state := {
                  afterLine with
                  db := { afterLine.db with error? := some ⟨error, i + 1⟩ }
                }
                calls := [call] }
          | none =>
              let rest := feedLogged base bytes (i + 1) .ws afterLine
              { state := rest.state, calls := call :: rest.calls }
    else
      let scan := match scan with
        | .ws => ParserState.FeedState.token (.this i)
        | .token oldToken => .token oldToken
      feedLogged base bytes (i + 1) scan state
  else
    { state := { state with
        charp := match scan with
          | .ws => .ws
          | .token oldToken =>
              match oldToken with
              | .this start => .token base (ByteSliceT.mk bytes start)
              | .old oldBase start oldBytes =>
                  .token oldBase (ByteSliceT.mk (oldBytes ++ bytes) start) }
      calls := [] }
termination_by bytes.size - i

/-- Instrumentation of the two `ParserState.feedAll` ingress branches. -/
def feedAllLogged (state : ParserState) (base : Nat)
    (bytes : ByteArray) : FeedRun :=
  match state.charp with
  | .ws => feedLogged base bytes 0 .ws state
  | .token oldBase token =>
      let oldBytes := token.byteArray
      let start := token.start
      let state := { state with charp := default }
      feedLogged base bytes 0 (.token (.old oldBase start oldBytes)) state

/-! ## Instrumented EOF handling -/

/-- The mode-dependent part of `ParserState.done`, after any pending token has
been flushed successfully. -/
def closeAtEOF (state : ParserState) (base : Nat) : DB :=
  let eofPos := state.mkPos base
  match state.tokp with
  | .start =>
      if state.db.scopes.size > 0 then
        state.db.mkParseError eofPos .unclosedBlock
      else state.db
  | .comment _ => state.db.mkParseError eofPos .unclosedComment
  | .const => state.db.mkParseError eofPos .unclosedConst
  | .var => state.db.mkParseError eofPos .unclosedVar
  | .djvars _ => state.db.mkParseError eofPos .unclosedDjvars
  | .math _ parser => match parser.k with
      | .float => state.db.mkParseError eofPos .unclosedFloat
      | .ess => state.db.mkParseError eofPos .unclosedEss
      | .ax => state.db.mkParseError eofPos .unclosedAx
      | .thm => state.db.mkParseError eofPos .unclosedThm
  | .label pos label =>
      state.db.mkErrorFromEvidence pos (.tokenForm (.notACommand label))
  | .includePath _ pos =>
      state.db.mkErrorFromEvidence pos (.tokenForm (.notACommand "$["))
  | .includeClose _ pos _ =>
      state.db.mkErrorFromEvidence pos (.tokenForm (.notACommand "$["))
  | .proof _ => state.db.mkParseError eofPos .unclosedProof

/-- Result of instrumented EOF handling. -/
structure DoneRun : Type where
  db : DB
  calls : List TokenCall

/-- Branch-for-branch instrumentation of `ParserState.done`. -/
def doneLogged (state : ParserState) (base : Nat) : DoneRun :=
  if state.db.error then
    { db := state.db, calls := [] }
  else
    match state.charp with
    | .ws => { db := closeAtEOF state base, calls := [] }
    | .token parserOffset token =>
        let origin := TokenOrigin.trailing parserOffset base token
        let after := state.feedToken origin.parserOffset origin.token
        let call : TokenCall := {
          origin := origin
          before := state
          after := after
          after_eq := rfl
        }
        if after.db.error then
          { db := after.db, calls := [call] }
        else
          { db := closeAtEOF after base, calls := [call] }

/-! ## Logged pure checker entrypoints -/

/-- Result of the instrumented pure checker. -/
structure CheckBytesRun : Type where
  db : DB
  calls : List TokenCall

/-- Instrumented `checkBytesCore`.  Feed calls precede the optional trailing
`done` call in the returned list. -/
def checkBytesCoreLogged (bytes : ByteArray)
    (config : ModeConfig := {}) : CheckBytesRun :=
  let initialDB : DB := { (default : DB) with config := config }
  let initialState : ParserState := {
    (default : ParserState) with db := initialDB
  }
  let feedRun := feedAllLogged initialState 0 bytes
  let doneRun := doneLogged feedRun.state bytes.size
  { db := doneRun.db, calls := feedRun.calls ++ doneRun.calls }

/-- Instrumented public `checkBytes`, including its final consistency gate. -/
def checkBytesLogged (bytes : ByteArray)
    (config : ModeConfig := {}) : CheckBytesRun :=
  let core := checkBytesCoreLogged bytes config
  let db :=
    if core.db.error? = none then
      if (core.db.config.allowDuplicateFloat || core.db.wellFormed?) &&
          core.db.assertDvVarsInFrame? then
        core.db
      else
        core.db.mkErrorFromEvidence ⟨0, 0⟩
          (.internalGate core.db.config.allowDuplicateFloat
            core.db.wellFormed? core.db.assertDvVarsInFrame?)
    else core.db
  { db := db, calls := core.calls }

end Mettapedia.Languages.Metamath.InferenceOneShotByteLog.Raw

namespace Mettapedia.Languages.Metamath.InferenceOneShotByteLog

open Metamath.Verify

abbrev TokenOrigin := Raw.TokenOrigin
abbrev TokenCall := Raw.TokenCall

/-! ## Structurally complete feed traces -/

/-- The exact current-chunk token call at a whitespace boundary. -/
def currentCall (base : Nat) (bytes : ByteArray) (start stop : Nat)
    (before : ParserState) : TokenCall :=
  let origin := Raw.TokenOrigin.current base bytes start stop
  { origin := origin
    before := before
    after := before.feedToken origin.parserOffset origin.token
    after_eq := rfl }

/-- The exact carried-token call at a whitespace boundary. -/
def carriedCall (oldBase : Nat) (oldBytes : ByteArray) (start : Nat)
    (base : Nat) (bytes : ByteArray) (stop : Nat)
    (before : ParserState) : TokenCall :=
  let origin :=
    Raw.TokenOrigin.carried oldBase oldBytes start base bytes stop
  { origin := origin
    before := before
    after := before.feedToken origin.parserOffset origin.token
    after_eq := rfl }

/-- The exact trailing call made by `done`. -/
def trailingCall (parserOffset eofOffset : Nat) (token : ByteSliceT)
    (before : ParserState) : TokenCall :=
  let origin := Raw.TokenOrigin.trailing parserOffset eofOffset token
  { origin := origin
    before := before
    after := before.feedToken origin.parserOffset origin.token
    after_eq := rfl }

/-- State after a current-chunk token call and the terminating whitespace's
line update. -/
def afterCurrentLine (base : Nat) (bytes : ByteArray) (start stop : Nat)
    (before : ParserState) : ParserState :=
  (currentCall base bytes start stop before).after.updateLine
    (base + stop) bytes[stop]!

/-- State after a carried-token call and the terminating whitespace's line
update. -/
def afterCarriedLine (oldBase : Nat) (oldBytes : ByteArray) (start : Nat)
    (base : Nat) (bytes : ByteArray) (stop : Nat)
    (before : ParserState) : ParserState :=
  (carriedCall oldBase oldBytes start base bytes stop before).after.updateLine
    (base + stop) bytes[stop]!

/-- The live loop's exact early-stop rewrite after a token error. -/
def stopWithConsumed (state : ParserState) (error : Error)
    (consumed : Nat) : ParserState :=
  { state with db := { state.db with error? := some ⟨error, consumed⟩ } }

/-- Type-valued chronology of every branch of `ParserState.feed`.

The indices fix the input cursor, scan state, live parser state, final parser
state, and complete chronological call list.  In token branches the raw
`TokenCall.after` precedes the line update retained by the continuation or
early-stop constructor.
-/
inductive FeedTrace :
    (base : Nat) → (bytes : ByteArray) → (cursor : Nat) →
    (scan : ParserState.FeedState) → (before final : ParserState) →
    (calls : List TokenCall) → Type where
  | endWs (base bytes cursor before)
      (hend : ¬ cursor < bytes.size) :
      FeedTrace base bytes cursor .ws before
        { before with charp := .ws } []
  | endCurrent (base bytes cursor start before)
      (hend : ¬ cursor < bytes.size) :
      FeedTrace base bytes cursor (.token (.this start)) before
        { before with charp := .token base (ByteSliceT.mk bytes start) } []
  | endCarried (base bytes cursor oldBase start oldBytes before)
      (hend : ¬ cursor < bytes.size) :
      FeedTrace base bytes cursor (.token (.old oldBase start oldBytes)) before
        ({ before with charp :=
            (CharParser.token oldBase
              (ByteSliceT.mk (oldBytes ++ bytes) start)) } : ParserState) []
  | whitespaceWs (base bytes cursor before final calls)
      (hcursor : cursor < bytes.size)
      (hspace : isWhitespace bytes[cursor] = true)
      (rest : FeedTrace base bytes (cursor + 1) .ws
        (before.updateLine (base + cursor) bytes[cursor]!) final calls) :
      FeedTrace base bytes cursor .ws before final calls
  | currentStop (base bytes cursor start before error previousConsumed)
      (hcursor : cursor < bytes.size)
      (hspace : isWhitespace bytes[cursor] = true)
      (herror :
        (afterCurrentLine base bytes start cursor before).db.error? =
          some ⟨error, previousConsumed⟩) :
      FeedTrace base bytes cursor (.token (.this start)) before
        (stopWithConsumed
          (afterCurrentLine base bytes start cursor before) error (cursor + 1))
        [currentCall base bytes start cursor before]
  | currentContinue (base bytes cursor start before final calls)
      (hcursor : cursor < bytes.size)
      (hspace : isWhitespace bytes[cursor] = true)
      (herror :
        (afterCurrentLine base bytes start cursor before).db.error? = none)
      (rest : FeedTrace base bytes (cursor + 1) .ws
        (afterCurrentLine base bytes start cursor before) final calls) :
      FeedTrace base bytes cursor (.token (.this start)) before final
        (currentCall base bytes start cursor before :: calls)
  | carriedStop
      (base bytes cursor oldBase start oldBytes before error previousConsumed)
      (hcursor : cursor < bytes.size)
      (hspace : isWhitespace bytes[cursor] = true)
      (herror :
        (afterCarriedLine oldBase oldBytes start base bytes cursor before).db.error? =
          some ⟨error, previousConsumed⟩) :
      FeedTrace base bytes cursor (.token (.old oldBase start oldBytes)) before
        (stopWithConsumed
          (afterCarriedLine oldBase oldBytes start base bytes cursor before)
          error (cursor + 1))
        [carriedCall oldBase oldBytes start base bytes cursor before]
  | carriedContinue
      (base bytes cursor oldBase start oldBytes before final calls)
      (hcursor : cursor < bytes.size)
      (hspace : isWhitespace bytes[cursor] = true)
      (herror :
        (afterCarriedLine oldBase oldBytes start base bytes cursor before).db.error? =
          none)
      (rest : FeedTrace base bytes (cursor + 1) .ws
        (afterCarriedLine oldBase oldBytes start base bytes cursor before)
        final calls) :
      FeedTrace base bytes cursor (.token (.old oldBase start oldBytes)) before
        final
        (carriedCall oldBase oldBytes start base bytes cursor before :: calls)
  | nonWhitespaceWs (base bytes cursor before final calls)
      (hcursor : cursor < bytes.size)
      (hspace : isWhitespace bytes[cursor] = false)
      (rest : FeedTrace base bytes (cursor + 1) (.token (.this cursor))
        before final calls) :
      FeedTrace base bytes cursor .ws before final calls
  | nonWhitespaceToken (base bytes cursor oldToken before final calls)
      (hcursor : cursor < bytes.size)
      (hspace : isWhitespace bytes[cursor] = false)
      (rest : FeedTrace base bytes (cursor + 1) (.token oldToken)
        before final calls) :
      FeedTrace base bytes cursor (.token oldToken) before final calls

/-- An exact feed result whose trace prevents omission, insertion, or
reordering of token calls. -/
structure FeedRun (base : Nat) (bytes : ByteArray) (cursor : Nat)
    (scan : ParserState.FeedState) (before : ParserState) : Type where
  final : ParserState
  calls : List TokenCall
  trace : FeedTrace base bytes cursor scan before final calls

/-- Structurally certified instrumentation of `ParserState.feed`. -/
def feedLogged (base : Nat) (bytes : ByteArray) (cursor : Nat)
    (scan : ParserState.FeedState) (before : ParserState) :
    FeedRun base bytes cursor scan before :=
  if hcursor : cursor < bytes.size then
    if hspace : isWhitespace bytes[cursor] then
      match scan with
      | .ws =>
          let rest := feedLogged base bytes (cursor + 1) .ws
            (before.updateLine (base + cursor) bytes[cursor]!)
          { final := rest.final
            calls := rest.calls
            trace := .whitespaceWs base bytes cursor before
              rest.final rest.calls hcursor hspace rest.trace }
      | .token (.this start) =>
          let afterLine := afterCurrentLine base bytes start cursor before
          match herror : afterLine.db.error? with
          | some ⟨error, previousConsumed⟩ =>
              { final := stopWithConsumed afterLine error (cursor + 1)
                calls := [currentCall base bytes start cursor before]
                trace := .currentStop base bytes cursor start before
                  error previousConsumed hcursor hspace herror }
          | none =>
              let rest := feedLogged base bytes (cursor + 1) .ws afterLine
              { final := rest.final
                calls := currentCall base bytes start cursor before :: rest.calls
                trace := .currentContinue base bytes cursor start before
                  rest.final rest.calls hcursor hspace herror rest.trace }
      | .token (.old oldBase start oldBytes) =>
          let afterLine :=
            afterCarriedLine oldBase oldBytes start base bytes cursor before
          match herror : afterLine.db.error? with
          | some ⟨error, previousConsumed⟩ =>
              { final := stopWithConsumed afterLine error (cursor + 1)
                calls :=
                  [carriedCall oldBase oldBytes start base bytes cursor before]
                trace := .carriedStop base bytes cursor oldBase start oldBytes
                  before error previousConsumed hcursor hspace herror }
          | none =>
              let rest := feedLogged base bytes (cursor + 1) .ws afterLine
              { final := rest.final
                calls :=
                  carriedCall oldBase oldBytes start base bytes cursor before ::
                    rest.calls
                trace := .carriedContinue base bytes cursor oldBase start oldBytes
                  before rest.final rest.calls hcursor hspace herror rest.trace }
    else
      have hspaceFalse : isWhitespace bytes[cursor] = false := by
        cases h : isWhitespace bytes[cursor] <;> simp_all
      match scan with
      | .ws =>
          let rest := feedLogged base bytes (cursor + 1)
            (.token (.this cursor)) before
          { final := rest.final
            calls := rest.calls
            trace := .nonWhitespaceWs base bytes cursor before
              rest.final rest.calls hcursor hspaceFalse rest.trace }
      | .token oldToken =>
          let rest := feedLogged base bytes (cursor + 1)
            (.token oldToken) before
          { final := rest.final
            calls := rest.calls
            trace := .nonWhitespaceToken base bytes cursor oldToken before
              rest.final rest.calls hcursor hspaceFalse rest.trace }
  else
    match scan with
    | .ws =>
        { final := { before with charp := .ws }
          calls := []
          trace := .endWs base bytes cursor before hcursor }
    | .token (.this start) =>
        { final := {
            before with charp := .token base (ByteSliceT.mk bytes start) }
          calls := []
          trace := .endCurrent base bytes cursor start before hcursor }
    | .token (.old oldBase start oldBytes) =>
        { final := ({ before with charp :=
            (CharParser.token oldBase
              (ByteSliceT.mk (oldBytes ++ bytes) start)) } : ParserState)
          calls := []
          trace := .endCarried base bytes cursor oldBase start oldBytes
            before hcursor }
termination_by bytes.size - cursor

/-! ## Structurally complete `feedAll` and `done` traces -/

inductive FeedAllTrace :
    (before : ParserState) → (base : Nat) → (bytes : ByteArray) →
    (final : ParserState) → (calls : List TokenCall) → Type where
  | ws (before base bytes final calls)
      (hchar : before.charp = .ws)
      (feed : FeedTrace base bytes 0 .ws before final calls) :
      FeedAllTrace before base bytes final calls
  | carried (before base bytes oldBase token final calls)
      (hchar : before.charp = .token oldBase token)
      (feed : FeedTrace base bytes 0
        (.token (.old oldBase token.start token.byteArray))
        { before with charp := default } final calls) :
      FeedAllTrace before base bytes final calls

structure FeedAllRun (before : ParserState) (base : Nat)
    (bytes : ByteArray) : Type where
  final : ParserState
  calls : List TokenCall
  trace : FeedAllTrace before base bytes final calls

def feedAllLogged (before : ParserState) (base : Nat)
    (bytes : ByteArray) : FeedAllRun before base bytes :=
  match hchar : before.charp with
  | .ws =>
      let feed := feedLogged base bytes 0 .ws before
      { final := feed.final
        calls := feed.calls
        trace := .ws before base bytes feed.final feed.calls hchar feed.trace }
  | .token oldBase token =>
      let cleared := { before with charp := default }
      let feed := feedLogged base bytes 0
        (.token (.old oldBase token.start token.byteArray)) cleared
      { final := feed.final
        calls := feed.calls
        trace := .carried before base bytes oldBase token
          feed.final feed.calls hchar feed.trace }

abbrev closeAtEOF := Raw.closeAtEOF

inductive DoneTrace :
    (before : ParserState) → (eofOffset : Nat) →
    (db : DB) → (calls : List TokenCall) → Type where
  | priorError (before eofOffset)
      (herror : before.db.error = true) :
      DoneTrace before eofOffset before.db []
  | whitespace (before eofOffset)
      (herror : before.db.error = false)
      (hchar : before.charp = .ws) :
      DoneTrace before eofOffset (closeAtEOF before eofOffset) []
  | trailingError (before eofOffset parserOffset token)
      (herror : before.db.error = false)
      (hchar : before.charp = .token parserOffset token)
      (hafter : (trailingCall parserOffset eofOffset token before).after.db.error =
        true) :
      DoneTrace before eofOffset
        (trailingCall parserOffset eofOffset token before).after.db
        [trailingCall parserOffset eofOffset token before]
  | trailingClose (before eofOffset parserOffset token)
      (herror : before.db.error = false)
      (hchar : before.charp = .token parserOffset token)
      (hafter : (trailingCall parserOffset eofOffset token before).after.db.error =
        false) :
      DoneTrace before eofOffset
        (closeAtEOF (trailingCall parserOffset eofOffset token before).after
          eofOffset)
        [trailingCall parserOffset eofOffset token before]

structure DoneRun (before : ParserState) (eofOffset : Nat) : Type where
  db : DB
  calls : List TokenCall
  trace : DoneTrace before eofOffset db calls

def doneLogged (before : ParserState) (eofOffset : Nat) :
    DoneRun before eofOffset :=
  if herror : before.db.error then
    { db := before.db
      calls := []
      trace := .priorError before eofOffset herror }
  else
    have herrorFalse : before.db.error = false :=
      by cases h : before.db.error <;> simp_all
    match hchar : before.charp with
    | .ws =>
        { db := closeAtEOF before eofOffset
          calls := []
          trace := .whitespace before eofOffset herrorFalse hchar }
    | .token parserOffset token =>
        let call := trailingCall parserOffset eofOffset token before
        if hafter : call.after.db.error then
          { db := call.after.db
            calls := [call]
            trace := .trailingError before eofOffset parserOffset token
              herrorFalse hchar hafter }
        else
          have hafterFalse : call.after.db.error = false :=
            by cases h : call.after.db.error <;> simp_all
          { db := closeAtEOF call.after eofOffset
            calls := [call]
            trace := .trailingClose before eofOffset parserOffset token
              herrorFalse hchar hafterFalse }

/-! ## Structurally complete checker runs -/

def initialDB (config : ModeConfig) : DB :=
  { (default : DB) with config := config }

def initialState (config : ModeConfig) : ParserState :=
  { (default : ParserState) with db := initialDB config }

structure CheckBytesCoreRun (bytes : ByteArray) (config : ModeConfig) : Type where
  feedRun : FeedAllRun (initialState config) 0 bytes
  doneRun : DoneRun feedRun.final bytes.size
  db : DB
  calls : List TokenCall
  db_eq : db = doneRun.db
  calls_eq : calls = feedRun.calls ++ doneRun.calls

def checkBytesCoreLogged (bytes : ByteArray)
    (config : ModeConfig := {}) : CheckBytesCoreRun bytes config :=
  let feedRun := feedAllLogged (initialState config) 0 bytes
  let doneRun := doneLogged feedRun.final bytes.size
  { feedRun := feedRun
    doneRun := doneRun
    db := doneRun.db
    calls := feedRun.calls ++ doneRun.calls
    db_eq := rfl
    calls_eq := rfl }

inductive PublicGateTrace : (core final : DB) → Type where
  | priorError (core)
      (herror : core.error? ≠ none) :
      PublicGateTrace core core
  | accepted (core)
      (herror : core.error? = none)
      (hgate :
        ((core.config.allowDuplicateFloat || core.wellFormed?) &&
          core.assertDvVarsInFrame?) = true) :
      PublicGateTrace core core
  | rejected (core)
      (herror : core.error? = none)
      (hgate :
        ((core.config.allowDuplicateFloat || core.wellFormed?) &&
          core.assertDvVarsInFrame?) = false) :
      PublicGateTrace core
        (core.mkErrorFromEvidence ⟨0, 0⟩
          (.internalGate core.config.allowDuplicateFloat
            core.wellFormed? core.assertDvVarsInFrame?))

structure CheckBytesRun (bytes : ByteArray) (config : ModeConfig) : Type where
  coreRun : CheckBytesCoreRun bytes config
  db : DB
  calls : List TokenCall
  gateTrace : PublicGateTrace coreRun.db db
  calls_eq : calls = coreRun.calls

def checkBytesLogged (bytes : ByteArray)
    (config : ModeConfig := {}) : CheckBytesRun bytes config :=
  let coreRun := checkBytesCoreLogged bytes config
  if herror : coreRun.db.error? = none then
    if hgate :
        ((coreRun.db.config.allowDuplicateFloat || coreRun.db.wellFormed?) &&
          coreRun.db.assertDvVarsInFrame?) then
      { coreRun := coreRun
        db := coreRun.db
        calls := coreRun.calls
        gateTrace := .accepted coreRun.db herror hgate
        calls_eq := rfl }
    else
      have hgateFalse :
          ((coreRun.db.config.allowDuplicateFloat || coreRun.db.wellFormed?) &&
            coreRun.db.assertDvVarsInFrame?) = false :=
        by
          cases h :
              ((coreRun.db.config.allowDuplicateFloat || coreRun.db.wellFormed?) &&
                coreRun.db.assertDvVarsInFrame?) <;> simp_all
      { coreRun := coreRun
        db := coreRun.db.mkErrorFromEvidence ⟨0, 0⟩
          (.internalGate coreRun.db.config.allowDuplicateFloat
            coreRun.db.wellFormed? coreRun.db.assertDvVarsInFrame?)
        calls := coreRun.calls
        gateTrace := .rejected coreRun.db herror hgateFalse
        calls_eq := rfl }
  else
    { coreRun := coreRun
      db := coreRun.db
      calls := coreRun.calls
      gateTrace := .priorError coreRun.db herror
      calls_eq := rfl }

/-! ## Universal erasure -/

/-- `updateLine` does not change the runtime database. -/
theorem updateLine_db_eq (state : ParserState) (position : Nat) (byte : UInt8) :
    (state.updateLine position byte).db = state.db := by
  unfold ParserState.updateLine
  split <;> rfl

/-- Structural feed traces erase to the live recursive parser on successful
and failing inputs alike. -/
theorem FeedTrace.final_eq_feed
    {base : Nat} {bytes : ByteArray} {cursor : Nat}
    {scan : ParserState.FeedState} {before final : ParserState}
    {calls : List TokenCall}
    (trace : FeedTrace base bytes cursor scan before final calls) :
    final = before.feed base bytes cursor scan := by
  induction trace with
  | endWs cursor before hend =>
      unfold ParserState.feed
      simp only [hend, dite_false]
  | endCurrent cursor start before hend =>
      unfold ParserState.feed
      simp only [hend, dite_false]
  | endCarried cursor oldBase start oldBytes before hend =>
      unfold ParserState.feed
      simp only [hend, dite_false]
  | whitespaceWs cursor before final calls hcursor hspace rest ih =>
      unfold ParserState.feed
      simp only [hcursor, dite_true, hspace, if_true]
      have hbyte : bytes[cursor]! = bytes[cursor] := by simp [hcursor]
      rw [hbyte] at ih
      exact ih
  | currentStop cursor start before error previousConsumed
      hcursor hspace herror =>
      unfold ParserState.feed
      simp only [hcursor, dite_true, hspace, if_true]
      simp only [afterCurrentLine, currentCall,
        Raw.TokenOrigin.parserOffset, Raw.TokenOrigin.token] at herror ⊢
      have hbyte : bytes[cursor]! = bytes[cursor] := by simp [hcursor]
      rw [hbyte] at herror ⊢
      rw [herror]
      rfl
  | currentContinue cursor start before final calls
      hcursor hspace herror rest ih =>
      unfold ParserState.feed
      simp only [hcursor, dite_true, hspace, if_true]
      simp only [afterCurrentLine, currentCall,
        Raw.TokenOrigin.parserOffset, Raw.TokenOrigin.token] at herror ih ⊢
      have hbyte : bytes[cursor]! = bytes[cursor] := by simp [hcursor]
      rw [hbyte] at herror ih
      rw [herror]
      exact ih
  | carriedStop cursor oldBase start oldBytes before error
      previousConsumed hcursor hspace herror =>
      unfold ParserState.feed
      simp only [hcursor, dite_true, hspace, if_true]
      simp only [afterCarriedLine, carriedCall,
        Raw.TokenOrigin.parserOffset, Raw.TokenOrigin.token] at herror ⊢
      have hbyte : bytes[cursor]! = bytes[cursor] := by simp [hcursor]
      rw [hbyte] at herror ⊢
      rw [herror]
      rfl
  | carriedContinue cursor oldBase start oldBytes before final calls
      hcursor hspace herror rest ih =>
      unfold ParserState.feed
      simp only [hcursor, dite_true, hspace, if_true]
      simp only [afterCarriedLine, carriedCall,
        Raw.TokenOrigin.parserOffset, Raw.TokenOrigin.token] at herror ih ⊢
      have hbyte : bytes[cursor]! = bytes[cursor] := by simp [hcursor]
      rw [hbyte] at herror ih
      rw [herror]
      exact ih
  | nonWhitespaceWs cursor before final calls hcursor hspace rest ih =>
      unfold ParserState.feed
      simp only [hcursor, dite_true, hspace]
      exact ih
  | nonWhitespaceToken cursor oldToken before final calls
      hcursor hspace rest ih =>
      unfold ParserState.feed
      simp only [hcursor, dite_true, hspace]
      exact ih

/-- The certified feed computation erases to `ParserState.feed`. -/
theorem feedLogged_final_eq_feed
    (base : Nat) (bytes : ByteArray) (cursor : Nat)
    (scan : ParserState.FeedState) (before : ParserState) :
    (feedLogged base bytes cursor scan before).final =
      before.feed base bytes cursor scan :=
  (feedLogged base bytes cursor scan before).trace.final_eq_feed

/-- Structural `feedAll` traces erase to the live parser. -/
theorem FeedAllTrace.final_eq_feedAll
    {before : ParserState} {base : Nat} {bytes : ByteArray}
    {final : ParserState} {calls : List TokenCall}
    (trace : FeedAllTrace before base bytes final calls) :
    final = before.feedAll base bytes := by
  cases trace with
  | ws final calls hchar feed =>
      simpa [ParserState.feedAll, hchar] using feed.final_eq_feed
  | carried oldBase token final calls hchar feed =>
      simpa [ParserState.feedAll, hchar] using feed.final_eq_feed

/-- The certified `feedAll` computation erases to `ParserState.feedAll`. -/
theorem feedAllLogged_final_eq_feedAll
    (before : ParserState) (base : Nat) (bytes : ByteArray) :
    (feedAllLogged before base bytes).final = before.feedAll base bytes :=
  (feedAllLogged before base bytes).trace.final_eq_feedAll

/-- Structural EOF traces erase to `ParserState.done`. -/
theorem DoneTrace.db_eq_done
    {before : ParserState} {eofOffset : Nat} {db : DB}
    {calls : List TokenCall}
    (trace : DoneTrace before eofOffset db calls) :
    db = before.done eofOffset := by
  cases trace with
  | priorError herror =>
      simp [ParserState.done, herror]
  | whitespace herror hchar =>
      unfold ParserState.done
      simp only [herror, hchar]
      rfl
  | trailingError parserOffset token herror hchar hafter =>
      simp only [trailingCall, Raw.TokenOrigin.parserOffset,
        Raw.TokenOrigin.token] at hafter
      simp [ParserState.done, herror, hchar, hafter, trailingCall,
        Raw.TokenOrigin.parserOffset, Raw.TokenOrigin.token]
  | trailingClose parserOffset token herror hchar hafter =>
      simp only [trailingCall, Raw.TokenOrigin.parserOffset,
        Raw.TokenOrigin.token] at hafter
      unfold ParserState.done
      simp only [herror, hchar, hafter]
      rfl

/-- The certified EOF computation erases to `ParserState.done`. -/
theorem doneLogged_db_eq_done (before : ParserState) (eofOffset : Nat) :
    (doneLogged before eofOffset).db = before.done eofOffset :=
  (doneLogged before eofOffset).trace.db_eq_done

/-- Any structurally certified core run erases to `checkBytesCore`. -/
theorem CheckBytesCoreRun.db_eq_checkBytesCore
    {bytes : ByteArray} {config : ModeConfig}
    (run : CheckBytesCoreRun bytes config) :
    run.db = checkBytesCore bytes config := by
  rw [run.db_eq]
  rw [run.doneRun.trace.db_eq_done]
  rw [run.feedRun.trace.final_eq_feedAll]
  rfl

/-- The computed core log erases to `checkBytesCore` for every result. -/
theorem checkBytesCoreLogged_db_eq_checkBytesCore
    (bytes : ByteArray) (config : ModeConfig := {}) :
    (checkBytesCoreLogged bytes config).db = checkBytesCore bytes config :=
  (checkBytesCoreLogged bytes config).db_eq_checkBytesCore

/-- The public consistency-gate trace erases to the exact post-check branch. -/
theorem PublicGateTrace.final_eq_gate
    {core final : DB} (trace : PublicGateTrace core final) :
    final =
      if core.error? = none then
        if (core.config.allowDuplicateFloat || core.wellFormed?) &&
            core.assertDvVarsInFrame? then
          core
        else
          core.mkErrorFromEvidence ⟨0, 0⟩
            (.internalGate core.config.allowDuplicateFloat
              core.wellFormed? core.assertDvVarsInFrame?)
      else core := by
  cases trace with
  | priorError herror => simp [herror]
  | accepted herror hgate => simp [herror, hgate]
  | rejected herror hgate => simp [herror, hgate]

/-- Any structurally certified public run erases to `checkBytes`. -/
theorem CheckBytesRun.db_eq_checkBytes
    {bytes : ByteArray} {config : ModeConfig}
    (run : CheckBytesRun bytes config) :
    run.db = checkBytes bytes config := by
  rw [run.gateTrace.final_eq_gate]
  rw [run.coreRun.db_eq_checkBytesCore]
  rfl

/-- The computed public log erases to `checkBytes` for every result. -/
theorem checkBytesLogged_db_eq_checkBytes
    (bytes : ByteArray) (config : ModeConfig := {}) :
    (checkBytesLogged bytes config).db = checkBytes bytes config :=
  (checkBytesLogged bytes config).db_eq_checkBytes

/-! ## Exact hand-off and call order -/

/-- The `DoneRun` trace is indexed by the final state certified by the
preceding `FeedAllRun`; this Type-valued projection exposes that hand-off. -/
def checkBytesCoreLogged_handoffTrace
    (bytes : ByteArray) (config : ModeConfig := {}) :
    let run := checkBytesCoreLogged bytes config
    DoneTrace run.feedRun.final bytes.size
      run.doneRun.db run.doneRun.calls := by
  intro run
  exact run.doneRun.trace

/-- Scanner calls precede the optional trailing `done` call exactly. -/
theorem checkBytesCoreLogged_calls_eq_append
    (bytes : ByteArray) (config : ModeConfig := {}) :
    let run := checkBytesCoreLogged bytes config
    run.calls = run.feedRun.calls ++ run.doneRun.calls := by
  intro run
  exact run.calls_eq

/-- The public consistency gate does not insert, drop, or reorder token calls. -/
theorem checkBytesLogged_calls_eq_core
    (bytes : ByteArray) (config : ModeConfig := {}) :
    (checkBytesLogged bytes config).calls =
      (checkBytesLogged bytes config).coreRun.calls :=
  (checkBytesLogged bytes config).calls_eq

end Mettapedia.Languages.Metamath.InferenceOneShotByteLog
