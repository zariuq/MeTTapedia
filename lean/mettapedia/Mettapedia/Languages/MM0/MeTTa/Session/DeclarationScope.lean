import Mettapedia.Languages.MM0.MeTTa.Data.InferenceCache

/-!
# Reset before a declaration check

The checkpoint below is reached by the actual `mm0:submit` body. Its next
computation is the retained `mm0:service-step` call, and the inference cache
has already been emptied. All other spaces and state cells are unchanged.

The reset establishes a coherent cache for the current signature even when
the previous values were stale or invalid. The four-field row shape comes from
the cache writer and does not assert that those values were correct. Preservation of that signature
through all checking families and ordered admission remain session obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.DeclarationScope

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean handleValue)
open NamedSpaces (Handle)

private def environment (command : Atom) : Subst := [("command", command)]

private def currentEnvironment (state command : Atom) : Subst :=
  ("current", .expression [.symbol "Some", state]) :: environment command

private def checkingEnvironment (state command : Atom) : Subst :=
  ("state", state) :: currentEnvironment state command

private def cacheEnvironment (handle : Handle) (state command : Atom) : Subst :=
  ("cache", handleValue handle) :: checkingEnvironment state command

def declarationEnvironment (handle : Handle) (state command : Atom) : Subst :=
  ("set", boolean true) :: cacheEnvironment handle state command

private def currentBody : Atom :=
  match submitEquation.body with
  | .expression [_, _, _, body] => body
  | _ => .expression []

private def cases : SpaceSemantics.Cases :=
  match currentBody with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def activeBody : Atom := (cases[0]'(by decide)).2

private def cacheBody : Atom :=
  match activeBody with
  | .expression [_, _, _, body] => body
  | _ => .expression []

def declarationBody : Atom :=
  match cacheBody with
  | .expression [_, _, _, body] => body
  | _ => .expression []

private def admittedBody : Atom :=
  match declarationBody with
  | .expression [_, _, _, body] => body
  | _ => .expression []

def checkpoint (after : State) (handle : Handle) (state command : Atom) : Configuration :=
  { state := after, control := .evaluate (declarationEnvironment handle state command) declarationBody,
    frames := [.sequence [] [], .sequence [] [], .sequence [] [], .sequence [] []] }

private theorem body_shape :
    submitEquation.body = .expression [.symbol "let", .var "current",
      .expression [.symbol "get-state", .symbol "mm0-session"], currentBody] := by decide

private theorem current_body_shape :
    currentBody = .expression [.symbol "case", .var "current",
      .expression (cases.map fun entry => .expression [entry.1, entry.2])] := by decide

private theorem cases_shape :
    cases = [(.expression [.symbol "Some", .var "state"], activeBody),
      (.symbol "None", .grounded (.bool false)), (.var "malformed", .symbol "MM0:Malformed")] := by decide

private theorem active_body_shape :
    activeBody = .expression [.symbol "let", .var "cache",
      .expression [.symbol "get-state", .symbol "mm0-inference-cache"], cacheBody] := by decide

private theorem cache_body_shape :
    cacheBody = .expression [.symbol "let", .var "set",
      .expression [.symbol "mm0:clear-space", .var "cache", SpaceClearing.cachePattern], declarationBody] := by decide

private theorem declaration_body_shape :
    declarationBody = .expression [.symbol "let", .var "answer",
      .expression [.symbol "mm0:service-step", .var "state", .var "command"], admittedBody] := by decide

theorem cell_returns (before : State) (bindings : Subst) (name : String) (value : Atom)
    (present : before.cells name = some value) :
    PureReturns program bindings before (.expression [.symbol "get-state", .symbol name]) before value := by
  apply native_unary_call_returns program bindings before before before "get-state" (.symbol name)
    (.symbol name) value (by decide) (by decide) (by decide)
    (symbol_returns program bindings before name) _ (by decide)
  simp [StdLib.apply, present]

private theorem active_body_enters (before : State) (handle : Handle) (stored : List Atom)
    (state command : Atom)
    (current : before.cells InferenceCache.cell = some (handleValue handle))
    (allocated : before.read handle = some stored)
    (shaped : Effects.RowsHaveArity 4 stored) :
    ∃ after, (theory program).MultiStep
        { state := before, control := .evaluate (checkingEnvironment state command) activeBody }
        { state := after, control := .evaluate (declarationEnvironment handle state command) declarationBody,
          frames := [.sequence [] [], .sequence [] []] } ∧
      after.read handle = some [] ∧
      (∀ other, other ≠ handle → after.read other = before.read other) ∧
      after.cells = before.cells := by
  obtain ⟨after, clear, empty, others, cells⟩ := SpaceClearing.clear_returns
    (cacheEnvironment handle state command) before handle stored "cache" SpaceClearing.cachePattern allocated
    (by simp [cacheEnvironment, applySubst, Subst.lookup])
    (by simp [SpaceClearing.cachePattern, cacheEnvironment, checkingEnvironment,
      currentEnvironment, environment, applySubst, applySubst.applySubstList, Subst.lookup])
    ⟨_, _, rfl⟩ (SpaceClearing.cache_pattern_selects shaped)
  refine ⟨after, ?_, empty, others, cells⟩
  rw [active_body_shape]
  have reached : (theory program).MultiStep
      { state := before, control := .evaluate (checkingEnvironment state command) (
        .expression [.symbol "let", .var "cache",
          .expression [.symbol "get-state", .symbol "mm0-inference-cache"], cacheBody]) }
      (withFrames
        { state := after, control := .evaluate (declarationEnvironment handle state command) declarationBody,
          frames := [.sequence [] []] } [.sequence [] []]) := by
    apply let_reaches program (checkingEnvironment state command) (cacheEnvironment handle state command)
      before before (.var "cache") _ cacheBody (handleValue handle) _
      (cell_returns before _ InferenceCache.cell (handleValue handle) current) _ _
    · simp [SpaceSemantics.matchValue, matchAtom, checkingEnvironment, currentEnvironment,
        environment, cacheEnvironment, Subst.lookup]
    · rw [cache_body_shape]
      apply let_enters program (cacheEnvironment handle state command)
        (declarationEnvironment handle state command) before after (.var "set") _ declarationBody
        (boolean true) clear
      simp [SpaceSemantics.matchValue, matchAtom, cacheEnvironment, checkingEnvironment,
        currentEnvironment, environment, declarationEnvironment, Subst.lookup]
  simpa [withFrames] using reached

/-- Before the actual declaration check can begin, the old cache rows have
been removed. The path makes no assumption about that check's answer. -/
theorem submit_body_enters_after_reset (before : State) (handle : Handle) (stored : List Atom)
    (state command : Atom)
    (session : before.cells "mm0-session" = some (.expression [.symbol "Some", state]))
    (current : before.cells InferenceCache.cell = some (handleValue handle))
    (allocated : before.read handle = some stored)
    (shaped : Effects.RowsHaveArity 4 stored) :
    ∃ after, (theory program).MultiStep
        { state := before, control := .evaluate (environment command) submitEquation.body }
        (checkpoint after handle state command) ∧
      after.read handle = some [] ∧
      (∀ other, other ≠ handle → after.read other = before.read other) ∧
      after.cells = before.cells := by
  obtain ⟨after, checking, empty, others, cells⟩ :=
    active_body_enters before handle stored state command current allocated shaped
  refine ⟨after, ?_, empty, others, cells⟩
  rw [body_shape]
  have reached : (theory program).MultiStep
      { state := before, control := .evaluate (environment command) (
        .expression [.symbol "let", .var "current",
          .expression [.symbol "get-state", .symbol "mm0-session"], currentBody]) }
      (withFrames
        { state := after, control := .evaluate (declarationEnvironment handle state command) declarationBody,
          frames := [.sequence [] [], .sequence [] [], .sequence [] []] } [.sequence [] []]) := by
    apply let_reaches program (environment command) (currentEnvironment state command)
      before before (.var "current") _ currentBody (.expression [.symbol "Some", state]) _
      (cell_returns before _ "mm0-session" _ session) _ _
    · simp [SpaceSemantics.matchValue, matchAtom, environment, Subst.lookup, currentEnvironment]
    · rw [current_body_shape]
      apply case_reaches program (currentEnvironment state command) (checkingEnvironment state command)
        before before (.var "current") (.expression [.symbol "Some", state]) activeBody _ cases _
        (read_cases_encoded cases) _ _ checking
      · simpa [currentEnvironment, applySubst, Subst.lookup] using
          variable_returns program (currentEnvironment state command) before "current"
      · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, currentEnvironment, environment,
          checkingEnvironment, Subst.lookup]
  simpa [withFrames, checkpoint] using reached

theorem checkpoint_starts_actual_service_call (after : State) (handle : Handle) (state command : Atom) :
    step program (checkpoint after handle state command) = some
      { state := after,
        control := .evaluate (declarationEnvironment handle state command)
          (.expression [.symbol "mm0:service-step", .var "state", .var "command"]),
        frames := .bind (declarationEnvironment handle state command) (.var "answer") admittedBody ::
          [.sequence [] [], .sequence [] [], .sequence [] [], .sequence [] []] } := by
  simp [checkpoint, declaration_body_shape, step]

/-- The actual reset discharges initial cache coherence. No authorization
condition is imposed on the old rows. All other table readings are retained. -/
theorem submit_body_enters_with_ready_cache (before : State) (handle : Handle) (stored : List Atom)
    (state command terms : Atom) (signature : Kernel.TermSignature)
    (session : before.cells "mm0-session" = some (.expression [.symbol "Some", state]))
    (current : before.cells InferenceCache.cell = some (handleValue handle))
    (allocated : before.read handle = some stored)
    (shaped : Effects.RowsHaveArity 4 stored) :
    ∃ after, (theory program).MultiStep
        { state := before, control := .evaluate (environment command) submitEquation.body }
        (checkpoint after handle state command) ∧
      InferenceCache.Ready signature terms handle after ∧
      (∀ other, other ≠ handle → after.read other = before.read other) ∧
      after.cells = before.cells := by
  obtain ⟨after, path, empty, others, cells⟩ :=
    submit_body_enters_after_reset before handle stored state command session current allocated shaped
  refine ⟨after, path, ⟨?_, [], empty, InferenceCache.empty_valid signature terms⟩, others, cells⟩
  rw [cells]
  exact current

theorem checkpoint_preserves_request (handle : Handle) (state command : Atom) :
    applySubst (declarationEnvironment handle state command) (.var "state") = state ∧
      applySubst (declarationEnvironment handle state command) (.var "command") = command := by
  simp [declarationEnvironment, cacheEnvironment, checkingEnvironment, currentEnvironment,
    environment, applySubst, Subst.lookup]

/-- A previous checking epoch supplies the physical layout even when the new
signature differs. Reset establishes coherence for the new signature instead
of treating a retained handle as authority to reuse old answers. -/
theorem reset_from_previous_epoch (before : State) (handle : Handle)
    (state command oldTerms newTerms : Atom) (oldSignature newSignature : Kernel.TermSignature)
    (session : before.cells "mm0-session" = some (.expression [.symbol "Some", state]))
    (previous : InferenceCache.Ready oldSignature oldTerms handle before) :
    ∃ after, (theory program).MultiStep
        { state := before, control := .evaluate (environment command) submitEquation.body }
        (checkpoint after handle state command) ∧
      InferenceCache.Ready newSignature newTerms handle after ∧
      (∀ other, other ≠ handle → after.read other = before.read other) ∧
      after.cells = before.cells := by
  obtain ⟨current, stored, allocated, valid⟩ := previous
  exact submit_body_enters_with_ready_cache before handle stored state command newTerms newSignature
    session current allocated valid.rows

namespace Initialization

private def equation : SpaceSemantics.Equation := serviceSource.program.equations[3]'(by decide)

private def bodyAfterLet : Atom → Atom
  | .expression [_, _, _, body] => body
  | _ => .expression []

private def cacheBody : Atom := bodyAfterLet equation.body
private def proofBody : Atom := bodyAfterLet cacheBody
private def setProofBody : Atom := bodyAfterLet proofBody

def continuation : Atom := bodyAfterLet setProofBody

def cacheHandle (before : State) : Handle := (before.allocate []).1
private def cacheAllocated (before : State) : State := (before.allocate []).2
private def cacheSet (before : State) : State :=
  (cacheAllocated before).putCell InferenceCache.cell (handleValue (cacheHandle before))

def proofHandle (before : State) : Handle := ((cacheSet before).allocate []).1
private def proofAllocated (before : State) : State := ((cacheSet before).allocate []).2

def stateAfter (before : State) : State :=
  (proofAllocated before).putCell "mm0-proof-store" (handleValue (proofHandle before))

private def initialEnvironment (spec : Atom) : Subst := [("spec", spec)]
private def cacheEnvironment (before : State) (spec : Atom) : Subst :=
  ("cache", handleValue (cacheHandle before)) :: initialEnvironment spec
private def cacheSetEnvironment (before : State) (spec : Atom) : Subst :=
  ("set", boolean true) :: cacheEnvironment before spec
private def proofEnvironment (before : State) (spec : Atom) : Subst :=
  ("proofs", handleValue (proofHandle before)) :: cacheSetEnvironment before spec

def initializedEnvironment (before : State) (spec : Atom) : Subst :=
  ("setProofs", boolean true) :: proofEnvironment before spec

def checkpoint (before : State) (spec : Atom) : Configuration :=
  { state := stateAfter before, control := .evaluate (initializedEnvironment before spec) continuation,
    frames := [.sequence [] [], .sequence [] [], .sequence [] [], .sequence [] []] }

private theorem source_shapes :
    equation.body = .expression [.symbol "let", .var "cache",
      .expression [.symbol "new-space"], cacheBody] ∧
    cacheBody = .expression [.symbol "let", .var "set",
      .expression [.symbol "change-state!", .symbol "mm0-inference-cache", .var "cache"], proofBody] ∧
    proofBody = .expression [.symbol "let", .var "proofs",
      .expression [.symbol "new-space"], setProofBody] ∧
    setProofBody = .expression [.symbol "let", .var "setProofs",
      .expression [.symbol "change-state!", .symbol "mm0-proof-store", .var "proofs"], continuation] := by decide

private theorem allocate_returns (bindings : Subst) (before : State) :
    PureReturns program bindings before (.expression [.symbol "new-space"])
      (before.allocate []).2 (handleValue (before.allocate []).1) :=
  native_variable_call_returns program bindings before (before.allocate []).2 "new-space" [] _
    (by decide) (by decide) rfl (by decide)

private theorem put_returns (bindings : Subst) (before : State) (name variableName : String) :
    PureReturns program bindings before
      (.expression [.symbol "change-state!", .symbol name, .var variableName])
      (before.putCell name (applySubst bindings (.var variableName))) (boolean true) := by
  let value := applySubst bindings (.var variableName)
  let after := before.putCell name value
  apply call_returns program bindings before after "change-state!" _ _ (by decide) _ (by decide)
  have native := native_function_arguments_return program bindings before after "change-state!"
    [.symbol name, value] 2 (boolean true) (by decide) (by decide) rfl
  have raw := raw_argument_answers program bindings before after "change-state!"
    (.var variableName) [] [.symbol name] 1 [boolean true] (by decide) native
  exact evaluated_argument_returns program bindings before before after (.function "change-state!")
    (.symbol name) (.symbol name) (boolean true) [.var variableName] [] 0 (by decide)
    (symbol_returns program bindings before name) raw

/-- The actual start body allocates both private stores and installs their
handles before entering the theory/session allocation tail. -/
theorem source_prefix_reaches (before : State) (spec : Atom) :
    (theory program).MultiStep
      { state := before, control := .evaluate (initialEnvironment spec) equation.body }
      (checkpoint before spec) := by
  have setProofs : (theory program).MultiStep
      { state := proofAllocated before, control := .evaluate (proofEnvironment before spec) setProofBody }
      { state := stateAfter before, control := .evaluate (initializedEnvironment before spec) continuation,
        frames := [.sequence [] []] } := by
    rw [source_shapes.2.2.2]
    apply let_enters program (proofEnvironment before spec) (initializedEnvironment before spec)
      (proofAllocated before) (stateAfter before) (.var "setProofs") _ continuation (boolean true)
    · simpa [stateAfter, proofEnvironment, applySubst, Subst.lookup] using
        put_returns (proofEnvironment before spec) (proofAllocated before) "mm0-proof-store" "proofs"
    · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, initializedEnvironment,
        proofEnvironment, cacheSetEnvironment, cacheEnvironment, initialEnvironment]
  have proofs : (theory program).MultiStep
      { state := cacheSet before, control := .evaluate (cacheSetEnvironment before spec) proofBody }
      { state := stateAfter before, control := .evaluate (initializedEnvironment before spec) continuation,
        frames := [.sequence [] [], .sequence [] []] } := by
    rw [source_shapes.2.2.1]
    apply let_reaches program (cacheSetEnvironment before spec) (proofEnvironment before spec)
      (cacheSet before) (proofAllocated before) (.var "proofs") _ setProofBody (handleValue (proofHandle before)) _
      (allocate_returns _ _) _ setProofs
    simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, proofEnvironment,
      cacheSetEnvironment, cacheEnvironment, initialEnvironment]
  have setCache : (theory program).MultiStep
      { state := cacheAllocated before, control := .evaluate (cacheEnvironment before spec) cacheBody }
      { state := stateAfter before, control := .evaluate (initializedEnvironment before spec) continuation,
        frames := [.sequence [] [], .sequence [] [], .sequence [] []] } := by
    rw [source_shapes.2.1]
    apply let_reaches program (cacheEnvironment before spec) (cacheSetEnvironment before spec)
      (cacheAllocated before) (cacheSet before) (.var "set") _ proofBody (boolean true) _ _ _ proofs
    · simpa [cacheSet, cacheEnvironment, InferenceCache.cell, applySubst, Subst.lookup] using
        put_returns (cacheEnvironment before spec) (cacheAllocated before) "mm0-inference-cache" "cache"
    · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup,
        cacheSetEnvironment, cacheEnvironment, initialEnvironment]
  rw [source_shapes.1]
  apply let_reaches program (initialEnvironment spec) (cacheEnvironment before spec)
    before (cacheAllocated before) (.var "cache") _ cacheBody (handleValue (cacheHandle before)) _
    (allocate_returns _ _) _ setCache
  simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, cacheEnvironment, initialEnvironment]

/-- Allocation establishes shape without an invariant assumption on the old
state. The stores are distinct, and both state-cell handles read back correctly. -/
theorem private_rows_initialized (before : State) :
    (stateAfter before).read (cacheHandle before) = some [] ∧
    (stateAfter before).read (proofHandle before) = some [] ∧
    (stateAfter before).cells InferenceCache.cell = some (handleValue (cacheHandle before)) ∧
    (stateAfter before).cells "mm0-proof-store" = some (handleValue (proofHandle before)) ∧
    cacheHandle before ≠ proofHandle before := by
  have different : cacheHandle before ≠ proofHandle before := by
    intro same
    have equal := Handle.privateSpace.inj same
    simp only [cacheHandle, cacheSet, cacheAllocated,
      NamedSpaces.Store.allocate, NamedSpaces.Store.putCell] at equal
    omega
  have below : before.next < before.next + 1 + 1 := by omega
  refine ⟨?_, ?_, ?_, ?_, different⟩
  · simp [stateAfter, proofAllocated, proofHandle, cacheSet, cacheAllocated, cacheHandle,
      InferenceCache.cell, NamedSpaces.Store.allocate, NamedSpaces.Store.putCell, NamedSpaces.Store.read, below]
  all_goals
    simp [stateAfter, proofAllocated, proofHandle, cacheSet, cacheAllocated, cacheHandle,
      InferenceCache.cell, NamedSpaces.Store.allocate, NamedSpaces.Store.putCell, NamedSpaces.Store.read]

end Initialization

/-! ## Completing a submission and retaining refusal -/

private def answerBody : Atom :=
  match admittedBody with
  | .expression [_, _, _, body] => body
  | _ => .expression []

private def answerCases : SpaceSemantics.Cases :=
  match answerBody with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private theorem admitted_body_shape :
    admittedBody = .expression [.symbol "let", .var "done",
      .expression [.symbol "change-state!", .symbol "mm0-session", .var "answer"],
      answerBody] := by decide +kernel

private theorem answer_body_shape :
    answerBody = .expression [.symbol "case", .var "answer",
      .expression (answerCases.map fun row => .expression [row.1, row.2])] := by decide +kernel

private theorem answer_cases_shape :
    answerCases = [(.expression [.symbol "Some", .var "next"], boolean true),
      (.symbol "None", boolean false), (.var "malformed", .symbol "MM0:Malformed")] := by
  decide +kernel

private theorem put_session_returns (bindings : Subst) (before : State) (answer : Atom)
    (captured : applySubst bindings (.var "answer") = answer) :
    PureReturns program bindings before
      (.expression [.symbol "change-state!", .symbol "mm0-session", .var "answer"])
      (before.putCell "mm0-session" answer) (boolean true) := by
  apply call_returns program bindings before (before.putCell "mm0-session" answer)
    "change-state!" _ _ (by decide) _ (by decide)
  have native := native_function_arguments_return program bindings before
    (before.putCell "mm0-session" answer) "change-state!"
    [.symbol "mm0-session", answer] 2 (boolean true) (by decide) (by decide) rfl
  have raw := raw_argument_answers program bindings before (before.putCell "mm0-session" answer)
    "change-state!" (.var "answer") [] [.symbol "mm0-session"] 1 [boolean true] (by decide)
    (by simpa only [captured, List.cons_append, List.nil_append, Nat.reduceAdd] using native)
  exact evaluated_argument_returns program bindings before before
    (before.putCell "mm0-session" answer) (.function "change-state!")
    (.symbol "mm0-session") (.symbol "mm0-session") (boolean true) [.var "answer"] [] 0
    (by decide) (symbol_returns program bindings before "mm0-session") raw

private theorem answer_body_returns (bindings : Subst) (before : State) (answer : Option Atom)
    (captured : applySubst bindings (.var "answer") = ListAccess.optionValue answer)
    (fresh : Subst.lookup bindings "next" = none) :
    PureReturns program bindings before answerBody before (boolean answer.isSome) := by
  rw [answer_body_shape]
  cases answer with
  | none =>
    apply case_returns program bindings bindings before before before (.var "answer")
      (.symbol "None") (boolean false) _ _ answerCases (read_cases_encoded _)
    · simpa only [captured, ListAccess.optionValue] using variable_returns program bindings before "answer"
    · simp [answer_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
    · exact grounded_returns program bindings before (.bool false)
  | some next =>
    let bound := ("next", next) :: bindings
    apply case_returns program bindings bound before before before (.var "answer")
      (.expression [.symbol "Some", next]) (boolean true) _ _ answerCases (read_cases_encoded _)
    · simpa only [captured, ListAccess.optionValue] using variable_returns program bindings before "answer"
    · simp [answer_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, fresh, bound]
    · exact grounded_returns program bound before (.bool true)

private theorem admitted_body_returns (bindings : Subst) (before : State) (answer : Option Atom)
    (captured : applySubst bindings (.var "answer") = ListAccess.optionValue answer)
    (freshDone : Subst.lookup bindings "done" = none)
    (freshNext : Subst.lookup bindings "next" = none) :
    PureReturns program bindings before admittedBody
      (before.putCell "mm0-session" (ListAccess.optionValue answer)) (boolean answer.isSome) := by
  rw [admitted_body_shape]
  let bound := ("done", boolean true) :: bindings
  apply let_returns program bindings bound before
    (before.putCell "mm0-session" (ListAccess.optionValue answer))
    (before.putCell "mm0-session" (ListAccess.optionValue answer)) (.var "done") _ _
    (boolean true) _ (put_session_returns bindings before _ captured)
  · simp [SpaceSemantics.matchValue, matchAtom, freshDone, bound]
  · apply answer_body_returns
    · simpa [bound, applySubst, Subst.lookup] using captured
    · change Subst.lookup (("done", boolean true) :: bindings) "next" = none
      simpa [Subst.lookup] using freshNext

/-- The retained submit tail records the actual service answer and returns
its Boolean status. It cannot publish a different session answer. -/
theorem declaration_tail_returns (before checked : State) (handle : Handle)
    (state command : Atom) (answer : Option Atom)
    (service : PureReturns program (declarationEnvironment handle state command) before
      (.expression [.symbol "mm0:service-step", .var "state", .var "command"])
      checked (ListAccess.optionValue answer)) :
    PureReturns program (declarationEnvironment handle state command) before declarationBody
      (checked.putCell "mm0-session" (ListAccess.optionValue answer)) (boolean answer.isSome) := by
  rw [declaration_body_shape]
  let bindings := declarationEnvironment handle state command
  let bound := ("answer", ListAccess.optionValue answer) :: bindings
  apply let_returns program bindings bound before checked
    (checked.putCell "mm0-session" (ListAccess.optionValue answer)) (.var "answer") _ _ _ _ service
  · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, bound, bindings,
      declarationEnvironment, cacheEnvironment, checkingEnvironment, currentEnvironment, environment]
  · apply admitted_body_returns
    · simp [bound, applySubst, Subst.lookup]
    · simp [bound, bindings, declarationEnvironment, cacheEnvironment, checkingEnvironment,
        currentEnvironment, environment, Subst.lookup]
    · simp [bound, bindings, declarationEnvironment, cacheEnvironment, checkingEnvironment,
        currentEnvironment, environment, Subst.lookup]

private theorem path_trans {system : Mettapedia.GSLT.GSLT}
    {first middle last : system.Term} (one : system.MultiStep first middle)
    (two : system.MultiStep middle last) : system.MultiStep first last := by
  induction one with
  | refl _ => exact two
  | step transition _ ih => exact .step transition (ih two)

private theorem empty_sequences_return (state : State) (answer : Atom) (count : Nat) :
    (theory program).MultiStep
      { state, control := .returned [answer], frames := List.replicate count (.sequence [] []) }
      (finished state [answer] [] []) := by
  induction count with
  | zero => exact .refl _
  | succ count ih =>
    simp only [List.replicate_succ]
    exact .step (step_transition rfl) (.step (step_transition rfl) ih)

/-- Compose the real reset checkpoint with the actual service computation.
The checking premise names only that child call, not submission or admission. -/
theorem submit_body_returns_of_service (before : State) (handle : Handle) (stored : List Atom)
    (state command : Atom) (answer : Option Atom)
    (session : before.cells "mm0-session" = some (.expression [.symbol "Some", state]))
    (current : before.cells InferenceCache.cell = some (handleValue handle))
    (allocated : before.read handle = some stored) (shaped : Effects.RowsHaveArity 4 stored)
    (service : ∀ (checking : State), checking.read handle = some [] →
      (∀ other, other ≠ handle → checking.read other = before.read other) →
      checking.cells = before.cells →
      ∃ (checked : State), PureReturns program (declarationEnvironment handle state command) checking
        (.expression [.symbol "mm0:service-step", .var "state", .var "command"])
        checked (ListAccess.optionValue answer)) :
    ∃ (checking checked : State), PureReturns program (environment command) before submitEquation.body
        (checked.putCell "mm0-session" (ListAccess.optionValue answer)) (boolean answer.isSome) ∧
      checking.read handle = some [] ∧
      (∀ other, other ≠ handle → checking.read other = before.read other) ∧
      checking.cells = before.cells := by
  obtain ⟨checking, resetPath, empty, others, cells⟩ :=
    submit_body_enters_after_reset before handle stored state command session current allocated shaped
  obtain ⟨checked, computed⟩ := service checking empty others cells
  refine ⟨checking, checked, ?_, empty, others, cells⟩
  have tail := declaration_tail_returns checking checked handle state command answer computed
  have lifted := path_with_caller_frames program
    [.sequence [] [], .sequence [] [], .sequence [] [], .sequence [] []] tail
  exact path_trans resetPath (path_trans lifted (empty_sequences_return _ _ 4))

private theorem submit_clause (command : Atom) :
    clauses program "mm0:submit" [command] = [.evaluate (environment command) submitEquation.body] := by
  rw [clauses_use_only_the_named_equations, submit_equation_is_unique]
  simp [submit_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, environment]

/-- The complete source request composes its reset, checking call and owned
session-cell update. The child receives the emptied cache and original tables. -/
theorem submit_returns_of_service (bindings : Subst) (before : State) (handle : Handle)
    (stored : List Atom) (state command : Atom) (answer : Option Atom) (name : String)
    (captured : applySubst bindings (.var name) = command)
    (session : before.cells "mm0-session" = some (.expression [.symbol "Some", state]))
    (current : before.cells InferenceCache.cell = some (handleValue handle))
    (allocated : before.read handle = some stored) (shaped : Effects.RowsHaveArity 4 stored)
    (service : ∀ (checking : State), checking.read handle = some [] →
      (∀ other, other ≠ handle → checking.read other = before.read other) →
      checking.cells = before.cells →
      ∃ (checked : State), PureReturns program (declarationEnvironment handle state command) checking
        (.expression [.symbol "mm0:service-step", .var "state", .var "command"])
        checked (ListAccess.optionValue answer)) :
    ∃ (checking checked : State),
      PureReturns program bindings before (.expression [.symbol "mm0:submit", .var name])
        (checked.putCell "mm0-session" (ListAccess.optionValue answer)) (boolean answer.isSome) ∧
      (checked.putCell "mm0-session" (ListAccess.optionValue answer)).cells "mm0-session" =
        some (ListAccess.optionValue answer) ∧
      checking.read handle = some [] ∧
      (∀ other, other ≠ handle → checking.read other = before.read other) ∧
      checking.cells = before.cells := by
  obtain ⟨checking, checked, body, empty, others, cells⟩ :=
    submit_body_returns_of_service before handle stored state command answer session current allocated shaped service
  refine ⟨checking, checked, ?_, by simp [NamedSpaces.Store.putCell], empty, others, cells⟩
  apply authored_variable_call_returns program bindings (environment command) before
    (checked.putCell "mm0-session" (ListAccess.optionValue answer)) "mm0:submit" [name]
    submitEquation.body _ (by decide) (by decide) (by decide +kernel) _ body (by decide)
  simpa [captured] using submit_clause command

/-- The same complete submit operation retains the child computation's
physical invariant, as well as the reset facts supplied to that child. -/
theorem submit_returns_with_frame (bindings : Subst) (before : State) (handle : Handle)
    (stored : List Atom) (state command : Atom) (answer : Option Atom) (name : String)
    (captured : applySubst bindings (.var name) = command)
    (session : before.cells "mm0-session" = some (.expression [.symbol "Some", state]))
    (current : before.cells InferenceCache.cell = some (handleValue handle))
    (allocated : before.read handle = some stored) (shaped : Effects.RowsHaveArity 4 stored)
    (frame : State → State → Prop)
    (service : ∀ (checking : State), checking.read handle = some [] →
      (∀ other, other ≠ handle → checking.read other = before.read other) →
      checking.cells = before.cells →
      ∃ (checked : State), PureReturns program (declarationEnvironment handle state command) checking
        (.expression [.symbol "mm0:service-step", .var "state", .var "command"])
        checked (ListAccess.optionValue answer) ∧ frame checking checked) :
    ∃ (checking checked : State),
      PureReturns program bindings before (.expression [.symbol "mm0:submit", .var name])
        (checked.putCell "mm0-session" (ListAccess.optionValue answer)) (boolean answer.isSome) ∧
      frame checking checked ∧ checking.read handle = some [] ∧
      (∀ other, other ≠ handle → checking.read other = before.read other) ∧
      checking.cells = before.cells := by
  obtain ⟨checking, resetPath, empty, others, cells⟩ :=
    submit_body_enters_after_reset before handle stored state command session current allocated shaped
  obtain ⟨checked, computed, framed⟩ := service checking empty others cells
  refine ⟨checking, checked, ?_, framed, empty, others, cells⟩
  have tail := declaration_tail_returns checking checked handle state command answer computed
  have lifted := path_with_caller_frames program
    [.sequence [] [], .sequence [] [], .sequence [] [], .sequence [] []] tail
  have body := path_trans resetPath (path_trans lifted (empty_sequences_return _ _ 4))
  apply authored_variable_call_returns program bindings (environment command) before
    (checked.putCell "mm0-session" (ListAccess.optionValue answer)) "mm0:submit" [name]
    submitEquation.body _ (by decide) (by decide) (by decide +kernel) _ body (by decide)
  simpa [captured] using submit_clause command

/-- Submission can also retain an observed child result together with its
physical frame. The child establishes the result; the driver stores exactly
that option and returns its Boolean status. -/
theorem submit_returns_with_result (bindings : Subst) (before : State) (handle : Handle)
    (stored : List Atom) (state command : Atom) (name : String)
    (captured : applySubst bindings (.var name) = command)
    (session : before.cells "mm0-session" = some (.expression [.symbol "Some", state]))
    (current : before.cells InferenceCache.cell = some (handleValue handle))
    (allocated : before.read handle = some stored) (shaped : Effects.RowsHaveArity 4 stored)
    (frame : State → State → Option Atom → Prop)
    (service : ∀ (checking : State), checking.read handle = some [] →
      (∀ other, other ≠ handle → checking.read other = before.read other) →
      checking.cells = before.cells →
      ∃ (checked : State) (answer : Option Atom),
        PureReturns program (declarationEnvironment handle state command) checking
          (.expression [.symbol "mm0:service-step", .var "state", .var "command"])
          checked (ListAccess.optionValue answer) ∧ frame checking checked answer) :
    ∃ (checking checked : State) (answer : Option Atom),
      PureReturns program bindings before (.expression [.symbol "mm0:submit", .var name])
        (checked.putCell "mm0-session" (ListAccess.optionValue answer)) (boolean answer.isSome) ∧
      frame checking checked answer ∧ checking.read handle = some [] ∧
      (∀ other, other ≠ handle → checking.read other = before.read other) ∧
      checking.cells = before.cells := by
  obtain ⟨checking, resetPath, empty, others, cells⟩ :=
    submit_body_enters_after_reset before handle stored state command session current allocated shaped
  obtain ⟨checked, answer, computed, framed⟩ := service checking empty others cells
  refine ⟨checking, checked, answer, ?_, framed, empty, others, cells⟩
  have tail := declaration_tail_returns checking checked handle state command answer computed
  have lifted := path_with_caller_frames program
    [.sequence [] [], .sequence [] [], .sequence [] [], .sequence [] []] tail
  have body := path_trans resetPath (path_trans lifted (empty_sequences_return _ _ 4))
  apply authored_variable_call_returns program bindings (environment command) before
    (checked.putCell "mm0-session" (ListAccess.optionValue answer)) "mm0:submit" [name]
    submitEquation.body _ (by decide) (by decide) (by decide +kernel) _ body (by decide)
  simpa [captured] using submit_clause command

/-- The source `None` branch does not run a command, clear a cache or change
a cell. This statement holds for arbitrary supplied command data. -/
theorem refused_submit_body_returns (before : State) (command : Atom)
    (failed : before.cells "mm0-session" = some (.symbol "None")) :
    PureReturns program (environment command) before submitEquation.body before (boolean false) := by
  rw [body_shape]
  let bindings := environment command
  let bound := ("current", .symbol "None") :: bindings
  apply let_returns program bindings bound before before before (.var "current") _ _
    (.symbol "None") _ (cell_returns before bindings "mm0-session" _ failed)
  · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, bound, bindings, environment]
  · rw [current_body_shape]
    apply case_returns program bound bound before before before (.var "current")
      (.symbol "None") (boolean false) _ _ cases (read_cases_encoded _)
    · simpa [bound, applySubst, Subst.lookup] using variable_returns program bound before "current"
    · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
    · exact grounded_returns program bound before (.bool false)

theorem refused_submit_returns (bindings : Subst) (before : State) (command : Atom)
    (name : String) (captured : applySubst bindings (.var name) = command)
    (failed : before.cells "mm0-session" = some (.symbol "None")) :
    PureReturns program bindings before (.expression [.symbol "mm0:submit", .var name])
      before (boolean false) := by
  apply authored_variable_call_returns program bindings (environment command) before before
    "mm0:submit" [name] submitEquation.body _ (by decide) (by decide) (by decide) _
    (refused_submit_body_returns before command failed) (by decide)
  simpa [captured] using submit_clause command

private def finishEquation : SpaceSemantics.Equation := serviceSource.program.equations[5]'(by decide)
private def finishBody : Atom :=
  match finishEquation.body with
  | .expression [_, _, _, body] => body
  | _ => .expression []
private def finishCases : SpaceSemantics.Cases :=
  match finishBody with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def finishActiveBody : Atom := (finishCases[0]'(by decide)).2

private theorem finish_body_shape : finishEquation.body =
    .expression [.symbol "let", .var "current",
      .expression [.symbol "get-state", .symbol "mm0-session"], finishBody] := by decide +kernel
private theorem finish_case_shape : finishBody =
    .expression [.symbol "case", .var "current",
      .expression (finishCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem finish_cases_shape :
    finishCases = [(.expression [.symbol "Some", .var "state"], finishActiveBody), (.symbol "None", boolean false),
      (.var "malformed", .symbol "MM0:Malformed")] := by decide +kernel
private theorem finish_unique :
    program.equations.filter (fun row => row.head == "mm0:finish") = [finishEquation] := by decide +kernel
private theorem finish_formals : finishEquation.arguments = [] := by decide +kernel

theorem refused_finish_returns (bindings : Subst) (before : State)
    (failed : before.cells "mm0-session" = some (.symbol "None")) :
    PureReturns program bindings before (.expression [.symbol "mm0:finish"])
      before (boolean false) := by
  have body : PureReturns program [] before finishEquation.body before (boolean false) := by
    rw [finish_body_shape]
    let bound : Subst := [("current", .symbol "None")]
    apply let_returns program [] bound before before before (.var "current") _ _
      (.symbol "None") _ (cell_returns before [] "mm0-session" _ failed)
    · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, bound]
    · rw [finish_case_shape]
      apply case_returns program bound bound before before before (.var "current")
        (.symbol "None") (boolean false) _ _ finishCases (read_cases_encoded _)
      · simpa [bound, applySubst, Subst.lookup] using variable_returns program bound before "current"
      · simp [finish_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          matchAtom]
      · exact grounded_returns program bound before (.bool false)
  apply authored_variable_call_returns program bindings [] before before "mm0:finish" []
    finishEquation.body _ (by decide) (by decide) (by decide +kernel) _ body (by decide)
  rw [clauses_use_only_the_named_equations, finish_unique]
  simp [finish_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues]

theorem refusal_cannot_reopen (bindings : Subst) (before : State) (command : Atom)
    (name : String) (captured : applySubst bindings (.var name) = command)
    (failed : before.cells "mm0-session" = some (.symbol "None")) :
    (∃ fuel, run program fuel
        { state := before, control := .evaluate bindings (.expression [.symbol "mm0:submit", .var name]) } =
        .complete before [boolean false] [] []) ∧
      (∃ fuel, run program fuel
        { state := before, control := .evaluate bindings (.expression [.symbol "mm0:finish"]) } =
        .complete before [boolean false] [] []) :=
  ⟨pure_returns_has_sufficient_fuel program bindings before before _ _
      (refused_submit_returns bindings before command name captured failed),
    pure_returns_has_sufficient_fuel program bindings before before _ _
      (refused_finish_returns bindings before failed)⟩

/-- A completed submission from a refused session has the original store,
even when the supplied command contains an executable-looking expression. -/
theorem completed_refusal_preserves_store (bindings : Subst) (before : State)
    (command : Atom) (name : String) (captured : applySubst bindings (.var name) = command)
    (failed : before.cells "mm0-session" = some (.symbol "None"))
    (fuel : Nat) (after : State) (answers input output : List Atom)
    (completed : run program fuel
      { state := before, control := .evaluate bindings (.expression [.symbol "mm0:submit", .var name]) } =
      .complete after answers input output) :
    after = before ∧ answers = [boolean false] ∧ input = [] ∧ output = [] := by
  obtain ⟨referenceFuel, reference⟩ :=
    (refusal_cannot_reopen bindings before command name captured failed).1
  exact completed_result_unique program fuel referenceFuel _ after before
    answers input output [boolean false] [] [] completed reference

end Mettapedia.Languages.MM0.MeTTa.DeclarationScope
