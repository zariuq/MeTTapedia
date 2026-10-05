import Mettapedia.Languages.MM0.MeTTa.InferenceCache

/-!
# Reset before a declaration check

The checkpoint below is reached by the actual `mm0:submit` body. Its next
computation is the retained `mm0:service-step` call, and the inference cache
has already been emptied. All other spaces and state cells are unchanged.

The reset establishes a coherent cache for the current signature even when
the previous rows were stale or malformed. Preservation of that signature
through all checking families and ordered admission remain session obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.DeclarationScope

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open SourceEvaluation SourceExecution
open SourcePrimitives (State boolean handleValue)
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

private def cases : SourceProgram.Cases :=
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
      .expression [.symbol "mm0:clear-space", .var "cache"], declarationBody] := by decide

private theorem declaration_body_shape :
    declarationBody = .expression [.symbol "let", .var "answer",
      .expression [.symbol "mm0:service-step", .var "state", .var "command"], admittedBody] := by decide

private theorem cell_returns (before : State) (bindings : Subst) (name : String) (value : Atom)
    (present : before.cells name = some value) :
    PureReturns program bindings before (.expression [.symbol "get-state", .symbol name]) before value := by
  apply native_unary_call_returns program bindings before before before "get-state" (.symbol name)
    (.symbol name) value (by decide) (by decide) (by decide)
    (symbol_returns program bindings before name) _ (by decide)
  simp [SourcePrimitives.apply, present]

private theorem active_body_enters (before : State) (handle : Handle) (stored : List Atom)
    (state command : Atom)
    (current : before.cells InferenceCache.cell = some (handleValue handle))
    (allocated : before.read handle = some stored) :
    ∃ after, (theory program).MultiStep
        { state := before, control := .evaluate (checkingEnvironment state command) activeBody }
        { state := after, control := .evaluate (declarationEnvironment handle state command) declarationBody,
          frames := [.sequence [] [], .sequence [] []] } ∧
      after.read handle = some [] ∧
      (∀ other, other ≠ handle → after.read other = before.read other) ∧
      after.cells = before.cells := by
  obtain ⟨after, clear, empty, others, cells⟩ := SpaceClearing.clear_returns
    (cacheEnvironment handle state command) before handle stored "cache" allocated
    (by simp [cacheEnvironment, applySubst, Subst.lookup])
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
    · simp [SourceProgram.matchValue, matchAtom, checkingEnvironment, currentEnvironment,
        environment, cacheEnvironment, Subst.lookup]
    · rw [cache_body_shape]
      apply let_enters program (cacheEnvironment handle state command)
        (declarationEnvironment handle state command) before after (.var "set") _ declarationBody
        (boolean true) clear
      simp [SourceProgram.matchValue, matchAtom, cacheEnvironment, checkingEnvironment,
        currentEnvironment, environment, declarationEnvironment, Subst.lookup]
  simpa [withFrames] using reached

/-- Before the actual declaration check can begin, the old cache rows have
been removed. The path makes no assumption about that check's answer. -/
theorem submit_body_enters_after_reset (before : State) (handle : Handle) (stored : List Atom)
    (state command : Atom)
    (session : before.cells "mm0-session" = some (.expression [.symbol "Some", state]))
    (current : before.cells InferenceCache.cell = some (handleValue handle))
    (allocated : before.read handle = some stored) :
    ∃ after, (theory program).MultiStep
        { state := before, control := .evaluate (environment command) submitEquation.body }
        (checkpoint after handle state command) ∧
      after.read handle = some [] ∧
      (∀ other, other ≠ handle → after.read other = before.read other) ∧
      after.cells = before.cells := by
  obtain ⟨after, checking, empty, others, cells⟩ :=
    active_body_enters before handle stored state command current allocated
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
    · simp [SourceProgram.matchValue, matchAtom, environment, Subst.lookup, currentEnvironment]
    · rw [current_body_shape]
      apply case_reaches program (currentEnvironment state command) (checkingEnvironment state command)
        before before (.var "current") (.expression [.symbol "Some", state]) activeBody _ cases _
        (read_cases_encoded cases) _ _ checking
      · simpa [currentEnvironment, applySubst, Subst.lookup] using
          variable_returns program (currentEnvironment state command) before "current"
      · simp [cases_shape, SourceProgram.selectCase, SourceProgram.matchValue,
          SourceProgram.matchValue.matchValues, matchAtom, currentEnvironment, environment,
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
    (allocated : before.read handle = some stored) :
    ∃ after, (theory program).MultiStep
        { state := before, control := .evaluate (environment command) submitEquation.body }
        (checkpoint after handle state command) ∧
      InferenceCache.Ready signature terms handle after ∧
      (∀ other, other ≠ handle → after.read other = before.read other) ∧
      after.cells = before.cells := by
  obtain ⟨after, path, empty, others, cells⟩ :=
    submit_body_enters_after_reset before handle stored state command session current allocated
  refine ⟨after, path, ⟨?_, [], empty, InferenceCache.empty_valid signature terms⟩, others, cells⟩
  rw [cells]
  exact current

theorem checkpoint_preserves_request (handle : Handle) (state command : Atom) :
    applySubst (declarationEnvironment handle state command) (.var "state") = state ∧
      applySubst (declarationEnvironment handle state command) (.var "command") = command := by
  simp [declarationEnvironment, cacheEnvironment, checkingEnvironment, currentEnvironment,
    environment, applySubst, Subst.lookup]

end Mettapedia.Languages.MM0.MeTTa.DeclarationScope
