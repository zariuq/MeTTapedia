import Mettapedia.Languages.MeTTa.PeTTa.Bridges.BoundQueryPattern
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshInsertionContinuation

/-!
# Fresh constructor rows at the actual source boundary

The guard matches the authored constructor pattern using current bindings;
the insertion passes that same pattern through the native raw-argument slot.
No extra source `let` or evaluation of the row as a function is introduced.
The inert guard payload remains authored, including `t` or false.

Preparation checks a complete read and refuses relevant open rows or program
declarations. These laws concern completed stateful, no-I/O execution. They
do not by themselves authorize native publication or recursive dispatch.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshConstructorSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Eval SpaceSemantics NamedSpaces EffectfulQuerySource
open FlatQueryRelationCompilation (sourceScan)

def query (spaceName : String) (pattern payload : Atom) : Atom :=
  .expression [.symbol "match", .var spaceName, pattern, payload]

def absent (spaceName : String) (pattern payload : Atom) : Atom :=
  .expression [.symbol "==", .expression [.symbol "collapse", query spaceName pattern payload], .expression []]

def source (spaceName temporary : String) (pattern payload continuation : Atom) : Atom :=
  FreshInsertionContinuation.guardedSource (absent spaceName pattern payload)
    (.expression [.symbol "add-atom", .var spaceName, pattern]) temporary continuation

theorem query_returns (program : Program) (bindings : Subst) (state : Effects.State)
    (spaceName : String) (pattern payload : Atom) (handle : Handle) (rows : List Atom)
    (scalar : ConstantQuerySource.Scalar payload)
    (location : Subst.lookup bindings spaceName = some (Effects.handleValue handle))
    (snapshot : state.read handle = some rows) :
    Returns program bindings state (query spaceName pattern payload) state
      ((sourceScan bindings pattern 0 rows).map fun _ => payload) := by
  have space : PureReturns program bindings state (.var spaceName) state (Effects.handleValue handle) := by
    simpa only [applySubst, location, Option.getD_some] using variable_returns program bindings state spaceName
  have result := CapturedQuerySource.match_returns program state bindings (.var spaceName)
    (Effects.handleValue handle) rows space (by simp [snapshot]) pattern payload (fun _ => [payload])
    (fun _ _ bound _ => by cases scalar with
      | symbol name => exact symbol_returns program bound state name
      | grounded value => exact grounded_returns program bound state value)
  simpa only [query, ← List.map_eq_flatMap] using result

theorem scan_empty_iff {bindings : Subst} {pattern : Atom} (captured : BoundQueryPattern.Captured bindings pattern)
    (rows : List Atom) (start : Nat) :
    sourceScan bindings pattern start rows = [] ↔ applySubst bindings pattern ∉ rows := by
  induction rows generalizing start with
  | nil => simp [sourceScan]
  | cons row rows ih =>
      by_cases same : applySubst bindings pattern = row
      · simp [sourceScan, captured.match_exact, same]
      · simp [sourceScan, captured.match_exact, same, ih]

theorem absent_returns (program : Program) (bindings : Subst) (state : Effects.State)
    (spaceName : String) (pattern payload : Atom) (handle : Handle) (rows : List Atom)
    (captured : BoundQueryPattern.Captured bindings pattern) (scalar : ConstantQuerySource.Scalar payload)
    (location : Subst.lookup bindings spaceName = some (Effects.handleValue handle))
    (snapshot : state.read handle = some rows) :
    PureReturns program bindings state (absent spaceName pattern payload) state
      (Effects.boolean (decide (applySubst bindings pattern ∉ rows))) := by
  have collected := collapse_returns program bindings state state _ _
    (query_returns program bindings state spaceName pattern payload handle rows scalar location snapshot)
  have emptyReturns : PureReturns program bindings state (.expression []) state (.expression []) :=
    .step (step_transition rfl) (.step (step_transition rfl) (.refl _))
  have equal : ((Atom.expression ((sourceScan bindings pattern 0 rows).map fun _ => payload)) ==
      Atom.expression []) = decide (applySubst bindings pattern ∉ rows) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, Atom.expression.injEq, List.map_eq_nil_iff, decide_eq_true_eq]
    exact scan_empty_iff captured rows 0
  exact native_binary_call_returns program bindings state state state state "==" _ _ _ _ _
    (by decide) (by decide)
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument])
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument]) collected emptyReturns
    (by simp only [StdLib.structural_equality, equal]) (by decide)

theorem insert_returns (program : Program) (bindings : Subst) (before after : Effects.State)
    (spaceName : String) (pattern : Atom) (handle : Handle)
    (location : Subst.lookup bindings spaceName = some (Effects.handleValue handle))
    (inserted : Effects.insert before handle (applySubst bindings pattern) = some after) :
    PureReturns program bindings before (.expression [.symbol "add-atom", .var spaceName, pattern])
      after (Effects.boolean true) := by
  have applied : StdLib.apply before "add-atom" [Effects.handleValue handle, applySubst bindings pattern] =
      .ok (after, [Effects.boolean true]) := by
    change (match Effects.readHandle (Effects.handleValue handle) >>= fun chosen =>
      Effects.insert before chosen (applySubst bindings pattern) with
      | some result => Except.ok (result, [Effects.boolean true])
      | none => Except.error Effects.Fault.invalidSpace) = _
    rw [Effects.readHandle_handleValue]
    change (match Effects.insert before handle (applySubst bindings pattern) with
      | some result => Except.ok (result, [Effects.boolean true])
      | none => Except.error Effects.Fault.invalidSpace) = _
    rw [inserted]
  have native := native_function_arguments_return program bindings before after "add-atom"
    [Effects.handleValue handle, applySubst bindings pattern] 2 (Effects.boolean true) (by decide) (by decide) applied
  have raw := raw_argument_answers program bindings before after "add-atom" pattern []
    [Effects.handleValue handle] 1 [Effects.boolean true]
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument]) native
  have arguments := variable_prefix_arguments_answers program bindings before after (.function "add-atom")
    [spaceName] [pattern] [] 0 [Effects.boolean true]
    (by simpa [applySubst, location] using raw)
  exact call_returns program bindings before after "add-atom" [.var spaceName, pattern] (Effects.boolean true)
    (by simp [StdLib.known]) arguments (by decide)

theorem returns (program : Program) (spaceName temporary : String) (pattern payload continuation : Atom)
    (target : Handle) (body : Body) (bindings : Subst) (before after : Effects.State) (answers : List Atom)
    (captured : BoundQueryPattern.Captured bindings pattern) (scalar : ConstantQuerySource.Scalar payload)
    (location : Subst.lookup bindings spaceName = some (Effects.handleValue target))
    (fresh : Subst.lookup bindings temporary = none)
    (law : ∀ current next values,
      body ((temporary, Effects.boolean true) :: bindings) current = some (next, values) →
      Returns program ((temporary, Effects.boolean true) :: bindings) current continuation next values)
    (completed : FreshInsertionContinuation.run target (applySubst bindings pattern) temporary body bindings before =
      some (after, answers)) :
    Returns program bindings before (source spaceName temporary pattern payload continuation) after answers :=
  FreshInsertionContinuation.returns_using program _ _ temporary continuation target (applySubst bindings pattern)
    body bindings before after answers
    (fun rows snapshot => absent_returns program bindings before spaceName pattern payload target rows
      captured scalar location snapshot)
    (fun middle written => insert_returns program bindings before middle spaceName pattern target location written)
    fresh law completed

structure Prepared (bindings : Subst) (pattern : Atom) (target : Handle) (state : Effects.State) : Type where
  captured : BoundQueryPattern.Captured bindings pattern
  rows : List Atom
  snapshot : state.read target = some rows
  closedRows : ClosedQueryAdmission.rowsReady (applySubst bindings pattern) rows = true
  dataRow : GuardedInsertionSource.dataRow (applySubst bindings pattern) = true

def prepare (bindings : Subst) (pattern : Atom) (target : Handle) (state : Effects.State) :
    Option (Prepared bindings pattern target state) := do
  let captured ← BoundQueryPattern.capture bindings pattern
  match snapshot : state.read target with
  | none => none
  | some rows =>
      if closedRows : ClosedQueryAdmission.rowsReady (applySubst bindings pattern) rows = true then
        if dataRow : GuardedInsertionSource.dataRow (applySubst bindings pattern) = true then
          some ⟨captured, rows, snapshot, closedRows, dataRow⟩
        else none
      else none

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshConstructorSource
