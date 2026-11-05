import Mettapedia.Languages.MeTTa.PeTTa.BoundCallComposition
import Mettapedia.Languages.MeTTa.PeTTa.PureData

/-!
# Source execution certificates shared by the two call fragments

The certificate records existing declarative transitions and checks that
captured dispatch does not replace any of them. These compositional laws
construct certificates from source operations. One certificate therefore
provides both the original execution and its conservative captured-call
execution, without asserting whole-program evaluator equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.BoundCalls.CorePath

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open SpaceSemantics (Program)
open Eval (Configuration Control Frame Target finished withFrames)
open Effects (State)

abbrev Returns (program : Program) (bindings : Subst)
    (before : State) (expression : Atom) (after : State) (answers : List Atom) : Prop :=
  CorePath program { state := before, control := .evaluate bindings expression }
    (finished after answers [] [])

abbrev PureReturns (program : Program) (bindings : Subst)
    (before : State) (expression : Atom) (after : State) (answer : Atom) : Prop :=
  Returns program bindings before expression after [answer]

theorem variable_returns (program : Program) (bindings : Subst) (state : State) (name : String) :
    PureReturns program bindings state (.var name) state (applySubst bindings (.var name)) :=
  .step rfl (Eval.step_transition rfl) (.refl _)

theorem symbol_returns (program : Program) (bindings : Subst) (state : State) (name : String) :
    PureReturns program bindings state (.symbol name) state (.symbol name) :=
  .step rfl (Eval.step_transition rfl) (.refl _)

theorem grounded_returns (program : Program) (bindings : Subst) (state : State)
    (value : Mettapedia.Languages.MeTTa.OSLFCore.GroundedValue) :
    PureReturns program bindings state (.grounded value) state (.grounded value) :=
  .step rfl (Eval.step_transition rfl) (.refl _)

theorem quote_returns (program : Program) (bindings : Subst) (state : State) (code : Atom) :
    PureReturns program bindings state (.expression [.symbol "quote", code]) state (applySubst bindings code) :=
  .step rfl (.quote_enter rfl) (.refl _)

/-- The source sequential-binding form contributes one administrative step;
all computation is retained in the certificate for its nested lets. -/
theorem let_star_returns (program : Program) (bindings : Subst)
    (before after : State) (pairs : List Atom) (body nested answer : Atom)
    (expanded : Eval.nestedLets pairs body = some nested)
    (returned : PureReturns program bindings before nested after answer) :
    PureReturns program bindings before
      (.expression [.symbol "let*", .expression pairs, body]) after answer := by
  refine .step rfl ?_ returned
  apply Eval.step_transition
  simp [Eval.step, expanded]

theorem starts_unchanged {program : Program} {source selected : Configuration}
    (path : CorePath program source selected) (different : source ≠ selected) :
    target program source.control = none := by
  cases path with
  | refl => exact False.elim (different rfl)
  | step unchanged => exact unchanged

/-- Pending sequence frames retain ordered occurrences until they are returned.
Discharging them neither drops duplicate answers nor repeats an effect. -/
theorem discharge_caller_cells (program : Program) (state : State) (answers : List Atom) (count : Nat) :
    CorePath program (withFrames (finished state answers [] []) (callerCells count))
      (finished state answers [] []) := by
  induction count with
  | zero => exact .refl _
  | succ count ih =>
      refine .step (middle := { state, control := .sequence [] answers, frames := callerCells count })
        rfl ?_ (.step rfl (Eval.step_transition rfl) ih)
      apply Eval.step_transition
      simp [withFrames, finished, callerCells, List.replicate_succ, Eval.step]

theorem case_returns (program : Program) (bindings bound : Subst)
    (before middle after : State) (expression value body answer : Atom)
    (rows : List Atom) (cases : SpaceSemantics.Cases)
    (decoded : Eval.readCases rows = some cases)
    (computed : PureReturns program bindings before expression middle value)
    (selected : SpaceSemantics.selectCase bindings value cases = some (bound, body))
    (continued : PureReturns program bound middle body after answer) :
    PureReturns program bindings before
      (.expression [.symbol "case", expression, .expression rows]) after answer := by
  have finish := (continued.with_caller_frames (callerCells 1)).trans
    (discharge_caller_cells program after [answer] 1)
  refine .step rfl ?_ ((computed.with_caller_frames [.select bindings cases]).trans ?_)
  · apply Eval.step_transition
    simp [Eval.step, decoded, withFrames]
  · refine .step (middle := { state := middle, control := .sequence [.evaluate bound body] [] })
      rfl ?_ (.step rfl (Eval.step_transition rfl) finish)
    apply Eval.step_transition
    simp [withFrames, finished, Eval.step, selected]

theorem if_returns (program : Program) (bindings : Subst)
    (before middle after : State) (condition value yes no answer : Atom)
    (computed : PureReturns program bindings before condition middle value)
    (continued : PureReturns program bindings middle
      (if value == Effects.boolean true then yes else no) after answer) :
    PureReturns program bindings before
      (.expression [.symbol "if", condition, yes, no]) after answer := by
  have finish := (continued.with_caller_frames (callerCells 1)).trans
    (discharge_caller_cells program after [answer] 1)
  refine .step rfl (Eval.step_transition rfl)
    ((computed.with_caller_frames [.branch bindings yes no]).trans ?_)
  exact .step rfl (Eval.step_transition rfl)
    (.step rfl (Eval.step_transition rfl) finish)

/-- A unique source clause is entered by certified argument capture. Its body
certificate then composes with the exact suspended caller stack. -/
theorem authored_variable_call_returns (program : Program) (bindings callee : Subst)
    (before after : State) (head : String) (names : List String) (body answer : Atom)
    (notIO : Eval.ioHead head = false) (notNative : StdLib.known head = false)
    (registered : program.equations.any (·.head == head) = true)
    (selected : Eval.clauses program head
      (names.map (fun name => applySubst bindings (.var name))) = [.evaluate callee body])
    (computed : PureReturns program callee before body after answer)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"]) :
    PureReturns program bindings before
      (.expression (.symbol head :: names.map Atom.var)) after answer := by
  have shape : DeclarativeSpec.controlForm (.expression (.symbol head :: names.map Atom.var)) = false := by
    exact Eval.controlForm_of_ordinary ordinary
  exact (authored_call_enters program bindings callee before head names body shape notIO notNative registered selected).trans
    ((computed.with_caller_frames (callerCells (names.length + 1))).trans
      (discharge_caller_cells program after [answer] (names.length + 1)))

theorem native_variable_call_returns (program : Program) (bindings : Subst)
    (before after : State) (head : String) (names : List String) (answer : Atom)
    (notIO : Eval.ioHead head = false) (native : StdLib.known head = true)
    (computed : StdLib.apply before head
      (names.map (fun name => applySubst bindings (.var name))) = .ok (after, [answer]))
    (ordinary : head ∉
      ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"]) :
    PureReturns program bindings before
      (.expression (.symbol head :: names.map Atom.var)) after answer := by
  have shape : DeclarativeSpec.controlForm (.expression (.symbol head :: names.map Atom.var)) = false := by
    exact Eval.controlForm_of_ordinary ordinary
  have arguments := variable_prefix_enters program bindings before (.function head) names [] [] 0
  have finish : CorePath program
      { state := before, control := .arguments bindings (.function head) []
          (names.map (fun name => applySubst bindings (.var name))) names.length }
      (finished after [answer] [] []) := by
    refine .step rfl ?_ (.refl _)
    apply Eval.step_transition
    simp [Eval.step, notIO, native, computed, finished]
  have framed : CorePath program
      { state := before, control := .arguments bindings (.function head) []
          ([] ++ names.map (fun name => applySubst bindings (.var name)))
          (0 + names.length), frames := callerCells names.length }
      (withFrames (finished after [answer] [] []) (callerCells names.length)) := by
    simpa [withFrames] using finish.with_caller_frames (callerCells names.length)
  refine .step rfl (DeclarativeSpec.Transition.call_enter rfl shape (by simp [native])) ?_
  simpa only [List.append_nil] using
    (arguments.trans framed).trans (discharge_caller_cells program after [answer] names.length)

theorem strict_argument_enters (program : Program) (bindings : Subst)
    (before after : State) (destination : Target) (expression value : Atom)
    (remaining values : List Atom) (index : Nat)
    (demanded : (match destination with
      | .function head => Eval.argumentIsRaw program head index
      | .data => false) = false)
    (computed : PureReturns program bindings before expression after value) :
    CorePath program
      { state := before, control := .arguments bindings destination (expression :: remaining) values index }
      { state := after, control := .arguments bindings destination remaining (values ++ [value]) (index + 1),
        frames := callerCells 1 } := by
  have finish : CorePath program
      (withFrames (finished after [value] [] []) [.argument bindings destination remaining values index])
      { state := after, control := .arguments bindings destination remaining (values ++ [value]) (index + 1),
        frames := callerCells 1 } :=
    .step rfl (Eval.step_transition rfl) (.step rfl (Eval.step_transition rfl) (.refl _))
  refine .step rfl ?_ ((computed.with_caller_frames [.argument bindings destination remaining values index]).trans finish)
  apply Eval.step_transition
  simp [Eval.step, withFrames]
  exact demanded

/-- Strict argument execution composes through the actual pending caller.
The continuation receives one occurrence at its original position. -/
theorem evaluated_argument_returns (program : Program) (bindings : Subst)
    (before middle after : State) (destination : Target) (argument value answer : Atom)
    (arguments values : List Atom) (index : Nat)
    (demanded : (match destination with
      | .function head => Eval.argumentIsRaw program head index
      | .data => false) = false)
    (first : PureReturns program bindings before argument middle value)
    (rest : CorePath program
      { state := middle, control := .arguments bindings destination arguments
          (values ++ [value]) (index + 1) }
      (finished after [answer] [] [])) :
    CorePath program
      { state := before, control := .arguments bindings destination (argument :: arguments) values index }
      (finished after [answer] [] []) :=
  (strict_argument_enters program bindings before middle destination argument value arguments values index
    demanded first).trans
    ((rest.with_caller_frames (callerCells 1)).trans
      (discharge_caller_cells program after [answer] 1))

/-- An application that is not control syntax enters the call of its head. -/
theorem application_returns (program : Program) (bindings : Subst)
    (before after : State) (head : String) (arguments : List Atom) (answer : Atom)
    (dispatch : (Eval.ioHead head || StdLib.known head ||
      program.equations.any (·.head == head)) = true)
    (computed : CorePath program
      { state := before, control := .arguments bindings (.function head) arguments [] 0 }
      (finished after [answer] [] []))
    (notControl : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false) :
    PureReturns program bindings before (.expression (.symbol head :: arguments)) after answer :=
  .step rfl (DeclarativeSpec.Transition.call_enter rfl notControl dispatch) computed

theorem call_returns (program : Program) (bindings : Subst)
    (before after : State) (head : String) (arguments : List Atom) (answer : Atom)
    (dispatch : (Eval.ioHead head || StdLib.known head ||
      program.equations.any (·.head == head)) = true)
    (computed : CorePath program
      { state := before, control := .arguments bindings (.function head) arguments [] 0 }
      (finished after [answer] [] []))
    (ordinary : head ∉
      ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"]) :
    PureReturns program bindings before (.expression (.symbol head :: arguments)) after answer :=
  application_returns program bindings before after head arguments answer dispatch computed
    (Eval.controlForm_of_ordinary ordinary)

theorem authored_function_arguments_return (program : Program) (bindings callee : Subst)
    (before after : State) (head : String) (values : List Atom) (index : Nat)
    (body answer : Atom) (ordinary : Eval.ioHead head = false)
    (authored : StdLib.known head = false)
    (selected : Eval.clauses program head values = [.evaluate callee body])
    (computed : PureReturns program callee before body after answer) :
    CorePath program
      { state := before, control := .arguments bindings (.function head) [] values index }
      (finished after [answer] [] []) := by
  have finish := (computed.with_caller_frames (callerCells 1)).trans
    (discharge_caller_cells program after [answer] 1)
  refine .step (middle := { state := before, control := .sequence [.evaluate callee body] [] })
    rfl ?_ (.step rfl (Eval.step_transition rfl) finish)
  apply Eval.step_transition
  simp [Eval.step, ordinary, authored, selected]

theorem native_function_arguments_return (program : Program) (bindings : Subst)
    (before after : State) (head : String) (values : List Atom) (index : Nat) (answer : Atom)
    (ordinary : Eval.ioHead head = false) (native : StdLib.known head = true)
    (computed : StdLib.apply before head values = .ok (after, [answer])) :
    CorePath program
      { state := before, control := .arguments bindings (.function head) [] values index }
      (finished after [answer] [] []) := by
  refine .step rfl ?_ (.refl _)
  apply Eval.step_transition
  simp [Eval.step, ordinary, native, computed, finished]

theorem native_binary_call_returns (program : Program) (bindings : Subst)
    (before firstState secondState after : State) (head : String)
    (left right leftValue rightValue answer : Atom)
    (ordinary : Eval.ioHead head = false) (native : StdLib.known head = true)
    (leftDemanded : Eval.argumentIsRaw program head 0 = false)
    (rightDemanded : Eval.argumentIsRaw program head 1 = false)
    (leftReturns : PureReturns program bindings before left firstState leftValue)
    (rightReturns : PureReturns program bindings firstState right secondState rightValue)
    (computed : StdLib.apply secondState head [leftValue, rightValue] = .ok (after, [answer]))
    (notControl : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"]) :
    PureReturns program bindings before (.expression [.symbol head, left, right]) after answer := by
  apply application_returns program bindings before after head [left, right] answer (by simp [native]) _
    (Eval.controlForm_of_ordinary notControl)
  have last := native_function_arguments_return program bindings secondState after head
    [leftValue, rightValue] 2 answer ordinary native computed
  have rest := evaluated_argument_returns program bindings firstState secondState after (.function head)
    right rightValue answer [] [leftValue] 1 rightDemanded rightReturns last
  exact evaluated_argument_returns program bindings before firstState after (.function head)
    left leftValue answer [right] [] 0 leftDemanded leftReturns rest

theorem native_unary_call_returns (program : Program) (bindings : Subst)
    (before middle after : State) (head : String) (argument value answer : Atom)
    (ordinary : Eval.ioHead head = false) (native : StdLib.known head = true)
    (demanded : Eval.argumentIsRaw program head 0 = false)
    (argumentReturns : PureReturns program bindings before argument middle value)
    (computed : StdLib.apply middle head [value] = .ok (after, [answer]))
    (notControl : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"]) :
    PureReturns program bindings before (.expression [.symbol head, argument]) after answer := by
  apply application_returns program bindings before after head [argument] answer (by simp [native]) _
    (Eval.controlForm_of_ordinary notControl)
  exact evaluated_argument_returns program bindings before middle after (.function head) argument value answer
    [] [] 0 demanded argumentReturns
    (native_function_arguments_return program bindings middle after head [value] 1 answer ordinary native computed)

theorem authored_unary_call_returns (program : Program) (bindings callee : Subst)
    (before middle after : State) (head : String) (argument value body answer : Atom)
    (ordinary : Eval.ioHead head = false) (authored : StdLib.known head = false)
    (registered : program.equations.any (·.head == head) = true)
    (demanded : Eval.argumentIsRaw program head 0 = false)
    (argumentReturns : PureReturns program bindings before argument middle value)
    (selected : Eval.clauses program head [value] = [.evaluate callee body])
    (computed : PureReturns program callee middle body after answer)
    (notControl : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"]) :
    PureReturns program bindings before (.expression [.symbol head, argument]) after answer := by
  apply application_returns program bindings before after head [argument] answer (by simp [registered]) _
    (Eval.controlForm_of_ordinary notControl)
  exact evaluated_argument_returns program bindings before middle after (.function head) argument value answer
    [] [] 0 demanded argumentReturns
    (authored_function_arguments_return program bindings callee middle after head [value] 1 body answer
      ordinary authored selected computed)

theorem authored_binary_call_returns (program : Program) (bindings callee : Subst)
    (before firstState secondState after : State) (head : String)
    (left right leftValue rightValue body answer : Atom)
    (ordinary : Eval.ioHead head = false) (authored : StdLib.known head = false)
    (registered : program.equations.any (·.head == head) = true)
    (leftDemanded : Eval.argumentIsRaw program head 0 = false)
    (rightDemanded : Eval.argumentIsRaw program head 1 = false)
    (leftReturns : PureReturns program bindings before left firstState leftValue)
    (rightReturns : PureReturns program bindings firstState right secondState rightValue)
    (selected : Eval.clauses program head [leftValue, rightValue] = [.evaluate callee body])
    (computed : PureReturns program callee secondState body after answer)
    (notControl : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"]) :
    PureReturns program bindings before (.expression [.symbol head, left, right]) after answer := by
  apply application_returns program bindings before after head [left, right] answer (by simp [registered]) _
    (Eval.controlForm_of_ordinary notControl)
  have last := authored_function_arguments_return program bindings callee secondState after head
    [leftValue, rightValue] 2 body answer ordinary authored selected computed
  have rest := evaluated_argument_returns program bindings firstState secondState after (.function head)
    right rightValue answer [] [leftValue] 1 rightDemanded rightReturns last
  exact evaluated_argument_returns program bindings before firstState after (.function head)
    left leftValue answer [right] [] 0 leftDemanded leftReturns rest

theorem data_arguments_values_return (program : Program) (bindings : Subst)
    (state : State) (values : List Atom) (index : Nat) :
    CorePath program { state, control := .arguments bindings .data [] values index }
      (finished state [.expression values] [] []) :=
  .step rfl (Eval.step_transition rfl) (.refl _)

theorem data_call_returns (program : Program) (bindings : Subst)
    (before after : State) (head : String) (arguments : List Atom) (answer : Atom)
    (inert : (Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head)) = false)
    (computed : CorePath program
      { state := before, control := .arguments bindings .data (.symbol head :: arguments) [] 0 }
      (finished after [answer] [] []))
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"]) :
    PureReturns program bindings before (.expression (.symbol head :: arguments)) after answer := by
  have shape : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false := by
    have notKnown : StdLib.known head = false := by
      simp only [Bool.or_eq_false_iff] at inert
      exact inert.1.2
    exact Eval.controlForm_of_ordinary ordinary
  exact .step rfl (DeclarativeSpec.Transition.data_enter rfl shape inert) computed

theorem binary_constructor_returns (program : Program) (bindings : Subst)
    (before middle after : State) (head : String) (left right leftValue rightValue : Atom)
    (inert : (Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head)) = false)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"])
    (first : PureReturns program bindings before left middle leftValue)
    (second : PureReturns program bindings middle right after rightValue) :
    PureReturns program bindings before (.expression [.symbol head, left, right]) after
      (.expression [.symbol head, leftValue, rightValue]) := by
  apply data_call_returns program bindings before after head [left, right] _ inert _ ordinary
  apply evaluated_argument_returns program bindings before before after .data (.symbol head) (.symbol head)
    _ [left, right] [] 0 rfl (symbol_returns program bindings before head)
  apply evaluated_argument_returns program bindings before middle after .data left leftValue _
    [right] [.symbol head] 1 rfl first
  exact evaluated_argument_returns program bindings middle after after .data right rightValue _
    [] [.symbol head, leftValue] 2 rfl second
    (data_arguments_values_return program bindings after [.symbol head, leftValue, rightValue] 3)

theorem unary_constructor_of_returns (program : Program) (bindings : Subst)
    (before after : State) (head : String) (expression value : Atom)
    (inert : (Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head)) = false)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"])
    (computed : PureReturns program bindings before expression after value) :
    PureReturns program bindings before (.expression [.symbol head, expression]) after
      (.expression [.symbol head, value]) := by
  apply data_call_returns program bindings before after head [expression] _ inert _ ordinary
  apply evaluated_argument_returns program bindings before before after .data (.symbol head) (.symbol head)
    _ [expression] [] 0 rfl (symbol_returns program bindings before head)
  exact evaluated_argument_returns program bindings before after after .data expression value _
    [] [.symbol head] 1 rfl computed (data_arguments_values_return program bindings after [.symbol head, value] 2)

/-- Pure constructor fields retain all ordered values, including repeated
occurrences and values containing executable heads. -/
theorem arguments_return (program : Program) (bindings : Subst)
    (state : State) (expressions values : List Atom)
    (computed : List.Forall₂ (fun expression value =>
      PureReturns program bindings state expression state value) expressions values)
    (accumulated : List Atom) (index : Nat) :
    CorePath program
      { state, control := .arguments bindings .data expressions accumulated index }
      (finished state [.expression (accumulated ++ values)] [] []) := by
  induction computed generalizing accumulated index with
  | nil => simpa using data_arguments_values_return program bindings state accumulated index
  | @cons expression value expressions values returned _ ih =>
      apply evaluated_argument_returns program bindings state state state .data expression value
        (.expression (accumulated ++ value :: values)) expressions accumulated index rfl returned
      simpa only [List.append_assoc, List.singleton_append] using ih (accumulated ++ [value]) (index + 1)

theorem constructor_return (program : Program) (bindings : Subst)
    (state : State) (head : String) (expressions values : List Atom)
    (inert : (Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head)) = false)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"])
    (computed : List.Forall₂ (fun expression value =>
      PureReturns program bindings state expression state value) expressions values) :
    PureReturns program bindings state (.expression (.symbol head :: expressions)) state
      (.expression (.symbol head :: values)) := by
  apply data_call_returns program bindings state state head expressions _ inert _ ordinary
  simpa using arguments_return program bindings state (.symbol head :: expressions) (.symbol head :: values)
    (.cons (symbol_returns program bindings state head) computed) [] 0

theorem literal_return (program : Program) (bindings : Subst)
    (state : State) (value : Atom) (literal : PureData.Literal program value) :
    PureReturns program bindings state value state value := by
  induction literal with
  | grounded value => exact grounded_returns program bindings state value
  | symbol name => exact symbol_returns program bindings state name
  | constructor head arguments inert ordinary _ ih =>
      apply constructor_return program bindings state head arguments arguments inert
        (fun member => ordinary (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; tauto))
      exact List.forall₂_same.mpr ih

theorem constructor_variables_return (program : Program) (bindings : Subst)
    (state : State) (head : String) (names : List String)
    (inert : (Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head)) = false)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"]) :
    PureReturns program bindings state (.expression (.symbol head :: names.map Atom.var)) state
      (.expression (.symbol head :: names.map fun name => applySubst bindings (.var name))) := by
  apply constructor_return program bindings state head _ _ inert ordinary
  induction names with
  | nil => exact .nil
  | cons name names ih => exact .cons (variable_returns program bindings state name) ih

/-- A non-call expression computes each field in order. Captured dispatch
must also be absent; nested expressions can still contain ordinary calls. -/
theorem expression_return (program : Program) (bindings : Subst) (state : State)
    (expressions values : List Atom)
    (notCall : ∀ head arguments, expressions ≠ .symbol head :: arguments)
    (unchanged : target program (.evaluate bindings (.expression expressions)) = none)
    (computed : List.Forall₂ (fun expression value =>
      PureReturns program bindings state expression state value) expressions values) :
    PureReturns program bindings state (.expression expressions) state (.expression values) := by
  refine .step unchanged (DeclarativeSpec.Transition.expression_enter rfl notCall) ?_
  simpa using arguments_return program bindings state expressions values computed [] 0

/-- Variable-headed tuples require a real dispatch guard: a captured ordinary
function is a computation, whereas a typed list or term field is data. -/
theorem tuple_variables_return (program : Program) (bindings : Subst) (state : State) (names : List String)
    (unchanged : target program (.evaluate bindings (.expression (names.map Atom.var))) = none) :
    PureReturns program bindings state (.expression (names.map Atom.var)) state
      (.expression (names.map fun name => applySubst bindings (.var name))) := by
  refine .step unchanged (DeclarativeSpec.Transition.expression_enter rfl ?_) ?_
  · intro head arguments
    cases names <;> simp
  · have captured : List.Forall₂ (fun expression value =>
        PureReturns program bindings state expression state value)
        (names.map Atom.var) (names.map fun name => applySubst bindings (.var name)) := by
      clear unchanged
      induction names with
      | nil => exact .nil
      | cons name names ih => exact .cons (variable_returns program bindings state name) ih
    simpa using arguments_return program bindings state (names.map Atom.var)
      (names.map fun name => applySubst bindings (.var name)) captured [] 0

/-- A captured value inside an inert constructor is returned as data. Its own
head is never executed merely because it is a constructor field. -/
theorem unary_constructor_returns (program : Program) (bindings : Subst)
    (state : State) (head name : String)
    (inert : (Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head)) = false)
    (notControl : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"]) :
    PureReturns program bindings state (.expression [.symbol head, .var name]) state
      (.expression [.symbol head, applySubst bindings (.var name)]) := by
  have ordinary : DeclarativeSpec.controlForm (.expression [.symbol head, .var name]) = false := by
    simp at notControl
    simp only [DeclarativeSpec.controlForm]
    split <;> simp_all
  have first := strict_argument_enters program bindings state state .data (.symbol head) (.symbol head)
    [.var name] [] 0 rfl (symbol_returns program bindings state head)
  have second := variable_prefix_enters program bindings state .data [name] [] [.symbol head] 1
  have rest := (second.with_caller_frames (callerCells 1))
  have values : CorePath program
      { state, control := .arguments bindings .data [] [.symbol head, applySubst bindings (.var name)] 2,
        frames := callerCells 2 }
      (finished state [.expression [.symbol head, applySubst bindings (.var name)]] [] []) := by
    refine .step rfl (Eval.step_transition rfl) ?_
    exact discharge_caller_cells program state [.expression [.symbol head, applySubst bindings (.var name)]] 2
  have composed := first.trans rest
  refine .step rfl (DeclarativeSpec.Transition.data_enter rfl ordinary inert) ?_
  apply CorePath.trans _ values
  simpa [withFrames, callerCells] using composed

end Mettapedia.Languages.MeTTa.PeTTa.BoundCalls.CorePath

namespace Mettapedia.Languages.MeTTa.PeTTa.BoundCalls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open SpaceSemantics (Program)
open Eval (Configuration Control finished withFrames)
open Effects (State)

/-- A body may itself use captured calls. The conservative call prefix still
composes with that body's actual extended execution and the retained frames. -/
theorem authored_variable_call_returns (program : Program) (bindings callee : Subst)
    (before after : State) (head : String) (names : List String) (body answer : Atom)
    (notIO : Eval.ioHead head = false) (notNative : StdLib.known head = false)
    (registered : program.equations.any (·.head == head) = true)
    (selected : Eval.clauses program head
      (names.map (fun name => applySubst bindings (.var name))) = [.evaluate callee body])
    (computed : PureReturns program callee before body after answer)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"]) :
    PureReturns program bindings before
      (.expression (.symbol head :: names.map Atom.var)) after answer := by
  have shape : DeclarativeSpec.controlForm (.expression (.symbol head :: names.map Atom.var)) = false := by
    exact Eval.controlForm_of_ordinary ordinary
  exact path_trans (CorePath.authored_call_enters program bindings callee before head names body
    shape notIO notNative registered selected).extended
    (path_trans (path_with_caller_frames program (callerCells (names.length + 1)) computed)
      (CorePath.discharge_caller_cells program after [answer] (names.length + 1)).extended)

/-- Replacing an admitted captured call by its ordinary literal head preserves
the whole completed computation, including its actual returned store. -/
theorem captured_returns_of_literal (program : Program) (bindings : Subst)
    (before after : State) (name head : String) (arguments : List Atom) (answers : List Atom)
    (captured : applySubst bindings (.var name) = .symbol head)
    (authorized : admitted program head arguments = true)
    (ordinary : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false)
    (computed : Returns program bindings before (.expression (.symbol head :: arguments)) after answers) :
    Returns program bindings before (.expression (.var name :: arguments)) after answers := by
  obtain ⟨fuel, completed⟩ := path_has_sufficient_fuel program computed after answers [] [] rfl
  cases fuel with
  | zero => simp [run, observation] at completed
  | succ fuel =>
      apply completed_has_path program (fuel + 1) _ after answers [] []
      have same := captured_literal_run program
        ({ state := before, control := .evaluate bindings (.expression (.symbol head :: arguments)) } : Configuration)
        bindings name head arguments fuel captured authorized ordinary
      exact same.trans completed

theorem if_returns (program : Program) (bindings : Subst)
    (before middle after : State) (condition value yes no answer : Atom)
    (computed : PureReturns program bindings before condition middle value)
    (continued : PureReturns program bindings middle
      (if value == Effects.boolean true then yes else no) after answer) :
    PureReturns program bindings before
      (.expression [.symbol "if", condition, yes, no]) after answer := by
  refine .step (.core rfl (Eval.step_transition rfl))
    (path_trans (path_with_caller_frames program [.branch bindings yes no] computed) ?_)
  exact .step (.core rfl (Eval.step_transition rfl))
    (single_sequence_returns program middle after _ answer continued)

theorem variable_prefix_arguments_return (program : Program) (bindings : Subst)
    (before after : State) (destination : Eval.Target) (names : List String)
    (remaining values : List Atom) (index : Nat) (answer : Atom)
    (computed : (theory program).MultiStep
      { state := before, control := .arguments bindings destination remaining
          (values ++ names.map (fun name => applySubst bindings (.var name)))
          (index + names.length) }
      (finished after [answer] [] [])) :
    (theory program).MultiStep
      { state := before, control := .arguments bindings destination
          (names.map Atom.var ++ remaining) values index }
      (finished after [answer] [] []) :=
  path_trans (CorePath.variable_prefix_enters program bindings before destination names remaining values index).extended
    (path_trans (path_with_caller_frames program (callerCells names.length) computed)
      (CorePath.discharge_caller_cells program after [answer] names.length).extended)

theorem evaluated_argument_returns (program : Program) (bindings : Subst)
    (before middle after : State) (destination : Eval.Target)
    (expression value answer : Atom) (remaining values : List Atom) (index : Nat)
    (demanded : (match destination with
      | .function head => Eval.argumentIsRaw program head index
      | .data => false) = false)
    (computed : PureReturns program bindings before expression middle value)
    (continued : (theory program).MultiStep
      { state := middle, control := .arguments bindings destination remaining (values ++ [value]) (index + 1) }
      (finished after [answer] [] [])) :
    (theory program).MultiStep
      { state := before, control := .arguments bindings destination (expression :: remaining) values index }
      (finished after [answer] [] []) := by
  refine .step ?_
    (path_trans (path_with_caller_frames program [.argument bindings destination remaining values index] computed) ?_)
  · apply Transition.core rfl
    apply Eval.step_transition
    simp [Eval.step, withFrames]
    exact demanded
  · refine .step (.core rfl (Eval.step_transition rfl)) ?_
    exact single_sequence_returns program middle after _ answer continued

theorem authored_function_arguments_return (program : Program) (bindings callee : Subst)
    (before after : State) (head : String) (values : List Atom) (index : Nat) (body answer : Atom)
    (notIO : Eval.ioHead head = false) (notNative : StdLib.known head = false)
    (selected : Eval.clauses program head values = [.evaluate callee body])
    (computed : PureReturns program callee before body after answer) :
    (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head) [] values index }
      (finished after [answer] [] []) := by
  refine .step ?_ (single_sequence_returns program before after (.evaluate callee body) answer computed)
  apply Transition.core rfl
  apply Eval.step_transition
  simp [Eval.step, notIO, notNative, selected]

/-- An ordinary literal call enters the same argument machine even when
the arguments or clause body contain admitted captured helper calls. -/
theorem call_returns (program : Program) (bindings : Subst)
    (before after : State) (head : String) (arguments : List Atom) (answer : Atom)
    (dispatch : (Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head)) = true)
    (computed : (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head) arguments [] 0 }
      (finished after [answer] [] []))
    (ordinary : head ∉
      ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"]) :
    PureReturns program bindings before (.expression (.symbol head :: arguments)) after answer := by
  have shape : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false := by
    exact Eval.controlForm_of_ordinary ordinary
  exact .step (.core rfl (DeclarativeSpec.Transition.call_enter rfl shape dispatch)) computed

/-- Captured prefix arguments and a computed final argument are supplied to
the actual selected clause. The final argument's evidence is its source path. -/
theorem authored_prefix_call_returns (program : Program) (bindings callee : Subst)
    (before middle after : State) (head : String) (names : List String)
    (argument value body answer : Atom)
    (notIO : Eval.ioHead head = false) (notNative : StdLib.known head = false)
    (registered : program.equations.any (·.head == head) = true)
    (ordinary : DeclarativeSpec.controlForm
      (.expression (.symbol head :: (names.map Atom.var ++ [argument]))) = false)
    (demanded : Eval.argumentIsRaw program head names.length = false)
    (argumentComputed : PureReturns program bindings before argument middle value)
    (selected : Eval.clauses program head
      (names.map (fun name => applySubst bindings (.var name)) ++ [value]) = [.evaluate callee body])
    (bodyComputed : PureReturns program callee middle body after answer) :
    PureReturns program bindings before
      (.expression (.symbol head :: (names.map Atom.var ++ [argument]))) after answer := by
  refine .step (.core rfl (DeclarativeSpec.Transition.call_enter rfl ordinary (by simp [registered]))) ?_
  apply variable_prefix_arguments_return program bindings before after (.function head) names [argument] [] 0 answer
  have finishedArguments := authored_function_arguments_return program bindings callee middle after head
    (names.map (fun name => applySubst bindings (.var name)) ++ [value]) (names.length + 1)
    body answer notIO notNative selected bodyComputed
  simpa only [List.nil_append, Nat.zero_add] using
    evaluated_argument_returns program bindings before middle after (.function head) argument value answer []
      (names.map (fun name => applySubst bindings (.var name))) names.length demanded argumentComputed finishedArguments

end Mettapedia.Languages.MeTTa.PeTTa.BoundCalls
