import Mettapedia.Languages.MeTTa.PeTTa.Eval
import Mathlib.Data.List.Forall2

/-!
# Finite pure data construction in PeTTa execution

These compositional laws use the existing evaluator's argument continuation.
They apply to any finite constructor arity and retain argument order. Captured
values are supplied through the ordinary pure-return judgments, so a value
containing an executable head is not implicitly evaluated again.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.PureData

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval

/-- A nonempty application sequence exposes exactly the selected source
clauses. Empty selection, partial application and over-application cannot
manufacture an evaluated body. -/
theorem clauses_of_singleton_application {program : SpaceSemantics.Program} {head : String}
    {values : List Atom} {body : Control}
    (selected : application program head values = .sequence [body] []) :
    clauses program head values = [body] := by
  cases found : clauses program head values with
  | nil =>
      simp only [application, found] at selected
      split_ifs at selected; cases selected
  | cons first rest =>
      have same : Control.sequence (first :: rest) [] = .sequence [body] [] := by
        simpa only [application, found] using selected
      exact (Control.sequence.inj same).1

theorem selected_clause_agreement {allowed : String → Bool} {first second : SpaceSemantics.Program}
    (agreement : ProgramAgreementOn allowed first second) {head : String} {values : List Atom}
    (supported : allowed head = true) {body : Control}
    (selected : clauses first head values = [body]) :
    clauses second head values = [body] := by
  apply clauses_of_singleton_application
  rw [← agreement.bodies head values supported]
  simp [application, selected]

/-- Fresh, distinct formal variables capture the supplied values in the
canonical matcher's retained binding order. -/
theorem match_variable_values (names : List String) (values : List Atom) (caller : Subst)
    (distinct : names.Nodup) (length : values.length = names.length)
    (fresh : ∀ name ∈ names, Subst.lookup caller name = none) :
    SpaceSemantics.matchValue.matchValues caller (names.map Atom.var) values =
      some ((names.zip values).reverse ++ caller) := by
  induction names generalizing values caller with
  | nil =>
      have empty : values = [] := List.eq_nil_of_length_eq_zero length
      subst values
      simp [SpaceSemantics.matchValue.matchValues]
  | cons name names ih =>
      cases values with
      | nil => simp at length
      | cons value values =>
          simp only [List.nodup_cons] at distinct
          have freshHead := fresh name List.mem_cons_self
          have freshTail : ∀ next ∈ names, Subst.lookup ((name, value) :: caller) next = none := by
            intro next member
            have unequal : name ≠ next := by intro same; subst next; exact distinct.1 member
            have neq : (name == next) = false := by simp [unequal]
            simpa only [Subst.lookup, List.find?_cons, neq, Bool.false_eq_true, ↓reduceIte] using
              fresh next (List.mem_cons_of_mem _ member)
          simp only [List.map_cons, SpaceSemantics.matchValue.matchValues,
            SpaceSemantics.matchValue, matchAtom, freshHead, Option.bind_eq_bind, Option.bind_some]
          rw [ih values ((name, value) :: caller) distinct.2 (by simpa using length) freshTail]
          simp only [List.zip_cons_cons, List.reverse_cons, List.append_assoc, List.singleton_append]

/-- A unique named equation with distinct variable formals captures its values
in the canonical environment. The source equation and every formal remain
explicit; the lemma does not assume the call's execution result. -/
theorem named_equation_clause (program : SpaceSemantics.Program) (head : String)
    (equation : SpaceSemantics.Equation) (names : List String) (values : List Atom)
    (rows : program.equations.filter (fun row => row.head == head) = [equation])
    (arguments : equation.arguments = names.map Atom.var)
    (distinct : names.Nodup) (length : values.length = names.length) :
    clauses program head values =
      [.evaluate ((names.zip values).reverse) equation.body] := by
  rw [clauses_use_only_the_named_equations, rows]
  simp only [List.filterMap_cons, List.filterMap_nil, arguments]
  rw [match_variable_values names values [] distinct length (by intro name member; rfl)]
  simp

theorem arguments_return (program : SpaceSemantics.Program) (bindings : Subst)
    (state : State) (expressions values : List Atom)
    (computed : List.Forall₂ (fun expression value =>
      PureReturns program bindings state expression state value) expressions values)
    (accumulated : List Atom) (index : Nat) :
    (theory program).MultiStep
      { state, control := .arguments bindings .data expressions accumulated index }
      (finished state [.expression (accumulated ++ values)] [] []) := by
  induction computed generalizing accumulated index with
  | nil =>
      simpa using data_arguments_values_return program bindings state accumulated index
  | @cons expression value expressions values returned _ ih =>
      apply evaluated_argument_returns program bindings state state state .data expression value
        (.expression (accumulated ++ value :: values)) expressions accumulated index rfl returned
      simpa only [List.append_assoc, List.singleton_append] using ih (accumulated ++ [value]) (index + 1)

/-- An expression of captured variables constructs the ordered tuple of their
values. The tuple has no interpreted head, and its payloads are not evaluated. -/
theorem variables_return (program : SpaceSemantics.Program) (bindings : Subst)
    (state : State) (names : List String) :
    PureReturns program bindings state (.expression (names.map Atom.var)) state
      (.expression (names.map (fun name => applySubst bindings (.var name)))) := by
  have computed : List.Forall₂ (fun expression value =>
      PureReturns program bindings state expression state value)
      (names.map Atom.var) (names.map (fun name => applySubst bindings (.var name))) := by
    induction names with
    | nil => exact .nil
    | cons name names ih => exact .cons (variable_returns program bindings state name) ih
  cases names with
  | nil =>
      refine .step (step_transition rfl) ?_
      exact arguments_return program bindings state _ _ computed [] 0
  | cons name names =>
      refine .step (step_transition rfl) ?_
      exact arguments_return program bindings state _ _ computed [] 0

/-- An inert constructor collects exactly the proved values of its arguments.
Neither argument multiplicity nor order is quotiented away. -/
theorem constructor_return (program : SpaceSemantics.Program) (bindings : Subst)
    (state : State) (head : String) (expressions values : List Atom)
    (inert : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = false)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"])
    (computed : List.Forall₂ (fun expression value =>
      PureReturns program bindings state expression state value) expressions values) :
    PureReturns program bindings state (.expression (.symbol head :: expressions)) state
      (.expression (.symbol head :: values)) := by
  apply data_call_returns program bindings state state head expressions _ inert _ (by simp_all)
  simpa using arguments_return program bindings state (.symbol head :: expressions) (.symbol head :: values)
    (.cons (symbol_returns program bindings state head) computed) [] 0

/-- Compositional evidence for sequential bindings. Each premise is an
execution of the existing evaluator, and each binding uses its actual matcher. -/
inductive BindingsReturn (program : SpaceSemantics.Program) :
    Subst → State → List (Atom × Atom) → Subst → State → Prop where
  | nil (bindings state) : BindingsReturn program bindings state [] bindings state
  | cons {bindings bound final : Subst} {before middle after : State}
      {pattern expression value : Atom} {rest : List (Atom × Atom)}
      (computed : PureReturns program bindings before expression middle value)
      (matched : SpaceSemantics.matchBinding bindings pattern value = some bound)
      (continued : BindingsReturn program bound middle rest final after) :
      BindingsReturn program bindings before ((pattern, expression) :: rest) final after

private def bindingNest (pairs : List (Atom × Atom)) (body : Atom) : Atom :=
  pairs.foldr (fun pair tail => .expression [.symbol "let", pair.1, pair.2, tail]) body

private theorem bindingNest_expands (pairs : List (Atom × Atom)) (body : Atom) :
    nestedLets (pairs.map (fun pair => .expression [pair.1, pair.2])) body =
      some (bindingNest pairs body) := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih => simp [nestedLets, bindingNest, ih]

private theorem BindingsReturn.nested_returns {program : SpaceSemantics.Program}
    {bindings final : Subst} {before middle : State} {pairs : List (Atom × Atom)}
    (computed : BindingsReturn program bindings before pairs final middle)
    (after : State) (body answer : Atom)
    (returned : PureReturns program final middle body after answer) :
    PureReturns program bindings before (bindingNest pairs body) after answer := by
  induction computed with
  | nil => exact returned
  | cons first matched continued ih =>
      exact let_returns program _ _ _ _ _ _ _ _ _ _ first matched (ih returned)

/-- A finite `let*` sequence composes the proved expression runs without a
fixed arity or a separate evaluator for source bodies. -/
theorem let_bindings_return {program : SpaceSemantics.Program}
    {bindings final : Subst} {before middle : State} {pairs : List (Atom × Atom)}
    (computed : BindingsReturn program bindings before pairs final middle)
    (after : State) (body answer : Atom)
    (returned : PureReturns program final middle body after answer) :
    PureReturns program bindings before
      (.expression [.symbol "let*", .expression (pairs.map fun pair => .expression [pair.1, pair.2]), body])
      after answer :=
  let_star_returns program bindings before after _ body (bindingNest pairs body) answer
    (bindingNest_expands pairs body) (computed.nested_returns after body answer returned)

/-- A literal data fragment excludes interpreted heads, control forms and
unbound program variables. Its constructor declarations have no effects. -/
inductive Literal (program : SpaceSemantics.Program) : Atom → Prop
  | grounded (value) : Literal program (.grounded value)
  | symbol (name) : Literal program (.symbol name)
  | constructor (head : String) (arguments : List Atom)
      (inert : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = false)
      (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"])
      (children : ∀ argument ∈ arguments, Literal program argument) :
      Literal program (.expression (.symbol head :: arguments))

theorem literal_return (program : SpaceSemantics.Program) (bindings : Subst)
    (state : State) (value : Atom) (literal : Literal program value) :
    PureReturns program bindings state value state value := by
  induction literal with
  | grounded value => exact grounded_returns program bindings state value
  | symbol name => exact symbol_returns program bindings state name
  | constructor head arguments inert ordinary _ ih =>
      apply constructor_return program bindings state head arguments arguments inert ordinary
      exact List.forall₂_same.mpr ih

/-- A known executable operation cannot be smuggled into this literal fragment. -/
theorem known_head_not_literal (program : SpaceSemantics.Program) (head : String)
    (arguments : List Atom) (known : StdLib.known head = true) :
    ¬ Literal program (.expression (.symbol head :: arguments)) := by
  intro literal
  cases literal with
  | constructor _ _ inert _ _ => simp [known] at inert

/-- Compose a raw authored call with its unique selected body. The captured
arguments are data even when they contain interpreted heads. Clause selection
and argument demand are obligations about the actual loaded program. -/
theorem raw_authored_call_return (program : SpaceSemantics.Program)
    (bindings callee : Subst) (before after : State) (head : String)
    (arguments : List Atom) (body answer : Atom)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"])
    (notIO : ioHead head = false) (notNative : StdLib.known head = false)
    (registered : program.equations.any (·.head == head) = true)
    (raw : ∀ index < arguments.length, argumentIsRaw program head index = true)
    (selected : clauses program head (arguments.map (applySubst bindings)) =
      [.evaluate callee body])
    (computed : PureReturns program callee before body after answer) :
    PureReturns program bindings before (.expression (.symbol head :: arguments)) after answer := by
  apply raw_call_returns program bindings before after head arguments answer
    (by simp [notIO, notNative, registered]) raw _ ordinary
  exact authored_function_arguments_return program bindings callee before after head
    (arguments.map (applySubst bindings)) arguments.length body answer notIO notNative selected computed

/-- Raw argument capture can precede demanded arguments. The retained
continuation decides how the remaining arguments are evaluated. -/
theorem raw_prefix_arguments_return (program : SpaceSemantics.Program) (bindings : Subst)
    (before after : State) (head : String) (arguments remaining values : List Atom)
    (index : Nat) (answer : Atom)
    (raw : ∀ offset < arguments.length, argumentIsRaw program head (index + offset) = true)
    (computed : (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head) remaining
          (values ++ arguments.map (applySubst bindings)) (index + arguments.length) }
      (finished after [answer] [] [])) :
    (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head)
          (arguments ++ remaining) values index }
      (finished after [answer] [] []) := by
  induction arguments generalizing values index with
  | nil => simpa using computed
  | cons argument arguments ih =>
      apply raw_argument_answers program bindings before after head argument
        (arguments ++ remaining) values index [answer] (raw 0 (by simp))
      apply ih (values ++ [applySubst bindings argument]) (index + 1)
      · intro offset bounded
        simpa [Nat.add_assoc, Nat.add_comm 1] using raw (offset + 1) (by simpa using bounded)
      · simpa [List.map, List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using computed

/-- A captured prefix followed by one evaluated argument uses the ordinary
argument continuation and named source clause selection. -/
theorem raw_prefix_authored_call_return (program : SpaceSemantics.Program)
    (bindings callee : Subst) (before middle after : State) (head : String)
    (arguments values : List Atom) (last value body answer : Atom)
    (notIO : ioHead head = false) (notNative : StdLib.known head = false)
    (dispatch : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = true)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"])
    (raw : ∀ index < arguments.length, argumentIsRaw program head index = true)
    (demanded : argumentIsRaw program head arguments.length = false)
    (captured : arguments.map (applySubst bindings) = values)
    (lastReturned : PureReturns program bindings before last middle value)
    (selected : clauses program head (values ++ [value]) = [.evaluate callee body])
    (bodyReturned : PureReturns program callee middle body after answer) :
    PureReturns program bindings before (.expression (.symbol head :: (arguments ++ [last]))) after answer := by
  apply call_returns program bindings before after head _ answer dispatch _ ordinary
  apply raw_prefix_arguments_return program bindings before after head arguments [last] [] 0 answer
    (by simpa using raw)
  simp only [List.nil_append, Nat.zero_add, captured]
  apply evaluated_argument_returns program bindings before middle after (.function head)
    last value answer [] values arguments.length demanded lastReturned
  exact authored_function_arguments_return program bindings callee middle after head
    (values ++ [value]) (arguments.length + 1) body answer notIO notNative selected bodyReturned

private theorem raw_arguments_stage (program : SpaceSemantics.Program) (bindings : Subst)
    (state : State) (head : String) (arguments values : List Atom) (index fuel : Nat)
    (caller : List Frame)
    (raw : ∀ offset < arguments.length, argumentIsRaw program head (index + offset) = true) :
    run program (fuel + 3 * arguments.length)
      { state, control := .arguments bindings (.function head) arguments values index, frames := caller } =
    run program fuel
      { state, control := .arguments bindings (.function head) []
          (values ++ arguments.map (applySubst bindings)) (index + arguments.length),
        frames := List.replicate arguments.length (.sequence [] []) ++ caller } := by
  induction arguments generalizing values index caller with
  | nil => simp
  | cons argument arguments ih =>
      have firstRaw : argumentIsRaw program head index = true := by
        simpa using raw 0 (by simp)
      have tailRaw : ∀ offset < arguments.length,
          argumentIsRaw program head (index + 1 + offset) = true := by
        intro offset bounded
        simpa [Nat.add_assoc, Nat.add_comm 1] using raw (offset + 1) (by simpa using bounded)
      have first : step program
          { state, control := .arguments bindings (.function head) (argument :: arguments) values index,
            frames := caller } =
          some { state := state, control := .returned [applySubst bindings argument], frames := .argument bindings (.function head) arguments values index :: caller } := by
        simp [step, firstRaw]
      have second : step program
          { state, control := .returned [applySubst bindings argument],
            frames := .argument bindings (.function head) arguments values index :: caller } =
          some { state := state, control := .sequence [.arguments bindings (.function head) arguments (values ++ [applySubst bindings argument]) (index + 1)] [], frames := caller } := by
        simp [step]
      have third : step program
          { state, control := .sequence [.arguments bindings (.function head) arguments (values ++ [applySubst bindings argument]) (index + 1)] [], frames := caller } =
          some { state := state, control := .arguments bindings (.function head) arguments (values ++ [applySubst bindings argument]) (index + 1), frames := .sequence [] [] :: caller } := rfl
      rw [show fuel + 3 * (argument :: arguments).length =
          ((fuel + 3 * arguments.length) + 1) + 1 + 1 by simp; omega]
      rw [run_succ_of_step program _ _ _ first, run_succ_of_step program _ _ _ second,
        run_succ_of_step program _ _ _ third]
      simpa [List.map_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm 1,
        List.replicate_succ'] using ih (values ++ [applySubst bindings argument])
        (index + 1) (.sequence [] [] :: caller) tailRaw

/-- Raw argument capture is independent of the caller environment and source
argument syntax. The retained program executes after the same captured values;
the argument contents are not evaluated as code. -/
theorem raw_capture_run_eq (program : SpaceSemantics.Program) (first second : Subst)
    (state : State) (head : String) (one two : List Atom) (fuel : Nat)
    (dispatch : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = true)
    (raw : ∀ index < one.length, argumentIsRaw program head index = true)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"])
    (captured : one.map (applySubst first) = two.map (applySubst second)) :
    run program (fuel + (3 * one.length + 2))
      { state, control := .evaluate first (.expression (.symbol head :: one)) } =
    run program (fuel + (3 * one.length + 2))
      { state, control := .evaluate second (.expression (.symbol head :: two)) } := by
  have sameLength : one.length = two.length := by simpa using congrArg List.length captured
  have enter (bindings : Subst) (arguments : List Atom) : step program
      { state, control := .evaluate bindings (.expression (.symbol head :: arguments)) } =
      some { state, control := .arguments bindings (.function head) arguments [] 0 } := by
    simp at ordinary
    simp only [step]
    split <;> simp_all <;> grind
  rw [show fuel + (3 * one.length + 2) = ((fuel + 1) + 3 * one.length) + 1 by omega,
    run_succ_of_step program _ _ _ (enter first one),
    run_succ_of_step program _ _ _ (enter second two)]
  rw [raw_arguments_stage program first state head one [] 0 (fuel + 1) [] (by simpa using raw)]
  rw [sameLength, raw_arguments_stage program second state head two [] 0 (fuel + 1) []
    (by simpa [← sameLength] using raw)]
  simp only [run, step, List.nil_append, List.append_nil, Nat.zero_add, captured]
  split
  · rfl
  · rename_i absent
    split at absent
    · split at absent <;> cases absent
    · split at absent
      · split at absent <;> cases absent
      · cases absent

/-- Reuse a proved raw call under any equal capture, retaining its complete
state and answer observation. This is a law of the actual target machine. -/
theorem raw_capture_returns (program : SpaceSemantics.Program) (first second : Subst)
    (before after : State) (head : String) (one two : List Atom) (answer : Atom)
    (dispatch : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = true)
    (raw : ∀ index < one.length, argumentIsRaw program head index = true)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"])
    (captured : one.map (applySubst first) = two.map (applySubst second))
    (returned : PureReturns program first before (.expression (.symbol head :: one)) after answer) :
    PureReturns program second before (.expression (.symbol head :: two)) after answer := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program first before after _ _ returned
  have enough := completed_run_more_fuel program fuel (3 * one.length + 2) _ after [answer] [] [] completed
  rw [raw_capture_run_eq program first second before head one two fuel dispatch raw ordinary captured] at enough
  exact completed_run_has_path program _ _ after [answer] [] [] enough

/-- A certificate that source syntax contains only captured variables and
inert data constructors. It recognizes a fragment of the existing Atom
syntax; it is not another term carrier or evaluation relation. -/
inductive Template (program : SpaceSemantics.Program) : Atom → Prop where
  | captured (name : String) : Template program (.var name)
  | grounded (value) : Template program (.grounded value)
  | symbol (name : String) : Template program (.symbol name)
  | constructor (head : String) (arguments : List Atom)
      (inert : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = false)
      (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"])
      (children : ∀ argument ∈ arguments, Template program argument) :
      Template program (.expression (.symbol head :: arguments))

/-- Data templates substitute captured values once, without evaluating the
values' contents. Only constructors occurring in the source template run. -/
theorem template_return (program : SpaceSemantics.Program) (bindings : Subst)
    (state : State) (expression : Atom) (template : Template program expression) :
    PureReturns program bindings state expression state (applySubst bindings expression) := by
  induction template with
  | captured name => exact variable_returns program bindings state name
  | grounded value => exact grounded_returns program bindings state value
  | symbol name => exact symbol_returns program bindings state name
  | constructor head arguments inert ordinary _ ih =>
      have substituted (atoms : List Atom) :
          applySubst.applySubstList bindings atoms = atoms.map (applySubst bindings) := by
        induction atoms with
        | nil => rfl
        | cons first rest ih => simp only [applySubst.applySubstList, List.map_cons, ih]
      have values : List.Forall₂ (fun expression value =>
          PureReturns program bindings state expression state value)
          arguments (arguments.map (applySubst bindings)) := by
        rw [List.forall₂_map_right_iff, List.forall₂_same]
        exact ih
      simpa only [applySubst, substituted, List.map_cons] using
        constructor_return program bindings state head arguments
          (arguments.map (applySubst bindings)) inert ordinary values

end Mettapedia.Languages.MeTTa.PeTTa.PureData
