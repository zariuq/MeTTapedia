import Mettapedia.Languages.MeTTa.PeTTa.StdLib

/-!
# PeTTa operational rules and whole-program derivations

The rules interpret syntax, argument demand, ordered alternatives, captured
values, private stores and parsed-line I/O on the existing Atom and execution
configuration carriers. They are independent of the executable step and fuel
functions. `Runs` relates an initial configuration to a completed observation
or a primitive fault. Exhaustion is a machine outcome, not a logical refusal.

These rules specify the implemented closed profile. An authored function's
equations are selected by matching their argument lists element by element
against the call's values. A call with a number of arguments no equation takes
is classified as PeTTa classifies it (P-APP-1): a partial application when an
equation takes more, an over-application fault otherwise. `match` with three
arguments runs its body once for each stored row its pattern matches, in row
order, under that row's bindings, as PeTTa's translator compiles it. Open
calls, run-time function redefinition and the unsupported control forms remain
separate coverage obligations. The selected Pattern presentation is in
`PatternRewrite.DeclarativeSpec`; it is not this whole-program judgment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Eval

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open SpaceSemantics (Program Cases)
open Effects (State Fault)

def ioHead (head : String) : Bool := head ∈ ["readln!", "println!", "eval"]

/-- Constructor/list-view patterns cannot invoke the program or a primitive.
The special `cons` pattern is handled by `SpaceSemantics.matchValue` itself. -/
def passivePattern (program : Program) (pattern : Atom) : Bool :=
  (SpaceSemantics.patternHeads pattern).all fun head =>
    head == "cons" || !(ioHead head || StdLib.known head ||
      program.equations.any (·.head == head) ||
      head ∈ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"])

def constructorPatterns (program : Program) : Bool :=
  (SpaceSemantics.programPatterns program).all (passivePattern program)

def argumentIsRaw (program : Program) (head : String) (index : Nat) : Bool :=
  if StdLib.known head then StdLib.rawArgument head index
  else
    program.declarations.any fun declaration =>
      match declaration with
      | .expression [.symbol ":", .symbol name, .expression (.symbol "->" :: types)] =>
          name == head && types[index]?.any formalArgumentIsRaw
      | _ => false

/-- Outside the primitive table, raw demand comes from a stored literal `Atom`
formal at this position. This lookup law does not establish call saturation. -/
theorem argumentIsRaw_iff_declaredAtom
    (program : Program) (head : String) (index : Nat)
    (notPrimitive : StdLib.known head = false) :
    argumentIsRaw program head index = true ↔
      ∃ types, .expression [.symbol ":", .symbol head,
        .expression (.symbol "->" :: types)] ∈ program.declarations ∧
        types[index]? = some (.symbol "Atom") := by
  simp only [argumentIsRaw, notPrimitive, Bool.false_eq_true, ↓reduceIte,
    List.any_eq_true]
  constructor
  · rintro ⟨declaration, member, raw⟩
    split at raw
    · simp only [Bool.and_eq_true, beq_iff_eq,
        optional_formalArgumentIsRaw] at raw
      rcases raw with ⟨rfl, literal⟩
      exact ⟨_, member, literal⟩
    · contradiction
  · rintro ⟨types, member, literal⟩
    refine ⟨_, member, ?_⟩
    simp [literal]

/-- The bodies of the equations of `head` whose argument patterns match the
call's values, in source order. The argument list is matched element by
element: a call's arguments are never read through the `cons` list view, so
`(h 1 2)` cannot select `(= (h cons $a $b) $b)`. Each argument pattern keeps
the list view of `SpaceSemantics.matchValue`. -/
def clauses (program : Program) (head : String) (values : List Atom) : List Control :=
  program.equations.filterMap fun equation =>
    if equation.head = head then
      (SpaceSemantics.matchValue.matchValues [] equation.arguments values).map
        fun bindings => .evaluate bindings equation.body
    else none

/-- The input arities the equations of `head` record, one per equation, in
source order (P-DEF-1). -/
def arities (program : Program) (head : String) : List Nat :=
  (program.equations.filter (·.head == head)).map (·.arguments.length)

/-- Insert into an ascending list without repeats. -/
def insertArity (arity : Nat) : List Nat → List Nat
  | [] => [arity]
  | first :: rest =>
      if arity < first then arity :: first :: rest
      else if arity = first then first :: rest
      else first :: insertArity arity rest

/-- The recorded input arities, ascending and without repeats, as PeTTa's
over-application error lists them. -/
def knownArities (program : Program) (head : String) : List Nat :=
  (arities program head).foldr insertArity []

/-- A grounded tag that source text cannot spell. A partial application is
`(tag f (values))`, so it prints as `(partial f (values))` while authored data
spelled `(partial f (values))` stays a different value, as in PeTTa, where the
partial is a compound term and not an expression list. -/
def partialTag : Atom := .grounded (.custom "PeTTa.Partial" "")

/-- PeTTa's value `partial(f, values)`: `f` applied to fewer arguments than an
equation takes, with those argument values held. -/
def partialValue (head : String) (values : List Atom) : Atom :=
  .expression [partialTag, .symbol head, .expression values]

/-- The control of a call of an authored function once its arguments are values
(P-APP-1). When an equation of this many arguments matches, the selected bodies
run in source order. Otherwise the arity decides: if some equation takes exactly
this many arguments, the call has no answers; if some equation takes more, or
none is recorded, the call answers the partial application; otherwise it is an
over-application fault. `application_classified` states the rule arity first. -/
@[simp] def application (program : Program) (head : String) (values : List Atom) : Control :=
  match clauses program head values with
  | [] =>
      if values.length ∈ arities program head then .sequence [] []
      else if (arities program head).all (· < values.length) &&
          !(arities program head).isEmpty then
        .fault (.overApplication head (knownArities program head) values.length)
      else .returned [partialValue head values]
  | selected => .sequence selected []

/-- The bodies one `match` runs on the rows `rows`: the body once for every row
its pattern matches, in row order, under the caller's bindings extended by that
row's. A variable the caller has bound tests the row, as a variable bound
earlier tests a `let` value. The body is code, evaluated under these bindings;
captured values are not evaluated again. -/
def queryBodies (bindings : Subst) (rows : List Atom) (pattern body : Atom) : List Control :=
  rows.filterMap fun row =>
    (SpaceSemantics.matchValue bindings pattern row).map fun bound => .evaluate bound body

/-- The alternatives of one query of the space value `space`: the bodies on its
rows as they are when the query starts, or an invalid-space fault. -/
def queryAlternatives (state : State) (bindings : Subst) (space pattern body : Atom) :
    List Control :=
  match Effects.readHandle space >>= state.read with
  | some rows => queryBodies bindings rows pattern body
  | none => [.fault .invalidSpace]

/-- A matching equation of this arity selects the call. -/
theorem application_of_selected {program : Program} {head : String} {values : List Atom}
    {first : Control} {rest : List Control}
    (selected : clauses program head values = first :: rest) :
    application program head values = .sequence (first :: rest) [] := by
  simp [application, selected]

/-- Element-by-element matching relates lists of the same length. -/
theorem matchValues_length {bindings bound : Subst} :
    {patterns values : List Atom} →
    SpaceSemantics.matchValue.matchValues bindings patterns values = some bound →
      patterns.length = values.length
  | [], [], _ => rfl
  | [], _ :: _, matched => by simp [SpaceSemantics.matchValue.matchValues] at matched
  | _ :: _, [], matched => by simp [SpaceSemantics.matchValue.matchValues] at matched
  | pattern :: patterns, value :: values, matched => by
      simp only [SpaceSemantics.matchValue.matchValues] at matched
      cases first : SpaceSemantics.matchValue bindings pattern value with
      | none => simp [first] at matched
      | some middle =>
          simp only [first, Option.bind_eq_bind, Option.bind_some] at matched
          simp [matchValues_length (bindings := middle) matched]

/-- A selected equation records the call's arity. -/
theorem arity_of_selected {program : Program} {head : String} {values : List Atom}
    {control : Control} (member : control ∈ clauses program head values) :
    values.length ∈ arities program head := by
  unfold clauses at member
  obtain ⟨equation, equationMember, selected⟩ := List.mem_filterMap.mp member
  by_cases same : equation.head = head
  · simp only [same, if_true] at selected
    cases matched : SpaceSemantics.matchValue.matchValues [] equation.arguments values with
    | none => simp [matched] at selected
    | some bindings =>
        have lengths := matchValues_length matched
        simp only [arities, List.mem_map, List.mem_filter]
        exact ⟨equation, ⟨equationMember, by simp [same]⟩, lengths⟩
  · simp [same] at selected

/-- P-APP-1, arity first: a call when an equation takes exactly this many
arguments (its bodies run in source order), a partial application when one
takes more or none is recorded, and an over-application fault otherwise. -/
theorem application_classified (program : Program) (head : String) (values : List Atom) :
    application program head values =
      if values.length ∈ arities program head then .sequence (clauses program head values) []
      else if (arities program head).all (· < values.length) &&
          !(arities program head).isEmpty then
        .fault (.overApplication head (knownArities program head) values.length)
      else .returned [partialValue head values] := by
  cases selected : clauses program head values with
  | nil => simp [application, selected]
  | cons first rest =>
      have arity := arity_of_selected (selected ▸ List.mem_cons_self : first ∈ clauses program head values)
      simp [application, selected, arity]

/-- A call with an arity some equation records is the ordinary selection. -/
theorem application_saturated {program : Program} {head : String} {values : List Atom}
    (saturated : values.length ∈ arities program head) :
    application program head values = .sequence (clauses program head values) [] := by
  rw [application_classified, if_pos saturated]

def readCases : List Atom → Option Cases
  | [] => some []
  | .expression [pattern, body] :: rest =>
      ((pattern, body) :: ·) <$> readCases rest
  | _ => none

def nestedLets : List Atom → Atom → Option Atom
  | [], body => some body
  | .expression [pattern, value] :: rest, body =>
      (.expression [.symbol "let", pattern, value, ·]) <$> nestedLets rest body
  | _, _ => none

end Mettapedia.Languages.MeTTa.PeTTa.Eval

namespace Mettapedia.Languages.MeTTa.PeTTa.DeclarativeSpec

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open SpaceSemantics (Program Cases)
open Effects (State Fault)
open Eval

/-- Recognition of the control syntax handled before ordinary applications.
Other arities and shapes continue through the ordinary call/data rules. -/
def controlForm : Atom → Bool
  | .expression [.symbol "let", _, _, _]
  | .expression [.symbol "let*", .expression _, _]
  | .expression [.symbol "case", _, .expression _]
  | .expression [.symbol "if", _, _, _]
  | .expression [.symbol "collapse", _]
  | .expression [.symbol "superpose", .expression _]
  | .expression [.symbol "empty"]
  | .expression [.symbol "quote", _]
  | .expression [.symbol "match", _, _, _] => true
  | _ => false

/-- Syntax-directed transitions. The constructors do not invoke the machine's
step function, its fuelled runner, or a guest checker's judgment. -/
inductive Transition (program : Program) : Configuration → Configuration → Prop where
  | sequence_done {source : Configuration} {answers : List Atom}
      (control : source.control = .sequence [] answers) :
      Transition program source { source with control := .returned answers }
  | sequence_enter {source : Configuration} {first : Control} {rest : List Control}
      {answers : List Atom} (control : source.control = .sequence (first :: rest) answers) :
      Transition program source
        { source with control := first, frames := .sequence rest answers :: source.frames }
  | construct {source : Configuration} {bindings : Subst} {values : List Atom} {index : Nat}
      (control : source.control = .arguments bindings .data [] values index) :
      Transition program source { source with control := .returned [.expression values] }
  | read_end {source : Configuration} {bindings : Subst} {index : Nat}
      (control : source.control = .arguments bindings (.function "readln!") [] [] index)
      (input : source.input = []) :
      Transition program source { source with control := .returned [.symbol "end_of_file"] }
  | read_line {source : Configuration} {bindings : Subst} {index : Nat}
      {first : Atom} {rest : List Atom}
      (control : source.control = .arguments bindings (.function "readln!") [] [] index)
      (input : source.input = first :: rest) :
      Transition program source { source with input := rest, control := .returned [first] }
  | print {source : Configuration} {bindings : Subst} {index : Nat} {value : Atom}
      (control : source.control = .arguments bindings (.function "println!") [] [value] index) :
      Transition program source
        { source with output := source.output ++ [value], control := .returned [Effects.boolean true] }
  | evaluate_code {source : Configuration} {bindings : Subst} {index : Nat} {code : Atom}
      (control : source.control = .arguments bindings (.function "eval") [] [code] index) :
      Transition program source { source with control := .evaluate [] code }
  | read_bad {source : Configuration} {bindings : Subst} {index : Nat} {values : List Atom}
      (control : source.control = .arguments bindings (.function "readln!") [] values index)
      (invalid : values ≠ []) :
      Transition program source { source with control := .fault (.invalidArguments "readln!") }
  | print_bad {source : Configuration} {bindings : Subst} {index : Nat} {values : List Atom}
      (control : source.control = .arguments bindings (.function "println!") [] values index)
      (invalid : ∀ value, values ≠ [value]) :
      Transition program source { source with control := .fault (.invalidArguments "println!") }
  | eval_bad {source : Configuration} {bindings : Subst} {index : Nat} {values : List Atom}
      (control : source.control = .arguments bindings (.function "eval") [] values index)
      (invalid : ∀ value, values ≠ [value]) :
      Transition program source { source with control := .fault (.invalidArguments "eval") }
  | primitive {source : Configuration} {bindings : Subst} {head : String}
      {index : Nat} {values answers : List Atom} {after : State}
      (control : source.control = .arguments bindings (.function head) [] values index)
      (ordinary : ioHead head = false) (native : StdLib.known head = true)
      (result : StdLib.apply source.state head values = .ok (after, answers)) :
      Transition program source { source with state := after, control := .returned answers }
  | primitive_fault {source : Configuration} {bindings : Subst} {head : String}
      {index : Nat} {values : List Atom} {reason : Fault}
      (control : source.control = .arguments bindings (.function head) [] values index)
      (ordinary : ioHead head = false) (native : StdLib.known head = true)
      (result : StdLib.apply source.state head values = .error reason) :
      Transition program source { source with control := .fault reason }
  | equations {source : Configuration} {bindings : Subst} {head : String}
      {index : Nat} {values : List Atom}
      (control : source.control = .arguments bindings (.function head) [] values index)
      (ordinary : ioHead head = false) (notNative : StdLib.known head = false) :
      Transition program source { source with control := application program head values }
  | raw_argument {source : Configuration} {bindings : Subst} {target : Target}
      {first : Atom} {rest values : List Atom} {index : Nat}
      (control : source.control = .arguments bindings target (first :: rest) values index)
      (raw : (match target with
        | .function head => argumentIsRaw program head index
        | .data => false) = true) :
      Transition program source
        { source with
          control := .returned [applySubst bindings first]
          frames := .argument bindings target rest values index :: source.frames }
  | evaluated_argument {source : Configuration} {bindings : Subst} {target : Target}
      {first : Atom} {rest values : List Atom} {index : Nat}
      (control : source.control = .arguments bindings target (first :: rest) values index)
      (demanded : (match target with
        | .function head => argumentIsRaw program head index
        | .data => false) = false) :
      Transition program source
        { source with
          control := .evaluate bindings first
          frames := .argument bindings target rest values index :: source.frames }
  | value_variable {source : Configuration} {bindings : Subst} {name : String}
      (control : source.control = .evaluate bindings (.var name)) :
      Transition program source { source with control := .returned [applySubst bindings (.var name)] }
  | symbol {source : Configuration} {bindings : Subst} {name : String}
      (control : source.control = .evaluate bindings (.symbol name)) :
      Transition program source { source with control := .returned [.symbol name] }
  | grounded {source : Configuration} {bindings : Subst} {value : GroundedValue}
      (control : source.control = .evaluate bindings (.grounded value)) :
      Transition program source { source with control := .returned [.grounded value] }
  | let_enter {source : Configuration} {bindings : Subst} {pattern value body : Atom}
      (control : source.control = .evaluate bindings
        (.expression [.symbol "let", pattern, value, body])) :
      Transition program source
        { source with
          control := .evaluate bindings value
          frames := .bind bindings pattern body :: source.frames }
  | let_star {source : Configuration} {bindings : Subst} {pairs : List Atom} {body nested : Atom}
      (control : source.control = .evaluate bindings
        (.expression [.symbol "let*", .expression pairs, body]))
      (expanded : nestedLets pairs body = some nested) :
      Transition program source { source with control := .evaluate bindings nested }
  | let_star_bad {source : Configuration} {bindings : Subst} {pairs : List Atom} {body : Atom}
      (control : source.control = .evaluate bindings
        (.expression [.symbol "let*", .expression pairs, body]))
      (invalid : nestedLets pairs body = none) :
      Transition program source { source with control := .fault (.invalidArguments "let*") }
  | case_enter {source : Configuration} {bindings : Subst} {value : Atom}
      {rows : List Atom} {cases : Cases}
      (control : source.control = .evaluate bindings
        (.expression [.symbol "case", value, .expression rows]))
      (parsed : readCases rows = some cases) :
      Transition program source
        { source with
          control := .evaluate bindings value
          frames := .select bindings cases :: source.frames }
  | case_bad {source : Configuration} {bindings : Subst} {value : Atom} {rows : List Atom}
      (control : source.control = .evaluate bindings
        (.expression [.symbol "case", value, .expression rows]))
      (invalid : readCases rows = none) :
      Transition program source { source with control := .fault (.invalidArguments "case") }
  | if_enter {source : Configuration} {bindings : Subst} {condition yes no : Atom}
      (control : source.control = .evaluate bindings
        (.expression [.symbol "if", condition, yes, no])) :
      Transition program source
        { source with
          control := .evaluate bindings condition
          frames := .branch bindings yes no :: source.frames }
  | collapse_enter {source : Configuration} {bindings : Subst} {expression : Atom}
      (control : source.control = .evaluate bindings
        (.expression [.symbol "collapse", expression])) :
      Transition program source
        { source with control := .evaluate bindings expression, frames := .collect :: source.frames }
  | superpose_enter {source : Configuration} {bindings : Subst} {alternatives : List Atom}
      (control : source.control = .evaluate bindings
        (.expression [.symbol "superpose", .expression alternatives])) :
      Transition program source
        { source with control := .sequence (alternatives.map (.evaluate bindings)) [] }
  | empty_enter {source : Configuration} {bindings : Subst}
      (control : source.control = .evaluate bindings (.expression [.symbol "empty"])) :
      Transition program source { source with control := .returned [] }
  | quote_enter {source : Configuration} {bindings : Subst} {expression : Atom}
      (control : source.control = .evaluate bindings (.expression [.symbol "quote", expression])) :
      Transition program source { source with control := .returned [applySubst bindings expression] }
  | call_enter {source : Configuration} {bindings : Subst} {head : String} {arguments : List Atom}
      (control : source.control = .evaluate bindings (.expression (.symbol head :: arguments)))
      (notControl : controlForm (.expression (.symbol head :: arguments)) = false)
      (callable : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = true) :
      Transition program source
        { source with control := .arguments bindings (.function head) arguments [] 0 }
  | data_enter {source : Configuration} {bindings : Subst} {head : String} {arguments : List Atom}
      (control : source.control = .evaluate bindings (.expression (.symbol head :: arguments)))
      (notControl : controlForm (.expression (.symbol head :: arguments)) = false)
      (notCallable : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = false) :
      Transition program source
        { source with control := .arguments bindings .data (.symbol head :: arguments) [] 0 }
  | expression_enter {source : Configuration} {bindings : Subst} {items : List Atom}
      (control : source.control = .evaluate bindings (.expression items))
      (unheaded : ∀ head arguments, items ≠ .symbol head :: arguments) :
      Transition program source { source with control := .arguments bindings .data items [] 0 }
  | collapse_return {source : Configuration} {answers : List Atom} {rest : List Frame}
      (control : source.control = .returned answers) (frames : source.frames = .collect :: rest) :
      Transition program source { source with control := .returned [.expression answers], frames := rest }
  | sequence_return {source : Configuration} {answers collected : List Atom}
      {pending : List Control} {rest : List Frame}
      (control : source.control = .returned answers)
      (frames : source.frames = .sequence pending collected :: rest) :
      Transition program source
        { source with control := .sequence pending (collected ++ answers), frames := rest }
  | argument_return {source : Configuration} {answers values pending : List Atom}
      {bindings : Subst} {target : Target} {index : Nat} {rest : List Frame}
      (control : source.control = .returned answers)
      (frames : source.frames = .argument bindings target pending values index :: rest) :
      Transition program source
        { source with control := .sequence (answers.map fun value =>
            .arguments bindings target pending (values ++ [value]) (index + 1)) [], frames := rest }
  | binding_return {source : Configuration} {answers : List Atom} {bindings : Subst}
      {pattern body : Atom} {rest : List Frame}
      (control : source.control = .returned answers)
      (frames : source.frames = .bind bindings pattern body :: rest) :
      Transition program source
        { source with control := .sequence (answers.filterMap fun value =>
            (SpaceSemantics.matchBinding bindings pattern value).map
              fun bound => .evaluate bound body) [], frames := rest }
  | case_return {source : Configuration} {answers : List Atom} {bindings : Subst}
      {cases : Cases} {rest : List Frame}
      (control : source.control = .returned answers)
      (frames : source.frames = .select bindings cases :: rest) :
      Transition program source
        { source with control := .sequence (answers.filterMap fun value =>
            (SpaceSemantics.selectCase bindings value cases).map
              fun (bound, body) => .evaluate bound body) [], frames := rest }
  | if_return {source : Configuration} {answers : List Atom} {bindings : Subst}
      {yes no : Atom} {rest : List Frame}
      (control : source.control = .returned answers)
      (frames : source.frames = .branch bindings yes no :: rest) :
      Transition program source
        { source with control := .sequence (answers.map fun value =>
            .evaluate bindings (if value == Effects.boolean true then yes else no)) [], frames := rest }
  /-- `(match space pattern body)` evaluates `space`; the pattern and body are
  held as written (translator.pl:289-292 at b74af1b). -/
  | query_enter {source : Configuration} {bindings : Subst} {space pattern body : Atom}
      (control : source.control = .evaluate bindings
        (.expression [.symbol "match", space, pattern, body])) :
      Transition program source
        { source with
          control := .evaluate bindings space
          frames := .query bindings pattern body :: source.frames }
  /-- Each space value is queried in turn: the body runs once per matching row. -/
  | query_return {source : Configuration} {answers : List Atom} {bindings : Subst}
      {pattern body : Atom} {rest : List Frame}
      (control : source.control = .returned answers)
      (frames : source.frames = .query bindings pattern body :: rest) :
      Transition program source
        { source with control := .sequence (answers.flatMap fun space =>
            queryAlternatives source.state bindings space pattern body) [], frames := rest }

/-- The whole-program judgment for finite execution in this profile. Completed
results retain the entire store and the ordered remaining input/output. -/
inductive Runs (program : Program) : Configuration → Outcome → Prop where
  | completed {source : Configuration} {answers : List Atom}
      (control : source.control = .returned answers) (frames : source.frames = []) :
      Runs program source (.complete source.state answers source.input source.output)
  | fault {source : Configuration} {reason : Fault}
      (control : source.control = .fault reason) :
      Runs program source (.fault reason source)
  | next {source target : Configuration} {result : Outcome}
      (transition : Transition program source target) (rest : Runs program target result) :
      Runs program source result

/-- Fuel exhaustion never becomes a derivation or a logical refusal. -/
theorem no_exhausted_derivation (program : Program) (source unfinished : Configuration) :
    ¬ Runs program source (.exhausted unfinished) := by
  intro derivation
  generalize resultEq : Outcome.exhausted unfinished = result at derivation
  induction derivation with
  | completed => cases resultEq
  | fault => cases resultEq
  | next _ _ ih => exact ih resultEq

/-! ## Cell support follows the derivation -/

open NamedSpaces.Store

theorem transition_finite_cells {program : SpaceSemantics.Program}
    {source target : Configuration} (finite : FiniteCells source.state)
    (transition : Transition program source target) : FiniteCells target.state := by
  cases transition
  all_goals first
    | exact finite
    | exact StdLib.successful_apply_finite_cells finite (by assumption)

theorem completed_finite_cells {program : SpaceSemantics.Program}
    {source : Configuration} {after : Effects.State}
    {answers input output : List Mettapedia.Languages.MeTTa.OSLFCore.Atom}
    (running : Runs program source (.complete after answers input output))
    (finite : FiniteCells source.state) : FiniteCells after := by
  generalize observation : Outcome.complete after answers input output = result at running
  induction running with
  | completed control frames =>
      cases observation
      exact finite
  | fault control => cases observation
  | next transition running ih =>
      exact ih (transition_finite_cells finite transition) observation

theorem transition_empty_tail {program : SpaceSemantics.Program}
    {source target : Configuration} (vacant : EmptyTail source.state [])
    (transition : Transition program source target) : EmptyTail target.state [] := by
  cases transition
  all_goals first
    | exact vacant
    | exact StdLib.successful_apply_empty_tail vacant (by assumption)

theorem completed_empty_tail {program : SpaceSemantics.Program}
    {source : Configuration} {after : Effects.State}
    {answers input output : List Mettapedia.Languages.MeTTa.OSLFCore.Atom}
    (running : Runs program source (.complete after answers input output))
    (vacant : EmptyTail source.state []) : EmptyTail after [] := by
  generalize observation : Outcome.complete after answers input output = result at running
  induction running with
  | completed control frames =>
      cases observation
      exact vacant
  | fault control => cases observation
  | next transition running ih =>
      exact ih (transition_empty_tail vacant transition) observation

/-- Every completed computation from the loaded store admits an exact finite
store representation. The support list is evidence, not a second state type
or an assumed empty cell table. -/
theorem completed_from_loaded_finite_representation {program : SpaceSemantics.Program}
    {source : Configuration} {after : Effects.State}
    {answers input output : List Mettapedia.Languages.MeTTa.OSLFCore.Atom}
    (initial : source.state = Effects.loaded program)
    (running : Runs program source (.complete after answers input output)) :
    ∃ names, reconstruct after.core [] after.spacesPrefix (after.cellRows names) = after := by
  have finite : FiniteCells source.state := by
    rw [initial]
    exact Effects.loaded_finite_cells program
  have vacant : EmptyTail source.state [] := by
    rw [initial]
    exact Effects.loaded_empty_tail program
  exact finite_reconstruction_exists after [] (completed_finite_cells running finite)
    (completed_empty_tail running vacant)

end Mettapedia.Languages.MeTTa.PeTTa.DeclarativeSpec
