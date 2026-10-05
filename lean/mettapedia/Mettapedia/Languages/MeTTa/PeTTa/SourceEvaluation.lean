import Mettapedia.Languages.MeTTa.PeTTa.SourcePrimitives
import Mettapedia.Languages.MeTTa.PeTTa.TypeSystem
import Mettapedia.GSLT.Core.GSLT

/-!
# An executable machine for closed, saturated PeTTa source

This machine evaluates source programs, independently of any guest checker.
Variables denote captured values; returning a value never reinterprets it as
code. Function entry gets a fresh local environment. Atom-typed arguments are
data, while other arguments are evaluated. Cases commit to the first matching
row, including when that row subsequently produces no answers.

The supported source forms are let, let*, case, if, collapse, ordinary function
calls, data construction, parsed-line I/O and the ground primitives in
SourcePrimitives. Branch answers retain their order and multiplicity. Space
and state-cell effects are threaded through execution. The selector requires
constructor/list-view patterns; computations inside patterns, open cyclic
unification and partial applications are separate profiles. Raw input reading
is a named boundary.

Every transition handles one control or continuation. Fuel bounds the number
of these transitions, rather than the depth of an MM0 proof. Exhaustion and
primitive faults have distinct results and cannot stand for logical refusal.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.SourceEvaluation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open SourceProgram (Program Cases)
open SourcePrimitives (State Fault)

inductive Target where
  | function (head : String)
  | data
  deriving Repr

inductive Control where
  | evaluate (bindings : Subst) (expression : Atom)
  | arguments (bindings : Subst) (target : Target)
      (remaining values : List Atom) (index : Nat)
  | sequence (remaining : List Control) (answers : List Atom)
  | returned (answers : List Atom)
  | fault (reason : Fault)
  deriving Repr

inductive Frame where
  | bind (bindings : Subst) (pattern body : Atom)
  | select (bindings : Subst) (cases : Cases)
  | branch (bindings : Subst) (yes no : Atom)
  | collect
  | argument (bindings : Subst) (target : Target)
      (remaining values : List Atom) (index : Nat)
  | sequence (remaining : List Control) (answers : List Atom)
  deriving Repr

structure Configuration where
  state : State
  control : Control
  frames : List Frame := []
  input : List Atom := []
  output : List Atom := []

def ioHead (head : String) : Bool := head ∈ ["readln!", "println!", "eval"]

/-- Constructor/list-view patterns cannot invoke the program or a primitive.
The special `cons` pattern is handled by `SourceProgram.matchValue` itself. -/
def passivePattern (program : Program) (pattern : Atom) : Bool :=
  (SourceProgram.patternHeads pattern).all fun head =>
    head == "cons" || !(ioHead head || SourcePrimitives.known head ||
      program.equations.any (·.head == head) ||
      head ∈ ["let", "let*", "case", "if", "collapse"])

def constructorPatterns (program : Program) : Bool :=
  (SourceProgram.programPatterns program).all (passivePattern program)

def argumentIsRaw (program : Program) (head : String) (index : Nat) : Bool :=
  if SourcePrimitives.known head then SourcePrimitives.rawArgument head index
  else
    program.declarations.any fun declaration =>
      match declaration with
      | .expression [.symbol ":", .symbol name, .expression (.symbol "->" :: types)] =>
          name == head && types[index]?.any formalArgumentIsRaw
      | _ => false

def clauses (program : Program) (head : String) (values : List Atom) : List Control :=
  program.equations.filterMap fun equation =>
    if equation.head = head then
      (SourceProgram.matchValue [] (.expression equation.arguments) (.expression values)).map
        fun bindings => .evaluate bindings equation.body
    else none

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

/-- A source transition is chosen from syntax and the existing program, never
from a guest kernel's answer. -/
def step (program : Program) (configuration : Configuration) : Option Configuration :=
  let state := configuration.state
  let frames := configuration.frames
  let advance := fun control => some { configuration with control }
  let push := fun frame bindings expression =>
    some { configuration with control := .evaluate bindings expression, frames := frame :: frames }
  match configuration.control with
  | .fault _ => none
  | .sequence [] answers => advance (.returned answers)
  | .sequence (first :: rest) answers =>
      some { configuration with control := first, frames := .sequence rest answers :: frames }
  | .arguments _ target [] values _ =>
      match target with
      | .data => advance (.returned [.expression values])
      | .function head =>
          if ioHead head then
            match head, values with
            | "readln!", [] =>
                match configuration.input with
                | [] => advance (.returned [.symbol "end_of_file"])
                | first :: rest => some { configuration with input := rest, control := .returned [first] }
            | "println!", [value] =>
                some { configuration with
                  output := configuration.output ++ [value]
                  control := .returned [SourcePrimitives.boolean true] }
            | "eval", [code] => advance (.evaluate [] code)
            | _, _ => advance (.fault (.invalidArguments head))
          else if SourcePrimitives.known head then
            match SourcePrimitives.apply state head values with
            | .ok (after, answers) => some { configuration with state := after, control := .returned answers }
            | .error fault => advance (.fault fault)
          else advance (.sequence (clauses program head values) [])
  | .arguments bindings target (first :: rest) values index =>
      let frame := Frame.argument bindings target rest values index
      let raw := match target with
        | .function head => argumentIsRaw program head index
        | .data => false
      if raw then
        some { configuration with control := .returned [applySubst bindings first], frames := frame :: frames }
      else push frame bindings first
  | .evaluate bindings expression =>
      match expression with
      | .var _ => advance (.returned [applySubst bindings expression])
      | .symbol _ | .grounded _ => advance (.returned [expression])
      | .expression [.symbol "let", pattern, value, body] =>
          push (.bind bindings pattern body) bindings value
      | .expression [.symbol "let*", .expression pairs, body] =>
          match nestedLets pairs body with
          | some nested => advance (.evaluate bindings nested)
          | none => advance (.fault (.invalidArguments "let*"))
      | .expression [.symbol "case", value, .expression rows] =>
          match readCases rows with
          | some cases => push (.select bindings cases) bindings value
          | none => advance (.fault (.invalidArguments "case"))
      | .expression [.symbol "if", condition, yes, no] =>
          push (.branch bindings yes no) bindings condition
      | .expression [.symbol "collapse", expression] => push .collect bindings expression
      | .expression (.symbol head :: arguments) =>
          if ioHead head || SourcePrimitives.known head || program.equations.any (·.head == head) then
            advance (.arguments bindings (.function head) arguments [] 0)
          else advance (.arguments bindings .data (.symbol head :: arguments) [] 0)
      | .expression items => advance (.arguments bindings .data items [] 0)
  | .returned answers =>
      match frames with
      | [] => none
      | frame :: rest =>
          let resume := fun control => some { configuration with control, frames := rest }
          match frame with
          | .collect => resume (.returned [.expression answers])
          | .sequence pending collected => resume (.sequence pending (collected ++ answers))
          | .argument bindings target pending values index =>
              resume (.sequence (answers.map fun value =>
                .arguments bindings target pending (values ++ [value]) (index + 1)) [])
          | .bind bindings pattern body =>
              resume (.sequence (answers.filterMap fun value =>
                (SourceProgram.matchValue bindings pattern value).map
                  fun bound => .evaluate bound body) [])
          | .select bindings cases =>
              resume (.sequence (answers.filterMap fun value =>
                (SourceProgram.selectCase bindings value cases).map
                  fun (bound, body) => .evaluate bound body) [])
          | .branch bindings yes no =>
              resume (.sequence (answers.map fun value =>
                .evaluate bindings (if value == SourcePrimitives.boolean true then yes else no)) [])

inductive Outcome where
  | complete (state : State) (answers input output : List Atom)
  | exhausted (configuration : Configuration)
  | fault (reason : Fault)

def run (program : Program) : Nat → Configuration → Outcome
  | fuel, configuration =>
      match configuration.control, configuration.frames with
      | .returned answers, [] => .complete configuration.state answers configuration.input configuration.output
      | .fault fault, _ => .fault fault
      | _, _ =>
          match fuel with
          | 0 => .exhausted configuration
          | fuel + 1 =>
              match step program configuration with
              | some next => run program fuel next
              | none => .exhausted configuration

def start (state : State) (expression : Atom) : Configuration :=
  { state, control := .evaluate [] expression }

def evaluate (program : Program) (fuel : Nat) (state : State) (expression : Atom) : Outcome :=
  run program fuel (start state expression)

/-- The operational graph has the same source controls and private store as
the executable machine. Equations are literal configuration equality: lexical
binding is represented by environments, not by name-changing graph equations. -/
def theory (program : Program) : Mettapedia.GSLT.GSLT where
  Term := Configuration
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun first second => step program first = some second
  rewrites_resp_left := by
    intro first other second same transition
    subst other
    exact ⟨second, transition, rfl⟩
  rewrites_resp_right := by
    intro first second other transition same
    subst other
    exact transition

theorem step_deterministic (program : Program) (source first second : Configuration)
    (left : (theory program).Step source first)
    (right : (theory program).Step source second) : first = second :=
  Option.some.inj (left.symm.trans right)

/-! ## Control boundaries -/

theorem computed_pattern_is_outside_the_profile :
    passivePattern { equations := [⟨"compute", [.var "x"], .var "x"⟩], declarations := [] }
      (.expression [.symbol "Some", .expression [.symbol "compute", .grounded (.int 7)]]) =
      false := by
  simp [passivePattern, SourceProgram.patternHeads, SourceProgram.patternHeads.nested]

theorem constructor_pattern_is_in_the_profile :
    passivePattern { equations := [⟨"compute", [.var "x"], .var "x"⟩], declarations := [] }
      (.expression [.symbol "Some", .expression [.var "head", .grounded (.int 7)]]) = true := by
  simp [passivePattern, SourceProgram.patternHeads, SourceProgram.patternHeads.nested]
  decide

theorem list_view_pattern_is_in_the_profile :
    passivePattern { equations := [], declarations := [] }
      (.expression [.symbol "cons", .var "first", .var "rest"]) = true := by
  simp [passivePattern, SourceProgram.patternHeads, SourceProgram.patternHeads.nested]

theorem value_occurrence_is_inert (program : Program) (state : State) (bindings : Subst)
    (name : String) (frames : List Frame) :
    step program { state, control := .evaluate bindings (.var name), frames } =
      some { state, control := .returned [applySubst bindings (.var name)], frames } := rfl

theorem completed_empty_is_not_exhausted (program : Program) (fuel : Nat) (state : State) :
    run program fuel { state, control := .returned [], frames := [] } = .complete state [] [] [] := by
  cases fuel <;> simp [run]

theorem returned_false_is_completed (program : Program) (fuel : Nat) (state : State) :
    run program fuel { state, control := .returned [SourcePrimitives.boolean false], frames := [] } =
      .complete state [SourcePrimitives.boolean false] [] [] := by
  cases fuel <;> simp [run]

theorem unfinished_zero_fuel (program : Program) (state : State) (expression : Atom) :
    evaluate program 0 state expression = .exhausted (start state expression) := rfl

end Mettapedia.Languages.MeTTa.PeTTa.SourceEvaluation
