import Mettapedia.Languages.MeTTa.PeTTa.LiveEquations

/-!
# PeTTa by two-way unification

SWI-PeTTa compiles an equation `(= (f p1 .. pn) body)` to a Prolog clause and a
call to a Prolog goal, so a call *unifies* its arguments with the clause head:
both sides may bind. `match` calls the stored rows as goals, so it unifies too,
and `remove-atom` removes the rows that unify with its argument (`retractall`).
Each use of a clause or a stored row renames its variables apart, while the
variables of the request are shared by everything the request runs.

    (= (g $x) (let $x 5 $x))     !(g $u)                     ; 5
    (= (z 0) yes)                !(let $r (z $u) ($r $u))    ; (yes 0)
    (fact $y 2)                  !(match &self (fact 1 $v) $v)   ; 2

This module is that machine. It has the shape of `Eval.step`: the answers of a
subexpression are finished before its continuation runs, and frames are shared
by the alternatives. Unification adds one thing that the answers of `Eval`
cannot carry: **each answer carries the substitution of the branch that
produced it** (`Answer`). In `(let $r (z $u) ($r $u))` with `(= (z 0) yes)` and
`(= (z 1) no)`, the call has two answers, `yes` with `$u = 0` and `no` with
`$u = 1`, and the `let` continues each with its own binding:
`(yes 0)`, `(no 1)`.

* **Terms.** The variables of a request are logic variables. Equation and row
  uses rename variables with a counter suffix (`rename`, from `uses`). The
  raw-entry counterexample in `PeTTaLambdaControls` shows why a legal caller
  name cannot be used as an unscoped logical identity. `ScopedSource` admits
  request variables in their own activation and retains the reached supply
  across requests. Parsing, input, enumeration and assignment copy variables
  at the corresponding boundary. The full world/readout invariant is separate
  from the checked entry and unifier-support results.
  A substitution is kept idempotent: no bound
  variable occurs in a bound value (`bindVar`), so `resolve` is one pass.
* **Unification** (`unifyTerms`) is first-order, with the occurs check: where
  SWI-PeTTa's default unification would build a cyclic term, there is no
  unifier. This is SWI-PeTTa run with the Prolog flag `occurs_check` set to
  `true`, and it is what CeTTa's PeTTa lane does. It runs on fuel; running out
  is never read as a failed unification: the step stops, and the run is
  `exhausted`.
* **Patterns with the list view** (`unifyPattern`): an equation head, a `let`
  pattern and a `case` pattern read `(cons a b)` as a list with head `a` and
  tail `b`, as PeTTa compiles them (`constrain_args`). Met by an unbound
  variable, `(cons a b)` binds it to the expression `(cons a b)`, which is how
  the runtimes print the open list they build; a later binding of its tail is
  not read as a list, since the finite carrier has no open lists
  (`Controls.open_list_tail_is_not_a_list`). A `match` pattern has no list view
  (the runtimes match `(cons $a $b)` literally there).
* **Equations are live.** A request is classified against the program as it
  stands when the request starts (`LiveEquations.atState`): whether `(f ..)` is a
  call, a partial application, an over-application or data (P-APP-1). A call
  selects among the `=` rows of `&self` that are live when it runs, in row
  order (P-APP-3).
* **`collapse`** collects copies of its answers, as Prolog's `findall`: each
  copy is resolved and renamed apart, and no binding made inside leaves it.
* **`remove-atom`** removes every row of the space that unifies with its
  argument, the row renamed apart and nothing bound (`retractall`). For an `=`
  row it answers whether some row was removed (SWI-PeTTa `e1db30d`), otherwise
  `True`.
* **Runtime heads.** Runtime-dispatch sites receive a computed head and strict
  supplied arguments. Function lookup and arity read the live equations. A
  private partial reuses its resolved captures without evaluating them again;
  authored data merely spelled `partial` is not that carrier. Runtime `match`
  unifies freshly copied rows and returns its already evaluated template under
  each branch's bindings. Written `match` instead schedules its body after
  selection. These two routes cannot share a second template-evaluation pass.
* **Runtime exceptions.** A runtime call catches exceptions in its invoked
  goal, retaining completed root answers and the reached effects. Arity
  rejection occurs before entering that goal. A fault with no runtime-call
  boundary remains an uncaught fault.

This remains the completed-operand profile. Source-to-runtime admission for
statically known computed heads, lambda authoring/installation, native partial
arity profiles and streaming operand schedules are separate obligations. In
particular the runtime argument policy here is SWI's dispatch policy, not a
claim that every corrected CeTTa profile uses it.

`Eval.step` is the matching machine with fixed equations. On ground calls and
ground rows the two select the same equations and rows with the same bindings
(`UnifyingGround`, `UnifyingRename`). The rules of this machine and the
adequacy of its runner are in `UnifyingSpec`, the soundness of its unifier in
`UnifyingSound`, its controls in `UnifyingControls`, and its reading as a
transform step in `UnifyingTransform`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Unifying

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst atomFreeVars)
open SpaceSemantics (Program Equation Cases)
open Effects (State Fault)
open Eval (Target ioHead argumentIsRaw readCases nestedLets arities knownArities partialValue)
open LiveEquations (liveEquations atState equationOfRow Observation)

/-- Recognize the private partial carrier, not authored syntax headed by the
symbol `partial`. Its stored arguments are values, never requests to evaluate. -/
def partial? : Atom → Option (String × List Atom)
  | .expression [.grounded (.custom "PeTTa.Partial" ""), .symbol head, .expression captured] =>
      some (head, captured)
  | _ => none

theorem partial?_some (value : Atom) (head : String) (captured : List Atom) :
    partial? value = some (head, captured) ↔ value = partialValue head captured := by
  constructor
  · intro recognized
    unfold partial? at recognized
    split at recognized
    · cases recognized
      rfl
    · cases recognized
  · rintro rfl
    rfl

/-- These heads are determined by evaluation rather than a written function
name. Literal scalar heads remain data constructors. -/
def dynamicItems : List Atom → Bool
  | .var _ :: _ | .expression _ :: _ => true
  | _ => false

/-! ## Unification -/

/-- The outcome of a fuelled unification: a unifier, none, or out of fuel. -/
inductive Unified where
  | ok (bindings : Subst)
  | clash
  | exhausted
  deriving Repr, DecidableEq

/-- Continue with the unifier, if there is one. -/
def Unified.andThen : Unified → (Subst → Unified) → Unified
  | .ok bindings, next => next bindings
  | .clash, _ => .clash
  | .exhausted, _ => .exhausted

@[simp] theorem Unified.ok_andThen (bindings : Subst) (next : Subst → Unified) :
    (Unified.ok bindings).andThen next = next bindings := rfl

@[simp] theorem Unified.clash_andThen (next : Subst → Unified) :
    Unified.clash.andThen next = .clash := rfl

@[simp] theorem Unified.exhausted_andThen (next : Subst → Unified) :
    Unified.exhausted.andThen next = .exhausted := rfl

/-- The value of `term` under `bindings`. The substitutions built here are
idempotent, so one pass resolves. -/
abbrev resolve (bindings : Subst) (term : Atom) : Atom := applySubst bindings term

/-- Whether the variable `name` occurs in `term`. -/
def occurs (name : String) (term : Atom) : Bool := (atomFreeVars term).contains name

/-- Bind the unbound variable `name` to the resolved `term`, keeping the
substitution idempotent: `name` is replaced in the values already bound. -/
def bindVar (bindings : Subst) (name : String) (term : Atom) : Subst :=
  (name, term) :: bindings.map fun binding => (binding.1, applySubst [(name, term)] binding.2)

/-- Unify two lists element by element, threading the substitution. -/
def unifyLists (unify : Subst → Atom → Atom → Unified) : Subst → List Atom → List Atom → Unified
  | bindings, [], [] => .ok bindings
  | bindings, first :: rest, other :: others =>
      (unify bindings first other).andThen fun bound => unifyLists unify bound rest others
  | _, _, _ => .clash

/-- First-order unification with the occurs check. Both sides are resolved
before they are compared, so a variable bound earlier is compared by its
value, and either side may bind. -/
def unifyTerms : Nat → Subst → Atom → Atom → Unified
  | 0, _, _, _ => .exhausted
  | fuel + 1, bindings, left, right =>
      match resolve bindings left, resolve bindings right with
      | .var name, .var other =>
          if name = other then .ok bindings else .ok (bindVar bindings name (.var other))
      | .var name, term =>
          if occurs name term then .clash else .ok (bindVar bindings name term)
      | term, .var name =>
          if occurs name term then .clash else .ok (bindVar bindings name term)
      | .symbol name, .symbol other => if name = other then .ok bindings else .clash
      | .grounded value, .grounded other => if value = other then .ok bindings else .clash
      | .expression items, .expression others => unifyLists (unifyTerms fuel) bindings items others
      | _, _ => .clash

/-- Unification of a pattern with PeTTa's list view against a value, by the
case order of `SpaceSemantics.matchValue`. `(cons a b)` against a nonempty
expression unifies `a` with its head and `b` with its tail; against an unbound
variable it binds the variable to `(cons a b)`; against anything else it fails.
Every other pattern is unified element by element. -/
def unifyPattern : Nat → Subst → Atom → Atom → Unified
  | 0, _, _, _ => .exhausted
  | fuel + 1, bindings, pattern, value =>
      match pattern, resolve bindings value with
      | .expression [.symbol "cons", first, rest], .expression (head :: tail) =>
          (unifyPattern fuel bindings first head).andThen fun bound =>
            unifyPattern fuel bound rest (.expression tail)
      | .expression [.symbol "cons", _, _], .var _ => unifyTerms fuel bindings pattern value
      | .expression [.symbol "cons", _, _], _ => .clash
      | .expression patterns, .expression values =>
          unifyLists (unifyPattern fuel) bindings patterns values
      | .expression _, .var _ => unifyTerms fuel bindings pattern value
      | .expression _, _ => .clash
      | _, _ => unifyTerms fuel bindings pattern value

/-- The number of constructors in a term. -/
def atomSize : Atom → Nat
  | .var _ | .symbol _ | .grounded _ => 1
  | .expression items => listSize items + 1
where
  listSize : List Atom → Nat
    | [] => 0
    | first :: rest => atomSize first + listSize rest

/-- The fuel given to one unification of `left` with `right`. -/
def fuelFor (bindings : Subst) (left right : Atom) : Nat :=
  atomSize left + atomSize right + atomSize (resolve bindings left) +
    atomSize (resolve bindings right) + 1

/-- A pattern with the list view, unified with a value. -/
def unifyAsPattern (bindings : Subst) (pattern value : Atom) : Unified :=
  unifyPattern (fuelFor bindings pattern value) bindings pattern value

/-- Two terms, unified. -/
def unify (bindings : Subst) (left right : Atom) : Unified :=
  unifyTerms (fuelFor bindings left right) bindings left right

/-- A call's argument list against an equation's argument patterns: element by
element, each argument pattern with the list view. The list itself is never
read through the list view, so `(h 1 2)` does not select `(= (h cons $a $b) $b)`. -/
def unifyArguments (bindings : Subst) (patterns values : List Atom) : Unified :=
  unifyLists (unifyPattern (fuelFor bindings (.expression patterns) (.expression values)))
    bindings patterns values

/-- A `let` pattern: a quoted pattern is literal syntax (no list view), as in
`SpaceSemantics.matchBinding`; every other pattern has the list view. -/
def unifyBinding (bindings : Subst) (pattern value : Atom) : Unified :=
  match pattern with
  | .expression [.symbol "quote", literal] => unify bindings literal value
  | _ => unifyAsPattern bindings pattern value

/-! ## Renaming apart -/

/-- The name of the variable `name` in the use numbered `use`. -/
def freshName (use : Nat) (name : String) : String := name ++ "#" ++ toString use

/-- The variables of a term renamed for the use numbered `use`. -/
def rename (use : Nat) : Atom → Atom
  | .var name => .var (freshName use name)
  | .symbol name => .symbol name
  | .grounded value => .grounded value
  | .expression items => .expression (renameList use items)
where
  renameList (use : Nat) : List Atom → List Atom
    | [] => []
    | first :: rest => rename use first :: renameList use rest

/-! ## The machine -/

/-- An answer: a value, resolved, and the substitution of the branch that
produced it. -/
structure Answer where
  value : Atom
  bindings : Subst
  deriving Repr, DecidableEq

inductive Control where
  | evaluate (bindings : Subst) (expression : Atom)
  /-- Runtime dispatch after the head and all supplied arguments are values. -/
  | dynamic (bindings : Subst) (head : Atom) (values : List Atom)
  | arguments (bindings : Subst) (target : Target) (remaining values : List Atom) (index : Nat)
  | sequence (remaining : List Control) (answers : List Answer)
  | returned (answers : List Answer)
  | fault (reason : Fault)
  deriving Repr

/-- A frame waits for the answers of a subexpression. It holds no substitution:
each answer brings its own. `collect` keeps the substitution of the `collapse`,
which continues without the bindings made inside. -/
inductive Frame where
  | bind (pattern body : Atom)
  | select (cases : Cases)
  | branch (yes no : Atom)
  | collect (bindings : Subst)
  | argument (target : Target) (remaining values : List Atom) (index : Nat)
  | sequence (remaining : List Control) (answers : List Answer)
  | query (pattern body : Atom)
  /-- The strict data-argument traversal has built the head/argument vector. -/
  | dispatch
  /-- Runtime reduce/2 catches exceptions raised by the invoked goal. -/
  | dynamicCall
  deriving Repr

/-- Recover completed root alternatives at the nearest runtime-call boundary.
Nested root collectors contribute in discovery order. A pending operand or
binding continuation makes its inner answers tentative, so that prefix is
discarded before the outer root collectors are visited. The reached store,
I/O and use counter are deliberately not restored. -/
def recoverDynamic : List Answer → List Frame → Option (List Answer × List Frame)
  | _, [] => none
  | earned, .dynamicCall :: rest => some (earned, rest)
  | earned, .sequence _ completed :: rest => recoverDynamic (completed ++ earned) rest
  | _, _ :: rest => recoverDynamic [] rest

/-- Saturated authored calls run a goal. Partial and over-applied calls do
not enter that goal, so their classification stays outside its error scope. -/
def invocationFrames (control : Control) (frames : List Frame) : List Frame :=
  match control with
  | .sequence _ _ => .dynamicCall :: frames
  | _ => frames

theorem invocationFrames_append (control : Control) (frames suffix : List Frame) :
    invocationFrames control (frames ++ suffix) = invocationFrames control frames ++ suffix := by
  cases control <;> rfl

theorem recoverDynamic_append (frames suffix : List Frame) (earned answers : List Answer)
    (remaining : List Frame) (recovered : recoverDynamic earned frames = some (answers, remaining)) :
    recoverDynamic earned (frames ++ suffix) = some (answers, remaining ++ suffix) := by
  induction frames generalizing earned with
  | nil => cases recovered
  | cons frame rest ih =>
      cases frame with
      | dynamicCall =>
          simp only [recoverDynamic, Option.some.injEq, Prod.mk.injEq] at recovered
          rcases recovered with ⟨rfl, rfl⟩
          rfl
      | sequence pending completed => exact ih (completed ++ earned) recovered
      | _ => exact ih [] recovered

structure Configuration where
  state : State
  control : Control
  frames : List Frame := []
  input : List Atom := []
  output : List Atom := []
  /-- The next use number for renaming apart. -/
  uses : Nat := 0
  /-- Translator-installed clauses are callable but are not atoms of `&self`.
  The staging owner retains this immutable inventory across requests. -/
  privateCode : List Equation := []

inductive Outcome where
  | complete (state : State) (answers : List Atom) (input output : List Atom)
  | exhausted (configuration : Configuration)
  | fault (reason : Fault) (configuration : Configuration)

/-- The equations of `head` that `live` records with `count` arguments, in row
order, each with its index among them. -/
def candidates (live : List Equation) (head : String) (count : Nat) : List Equation :=
  live.filter fun equation => equation.head == head && equation.arguments.length == count

/-- The alternatives of a call: for each candidate equation, renamed apart for
its own use, its body under the unifier of its head with the arguments.
`none` when a unification ran out of fuel. -/
def selections (bindings : Subst) (values : List Atom) :
    Nat → List Equation → Option (List Control)
  | _, [] => some []
  | use, equation :: rest => do
      let others ← selections bindings values (use + 1) rest
      match unifyArguments bindings (equation.arguments.map (rename use)) values with
      | .ok bound => some (.evaluate bound (rename use equation.body) :: others)
      | .clash => some others
      | .exhausted => none

/-- The control of a call of an authored function translated against
`registry`, selecting from the `live` equations, and the number of uses it
took. The registry decides by the arity (P-APP-1), as in
`LiveEquations.liveApplication`. -/
def application (registry : Program) (live : List Equation) (head : String)
    (values : List Atom) (bindings : Subst) (use : Nat) : Option (Control × Nat) :=
  if values.length ∈ arities registry head then
    let chosen := candidates live head values.length
    (selections bindings values use chosen).map fun selected =>
      (.sequence selected [], chosen.length)
  else if (arities registry head).all (· < values.length) &&
      !(arities registry head).isEmpty then
    some (.fault (.overApplication head (knownArities registry head) values.length), 0)
  else some (.returned [⟨partialValue head values, bindings⟩], 0)

/-- Private generated clauses precede later public definitions of their fresh
name. Space inspection/removal still sees only the actual public rows. -/
def codeEquations (state : State) (privateCode : List Equation) : List Equation :=
  privateCode ++ liveEquations state

def codeRegistry (registry : Program) (privateCode : List Equation) : Program :=
  {registry with equations := privateCode ++ registry.equations}

def runtimeRegistry (registry : Program) (state : State) (privateCode : List Equation) : Program :=
  {registry with equations := codeEquations state privateCode}

/-- Runtime lookup uses current public equations and installed private code.
Runtime type-declaration mutation remains outside this source profile. -/
def runtimeCallable (state : State) (value : Atom) (privateCode : List Equation := []) : Bool :=
  match value with
  | .symbol head => ioHead head || StdLib.known head ||
      (codeEquations state privateCode).any (·.head == head)
  | _ => false

def dispatchAnswer (answer : Answer) : Control :=
  match answer.value with
  | .expression (head :: values) => .dynamic answer.bindings head values
  | _ => .returned [answer]

/-- Whether an atom is an `=` row with a call head. -/
def equationRow (atom : Atom) : Bool := (equationOfRow atom).isSome

/-- The rows that survive the removal of `pattern`: a row is removed when it
unifies with `pattern`, renamed apart for its own use and binding nothing
outside the test. `none` when a unification ran out of fuel. -/
def survivors (pattern : Atom) : Nat → List Atom → Option (List Atom)
  | _, [] => some []
  | use, row :: rest => do
      let kept ← survivors pattern (use + 1) rest
      match unify [] pattern (rename use row) with
      | .ok _ => some kept
      | .clash => some (row :: kept)
      | .exhausted => none

/-- `remove-atom` by unification. A variable removes nothing and answers
`True`, and a symbol or a number removes nothing and has no answer, as in
`StdLib.apply`. -/
def removeRows (state : State) (location pattern : Atom) (use : Nat) :
    Option (Except Fault (State × List Atom × Nat)) :=
  match Effects.readHandle location with
  | none => some (.error .invalidSpace)
  | some handle =>
      match state.read handle with
      | none => some (.error .invalidSpace)
      | some rows =>
          match pattern with
          | .var _ => some (.ok (state, [Effects.boolean true], 0))
          | .expression (_ :: _) =>
              (survivors pattern use rows).map fun kept =>
                match state.write handle kept with
                | some after =>
                    let answer := if equationRow pattern then kept.length < rows.length else true
                    .ok (after, [Effects.boolean answer], rows.length)
                | none => .error .invalidSpace
          | _ => some (.ok (state, [], 0))

/-- The bodies a `match` runs on `rows`: the body once for each row that
unifies with the pattern, the row renamed apart for its own use, in row order.
`none` when a unification ran out of fuel. -/
def queryBodies (bindings : Subst) (pattern body : Atom) :
    Nat → List Atom → Option (List Control)
  | _, [] => some []
  | use, row :: rest => do
      let others ← queryBodies bindings pattern body (use + 1) rest
      match unify bindings pattern (rename use row) with
      | .ok bound => some (.evaluate bound body :: others)
      | .clash => some others
      | .exhausted => none

/-- Runtime `match` receives values: its template has already completed its
argument evaluation. Return it under each row's unifier without evaluating it
again. Open row variables are freshly copied and caller bindings escape. -/
def matchAnswers (bindings : Subst) (pattern template : Atom) :
    Nat → List Atom → Option (List Answer)
  | _, [] => some []
  | use, row :: rest => do
      let others ← matchAnswers bindings pattern template (use + 1) rest
      match unify bindings pattern (rename use row) with
      | .ok bound => some (⟨resolve bound template,bound⟩ :: others)
      | .clash => some others
      | .exhausted => none

/-- The value-level native call differs from the written `match` control:
the latter schedules body computation after each match. -/
def matchCall (state : State) (bindings : Subst) (use : Nat) (values : List Atom) :
    Option (Except Fault (List Answer × Nat)) :=
  match values with
  | [location,pattern,template] =>
      match Effects.readHandle location >>= state.read with
      | none => some (.error .invalidSpace)
      | some rows => (matchAnswers bindings pattern template use rows).map fun answers =>
          .ok (answers,rows.length)
  | _ => some (.error (.invalidArguments "match"))

/-- The alternatives of `match` on the space values `answers`, and the uses
they took; a value that is not a space is an invalid-space fault. -/
def queries (state : State) (pattern body : Atom) :
    Nat → List Answer → Option (List Control × Nat)
  | _, [] => some ([], 0)
  | use, answer :: rest =>
      match Effects.readHandle answer.value >>= state.read with
      | some rows => do
          let here ← queryBodies answer.bindings pattern body use rows
          let (others, used) ← queries state pattern body (use + rows.length) rest
          some (here ++ others, rows.length + used)
      | none => do
          let (others, used) ← queries state pattern body use rest
          some (.fault .invalidSpace :: others, used)

/-- The continuation of each answer of a `let` value. -/
def bindAnswers (pattern body : Atom) : List Answer → Option (List Control)
  | [] => some []
  | answer :: rest => do
      let others ← bindAnswers pattern body rest
      match unifyBinding answer.bindings pattern answer.value with
      | .ok bound => some (.evaluate bound body :: others)
      | .clash => some others
      | .exhausted => none

/-- The first case whose pattern unifies with the value: committed choice, as
PeTTa's `(Key = Pattern -> Then ; Next)`. -/
def selectCase (bindings : Subst) (value : Atom) : Cases → Option (Option (Subst × Atom))
  | [] => some none
  | (pattern, body) :: rest =>
      match unifyAsPattern bindings pattern value with
      | .ok bound => some (some (bound, body))
      | .clash => selectCase bindings value rest
      | .exhausted => none

/-- The continuation of each answer of a `case` key. -/
def selectAnswers (cases : Cases) : List Answer → Option (List Control)
  | [] => some []
  | answer :: rest => do
      let others ← selectAnswers cases rest
      match ← selectCase answer.bindings answer.value cases with
      | some (bound, body) => some (.evaluate bound body :: others)
      | none => some others

/-- Copies of the answers of a `collapse`, each resolved and renamed apart for
its own use, as `findall` copies its solutions. -/
def copies (use : Nat) : List Answer → List Atom
  | [] => []
  | answer :: rest => rename use (resolve answer.bindings answer.value) :: copies (use + 1) rest

/-- Newly parsed syntax and enumerated stored rows contain fresh variables;
equal printed names in different returned occurrences do not share identities. -/
def copyTerms (use : Nat) : List Atom → List Atom
  | [] => []
  | value :: rest => rename use value :: copyTerms (use + 1) rest

def primitiveCopies (head : String) : Bool := head == "parse" || head == "get-atoms"

/-- SWI's non-backtrackable assignment copies the assigned term. A subsequent
read returns the retained value, rather than copying it a second time. -/
def primitiveInputs (head : String) (use : Nat) (values : List Atom) : List Atom :=
  match head, values with
  | "change-state!", [name,value] => [name,rename use value]
  | _, _ => values

def primitiveOutputs (head : String) (use : Nat) (answers : List Atom) : List Atom :=
  if primitiveCopies head then copyTerms use answers else answers

def primitiveUses (head : String) (answers : List Atom) : Nat :=
  if head = "change-state!" then 1 else if primitiveCopies head then answers.length else 0

/-- One step of a request translated against `registry`. -/
def step (registry : Program) (configuration : Configuration) : Option Configuration :=
  let state := configuration.state
  let frames := configuration.frames
  let use := configuration.uses
  let advance := fun control => some { configuration with control }
  let push := fun frame bindings expression =>
    some { configuration with control := .evaluate bindings expression, frames := frame :: frames }
  match configuration.control with
  | .fault _ =>
      match recoverDynamic [] frames with
      | none => none
      | some (earned, rest) => some { configuration with control := .returned earned, frames := rest }
  | .dynamic bindings callee supplied =>
      let callee := resolve bindings callee
      let values := supplied.map (resolve bindings)
      match partial? callee with
      | some (head, captured) => advance (.dynamic bindings (.symbol head) (captured ++ values))
      | none =>
          match callee with
          | .symbol head =>
              if ioHead head || StdLib.known head then
                some { configuration with
                  control := .arguments bindings (.function head) [] values 0
                  frames := .dynamicCall :: frames }
              else if (codeEquations state configuration.privateCode).any (·.head == head) then
                match application (runtimeRegistry registry state configuration.privateCode)
                    (codeEquations state configuration.privateCode) head values bindings use with
                | some (control, used) => some { configuration with
                    control, uses := use + used, frames := invocationFrames control frames }
                | none => none
              else advance (.returned [⟨.expression (.symbol head :: values), bindings⟩])
          | _ => advance (.returned [⟨.expression (callee :: values), bindings⟩])
  | .sequence [] answers => advance (.returned answers)
  | .sequence (first :: rest) answers =>
      some { configuration with control := first, frames := .sequence rest answers :: frames }
  | .arguments bindings target [] held _ =>
      let values := held.map (resolve bindings)
      match target with
      | .data => advance (.returned [⟨.expression values, bindings⟩])
      | .function head =>
          if ioHead head then
            match head, values with
            | "readln!", [] =>
                match configuration.input with
                | [] => advance (.returned [⟨.symbol "end_of_file", bindings⟩])
                | first :: rest =>
                    some { configuration with
                      input := rest
                      control := .returned [⟨rename use first, bindings⟩]
                      uses := use + 1 }
            | "println!", [value] =>
                some { configuration with
                  output := configuration.output ++ [value]
                  control := .returned [⟨Effects.boolean true, bindings⟩] }
            | "eval", [code] => advance (.evaluate bindings code)
            | _, _ => advance (.fault (.invalidArguments head))
          else if head = "remove-atom" then
            match values with
            | [location, pattern] =>
                match removeRows state location pattern use with
                | some (.ok (after, answers, used)) =>
                    some { configuration with
                      state := after
                      control := .returned (answers.map fun value => ⟨value, bindings⟩)
                      uses := use + used }
                | some (.error fault) => advance (.fault fault)
                | none => none
            | _ => advance (.fault (.invalidArguments head))
          else if head = "match" then
            match matchCall state bindings use values with
            | some (.ok (answers,used)) =>
                some {configuration with control := .returned answers, uses := use + used}
            | some (.error fault) => advance (.fault fault)
            | none => none
          else if StdLib.known head then
            match StdLib.apply state head (primitiveInputs head use values) with
            | .ok (after, answers) =>
                some { configuration with
                  state := after
                  control := .returned ((primitiveOutputs head use answers).map fun value => ⟨value, bindings⟩)
                  uses := use + primitiveUses head answers }
            | .error fault => advance (.fault fault)
          else
            match application (codeRegistry registry configuration.privateCode)
                (codeEquations state configuration.privateCode) head values bindings use with
            | some (control, used) => some { configuration with control, uses := use + used }
            | none => none
  | .arguments bindings target (first :: rest) values index =>
      let frame := Frame.argument target rest values index
      let raw := match target with
        | .function head => argumentIsRaw registry head index
        | .data => false
      if raw then
        some { configuration with
          control := .returned [⟨resolve bindings first, bindings⟩], frames := frame :: frames }
      else push frame bindings first
  | .evaluate bindings expression =>
      match expression with
      | .var _ => advance (.returned [⟨resolve bindings expression, bindings⟩])
      | .symbol _ | .grounded _ => advance (.returned [⟨expression, bindings⟩])
      | .expression [.symbol "let", pattern, value, body] =>
          push (.bind pattern body) bindings value
      | .expression [.symbol "let*", .expression pairs, body] =>
          match nestedLets pairs body with
          | some nested => advance (.evaluate bindings nested)
          | none => advance (.fault (.invalidArguments "let*"))
      | .expression [.symbol "case", value, .expression rows] =>
          match readCases rows with
          | some cases => push (.select cases) bindings value
          | none => advance (.fault (.invalidArguments "case"))
      | .expression [.symbol "if", condition, yes, no] =>
          push (.branch yes no) bindings condition
      | .expression [.symbol "collapse", expression] => push (.collect bindings) bindings expression
      | .expression [.symbol "superpose", .expression alternatives] =>
          advance (.sequence (alternatives.map (.evaluate bindings)) [])
      | .expression [.symbol "empty"] => advance (.returned [])
      | .expression [.symbol "quote", expression] =>
          advance (.returned [⟨resolve bindings expression, bindings⟩])
      | .expression [.symbol "match", space, pattern, body] =>
          push (.query pattern body) bindings space
      | .expression (.symbol head :: arguments) =>
          if ioHead head || StdLib.known head ||
              (codeRegistry registry configuration.privateCode).equations.any (·.head == head) then
            advance (.arguments bindings (.function head) arguments [] 0)
          else advance (.arguments bindings .data (.symbol head :: arguments) [] 0)
      | .expression items =>
          match partial? (.expression items) with
          | some _ => advance (.returned [⟨resolve bindings (.expression items), bindings⟩])
          | none =>
              if dynamicItems items then
                some { configuration with
                  control := .arguments bindings .data items [] 0
                  frames := .dispatch :: frames }
              else advance (.arguments bindings .data items [] 0)
  | .returned answers =>
      match frames with
      | [] => none
      | frame :: rest =>
          let resume := fun control => some { configuration with control, frames := rest }
          match frame with
          | .collect outer =>
              some { configuration with
                control := .returned [⟨.expression (copies use answers), outer⟩]
                frames := rest
                uses := use + answers.length }
          | .sequence pending collected => resume (.sequence pending (collected ++ answers))
          | .argument target pending values index =>
              resume (.sequence (answers.map fun answer =>
                .arguments answer.bindings target pending (values ++ [answer.value]) (index + 1)) [])
          | .bind pattern body =>
              (bindAnswers pattern body answers).bind fun continued => resume (.sequence continued [])
          | .select cases =>
              (selectAnswers cases answers).bind fun continued => resume (.sequence continued [])
          | .branch yes no =>
              resume (.sequence (answers.map fun answer =>
                .evaluate answer.bindings
                  (if answer.value == Effects.boolean true then yes else no)) [])
          | .query pattern body =>
              (queries state pattern body use answers).bind fun (continued, used) =>
                some { configuration with
                  control := .sequence continued []
                  frames := rest
                  uses := use + used }
          | .dispatch => resume (.sequence (answers.map dispatchAnswer) [])
          | .dynamicCall => resume (.returned answers)

/-- The fuelled runner. Completed answers are the values resolved under their
own branches. -/
def run (registry : Program) : Nat → Configuration → Outcome
  | fuel, configuration =>
      match configuration.control, configuration.frames with
      | .returned answers, [] =>
          .complete configuration.state (answers.map fun answer => resolve answer.bindings answer.value)
            configuration.input configuration.output
      | .fault fault, frames =>
          match recoverDynamic [] frames with
          | none => .fault fault configuration
          | some _ =>
              match fuel with
              | 0 => .exhausted configuration
              | fuel + 1 =>
                  match step registry configuration with
                  | some next => run registry fuel next
                  | none => .exhausted configuration
      | _, _ =>
          match fuel with
          | 0 => .exhausted configuration
          | fuel + 1 =>
              match step registry configuration with
              | some next => run registry fuel next
              | none => .exhausted configuration

/-- Raw machine entry with no bindings or uses. Scoped source admission is
provided by `ScopedSource`; this constructor alone does not ensure freshness. -/
def start (state : State) (expression : Atom) : Configuration :=
  { state, control := .evaluate [] expression }

/-- Raw-entry controls run in order, retaining stores but resetting local use
numbers. `ScopedSource.requests` is the source driver which also retains the
reached identity supply. A request that does not complete ends either list. -/
def requests (program : Program) (fuel : Nat) : State → List Atom → List Outcome
  | _, [] => []
  | state, request :: rest =>
      match run (atState program state) fuel (start state request) with
      | .complete after answers input output =>
          .complete after answers input output :: requests program fuel after rest
      | outcome => [outcome]

/-- What a request shows: its answers when it completes without reading input or
printing, or its fault. -/
def observed : Outcome → Observation
  | .complete _ answers [] [] => .answers answers
  | .fault reason _ => .fault reason
  | _ => .other

/-- What a request prints and answers when it completes, or its fault. -/
inductive Shown where
  | printed (output answers : List Atom)
  | fault (reason : Fault)
  | other
  deriving DecidableEq

def shown : Outcome → Shown
  | .complete _ answers [] output => .printed output answers
  | .fault reason _ => .fault reason
  | _ => .other

end Mettapedia.Languages.MeTTa.PeTTa.Unifying
