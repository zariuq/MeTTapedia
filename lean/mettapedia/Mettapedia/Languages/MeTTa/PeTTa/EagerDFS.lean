import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ApplicationEquivariance
import Mettapedia.Languages.MeTTa.PeTTa.ProgramReplay
import Mettapedia.Logic.LP.UnificationIdempotence
import Mettapedia.GSLT.Distinction.ProductiveBlocks
import Mettapedia.Util.LinearHash

/-!
# Eager value binding and depth-first continuation delivery

This additive source model uses the existing PeTTa atoms, program selection,
patterns and primitive table. A returned occurrence resumes its caller before
the next alternative. Bindings and frames belong to each alternative; performed
output, input and the named-space store belong to the whole execution.

`collapse` opens an independent search scope. Its caller remains suspended until
that scope exhausts, then receives one expression containing all inner answer
occurrences in order. The scope boundary does not discard performed effects.

The initial section specifies an explicit eager-value source profile. Its
historical module name does not make a native runtime authoritative. Equality
with the existing list-valued evaluator, SWI's static output unification, native
operation registries, native fault-as-value policies or compiled C execution
requires separate conformance evidence. External callback latency is outside
the transition-count contract.

The `Destination` component below separately states the finite structural
relational and eager destination policies. It retains reached equations,
caller destinations and shared effects, with unsupported operations saved
as requests. This extends the source owner without equating the default
relational runtime with the eager profile above. Its native binding reader
and primitive/choice/collection joins remain separate obligations.

The finite `Destination` choice and collection components construct ordered
source instances and independently copied answers before resuming the saved
caller. They retain reached equations, origins, siblings and the shared world.
The old eager collector remains its separate unchanged instance: the ground
negative control below records that its open answers are not yet copied.
The explicit scoped Destination profile below constructs generative loading,
literal child entry, branch refusal, saved control faults and independently
copied completion through the existing retained driver. Associated work and
unserved allocation remain saved requests. Typed and rational regions, dynamic
name creation and an unrestricted default-profile replacement remain separate
obligations. Local world-write laws expose their actual payload premises.

This first-order Atom machine specifies PeTTa's ordered, destination-scoped
depth-first profile. It is not a definition of MeTTa and does not constrain HO
MeTTa Prime. The module and namespace were formerly named
`Mettapedia.Languages.MeTTa.PeTTa.CettaEagerDFS`; the mechanism-based name avoids
suggesting a CeTTa runtime-conformance result.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open SpaceSemantics (Program Cases)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects (State Fault)

/-- The continuation consumes one value occurrence. -/
inductive Frame where
  | argument (bindings : Subst) (target : Eval.Target)
      (remaining values : List Atom) (index : Nat)
  | bind (bindings : Subst) (pattern body : Atom)
  | select (bindings : Subst) (cases : Cases)
  | branch (bindings : Subst) (yes no : Atom)
  deriving Repr

inductive Control where
  | evaluate (bindings : Subst) (expression : Atom)
  | arguments (bindings : Subst) (target : Eval.Target)
      (remaining values : List Atom) (index : Nat)
  | returned (value : Atom)
  | fault (reason : Fault)
  deriving Repr

structure Branch where
  control : Control
  frames : List Frame := []
  deriving Repr

/-- A scope owns its ordered frontier and its answer collection. `caller`
is absent only for the root scope. -/
structure Scope (Work : Type := Branch) (Answer : Type := Atom)
    (Caller : Type := List Frame) where
  frontier : List Work
  collected : List Answer := []
  caller : Option Caller := none
  deriving Repr

/-- These fields are globally threaded, including across failed alternatives.
Neither choice nor collection copies or rolls back this world. -/
structure World where
  state : State
  input : List Atom := []
  output : List Atom := []

structure Configuration (Work : Type := Branch) (Answer : Type := Atom)
    (Caller : Type := List Frame) where
  world : World
  scopes : List (Scope Work Answer Caller)

/-- A local source reduction either replaces the current branch, authorizes
ordered alternatives, enters a delimiter, or delivers a value to that scope. -/
inductive Movement where
  | next (branch : Branch)
  | alternatives (branches : List Branch)
  | collect (bindings : Subst) (expression : Atom) (caller : List Frame)
  | answer (value : Atom)
  deriving Repr

/-- The control syntax of this profile. It treats `match` as a primitive call whose
template is returned as data, as `StdLib.apply` does; the list-valued machine of
`Eval` runs a three-argument `match` body once per row (`DeclarativeSpec.controlForm`).
Bringing this profile's `match` in line with that is open. -/
def eagerControlForm : Atom → Bool
  | .expression [.symbol "let", _, _, _]
  | .expression [.symbol "let*", .expression _, _]
  | .expression [.symbol "case", _, .expression _]
  | .expression [.symbol "if", _, _]
  | .expression [.symbol "if", _, _, _]
  | .expression [.symbol "collapse", _]
  | .expression [.symbol "superpose", .expression _]
  | .expression [.symbol "empty"]
  | .expression [.symbol "quote", _] => true
  | _ => false

/-- Existing equation selection can only return evaluation controls. This
adapter retains the selected bindings, body and the new scalar continuation. -/
def clauseBranch (frames : List Frame) : Eval.Control → Option Branch
  | .evaluate bindings body => some ⟨.evaluate bindings body, frames⟩
  | _ => none

def equationBranches (program : Program) (head : String) (values : List Atom)
    (frames : List Frame) : List Branch :=
  (Eval.clauses program head values).filterMap (clauseBranch frames)

def returnedBranches (values : List Atom) (frames : List Frame) : List Branch :=
  values.map fun value => ⟨.returned value, frames⟩

def rawArgument (program : Program) (target : Eval.Target) (index : Nat) : Bool :=
  match target with
  | .data => false
  | .function head => Eval.argumentIsRaw program head index

/-- Local execution uses the actual shared source helpers and primitive table.
An alternative does not run recursively inside this operation. -/
def localStep (program : Program) (world : World) (branch : Branch) :
    Option (World × Movement) :=
  let resume := fun control frames => some (world, .next ⟨control, frames⟩)
  let replace := fun control => resume control branch.frames
  let push := fun frame bindings expression =>
    resume (.evaluate bindings expression) (frame :: branch.frames)
  match branch.control with
  | .fault _ => none
  | .arguments _ .data [] values _ => replace (.returned (.expression values))
  | .arguments _ (.function head) [] values _ =>
      if Eval.ioHead head then
        match head, values with
        | "readln!", [] =>
            match world.input with
            | [] => replace (.returned (.symbol "end_of_file"))
            | value :: rest => some ({ world with input := rest },
                .next ⟨.returned value, branch.frames⟩)
        | "println!", [value] => some ({ world with output := world.output ++ [value] },
            .next ⟨.returned (Effects.boolean true), branch.frames⟩)
        | "eval", [code] => replace (.evaluate [] code)
        | _, _ => replace (.fault (.invalidArguments head))
      else if StdLib.known head then
        match StdLib.apply world.state head values with
        | .ok (after, answers) => some ({ world with state := after },
            .alternatives (returnedBranches answers branch.frames))
        | .error reason => replace (.fault reason)
      else some (world, .alternatives (equationBranches program head values branch.frames))
  | .arguments bindings target (first :: rest) values index =>
      let frame := Frame.argument bindings target rest values index
      if rawArgument program target index then
        resume (.returned (applySubst bindings first)) (frame :: branch.frames)
      else push frame bindings first
  | .evaluate bindings expression =>
      match expression with
      | .var _ => replace (.returned (applySubst bindings expression))
      | .symbol _ | .grounded _ => replace (.returned expression)
      | .expression [.symbol "let", pattern, value, body] =>
          push (.bind bindings pattern body) bindings value
      | .expression [.symbol "let*", .expression pairs, body] =>
          match Eval.nestedLets pairs body with
          | some nested => replace (.evaluate bindings nested)
          | none => replace (.fault (.invalidArguments "let*"))
      | .expression [.symbol "case", value, .expression rows] =>
          match Eval.readCases rows with
          | some cases => push (.select bindings cases) bindings value
          | none => replace (.fault (.invalidArguments "case"))
      | .expression [.symbol "if", condition, yes, no] =>
          push (.branch bindings yes no) bindings condition
      | .expression [.symbol "if", condition, yes] =>
          push (.branch bindings yes (.expression [.symbol "empty"])) bindings condition
      | .expression [.symbol "collapse", expression] =>
          some (world, .collect bindings expression branch.frames)
      | .expression [.symbol "superpose", .expression alternatives] =>
          some (world, .alternatives
            (alternatives.map fun expression => ⟨.evaluate bindings expression, branch.frames⟩))
      | .expression [.symbol "empty"] => some (world, .alternatives [])
      | .expression [.symbol "quote", expression] => replace (.returned (applySubst bindings expression))
      | .expression (.symbol head :: arguments) =>
          if Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head) then
            replace (.arguments bindings (.function head) arguments [] 0)
          else replace (.arguments bindings .data (.symbol head :: arguments) [] 0)
      | .expression items => replace (.arguments bindings .data items [] 0)
  | .returned value =>
      match branch.frames with
      | [] => some (world, .answer value)
      | frame :: rest =>
          match frame with
          | .argument bindings target pending values index =>
              resume (.arguments bindings target pending (values ++ [value]) (index + 1)) rest
          | .bind bindings pattern body =>
              match SpaceSemantics.matchBinding bindings pattern value with
              | some bound => resume (.evaluate bound body) rest
              | none => some (world, .alternatives [])
          | .select bindings cases =>
              match SpaceSemantics.selectCase bindings value cases with
              | some (bound, body) => resume (.evaluate bound body) rest
              | none => some (world, .alternatives [])
          | .branch bindings yes no =>
              resume (.evaluate bindings (if value == Effects.boolean true then yes else no)) rest

/-- Install a local reduction at the head of the current scope. Choice puts
the authorized branches before the saved alternatives. -/
def install (world : World) (scope : Scope) (pending : List Branch)
    (parents : List Scope) : Movement → Configuration
  | .next branch => ⟨world, { scope with frontier := branch :: pending } :: parents⟩
  | .alternatives branches => ⟨world, { scope with frontier := branches ++ pending } :: parents⟩
  | .collect bindings expression frames =>
      ⟨world, { frontier := [⟨.evaluate bindings expression, []⟩], caller := some frames } ::
        { scope with frontier := pending } :: parents⟩
  | .answer value =>
      ⟨world, { scope with frontier := pending, collected := scope.collected ++ [value] } :: parents⟩

/-- Only exhaustion of the child scope releases its caller. Parent alternatives
remain saved throughout the complete collection. -/
def finishScope (world : World) (rows : List Atom) (frames : List Frame)
    (parent : Scope) (parents : List Scope) : Configuration :=
  ⟨world, { parent with frontier := ⟨.returned (.expression rows), frames⟩ :: parent.frontier } :: parents⟩

def step (program : Program) (configuration : Configuration) : Option Configuration :=
  match configuration.scopes with
  | [] => none
  | scope :: parents =>
      match scope.frontier with
      | [] =>
          match scope.caller, parents with
          | some frames, parent :: rest =>
              some (finishScope configuration.world scope.collected frames parent rest)
          | _, _ => none
      | branch :: pending =>
          (localStep program configuration.world branch).map fun (world, movement) =>
            install world scope pending parents movement

def start (state : State) (expression : Atom) (input : List Atom := []) : Configuration :=
  ⟨⟨state, input, []⟩, [{ frontier := [⟨.evaluate [] expression, []⟩] }]⟩

def answers (configuration : Configuration) : List Atom :=
  configuration.scopes.getLast? |>.map Scope.collected |>.getD []

def fault (configuration : Configuration) : Option Fault := do
  let scope ← configuration.scopes.head?
  let branch ← scope.frontier.head?
  match branch.control with
  | .fault reason => some reason
  | _ => none

def completed (configuration : Configuration) : Bool :=
  match configuration.scopes with
  | [{ frontier := [], caller := none, .. }] => true
  | _ => false

inductive Outcome where
  | complete (configuration : Configuration)
  | exhausted (configuration : Configuration)
  | fault (reason : Fault) (configuration : Configuration)

def observe (configuration : Configuration) : Outcome :=
  match fault configuration with
  | some reason => .fault reason configuration
  | none => if completed configuration then .complete configuration else .exhausted configuration

/-- Running and retaining configurations are independent recursive clients of
the same transition function. -/
def run (program : Program) : Nat → Configuration → Outcome
  | 0, configuration => observe configuration
  | fuel + 1, configuration =>
      match step program configuration with
      | none => observe configuration
      | some next => run program fuel next

def advance (program : Program) : Nat → Configuration → Configuration
  | 0, configuration => configuration
  | fuel + 1, configuration =>
      match step program configuration with
      | none => configuration
      | some next => advance program fuel next

def chunks (program : Program) : List Nat → Configuration → Configuration
  | [], configuration => configuration
  | fuel :: rest, configuration => chunks program rest (advance program fuel configuration)

/-! ## Independently authored source rules -/

/-- The source rules specify scalar continuation delivery. Primitive and
pattern premises refer to their existing semantic operations, never to either
driver's transition function. -/
inductive LocalTransition (program : Program) : World → Branch → World → Movement → Prop where
  | construct {world bindings values index frames} :
      LocalTransition program world ⟨.arguments bindings .data [] values index, frames⟩
        world (.next ⟨.returned (.expression values), frames⟩)
  | read_end {world bindings index frames} (input : world.input = []) :
      LocalTransition program world ⟨.arguments bindings (.function "readln!") [] [] index, frames⟩
        world (.next ⟨.returned (.symbol "end_of_file"), frames⟩)
  | read_line {world bindings index frames value rest} (input : world.input = value :: rest) :
      LocalTransition program world ⟨.arguments bindings (.function "readln!") [] [] index, frames⟩
        { world with input := rest } (.next ⟨.returned value, frames⟩)
  | print {world bindings index frames value} :
      LocalTransition program world ⟨.arguments bindings (.function "println!") [] [value] index, frames⟩
        { world with output := world.output ++ [value] }
        (.next ⟨.returned (Effects.boolean true), frames⟩)
  | evaluate_code {world bindings index frames code} :
      LocalTransition program world ⟨.arguments bindings (.function "eval") [] [code] index, frames⟩
        world (.next ⟨.evaluate [] code, frames⟩)
  | read_bad {world bindings index frames values} (invalid : values ≠ []) :
      LocalTransition program world ⟨.arguments bindings (.function "readln!") [] values index, frames⟩
        world (.next ⟨.fault (.invalidArguments "readln!"), frames⟩)
  | print_bad {world bindings index frames values} (invalid : ∀ value, values ≠ [value]) :
      LocalTransition program world ⟨.arguments bindings (.function "println!") [] values index, frames⟩
        world (.next ⟨.fault (.invalidArguments "println!"), frames⟩)
  | eval_bad {world bindings index frames values} (invalid : ∀ value, values ≠ [value]) :
      LocalTransition program world ⟨.arguments bindings (.function "eval") [] values index, frames⟩
        world (.next ⟨.fault (.invalidArguments "eval"), frames⟩)
  | primitive {world bindings head index frames values after returns}
      (ordinary : Eval.ioHead head = false) (known : StdLib.known head = true)
      (applied : StdLib.apply world.state head values = .ok (after, returns)) :
      LocalTransition program world ⟨.arguments bindings (.function head) [] values index, frames⟩
        { world with state := after } (.alternatives (returnedBranches returns frames))
  | primitive_fault {world bindings head index frames values reason}
      (ordinary : Eval.ioHead head = false) (known : StdLib.known head = true)
      (applied : StdLib.apply world.state head values = .error reason) :
      LocalTransition program world ⟨.arguments bindings (.function head) [] values index, frames⟩
        world (.next ⟨.fault reason, frames⟩)
  | equations {world bindings head index frames values}
      (ordinary : Eval.ioHead head = false) (unknown : StdLib.known head = false) :
      LocalTransition program world ⟨.arguments bindings (.function head) [] values index, frames⟩
        world (.alternatives (equationBranches program head values frames))
  | raw_argument {world bindings target first rest values index frames}
      (raw : rawArgument program target index = true) :
      LocalTransition program world ⟨.arguments bindings target (first :: rest) values index, frames⟩
        world (.next ⟨.returned (applySubst bindings first),
          .argument bindings target rest values index :: frames⟩)
  | evaluated_argument {world bindings target first rest values index frames}
      (eager : rawArgument program target index = false) :
      LocalTransition program world ⟨.arguments bindings target (first :: rest) values index, frames⟩
        world (.next ⟨.evaluate bindings first, .argument bindings target rest values index :: frames⟩)
  | variable {world bindings name frames} :
      LocalTransition program world ⟨.evaluate bindings (.var name), frames⟩
        world (.next ⟨.returned (applySubst bindings (.var name)), frames⟩)
  | symbol {world bindings name frames} :
      LocalTransition program world ⟨.evaluate bindings (.symbol name), frames⟩
        world (.next ⟨.returned (.symbol name), frames⟩)
  | grounded {world bindings value frames} :
      LocalTransition program world ⟨.evaluate bindings (.grounded value), frames⟩
        world (.next ⟨.returned (.grounded value), frames⟩)
  | let_enter {world bindings pattern value body frames} :
      LocalTransition program world
        ⟨.evaluate bindings (.expression [.symbol "let", pattern, value, body]), frames⟩
        world (.next ⟨.evaluate bindings value, .bind bindings pattern body :: frames⟩)
  | let_star {world bindings pairs body nested frames} (expanded : Eval.nestedLets pairs body = some nested) :
      LocalTransition program world
        ⟨.evaluate bindings (.expression [.symbol "let*", .expression pairs, body]), frames⟩
        world (.next ⟨.evaluate bindings nested, frames⟩)
  | let_star_bad {world bindings pairs body frames} (invalid : Eval.nestedLets pairs body = none) :
      LocalTransition program world
        ⟨.evaluate bindings (.expression [.symbol "let*", .expression pairs, body]), frames⟩
        world (.next ⟨.fault (.invalidArguments "let*"), frames⟩)
  | case_enter {world bindings value rows cases frames} (parsed : Eval.readCases rows = some cases) :
      LocalTransition program world
        ⟨.evaluate bindings (.expression [.symbol "case", value, .expression rows]), frames⟩
        world (.next ⟨.evaluate bindings value, .select bindings cases :: frames⟩)
  | case_bad {world bindings value rows frames} (invalid : Eval.readCases rows = none) :
      LocalTransition program world
        ⟨.evaluate bindings (.expression [.symbol "case", value, .expression rows]), frames⟩
        world (.next ⟨.fault (.invalidArguments "case"), frames⟩)
  | if_enter {world bindings condition yes no frames} :
      LocalTransition program world
        ⟨.evaluate bindings (.expression [.symbol "if", condition, yes, no]), frames⟩
        world (.next ⟨.evaluate bindings condition, .branch bindings yes no :: frames⟩)
  | if_without_else {world bindings condition yes frames} :
      LocalTransition program world
        ⟨.evaluate bindings (.expression [.symbol "if", condition, yes]), frames⟩
        world (.next ⟨.evaluate bindings condition,
          .branch bindings yes (.expression [.symbol "empty"]) :: frames⟩)
  | collapse_enter {world bindings expression frames} :
      LocalTransition program world ⟨.evaluate bindings (.expression [.symbol "collapse", expression]), frames⟩
        world (.collect bindings expression frames)
  | superpose_enter {world bindings alternatives frames} :
      LocalTransition program world
        ⟨.evaluate bindings (.expression [.symbol "superpose", .expression alternatives]), frames⟩
        world (.alternatives
          (alternatives.map fun expression => ⟨.evaluate bindings expression, frames⟩))
  | empty_enter {world bindings frames} :
      LocalTransition program world ⟨.evaluate bindings (.expression [.symbol "empty"]), frames⟩
        world (.alternatives [])
  | quote_enter {world bindings expression frames} :
      LocalTransition program world ⟨.evaluate bindings (.expression [.symbol "quote", expression]), frames⟩
        world (.next ⟨.returned (applySubst bindings expression), frames⟩)
  | call_enter {world bindings head arguments frames}
      (notControl : eagerControlForm (.expression (.symbol head :: arguments)) = false)
      (callable : (Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head)) = true) :
      LocalTransition program world ⟨.evaluate bindings (.expression (.symbol head :: arguments)), frames⟩
        world (.next ⟨.arguments bindings (.function head) arguments [] 0, frames⟩)
  | data_enter {world bindings head arguments frames}
      (notControl : eagerControlForm (.expression (.symbol head :: arguments)) = false)
      (uncallable : (Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head)) = false) :
      LocalTransition program world ⟨.evaluate bindings (.expression (.symbol head :: arguments)), frames⟩
        world (.next ⟨.arguments bindings .data (.symbol head :: arguments) [] 0, frames⟩)
  | expression_enter {world bindings items frames}
      (unheaded : ∀ head rest, items ≠ .symbol head :: rest) :
      LocalTransition program world ⟨.evaluate bindings (.expression items), frames⟩
        world (.next ⟨.arguments bindings .data items [] 0, frames⟩)
  | answer {world value} :
      LocalTransition program world ⟨.returned value, []⟩ world (.answer value)
  | argument_return {world value bindings target pending values index rest} :
      LocalTransition program world
        ⟨.returned value, .argument bindings target pending values index :: rest⟩
        world (.next ⟨.arguments bindings target pending (values ++ [value]) (index + 1), rest⟩)
  | bind_return {world value bindings pattern body bound rest}
      (matched : SpaceSemantics.matchBinding bindings pattern value = some bound) :
      LocalTransition program world ⟨.returned value, .bind bindings pattern body :: rest⟩
        world (.next ⟨.evaluate bound body, rest⟩)
  | bind_failure {world value bindings pattern body rest}
      (unmatched : SpaceSemantics.matchBinding bindings pattern value = none) :
      LocalTransition program world ⟨.returned value, .bind bindings pattern body :: rest⟩
        world (.alternatives [])
  | case_return {world value bindings cases bound body rest}
      (selected : SpaceSemantics.selectCase bindings value cases = some (bound, body)) :
      LocalTransition program world ⟨.returned value, .select bindings cases :: rest⟩
        world (.next ⟨.evaluate bound body, rest⟩)
  | case_failure {world value bindings cases rest}
      (unmatched : SpaceSemantics.selectCase bindings value cases = none) :
      LocalTransition program world ⟨.returned value, .select bindings cases :: rest⟩
        world (.alternatives [])
  | if_return {world value bindings yes no rest} :
      LocalTransition program world ⟨.returned value, .branch bindings yes no :: rest⟩
        world (.next ⟨.evaluate bindings (if value == Effects.boolean true then yes else no), rest⟩)

inductive Transition (program : Program) : Configuration → Configuration → Prop where
  | branch {world after scope parents branch pending movement}
      (frontier : scope.frontier = branch :: pending)
      (source : LocalTransition program world branch after movement) :
      Transition program ⟨world, scope :: parents⟩ (install after scope pending parents movement)
  | collapse_return {world rows frames parent parents} :
      Transition program ⟨world, ⟨[], rows, some frames⟩ :: parent :: parents⟩
        (finishScope world rows frames parent parents)

theorem local_transition_step {program : Program} {world after : World}
    {branch : Branch} {movement : Movement}
    (source : LocalTransition program world branch after movement) :
    localStep program world branch = some (after, movement) := by
  cases source
  all_goals try solve | simp_all [localStep, Eval.ioHead]
  case bind_return matched =>
    simp only [localStep, matched]
  case call_enter =>
    simp only [localStep]
    split <;> simp_all [eagerControlForm] <;> aesop
  case data_enter =>
    simp only [localStep]
    split <;> simp_all [eagerControlForm]

theorem transition_step {program : Program} {source target : Configuration}
    (transition : Transition program source target) : step program source = some target := by
  cases transition with
  | branch frontier derivation => simp [step, frontier, local_transition_step derivation]
  | collapse_return => rfl

theorem local_step_transition {program : Program} {world after : World}
    {branch : Branch} {movement : Movement}
    (computed : localStep program world branch = some (after, movement)) :
    LocalTransition program world branch after movement := by
  cases branch with
  | mk control frames =>
      cases control with
      | fault reason => simp [localStep] at computed
      | arguments bindings target pending values index =>
          cases pending with
          | nil =>
              cases target with
              | data =>
                  simp only [localStep, Option.some.injEq, Prod.mk.injEq] at computed
                  rcases computed with ⟨rfl, rfl⟩
                  exact .construct
              | function head =>
                  simp only [localStep] at computed
                  split at computed
                  · rename_i isIO
                    simp [Eval.ioHead] at isIO
                    rcases isIO with read | print | evaluate
                    · subst head
                      cases values with
                      | nil =>
                          cases input : world.input with
                          | nil =>
                              simp only [input, Option.some.injEq, Prod.mk.injEq] at computed
                              rcases computed with ⟨rfl, rfl⟩
                              exact .read_end input
                          | cons value rest =>
                              simp only [input, Option.some.injEq, Prod.mk.injEq] at computed
                              rcases computed with ⟨rfl, rfl⟩
                              exact .read_line input
                      | cons value rest =>
                          simp at computed
                          rcases computed with ⟨rfl, rfl⟩
                          exact .read_bad (by simp)
                    · subst head
                      cases values with
                      | nil =>
                          simp at computed
                          rcases computed with ⟨rfl, rfl⟩
                          exact .print_bad (by simp)
                      | cons value rest =>
                          cases rest with
                          | nil =>
                              simp only [Option.some.injEq, Prod.mk.injEq] at computed
                              rcases computed with ⟨rfl, rfl⟩
                              exact .print
                          | cons next remaining =>
                              simp at computed
                              rcases computed with ⟨rfl, rfl⟩
                              exact .print_bad (by simp)
                    · subst head
                      cases values with
                      | nil =>
                          simp at computed
                          rcases computed with ⟨rfl, rfl⟩
                          exact .eval_bad (by simp)
                      | cons value rest =>
                          cases rest with
                          | nil =>
                              simp only [Option.some.injEq, Prod.mk.injEq] at computed
                              rcases computed with ⟨rfl, rfl⟩
                              exact .evaluate_code
                          | cons next remaining =>
                              simp at computed
                              rcases computed with ⟨rfl, rfl⟩
                              exact .eval_bad (by simp)
                  · rename_i notIO
                    split at computed
                    · rename_i known
                      cases applied : StdLib.apply world.state head values with
                      | error reason =>
                          simp only [applied, Option.some.injEq, Prod.mk.injEq] at computed
                          rcases computed with ⟨rfl, rfl⟩
                          exact .primitive_fault (Bool.eq_false_iff.mpr notIO) known applied
                      | ok result =>
                          rcases result with ⟨state, returns⟩
                          simp only [applied, Option.some.injEq, Prod.mk.injEq] at computed
                          rcases computed with ⟨rfl, rfl⟩
                          exact .primitive (Bool.eq_false_iff.mpr notIO) known applied
                    · rename_i unknown
                      simp only [Option.some.injEq, Prod.mk.injEq] at computed
                      rcases computed with ⟨rfl, rfl⟩
                      exact .equations (Bool.eq_false_iff.mpr notIO) (Bool.eq_false_iff.mpr unknown)
          | cons first rest =>
              simp only [localStep] at computed
              split at computed
              · rename_i raw
                simp only [Option.some.injEq, Prod.mk.injEq] at computed
                rcases computed with ⟨rfl, rfl⟩
                exact .raw_argument raw
              · rename_i eager
                simp only [Option.some.injEq, Prod.mk.injEq] at computed
                rcases computed with ⟨rfl, rfl⟩
                exact .evaluated_argument (Bool.eq_false_iff.mpr eager)
      | evaluate bindings expression =>
          simp only [localStep] at computed
          split at computed
          · rcases Option.some.inj computed with ⟨rfl, rfl⟩
            exact .variable
          · rcases Option.some.inj computed with ⟨rfl, rfl⟩
            exact .symbol
          · rcases Option.some.inj computed with ⟨rfl, rfl⟩
            exact .grounded
          · rcases Option.some.inj computed with ⟨rfl, rfl⟩
            exact .let_enter
          · split at computed
            · rcases Option.some.inj computed with ⟨rfl, rfl⟩
              exact .let_star (by assumption)
            · rcases Option.some.inj computed with ⟨rfl, rfl⟩
              exact .let_star_bad (by assumption)
          · split at computed
            · rcases Option.some.inj computed with ⟨rfl, rfl⟩
              exact .case_enter (by assumption)
            · rcases Option.some.inj computed with ⟨rfl, rfl⟩
              exact .case_bad (by assumption)
          · rcases Option.some.inj computed with ⟨rfl, rfl⟩
            exact .if_enter
          · rcases Option.some.inj computed with ⟨rfl, rfl⟩
            exact .if_without_else
          · rcases Option.some.inj computed with ⟨rfl, rfl⟩
            exact .collapse_enter
          · rcases Option.some.inj computed with ⟨rfl, rfl⟩
            exact .superpose_enter
          · rcases Option.some.inj computed with ⟨rfl, rfl⟩
            exact .empty_enter
          · rcases Option.some.inj computed with ⟨rfl, rfl⟩
            exact .quote_enter
          · split at computed
            · rcases Option.some.inj computed with ⟨rfl, rfl⟩
              apply LocalTransition.call_enter _ (by assumption)
              simp only [eagerControlForm]
              split <;> simp_all
            · rename_i uncallable
              rcases Option.some.inj computed with ⟨rfl, rfl⟩
              apply LocalTransition.data_enter _ (Bool.eq_false_iff.mpr uncallable)
              simp only [eagerControlForm]
              split <;> simp_all
          · rcases Option.some.inj computed with ⟨rfl, rfl⟩
            apply LocalTransition.expression_enter
            aesop
      | returned value =>
          cases frames with
          | nil =>
              simp only [localStep, Option.some.injEq, Prod.mk.injEq] at computed
              rcases computed with ⟨rfl, rfl⟩
              exact .answer
          | cons frame rest =>
              cases frame with
              | argument bindings target pending values index =>
                  simp only [localStep, Option.some.injEq, Prod.mk.injEq] at computed
                  rcases computed with ⟨rfl, rfl⟩
                  exact .argument_return
              | bind bindings pattern body =>
                  simp only [localStep] at computed
                  split at computed
                  · simp only [Option.some.injEq, Prod.mk.injEq] at computed
                    rcases computed with ⟨rfl, rfl⟩
                    exact .bind_return (by assumption)
                  · simp only [Option.some.injEq, Prod.mk.injEq] at computed
                    rcases computed with ⟨rfl, rfl⟩
                    exact .bind_failure (by assumption)
              | select bindings cases =>
                  simp only [localStep] at computed
                  split at computed
                  · simp only [Option.some.injEq, Prod.mk.injEq] at computed
                    rcases computed with ⟨rfl, rfl⟩
                    exact .case_return (by assumption)
                  · simp only [Option.some.injEq, Prod.mk.injEq] at computed
                    rcases computed with ⟨rfl, rfl⟩
                    exact .case_failure (by assumption)
              | branch bindings yes no =>
                  simp only [localStep, Option.some.injEq, Prod.mk.injEq] at computed
                  rcases computed with ⟨rfl, rfl⟩
                  exact .if_return

theorem step_transition {program : Program} {source target : Configuration}
    (computed : step program source = some target) : Transition program source target := by
  cases source with
  | mk world scopes =>
      cases scopes with
      | nil => simp [step] at computed
      | cons scope parents =>
          cases frontier : scope.frontier with
          | nil =>
              cases caller : scope.caller with
              | none => simp [step, frontier, caller] at computed
              | some frames =>
                  cases parents with
                  | nil => simp [step, frontier, caller] at computed
                  | cons parent rest =>
                      simp only [step, frontier, caller, Option.some.injEq] at computed
                      subst target
                      cases scope with
                      | mk work collected continuation =>
                          simp only at frontier caller
                          subst work
                          subst continuation
                          exact .collapse_return
          | cons branch pending =>
              simp only [step, frontier] at computed
              cases reduced : localStep program world branch with
              | none => simp [reduced] at computed
              | some result =>
                  rcases result with ⟨after, movement⟩
                  simp only [reduced, Option.map_some, Option.some.injEq] at computed
                  subst target
                  exact .branch frontier (local_step_transition reduced)

theorem step_iff_transition (program : Program) (source target : Configuration) :
    step program source = some target ↔ Transition program source target :=
  ⟨step_transition, transition_step⟩

/-! ## Exact finite execution and resumption -/

theorem transition_deterministic {program : Program} {source first second : Configuration}
    (left : Transition program source first) (right : Transition program source second) :
    first = second :=
  Option.some.inj ((transition_step left).symm.trans (transition_step right))

def theory (program : Program) : Mettapedia.GSLT.GSLT where
  Term := Configuration
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Transition program
  rewrites_resp_left := by
    intro first other second same transition
    subst other
    exact ⟨second, transition, rfl⟩
  rewrites_resp_right := by
    intro first second other transition same
    subst other
    exact transition

@[simp] theorem theory_step_iff (program : Program) (source target : Configuration) :
    (theory program).Step source target ↔ step program source = some target :=
  (step_iff_transition program source target).symm

theorem advance_stopped (program : Program) (fuel : Nat) (configuration : Configuration)
    (stopped : step program configuration = none) :
    advance program fuel configuration = configuration := by
  cases fuel <;> simp [advance, stopped]

theorem run_stopped (program : Program) (fuel : Nat) (configuration : Configuration)
    (stopped : step program configuration = none) :
    run program fuel configuration = observe configuration := by
  cases fuel <;> simp [run, stopped]

theorem run_advance (program : Program) (fuel : Nat) (configuration : Configuration) :
    run program 0 (advance program fuel configuration) = run program fuel configuration := by
  induction fuel generalizing configuration with
  | zero => rfl
  | succ fuel ih =>
      cases next : step program configuration with
      | none => simp [run, advance, next]
      | some target => simpa only [advance, run, next] using ih target

theorem advance_split (program : Program) (first second : Nat) (configuration : Configuration) :
    advance program second (advance program first configuration) =
      advance program (first + second) configuration := by
  induction first generalizing configuration with
  | zero => simp [advance]
  | succ first ih =>
      cases next : step program configuration with
      | none =>
          rw [advance_stopped program (first + 1) configuration next,
            advance_stopped program second configuration next,
            advance_stopped program (first + 1 + second) configuration next]
      | some target => simpa [advance, next, Nat.succ_add] using ih target

theorem chunks_eq_advance_sum (program : Program) (fuels : List Nat) (configuration : Configuration) :
    chunks program fuels configuration = advance program fuels.sum configuration := by
  induction fuels generalizing configuration with
  | nil => rfl
  | cons fuel rest ih =>
      rw [chunks, ih, advance_split]
      rfl

theorem advance_path (program : Program) (fuel : Nat) (configuration : Configuration) :
    (theory program).MultiStep configuration (advance program fuel configuration) := by
  induction fuel generalizing configuration with
  | zero => exact .refl _
  | succ fuel ih =>
      cases next : step program configuration with
      | none =>
          simp only [advance, next]
          exact .refl _
      | some target =>
          exact .step (step_transition next) (by simpa [advance, next] using ih target)

/-- An exact source execution counts applications of the independently
authored rules. Completion and unused allowance do not manufacture steps. -/
inductive SourceRun (program : Program) : Nat → Configuration → Configuration → Prop where
  | refl (configuration) : SourceRun program 0 configuration configuration
  | next {source intermediate target count}
      (first : Transition program source intermediate)
      (rest : SourceRun program count intermediate target) :
      SourceRun program (count + 1) source target

theorem source_run_advances {program : Program} {count : Nat} {source target : Configuration}
    (sourceRun : SourceRun program count source target) : advance program count source = target := by
  induction sourceRun with
  | refl => rfl
  | next first _ ih => simpa [advance, transition_step first] using ih

theorem advance_has_source_run (program : Program) (fuel : Nat) (configuration : Configuration) :
    ∃ count ≤ fuel, SourceRun program count configuration (advance program fuel configuration) := by
  induction fuel generalizing configuration with
  | zero => exact ⟨0, Nat.le_refl 0, .refl _⟩
  | succ fuel ih =>
      cases next : step program configuration with
      | none =>
          exact ⟨0, Nat.zero_le _, by simpa [advance, next] using SourceRun.refl configuration⟩
      | some target =>
          obtain ⟨count, bound, path⟩ := ih target
          exact ⟨count + 1, Nat.succ_le_succ bound,
            by simpa [advance, next] using SourceRun.next (step_transition next) path⟩

theorem stopped_of_fault (program : Program) (configuration : Configuration) (reason : Fault)
    (isFault : fault configuration = some reason) : step program configuration = none := by
  cases configuration with
  | mk world scopes =>
      cases scopes with
      | nil => simp [fault] at isFault
      | cons scope parents =>
          cases scope with
          | mk frontier collected caller =>
              cases frontier with
              | nil => simp [fault] at isFault
              | cons branch pending =>
                  cases branch with
                  | mk control frames =>
                      cases control <;> simp_all [fault, step, localStep]

theorem stopped_of_completed (program : Program) (configuration : Configuration)
    (isComplete : completed configuration = true) : step program configuration = none := by
  cases configuration with
  | mk world scopes =>
      cases scopes with
      | nil => simp [completed] at isComplete
      | cons scope parents =>
          cases scope with
          | mk frontier collected caller =>
              cases frontier <;> cases caller <;> cases parents <;>
                simp_all [completed, step]

def resume (program : Program) (fuel : Nat) : Outcome → Outcome
  | .exhausted configuration => run program fuel configuration
  | outcome => outcome

theorem resume_observe (program : Program) (fuel : Nat) (configuration : Configuration) :
    resume program fuel (observe configuration) = run program fuel configuration := by
  cases isFault : fault configuration with
  | some reason =>
      rw [run_stopped program fuel configuration (stopped_of_fault program configuration reason isFault)]
      simp [observe, isFault, resume]
  | none =>
      cases isComplete : completed configuration with
      | false => simp [observe, isFault, isComplete, resume]
      | true =>
          rw [run_stopped program fuel configuration (stopped_of_completed program configuration isComplete)]
          simp [observe, isFault, isComplete, resume]

theorem resume_run (program : Program) (first second : Nat) (configuration : Configuration) :
    resume program second (run program first configuration) =
      run program (first + second) configuration := by
  rw [← run_advance program first configuration]
  change resume program second (observe (advance program first configuration)) = _
  rw [resume_observe, ← run_advance program second, advance_split, run_advance]

def checkpoints (program : Program) : List Nat → Configuration → List Configuration
  | [], _ => []
  | fuel :: rest, configuration =>
      let reached := advance program fuel configuration
      reached :: checkpoints program rest reached

def resumeChunks (program : Program) : List Nat → Outcome → Outcome
  | [], outcome => outcome
  | fuel :: rest, outcome => resumeChunks program rest (resume program fuel outcome)

theorem resumeChunks_run (program : Program) (fuels : List Nat) (paid : Nat)
    (configuration : Configuration) :
    resumeChunks program fuels (run program paid configuration) =
      run program (paid + fuels.sum) configuration := by
  induction fuels generalizing paid with
  | nil => simp [resumeChunks]
  | cons fuel rest ih =>
      rw [resumeChunks, resume_run, ih]
      simp [Nat.add_assoc]

theorem chunks_readout (program : Program) (fuels : List Nat) (configuration : Configuration) :
    run program 0 (chunks program fuels configuration) =
      resumeChunks program fuels (run program 0 configuration) := by
  rw [chunks_eq_advance_sum, run_advance, resumeChunks_run, Nat.zero_add]

/-! ## Retained scopes and performed effects -/

inductive ScopesValid {Work Answer Caller : Type} :
    List (Scope Work Answer Caller) → Prop where
  | root (work rows) : ScopesValid [⟨work, rows, none⟩]
  | nested {parents} (work rows frames) (valid : ScopesValid parents) :
      ScopesValid (⟨work, rows, some frames⟩ :: parents)

theorem start_scopes_valid (state : State) (expression : Atom) (input : List Atom) :
    ScopesValid (start state expression input).scopes := .root _ _

theorem ScopesValid.nonempty {Work Answer Caller : Type} {scopes : List (Scope Work Answer Caller)} (valid : ScopesValid scopes) : scopes ≠ [] := by
  cases valid <;> simp

theorem ScopesValid.replace_head {Work Answer Caller : Type}
    {scope : Scope Work Answer Caller} {parents : List (Scope Work Answer Caller)}
    (valid : ScopesValid (scope :: parents)) (work : List Work) (rows : List Answer) :
    ScopesValid ({ scope with frontier := work, collected := rows } :: parents) := by
  cases valid with
  | root => exact .root _ _
  | nested _ _ _ parentValid => exact .nested _ _ _ parentValid

theorem transition_scopes_valid {program : Program} {source target : Configuration}
    (transition : Transition program source target) (valid : ScopesValid source.scopes) :
    ScopesValid target.scopes := by
  cases transition with
  | branch frontier derivation =>
      cases derivation <;> simp only [install]
      all_goals try exact valid.replace_head _ _
      exact .nested _ _ _ (valid.replace_head _ _)
  | collapse_return =>
      cases valid with
      | nested _ _ _ parentValid => exact parentValid.replace_head _ _

theorem advance_scopes_valid (program : Program) (fuel : Nat) (configuration : Configuration)
    (valid : ScopesValid configuration.scopes) : ScopesValid (advance program fuel configuration).scopes := by
  induction fuel generalizing configuration with
  | zero => exact valid
  | succ fuel ih =>
      cases next : step program configuration with
      | none => simpa [advance, next] using valid
      | some target =>
          simpa [advance, next] using ih target (transition_scopes_valid (step_transition next) valid)

theorem local_output_extension {program : Program} {world after : World} {branch : Branch}
    {movement : Movement} (transition : LocalTransition program world branch after movement) :
    ∃ suffix, after.output = world.output ++ suffix := by
  cases transition
  all_goals try exact ⟨[], (List.append_nil _).symm⟩
  exact ⟨[_], rfl⟩

theorem transition_output_extension {program : Program} {source target : Configuration}
    (transition : Transition program source target) :
    ∃ suffix, target.world.output = source.world.output ++ suffix := by
  cases transition with
  | branch frontier derivation =>
      obtain ⟨suffix, appended⟩ := local_output_extension derivation
      cases derivation <;> exact ⟨suffix, appended⟩
  | collapse_return => exact ⟨[], (List.append_nil _).symm⟩

theorem advance_output_extension (program : Program) (fuel : Nat) (configuration : Configuration) :
    ∃ suffix, (advance program fuel configuration).world.output = configuration.world.output ++ suffix := by
  induction fuel generalizing configuration with
  | zero => exact ⟨[], (List.append_nil _).symm⟩
  | succ fuel ih =>
      cases next : step program configuration with
      | none => exact ⟨[], by simp [advance, next]⟩
      | some target =>
          obtain ⟨first, appended⟩ := transition_output_extension (step_transition next)
          obtain ⟨rest, later⟩ := ih target
          exact ⟨first ++ rest, by simpa [advance, next, appended, List.append_assoc] using later⟩

theorem local_input_suffix {program : Program} {world after : World} {branch : Branch}
    {movement : Movement} (transition : LocalTransition program world branch after movement) :
    ∃ consumed, world.input = consumed ++ after.input := by
  cases transition
  all_goals try exact ⟨[], rfl⟩
  rename_i value rest input
  exact ⟨[value], input⟩

theorem transition_input_suffix {program : Program} {source target : Configuration}
    (transition : Transition program source target) :
    ∃ consumed, source.world.input = consumed ++ target.world.input := by
  cases transition with
  | branch frontier derivation =>
      obtain ⟨consumed, retained⟩ := local_input_suffix derivation
      cases derivation <;> exact ⟨consumed, retained⟩
  | collapse_return => exact ⟨[], rfl⟩

theorem advance_input_suffix (program : Program) (fuel : Nat) (configuration : Configuration) :
    ∃ consumed, configuration.world.input = consumed ++ (advance program fuel configuration).world.input := by
  induction fuel generalizing configuration with
  | zero => exact ⟨[], rfl⟩
  | succ fuel ih =>
      cases next : step program configuration with
      | none => exact ⟨[], by simp [advance, next]⟩
      | some target =>
          obtain ⟨first, consumed⟩ := transition_input_suffix (step_transition next)
          obtain ⟨rest, retained⟩ := ih target
          exact ⟨first ++ rest, by simpa [advance, next, retained, List.append_assoc] using consumed⟩

/-! ## Equation occurrence retention and pending code support -/

/-- This embedding records a scalar control in the existing control datatype.
It makes no claim that list-valued and scalar continuation execution agree. -/
def controlImage : Control → Eval.Control
  | .evaluate bindings expression => .evaluate bindings expression
  | .arguments bindings target remaining values index =>
      .arguments bindings target remaining values index
  | .returned value => .returned [value]
  | .fault reason => .fault reason

theorem selected_clause_shape (program : Program) (head : String) (values : List Atom)
    {control : Eval.Control} (member : control ∈ Eval.clauses program head values) :
    ∃ bindings body, control = .evaluate bindings body := by
  unfold Eval.clauses at member
  obtain ⟨equation, _, selected⟩ := List.mem_filterMap.mp member
  split at selected
  · cases matched : SpaceSemantics.matchValue.matchValues [] equation.arguments values with
    | none => simp [matched] at selected
    | some bindings =>
        simp only [matched, Option.map_some, Option.some.injEq] at selected
        exact ⟨bindings, equation.body, selected.symm⟩
  · contradiction

theorem clause_occurrences_recovered (program : Program) (head : String) (values : List Atom)
    (frames : List Frame) :
    (equationBranches program head values frames).map (fun branch => controlImage branch.control) =
      Eval.clauses program head values := by
  have recover : ∀ controls : List Eval.Control,
      (∀ control ∈ controls, ∃ bindings body, control = .evaluate bindings body) →
      (controls.filterMap (clauseBranch frames)).map (fun branch => controlImage branch.control) = controls := by
    intro controls
    induction controls with
    | nil => intro _; rfl
    | cons control rest ih =>
        intro shapes
        obtain ⟨bindings, body, rfl⟩ := shapes control (by simp)
        have tail := ih (fun item member => shapes item (List.mem_cons_of_mem _ member))
        simpa only [List.filterMap_cons, clauseBranch, List.map_cons, controlImage] using
          congrArg (List.cons (.evaluate bindings body)) tail
  exact recover _ (fun control member => selected_clause_shape program head values member)

theorem equation_branches_length (program : Program) (head : String) (values : List Atom)
    (frames : List Frame) :
    (equationBranches program head values frames).length = (Eval.clauses program head values).length := by
  simpa using congrArg List.length (clause_occurrences_recovered program head values frames)

def controlWithin (allowed : String → Bool) (control : Control) : Bool :=
  Eval.controlWithin allowed (controlImage control)

def frameWithin (allowed : String → Bool) : Frame → Bool
  | .argument _ target pending _ _ => Eval.targetWithin allowed target && Eval.atomsWithin allowed pending
  | .bind _ _ body => Eval.codeWithin allowed body
  | .select _ cases => cases.all (fun row => Eval.codeWithin allowed row.2)
  | .branch _ yes no => Eval.codeWithin allowed yes && Eval.codeWithin allowed no

def branchWithin (allowed : String → Bool) (branch : Branch) : Bool :=
  controlWithin allowed branch.control && branch.frames.all (frameWithin allowed)

def scopeWithin (allowed : String → Bool) (scope : Scope) : Bool :=
  scope.frontier.all (branchWithin allowed) &&
    (scope.caller.map (fun frames => frames.all (frameWithin allowed))).getD true

def configurationWithin (allowed : String → Bool) (configuration : Configuration) : Prop :=
  configuration.scopes.all (scopeWithin allowed) = true

def movementWithin (allowed : String → Bool) : Movement → Bool
  | .next branch => branchWithin allowed branch
  | .alternatives branches => branches.all (branchWithin allowed)
  | .collect _ expression frames =>
      Eval.codeWithin allowed expression && frames.all (frameWithin allowed)
  | .answer _ => true

theorem equation_branches_within {allowed : String → Bool} {program : Program} {head : String}
    (closed : Eval.ProgramClosed allowed program) (supported : allowed head = true)
    (values : List Atom) (frames : List Frame) (frameCodes : frames.all (frameWithin allowed) = true) :
    (equationBranches program head values frames).all (branchWithin allowed) = true := by
  rw [List.all_eq_true]
  intro branch member
  obtain ⟨control, controlMember, mapped⟩ := List.mem_filterMap.mp member
  obtain ⟨bindings, body, shape⟩ := selected_clause_shape program head values controlMember
  subst control
  simp only [clauseBranch, Option.some.injEq] at mapped
  subst branch
  have codes : (Eval.clauses program head values).all (Eval.controlWithin allowed) = true := by
    simpa only [Eval.controlsWithin_eq_all] using Eval.clauses_within allowed closed supported values
  have code := List.all_eq_true.mp codes (Eval.Control.evaluate bindings body) controlMember
  simp only [branchWithin, Bool.and_eq_true]
  exact ⟨code, frameCodes⟩

theorem local_transition_within {allowed : String → Bool} {program : Program}
    {world after : World} {branch : Branch} {movement : Movement}
    (closed : Eval.ProgramClosed allowed program)
    (emptyAllowed : allowed "empty" = true)
    (transition : LocalTransition program world branch after movement)
    (within : branchWithin allowed branch = true) : movementWithin allowed movement = true := by
  cases transition
  all_goals try solve |
    simp_all [movementWithin, branchWithin, controlWithin, controlImage, frameWithin,
      Eval.controlWithin, Eval.targetWithin, Eval.codeWithin,
      Eval.atomsWithin, Eval.expressionHeadWithin, Bool.and_eq_true, returnedBranches,
      List.all_map]
  case equations bindings head index frames values _ _ =>
    simp only [branchWithin, controlWithin, controlImage, Eval.controlWithin,
      Eval.targetWithin, Eval.atomsWithin, Bool.and_true, Bool.and_eq_true] at within
    exact equation_branches_within closed within.1.1 values frames within.2
  case let_star bindings pairs body nested frames expanded =>
    simp only [movementWithin, branchWithin, controlWithin, controlImage, Eval.controlWithin,
      Bool.and_eq_true]
    refine ⟨Eval.nestedLets_within allowed closed.binding expanded ?_ ?_, ?_⟩
    all_goals simp_all [branchWithin, controlWithin, controlImage, Eval.controlWithin,
      Eval.codeWithin, Eval.atomsWithin, Eval.expressionHeadWithin, Bool.and_eq_true]
  case case_enter bindings value rows cases frames parsed =>
    simp only [movementWithin, branchWithin, controlWithin, controlImage, Eval.controlWithin,
      List.all_cons, frameWithin, Bool.and_eq_true]
    refine ⟨?_, Eval.readCases_within allowed parsed ?_, ?_⟩
    all_goals simp_all [branchWithin, controlWithin, controlImage, Eval.controlWithin,
      Eval.codeWithin, Eval.atomsWithin, Eval.expressionHeadWithin, Bool.and_eq_true]
  case case_return value bindings cases rest bound body selected =>
    simp only [branchWithin, controlWithin, controlImage, Eval.controlWithin, Bool.true_and,
      List.all_cons, frameWithin, Bool.and_eq_true] at within
    simp only [movementWithin, branchWithin, controlWithin, controlImage, Eval.controlWithin,
      Bool.and_eq_true]
    exact ⟨Eval.selected_body_within allowed (SpaceSemantics.selectCase_sound selected) within.1, within.2⟩
  case if_return value bindings yes no rest =>
    simp only [branchWithin, controlWithin, controlImage, Eval.controlWithin, Bool.true_and,
      List.all_cons, frameWithin, Bool.and_eq_true] at within
    simp only [movementWithin, branchWithin, controlWithin, controlImage, Eval.controlWithin,
      Bool.and_eq_true]
    refine ⟨?_, within.2⟩
    split
    · exact within.1.1
    · exact within.1.2

theorem install_within {allowed : String → Bool} {world : World} {scope : Scope}
    {pending : List Branch} {parents : List Scope} {movement : Movement}
    (old : scopeWithin allowed { scope with frontier := pending } = true)
    (outer : parents.all (scopeWithin allowed) = true)
    (changed : movementWithin allowed movement = true) :
    configurationWithin allowed (install world scope pending parents movement) := by
  have oldCodes := old
  simp only [scopeWithin, Bool.and_eq_true] at oldCodes
  have withFrontier (work : List Branch) (rows : List Atom)
      (workCodes : work.all (branchWithin allowed) = true) :
      scopeWithin allowed { scope with frontier := work, collected := rows } = true := by
    simp only [scopeWithin, Bool.and_eq_true]
    exact ⟨workCodes, oldCodes.2⟩
  cases movement with
  | next branch =>
      simp only [configurationWithin, install, List.all_cons, Bool.and_eq_true]
      refine ⟨withFrontier _ _ ?_, outer⟩
      simp only [List.all_cons, Bool.and_eq_true]
      exact ⟨changed, oldCodes.1⟩
  | alternatives branches =>
      simp only [configurationWithin, install, List.all_cons, Bool.and_eq_true]
      refine ⟨withFrontier _ _ ?_, outer⟩
      simp only [List.all_append, Bool.and_eq_true]
      exact ⟨changed, oldCodes.1⟩
  | collect bindings expression frames =>
      simp only [configurationWithin, install, List.all_cons, Bool.and_eq_true]
      refine ⟨?_, old, outer⟩
      simp only [movementWithin, Bool.and_eq_true] at changed
      simp [scopeWithin, branchWithin, controlWithin, controlImage, Eval.controlWithin,
        changed.1, changed.2]
  | answer value =>
      simp only [configurationWithin, install, List.all_cons, Bool.and_eq_true]
      exact ⟨withFrontier _ _ oldCodes.1, outer⟩

theorem transition_within {allowed : String → Bool} {program : Program}
    {source target : Configuration} (closed : Eval.ProgramClosed allowed program)
    (emptyAllowed : allowed "empty" = true)
    (transition : Transition program source target)
    (within : configurationWithin allowed source) : configurationWithin allowed target := by
  cases transition with
  | branch frontier derivation =>
      simp only [configurationWithin, List.all_cons, Bool.and_eq_true] at within
      have head := within.1
      simp only [scopeWithin, frontier, List.all_cons, Bool.and_eq_true] at head
      apply install_within _ within.2 (local_transition_within closed emptyAllowed derivation head.1.1)
      simp only [scopeWithin, Bool.and_eq_true]
      exact ⟨head.1.2, head.2⟩
  | collapse_return =>
      simp only [configurationWithin, List.all_cons, Bool.and_eq_true] at within
      have frameCodes := within.1
      simp only [scopeWithin, List.all_nil, Bool.true_and, Option.map_some, Option.getD_some] at frameCodes
      have parentCodes := within.2.1
      simp only [scopeWithin, Bool.and_eq_true] at parentCodes
      simp only [configurationWithin, finishScope, List.all_cons, Bool.and_eq_true]
      refine ⟨?_, within.2.2⟩
      simp only [scopeWithin, List.all_cons, branchWithin, controlWithin, controlImage,
        Eval.controlWithin, Bool.true_and, Bool.and_eq_true]
      exact ⟨⟨frameCodes, parentCodes.1⟩, parentCodes.2⟩

theorem advance_within (program : Program) (fuel : Nat) (configuration : Configuration)
    {allowed : String → Bool} (closed : Eval.ProgramClosed allowed program)
    (emptyAllowed : allowed "empty" = true)
    (within : configurationWithin allowed configuration) :
    configurationWithin allowed (advance program fuel configuration) := by
  induction fuel generalizing configuration with
  | zero => exact within
  | succ fuel ih =>
      cases next : step program configuration with
      | none => simpa [advance, next] using within
      | some target =>
          simpa [advance, next] using ih target (transition_within closed emptyAllowed (step_transition next) within)

theorem transition_preserves_state {program : Program} {source target : Configuration}
    (within : configurationWithin ProgramReplay.readOnlyHead source)
    (transition : Transition program source target) : target.world.state = source.world.state := by
  cases transition with
  | branch frontier derivation =>
      cases derivation
      all_goals try rfl
      rename_i bindings head index frames values after returns _ _ applied
      simp only [configurationWithin, List.all_cons, Bool.and_eq_true] at within
      have headCodes := within.1
      simp only [scopeWithin, frontier, List.all_cons, branchWithin, controlWithin,
        controlImage, Eval.controlWithin, Eval.targetWithin, Eval.atomsWithin,
        Bool.and_true, Bool.and_eq_true] at headCodes
      exact ProgramReplay.primitive_preserves_state headCodes.1.1.1.1 applied
  | collapse_return => rfl

theorem advance_preserves_state (program : Program) (fuel : Nat) (configuration : Configuration)
    (closed : Eval.ProgramClosed ProgramReplay.readOnlyHead program)
    (within : configurationWithin ProgramReplay.readOnlyHead configuration) :
    (advance program fuel configuration).world.state = configuration.world.state := by
  induction fuel generalizing configuration with
  | zero => rfl
  | succ fuel ih =>
      cases next : step program configuration with
      | none => simp [advance, next]
      | some target =>
          have transition := step_transition next
          simpa only [advance, next] using
            (ih target (transition_within closed (by decide +kernel) transition within)).trans
              (transition_preserves_state within transition)

theorem chunks_loaded_store_reconstruction (program : Program) (fuels : List Nat)
    (expression : Atom) (input : List Atom)
    (checked : ProgramReplay.readOnlyProgram program = true)
    (code : Eval.codeWithin ProgramReplay.readOnlyHead expression = true) :
    let reached := chunks program fuels (start (Effects.loaded program) expression input)
    NamedSpaces.Store.reconstruct reached.world.state.core [] reached.world.state.spacesPrefix
      (reached.world.state.cellRows []) = reached.world.state := by
  dsimp only
  have initial : configurationWithin ProgramReplay.readOnlyHead
      (start (Effects.loaded program) expression input) := by
    simp [configurationWithin, start, scopeWithin, branchWithin, controlWithin, controlImage, Eval.controlWithin, code]
  have same := advance_preserves_state program fuels.sum
    (start (Effects.loaded program) expression input)
    (ProgramReplay.checked_program_closed program checked) initial
  rw [chunks_eq_advance_sum, same]
  exact ProgramReplay.loaded_store_reconstruction program

/-! ## Positive and distinguishing controls -/

namespace Examples

def call (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)

def a : Atom := .symbol "a"
def b : Atom := .symbol "b"
def seven : Atom := .grounded (.int 7)
def pair (first second : Atom) : Atom := call "Pair" [first, second]
def choice : Atom := call "superpose" [.expression [a, b]]

def program : Program :=
  { equations := [
      { head := "dup", arguments := [.var "x"], body := .var "x" },
      { head := "dup", arguments := [.var "x"], body := .var "x" },
      { head := "mark", arguments := [.var "x"], body :=
          call "let" [.var "ignored", call "println!" [.var "x"], .var "x"] }]
    declarations := [], layout := [.equation, .equation, .equation] }

def initial (expression : Atom) : Configuration := start (Effects.loaded program) expression
def mark (expression : Atom) : Atom := call "mark" [expression]
def nested : Atom := mark (mark choice)
def letContinuation : Atom := call "let" [.var "held", mark choice, mark (.var "held")]
def twoArguments : Atom := pair (mark choice) (mark choice)
def collected : Atom := mark (call "collapse" [mark choice])
def collectedLet : Atom := call "let"
  [.var "held", call "collapse" [mark choice], mark (.var "held")]
def correlated : Atom := call "let" [.var "held", choice, pair (.var "held") (.var "held")]
def independent : Atom := pair choice choice

theorem authored_program_admitted : ProgramReplay.readOnlyProgram program = true := by decide

theorem duplicate_equation_occurrences_retained :
    answers (advance program 9 (initial (call "dup" [seven]))) = [seven, seven] := by
  with_unfolding_all rfl

theorem duplicates_do_not_become_a_set :
    (answers (advance program 9 (initial (call "dup" [seven])))).length ≠ 1 := by
  rw [duplicate_equation_occurrences_retained]
  decide

/-- A prepared frontier lets the controls isolate the continuation rule from
the earlier argument evaluation. Complete authored runs remain executable via
`nested`, `letContinuation`, `twoArguments`, `collected` and `collectedLet`. -/
def printFrame : Frame := .argument [] (.function "println!") [] [] 0

def readyPrint (value : Atom) (frames : List Frame) : Branch :=
  ⟨.arguments [] (.function "println!") [] [value] 1, frames⟩

def scalarPrefix : Configuration :=
  ⟨⟨Effects.loaded program, [], []⟩,
    [{ frontier := [readyPrint a [printFrame], readyPrint b [printFrame]] }]⟩

def letPrefix : Configuration :=
  ⟨⟨Effects.loaded program, [], []⟩,
    [{ frontier := [readyPrint a [.bind [] (.var "held") (.var "held"), printFrame],
                    readyPrint b [.bind [] (.var "held") (.var "held"), printFrame]] }]⟩

theorem scalar_delivery_resumes_caller_first :
    (advance program 7 scalarPrefix).world.output =
      [a, Effects.boolean true, b, Effects.boolean true] := by rfl

theorem scalar_delivery_is_not_batched :
    (advance program 3 scalarPrefix).world.output ≠ [a, b] := by
  decide +kernel

theorem let_continuation_resumes_caller_first :
    (advance program 5 letPrefix).world.output = [a, Effects.boolean true] := by
  with_unfolding_all rfl

theorem argument_delivery_preserves_pending_work (first : Atom) (pending values : List Atom)
    (index : Nat) (frames : List Frame) :
    localStep program ⟨Effects.loaded program, [], []⟩
      ⟨.returned first, .argument [] .data pending values index :: frames⟩ =
      some (⟨Effects.loaded program, [], []⟩,
        .next ⟨.arguments [] .data pending (values ++ [first]) (index + 1), frames⟩) := by rfl

theorem independent_arguments_keep_cartesian_occurrences :
    answers (advance program 30 (initial independent)) =
      [pair a a, pair a b, pair b a, pair b b] := by
  with_unfolding_all rfl

theorem binding_keeps_choice_correlation :
    answers (advance program 30 (initial correlated)) = [pair a a, pair b b] := by
  with_unfolding_all rfl

theorem independent_choice_is_not_shared_choice :
    answers (advance program 30 (initial independent)) ≠
      answers (advance program 30 (initial correlated)) := by
  rw [independent_arguments_keep_cartesian_occurrences, binding_keeps_choice_correlation]
  decide

def collapsePrefix : Configuration :=
  ⟨⟨Effects.loaded program, [], []⟩,
    [{ frontier := [readyPrint a [], readyPrint b []], caller := some [printFrame] },
     { frontier := [] }]⟩

def collapseLetPrefix : Configuration :=
  ⟨⟨Effects.loaded program, [], []⟩,
    [{ frontier := [readyPrint a [], readyPrint b []],
       caller := some [.bind [] (.var "held") (.var "held"), printFrame] },
     { frontier := [] }]⟩

theorem collapse_collects_before_releasing_caller :
    (advance program 8 collapsePrefix).world.output =
      [a, b, .expression [Effects.boolean true, Effects.boolean true]] ∧
      answers (advance program 8 collapsePrefix) = [Effects.boolean true] := by
  exact ⟨rfl, rfl⟩

theorem collapse_let_keeps_the_same_delimiter :
    (advance program 9 collapseLetPrefix).world.output =
      [a, b, .expression [Effects.boolean true, Effects.boolean true]] := by
  with_unfolding_all rfl

theorem collapse_does_not_interleave_its_caller :
    (advance program 4 collapsePrefix).world.output ≠ [a, .expression [Effects.boolean true], b] := by
  decide +kernel

theorem collapse_residual_retains_inner_and_outer_scopes :
    (advance program 3 (initial collected)).scopes.length = 2 := by with_unfolding_all rfl

theorem completed_empty_choice_is_not_a_pause :
    completed (advance program 1 (initial (call "empty" []))) = true ∧
      answers (advance program 1 (initial (call "empty" []))) = [] := by
  exact ⟨rfl, rfl⟩

theorem collapse_empty_delivers_one_empty_expression :
    answers (advance program 4 (initial (call "collapse" [call "empty" []]))) =
      [.expression []] := by rfl

def eagerMismatch : Atom := call "let"
  [.symbol "mismatch", call "println!" [call "Seen" [.grounded (.int 9)]], .symbol "value"]

/-- The selected profile performs the value before matching it. Static output
unification before execution would erase this effect. -/
theorem eager_mismatch_retains_performed_effect :
    (advance program 14 (initial eagerMismatch)).world.output =
      [call "Seen" [.grounded (.int 9)]] ∧
      answers (advance program 14 (initial eagerMismatch)) = [] := by
  with_unfolding_all exact ⟨rfl, rfl⟩

def effectThenFault : Atom := call "let"
  [.var "ignored", call "println!" [.symbol "once"], call "%" [seven, .grounded (.int 0)]]

theorem effect_immediately_before_pause_is_retained :
    (advance program 6 (initial effectThenFault)).world.output = [.symbol "once"] ∧
      completed (advance program 6 (initial effectThenFault)) = false ∧
      fault (advance program 6 (initial effectThenFault)) = none := by
  with_unfolding_all exact ⟨rfl, rfl, rfl⟩

theorem fault_retains_performed_effect_and_residual :
    (advance program 15 (initial effectThenFault)).world.output = [.symbol "once"] ∧
      fault (advance program 15 (initial effectThenFault)) = some .zeroDivisor ∧
      completed (advance program 15 (initial effectThenFault)) = false := by
  with_unfolding_all exact ⟨rfl, rfl, rfl⟩

theorem nested_split_preserves_complete_residual :
    chunks program [14, 0, 10, 25] (initial nested) = advance program 49 (initial nested) := by
  rw [chunks_eq_advance_sum]
  rfl

theorem collapse_split_preserves_complete_residual :
    chunks program [2, 13, 12, 15] (initial collected) = advance program 42 (initial collected) := by
  rw [chunks_eq_advance_sum]
  rfl

def lostAlternative : Configuration :=
  { (initial choice) with scopes := [{ frontier := [⟨.evaluate [] a, []⟩] }] }

theorem omitting_saved_alternative_changes_answers :
    answers (advance program 5 (initial choice)) ≠ answers (advance program 5 lostAlternative) := by
  decide +kernel

def batchPrefix : Eval.Configuration :=
  { state := Effects.loaded program
    control := .sequence
      [.arguments [] (.function "println!") [] [a] 1,
       .arguments [] (.function "println!") [] [b] 1] []
    frames := [.bind [] (.var "held") (call "println!" [.var "held"])] }

/-- Existing batch semantics remains a separate, valid reference endpoint.
Its inner sequence completes before the caller receives its answers. -/
theorem batch_prefix_differs_from_scalar_delivery :
    (ProgramReplay.advance program 5 batchPrefix).output = [a, b] ∧
      (advance program 3 scalarPrefix).world.output = [a, Effects.boolean true] := by
  with_unfolding_all exact ⟨rfl, rfl⟩

end Examples

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS

/-! ## Reached destinations and finite structural branch execution -/

set_option maxRecDepth 12000
set_option maxHeartbeats 2000000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Logic.LP

/-- First-order source syntax keeps symbols and grounded values distinct.
This is a syntax interpretation into the shared unification theory, not a
claim about a native matching implementation. -/
abbrev signature : LPSignature where
  constants := String ⊕ GroundedValue
  vars := String
  relationSymbols := Unit
  relationArity _ := 0
  functionSymbols := Nat
  functionArity := id

abbrev Value := Term signature
abbrev Environment := Subst signature
abbrev Equations := List (Atom × Atom)

/-- Sufficient finite structural syntax for the native bridge. Opaque grounded
objects (including list/rational carriers) and alternate truth spellings need
their own runtime readback. Rejecting this admission does not reject a source
program: its native operation remains outside this component. The syntax
interpretation below is mathematical and remains defined for every `Atom`. -/
def finiteStructural : Atom → Bool
  | .symbol name => !(name ∈ ["True", "False", "true", "false"])
  | .var _ => true
  | .grounded (.custom _ _) => false
  | .grounded _ => true
  | .expression children => children.attach.all (fun child => finiteStructural child.1)
termination_by atom => sizeOf atom
decreasing_by
  simp_wf
  exact Nat.lt_trans (List.sizeOf_lt_of_mem child.property) (by omega)


def encode : Atom → Value
  | .var name => .var name
  | .symbol name => .const (.inl name)
  | .grounded value => .const (.inr value)
  | .expression values => .app values.length (fun index => encode values[index])
termination_by atom => sizeOf atom
decreasing_by
  simp_wf
  exact Nat.lt_trans (List.sizeOf_lt_of_mem (List.getElem_mem index.isLt))
    (by omega)

def decode : Value → Atom
  | .var name => .var name
  | .const (.inl name) => .symbol name
  | .const (.inr value) => .grounded value
  | .app _ children => .expression (List.ofFn (fun index => decode (children index)))

@[simp] theorem decode_encode (atom : Atom) : decode (encode atom) = atom := by
  cases atom with
  | symbol => simp [encode, decode]
  | var => simp [encode, decode]
  | grounded => simp [encode, decode]
  | expression values =>
      simp only [encode, decode, OSLFCore.Atom.expression.injEq]
      apply List.ext_getElem
      · simp
      · intro index before after
        simp only [List.getElem_ofFn]
        exact decode_encode values[index]
termination_by sizeOf atom
decreasing_by
  simp_wf
  exact Nat.lt_trans (List.sizeOf_lt_of_mem (List.getElem_mem after)) (by omega)

private theorem app_ext {first second : Nat} (same : first = second)
    (left : Fin first → Value) (right : Fin second → Value)
    (children : ∀ index, left index = right (index.cast same)) :
    Term.app (σ := signature) first left = Term.app second right := by
  subst second
  exact congrArg (Term.app (σ := signature) first) (funext children)

@[simp] theorem encode_decode (value : Value) : encode (decode value) = value := by
  induction value with
  | var => simp [encode, decode]
  | const scalar => cases scalar <;> simp [encode, decode]
  | app arity children ih =>
      simp only [decode, encode]
      apply app_ext List.length_ofFn
      intro index
      simp only [Fin.getElem_fin, List.getElem_ofFn]
      exact ih _

def equations (source : Equations) : List (Value × Value) :=
  source.map fun pair => (encode pair.1, encode pair.2)

/-- A branch carries its accumulated constraints. The solved presentation is
computed by the existing total unifier; a failed presentation is not an empty
successful environment. Native checkpoints keep their original records. -/
def resolve (source : Equations) : Option Environment := unifyTotal (equations source)

def read (environment : Environment) (atom : Atom) : Atom :=
  decode (environment.applyTerm (encode atom))

/-- Both sides are constrained together with the reached branch environment.
No source occurrence or destination is replaced by a fresh unrelated slot. -/
def refine (source : Equations) (value destination : Atom) : Option Equations :=
  if (resolve (source ++ [(value, destination)])).isSome then
    some (source ++ [(value, destination)]) else none

def Solves (environment : Environment) (source : Equations) : Prop :=
  ∀ pair ∈ source, read environment pair.1 = read environment pair.2

theorem solves_iff_unifies (environment : Environment) (source : Equations) :
    Solves environment source ↔ Unifies environment (equations source) := by
  constructor
  · intro solved pair member
    obtain ⟨original, occurs, rfl⟩ := List.mem_map.mp member
    have same := congrArg encode (solved original occurs)
    simpa [read] using same
  · intro solved pair member
    exact congrArg decode (solved _ (List.mem_map.mpr ⟨pair, member, rfl⟩))

theorem resolve_sound {source : Equations} {environment : Environment}
    (resolved : resolve source = some environment) : Solves environment source :=
  (solves_iff_unifies environment source).mpr
    (unifyTotal_sound _ _ resolved)

theorem resolve_complete {source : Equations}
    (solved : ∃ environment, Solves environment source) :
    ∃ environment, resolve source = some environment := by
  obtain ⟨environment, correct⟩ := solved
  exact unifyTotal_complete ⟨environment, (solves_iff_unifies _ _).mp correct⟩

/-- Refinement succeeds exactly when the old environment and the new
value/destination equation have a common solution. This is an independent
logical criterion, rather than the definition of a native service. -/
theorem refine_iff (source next : Equations) (value destination : Atom) :
    refine source value destination = some next ↔
      next = source ++ [(value, destination)] ∧
      ∃ environment, Solves environment source ∧
        read environment value = read environment destination := by
  unfold refine
  split
  · rename_i accepted
    obtain ⟨environment, resolved⟩ := Option.isSome_iff_exists.mp accepted
    have sound := resolve_sound resolved
    constructor
    · intro same
      cases same
      exact ⟨rfl, environment,
        fun pair member => sound pair (List.mem_append_left _ member),
        sound (value, destination) (List.mem_append_right _ (by simp))⟩
    · rintro ⟨rfl, _⟩; rfl
  · rename_i rejected
    constructor
    · intro impossible; cases impossible
    · rintro ⟨rfl, environment, old, new⟩
      have solved : Solves environment (source ++ [(value, destination)]) := by
        intro pair member
        rcases List.mem_append.mp member with member | member
        · exact old pair member
        · simp only [List.mem_singleton] at member
          subst pair; exact new
      obtain ⟨result, found⟩ := resolve_complete ⟨environment, solved⟩
      simp [found] at rejected

/-- One solved presentation determines the complete joint tuple of caller
observations. Repeated variables use one substitution, so sharing is retained. -/
def observations (source : Equations) (atoms : List Atom) : Option (List Atom) :=
  (resolve source).map fun environment => atoms.map (read environment)

/-- All joint readouts licensed by the source equations, independently of
the solver's chosen residual presentation. One model reads every position. -/
def solutionTuples (source : Equations) (atoms : List Atom) : Set (List Atom) :=
  {values | ∃ environment, Solves environment source ∧
    atoms.map (read environment) = values}

/-- Packet transformations justified in every model preserve the complete
joint observer, including repeated positions and shared open variables. -/
theorem solutionTuples_congr_models (source : Equations) (before after : List Atom)
    (preserved : ∀ environment, Solves environment source →
      after.map (read environment) = before.map (read environment)) :
    solutionTuples source after = solutionTuples source before := by
  ext values
  constructor
  · rintro ⟨environment,solved,returned⟩
    exact ⟨environment,solved,(preserved environment solved).symm.trans returned⟩
  · rintro ⟨environment,solved,returned⟩
    exact ⟨environment,solved,(preserved environment solved).trans returned⟩

theorem one_joint_environment {source : Equations} {environment : Environment}
    (resolved : resolve source = some environment) (atoms : List Atom) :
    observations source atoms = some (atoms.map (read environment)) := by
  simp [observations, resolved]

namespace Controls

theorem finite_structure_keeps_aliases :
    finiteStructural (.expression [.symbol "f", .var "x", .var "x"]) = true := by simp [finiteStructural]

theorem opaque_carrier_requires_separate_admission :
    finiteStructural (.grounded (.custom "ListCell" "opaque")) = false := by simp [finiteStructural]

theorem truth_spelling_requires_canonical_readback :
    finiteStructural (.symbol "True") = false ∧
      finiteStructural (.grounded (.bool true)) = true := by simp [finiteStructural]

theorem alias_keeps_repeated_destination :
    observations [(.var "x", .var "y"), (.var "y", .symbol "A")]
      [.var "x", .var "y", .expression [.var "x", .var "y"]] =
      some [.symbol "A", .symbol "A", .expression [.symbol "A", .symbol "A"]] := by
  simp [observations, resolve, equations, read, encode, decode, unifyTotal,
    Subst.applyEqs, Subst.single, Subst.comp, Subst.applyTerm, Subst.id, Term.occursIn]

theorem incompatible_destination_refuses :
    refine [(.var "out", .symbol "A")] (.symbol "B") (.var "out") = none := by
  simp [resolve, equations, refine, encode, unifyTotal,
    Subst.applyEqs, Subst.single, Subst.applyTerm, Term.occursIn]

theorem expression_cycle_refuses :
    refine [] (.var "x") (.expression [.symbol "f", .var "x"]) = none := by
  simp [resolve, equations, refine, encode, unifyTotal, Term.occursIn]

end Controls
end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Logic.LP
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Relational destination constraints and eager value binding are distinct
source profiles. Neither changes the source order of performed effects. -/
inductive Policy where
  | relational
  | eagerValue
  deriving DecidableEq, Repr

/-- A continuation keeps the destination of every producer. Completed values
refine the reached environment; they do not restore an earlier capture. -/
inductive Goal where
  | evaluate (expression destination : Atom)
  | equate (value destination : Atom)
  /-- The condition has returned; neither authored branch has run yet. -/
  | branch (condition yes no destination : Atom)
  | invoke (head : String) (arguments : List Atom) (destination : Atom)
  /-- Surface match executes each template under that row's reached record. -/
  | query (location pattern template destination : Atom)
  | argumentReturn (value destination : Atom) (callerDepth : Nat)
  | openCommit
  | commit
  | restoreCommit (olderBoundary : Nat)
  deriving DecidableEq, Repr

def Goal.atoms : Goal → List Atom
  | .evaluate expression destination | .equate expression destination => [expression, destination]
  | .branch condition yes no destination => [condition, yes, no, destination]
  | .invoke _ arguments destination => destination :: arguments
  | .query location pattern template destination => [location, pattern, template, destination]
  | .argumentReturn value destination _ => [value, destination]
  | .openCommit | .commit | .restoreCommit _ => []

/-- A saved continuation delimiter selects an older suffix. The list-split
source rules below give its meaning independently of this finite index. -/
def callerSuffix? (callerDepth : Nat) (remaining : List Goal) : Option (List Goal) :=
  if callerDepth ≤ remaining.length then
    some (remaining.drop (remaining.length - callerDepth)) else none

structure Control where
  bindings : Equations
  goals : List Goal
  destination : Atom
  /-- Names retained by sibling scopes, source declarations and caller frames. -/
  reserved : Finset String := ∅
  /-- Number of older alternatives outside the current predicate/meta-call.
  This is a logical choice-stack delimiter, independent of native storage. -/
  cutBoundary : Nat := 0
  deriving DecidableEq

/-- Admission concerns the complete reached branch, including pending caller
observations. It is not a native matcher equivalence claim. Native cell/rational
routing, scalar representation, operation plans and binding readback remain
separate component boundaries. -/
def Control.finiteStructural (control : Control) : Bool :=
  (control.destination ::
    control.bindings.flatMap (fun pair => [pair.1, pair.2]) ++
    control.goals.flatMap Goal.atoms).all EagerDFS.Destination.finiteStructural

abbrev FiniteStructuralAdmission (control : Control) : Prop :=
  control.finiteStructural = true

structure Cursor (Context : Type) where
  world : World
  control : Control
  context : Context

/-- All caller observations participate in allocation. This is finite source
allocation; matching a concrete native variable allocator is a separate map. -/
def Control.support (control : Control) : Finset String :=
  control.reserved ∪
    ((control.destination ::
      control.bindings.flatMap (fun pair => [pair.1, pair.2]) ++
      control.goals.flatMap Goal.atoms).foldl
        (fun names atom => names ∪ (encode atom).freeVars) ∅)

def freshName (control : Control) (index : Nat) : String :=
  String.replicate (control.support.sup String.length + index + 1) '#'

def freshSlots (control : Control) (count : Nat) : List Atom :=
  (List.range count).map (fun index => .var (freshName control index))

theorem freshName_not_mem (control : Control) (index : Nat) :
    freshName control index ∉ control.support := by
  intro member
  have bound := Finset.le_sup (f := String.length) member
  simp only [freshName, String.length_replicate] at bound
  omega

theorem freshName_injective (control : Control) : Function.Injective (freshName control) := by
  intro first second same
  have sizes := congrArg String.length same
  simp only [freshName, String.length_replicate] at sizes
  omega

@[simp] theorem freshSlots_length (control : Control) (count : Nat) :
    (freshSlots control count).length = count := by simp [freshSlots]

def replace (control : Control) (goals : List Goal) : Control :=
  { control with goals }

def callable (program : SpaceSemantics.Program) (head : String) : Bool :=
  Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head)

/-- Authored match equations need their canonical dispatch policy. This
component does not silently override them with the intrinsic query. -/
def queryOwned (program : SpaceSemantics.Program) : Bool :=
  !(program.equations.any fun equation => equation.head == "match" && equation.arguments.length == 3)

/-- This classification is restricted to the ordinary fixed-head source
surface. Captured native plans, callable pattern heads and opaque host values
remain separate admission facts when constructing the native map. -/
def rigid (program : SpaceSemantics.Program) : Atom → Bool
  | .symbol _ | .grounded _ | .var _ => true
  | .expression (.symbol head :: _) => !callable program head
  | .expression [] => true
  | .expression _ => false

/-- Argument productions are ordered left to right. A literal Atom domain
passes its source as data; all other arguments share their actual fresh slots
with the final call. -/
def callArguments (program : SpaceSemantics.Program) (head : String)
    (arguments slots : List Atom) : List Goal × List Atom :=
  (arguments.zip slots).zipIdx.foldl (fun (pending, ready) ((argument, slot), index) =>
      if Eval.argumentIsRaw program head index then
        (pending, ready ++ [argument])
      else (pending ++ [.evaluate argument slot], ready ++ [slot])) ([], [])

/-- Source scheduling for one let. The relational profile can evaluate either
side first; both sides constrain one shared destination. The body retains the
original outer destination and the reached environment. -/
def letGoals (policy : Policy) (program : SpaceSemantics.Program)
    (pattern producer body output joined : Atom) : List Goal :=
  match policy with
  | .eagerValue => [.evaluate producer joined, .equate pattern joined, .evaluate body output]
  | .relational =>
      if rigid program producer && !rigid program pattern then
        [.evaluate producer joined, .evaluate pattern joined, .evaluate body output]
      else [.evaluate pattern joined, .evaluate producer joined, .evaluate body output]

/-- Relational data skeletons constrain the destination before any child runs.
Eager data builds its children first. This does not move a primitive effect
past its own result check. -/
def dataGoals (policy : Policy) (children slots : List Atom) (destination : Atom) : List Goal :=
  let children := (children.zip slots).map fun (expression, slot) => Goal.evaluate expression slot
  let check := Goal.equate (.expression slots) destination
  match policy with
  | .relational => check :: children
  | .eagerValue => children ++ [check]

inductive Boundary where
  | invoke (head : String) (arguments : List Atom) (destination : Atom)
  | query (location pattern template destination : Atom)
  | invalidEnvironment
  | invalidDelimiter (callerDepth available : Nat)
  | openCommit
  | commit (retained : Nat)
  deriving DecidableEq, Repr

inductive Result where
  | value (value : Atom) (bindings : Equations)
  | noValue (bindings : Equations)
  deriving DecidableEq, Repr

/-- Branch-local request construction. An unimplemented operation is retained
as an operation request, never interpreted as successful exhaustion. -/
def prepare (policy : Policy) (program : SpaceSemantics.Program)
    (control : Control) (expression destination : Atom) (older : List Goal) : Control :=
  let resume := fun goals => replace control (goals ++ older)
  match expression with
  | .var _ | .symbol _ | .grounded _ => resume [.equate expression destination]
  | .expression [.symbol "quote", value] => resume [.equate value destination]
  | .expression [.symbol "let", pattern, producer, body] =>
      resume (letGoals policy program pattern producer body destination
        (.var (freshName control 0)))
  | .expression [.symbol "cut"] =>
      resume [.commit,.equate (Effects.boolean true) destination]
  | .expression [.symbol "once", child] =>
      resume [.openCommit,.evaluate child destination,.commit,.restoreCommit control.cutBoundary]
  | .expression [.symbol "if", condition, yes, no] =>
      let value := Atom.var (freshName control 0)
      resume [.evaluate condition value, .branch value yes no destination]
  | .expression [.symbol "if", condition, yes] =>
      let value := Atom.var (freshName control 0)
      resume [.evaluate condition value, .branch value yes (.expression [.symbol "empty"]) destination]
  | .expression (.symbol head :: arguments) =>
      if callable program head then
        let (pending, ready) := callArguments program head arguments
          (freshSlots control arguments.length)
        resume (pending ++ [.invoke head ready destination])
      else
        let slots := freshSlots control arguments.length
        -- The literal head is never a child call: it belongs to the skeleton.
        let skeleton := Goal.equate (.expression (.symbol head :: slots)) destination
        let work := (arguments.zip slots).map fun (argument, slot) => Goal.evaluate argument slot
        resume (match policy with
          | .relational => skeleton :: work
          | .eagerValue => work ++ [skeleton])
  | .expression children => resume (dataGoals policy children
      (freshSlots control children.length) destination)

/-- One source branch step. Shared-world changes happen in the corresponding
primitive rule and remain in the retained cursor even if matching later fails.
This component does not select a sibling or close a collection scope. -/
def machine {Context : Type} (policy : Policy) (program : SpaceSemantics.Program) :
    Machine (Cursor Context) Empty (Result × Cursor Context) Boundary where
  step cursor := some <|
    match cursor.control.goals with
    | .openCommit :: _ => .call .openCommit cursor
    | .commit :: _ => .call (.commit cursor.control.cutBoundary) cursor
    | .restoreCommit boundary :: older =>
        .silent {cursor with control := {cursor.control with goals := older,cutBoundary := boundary}}
    | [] =>
        match resolve cursor.control.bindings with
        | none => .call .invalidEnvironment cursor
        | some environment => .finish (.value (read environment cursor.control.destination)
            cursor.control.bindings, cursor)
    | .equate value destination :: older =>
        match refine cursor.control.bindings value destination with
        | none => .finish (.noValue cursor.control.bindings, cursor)
        | some bindings => .silent { cursor with control :=
            { cursor.control with bindings, goals := older } }
    | .evaluate expression destination :: older =>
        .silent { cursor with control := prepare policy program cursor.control expression destination older }
    | .branch condition yes no destination :: older =>
        match resolve cursor.control.bindings with
        | none => .call .invalidEnvironment cursor
        | some environment =>
            .silent {cursor with control := (replace cursor.control
              (.evaluate (if read environment condition == Effects.boolean true then yes else no) destination :: older))}
    | .argumentReturn value destination callerDepth :: remaining =>
        match resolve cursor.control.bindings with
        | none => .call .invalidEnvironment cursor
        | some environment =>
            match callerSuffix? callerDepth remaining with
            | none => .call (.invalidDelimiter callerDepth remaining.length) cursor
            | some older =>
                let value := read environment value
                if value.isError then
                  match refine cursor.control.bindings value destination with
                  | none => .finish (.noValue cursor.control.bindings, cursor)
                  | some bindings => .silent { cursor with control :=
                      { cursor.control with bindings, goals := older } }
                else .silent { cursor with control := replace cursor.control remaining }
    | .query location pattern template destination :: _ =>
        match resolve cursor.control.bindings with
        | none => .call .invalidEnvironment cursor
        | some environment =>
            .call (.query (read environment location) pattern template destination) cursor
    | .invoke head arguments destination :: older =>
        match resolve cursor.control.bindings with
        | none => .call .invalidEnvironment cursor
        | some environment =>
            let arguments := arguments.map (read environment)
            match head, arguments with
            | "println!", [value] =>
                .silent { cursor with
                  world := { cursor.world with output := cursor.world.output ++ [value] }
                  control := replace cursor.control (.equate (Effects.boolean true) destination :: older) }
            | _, _ => .call (.invoke head arguments destination) cursor

/-- An independent logical refinement step, including failed matches. -/
inductive Refinement (before : Equations) (value destination : Atom) : Option Equations → Prop where
  | accepted (environment : Environment) (old : Solves environment before)
      (new : read environment value = read environment destination) :
      Refinement before value destination (some (before ++ [(value, destination)]))
  | refused (noSolution : ¬∃ environment, Solves environment before ∧
      read environment value = read environment destination) :
      Refinement before value destination none

theorem refinement_iff (before : Equations) (value destination : Atom) (after : Option Equations) :
    Refinement before value destination after ↔ refine before value destination = after := by
  cases after with
  | some after =>
      rw [refine_iff]
      constructor
      · intro derivation
        cases derivation with
        | accepted environment old new => exact ⟨rfl, environment, old, new⟩
      · rintro ⟨rfl, environment, old, new⟩
        exact .accepted environment old new
  | none =>
      constructor
      · intro derivation
        cases derivation with
        | refused noSolution =>
            cases result : refine before value destination with
            | none => rfl
            | some after => exact False.elim (noSolution ((refine_iff _ _ _ _).mp result).2)
      · intro refused
        apply Refinement.refused
        rintro ⟨environment, old, new⟩
        have accepted := (refine_iff before (before ++ [(value, destination)]) value destination).mpr
          ⟨rfl, environment, old, new⟩
        rw [refused] at accepted
        cases accepted

/-- The local return square uses an independently stated solution relation,
while updating the actual retained bindings and exact older goal list. -/
theorem return_square {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (cursor : Cursor Context) (value destination : Atom) (older : List Goal)
    (atReturn : cursor.control.goals = .equate value destination :: older)
    (after : Equations) :
    Refinement cursor.control.bindings value destination (some after) ↔
      (machine policy program).step cursor = some (.silent
        { cursor with control := { cursor.control with bindings := after, goals := older } }) := by
  rw [refinement_iff]
  simp only [machine, atReturn]
  cases found : refine cursor.control.bindings value destination with
  | none => simp
  | some actual => simp [Control.mk.injEq, Cursor.mk.injEq]

/-- Scheduler cuts save the reached constraint store, world, destination,
older frames and enclosing context. Resumption uses this cursor directly. -/
theorem resume {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (first second : Nat) (source residual : Cursor Context) (events : List Empty)
    (paused : (machine policy program).run first source = (events, .exhausted residual)) :
    (machine policy program).run (first + second) source =
      (events ++ ((machine policy program).run second residual).1,
        ((machine policy program).run second residual).2) :=
  (machine policy program).established_and_pending first second source residual events paused

def start (world : World) (expression destination : Atom) : Cursor Unit :=
  ⟨world, { bindings := [], goals := [.evaluate expression destination], destination }, ()⟩

/-- Public inspection retains failed/suspended cursors too. -/
def observed {Context : Type} : Mettapedia.GSLT.Distinction.ProductiveBlocks.Outcome (Cursor Context) (Result × Cursor Context) Boundary →
    Option (World × Control)
  | .finished (_, cursor) | .exhausted cursor | .suspended _ cursor | .stuck cursor =>
      some (cursor.world, cursor.control)
  | .faulted => none

namespace Controls

def program : SpaceSemantics.Program := { equations := [], declarations := [] }
def world : World := ⟨Effects.empty, [], []⟩
def printMarker : Atom := .expression [.symbol "println!", .symbol "marker"]
def dataPrint : Atom := .expression [.symbol "Data", printMarker]
def veto : Atom := .expression [.symbol "let", .symbol "A", dataPrint, .symbol "C"]

def outputAfter (policy : Policy) (fuel : Nat) (expression : Atom) : Option (List Atom) :=
  (observed ((machine policy program).run fuel (start world expression (.var "out"))).2).map
    (fun result => result.1.output)

#guard outputAfter .relational 40 veto == some []
#guard outputAfter .eagerValue 60 veto == some [.symbol "marker"]
#guard outputAfter .relational 40
  (.expression [.symbol "let", Effects.boolean false, printMarker, .symbol "C"]) ==
  some [.symbol "marker"]


#guard outputAfter .relational 4 printMarker == some [.symbol "marker"]

def resumePrint : Option (List Atom) := do
  match ((machine .relational program).run 4 (start world printMarker (.var "out"))).2 with
  | .exhausted retained =>
      (observed ((machine .relational program).run 10 retained).2).map (fun result => result.1.output)
  | _ => none

#guard resumePrint == some [.symbol "marker"]

/-- Restarting from the original expression after the effect is a different
operation, and visibly repeats it. The retained-resumption law does not do it. -/
def restartedPrint : Option (List Atom) := do
  match ((machine .relational program).run 4 (start world printMarker (.var "out"))).2 with
  | .exhausted retained =>
      (observed ((machine .relational program).run 10
        (start retained.world printMarker (.var "out"))).2).map (fun result => result.1.output)
  | _ => none

#guard restartedPrint == some [.symbol "marker", .symbol "marker"]

/-- The arithmetic source service is intentionally unserved by this local
control component. Its pending call and later let-body are both retained. -/
def pendingNestedCall : Bool :=
  let expression := Atom.expression [.symbol "let", .var "x",
    .expression [.symbol "+", .grounded (.int 1), .grounded (.int 2)], .var "x"]
  match ((machine .relational program).run 40 (start world expression (.var "out"))).2 with
  | .suspended (.invoke "+" _ _) retained => retained.control.goals.length > 1
  | _ => false

#guard pendingNestedCall

end Controls
end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination

/-! ## Certified finite presentation at the destination return boundary

These laws reuse pure first-order binding mathematics. The independently
stated PeTTa return judgment remains the authority; no HE evaluator is used.
Materialization alone is not evaluation of a written application.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Logic.LP
open Mettapedia.Languages.MeTTa.HE (Bindings)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.PrincipalAlpha
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ApplicationEquivariance
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Alpha
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Structural interpretation of a substitution; this compares two syntax
representations, without identifying their language evaluation policies. -/
theorem decode_applyTerm (environment : Environment) (term : Value) :
    decode (environment.applyTerm term) =
      applyTypeValuation (fun name => decode (environment name)) (decode term) := by
  induction term with
  | var name => simp only [Subst.applyTerm, decode, applyTypeValuation]
  | const constant => cases constant <;> simp only [Subst.applyTerm, decode, applyTypeValuation]
  | app arity children ih =>
      simp only [Subst.applyTerm, decode, applyTypeValuation, List.map_ofFn]
      exact congrArg Atom.expression (congrArg List.ofFn (funext ih))

theorem read_eq_applyTypeValuation (environment : Environment) (atom : Atom) :
    read environment atom =
      applyTypeValuation (fun name => decode (environment name)) atom := by
  simpa only [read, decode_encode] using decode_applyTerm environment (encode atom)

/-- Binding certificates and destination constraints denote the same ordinary
first-order equations. All grounded atoms remain constants. -/
theorem solves_binding_equations (environment : Environment) (bindings : Bindings) :
    Solves environment (bindingAtomEquations bindings) ↔
      TypeBindingSatisfied (fun name => decode (environment name)) bindings := by
  rw [typeBindingSatisfied_iff_equations]
  simp only [Solves, read_eq_applyTypeValuation]

theorem solves_append_equation (environment : Environment) (before : Equations)
    (value destination : Atom) :
    Solves environment (before ++ [(value, destination)]) ↔
      Solves environment before ∧ read environment value = read environment destination := by
  constructor
  · intro all
    exact ⟨fun pair member => all pair (List.mem_append_left _ member),
      all (value, destination) (List.mem_append_right _ (by simp))⟩
  · rintro ⟨old, new⟩ pair member
    rcases List.mem_append.mp member with member | member
    · exact old pair member
    · simp only [List.mem_singleton] at member
      subst pair
      exact new

/-- A certified table changes the finite presentation of an operand while
preserving its meaning in every solution of the reached constraints. -/
theorem certified_read_preserves {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table) (environment : Environment)
    (solved : Solves environment (bindingAtomEquations bindings)) (atom : Atom) :
    read environment (table.apply atom) = read environment atom := by
  simpa only [read_eq_applyTypeValuation] using
    certified.preserves_model (fun name => decode (environment name))
      ((solves_binding_equations environment bindings).mp solved) atom

/-- Both operands use one table. In particular this transports failure as
well as success; it does not select a convenient successful valuation. -/
theorem certified_return_solutions {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table) (value destination : Atom)
    (environment : Environment) :
    Solves environment (bindingAtomEquations bindings ++ [(value, destination)]) ↔
      Solves environment (bindingAtomEquations bindings ++
        [(table.apply value, table.apply destination)]) := by
  rw [solves_append_equation, solves_append_equation]
  constructor <;> rintro ⟨old, new⟩ <;> refine ⟨old, ?_⟩
  · simpa only [certified_read_preserves certified environment old] using new
  · simpa only [certified_read_preserves certified environment old] using new

/-- The accepted logical return is equivalent after applying the retained
presentation. Its constraint records are kept distinct. -/
theorem certified_return_accepted {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table) (value destination : Atom) :
    Refinement (bindingAtomEquations bindings) value destination
      (some (bindingAtomEquations bindings ++ [(value, destination)])) ↔
    Refinement (bindingAtomEquations bindings) (table.apply value) (table.apply destination)
      (some (bindingAtomEquations bindings ++ [(table.apply value, table.apply destination)])) := by
  rw [refinement_iff, refinement_iff, refine_iff, refine_iff]
  simp only [true_and]
  apply exists_congr
  intro environment
  simpa only [solves_append_equation] using
    certified_return_solutions certified value destination environment

/-- Refusal means the old constraints and new equation have no common
solution, regardless of the certified residual representative choice. -/
theorem certified_return_refused {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table) (value destination : Atom) :
    Refinement (bindingAtomEquations bindings) value destination none ↔
      Refinement (bindingAtomEquations bindings) (table.apply value) (table.apply destination) none := by
  constructor
  · intro denied
    cases denied with
    | refused noSolution =>
        apply Refinement.refused
        rintro ⟨environment, old, new⟩
        exact noSolution ⟨environment, old, by
          simpa only [certified_read_preserves certified environment old] using new⟩
  · intro denied
    cases denied with
    | refused noSolution =>
        apply Refinement.refused
        rintro ⟨environment, old, new⟩
        exact noSolution ⟨environment, old, by
          simpa only [certified_read_preserves certified environment old] using new⟩

/-- Every later actual destination solution absorbs the earlier retained
presentation on the whole pending tuple, including repeated positions. -/
theorem resolved_pending_absorbs {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table) {later : Equations}
    {environment : Environment} (resolved : resolve later = some environment)
    (extension : ∀ candidate, Solves candidate later →
      Solves candidate (bindingAtomEquations bindings)) (pending : List Atom) :
    (pending.map table.apply).map (read environment) = pending.map (read environment) := by
  have old := extension environment (resolve_sound resolved)
  simp only [List.map_map]
  exact List.map_congr_left fun atom _ => certified_read_preserves certified environment old atom

/-- The actual resolved presentation is most general, by the independent
finite unifier rather than a property required of a binding-reader callback. -/
theorem resolve_mostGeneral {source : Equations} {environment : Environment}
    (resolved : resolve source = some environment) (candidate : Environment)
    (solved : Solves candidate source) : environment.moreGeneral candidate :=
  unifyTotal_mgu (equations source) environment resolved candidate
    ((solves_iff_unifies candidate source).mp solved)

/-- Materializing a returned value through the actual solved presentation
preserves its meaning in every model of the reached equations. This also
holds for open values; selecting one ground solution is unnecessary. -/
theorem resolve_read_preserves {source : Equations} {environment : Environment}
    (resolved : resolve source = some environment) (candidate : Environment)
    (solved : Solves candidate source) (atom : Atom) :
    read candidate (read environment atom) = read candidate atom := by
  have idempotent := (unifyTotal_relevantIdempotent
    (equations source) environment resolved).absorbs
  have absorbs := Subst.absorbs_of_moreGeneral idempotent
    (resolve_mostGeneral resolved candidate solved)
  simpa only [read, encode_decode] using
    congrArg decode (absorbs.applyTerm (encode atom))

/-- The same later model reads the entire saved packet. In particular,
materializing a head does not detach its aliases from pending siblings. -/
theorem resolve_packet_preserves {source : Equations} {environment : Environment}
    (resolved : resolve source = some environment) (candidate : Environment)
    (solved : Solves candidate source) (atoms : List Atom) :
    (atoms.map (read environment)).map (read candidate) = atoms.map (read candidate) := by
  rw [List.map_map]
  exact List.map_congr_left fun atom _ => resolve_read_preserves resolved candidate solved atom

/-- Solved presentation and source packet have exactly the same complete
joint observations. This is stronger than agreement at the chosen unifier. -/
theorem solutionTuples_resolved {source : Equations} {environment : Environment}
    (resolved : resolve source = some environment) (atoms : List Atom) :
    solutionTuples source (atoms.map (read environment)) = solutionTuples source atoms :=
  solutionTuples_congr_models source atoms _
    (fun candidate solved => resolve_packet_preserves resolved candidate solved atoms)

/-- An earlier materialized head remains valid when its caller adds further
constraints. The extension premise is about models, not evaluator results. -/
theorem resolve_read_preserved_by_extension {source later : Equations}
    {environment : Environment} (resolved : resolve source = some environment)
    (extension : ∀ candidate, Solves candidate later → Solves candidate source)
    (candidate : Environment) (solved : Solves candidate later) (atom : Atom) :
    read candidate (read environment atom) = read candidate atom :=
  resolve_read_preserves resolved candidate (extension candidate solved) atom

private theorem moreGeneral_read {first second : Environment}
    (factor : first.moreGeneral second) :
    ∃ post : String → Atom, ∀ atom,
      applyTypeValuation post (read first atom) = read second atom := by
  obtain ⟨post, agreement⟩ := factor
  refine ⟨fun name => decode (post name), ?_⟩
  intro atom
  have functions : second = post ∘ₛ first := funext agreement
  change applyTypeValuation (fun name => decode (post name))
      (decode (first.applyTerm (encode atom))) = decode (second.applyTerm (encode atom))
  rw [← decode_applyTerm, functions, Subst.applyTerm_comp]

/-- One residual permutation witnesses all observed positions simultaneously.
Independent renamings of each output could destroy repeated-variable sharing. -/
theorem resolve_joint_permutation {first second : Equations}
    {left right : Environment} (one : resolve first = some left)
    (two : resolve second = some right)
    (models : ∀ environment, Solves environment first ↔ Solves environment second)
    (pending : List Atom) :
    ∃ permutation : Equiv.Perm String,
      pending.map (read right) = (pending.map (read left)).map (renameTypeVars permutation) := by
  obtain ⟨forward, forwardLaw⟩ := moreGeneral_read
    (resolve_mostGeneral one right ((models right).mpr (resolve_sound two)))
  obtain ⟨backward, backwardLaw⟩ := moreGeneral_read
    (resolve_mostGeneral two left ((models left).mp (resolve_sound one)))
  have alpha := observedTypeAlpha_of_mutual_instances
    ⟨forward, forwardLaw (.expression pending)⟩
    ⟨backward, backwardLaw (.expression pending)⟩
  have singletonAlpha : ScopedObservedTypeListAlphaRel
      [read left (.expression pending)] [read right (.expression pending)] :=
    .cons alpha (by simp [AtomVarsFreshFromAtoms, TypeSubst.typeVarsList])
      (by simp [AtomVarsFreshFromAtoms, TypeSubst.typeVarsList]) .nil
  obtain ⟨permutation, renamedList⟩ := singletonAlpha.exists_permutation
  have renamed := (List.cons.inj renamedList).1
  refine ⟨permutation, ?_⟩
  have expressionRead (environment : Environment) :
      read environment (.expression pending) = .expression (pending.map (read environment)) := by
    rw [read_eq_applyTypeValuation, applyTypeValuation]
    exact congrArg Atom.expression (List.map_congr_left fun atom _ =>
      (read_eq_applyTypeValuation environment atom).symm)
  simpa only [expressionRead, renameTypeVars, Atom.expression.injEq] using renamed

/-- Materialization maps operand positions without changing invocation heads
or erasing goal occurrences. The same table is supplied for every position. -/
def Goal.readout (table : TypeSubst) : Goal → Goal
  | .evaluate expression destination => .evaluate (table.apply expression) (table.apply destination)
  | .equate value destination => .equate (table.apply value) (table.apply destination)
  | .branch condition yes no destination =>
      .branch (table.apply condition) (table.apply yes) (table.apply no) (table.apply destination)
  | .invoke head arguments destination => .invoke head (arguments.map table.apply) (table.apply destination)
  | .query location pattern template destination =>
      .query (table.apply location) (table.apply pattern) (table.apply template) (table.apply destination)
  | .argumentReturn value destination depth => .argumentReturn (table.apply value) (table.apply destination) depth
  | .openCommit => .openCommit
  | .commit => .commit
  | .restoreCommit boundary => .restoreCommit boundary

@[simp] theorem Goal.readout_atoms (table : TypeSubst) (goal : Goal) :
    (goal.readout table).atoms = goal.atoms.map table.apply := by
  cases goal <;> rfl

/-- This view shares the reached equation record. It is a continuation
presentation, not a new evaluator or a change to the source return judgment. -/
def Cursor.readout {Context : Type} (table : TypeSubst) (cursor : Cursor Context) : Cursor Context :=
  { cursor with control := { cursor.control with
      goals := cursor.control.goals.map (Goal.readout table)
      destination := table.apply cursor.control.destination } }

@[simp] theorem Cursor.readout_world {Context : Type} (table : TypeSubst) (cursor : Cursor Context) :
    (cursor.readout table).world = cursor.world := rfl
@[simp] theorem Cursor.readout_context {Context : Type} (table : TypeSubst) (cursor : Cursor Context) :
    (cursor.readout table).context = cursor.context := rfl
@[simp] theorem Cursor.readout_bindings {Context : Type} (table : TypeSubst) (cursor : Cursor Context) :
    (cursor.readout table).control.bindings = cursor.control.bindings := rfl
@[simp] theorem Cursor.readout_reserved {Context : Type} (table : TypeSubst) (cursor : Cursor Context) :
    (cursor.readout table).control.reserved = cursor.control.reserved := rfl

/-- Raw and read-out returns advance the exact corresponding saved cursors.
Their resulting equation lists are semantically equivalent, not identified. -/
theorem certified_return_step {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (cursor : Cursor Context) {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table)
    (record : cursor.control.bindings = bindingAtomEquations bindings)
    (value destination : Atom) (older : List Goal)
    (atReturn : cursor.control.goals = .equate value destination :: older) :
    (machine policy program).step cursor = some (.silent
      { cursor with control := { cursor.control with
        bindings := bindingAtomEquations bindings ++ [(value, destination)], goals := older } }) ↔
    (machine policy program).step (cursor.readout table) = some (.silent
      { cursor.readout table with control := { (cursor.readout table).control with
        bindings := bindingAtomEquations bindings ++ [(table.apply value, table.apply destination)],
        goals := older.map (Goal.readout table) } }) := by
  rw [← return_square policy program cursor value destination older atReturn]
  rw [← return_square policy program (cursor.readout table)
    (table.apply value) (table.apply destination) (older.map (Goal.readout table))
    (by simp only [Cursor.readout, atReturn, List.map_cons, Goal.readout])]
  simpa only [Cursor.readout_bindings, record] using certified_return_accepted certified value destination

/-- A refused return retains its actual cursor, independently of scheduler
exhaustion and unsupported invocation requests. -/
theorem refused_return_square {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (cursor : Cursor Context) (value destination : Atom) (older : List Goal)
    (atReturn : cursor.control.goals = .equate value destination :: older) :
    Refinement cursor.control.bindings value destination none ↔
      (machine policy program).step cursor =
        some (.finish (.noValue cursor.control.bindings, cursor)) := by
  rw [refinement_iff]
  simp only [machine, atReturn]
  cases found : refine cursor.control.bindings value destination <;> simp

/-- Failed refinement retains the reached cursor and shared world on either
presentation. It is not scheduler exhaustion or an unsupported request. -/
theorem certified_refused_step {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (cursor : Cursor Context) {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table)
    (record : cursor.control.bindings = bindingAtomEquations bindings)
    (value destination : Atom) (older : List Goal)
    (atReturn : cursor.control.goals = .equate value destination :: older) :
    (machine policy program).step cursor = some (.finish (.noValue cursor.control.bindings, cursor)) ↔
    (machine policy program).step (cursor.readout table) =
      some (.finish (.noValue cursor.control.bindings, cursor.readout table)) := by
  rw [← refused_return_square policy program cursor value destination older atReturn]
  have reached : (cursor.readout table).control.goals =
      .equate (table.apply value) (table.apply destination) :: older.map (Goal.readout table) := by
    simp only [Cursor.readout, atReturn, List.map_cons, Goal.readout]
  change Refinement cursor.control.bindings value destination none ↔
    (machine policy program).step (cursor.readout table) =
      some (.finish (.noValue (cursor.readout table).control.bindings, cursor.readout table))
  rw [← refused_return_square policy program (cursor.readout table)
    (table.apply value) (table.apply destination) (older.map (Goal.readout table)) reached]
  simpa only [Cursor.readout_bindings, record] using certified_return_refused certified value destination

/-- The actual later solve earns the old-frame extension required for
absorption; it is not supplied as a readout correspondence assumption. -/
theorem resolved_return_pending_absorbs {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table) (value destination : Atom)
    {environment : Environment}
    (resolved : resolve (bindingAtomEquations bindings ++ [(value, destination)]) =
      some environment) (pending : List Atom) :
    (pending.map table.apply).map (read environment) = pending.map (read environment) :=
  resolved_pending_absorbs certified resolved
    (fun candidate solved => (solves_append_equation candidate _ _ _).mp solved |>.1) pending

/-- Starting from an actual accepted raw solve, completeness constructs the
actual solve of the materialized equation. A single permutation compares the
complete joint continuation readout, including every repeated occurrence. -/
theorem certified_return_resolve {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table) (value destination : Atom)
    {environment : Environment}
    (resolved : resolve (bindingAtomEquations bindings ++ [(value, destination)]) =
      some environment) (pending : List Atom) :
    ∃ presented, resolve (bindingAtomEquations bindings ++
        [(table.apply value, table.apply destination)]) = some presented ∧
      ∃ permutation : Equiv.Perm String,
        (pending.map table.apply).map (read presented) =
          (pending.map (read environment)).map (renameTypeVars permutation) := by
  obtain ⟨presented, solved⟩ := resolve_complete
    ⟨environment, (certified_return_solutions certified value destination environment).mp
      (resolve_sound resolved)⟩
  obtain ⟨permutation, joint⟩ := resolve_joint_permutation resolved solved
    (certified_return_solutions certified value destination) pending
  have absorbed := resolved_return_pending_absorbs certified
    (table.apply value) (table.apply destination) solved pending
  exact ⟨presented, solved, permutation, absorbed.trans joint⟩

/-- All pending atom positions in the exact older goal list retain their
order and multiplicity when a single table is read. -/
theorem goals_readout_atoms (table : TypeSubst) (goals : List Goal) :
    (goals.map (Goal.readout table)).flatMap Goal.atoms =
      (goals.flatMap Goal.atoms).map table.apply := by
  induction goals with
  | nil => rfl
  | cons goal goals ih => simp only [List.map_cons, List.flatMap_cons,
      Goal.readout_atoms, ih, List.map_append]

/-- The current destination, older goals and any further contextual operands
form one observation tuple. No per-goal representative is selected. -/
theorem resolved_return_continuation_absorbs {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table) (value destination output : Atom)
    (older : List Goal) (contextual : List Atom) {environment : Environment}
    (resolved : resolve (bindingAtomEquations bindings ++ [(value, destination)]) =
      some environment) :
    (table.apply output ::
      (older.map (Goal.readout table)).flatMap Goal.atoms ++ contextual.map table.apply).map
        (read environment) =
      (output :: older.flatMap Goal.atoms ++ contextual).map (read environment) := by
  rw [goals_readout_atoms]
  simpa only [List.map_cons, List.map_append] using
    resolved_return_pending_absorbs certified value destination resolved
      (output :: older.flatMap Goal.atoms ++ contextual)

/-- Reading a presentation neither merges equal goal occurrences nor changes
any retained world, enclosing context, raw constraint record or reservation. -/
theorem Cursor.readout_retains {Context : Type} (table : TypeSubst) (cursor : Cursor Context) :
    (cursor.readout table).world = cursor.world ∧
      (cursor.readout table).context = cursor.context ∧
      (cursor.readout table).control.bindings = cursor.control.bindings ∧
      (cursor.readout table).control.reserved = cursor.control.reserved ∧
      (cursor.readout table).control.goals.length = cursor.control.goals.length := by
  simp only [Cursor.readout, List.length_map, and_self]

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination

/-! ## Retained invocation and argument-return boundaries -/


set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Bindings)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- A finite saved height implements the independently described split into
younger argument work and the caller's older continuation. -/
theorem callerSuffix?_split (younger older : List Goal) :
    callerSuffix? older.length (younger ++ older) = some older := by
  simp [callerSuffix?]

theorem callerSuffix?_some_iff (depth : Nat) (remaining older : List Goal) :
    callerSuffix? depth remaining = some older ↔
      ∃ younger, remaining = younger ++ older ∧ older.length = depth := by
  constructor
  · intro selected
    unfold callerSuffix? at selected
    split at selected
    · rename_i bound
      cases selected
      refine ⟨remaining.take (remaining.length - depth),
        (List.take_append_drop _ _).symm, ?_⟩
      simp only [List.length_drop]
      omega
    · cases selected
  · rintro ⟨younger, rfl, rfl⟩
    exact callerSuffix?_split younger older

theorem callerSuffix?_none_iff (depth : Nat) (remaining : List Goal) :
    callerSuffix? depth remaining = none ↔ remaining.length < depth := by
  simp [callerSuffix?]

theorem callerSuffix?_readout (table : TypeSubst) (depth : Nat) (remaining : List Goal) :
    callerSuffix? depth (remaining.map (Goal.readout table)) =
      (callerSuffix? depth remaining).map (List.map (Goal.readout table)) := by
  simp only [callerSuffix?, List.length_map]
  split <;> simp [List.map_drop]

/-- Invalid reached constraints have no first-order model. Failure of the
actual total solver is derived from that independent criterion. -/
theorem resolve_none_iff (bindings : Equations) :
    resolve bindings = none ↔ ¬∃ environment, Solves environment bindings := by
  constructor
  · intro missing solution
    obtain ⟨environment, found⟩ := resolve_complete solution
    rw [missing] at found
    cases found
  · intro impossible
    cases found : resolve bindings with
    | none => rfl
    | some environment => exact False.elim (impossible ⟨environment, resolve_sound found⟩)

/-- Independent local argument-return rules. A normal value continues the
whole pending list. An error bypasses only the younger argument work, then
constrains the outer destination with the reached branch equations. -/
inductive ArgumentReturn {Context : Type} (cursor : Cursor Context) (value destination : Atom)
    (younger older : List Goal) :
    Mettapedia.GSLT.Distinction.ProductiveBlocks.Transition
      (Cursor Context) Empty (Result × Cursor Context) Boundary → Prop where
  | ordinary (environment : Environment)
      (resolved : resolve cursor.control.bindings = some environment)
      (normal : (read environment value).isError = false) :
      ArgumentReturn cursor value destination younger older
        (.silent { cursor with control := replace cursor.control (younger ++ older) })
  | propagated (environment : Environment)
      (resolved : resolve cursor.control.bindings = some environment)
      (error : (read environment value).isError = true) (after : Equations)
      (accepted : Refinement cursor.control.bindings (read environment value) destination (some after)) :
      ArgumentReturn cursor value destination younger older
        (.silent { cursor with control := { cursor.control with bindings := after, goals := older } })
  | refused (environment : Environment)
      (resolved : resolve cursor.control.bindings = some environment)
      (error : (read environment value).isError = true)
      (refused : Refinement cursor.control.bindings (read environment value) destination none) :
      ArgumentReturn cursor value destination younger older
        (.finish (.noValue cursor.control.bindings, cursor))
  | invalid (inconsistent : ¬∃ environment, Solves environment cursor.control.bindings) :
      ArgumentReturn cursor value destination younger older
        (.call .invalidEnvironment cursor)

/-- The executable finite delimiter implements every source argument-return
rule without replaying its producer or rolling back its reached world. -/
theorem argumentReturn_source_step {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (cursor : Cursor Context)
    (value destination : Atom) (younger older : List Goal)
    (atReturn : cursor.control.goals =
      .argumentReturn value destination older.length :: younger ++ older)
    {transition : Mettapedia.GSLT.Distinction.ProductiveBlocks.Transition
      (Cursor Context) Empty (Result × Cursor Context) Boundary}
    (source : ArgumentReturn cursor value destination younger older transition) :
    (machine policy program).step cursor = some transition := by
  cases source with
  | ordinary environment resolved normal =>
      simp only [machine, atReturn, List.cons_append, resolved, callerSuffix?_split, normal, Bool.false_eq_true, ↓reduceIte]
  | propagated environment resolved error after accepted =>
      have actual := (refinement_iff _ _ _ _).mp accepted
      simp only [machine, atReturn, List.cons_append, resolved, callerSuffix?_split, error, ↓reduceIte, actual]
  | refused environment resolved error refused =>
      have actual := (refinement_iff _ _ _ _).mp refused
      simp only [machine, atReturn, List.cons_append, resolved, callerSuffix?_split, error, ↓reduceIte, actual]
  | invalid inconsistent =>
      have invalid := (resolve_none_iff _).mpr inconsistent
      simp only [machine, atReturn, List.cons_append, invalid]

/-- Every executable completed local rule reflects to the independent split
judgment. The branch's raw equations and shared world remain visible. -/
theorem argumentReturn_step_source {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (cursor : Cursor Context)
    (value destination : Atom) (younger older : List Goal)
    (atReturn : cursor.control.goals =
      .argumentReturn value destination older.length :: younger ++ older)
    {transition : Mettapedia.GSLT.Distinction.ProductiveBlocks.Transition
      (Cursor Context) Empty (Result × Cursor Context) Boundary}
    (actual : (machine policy program).step cursor = some transition) :
    ArgumentReturn cursor value destination younger older transition := by
  simp only [machine, atReturn, List.cons_append, callerSuffix?_split] at actual
  cases resolved : resolve cursor.control.bindings with
  | none =>
      simp only [resolved, Option.some.injEq] at actual
      subst transition
      exact .invalid ((resolve_none_iff _).mp resolved)
  | some environment =>
      simp only [resolved] at actual
      cases error : (read environment value).isError with
      | false =>
          simp only [error, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at actual
          subst transition
          exact .ordinary environment resolved error
      | true =>
          simp only [error, ↓reduceIte] at actual
          cases refined : refine cursor.control.bindings (read environment value) destination with
          | none =>
              simp only [refined, Option.some.injEq] at actual
              subst transition
              exact .refused environment resolved error ((refinement_iff _ _ _ _).mpr refined)
          | some after =>
              simp only [refined, Option.some.injEq] at actual
              subst transition
              exact .propagated environment resolved error after ((refinement_iff _ _ _ _).mpr refined)

theorem argumentReturn_source_iff {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (cursor : Cursor Context)
    (value destination : Atom) (younger older : List Goal)
    (atReturn : cursor.control.goals =
      .argumentReturn value destination older.length :: younger ++ older)
    (transition : Mettapedia.GSLT.Distinction.ProductiveBlocks.Transition
      (Cursor Context) Empty (Result × Cursor Context) Boundary) :
    ArgumentReturn cursor value destination younger older transition ↔
      (machine policy program).step cursor = some transition :=
  ⟨argumentReturn_source_step policy program cursor value destination younger older atReturn,
   argumentReturn_step_source policy program cursor value destination younger older atReturn⟩

/-- An invalid continuation delimiter is retained separately from both a
refused language equation and scheduler exhaustion. -/
theorem argumentReturn_invalid_delimiter {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (cursor : Cursor Context)
    (value destination : Atom) (depth : Nat) (remaining : List Goal)
    (atReturn : cursor.control.goals = .argumentReturn value destination depth :: remaining)
    {environment : Environment} (resolved : resolve cursor.control.bindings = some environment)
    (invalid : remaining.length < depth) :
    (machine policy program).step cursor =
      some (.call (.invalidDelimiter depth remaining.length) cursor) := by
  have absent := (callerSuffix?_none_iff depth remaining).mpr invalid
  simp only [machine, atReturn, resolved, absent]

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination


set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Every saved delimiter designates an actual suffix of its remaining work.
This property concerns source continuations, independently of an array layout. -/
def WellDelimited : List Goal → Prop
  | [] => True
  | .argumentReturn _ _ depth :: rest => depth ≤ rest.length ∧ WellDelimited rest
  | _ :: rest => WellDelimited rest

private def noDelimiter : Goal → Prop
  | .argumentReturn _ _ _ => False
  | _ => True

theorem WellDelimited.tail {goal : Goal} {rest : List Goal}
    (valid : WellDelimited (goal :: rest)) : WellDelimited rest := by
  cases goal <;> simp only [WellDelimited] at valid ⊢
  all_goals first | exact valid | exact valid.2

theorem WellDelimited.drop {goals : List Goal} (valid : WellDelimited goals) (count : Nat) :
    WellDelimited (goals.drop count) := by
  induction count generalizing goals with
  | zero => exact valid
  | succ count ih =>
      cases goals with
      | nil => trivial
      | cons goal rest => exact ih valid.tail

theorem WellDelimited.suffix {depth : Nat} {remaining older : List Goal}
    (valid : WellDelimited remaining) (selected : callerSuffix? depth remaining = some older) :
    WellDelimited older := by
  obtain ⟨younger, rfl, _⟩ := (callerSuffix?_some_iff depth remaining older).mp selected
  simpa using valid.drop younger.length

theorem WellDelimited.readout (table : TypeSubst) {goals : List Goal}
    (valid : WellDelimited goals) : WellDelimited (goals.map (Goal.readout table)) := by
  induction goals with
  | nil => trivial
  | cons goal rest ih =>
      cases goal <;> simp only [WellDelimited, List.map_cons, Goal.readout, List.length_map] at *
      all_goals first | exact ih valid | exact ⟨valid.1, ih valid.2⟩

private theorem prefix_wellDelimited (work older : List Goal)
    (plain : ∀ goal ∈ work, noDelimiter goal) (valid : WellDelimited older) :
    WellDelimited (work ++ older) := by
  induction work with
  | nil => exact valid
  | cons goal rest ih =>
      have here := plain goal (by simp)
      have tail := ih (fun next occurs => plain next (by simp [occurs]))
      cases goal <;> simp_all [WellDelimited, noDelimiter]

private theorem callArguments_plain (program : SpaceSemantics.Program) (head : String)
    (arguments slots : List Atom) :
    ∀ goal ∈ (callArguments program head arguments slots).1, noDelimiter goal := by
  unfold callArguments
  generalize (arguments.zip slots).zipIdx = rows
  suffices ∀ (pending : List Goal) (ready : List Atom),
      (∀ goal ∈ pending, noDelimiter goal) →
      ∀ goal ∈ (rows.foldl (fun (pending, ready) ((argument, slot), index) =>
        if Eval.argumentIsRaw program head index then (pending, ready ++ [argument])
        else (pending ++ [.evaluate argument slot], ready ++ [slot])) (pending, ready)).1,
      noDelimiter goal by
    exact this [] [] (by simp)
  induction rows with
  | nil => intro pending ready valid; exact valid
  | cons row rest ih =>
      intro pending ready valid
      rcases row with ⟨⟨argument, slot⟩, index⟩
      simp only [List.foldl_cons]
      split
      · exact ih pending _ valid
      · apply ih
        intro goal occurs
        rcases List.mem_append.mp occurs with old | last
        · exact valid goal old
        · simp only [List.mem_singleton] at last
          subst goal
          trivial

private theorem letGoals_plain (policy : Policy) (program : SpaceSemantics.Program)
    (pattern producer body output joined : Atom) :
    ∀ goal ∈ letGoals policy program pattern producer body output joined, noDelimiter goal := by
  cases policy <;> simp only [letGoals]
  · split <;> simp [noDelimiter]
  · simp [noDelimiter]

private theorem dataGoals_plain (policy : Policy) (children slots : List Atom) (destination : Atom) :
    ∀ goal ∈ dataGoals policy children slots destination, noDelimiter goal := by
  intro goal occurs
  cases goal <;> cases policy <;> simp_all [dataGoals, noDelimiter]

/-- Ordinary request construction creates no new delimiter; arbitrary older
valid delimiters survive the newly scheduled prefix. -/
theorem prepare_wellDelimited (policy : Policy) (program : SpaceSemantics.Program)
    (control : Control) (expression destination : Atom) (older : List Goal)
    (valid : WellDelimited older) :
    WellDelimited (prepare policy program control expression destination older).goals := by
  unfold prepare
  split
  · exact prefix_wellDelimited _ _ (by simp [noDelimiter]) valid
  · exact prefix_wellDelimited _ _ (by simp [noDelimiter]) valid
  · exact prefix_wellDelimited _ _ (by simp [noDelimiter]) valid
  · exact prefix_wellDelimited _ _ (by simp [noDelimiter]) valid
  · exact prefix_wellDelimited _ _ (letGoals_plain _ _ _ _ _ _ _) valid
  · exact prefix_wellDelimited _ _ (by simp [noDelimiter]) valid
  · exact prefix_wellDelimited _ _ (by simp [noDelimiter]) valid
  · exact prefix_wellDelimited _ _ (by simp [noDelimiter]) valid
  · exact prefix_wellDelimited _ _ (by simp [noDelimiter]) valid
  · split
    · apply prefix_wellDelimited _ _ ?_ valid
      intro goal occurs
      rcases List.mem_append.mp occurs with pending | invoke
      · exact callArguments_plain _ _ _ _ goal pending
      · cases List.mem_singleton.mp invoke
        trivial
    · apply prefix_wellDelimited _ _ ?_ valid
      intro goal occurs
      cases goal <;> cases policy <;> simp_all [noDelimiter]
  · exact prefix_wellDelimited _ _ (dataGoals_plain _ _ _ _) valid

/-- The independent argument-return judgment retains a valid continuation on
both successful paths. Error propagation selects a proven suffix. -/
theorem argumentReturn_wellDelimited {Context : Type} (cursor : Cursor Context)
    (value destination : Atom) (younger older : List Goal)
    (atReturn : cursor.control.goals =
      .argumentReturn value destination older.length :: (younger ++ older))
    (valid : WellDelimited cursor.control.goals) {target : Cursor Context}
    (source : ArgumentReturn cursor value destination younger older (.silent target)) :
    WellDelimited target.control.goals := by
  rw [atReturn] at valid
  cases source with
  | ordinary => exact valid.2
  | propagated => simpa using valid.2.drop younger.length

/-- One actual source step preserves valid delimiters. The existing evaluator
can run loops; this invariant makes no termination claim. -/
theorem step_wellDelimited {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    {cursor target : Cursor Context} (valid : WellDelimited cursor.control.goals)
    (advanced : (machine policy program).step cursor = some (.silent target)) :
    WellDelimited target.control.goals := by
  cases goals : cursor.control.goals with
  | nil =>
      simp only [machine, goals] at advanced
      cases resolved : resolve cursor.control.bindings <;> simp_all
  | cons goal older =>
      rw [goals] at valid
      cases goal with
      | openCommit | commit => simp [machine, goals] at advanced
      | restoreCommit boundary =>
          simp only [machine, goals, Option.some.injEq, Transition.silent.injEq] at advanced
          subst target
          exact valid
      | evaluate expression destination =>
          simp only [machine, goals, Option.some.injEq, Transition.silent.injEq] at advanced
          subst target
          exact prepare_wellDelimited policy program cursor.control expression destination older valid
      | branch condition yes no destination =>
          simp only [machine, goals] at advanced
          cases resolved : resolve cursor.control.bindings with
          | none => simp [resolved] at advanced
          | some environment =>
              simp only [resolved, Option.some.injEq, Transition.silent.injEq] at advanced
              subst target
              exact valid
      | equate value destination =>
          simp only [machine, goals] at advanced
          cases refined : refine cursor.control.bindings value destination with
          | none => simp [refined] at advanced
          | some bindings =>
              simp only [refined, Option.some.injEq, Transition.silent.injEq] at advanced
              subst target
              exact valid
      | invoke head arguments destination =>
          simp only [machine, goals] at advanced
          cases resolved : resolve cursor.control.bindings with
          | none => simp [resolved] at advanced
          | some environment =>
              simp only [resolved] at advanced
              split at advanced
              · simp only [Option.some.injEq, Transition.silent.injEq] at advanced
                subst target
                exact valid
              · simp at advanced
      | query location pattern template destination =>
          simp only [machine, goals] at advanced
          cases resolved : resolve cursor.control.bindings <;> simp_all
      | argumentReturn value destination depth =>
          obtain ⟨bound, rest⟩ := valid
          have selected : callerSuffix? depth older = some (older.drop (older.length - depth)) := by
            simp [callerSuffix?, bound]
          obtain ⟨younger, split, length⟩ := (callerSuffix?_some_iff _ _ _).mp selected
          have atReturn : cursor.control.goals =
              .argumentReturn value destination (older.drop (older.length - depth)).length ::
                (younger ++ older.drop (older.length - depth)) := by
            rw [length, ← split]
            exact goals
          exact argumentReturn_wellDelimited cursor value destination _ _ atReturn
            (by rw [goals]; exact ⟨bound, rest⟩)
            (argumentReturn_step_source policy program cursor value destination _ _
              (by simpa only [List.cons_append] using atReturn) advanced)

/-- Malformed delimiter refusal is unreachable from a well-delimited source
cursor. This does not conflate it with language-level equation refusal. -/
theorem no_invalidDelimiter_step {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (cursor : Cursor Context) (valid : WellDelimited cursor.control.goals)
    (depth available : Nat) (saved : Cursor Context) :
    (machine policy program).step cursor ≠ some (.call (.invalidDelimiter depth available) saved) := by
  intro bad
  cases goals : cursor.control.goals with
  | nil =>
      simp only [machine, goals] at bad
      cases resolved : resolve cursor.control.bindings <;> simp_all
  | cons goal older =>
      rw [goals] at valid
      cases goal with
      | openCommit | commit | restoreCommit _ => simp [machine, goals] at bad
      | evaluate => simp [machine, goals] at bad
      | branch condition yes no destination =>
          simp only [machine, goals] at bad
          cases resolved : resolve cursor.control.bindings <;> simp_all
      | equate value destination =>
          simp only [machine, goals] at bad
          cases refined : refine cursor.control.bindings value destination <;> simp_all
      | invoke head arguments destination =>
          simp only [machine, goals] at bad
          cases resolved : resolve cursor.control.bindings with
          | none => simp [resolved] at bad
          | some environment =>
              simp only [resolved] at bad
              split at bad <;> simp_all
      | query location pattern template destination =>
          simp only [machine, goals] at bad
          cases resolved : resolve cursor.control.bindings <;> simp_all
      | argumentReturn value destination callerDepth =>
          have selected : callerSuffix? callerDepth older = some (older.drop (older.length - callerDepth)) := by
            simp [callerSuffix?, valid.1]
          simp only [machine, goals, selected] at bad
          cases resolved : resolve cursor.control.bindings with
          | none => simp [resolved] at bad
          | some environment =>
              simp only [resolved] at bad
              split at bad
              · cases refined : refine cursor.control.bindings (read environment value) destination <;> simp_all
              · simp at bad

/-- The local machine records effects in its reached world; it has no separate
publication transition. This is not a physical receipt adequacy claim. -/
theorem no_publish_step {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (cursor target : Cursor Context) (events : List Empty) :
    (machine policy program).step cursor ≠ some (.publish events target) := by
  intro bad
  simp only [machine] at bad
  repeat' first | split at bad | contradiction
  all_goals simp at bad

/-- Every scheduler cut preserves the source delimiter invariant. -/
theorem run_exhausted_wellDelimited {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (ticks : Nat) (cursor saved : Cursor Context)
    (valid : WellDelimited cursor.control.goals) (events : List Empty)
    (paused : (machine policy program).run ticks cursor = (events, .exhausted saved)) :
    WellDelimited saved.control.goals := by
  induction ticks generalizing cursor events with
  | zero =>
      have same := congrArg Prod.snd paused
      cases same
      exact valid
  | succ ticks ih =>
      cases advanced : (machine policy program).step cursor with
      | none => simp [Machine.run, advanced] at paused
      | some transition =>
          cases transition with
          | silent next =>
              apply ih next (step_wellDelimited policy program valid advanced) events
              simpa only [Machine.run, advanced] using paused
          | publish published next =>
              exact False.elim (no_publish_step policy program cursor next published advanced)
          | finish verdict => simp [Machine.run, advanced] at paused
          | fail faults => simp [Machine.run, advanced] at paused
          | call request next => simp [Machine.run, advanced] at paused

/-- A well-formed source execution cannot reach a malformed saved delimiter,
for any scheduler budget or prefix of a looping computation. -/
theorem no_invalidDelimiter_run {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (ticks : Nat) (cursor saved : Cursor Context)
    (valid : WellDelimited cursor.control.goals) (depth available : Nat) :
    ((machine policy program).run ticks cursor).2 ≠
      .suspended (.invalidDelimiter depth available) saved := by
  intro invalid
  have ran : (machine policy program).run ticks cursor =
      (((machine policy program).run ticks cursor).1, .suspended (.invalidDelimiter depth available) saved) :=
    Prod.ext rfl invalid
  obtain ⟨count, _, atBoundary, earlier, final, paused, boundary, _⟩ :=
    (machine policy program).run_boundary_prefix ran
      (by intro residual same; cases same)
  have reached := run_exhausted_wellDelimited policy program count cursor atBoundary valid earlier paused
  have actual := ((machine policy program).run_one_suspended_iff atBoundary final
    (.invalidDelimiter depth available) saved).mp boundary
  exact no_invalidDelimiter_step policy program atBoundary reached depth available saved actual.2

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination


set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Bindings)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Argument return already read the produced value in the reached branch.
Only the destination spelling changes between these two presentations. -/
theorem certified_destination_solutions {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table) (ready destination : Atom)
    (environment : Environment) :
    Solves environment (bindingAtomEquations bindings ++ [(ready, destination)]) ↔
      Solves environment (bindingAtomEquations bindings ++ [(ready, table.apply destination)]) := by
  rw [solves_append_equation, solves_append_equation]
  constructor <;> rintro ⟨old, new⟩ <;> refine ⟨old, ?_⟩ <;>
    simpa only [certified_read_preserves certified environment old] using new

theorem certified_destination_accepted {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table) (ready destination : Atom) :
    Refinement (bindingAtomEquations bindings) ready destination
        (some (bindingAtomEquations bindings ++ [(ready, destination)])) ↔
      Refinement (bindingAtomEquations bindings) ready (table.apply destination)
        (some (bindingAtomEquations bindings ++ [(ready, table.apply destination)])) := by
  rw [refinement_iff, refinement_iff, refine_iff, refine_iff]
  simp only [true_and]
  constructor <;> rintro ⟨environment, old, new⟩ <;> refine ⟨environment, old, ?_⟩ <;>
    simpa only [certified_read_preserves certified environment old] using new

theorem certified_destination_refused {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table) (ready destination : Atom) :
    Refinement (bindingAtomEquations bindings) ready destination none ↔
      Refinement (bindingAtomEquations bindings) ready (table.apply destination) none := by
  constructor <;> intro refused <;> cases refused with
  | refused noSolution =>
      apply Refinement.refused
      rintro ⟨environment, old, new⟩
      apply noSolution
      refine ⟨environment, old, ?_⟩
      simpa only [certified_read_preserves certified environment old] using new

/-- This exact source square retains reached equations on success and drops
only the younger argument prefix designated by the source delimiter. -/
theorem argumentReturn_propagated_square {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (cursor : Cursor Context)
    (value destination : Atom) (younger older : List Goal)
    (atReturn : cursor.control.goals = .argumentReturn value destination older.length ::
      (younger ++ older)) {environment : Environment}
    (resolved : resolve cursor.control.bindings = some environment)
    (error : (read environment value).isError = true) (after : Equations) :
    Refinement cursor.control.bindings (read environment value) destination (some after) ↔
      (machine policy program).step cursor = some (.silent
        { cursor with control := { cursor.control with bindings := after, goals := older } }) := by
  rw [refinement_iff]
  simp only [machine, atReturn, resolved, callerSuffix?_split, error, ↓reduceIte]
  cases refine cursor.control.bindings (read environment value) destination <;>
    simp [Cursor.mk.injEq, Control.mk.injEq]

theorem argumentReturn_refused_square {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (cursor : Cursor Context)
    (value destination : Atom) (younger older : List Goal)
    (atReturn : cursor.control.goals = .argumentReturn value destination older.length ::
      (younger ++ older)) {environment : Environment}
    (resolved : resolve cursor.control.bindings = some environment)
    (error : (read environment value).isError = true) :
    Refinement cursor.control.bindings (read environment value) destination none ↔
      (machine policy program).step cursor = some (.finish (.noValue cursor.control.bindings, cursor)) := by
  rw [refinement_iff]
  simp only [machine, atReturn, resolved, callerSuffix?_split, error, ↓reduceIte]
  cases refine cursor.control.bindings (read environment value) destination <;> simp

/-- Nonerror argument delivery continues the complete pending list; it neither
creates a second result nor constrains the call's final destination early. -/
theorem argumentReturn_ordinary_step {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (cursor : Cursor Context)
    (value destination : Atom) (younger older : List Goal)
    (atReturn : cursor.control.goals = .argumentReturn value destination older.length ::
      (younger ++ older)) {environment : Environment}
    (resolved : resolve cursor.control.bindings = some environment)
    (normal : (read environment value).isError = false) :
    (machine policy program).step cursor = some (.silent
      { cursor with control := replace cursor.control (younger ++ older) }) :=
  argumentReturn_source_step policy program cursor value destination younger older
    (by simpa only [List.cons_append] using atReturn) (.ordinary environment resolved normal)

/-- One shared table preserves the actual guard classification and complete
normal continuation, not merely separate alpha classes of its values. -/
theorem certified_argumentReturn_ordinary {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (cursor : Cursor Context)
    {bindings : Bindings} {table : TypeSubst} (certified : ReadoutCertificate bindings table)
    (record : cursor.control.bindings = bindingAtomEquations bindings)
    (value destination : Atom) (younger older : List Goal)
    (atReturn : cursor.control.goals = .argumentReturn value destination older.length ::
      (younger ++ older)) {environment : Environment}
    (resolved : resolve cursor.control.bindings = some environment)
    (normal : (read environment value).isError = false) :
    (machine policy program).step (cursor.readout table) = some (.silent
      ({ cursor with control := replace cursor.control (younger ++ older) }.readout table)) := by
  have same := certified_read_preserves certified environment
    (resolve_sound (by simpa only [record] using resolved)) value
  simpa only [Cursor.readout, replace, List.map_append] using
    argumentReturn_ordinary_step policy program (cursor.readout table)
      (table.apply value) (table.apply destination)
      (younger.map (Goal.readout table)) (older.map (Goal.readout table))
      (by simp only [Cursor.readout, atReturn, List.map_cons, Goal.readout,
        List.map_append, List.length_map]) resolved (by simpa only [same] using normal)

/-- An error is delivered to the outer destination using the same reached
value. The accepted equation records can differ in presentation, so this law
compares their constructed transitions rather than equating raw records. -/
theorem certified_argumentReturn_propagated {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (cursor : Cursor Context)
    {bindings : Bindings} {table : TypeSubst} (certified : ReadoutCertificate bindings table)
    (record : cursor.control.bindings = bindingAtomEquations bindings)
    (value destination : Atom) (younger older : List Goal)
    (atReturn : cursor.control.goals = .argumentReturn value destination older.length ::
      (younger ++ older)) {environment : Environment}
    (resolved : resolve cursor.control.bindings = some environment)
    (error : (read environment value).isError = true) :
    (machine policy program).step cursor = some (.silent
      { cursor with control := { cursor.control with
        bindings := cursor.control.bindings ++ [(read environment value, destination)], goals := older } }) ↔
    (machine policy program).step (cursor.readout table) = some (.silent
      { cursor.readout table with control := { (cursor.readout table).control with
        bindings := cursor.control.bindings ++ [(read environment value, table.apply destination)],
        goals := older.map (Goal.readout table) } }) := by
  have same := certified_read_preserves certified environment
    (resolve_sound (by simpa only [record] using resolved)) value
  rw [← argumentReturn_propagated_square policy program cursor value destination younger older
    atReturn resolved error]
  rw [← argumentReturn_propagated_square policy program (cursor.readout table)
    (table.apply value) (table.apply destination) (younger.map (Goal.readout table))
    (older.map (Goal.readout table))
    (by simp only [Cursor.readout, atReturn, List.map_cons, Goal.readout,
      List.map_append, List.length_map]) resolved (by simpa only [same] using error)]
  simpa only [Cursor.readout_bindings, record, same] using
    certified_destination_accepted certified (read environment value) destination

/-- Refusal after a reached error keeps the performed world and saved cursor
on either presentation. No younger work or caller alternative is restarted. -/
theorem certified_argumentReturn_refused {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (cursor : Cursor Context)
    {bindings : Bindings} {table : TypeSubst} (certified : ReadoutCertificate bindings table)
    (record : cursor.control.bindings = bindingAtomEquations bindings)
    (value destination : Atom) (younger older : List Goal)
    (atReturn : cursor.control.goals = .argumentReturn value destination older.length ::
      (younger ++ older)) {environment : Environment}
    (resolved : resolve cursor.control.bindings = some environment)
    (error : (read environment value).isError = true) :
    (machine policy program).step cursor = some (.finish (.noValue cursor.control.bindings, cursor)) ↔
    (machine policy program).step (cursor.readout table) =
      some (.finish (.noValue cursor.control.bindings, cursor.readout table)) := by
  have same := certified_read_preserves certified environment
    (resolve_sound (by simpa only [record] using resolved)) value
  rw [← argumentReturn_refused_square policy program cursor value destination younger older
    atReturn resolved error]
  change _ ↔ (machine policy program).step (cursor.readout table) =
    some (.finish (.noValue (cursor.readout table).control.bindings, cursor.readout table))
  rw [← argumentReturn_refused_square policy program (cursor.readout table)
    (table.apply value) (table.apply destination) (younger.map (Goal.readout table))
    (older.map (Goal.readout table))
    (by simp only [Cursor.readout, atReturn, List.map_cons, Goal.readout,
      List.map_append, List.length_map]) resolved (by simpa only [same] using error)]
  simpa only [Cursor.readout_bindings, record, same] using
    certified_destination_refused certified (read environment value) destination

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination


set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Bindings)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Ready arguments are read from the reached equation record. One certified
presentation leaves the complete resolved list literally unchanged. -/
theorem certified_invocation_arguments {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table) {environment : Environment}
    (resolved : resolve (bindingAtomEquations bindings) = some environment)
    (arguments : List Atom) :
    (arguments.map table.apply).map (read environment) = arguments.map (read environment) := by
  simp only [List.map_map]
  exact List.map_congr_left fun argument _ =>
    certified_read_preserves certified environment (resolve_sound resolved) argument

/-- The independently stated print rule supplies the effect. Destination
return matching happens afterwards and cannot undo this append. -/
theorem print_independent_source (program : SpaceSemantics.Program) (world : World) (value : Atom)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (frames : List EagerDFS.Frame) :
    EagerDFS.LocalTransition program world
      ⟨.arguments bindings (.function "println!") [] [value] 0, frames⟩
      { world with output := world.output ++ [value] }
      (.next ⟨.returned (Effects.boolean true), frames⟩) :=
  .print

/-- Actual invocation dispatch preserves reached bindings and older goals.
Its argument is resolved once from those bindings before the source effect. -/
theorem print_step {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (cursor : Cursor Context) (argument destination : Atom) (older : List Goal)
    (atPrint : cursor.control.goals = .invoke "println!" [argument] destination :: older)
    {environment : Environment} (resolved : resolve cursor.control.bindings = some environment) :
    (machine policy program).step cursor = some (.silent
      { cursor with
        world := { cursor.world with output := cursor.world.output ++ [read environment argument] }
        control := replace cursor.control (.equate (Effects.boolean true) destination :: older) }) := by
  simp only [machine, atPrint, resolved, List.map_cons, List.map_nil]

/-- Nonprimitive calls remain requests with their actual resolved arguments.
They are not replaced with a fabricated answer or an empty producer. -/
theorem invoke_request_step {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (cursor : Cursor Context) (head : String) (arguments : List Atom) (destination : Atom)
    (older : List Goal)
    (atCall : cursor.control.goals = .invoke head arguments destination :: older)
    (notPrint : head ≠ "println!") {environment : Environment}
    (resolved : resolve cursor.control.bindings = some environment) :
    (machine policy program).step cursor =
      some (.call (.invoke head (arguments.map (read environment)) destination) cursor) := by
  simp only [machine, atCall, resolved]
  split <;> simp_all

/-- Invalid reached constraints remain a retained boundary on either
presentation; no argument or operation is executed. -/
theorem invocation_invalid_environment {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (cursor : Cursor Context)
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (atCall : cursor.control.goals = .invoke head arguments destination :: older)
    (invalid : resolve cursor.control.bindings = none) (table : TypeSubst) :
    (machine policy program).step cursor = some (.call .invalidEnvironment cursor) ∧
      (machine policy program).step (cursor.readout table) =
        some (.call .invalidEnvironment (cursor.readout table)) := by
  simp only [machine, Cursor.readout, atCall, List.map_cons, Goal.readout, invalid, and_self]

/-- The exact print effect is preserved by one simultaneous presentation.
The target is constructed from the actual resolved argument and reached world. -/
theorem certified_print_step {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (cursor : Cursor Context) {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table)
    (record : cursor.control.bindings = bindingAtomEquations bindings)
    (argument destination : Atom) (older : List Goal)
    (atPrint : cursor.control.goals = .invoke "println!" [argument] destination :: older)
    {environment : Environment} (resolved : resolve cursor.control.bindings = some environment) :
    (machine policy program).step (cursor.readout table) = some (.silent
      ({ cursor with
        world := { cursor.world with output := cursor.world.output ++ [read environment argument] }
        control := replace cursor.control (.equate (Effects.boolean true) destination :: older) }.readout table)) := by
  have same := certified_read_preserves certified environment
    (resolve_sound (by simpa only [record] using resolved)) argument
  simpa only [Cursor.readout, replace, List.map_cons, List.map_nil, Goal.readout,
      TypeSubst.apply, Effects.boolean, same] using
    print_step policy program (cursor.readout table) (table.apply argument) (table.apply destination)
      (older.map (Goal.readout table))
      (by simp only [Cursor.readout, atPrint, List.map_cons, List.map_nil, Goal.readout]) resolved

/-- Suspended invocations carry the same resolved argument occurrences, while
the receiving destination and saved continuation use the shared presentation. -/
theorem certified_invoke_request_step {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (cursor : Cursor Context)
    {bindings : Bindings} {table : TypeSubst} (certified : ReadoutCertificate bindings table)
    (record : cursor.control.bindings = bindingAtomEquations bindings)
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (atCall : cursor.control.goals = .invoke head arguments destination :: older)
    (notPrint : head ≠ "println!") {environment : Environment}
    (resolved : resolve cursor.control.bindings = some environment) :
    (machine policy program).step (cursor.readout table) = some
      (.call (.invoke head (arguments.map (read environment)) (table.apply destination))
        (cursor.readout table)) := by
  have same := certified_invocation_arguments certified
    (by simpa only [record] using resolved) arguments
  simpa only [same] using
    invoke_request_step policy program (cursor.readout table) head (arguments.map table.apply)
      (table.apply destination) (older.map (Goal.readout table))
      (by simp only [Cursor.readout, atCall, List.map_cons, Goal.readout]) notPrint resolved

/-- The source effect before a scheduler cut is retained. Continuing this
saved result executes the pending return check, not the old print invocation. -/
theorem certified_print_resume {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (cursor : Cursor Context) {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table)
    (record : cursor.control.bindings = bindingAtomEquations bindings)
    (argument destination : Atom) (older : List Goal)
    (atPrint : cursor.control.goals = .invoke "println!" [argument] destination :: older)
    {environment : Environment} (resolved : resolve cursor.control.bindings = some environment)
    (later : Nat) :
    (machine policy program).run (later + 1) (cursor.readout table) =
      (machine policy program).run later
        ({ cursor with
          world := { cursor.world with output := cursor.world.output ++ [read environment argument] }
          control := replace cursor.control (.equate (Effects.boolean true) destination :: older) }.readout table) :=
  (machine policy program).run_succ_silent
    (certified_print_step policy program cursor certified record argument destination older atPrint resolved)

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination


set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.ArgumentControls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Bindings)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.Logic.LP

private def program : SpaceSemantics.Program := { equations := [], declarations := [] }
private def pair (a b : Atom) : Atom := .expression [.symbol "Pair", a, b]
private def error : Atom := .expression [.symbol "Error", pair (.var "x") (.var "x")]
private def reachedError : Atom := .expression [.symbol "Error", pair (.symbol "A") (.symbol "A")]
private def bindings : Bindings := ⟨[("x", .var "y"), ("y", .symbol "A")], []⟩
private def table : TypeSubst := CurrentStore.normalize bindings.assignments
private def rank (name : String) : Nat := if name = "x" then 1 else 0

private theorem ranked : CurrentStore.Ranked rank bindings.assignments := by
  intro key value occurs name dependency
  simp only [bindings, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at occurs
  rcases occurs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [TypeSubst.typeVars, List.mem_singleton] at dependency
    subst name
    decide
  · simp [TypeSubst.typeVars] at dependency

private theorem certified : ReadoutCertificate bindings table :=
  CurrentStore.normalize_certified (by decide) ranked

private def world : World := ⟨Effects.empty, [], [.symbol "before"]⟩
private def younger : List Goal := [.invoke "println!" [.symbol "skipped"] (.var "unit")]
private def older : List Goal := [.invoke "println!" [pair (.var "x") (.var "x")] (.var "unit")]
private def cursor : Cursor String :=
  ⟨world, {bindings := bindingAtomEquations bindings
           goals := .argumentReturn error (.var "result") older.length :: (younger ++ older)
           destination := .var "result", reserved := {"sibling"}}, "parent"⟩
private def withEffect : Cursor String :=
  {cursor with control := {cursor.control with
    goals := .invoke "println!" [pair (.var "x") (.var "x")] (.var "unit") :: cursor.control.goals}}

private def outcome (budget : Nat) (state : Cursor String) := (machine .relational program).run budget state
private def printed (result : Mettapedia.GSLT.Distinction.ProductiveBlocks.Outcome (Cursor String) (Result × Cursor String) Boundary) : Option (List Atom) :=
  (observed result).map (fun state => state.1.output)
private def answer (result : Mettapedia.GSLT.Distinction.ProductiveBlocks.Outcome (Cursor String) (Result × Cursor String) Boundary) : Option Atom :=
  match result with | .finished (.value value _, _) => some value | _ => none
private def pending (result : Mettapedia.GSLT.Distinction.ProductiveBlocks.Outcome (Cursor String) (Result × Cursor String) Boundary) : Option (List Goal) :=
  match result with | .exhausted cursor => some cursor.control.goals | _ => none
private def resumePrinted : Option (List Atom) := do
  match (outcome 1 withEffect).2 with
  | .exhausted saved => printed (outcome 20 saved).2
  | _ => none
private def restartedPrinted : Option (List Atom) := do
  match (outcome 1 withEffect).2 with
  | .exhausted saved => printed (outcome 20 {withEffect with world := saved.world}).2
  | _ => none

theorem correlated_guard_readout :
    table.apply error = reachedError ∧
      table.apply (pair (.var "x") (.var "x")) = pair (.symbol "A") (.symbol "A") := by
  simp [table, bindings, CurrentStore.normalize, CurrentStore.normalizeFrom, TypeSubst.bind, TypeSubst.erase,
    TypeSubst.apply, TypeSubst.applyAssignment, TypeSubst.lookup, error, pair, reachedError]

theorem independent_occurrences_cannot_replace_sharing :
    table.apply error ≠ .expression [.symbol "Error", pair (.symbol "A") (.symbol "B")] := by
  rw [correlated_guard_readout.1]
  decide

theorem actual_guard_is_wellDelimited : WellDelimited cursor.control.goals := by
  simp [cursor, younger, older, WellDelimited]

theorem every_budget_excludes_invalid_guard (budget depth available : Nat) (saved : Cursor String) :
    (outcome budget cursor).2 ≠ .suspended (.invalidDelimiter depth available) saved :=
  no_invalidDelimiter_run .relational program budget cursor saved actual_guard_is_wellDelimited depth available

#guard pending (outcome 1 cursor).2 == some older
#guard answer (outcome 20 cursor).2 == some reachedError
#guard printed (outcome 20 cursor).2 == some [.symbol "before", pair (.symbol "A") (.symbol "A")]
#guard printed (outcome 1 withEffect).2 == some [.symbol "before", pair (.symbol "A") (.symbol "A")]
#guard resumePrinted == some [.symbol "before", pair (.symbol "A") (.symbol "A"), pair (.symbol "A") (.symbol "A")]
#guard restartedPrinted == some [.symbol "before", pair (.symbol "A") (.symbol "A"),
  pair (.symbol "A") (.symbol "A"), pair (.symbol "A") (.symbol "A")]

private def refused : Cursor String :=
  {cursor with control := {cursor.control with
    bindings := cursor.control.bindings ++ [(.var "result", .symbol "not-an-error")]}}

private def isRefusal (result : Mettapedia.GSLT.Distinction.ProductiveBlocks.Outcome (Cursor String) (Result × Cursor String) Boundary) : Bool :=
  match result with | .finished (.noValue _, _) => true | _ => false

#guard isRefusal (outcome 20 refused).2
#guard printed (outcome 20 refused).2 == some [.symbol "before"]
#guard !(isRefusal (outcome 0 refused).2)

private def malformed : Cursor String :=
  {cursor with control := {cursor.control with
    goals := [.argumentReturn error (.var "result") 4]}}

private def invalidHeight : Option (Nat × Nat) :=
  match (outcome 3 malformed).2 with
  | .suspended (.invalidDelimiter requested available) _ => some (requested, available)
  | _ => none

#guard invalidHeight == some (4, 0)
#guard !(isRefusal (outcome 3 malformed).2)

theorem malformed_has_no_source_delimiter : ¬WellDelimited malformed.control.goals := by
  simp [malformed, WellDelimited]

theorem saved_suffix_keeps_occurrence_count :
    callerSuffix? 2 (younger ++ older ++ older) = some (older ++ older) := by
  simpa [older, List.append_assoc] using
    callerSuffix?_split younger (older ++ older)

theorem dropping_the_caller_is_not_the_saved_delimiter :
    callerSuffix? older.length (younger ++ older) ≠ some [] := by
  rw [callerSuffix?_split]
  simp [older]

theorem stopped_cursor_retains_scope_and_world :
    (cursor.readout table).context = "parent" ∧
      (cursor.readout table).control.reserved = {"sibling"} ∧
      (cursor.readout table).world = world := by
  exact ⟨rfl, rfl, rfl⟩

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.ArgumentControls


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.ClauseChoice

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Equation Program)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory

/-- All local observations of one clause use one finite renamer. Repeated
variables keep their first position, and equation occurrences remain distinct. -/
def names (atoms : List Atom) : List String := atoms.flatMap TypeSubst.typeVars

def rename (control : Control) (occurrence : Nat) (atoms : List Atom) (name : String) : String :=
  freshName control (Nat.pair occurrence ((names atoms).idxOf name))

def freshen (control : Control) (occurrence : Nat) (atoms : List Atom) : List Atom :=
  atoms.map (renameTypeVars (rename control occurrence atoms))

theorem rename_fresh (control : Control) (occurrence : Nat) (atoms : List Atom) (name : String) :
    rename control occurrence atoms name ∉ control.support :=
  freshName_not_mem control _

theorem rename_injective_on (control : Control) (occurrence : Nat) (atoms : List Atom) :
    Set.InjOn (rename control occurrence atoms) {name | name ∈ names atoms} := by
  intro first firstMember second _secondMember same
  have paired := freshName_injective control same
  have indices := (Nat.pair_eq_pair.mp paired).2
  exact (List.idxOf_inj firstMember).mp indices

theorem distinct_occurrences (control : Control) (first second : Nat)
    (left right : List Atom) (one two : String) (different : first ≠ second) :
    rename control first left one ≠ rename control second right two := by
  intro same
  exact different (Nat.pair_eq_pair.mp (freshName_injective control same)).1

/-- Freshening is one simultaneous syntax map, not independent representative
selection for the individual pattern, body or local continuation positions. -/
theorem freshen_preserves_positions (control : Control) (occurrence : Nat) (atoms : List Atom) :
    (freshen control occurrence atoms).length = atoms.length := by simp [freshen]

theorem freshen_vars_avoid (control : Control) (occurrence : Nat) (atoms : List Atom)
    (atom : Atom) (member : atom ∈ freshen control occurrence atoms)
    (name : String) (occurs : name ∈ TypeSubst.typeVars atom) :
    name ∉ control.support := by
  obtain ⟨original, _present, rfl⟩ := List.mem_map.mp member
  rw [ScopeObservation.typeVars_renameTypeVars] at occurs
  obtain ⟨old, _occurs, rfl⟩ := List.mem_map.mp occurs
  exact rename_fresh control occurrence atoms old

def pattern (equation : Equation) : Atom :=
  .expression (.symbol equation.head :: equation.arguments)

def clauseAtoms (equation : Equation) : List Atom := [pattern equation, equation.body]

def freshPattern (control : Control) (occurrence : Nat) (equation : Equation) : Atom :=
  renameTypeVars (rename control occurrence (clauseAtoms equation)) (pattern equation)

def freshBody (control : Control) (occurrence : Nat) (equation : Equation) : Atom :=
  renameTypeVars (rename control occurrence (clauseAtoms equation)) equation.body

/-- Local source-instance admission states injection and caller avoidance
independently of the allocation algorithm used below. -/
def FreshInstance (control : Control) (equation : Equation) (left body : Atom) : Prop :=
  ∃ renamer : String → String,
    Set.InjOn renamer {name | name ∈ names (clauseAtoms equation)} ∧
    (∀ name ∈ names (clauseAtoms equation), renamer name ∉ control.support) ∧
    left = renameTypeVars renamer (pattern equation) ∧
    body = renameTypeVars renamer equation.body

theorem fresh_clause_instance (control : Control) (occurrence : Nat) (equation : Equation) :
    FreshInstance control equation (freshPattern control occurrence equation)
      (freshBody control occurrence equation) := by
  refine ⟨rename control occurrence (clauseAtoms equation),
    rename_injective_on control occurrence _, ?_, rfl, rfl⟩
  intro name _member
  exact rename_fresh control occurrence _ name

/-- The actual finite matcher decides this attempt. The successful branch
retains raw reached equations and schedules the fresh body on the old caller
continuation; a shared world is not captured into the alternative. -/
def attempt (control : Control) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List Goal) (occurrence : Nat) (equation : Equation) :
    Option Control :=
  if equation.head = head then do
    let bindings ← refine control.bindings (.expression (.symbol head :: arguments))
      (freshPattern control occurrence equation)
    pure { control with
      bindings := bindings
      goals := .evaluate (freshBody control occurrence equation) destination :: older }
  else none

/-- One source position is looked up and attempted without executing its body. -/
def trial (program : Program) (control : Control) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List Goal) (occurrence : Nat) : Option Control := do
  let equation ← program.equations[occurrence]?
  attempt control head arguments destination older occurrence equation

/-- A physical source position survives filtering. Identical equation rows
are attempted separately, in their original order. -/
def choices (program : Program) (control : Control) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List Goal) : List (Nat × Control) :=
  (List.range program.equations.length).filterMap fun occurrence =>
    (trial program control head arguments destination older occurrence).map (occurrence, ·)

/-- The source validity condition is the independent common-solution judgment;
no candidate environment or accepted result is supplied to `attempt`. -/
theorem attempt_iff (control : Control) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List Goal) (occurrence : Nat) (equation : Equation)
    (sameHead : equation.head = head) (next : Control) :
    attempt control head arguments destination older occurrence equation = some next ↔
      ∃ bindings, Refinement control.bindings (.expression (.symbol head :: arguments))
          (freshPattern control occurrence equation) (some bindings) ∧
        next = { control with
          bindings := bindings
          goals := .evaluate (freshBody control occurrence equation) destination :: older } := by
  simp only [attempt, sameHead, ↓reduceIte]
  cases result : refine control.bindings (.expression (.symbol head :: arguments))
      (freshPattern control occurrence equation) with
  | none => simp [result, refinement_iff]
  | some bindings => simp [result, refinement_iff, eq_comm]

theorem attempt_refused_iff (control : Control) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List Goal) (occurrence : Nat) (equation : Equation)
    (sameHead : equation.head = head) :
    attempt control head arguments destination older occurrence equation = none ↔
      Refinement control.bindings (.expression (.symbol head :: arguments))
        (freshPattern control occurrence equation) none := by
  simp only [attempt, sameHead, ↓reduceIte, refinement_iff]
  cases refine control.bindings (.expression (.symbol head :: arguments))
      (freshPattern control occurrence equation) <;> simp

theorem wrong_head_not_selected (control : Control) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List Goal) (occurrence : Nat) (equation : Equation)
    (different : equation.head ≠ head) :
    attempt control head arguments destination older occurrence equation = none := by
  simp [attempt, different]

/-- Exact occurrence origin, including duplicate source equations. -/
theorem mem_choices_iff (program : Program) (control : Control) (head : String)
    (arguments : List Atom) (destination : Atom) (older : List Goal)
    (occurrence : Nat) (next : Control) :
    (occurrence, next) ∈ choices program control head arguments destination older ↔
      ∃ equation, program.equations[occurrence]? = some equation ∧
        attempt control head arguments destination older occurrence equation = some next := by
  simp only [choices, trial, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨index, _bound, selected⟩
    cases row : program.equations[index]? with
    | none => simp [row] at selected
    | some equation =>
        cases choice : attempt control head arguments destination older index equation with
        | none => simp [row, choice] at selected
        | some result =>
            simp [row, choice] at selected
            rcases selected with ⟨rfl, rfl⟩
            exact ⟨equation, row, choice⟩
  · rintro ⟨equation, row, selected⟩
    obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp row
    exact ⟨occurrence, bound, by simp [row, selected]⟩

/-- Every accepted alternative keeps the old caller goals and reserved names.
The produced constraint is appended to the reached record. -/
theorem attempt_preserves_caller (control : Control) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List Goal) (occurrence : Nat) (equation : Equation)
    (next : Control) (selected : attempt control head arguments destination older occurrence equation = some next) :
    next.destination = control.destination ∧ next.reserved = control.reserved ∧
      next.goals = .evaluate (freshBody control occurrence equation) destination :: older ∧
      next.bindings = control.bindings ++
        [(.expression (.symbol head :: arguments), freshPattern control occurrence equation)] := by
  by_cases sameHead : equation.head = head
  · obtain ⟨bindings, valid, rfl⟩ := (attempt_iff control head arguments destination older occurrence equation sameHead next).mp selected
    cases valid
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [wrong_head_not_selected control head arguments destination older occurrence equation sameHead] at selected
    cases selected

/-- Selection does not invalidate an already admitted caller delimiter. -/
theorem attempt_wellDelimited (control : Control) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List Goal) (occurrence : Nat) (equation : Equation)
    (next : Control) (selected : attempt control head arguments destination older occurrence equation = some next)
    (valid : WellDelimited older) : WellDelimited next.goals := by
  rw [(attempt_preserves_caller control head arguments destination older occurrence equation next selected).2.2.1]
  exact valid

/-- Source resolution of a prepared certified frame is constructed; an
inconsistent environment cannot be supplied by that admitted snapshot. -/
theorem certified_resolves {bindings : Mettapedia.Languages.MeTTa.HE.Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table) :
    ∃ environment, resolve (bindingAtomEquations bindings) = some environment := by
  obtain ⟨valuation, satisfied⟩ := certified.satisfiable
  apply resolve_complete
  refine ⟨fun name => encode (valuation name), ?_⟩
  apply (solves_binding_equations _ _).mpr
  simpa only [decode_encode] using satisfied

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.ClauseChoice


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.ClauseChoice
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Equation Program)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- A source alternative is a selected equation occurrence, one fresh local
instance, a common solution of its call equation and reached constraints,
and its actual older continuation. This rule does not execute the body. -/
inductive Selection (program : Program) (control : Control) (head : String)
    (arguments : List Atom) (destination : Atom) (older : List Goal) :
    Nat → Atom → Atom → Control → Prop where
  | selected (occurrence : Nat) (equation : Equation) (left body : Atom) (bindings : Equations)
      (row : program.equations[occurrence]? = some equation)
      (sameHead : equation.head = head)
      (fresh : FreshInstance control equation left body)
      (accepted : Refinement control.bindings (.expression (.symbol head :: arguments)) left
        (some bindings)) :
      Selection program control head arguments destination older occurrence left body
        { control with bindings := bindings, goals := .evaluate body destination :: older }

/-- The exact concrete allocation earns the source instance. Reflection is
for that one shared allocation; arbitrary other fresh spellings are not
claimed to be literally equal records. -/
theorem selection_iff_attempt (program : Program) (control : Control) (head : String)
    (arguments : List Atom) (destination : Atom) (older : List Goal)
    (occurrence : Nat) (equation : Equation) (next : Control)
    (row : program.equations[occurrence]? = some equation) :
    Selection program control head arguments destination older occurrence
      (freshPattern control occurrence equation) (freshBody control occurrence equation) next ↔
      attempt control head arguments destination older occurrence equation = some next := by
  constructor
  · intro selected
    cases selected with
    | selected equation' left body bindings row' same fresh accepted =>
      have equationsSame : equation' = equation := Option.some.inj (row'.symm.trans row)
      subst equation'
      apply (attempt_iff control head arguments destination older occurrence equation same _).mpr
      exact ⟨bindings, accepted, rfl⟩
  · intro actual
    by_cases sameHead : equation.head = head
    · obtain ⟨bindings, valid, rfl⟩ :=
        (attempt_iff control head arguments destination older occurrence equation sameHead next).mp actual
      exact .selected occurrence equation _ _ bindings row sameHead
        (fresh_clause_instance control occurrence equation) valid
    · rw [wrong_head_not_selected control head arguments destination older occurrence equation sameHead] at actual
      cases actual

/-- The actual list selects precisely the source occurrences that admit the
computed fresh instance. Equal equations at different indices remain separate. -/
theorem choices_source_iff (program : Program) (control : Control) (head : String)
    (arguments : List Atom) (destination : Atom) (older : List Goal)
    (occurrence : Nat) (next : Control) :
    (occurrence, next) ∈ choices program control head arguments destination older ↔
      ∃ equation, program.equations[occurrence]? = some equation ∧
        Selection program control head arguments destination older occurrence
          (freshPattern control occurrence equation) (freshBody control occurrence equation) next := by
  rw [mem_choices_iff]
  apply exists_congr
  intro equation
  constructor
  · rintro ⟨row, selected⟩
    exact ⟨row, (selection_iff_attempt program control head arguments destination older occurrence equation next row).mpr selected⟩
  · rintro ⟨row, selected⟩
    exact ⟨row, (selection_iff_attempt program control head arguments destination older occurrence equation next row).mp selected⟩

/-- Successful selection has a genuinely solvable reached store. This is
constructed from its independent matching rule, not required of the caller. -/
theorem selected_resolves {program : Program} {control : Control} {head : String}
    {arguments : List Atom} {destination : Atom} {older : List Goal}
    {occurrence : Nat} {left body : Atom} {next : Control}
    (selected : Selection program control head arguments destination older occurrence left body next) :
    ∃ environment, resolve next.bindings = some environment := by
  cases selected with
  | selected equation left body bindings row same fresh accepted =>
    cases accepted with
    | accepted environment old new =>
      apply resolve_complete
      exact ⟨environment, (solves_append_equation _ _ _ _).mpr ⟨old, new⟩⟩

/-- The new constraint store strengthens the old one. All pending operands
are therefore interpreted by the same later environment. -/
theorem selected_extends {program : Program} {control : Control} {head : String}
    {arguments : List Atom} {destination : Atom} {older : List Goal}
    {occurrence : Nat} {left body : Atom} {next : Control}
    (selected : Selection program control head arguments destination older occurrence left body next)
    (environment : Environment) (solved : Solves environment next.bindings) :
    Solves environment control.bindings := by
  cases selected with
  | selected equation left body bindings row same fresh accepted =>
    cases accepted
    exact (solves_append_equation _ _ _ _).mp solved |>.1

/-- One certified table is absorbed for the whole later tuple, including body,
caller destination and every saved goal; no pointwise residual renaming occurs. -/
theorem selected_pending_absorbed {program : Program} {control : Control} {head : String}
    {arguments : List Atom} {destination : Atom} {older : List Goal}
    {occurrence : Nat} {left body : Atom} {next : Control}
    {bindings : Mettapedia.Languages.MeTTa.HE.Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table)
    (record : control.bindings = bindingAtomEquations bindings)
    (selected : Selection program control head arguments destination older occurrence left body next)
    {environment : Environment} (resolved : resolve next.bindings = some environment)
    (pending : List Atom) :
    (pending.map table.apply).map (read environment) = pending.map (read environment) := by
  apply resolved_pending_absorbs certified resolved
  intro candidate model
  rw [← record]
  exact selected_extends selected candidate model

/-- The same certified presentation may be applied to the complete call
and fresh clause pattern. Selection still checks an actual common solution;
this does not equate the two raw reached equation records. -/
theorem selected_presented_refinement {program : Program} {control : Control} {head : String}
    {arguments : List Atom} {destination : Atom} {older : List Goal}
    {occurrence : Nat} {left body : Atom} {next : Control}
    {bindings : Mettapedia.Languages.MeTTa.HE.Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table)
    (record : control.bindings = bindingAtomEquations bindings)
    (selected : Selection program control head arguments destination older occurrence left body next) :
    Refinement control.bindings (table.apply (.expression (.symbol head :: arguments)))
      (table.apply left) (some (control.bindings ++
        [(table.apply (.expression (.symbol head :: arguments)), table.apply left)])) := by
  have original : Refinement control.bindings (.expression (.symbol head :: arguments)) left
      (some (control.bindings ++ [(.expression (.symbol head :: arguments), left)])) := by
    cases selected with
    | selected equation left body bindings row same fresh accepted =>
      cases accepted with
      | accepted environment old new => exact .accepted environment old new
  rw [record] at original ⊢
  exact (certified_return_accepted certified _ _).mp original

/-- A refused occurrence cannot become an accepted one by presenting its
call and pattern through the retained table. -/
theorem presented_refusal_iff (control : Control) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List Goal) (occurrence : Nat) (equation : Equation)
    (sameHead : equation.head = head)
    {bindings : Mettapedia.Languages.MeTTa.HE.Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table)
    (record : control.bindings = bindingAtomEquations bindings) :
    attempt control head arguments destination older occurrence equation = none ↔
      refine control.bindings (table.apply (.expression (.symbol head :: arguments)))
        (table.apply (freshPattern control occurrence equation)) = none := by
  rw [attempt_refused_iff control head arguments destination older occurrence equation sameHead,
    record, ← refinement_iff]
  exact certified_return_refused certified _ _

/-- Reached invocation requests carry the actual resolved argument list.
Choosing a source equation resumes the saved cursor without copying back an
older world or replacing the caller's context. -/
theorem invocation_selected {Context : Type} (policy : Policy) (program : Program)
    (cursor : Cursor Context) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List Goal)
    (ordinary : Eval.ioHead head = false ∧ StdLib.known head = false)
    (atCall : cursor.control.goals = .invoke head arguments destination :: older)
    {environment : Environment} (resolved : resolve cursor.control.bindings = some environment)
    (occurrence : Nat) (next : Control)
    (selected : (occurrence, next) ∈ choices program cursor.control head
      (arguments.map (read environment)) destination older) :
    (machine policy program).step cursor = some (.call
      (.invoke head (arguments.map (read environment)) destination) cursor) ∧
    ∃ equation, program.equations[occurrence]? = some equation ∧
      Selection program cursor.control head (arguments.map (read environment)) destination older
        occurrence (freshPattern cursor.control occurrence equation)
        (freshBody cursor.control occurrence equation) next ∧
      ({cursor with control := next} : Cursor Context).world = cursor.world ∧
      ({cursor with control := next} : Cursor Context).context = cursor.context := by
  have notPrint : head ≠ "println!" := by
    intro same
    subst head
    simpa [Eval.ioHead] using ordinary.1
  constructor
  · simp [machine, atCall, resolved, notPrint]
  · obtain ⟨equation, row, source⟩ :=
      (choices_source_iff program cursor.control head (arguments.map (read environment)) destination older occurrence next).mp selected
    exact ⟨equation, row, source, rfl, rfl⟩

/-- Administrative selection resumes the actual reached cursor. Subsequent
scheduler cuts obey the existing machine's exact continuation law. -/
theorem selected_resume {Context : Type} (policy : Policy) (program : Program)
    (cursor residual : Cursor Context) (next : Control) (first second : Nat) (events : List Empty)
    (paused : (machine policy program).run first {cursor with control := next} =
      (events, .exhausted residual)) :
    (machine policy program).run (first + second) {cursor with control := next} =
      (events ++ ((machine policy program).run second residual).1,
        ((machine policy program).run second residual).2) :=
  resume policy program first second {cursor with control := next} residual events paused

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.ClauseChoice


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.ClauseChoice.Controls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Logic.LP
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.GSLT.Distinction.ProductiveBlocks

private def pair (left right : Atom) : Atom := .expression [.symbol "pair", left, right]
private def equation : SpaceSemantics.Equation :=
  ⟨"f", [.var "x"], pair (.var "x") (.var "x")⟩
private def duplicateProgram : SpaceSemantics.Program := {equations := [equation, equation], declarations := []}
private def older : List Goal := [.invoke "println!" [pair (.var "x") (.var "x")] (.var "unit")]
private def caller : Control :=
  { bindings := [(.var "x", .symbol "A")]
    goals := .invoke "f" [.symbol "B"] (.var "out") :: older
    destination := .var "out"
    reserved := {"sibling"} }
private def alternatives := choices duplicateProgram caller "f" [.symbol "B"] (.var "out") older
private def first : Control := (alternatives.head?.map Prod.snd).getD caller
private def world : World := ⟨Effects.empty, [], [.symbol "before"]⟩
private def cursor : Cursor String := ⟨world, first, "parent"⟩
private def execution (budget : Nat) := (machine .relational duplicateProgram).run budget cursor
private def answer : Option Atom :=
  match (execution 32).2 with
  | .finished (.value value _, _) => some value
  | _ => none
private def printed : Option (List Atom) :=
  ((observed (execution 32).2).map fun state => state.1.output)
private def reachedReads : Option (List Atom) :=
  match (execution 32).2 with
  | .finished (.value _ bindings, _) => observations bindings [.var "x", .var "out"]
  | _ => none
private def afterPause : Option (List Atom) :=
  match (execution 4).2 with
  | .exhausted saved => ((observed ((machine .relational duplicateProgram).run 28 saved).2).map fun state => state.1.output)
  | _ => none

#guard alternatives.map Prod.fst == [0, 1]
#guard answer == some (pair (.symbol "B") (.symbol "B"))
#guard printed == some [.symbol "before", pair (.symbol "A") (.symbol "A")]
#guard reachedReads == some [.symbol "A", pair (.symbol "B") (.symbol "B")]
#guard afterPause == printed
#guard first.reserved == caller.reserved

/-- Reusing the caller's authored name would reject a valid fresh clause. -/
theorem unrenamed_clause_captures_caller :
    refine caller.bindings (.expression [.symbol "f", .symbol "B"]) (pattern equation) = none := by
  simp [caller, pattern, equation, refine, resolve, equations, encode, unifyTotal,
    Subst.applyEqs, Subst.single, Subst.applyTerm, Term.occursIn,
    finPairsToList, List.finRange_succ]

theorem duplicate_source_occurrences_have_distinct_local_names :
    rename caller 0 (clauseAtoms equation) "x" ≠
      rename caller 1 (clauseAtoms equation) "x" :=
  distinct_occurrences caller 0 1 _ _ "x" "x" (by decide)

private def repeated : SpaceSemantics.Equation := ⟨"g", [.var "x", .var "x"], .var "x"⟩
private def blank : Control := {bindings := [], goals := [], destination := .var "out"}
#guard (attempt blank "g" [.symbol "A", .symbol "A"] (.var "out") [] 0 repeated).isSome
#guard !(attempt blank "g" [.symbol "A", .symbol "B"] (.var "out") [] 0 repeated).isSome
#guard !(attempt blank "h" [.symbol "A", .symbol "A"] (.var "out") [] 0 repeated).isSome

private def inconsistent : Control :=
  {caller with bindings := [(.var "x", .symbol "A"), (.var "x", .symbol "B")]}
#guard (choices duplicateProgram inconsistent "f" [.symbol "B"] (.var "out") older).isEmpty

/-- Selected alternatives are controls only. Dispatching a later alternative
uses the reached shared world and the same parent context. -/
theorem later_alternative_keeps_reached_world (next : Control) (reached : World) :
    ({cursor with world := reached, control := next} : Cursor String).world = reached ∧
      ({cursor with world := reached, control := next} : Cursor String).context = "parent" :=
  ⟨rfl, rfl⟩

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.ClauseChoice.Controls


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Collection
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Destination

/-- The inventory is the complete finite set protected by the enclosing
source context. Computing that inventory from a backend is a separate map. -/
def allocation (protectedNames : Finset String) : Destination.Control :=
  { bindings := [], goals := [], destination := .symbol "collection", reserved := protectedNames }

def copyName (protectedNames : Finset String) (occurrence : Nat)
    (value : Atom) (associated : List Atom) : String → String :=
  ClauseChoice.rename (allocation protectedNames) occurrence (value :: associated)

/-- The value and all syntax attached to this answer use one renaming. The
occurrence index separates equal answers; the source spelling is not a key
shared between answers. -/
def copyAnswer (protectedNames : Finset String) (occurrence : Nat)
    (value : Atom) (associated : List Atom) : Atom × List Atom :=
  let rename := copyName protectedNames occurrence value associated
  (renameTypeVars rename value, associated.map (renameTypeVars rename))

/-- Independent validity of one copied tuple: all participating variables
are renamed injectively and avoid the caller's protected inventory. -/
def IsCopy (protectedNames : Finset String) (value : Atom) (associated : List Atom)
    (copied : Atom × List Atom) : Prop :=
  ∃ rename : String → String,
    Set.InjOn rename {name | name ∈ ClauseChoice.names (value :: associated)} ∧
    (∀ name ∈ ClauseChoice.names (value :: associated), rename name ∉ protectedNames) ∧
    copied.1 = renameTypeVars rename value ∧
    copied.2 = associated.map (renameTypeVars rename)

theorem copyName_fresh (protectedNames : Finset String) (occurrence : Nat)
    (value : Atom) (associated : List Atom) (name : String) :
    copyName protectedNames occurrence value associated name ∉ protectedNames := by
  intro member
  exact ClauseChoice.rename_fresh (allocation protectedNames) occurrence (value :: associated) name
    (Finset.mem_union_left _ member)

theorem copyAnswer_valid (protectedNames : Finset String) (occurrence : Nat)
    (value : Atom) (associated : List Atom) :
    IsCopy protectedNames value associated (copyAnswer protectedNames occurrence value associated) := by
  refine ⟨copyName protectedNames occurrence value associated,
    ClauseChoice.rename_injective_on _ _ _, ?_, rfl, rfl⟩
  intro name _member
  exact copyName_fresh protectedNames occurrence value associated name

theorem copyAnswer_tuple (protectedNames : Finset String) (occurrence : Nat)
    (value : Atom) (associated : List Atom) :
    let copied := copyAnswer protectedNames occurrence value associated
    copied.1 :: copied.2 =
      (value :: associated).map (renameTypeVars (copyName protectedNames occurrence value associated)) := rfl

theorem copyAnswer_variables_fresh (protectedNames : Finset String) (occurrence : Nat)
    (value : Atom) (associated : List Atom) (name : String)
    (occurs : name ∈ TypeSubst.typeVars (copyAnswer protectedNames occurrence value associated).1) :
    name ∉ protectedNames := by
  rw [show (copyAnswer protectedNames occurrence value associated).1 =
    renameTypeVars (copyName protectedNames occurrence value associated) value from rfl,
    ScopeObservation.typeVars_renameTypeVars] at occurs
  obtain ⟨old, _member, rfl⟩ := List.mem_map.mp occurs
  exact copyName_fresh protectedNames occurrence value associated old

/-- A later binding whose keys belong to the caller cannot bind any variable
of the copied answer. The full copied syntax is preserved, not just its shape. -/
theorem caller_assignment_cannot_capture (protectedNames : Finset String) (occurrence : Nat)
    (value : Atom) (associated : List Atom) (later : TypeSubst)
    (owned : ∀ name ∈ later.keys, name ∈ protectedNames) :
    later.apply (copyAnswer protectedNames occurrence value associated).1 =
      (copyAnswer protectedNames occurrence value associated).1 := by
  apply TypeSubst.apply_eq_self_of_variables_not_keys
  intro name present key
  exact copyAnswer_variables_fresh protectedNames occurrence value associated name present
    (owned name key)

/-- Different answer occurrences have disjoint copied variable names, even
when their original payloads are literally equal. -/
theorem different_answers_disjoint (protectedNames : Finset String) (first second : Nat)
    (firstValue secondValue : Atom) (firstAssociated secondAssociated : List Atom)
    (different : first ≠ second) (name : String)
    (firstMember : name ∈ TypeSubst.typeVars
      (copyAnswer protectedNames first firstValue firstAssociated).1) :
    name ∉ TypeSubst.typeVars (copyAnswer protectedNames second secondValue secondAssociated).1 := by
  intro secondMember
  change name ∈ TypeSubst.typeVars (renameTypeVars
    (copyName protectedNames first firstValue firstAssociated) firstValue) at firstMember
  change name ∈ TypeSubst.typeVars (renameTypeVars
    (copyName protectedNames second secondValue secondAssociated) secondValue) at secondMember
  rw [ScopeObservation.typeVars_renameTypeVars] at firstMember secondMember
  obtain ⟨firstName, _one, sameOne⟩ := List.mem_map.mp firstMember
  obtain ⟨secondName, _two, sameTwo⟩ := List.mem_map.mp secondMember
  exact ClauseChoice.distinct_occurrences (allocation protectedNames) first second _ _
    firstName secondName different (sameOne.trans sameTwo.symm)

/-- Associated syntax can include delayed goals, provided their operational
admission is established separately. This law copies the same variable in
value and associated syntax with exactly one map. -/
theorem associated_variable_uses_same_copy (protectedNames : Finset String) (occurrence : Nat)
    (name : String) :
    copyAnswer protectedNames occurrence (.var name) [.var name] =
      (.var (copyName protectedNames occurrence (.var name) [.var name] name),
       [.var (copyName protectedNames occurrence (.var name) [.var name] name)]) := by
  simp [copyAnswer, renameTypeVars]

def copyAnswers (protectedNames : Finset String) (answers : List (Atom × List Atom)) :
    List (Atom × List Atom) :=
  answers.zipIdx.map fun (answer, occurrence) =>
    copyAnswer protectedNames occurrence answer.1 answer.2

theorem copyAnswers_length (protectedNames : Finset String) (answers : List (Atom × List Atom)) :
    (copyAnswers protectedNames answers).length = answers.length := by simp [copyAnswers]

namespace Controls
private def protect : Finset String := {"x", "caller", "future"}
private def pair (left right : Atom) : Atom := .expression [.symbol "Pair", left, right]
private def rows := copyAnswers protect
  [(pair (.var "x") (.var "x"), [.expression [.symbol "delay", .var "x"]]),
   (pair (.var "x") (.var "x"), [.expression [.symbol "delay", .var "x"]])]
private def firstName := copyName protect 0 (pair (.var "x") (.var "x"))
  [.expression [.symbol "delay", .var "x"]] "x"
private def secondName := copyName protect 1 (pair (.var "x") (.var "x"))
  [.expression [.symbol "delay", .var "x"]] "x"

#guard rows == [(pair (.var firstName) (.var firstName), [.expression [.symbol "delay", .var firstName]]),
  (pair (.var secondName) (.var secondName), [.expression [.symbol "delay", .var secondName]])]
#guard firstName != secondName
#guard rows.length == 2
#guard copyAnswers protect [(.symbol "A", []), (.symbol "A", [])] ==
  [(.symbol "A", []), (.symbol "A", [])]
#guard copyAnswers protect [(.grounded (.string "$x"), []), (.grounded (.string "$x"), [])] ==
  [(.grounded (.string "$x"), []), (.grounded (.string "$x"), [])]
#guard (copyAnswer protect 0 (.expression [.symbol "quote", pair (.var "x") (.var "x")]) []).1 !=
  .expression [.symbol "quote", pair (.var "x") (.var "x")]

theorem caller_x_does_not_bind_copied_x :
    TypeSubst.apply [("x", .symbol "A")] (copyAnswer protect 0 (.var "x") []).1 =
      (copyAnswer protect 0 (.var "x") []).1 := by
  apply caller_assignment_cannot_capture
  intro name member
  have same : name = "x" := by simpa [TypeSubst.keys] using member
  simp [same, protect]

theorem original_answer_would_be_captured :
    TypeSubst.apply [("x", .symbol "A")] (.var "x") ≠ .var "x" := by
  simp [TypeSubst.apply, TypeSubst.lookup]

end Controls
end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Collection


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Collection

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.Languages.MeTTa

/-- One manufactured answer owns one finite inventory for its value and all
associated syntax. Repeated uses occupy the same slot. -/
def answerInventory (value : Atom) (associated : List Atom) : MetavariableFrame.Frame :=
  (Destination.ClauseChoice.names (value :: associated)).eraseDups

def allocatedName (token : Token) (inventory : MetavariableFrame.Frame)
    (name : String) : String :=
  CurrentStore.referenceName (token.ref (inventory.idxOf name))

def copyAllocated (token : Token) (value : Atom) (associated : List Atom) : Atom × List Atom :=
  let rename := allocatedName token (answerInventory value associated)
  (renameTypeVars rename value, associated.map (renameTypeVars rename))

/-- Names already represented by live identities or declared globals. This
is a representation invariant, not a claim about arbitrary raw strings. -/
def RepresentedName (allocator : Allocator) (globals : List String) (name : String) : Prop :=
  (∃ reference : Ref, Live allocator ⟨reference.handle, reference.generation⟩ ∧
    name = CurrentStore.referenceName reference) ∨
  (∃ global ∈ globals, name = CurrentStore.freeName global)

def RepresentedAtom (allocator : Allocator) (globals : List String) (atom : Atom) : Prop :=
  ∀ name ∈ TypeSubst.typeVars atom, RepresentedName allocator globals name

theorem allocatedName_injective_on (token : Token) (inventory : MetavariableFrame.Frame) :
    Set.InjOn (allocatedName token inventory) {name | name ∈ inventory} := by
  intro first member second _ same
  have references := CurrentStore.referenceName_injective same
  have slots := congrArg Ref.slot references
  exact (List.idxOf_inj member).mp slots

theorem allocatedName_fresh {allocator next : Allocator} {handle : Nat} {token : Token}
    (allocated : allocate? allocator handle = some (next, token))
    (inventory : MetavariableFrame.Frame) (name : String) (globals : List String) :
    ¬ RepresentedName allocator globals (allocatedName token inventory name) := by
  rintro (⟨old, live, same⟩ | ⟨global, _member, same⟩)
  · have references := CurrentStore.referenceName_injective same
    exact fresh_allocation_distinct_handle allocated live (congrArg Ref.handle references)
  · exact CurrentStore.referenceName_ne_freeName _ _ same

/-- Any finite observation of the old context is protected by the actual
allocator's live-reference separation. No scan of world cells is needed. -/
theorem copyAllocated_valid {allocator next : Allocator} {handle : Nat} {token : Token}
    (allocated : allocate? allocator handle = some (next, token))
    (protectedNames : Finset String) (globals : List String)
    (represented : ∀ name ∈ protectedNames, RepresentedName allocator globals name)
    (value : Atom) (associated : List Atom) :
    IsCopy protectedNames value associated (copyAllocated token value associated) := by
  refine ⟨allocatedName token (answerInventory value associated), ?_, ?_, rfl, rfl⟩
  · intro first firstMember second secondMember same
    exact allocatedName_injective_on token _
      (by simpa [answerInventory] using firstMember)
      (by simpa [answerInventory] using secondMember) same
  · intro name _member present
    exact allocatedName_fresh allocated _ name globals (represented _ present)

theorem copyAllocated_represented {allocator : Allocator} {token : Token}
    (live : Live allocator token) (globals : List String) (value : Atom) (associated : List Atom) :
    RepresentedAtom allocator globals (copyAllocated token value associated).1 := by
  intro name member
  change name ∈ TypeSubst.typeVars (renameTypeVars _ value) at member
  rw [ScopeObservation.typeVars_renameTypeVars] at member
  obtain ⟨old, _present, rfl⟩ := List.mem_map.mp member
  exact Or.inl ⟨token.ref ((answerInventory value associated).idxOf old), live, rfl⟩

theorem represented_preserved_by_allocation {allocator next : Allocator} {handle : Nat}
    {token : Token} (allocated : allocate? allocator handle = some (next, token))
    {globals : List String} {name : String} (represented : RepresentedName allocator globals name) :
    RepresentedName next globals name := by
  rcases represented with ⟨reference, live, same⟩ | global
  · exact Or.inl ⟨reference, (allocation_separates_live allocated live).2.1, same⟩
  · exact Or.inr global

/-- Allocating the second answer while the first is retained earns their
disjoint names, independently of printed spellings and old world size. -/
theorem allocated_answers_disjoint {allocator next : Allocator} {handle : Nat}
    {first second : Token} (firstLive : Live allocator first)
    (allocated : allocate? allocator handle = some (next, second))
    (firstValue secondValue : Atom) (firstAssociated secondAssociated : List Atom)
    (name : String)
    (member : name ∈ TypeSubst.typeVars (copyAllocated first firstValue firstAssociated).1) :
    name ∉ TypeSubst.typeVars (copyAllocated second secondValue secondAssociated).1 := by
  have old := copyAllocated_represented firstLive [] firstValue firstAssociated name member
  intro present
  change name ∈ TypeSubst.typeVars (renameTypeVars _ secondValue) at present
  rw [ScopeObservation.typeVars_renameTypeVars] at present
  obtain ⟨source, _sourceMember, rfl⟩ := List.mem_map.mp present
  exact allocatedName_fresh allocated _ source [] old

private theorem indexOf_of_mem (inventory : MetavariableFrame.Frame)
    (unique : inventory.Nodup) (name : String) (member : name ∈ inventory) :
    MetavariableFrame.indexOf inventory name = some (inventory.idxOf name) := by
  have bound := List.idxOf_lt_length_of_mem member
  have atName : MetavariableFrame.nameOf
      (φ := inventory) ⟨inventory.idxOf name, bound⟩ = name := by
    exact List.getElem_idxOf bound
  simpa only [atName] using
    MetavariableFrame.indexOf_get unique ⟨inventory.idxOf name, bound⟩

theorem allocatedName_eq_nameIn (token : Token) (inventory : MetavariableFrame.Frame)
    (unique : inventory.Nodup) (name : String) (member : name ∈ inventory) :
    allocatedName token inventory name = CurrentStore.nameIn token inventory name := by
  simp only [CurrentStore.nameIn, indexOf_of_mem inventory unique name member, allocatedName]

/-- The same copy is the existing contextual-operand qualification after the
actual answer inventory has been installed. No alternate decoder is used. -/
theorem qualify_answer_copy {Payload : Type} (image : ImageOf Payload)
    (token : Token) (entry : EntryOf Payload)
    (present : image.frameAt token.handle = some entry)
    (generation : entry.generation = token.generation)
    (value : Atom) (associated : List Atom)
    (inventory : entry.frame = answerInventory value associated) :
    CurrentStore.qualify? image (token, value) =
      some (copyAllocated token value associated).1 := by
  have unique : entry.frame.Nodup := by rw [inventory]; exact Mettapedia.Util.LinearHash.eraseDups_nodup _
  rw [CurrentStore.qualify?_of_frame present generation unique]
  congr 1
  apply ScopeObservation.renameTypeVars_congr_on_typeVars value
  intro name member
  rw [inventory]
  exact (allocatedName_eq_nameIn token _ (Mettapedia.Util.LinearHash.eraseDups_nodup _) name
    (by simp only [List.mem_eraseDups, Destination.ClauseChoice.names,
      List.flatMap_cons, List.mem_append]; exact Or.inl member)).symm

theorem qualify_represented {image : ImageOf CurrentStore.ContextualOperand}
    {allocator : Allocator} {globals : List String} {token : Token} {atom qualified : Atom}
    {entry : EntryOf CurrentStore.ContextualOperand}
    (present : image.frameAt token.handle = some entry) (generation : entry.generation = token.generation)
    (unique : entry.frame.Nodup) (live : Live allocator token)
    (scope : CurrentStore.operandScope globals image (token, atom) = true)
    (qualification : CurrentStore.qualify? image (token, atom) = some qualified) :
    RepresentedAtom allocator globals qualified := by
  rw [CurrentStore.qualify?_of_frame present generation unique] at qualification
  cases Option.some.inj qualification
  intro name member
  rw [ScopeObservation.typeVars_renameTypeVars] at member
  obtain ⟨old, occurs, rfl⟩ := List.mem_map.mp member
  rcases (CurrentStore.operandScope_iff present).mp scope old occurs with localMember | global
  · rw [CurrentStore.nameIn, indexOf_of_mem entry.frame unique old localMember]
    exact Or.inl ⟨token.ref (entry.frame.idxOf old), live, rfl⟩
  · cases index : MetavariableFrame.indexOf entry.frame old with
    | none => exact Or.inr ⟨old, global, CurrentStore.nameIn_external _ _ _ index⟩
    | some slot =>
        exact Or.inl ⟨token.ref slot, live, by simp [CurrentStore.nameIn, index]⟩

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Collection


set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Collection

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open NamedSpaces (Store Handle)

/-- All future readable space rows and cells carry owned contextual variable
identities or declared globals. This predicate does not enumerate the store,
change its contents, or validate a missing variable's slot. -/
def RepresentedState (allocator : Allocator) (globals : List String) (state : Effects.State) : Prop :=
  (∀ handle rows, state.read handle = some rows →
    ∀ atom ∈ rows, RepresentedAtom allocator globals atom) ∧
  (∀ cell atom, state.cells cell = some atom → RepresentedAtom allocator globals atom)

def RepresentedWorld (allocator : Allocator) (globals : List String) (world : World) : Prop :=
  RepresentedState allocator globals world.state ∧
    (∀ atom ∈ world.input, RepresentedAtom allocator globals atom) ∧
    (∀ atom ∈ world.output, RepresentedAtom allocator globals atom)

theorem represented_new (allocator : Allocator) (globals : List String) (core : List Atom)
    (represented : ∀ atom ∈ core, RepresentedAtom allocator globals atom) :
    RepresentedState allocator globals (Store.new core []) := by
  constructor
  · intro handle rows present atom member
    cases handle with
    | self =>
      cases Option.some.inj present
      exact represented atom member
    | privateSpace index => simp [Store.new, Store.read] at present
  · intro cell atom present
    simp [Store.new] at present

theorem represented_write {allocator : Allocator} {globals : List String}
    {state next : Effects.State} {handle : Handle} {rows : List Atom}
    (before : RepresentedState allocator globals state)
    (values : ∀ atom ∈ rows, RepresentedAtom allocator globals atom)
    (written : state.write handle rows = some next) :
    RepresentedState allocator globals next := by
  constructor
  · intro observed contents read atom member
    by_cases same : observed = handle
    · subst observed
      have exactRows := Store.write_reads_back state handle rows next written
      cases Option.some.inj (exactRows.symm.trans read)
      exact values atom member
    · rw [Store.write_read_other state handle observed rows next written same] at read
      exact before.1 observed contents read atom member
  · intro cell atom present
    rw [Store.write_preserves_cells state handle rows next written] at present
    exact before.2 cell atom present

theorem represented_allocate_space {allocator : Allocator} {globals : List String}
    {state : Effects.State} (before : RepresentedState allocator globals state)
    (rows : List Atom) (values : ∀ atom ∈ rows, RepresentedAtom allocator globals atom) :
    RepresentedState allocator globals (state.allocate rows).2 := by
  constructor
  · intro observed contents read atom member
    by_cases same : observed = (state.allocate rows).1
    · rw [same, Store.allocation_reads_empty] at read
      cases Option.some.inj read
      exact values atom member
    · rw [Store.allocation_read_existing state rows observed same] at read
      exact before.1 observed contents read atom member
  · exact before.2

theorem represented_putCell {allocator : Allocator} {globals : List String}
    {state : Effects.State} (before : RepresentedState allocator globals state)
    (name : String) (value : Atom) (represented : RepresentedAtom allocator globals value) :
    RepresentedState allocator globals (state.putCell name value) := by
  constructor
  · intro handle rows read
    rw [Store.cell_preserves_spaces] at read
    exact before.1 handle rows read
  · intro cell atom present
    by_cases same : cell = name
    · subst cell
      rw [Store.cell_reads_back] at present
      cases Option.some.inj present
      exact represented
    · rw [Store.cell_read_other state name cell value same] at present
      exact before.2 cell atom present

theorem represented_world_allocation {allocator next : Allocator} {handle : Nat}
    {token : Token} (allocated : allocate? allocator handle = some (next, token))
    {globals : List String} {world : World} (before : RepresentedWorld allocator globals world) :
    RepresentedWorld next globals world := by
  have atomStep : ∀ atom, RepresentedAtom allocator globals atom →
      RepresentedAtom next globals atom := by
    intro atom supported name member
    exact represented_preserved_by_allocation allocated (supported name member)
  exact ⟨⟨fun handle rows read atom member => atomStep atom (before.1.1 handle rows read atom member),
      fun cell atom present => atomStep atom (before.1.2 cell atom present)⟩,
    fun atom member => atomStep atom (before.2.1 atom member),
    fun atom member => atomStep atom (before.2.2 atom member)⟩

theorem represented_print {allocator : Allocator} {globals : List String} {world : World}
    (before : RepresentedWorld allocator globals world) (value : Atom)
    (represented : RepresentedAtom allocator globals value) :
    RepresentedWorld allocator globals {world with output := world.output ++ [value]} := by
  refine ⟨before.1, before.2.1, ?_⟩
  intro atom member
  rcases List.mem_append.mp member with old | new
  · exact before.2.2 atom old
  · cases List.mem_singleton.mp new
    exact represented

theorem represented_read {allocator : Allocator} {globals : List String} {world : World}
    (before : RepresentedWorld allocator globals world) (value : Atom) (rest : List Atom)
    (input : world.input = value :: rest) :
    RepresentedAtom allocator globals value ∧
      RepresentedWorld allocator globals {world with input := rest} := by
  refine ⟨before.2.1 value (by simp [input]), before.1, ?_, before.2.2⟩
  intro atom member
  exact before.2.1 atom (by simp [input, member])

/-- The initial shared store and IO lists are actual existing constructors.
Every atom in this loading packet is qualified through one complete frame. -/
theorem represented_load (allocator : Allocator) (globals : List String) (token : Token)
    (live : Live allocator token) (core input : List Atom) :
    let inventory := (Destination.ClauseChoice.names (core ++ input)).eraseDups
    let rename := allocatedName token inventory
    RepresentedWorld allocator globals
      ⟨Store.new (core.map (renameTypeVars rename)) [],
        input.map (renameTypeVars rename), []⟩ := by
  dsimp only
  have every : ∀ atom, RepresentedAtom allocator globals
      (renameTypeVars (allocatedName token
        (Destination.ClauseChoice.names (core ++ input)).eraseDups) atom) := by
    intro atom name member
    rw [ScopeObservation.typeVars_renameTypeVars] at member
    obtain ⟨old, _occurs, rfl⟩ := List.mem_map.mp member
    exact Or.inl ⟨token.ref (((Destination.ClauseChoice.names (core ++ input)).eraseDups).idxOf old),
      live, rfl⟩
  refine ⟨represented_new allocator globals _ ?_, ?_, ?_⟩
  · intro atom member
    obtain ⟨raw, _present, rfl⟩ := List.mem_map.mp member
    exact every raw
  · intro atom member
    obtain ⟨raw, _present, rfl⟩ := List.mem_map.mp member
    exact every raw
  · simp

/-- A freshly allocated answer cannot be captured by any future read of an
old world cell. The cell remains in the same shared state. -/
theorem allocated_copy_avoids_world_cell {allocator next : Allocator} {handle : Nat}
    {token : Token} (allocated : allocate? allocator handle = some (next, token))
    {globals : List String} {world : World} (represented : RepresentedWorld allocator globals world)
    (cell : String) (stored : Atom) (present : world.state.cells cell = some stored)
    (value : Atom) (associated : List Atom) (name : String)
    (occurs : name ∈ TypeSubst.typeVars stored) :
    name ∉ TypeSubst.typeVars (copyAllocated token value associated).1 := by
  intro copied
  change name ∈ TypeSubst.typeVars (renameTypeVars _ value) at copied
  rw [ScopeObservation.typeVars_renameTypeVars] at copied
  obtain ⟨old, _member, rfl⟩ := List.mem_map.mp copied
  exact allocatedName_fresh allocated _ old globals (represented.1.2 cell stored present _ occurs)

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Collection


set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Collection.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared

private def initialAllocator := Allocator.empty 4 8
private def caller := (allocate? initialAllocator 0).getD (initialAllocator, ⟨0, 0⟩)
private def first := (allocate? caller.1 1).getD (caller.1, ⟨1, 0⟩)
private def second := (allocate? first.1 2).getD (first.1, ⟨2, 0⟩)
private def allocatedPair (x y : Atom) := Atom.expression [.symbol "Pair", x, y]
private def value := allocatedPair (.var "x") (.var "x")
private def associated := [Atom.expression [.symbol "delay", .var "x"]]
private def firstCopy := copyAllocated first.2 value associated
private def secondCopy := copyAllocated second.2 value associated
private def name1 := allocatedName first.2 (answerInventory value associated) "x"
private def name2 := allocatedName second.2 (answerInventory value associated) "x"

theorem first_allocation : allocate? caller.1 1 = some first := by decide +kernel
theorem second_allocation : allocate? first.1 2 = some second := by decide +kernel
theorem first_retained : Live first.1 first.2 := allocated_live first_allocation

theorem allocated_rows_are_independent :
    ∀ name ∈ TypeSubst.typeVars firstCopy.1, name ∉ TypeSubst.typeVars secondCopy.1 :=
  allocated_answers_disjoint first_retained second_allocation _ _ _ _

#guard firstCopy == (allocatedPair (.var name1) (.var name1), [.expression [.symbol "delay", .var name1]])
#guard secondCopy == (allocatedPair (.var name2) (.var name2), [.expression [.symbol "delay", .var name2]])
#guard name1 != name2
#guard copyAllocated first.2 (.grounded (.string "$x")) [] == (.grounded (.string "$x"), [])
#guard (copyAllocated first.2 (.expression [.symbol "quote", value]) associated).1 !=
  .expression [.symbol "quote", value]

private def emptyImage : ImageOf CurrentStore.ContextualOperand := ImageOf.empty 4
private def firstImage :=
  (emptyImage.publish? first.1 first.2 (answerInventory value associated) (fun _ => none)).getD emptyImage

theorem published_first_frame :
    firstImage.frameAt first.2.handle =
      some (EntryOf.initial first.2.generation (answerInventory value associated) (fun _ => none)) := by
  with_unfolding_all rfl

theorem actual_qualifier_observes_copy :
    CurrentStore.qualify? firstImage (first.2, value) = some firstCopy.1 :=
  qualify_answer_copy firstImage first.2 _ published_first_frame rfl value associated rfl

theorem reusing_live_handle_is_refused : allocate? first.1 first.2.handle = none :=
  live_prevents_allocation first_retained

private def program : SpaceSemantics.Program := { equations := [], declarations := [] }
private def finishProtected : Finset String := {"a", "b", "x"}
private def copiedRows :=
  (copyAnswers finishProtected [(Atom.var "x", []), (Atom.var "x", [])]).map Prod.fst
private def equalityBody := Atom.expression [.symbol "==", .var "a", .var "b"]
private def compareFrame := Frame.bind [] (.expression [.var "a", .var "b"]) equalityBody
private def initialWorld : World := ⟨Effects.empty, [], []⟩
private def reachedWorld : World := { initialWorld with output := [.symbol "effect-before-pause"] }
private def parentScope : Scope := ⟨[], [], none⟩
private def resumed := finishScope reachedWorld copiedRows [compareFrame] parentScope []

/-- Correctly copied copiedRows use the existing caller evaluator to produce the
same ground distinction as both tested runtimes. This is the finish seam,
not a claim that the old complete machine already copies its child answers. -/
theorem copied_finish_observes_false :
    answers (advance program 32 resumed) = [Effects.boolean false] := by
  simp only [resumed, copiedRows, copyAnswers, List.zipIdx_cons, List.zipIdx_nil,
    List.map_cons, List.map_nil, copyAnswer, renameTypeVars]
  with_unfolding_all rfl

/-- Reusing one token for both answer occurrences yields the wrong ground
observation, even though the two copiedRows and their order are still retained. -/
theorem reused_answer_token_observes_true :
    answers (advance program 32 (finishScope reachedWorld
      [(copyAllocated first.2 (.var "x") []).1, (copyAllocated first.2 (.var "x") []).1]
      [compareFrame] parentScope [])) = [Effects.boolean true] := by
  simp only [copyAllocated, renameTypeVars]
  with_unfolding_all rfl

theorem copied_finish_keeps_reached_effect :
    (advance program 32 resumed).world.output = [.symbol "effect-before-pause"] := by
  with_unfolding_all rfl

theorem copied_finish_pause_retains_parent :
    advance program 31 (advance program 1 resumed) = advance program 32 resumed := by
  with_unfolding_all rfl

theorem effect_is_actual_source_step :
    localStep program initialWorld
      ⟨.arguments [] (.function "println!") [] [.symbol "effect-before-pause"] 0, []⟩ =
      some (reachedWorld, .next ⟨.returned (Effects.boolean true), []⟩) := by
  with_unfolding_all rfl

private def errorData := Atom.expression [.symbol "Error", .symbol "marker", .symbol "text"]

theorem literal_error_is_collected_data :
    answers (advance program 3 (finishScope reachedWorld [errorData] [] parentScope [])) =
      [.expression [errorData]] := by with_unfolding_all rfl

theorem raised_control_fault_keeps_incomplete_child :
    step program ⟨reachedWorld,
      [⟨[⟨.fault (.invalidArguments "raised"), []⟩], copiedRows, some [compareFrame]⟩, parentScope]⟩ = none := by
  with_unfolding_all rfl

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Collection.Controls


set_option autoImplicit false
namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Collection.Controls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

private def uncopiedCollectionProgram : SpaceSemantics.Program := { equations := [], declarations := [] }
private def uncopiedOpenCollapse : Atom := .expression [.symbol "collapse", .expression
  [.symbol "superpose", .expression [.var "x", .var "x"]]]

/-- The eager profile currently preserves the original open name across
collected rows. This is not PeTTa's independently fresh findall observation. -/
theorem eager_open_collection_keeps_shared_name :
    answers (advance uncopiedCollectionProgram 8 (start Effects.empty uncopiedOpenCollapse)) =
      [.expression [.var "x", .var "x"]] := by with_unfolding_all rfl

private def uncopiedCompareRows : Atom := .expression [.symbol "let", .expression [.var "a", .var "b"],
  uncopiedOpenCollapse, .expression [.symbol "==", .var "a", .var "b"]]

/-- This Boolean observation distinguishes the retained shared name from
PeTTa's per-answer copies without inspecting their printed spelling. -/
theorem eager_open_collection_ground_comparison :
    answers (advance uncopiedCollectionProgram 32 (start Effects.empty uncopiedCompareRows)) =
      [Effects.boolean true] := by with_unfolding_all rfl

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Collection.Controls


set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

namespace Scope

/-- Append one actual occurrence while keeping the older frontier and all
prior rows. Metadata belongs to the answer carrier, not a set of values. -/
def record {Work Answer Caller : Type} (scope : Scope Work Answer Caller)
    (pending : List Work) (answer : Answer) : Scope Work Answer Caller :=
  {scope with frontier := pending, collected := scope.collected ++ [answer]}

/-- The single shared world is threaded through child entry. The parent's
saved frontier is not copied into the child. -/
def enter {Work Answer Caller : Type} (world : World) (scope : Scope Work Answer Caller)
    (pending : List Work) (parents : List (Scope Work Answer Caller))
    (child : Work) (caller : Caller) : Configuration Work Answer Caller :=
  ⟨world, {frontier := [child], caller := some caller} ::
    {scope with frontier := pending} :: parents⟩

/-- The resume map is a structural continuation policy. A not-yet-served
policy or any remaining child work retains the entire source configuration;
neither produces a partial aggregate. -/
def finish? {Work Answer Caller : Type}
    (resume : List Answer → Caller → Option Work)
    (configuration : Configuration Work Answer Caller) : Option (Configuration Work Answer Caller) :=
  match configuration.scopes with
  | {frontier := [], collected := answers, caller := some caller} :: parent :: parents => do
      let work ← resume answers caller
      pure ⟨configuration.world, {parent with frontier := work :: parent.frontier} :: parents⟩
  | _ => none

theorem finish_pending {Work Answer Caller : Type}
    (resume : List Answer → Caller → Option Work) (world : World)
    (scope : Scope Work Answer Caller) (parents : List (Scope Work Answer Caller))
    (work : Work) (pending : List Work) (nonempty : scope.frontier = work :: pending) :
    finish? resume ⟨world, scope :: parents⟩ = none := by
  cases scope
  simp_all [finish?]

theorem finish_completed {Work Answer Caller : Type}
    (resume : List Answer → Caller → Option Work) (world : World)
    (answers : List Answer) (caller : Caller) (parent : Scope Work Answer Caller)
    (parents : List (Scope Work Answer Caller)) (work : Work)
    (resumed : resume answers caller = some work) :
    finish? resume ⟨world, ⟨[], answers, some caller⟩ :: parent :: parents⟩ =
      some ⟨world, {parent with frontier := work :: parent.frontier} :: parents⟩ := by
  simp [finish?, resumed]

theorem finish_unserved {Work Answer Caller : Type}
    (resume : List Answer → Caller → Option Work) (world : World)
    (answers : List Answer) (caller : Caller) (parent : Scope Work Answer Caller)
    (parents : List (Scope Work Answer Caller)) (unserved : resume answers caller = none) :
    finish? resume ⟨world, ⟨[], answers, some caller⟩ :: parent :: parents⟩ = none := by
  simp [finish?, unserved]

theorem finish_preserves_world {Work Answer Caller : Type}
    (resume : List Answer → Caller → Option Work)
    {before after : Configuration Work Answer Caller} (finished : finish? resume before = some after) :
    after.world = before.world := by
  unfold finish? at finished
  split at finished
  · obtain ⟨work, _selected, same⟩ := Option.bind_eq_some_iff.mp finished
    cases Option.some.inj same
    rfl
  · contradiction

def eagerResume (answers : List Atom) (frames : List Frame) : Option Branch :=
  some ⟨.returned (.expression answers), frames⟩

/-- The old eager collector is precisely the corresponding instance of the
shared scope boundary, including its presently uncopied row policy. -/
theorem eager_finish_instance (world : World) (answers : List Atom) (frames : List Frame)
    (parent : Scope) (parents : List Scope) :
    finish? eagerResume ⟨world, ⟨[], answers, some frames⟩ :: parent :: parents⟩ =
      some (finishScope world answers frames parent parents) := rfl

theorem eager_enter_instance (world : World) (scope : Scope) (pending : List Branch)
    (parents : List Scope) (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (expression : Atom) (frames : List Frame) :
    enter world scope pending parents ⟨.evaluate bindings expression, []⟩ frames =
      install world scope pending parents (.collect bindings expression frames) := rfl

theorem eager_record_instance (world : World) (scope : Scope) (pending : List Branch)
    (parents : List Scope) (value : Atom) :
    (⟨world, record scope pending value :: parents⟩ : Configuration) =
      install world scope pending parents (.answer value) := rfl

end Scope

namespace Destination

/-- Value, reached bindings, source occurrences and associated syntax are
retained while collection is incomplete. Associated operational work has a
separate admission; it is never silently discarded. -/
structure CollectedAnswer where
  value : Atom
  bindings : Equations
  occurrences : List Nat
  associated : List Atom := []
  deriving Repr

abbrev CollectionWork (Context : Type) := Control × Context × List Nat
abbrev CollectionCaller (Context : Type) := Control × Atom × Context × List Nat
abbrev CollectionScope (Context : Type) :=
  Scope (CollectionWork Context) CollectedAnswer (CollectionCaller Context)

/-- This finite collection policy computes fresh copies of the actual rows.
The independent copy laws justify its renaming. Nonempty associated work
remains an unserved collection continuation in this instance. -/
def copiedResume {Context : Type} (protectedNames : Finset String)
    (answers : List CollectedAnswer) (caller : CollectionCaller Context) : Option (CollectionWork Context) :=
  if answers.all (fun answer => answer.associated.isEmpty) then
    let copied := Collection.copyAnswers protectedNames
      (answers.map fun answer => (answer.value, answer.associated))
    some ({caller.1 with
      goals := Goal.equate (.expression (copied.map Prod.fst)) caller.2.1 :: caller.1.goals},
      caller.2.2.1, caller.2.2.2)
  else none

theorem copied_resume_retains_caller {Context : Type} (protectedNames : Finset String)
    (answers : List CollectedAnswer) (caller : CollectionCaller Context) (work : CollectionWork Context)
    (resumed : copiedResume protectedNames answers caller = some work) :
    work.1.bindings = caller.1.bindings ∧ work.1.destination = caller.1.destination ∧
      work.1.reserved = caller.1.reserved ∧ work.2 = caller.2.2 := by
  unfold copiedResume at resumed
  split at resumed
  · cases Option.some.inj resumed
    exact ⟨rfl, rfl, rfl, rfl⟩
  · contradiction

theorem associated_work_retained {Context : Type} (protectedNames : Finset String)
    (answers : List CollectedAnswer) (caller : CollectionCaller Context)
    (answer : CollectedAnswer) (present : answer ∈ answers) (pending : answer.associated ≠ []) :
    copiedResume protectedNames answers caller = none := by
  have refused : answers.all (fun answer => answer.associated.isEmpty) ≠ true := by
    intro all
    exact pending (List.isEmpty_iff.mp (List.all_eq_true.mp all answer present))
  simp [copiedResume, refused]

/-- Partial child results cannot reach the copied return policy. The exact
older frontier, bindings and one shared world remain in the saved carrier. -/
theorem copied_collection_pending {Context : Type} (protectedNames : Finset String)
    (world : World) (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (work : CollectionWork Context) (pending : List (CollectionWork Context))
    (nonempty : scope.frontier = work :: pending) :
    Scope.finish? (copiedResume protectedNames) ⟨world, scope :: parents⟩ = none :=
  Scope.finish_pending _ _ _ _ _ _ nonempty

theorem copied_collection_completed {Context : Type} (protectedNames : Finset String)
    (world : World) (answers : List CollectedAnswer) (caller : CollectionCaller Context)
    (parent : CollectionScope Context) (parents : List (CollectionScope Context))
    (work : CollectionWork Context) (resumed : copiedResume protectedNames answers caller = some work) :
    Scope.finish? (copiedResume protectedNames)
      ⟨world, ⟨[], answers, some caller⟩ :: parent :: parents⟩ =
        some ⟨world, {parent with frontier := work :: parent.frontier} :: parents⟩ :=
  Scope.finish_completed _ _ _ _ _ _ _ resumed

/-- An actual terminal branch supplies the collected value and its complete
reached constraint record. The occurrence path is retained separately. -/
theorem terminal_answer_iff {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (cursor : Cursor Context) (value : Atom) (bindings : Equations)
    (atEnd : cursor.control.goals = []) :
    (machine policy program).step cursor = some (.finish (.value value bindings, cursor)) ↔
      ∃ environment, resolve cursor.control.bindings = some environment ∧
        value = read environment cursor.control.destination ∧ bindings = cursor.control.bindings := by
  simp only [machine, atEnd]
  cases resolved : resolve cursor.control.bindings with
  | none => simp
  | some environment => simp [eq_comm, and_comm]

theorem terminal_answer_has_source_model {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (cursor : Cursor Context) (value : Atom) (bindings : Equations)
    (atEnd : cursor.control.goals = [])
    (returned : (machine policy program).step cursor = some (.finish (.value value bindings, cursor))) :
    ∃ environment, Solves environment bindings ∧ value = read environment cursor.control.destination := by
  obtain ⟨environment, resolved, valueEq, rfl⟩ :=
    (terminal_answer_iff policy program cursor value bindings atEnd).mp returned
  exact ⟨environment, resolve_sound resolved, valueEq⟩

theorem value_return_has_empty_goals {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (cursor reached : Cursor Context)
    (value : Atom) (bindings : Equations)
    (returned : (machine policy program).step cursor = some (.finish (.value value bindings, reached))) :
    cursor.control.goals = [] := by
  cases goals : cursor.control.goals with
  | nil => rfl
  | cons goal rest =>
    cases goal <;> simp only [machine, goals] at returned
    all_goals
      repeat' first | split at returned | contradiction | cases returned

/-- Lift one actual child terminal return into the existing scope carrier.
The selected work, reached world, raw equations and occurrence path are read
from that return. No expected-value callback supplies the collected payload. -/
def collectReturned? {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (configuration : Configuration (CollectionWork Context) CollectedAnswer (CollectionCaller Context)) :
    Option (Configuration (CollectionWork Context) CollectedAnswer (CollectionCaller Context)) :=
  match configuration.scopes with
  | scope :: parents =>
    match scope.frontier with
    | (control, context, occurrences) :: pending =>
      match (machine policy program).step ⟨configuration.world, control, context⟩ with
      | some (.finish (.value value bindings, reached)) =>
        some ⟨reached.world, Scope.record scope pending ⟨value, bindings, occurrences, []⟩ :: parents⟩
      | _ => none
    | [] => none
  | [] => none

/-- Collection closes only after the actual child return emptied its frontier
and the copy policy served the entire answer list. Otherwise the newly reached
scope remains saved, including any associated work not handled by this policy. -/
def collectAndResume? {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (protectedNames : Finset String)
    (configuration : Configuration (CollectionWork Context) CollectedAnswer (CollectionCaller Context)) :
    Option (Configuration (CollectionWork Context) CollectedAnswer (CollectionCaller Context)) := do
  let collected ← collectReturned? policy program configuration
  pure ((Scope.finish? (copiedResume protectedNames) collected).getD collected)

theorem collect_actual_terminal {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (world : World) (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (control : Control) (context : Context) (occurrences : List Nat)
    (pending : List (CollectionWork Context)) (value : Atom) (bindings : Equations)
    (frontier : scope.frontier = (control, context, occurrences) :: pending)
    (returned : (machine policy program).step ⟨world, control, context⟩ =
      some (.finish (.value value bindings, ⟨world, control, context⟩))) :
    collectReturned? policy program ⟨world, scope :: parents⟩ =
      some ⟨world, Scope.record scope pending ⟨value, bindings, occurrences, []⟩ :: parents⟩ := by
  simp [collectReturned?, frontier, returned]

/-- An actual earlier occurrence cannot publish a partial aggregate while
another child alternative is saved. The complete row metadata is appended. -/
theorem collect_keeps_pending_alternative {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (protectedNames : Finset String)
    (world : World) (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (control : Control) (context : Context) (occurrences : List Nat)
    (next : CollectionWork Context) (pending : List (CollectionWork Context))
    (value : Atom) (bindings : Equations)
    (frontier : scope.frontier = (control, context, occurrences) :: next :: pending)
    (returned : (machine policy program).step ⟨world, control, context⟩ =
      some (.finish (.value value bindings, ⟨world, control, context⟩))) :
    collectAndResume? policy program protectedNames ⟨world, scope :: parents⟩ =
      some ⟨world, Scope.record scope (next :: pending) ⟨value, bindings, occurrences, []⟩ :: parents⟩ := by
  rw [collectAndResume?, collect_actual_terminal policy program world scope parents control context
    occurrences (next :: pending) value bindings frontier returned]
  simp [Scope.finish?, Scope.record]

/-- The final actual child value is appended and copied before the caller's
first resumed goal can run. Old siblings and the reached shared world survive. -/
theorem last_return_copies_before_caller {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (protectedNames : Finset String)
    (world : World) (scope parent : CollectionScope Context) (parents : List (CollectionScope Context))
    (control : Control) (context : Context) (occurrences : List Nat)
    (caller : CollectionCaller Context) (value : Atom) (bindings : Equations)
    (frontier : scope.frontier = [(control, context, occurrences)])
    (saved : scope.caller = some caller)
    (returned : (machine policy program).step ⟨world, control, context⟩ =
      some (.finish (.value value bindings, ⟨world, control, context⟩)))
    (work : CollectionWork Context)
    (copied : copiedResume protectedNames
      (scope.collected ++ [⟨value, bindings, occurrences, []⟩]) caller = some work) :
    collectAndResume? policy program protectedNames ⟨world, scope :: parent :: parents⟩ =
      some ⟨world, {parent with frontier := work :: parent.frontier} :: parents⟩ := by
  rw [collectAndResume?, collect_actual_terminal policy program world scope (parent :: parents)
    control context occurrences [] value bindings frontier returned]
  simp [Scope.finish?, Scope.record, saved, copied]

namespace CollectionControls
private def pair (x y : Atom) : Atom := .expression [.symbol "Pair", x, y]
private def row : CollectedAnswer :=
  ⟨pair (.var "x") (.var "x"), [(.var "unused", .symbol "B")], [4, 9], []⟩
private def outer : Control :=
  {bindings := [(.var "caller", .symbol "A")]
   goals := [.invoke "println!" [.var "caller"] (.var "unit")]
   destination := .var "out", reserved := {"older"}}
private def caller : CollectionCaller String := (outer, .var "target", "saved-caller", [2, 3])
private def oldWork : CollectionWork String := (outer, "older-sibling", [1])
private def parent : CollectionScope String := ⟨[oldWork], [], none⟩
private def world : World := ⟨Effects.empty, [], [.symbol "earlier-effect"]⟩
private def protectedNames : Finset String := outer.support ∪ {"target"}
private def child : CollectionScope String := ⟨[], [row, row], some caller⟩
private def finished := Scope.finish? (copiedResume protectedNames) ⟨world, [child, parent]⟩
private def observeFinish := finished.bind fun configuration =>
  configuration.scopes.head?.bind fun scope =>
    scope.frontier.head?.map fun work =>
      (configuration.world.output, configuration.scopes.length,
       scope.frontier.length, work.2, work.1.bindings)

#guard observeFinish == some ([.symbol "earlier-effect"], 1, 2,
  ("saved-caller", [2, 3]), outer.bindings)
#guard (copiedResume protectedNames [row, row] caller).map
  (fun work => work.1.goals.tail) == some outer.goals
#guard ((Scope.finish? (copiedResume protectedNames)
  ⟨world, [{child with frontier := [oldWork]}, parent]⟩).map
  (fun configuration => configuration.scopes.length)) == none
#guard (copiedResume protectedNames [{row with associated := [.symbol "delayed"]}] caller).isNone
#guard child.collected.map CollectedAnswer.occurrences == [[4, 9], [4, 9]]
#guard child.collected.map CollectedAnswer.bindings == [row.bindings, row.bindings]

end CollectionControls

end Destination
end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS


set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.GSLT.Distinction.ProductiveBlocks

namespace Collection

/-- Ordered answer copies retain every occurrence. Each row has an independent
injective map, and distinct rows have disjoint residual variables. -/
def Copies (protectedNames : Finset String) (source copied : List (Atom × List Atom)) : Prop :=
  copied.length = source.length ∧
  (∀ index (before : index < source.length) (after : index < copied.length),
    IsCopy protectedNames source[index].1 source[index].2 copied[index]) ∧
  (∀ first second (firstBound : first < copied.length) (secondBound : second < copied.length),
    first ≠ second → ∀ name ∈ TypeSubst.typeVars copied[first].1,
      name ∉ TypeSubst.typeVars copied[second].1)

theorem copyAnswers_valid (protectedNames : Finset String) (source : List (Atom × List Atom)) :
    Copies protectedNames source (copyAnswers protectedNames source) := by
  refine ⟨copyAnswers_length _ _, ?_, ?_⟩
  · intro index before after
    simpa only [copyAnswers, List.getElem_map, List.getElem_zipIdx, Nat.zero_add] using
      copyAnswer_valid protectedNames index source[index].1 source[index].2
  · intro first second firstBound secondBound different name member
    simp only [copyAnswers, List.getElem_map, List.getElem_zipIdx, Nat.zero_add] at member ⊢
    exact different_answers_disjoint protectedNames first second _ _ _ _ different name member

end Collection
namespace Destination

abbrev CollectionConfiguration (Context : Type) :=
  Configuration (CollectionWork Context) CollectedAnswer (CollectionCaller Context)

def copiedWork {Context : Type} (protectedNames : Finset String)
    (answers : List CollectedAnswer) (caller : CollectionCaller Context) : CollectionWork Context :=
  let copied := Collection.copyAnswers protectedNames
    (answers.map fun answer => (answer.value, answer.associated))
  ({caller.1 with
      goals := Goal.equate (.expression (copied.map Prod.fst)) caller.2.1 :: caller.1.goals},
    caller.2.2.1, caller.2.2.2)

theorem copiedResume_served {Context : Type} (protectedNames : Finset String)
    (answers : List CollectedAnswer) (caller : CollectionCaller Context)
    (ready : ∀ answer ∈ answers, answer.associated = []) :
    copiedResume protectedNames answers caller = some (copiedWork protectedNames answers caller) := by
  have allReady : answers.all (fun answer => answer.associated.isEmpty) = true := by
    apply List.all_eq_true.mpr
    intro answer present
    simp [ready answer present]
  simp only [copiedResume, allReady, ↓reduceIte, copiedWork]

/-- A successful local return discovers the terminal goal boundary, keeps the
actual reached cursor, and earns a source solution for its recorded equations. -/
theorem value_return_origin {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (cursor reached : Cursor Context) (value : Atom) (bindings : Equations)
    (returned : (machine policy program).step cursor = some (.finish (.value value bindings, reached))) :
    reached = cursor ∧ cursor.control.goals = [] ∧ bindings = cursor.control.bindings ∧
      ∃ environment, resolve bindings = some environment ∧ Solves environment bindings ∧
        value = read environment cursor.control.destination := by
  have atEnd := value_return_has_empty_goals policy program cursor reached value bindings returned
  simp only [machine, atEnd] at returned
  cases found : resolve cursor.control.bindings with
  | none => simp [found] at returned
  | some environment =>
    simp only [found, Option.some.injEq, Transition.finish.injEq, Prod.mk.injEq,
      Result.value.injEq] at returned
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := returned
    exact ⟨rfl, atEnd, rfl, environment, found, resolve_sound found, rfl⟩

/-- Reflection of the executed collection operation recovers the selected
source occurrence, its exact terminal cursor and the complete appended row.
There is no supplied decomposition of the original frontier. -/
theorem collectReturned_origin {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (before after : CollectionConfiguration Context)
    (collected : collectReturned? policy program before = some after) :
    ∃ scope parents control context occurrences pending value bindings environment,
      before.scopes = scope :: parents ∧
      scope.frontier = (control, context, occurrences) :: pending ∧
      control.goals = [] ∧ resolve bindings = some environment ∧ Solves environment bindings ∧
      bindings = control.bindings ∧ value = read environment control.destination ∧
      after = ⟨before.world,
        Scope.record scope pending ⟨value, bindings, occurrences, []⟩ :: parents⟩ := by
  cases scopes : before.scopes with
  | nil => simp [collectReturned?, scopes] at collected
  | cons scope parents =>
    cases frontier : scope.frontier with
    | nil => simp [collectReturned?, scopes, frontier] at collected
    | cons work pending =>
      rcases work with ⟨control, context, occurrences⟩
      simp only [collectReturned?, scopes, frontier] at collected
      cases stepped : (machine policy program).step ⟨before.world, control, context⟩ with
      | none => simp [stepped] at collected
      | some transition =>
        cases transition with
        | silent next | publish events next | fail events | call request next =>
          simp [stepped] at collected
        | finish result =>
          rcases result with ⟨result, reached⟩
          cases result with
          | noValue bindings => simp [stepped] at collected
          | value value bindings =>
            obtain ⟨rfl, ended, bindingEq, environment, resolved, model, readout⟩ :=
              value_return_origin policy program _ reached value bindings stepped
            simp only [stepped, Option.some.injEq] at collected
            exact ⟨scope, parents, control, context, occurrences, pending, value, bindings,
              environment, rfl, frontier, ended, resolved, model, bindingEq, readout, collected.symm⟩

/-- Constructed completion of the last source return. The actual appended rows
are copied before caller work is installed, and the independent copy judgment
is earned for that complete ordered list. -/
theorem last_return_constructs_copied_caller {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (protectedNames : Finset String)
    (cursor reached : Cursor Context) (scope parent : CollectionScope Context)
    (parents : List (CollectionScope Context)) (occurrences : List Nat)
    (caller : CollectionCaller Context) (value : Atom) (bindings : Equations)
    (frontier : scope.frontier = [(cursor.control, cursor.context, occurrences)])
    (saved : scope.caller = some caller)
    (ready : ∀ answer ∈ scope.collected, answer.associated = [])
    (returned : (machine policy program).step cursor = some (.finish (.value value bindings, reached))) :
    let answers := scope.collected ++ [⟨value, bindings, occurrences, []⟩]
    let work := copiedWork protectedNames answers caller
    collectAndResume? policy program protectedNames ⟨cursor.world, scope :: parent :: parents⟩ =
      some ⟨reached.world, {parent with frontier := work :: parent.frontier} :: parents⟩ ∧
    Collection.Copies protectedNames (answers.map fun answer => (answer.value, answer.associated))
      (Collection.copyAnswers protectedNames (answers.map fun answer => (answer.value, answer.associated))) ∧
    work.1.bindings = caller.1.bindings ∧ work.2 = caller.2.2 := by
  have sameReached := (value_return_origin policy program cursor reached value bindings returned).1
  subst reached
  have allReady : ∀ answer ∈ scope.collected ++ [⟨value, bindings, occurrences, []⟩],
      answer.associated = [] := by
    intro answer present
    rcases List.mem_append.mp present with old | new
    · exact ready answer old
    · cases List.mem_singleton.mp new
      rfl
  refine ⟨last_return_copies_before_caller policy program protectedNames cursor.world scope parent
    parents cursor.control cursor.context occurrences caller value bindings frontier saved returned _
    (copiedResume_served protectedNames _ caller allReady), Collection.copyAnswers_valid _ _, rfl, rfl⟩

/-- An arbitrary completed child run supplies its own terminal cut. Effects
performed before that cut are already in `reached.world`; the collector neither
replays the prefix nor restores the entry world. -/
theorem completed_child_terminal_cut {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (fuel : Nat) (source reached : Cursor Context)
    (events : List Empty) (value : Atom) (bindings : Equations)
    (ran : (machine policy program).run fuel source = (events, .finished (.value value bindings, reached))) :
    ∃ count < fuel,
      (machine policy program).run count source = ([], .exhausted reached) ∧
      (machine policy program).step reached = some (.finish (.value value bindings, reached)) := by
  obtain ⟨count, bound, saved, earlier, final, earlierRun, boundary, _events⟩ :=
    (machine policy program).run_boundary_prefix ran (by intro saved; simp)
  have terminal := ((machine policy program).run_one_finished_iff saved final _).mp boundary
  obtain ⟨rfl, _rest⟩ := value_return_origin policy program saved reached value bindings terminal.2
  have empty : earlier = [] := List.eq_nil_iff_forall_not_mem.mpr (fun impossible _ => nomatch impossible)
  exact ⟨count, bound, by simpa only [empty] using earlierRun, terminal.2⟩

end Destination
end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS


set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Collection
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement

private theorem copied_tuple_name (protectedNames : Finset String) (occurrence : Nat)
    (value : Atom) (associated : List Atom) (name : String)
    (member : name ∈ Destination.ClauseChoice.names
      ((copyAnswer protectedNames occurrence value associated).1 ::
        (copyAnswer protectedNames occurrence value associated).2)) :
    ∃ original, copyName protectedNames occurrence value associated original = name := by
  rw [copyAnswer_tuple] at member
  obtain ⟨atom, present, occurs⟩ := List.mem_flatMap.mp member
  obtain ⟨old, _present, rfl⟩ := List.mem_map.mp present
  rw [ScopeObservation.typeVars_renameTypeVars] at occurs
  obtain ⟨original, _occurs, same⟩ := List.mem_map.mp occurs
  exact ⟨original, same⟩

/-- Different occurrences separate the entire payload and associated-syntax
packet, including variables occurring only in delayed syntax. -/
theorem different_answer_tuples_disjoint (protectedNames : Finset String) (first second : Nat)
    (firstValue secondValue : Atom) (firstAssociated secondAssociated : List Atom)
    (different : first ≠ second) (name : String)
    (member : name ∈ Destination.ClauseChoice.names
      ((copyAnswer protectedNames first firstValue firstAssociated).1 ::
        (copyAnswer protectedNames first firstValue firstAssociated).2)) :
    name ∉ Destination.ClauseChoice.names
      ((copyAnswer protectedNames second secondValue secondAssociated).1 ::
        (copyAnswer protectedNames second secondValue secondAssociated).2) := by
  intro other
  obtain ⟨original, same⟩ := copied_tuple_name protectedNames first firstValue firstAssociated name member
  obtain ⟨next, also⟩ := copied_tuple_name protectedNames second secondValue secondAssociated name other
  exact Destination.ClauseChoice.distinct_occurrences (allocation protectedNames) first second _ _
    original next different (same.trans also.symm)

theorem copyAnswers_whole_tuples_disjoint (protectedNames : Finset String)
    (source : List (Atom × List Atom))
    (first second : Nat) (firstBound : first < (copyAnswers protectedNames source).length)
    (secondBound : second < (copyAnswers protectedNames source).length) (different : first ≠ second)
    (name : String)
    (member : name ∈ Destination.ClauseChoice.names
      ((copyAnswers protectedNames source)[first].1 :: (copyAnswers protectedNames source)[first].2)) :
    name ∉ Destination.ClauseChoice.names
      ((copyAnswers protectedNames source)[second].1 :: (copyAnswers protectedNames source)[second].2) := by
  simp only [copyAnswers, List.getElem_map, List.getElem_zipIdx, Nat.zero_add] at member ⊢
  exact different_answer_tuples_disjoint protectedNames first second _ _ _ _ different name member

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Collection


set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Install only the reached active child. Its older alternatives, collection
rows and caller delimiter remain in the existing scope carrier. -/
def retainChild {Context : Type} (scope : CollectionScope Context)
    (pending : List (CollectionWork Context)) (occurrences : List Nat)
    (reached : Cursor Context) : CollectionScope Context :=
  {scope with frontier := (reached.control, reached.context, occurrences) :: pending}

/-- Completed source execution finds its actual terminal cut and closes the
scope by computing fresh copies. The old world is never used after the child
has reached its terminal cursor. This local completion handles empty associated
work; nonempty associated work remains saved by `collectAndResume?`. -/
theorem completed_child_constructs_caller {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (protectedNames : Finset String)
    (fuel : Nat) (source reached : Cursor Context) (events : List Empty)
    (scope parent : CollectionScope Context) (parents : List (CollectionScope Context))
    (occurrences : List Nat) (caller : CollectionCaller Context)
    (value : Atom) (bindings : Equations)
    (saved : scope.caller = some caller)
    (ready : ∀ answer ∈ scope.collected, answer.associated = [])
    (ran : (machine policy program).run fuel source =
      (events, .finished (.value value bindings, reached))) :
    let answers := scope.collected ++ [⟨value, bindings, occurrences, []⟩]
    let work := copiedWork protectedNames answers caller
    ∃ count < fuel,
      (machine policy program).run count source = ([], .exhausted reached) ∧
      collectAndResume? policy program protectedNames
        ⟨reached.world, retainChild scope [] occurrences reached :: parent :: parents⟩ =
        some ⟨reached.world, {parent with frontier := work :: parent.frontier} :: parents⟩ ∧
      Collection.Copies protectedNames (answers.map fun answer => (answer.value, answer.associated))
        (Collection.copyAnswers protectedNames (answers.map fun answer => (answer.value, answer.associated))) ∧
      work.1.bindings = caller.1.bindings ∧ work.2 = caller.2.2 := by
  obtain ⟨count, bound, earlier, returned⟩ :=
    completed_child_terminal_cut policy program fuel source reached events value bindings ran
  exact ⟨count, bound, earlier,
    last_return_constructs_copied_caller policy program protectedNames reached reached
      (retainChild scope [] occurrences reached) parent parents occurrences caller value bindings
      rfl saved ready returned⟩

/-- A pause is a saved child cursor, not a partial collection result. The same
world, complete prior rows and caller delimiter are carried to resumption. -/
theorem paused_child_retains_collection {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (first second : Nat) (source retained : Cursor Context)
    (events : List Empty) (scope : CollectionScope Context)
    (pending : List (CollectionWork Context)) (occurrences : List Nat)
    (paused : (machine policy program).run first source = (events, .exhausted retained)) :
    (machine policy program).run (first + second) source =
      (events ++ ((machine policy program).run second retained).1,
        ((machine policy program).run second retained).2) ∧
    (retainChild scope pending occurrences retained).collected = scope.collected ∧
    (retainChild scope pending occurrences retained).caller = scope.caller ∧
    (retainChild scope pending occurrences retained).frontier.tail = pending :=
  ⟨resume policy program first second source retained events paused, rfl, rfl, rfl⟩

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.CollectionReturnControls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.Logic.LP

private def program : SpaceSemantics.Program := {equations := [], declarations := []}
private def startWorld : World := ⟨Effects.empty, [], []⟩
private def childControl : Control :=
  {bindings := [(.var "caller", .symbol "A")]
   goals := [.invoke "println!" [.symbol "before-pause"] (Effects.boolean true)]
   destination := .var "x"}
private def child : Cursor String := ⟨startWorld, childControl, "child"⟩
private def reached : Cursor String :=
  ⟨{startWorld with output := [.symbol "before-pause"]},
    {childControl with goals := [], bindings := childControl.bindings ++
      [(Effects.boolean true, Effects.boolean true)]}, "child"⟩
private def second : CollectionWork String := ({childControl with goals := []}, "second-child", [9, 1])
private def callerControl : Control :=
  {bindings := [(.var "caller", .symbol "A")]
   goals := [.invoke "==" [.var "a", .var "b"] (.var "out")]
   destination := .var "out"
   reserved := {"older"}}
private def caller : CollectionCaller String :=
  (callerControl, .expression [.var "a", .var "b"], "caller", [4])
private def sibling : CollectionWork String := (callerControl, "older-sibling", [3])
private def parent : CollectionScope String := ⟨[sibling], [], none⟩
private def childScope : CollectionScope String :=
  ⟨[(reached.control, reached.context, [9, 0]), second], [], some caller⟩
private def protect : Finset String := callerControl.support ∪ {"a", "b", "x"}
private def firstCollected := collectAndResume? .relational program protect
  ⟨reached.world, [childScope, parent]⟩
private def completed := firstCollected.bind (collectAndResume? .relational program protect)
private def callerCursor : Option (Cursor String) := do
  let configuration ← completed
  let scope ← configuration.scopes.head?
  let work ← scope.frontier.head?
  pure ⟨configuration.world, work.1, work.2.1⟩
private def comparison : Option (List Atom) := do
  let cursor ← callerCursor
  match ((machine .relational program).run 2 cursor).2 with
  | .suspended (.invoke "==" arguments _) reached =>
      match StdLib.apply reached.world.state "==" arguments with
      | .ok (_, values) => some values
      | .error _ => none
  | _ => none

/-- The effect comes from the actual primitive branch before a scheduler cut.
The remaining equate/terminal work is saved, not rerun from child entry. -/
theorem effect_then_saved_terminal :
    (machine .relational program).run 2 child = ([], .exhausted reached) := by
  simp only [Machine.run, machine, resolve, equations, read, refine, List.map_append, List.map_cons,
    List.map_nil, encode_decode, replace, Effects.boolean, child, startWorld, childControl, encode, unifyTotal,
    Term.occursIn, Bool.false_eq_true, ↓reduceIte, Subst.applyEqs, Subst.id, Subst.applyTerm_const, decode,
    List.nil_append, List.cons_append, Subst.applyTerm, Option.isSome_some, reached]

theorem pause_after_effect_keeps_work :
    (machine .relational program).run 1 child =
      ([], .exhausted ⟨reached.world,
        {childControl with goals := [.equate (Effects.boolean true) (Effects.boolean true)]}, "child"⟩) := by
  simp only [Machine.run, machine, resolve, equations, read, refine, List.map_append, List.map_cons,
    List.map_nil, encode_decode, replace, Effects.boolean, child, startWorld, childControl, encode, unifyTotal,
    Term.occursIn, Bool.false_eq_true, ↓reduceIte, Subst.applyEqs, Subst.id, Subst.applyTerm_const, decode,
    List.nil_append, reached, List.cons_append]

theorem resumed_prefix_is_same :
    (machine .relational program).run 1
      ⟨reached.world, {childControl with goals := [.equate (Effects.boolean true) (Effects.boolean true)]}, "child"⟩ =
      ([], .exhausted reached) := by
  simp only [Machine.run, machine, resolve, equations, read, refine, List.map_append, List.map_cons,
    List.map_nil, encode_decode, replace, Effects.boolean, reached, startWorld, childControl, List.cons_append,
    List.nil_append, encode, unifyTotal, Term.occursIn, Bool.false_eq_true, ↓reduceIte, Subst.applyEqs, Subst.applyTerm,
    Subst.id, Option.isSome_some]

#guard firstCollected.map (fun configuration =>
  (configuration.scopes.length, configuration.scopes.head?.map (fun scope =>
    (scope.frontier.length, scope.collected.map CollectedAnswer.occurrences)))) ==
      some (2, some (1, [[9, 0]]))
#guard completed.map (fun configuration =>
  (configuration.world.output, configuration.scopes.length,
    configuration.scopes.head?.map (fun scope => scope.frontier.map Prod.snd))) ==
      some ([.symbol "before-pause"], 1, some [("caller", [4]), ("older-sibling", [3])])
#guard callerCursor.map (fun cursor => cursor.control.bindings) == some callerControl.bindings
#guard comparison == some [Effects.boolean false]

/-- The computed source return path yields the observed ground distinction,
not merely different pretty-printed variable names. -/
theorem actual_two_returns_ground_false : comparison = some [Effects.boolean false] := by
  have callerLength : "caller".length = 6 := rfl
  have outLength : "out".length = 3 := rfl
  have aLength : "a".length = 1 := rfl
  have olderLength : "older".length = 5 := rfl
  have bLength : "b".length = 1 := rfl
  have xLength : "x".length = 1 := rfl
  have firstName : String.replicate 7 '#' = "#######" := rfl
  have secondName : String.replicate 9 '#' = "#########" := rfl
  simp only [comparison, callerCursor, completed, firstCollected, collectAndResume?, collectReturned?,
    childScope, reached, startWorld, childControl, Effects.boolean, List.cons_append, List.nil_append, second, caller,
    callerControl, machine, resolve, equations, read, refine, List.map_append, List.map_cons, List.map_nil,
    encode_decode, encode, unifyTotal, Term.occursIn, Bool.false_eq_true, ↓reduceIte, Subst.applyEqs, Subst.applyTerm,
    Subst.id, Subst.applyTerm_var, Subst.comp, Subst.single, String.reduceEq, decode, Scope.record, parent, sibling,
    Scope.finish?, copiedResume, List.all_eq_true, List.isEmpty_iff, Collection.copyAnswers, Collection.copyAnswer,
    Collection.copyName, Collection.allocation, protect, Control.support, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, Goal.atoms, List.foldl_cons, Term.freeVars, Finset.empty_union, Finset.singleton_union,
    Finset.union_empty, Finset.insert_union, Finset.mem_insert, Finset.mem_singleton, or_true, Finset.insert_eq_of_mem,
    List.foldl_nil, Finset.union_insert, or_false, or_self, List.map_map, Prod.mk.eta, Option.pure_def,
    Option.bind_eq_bind, Option.bind_some, Option.getD_none, List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
    forall_eq, and_self, List.zipIdx_cons, zero_add, Nat.reduceAdd, List.zipIdx_nil, Function.comp_apply,
    HE.Spec.Type.RuntimeRefinement.renameTypeVars, ClauseChoice.rename, freshName, Finset.union_idempotent,
    Finset.sup_insert, callerLength, outLength, aLength, olderLength, bLength, Finset.sup_singleton, xLength, max_self,
    Nat.one_le_ofNat, sup_of_le_left, sup_of_le_right, Nat.reduceLeDiff, Nat.pair, ClauseChoice.names,
    HE.Spec.Type.Presentation.TypeSubst.typeVars, List.idxOf_cons_self, lt_self_iff_false, mul_zero, add_zero,
    ↓Char.isValue, firstName, not_lt_zero, mul_one, secondName, Option.getD_some, List.head?_cons, Machine.run,
    ExceptT.stM_eq, List.length_cons, List.length_nil, id_eq, Fin.getElem_fin, ↓reduceDIte, finPairsToList,
    List.finRange_succ, Fin.isValue, List.finRange_zero, Fin.succ_zero_eq_one, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
    List.getElem_cons_zero, Nat.mod_succ, List.getElem_cons_succ, Option.isSome_some, List.cons.injEq,
    List.cons_ne_self, and_false, imp_self, implies_true, StdLib.structural_equality, Option.some.injEq,
    Atom.grounded.injEq, OSLFCore.GroundedValue.bool.injEq, beq_eq_false_iff_ne, ne_eq, Atom.var.injEq,
    not_false_eq_true]

theorem first_return_does_not_publish_aggregate :
    firstCollected.map (fun configuration => configuration.scopes.length) = some 2 := by
  simp only [firstCollected, collectAndResume?, collectReturned?, childScope, reached, startWorld, childControl,
    Effects.boolean, List.cons_append, List.nil_append, second, caller, callerControl, machine, resolve, equations,
    read, refine, List.map_append, List.map_cons, List.map_nil, encode_decode, encode, unifyTotal, Term.occursIn,
    Bool.false_eq_true, ↓reduceIte, Subst.applyEqs, Subst.applyTerm, Subst.id, Subst.applyTerm_var, Subst.comp,
    Subst.single, String.reduceEq, decode, Scope.record, parent, sibling, Scope.finish?, copiedResume, List.all_eq_true,
    List.isEmpty_iff, Collection.copyAnswers, Collection.copyAnswer, Collection.copyName, Collection.allocation,
    protect, Control.support, List.flatMap_cons, List.flatMap_nil, List.append_nil, Goal.atoms, List.foldl_cons,
    Term.freeVars, Finset.empty_union, Finset.singleton_union, Finset.union_empty, Finset.insert_union,
    Finset.mem_insert, Finset.mem_singleton, or_true, Finset.insert_eq_of_mem, List.foldl_nil, Finset.union_insert,
    or_false, or_self, List.map_map, Prod.mk.eta, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
    Option.getD_none, Option.map_some, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]

private def blocked : CollectionConfiguration String :=
  ⟨reached.world, [{childScope with
    frontier := [(reached.control, reached.context, [9, 0])]
    collected := [⟨.var "old", [], [8], [.expression [.symbol "delay", .var "old"]]⟩]}, parent]⟩
private def blockedReturn := collectAndResume? .relational program protect blocked
#guard blockedReturn.map (fun configuration => configuration.scopes.head?.map (fun scope =>
  (scope.frontier.length, scope.collected.length, scope.collected.map CollectedAnswer.associated))) ==
    some (some (0, 2, [[.expression [.symbol "delay", .var "old"]], []]))
#guard blockedReturn.map (fun configuration => configuration.world.output) ==
  some [.symbol "before-pause"]

private def refusedControl : Control :=
  {childControl with goals := [.equate (.symbol "B") (.var "caller")]}
#guard (collectReturned? .relational program
  ⟨reached.world, [{childScope with frontier := [(refusedControl, "rejected", [7])]}, parent]⟩).isNone
#guard (collectReturned? .relational program
  ⟨startWorld, [{childScope with frontier := [(childControl, "pending-effect", [7])]}, parent]⟩).isNone

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.CollectionReturnControls


/-!
## Destination collection entry and current-scope copying

These finite source operations select actual goals at the existing retained
scope boundary. They keep reached equations, occurrence paths, caller contexts
and the shared world. Fresh clause and copy names avoid the current finite
source inventory, including intermediate caller destinations. Loading opaque
contexts and future world cells, associated continuations and the whole default
dispatcher remain separate obligations. No second scope or branch machine is
introduced here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Names in actual retained source operands. This finite inventory does not
claim to decode opaque contexts or future world cells. -/
def operandSupport (atoms : List Atom) : Finset String :=
  atoms.foldr (fun atom names => (encode atom).freeVars ∪ names) ∅

def CollectedAnswer.support (answer : CollectedAnswer) : Finset String :=
  operandSupport (answer.value :: answer.bindings.flatMap (fun pair => [pair.1, pair.2]) ++
    answer.associated)

def CollectionScope.support {Context : Type} (scope : CollectionScope Context) : Finset String :=
  scope.frontier.foldr (fun work names => work.1.support ∪ names) ∅ ∪
  scope.collected.foldr (fun answer names => answer.support ∪ names) ∅ ∪
  (scope.caller.map fun caller => caller.1.support ∪ (encode caller.2.1).freeVars).getD ∅

def collectionSupport {Context : Type} (configuration : CollectionConfiguration Context) : Finset String :=
  configuration.scopes.foldr (fun scope names => CollectionScope.support scope ∪ names) ∅

theorem scope_work_support {Context : Type} (scope : CollectionScope Context)
    (work : CollectionWork Context) (member : work ∈ scope.frontier) :
    work.1.support ⊆ CollectionScope.support scope := by
  have contained : work.1.support ⊆
      scope.frontier.foldr (fun work names => work.1.support ∪ names) ∅ := by
    generalize scope.frontier = works at member ⊢
    induction works with
    | nil => cases member
    | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact Finset.subset_union_left
      · exact Finset.Subset.trans (ih member) Finset.subset_union_right
  exact Finset.Subset.trans contained
    (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left)

theorem scope_support {Context : Type} (configuration : CollectionConfiguration Context)
    (scope : CollectionScope Context) (member : scope ∈ configuration.scopes) :
    CollectionScope.support scope ⊆ collectionSupport configuration := by
  unfold collectionSupport
  generalize configuration.scopes = scopes at member ⊢
  induction scopes with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Finset.subset_union_left
    · exact Finset.Subset.trans (ih member) Finset.subset_union_right

theorem scope_caller_support {Context : Type} (scope : CollectionScope Context)
    (caller : CollectionCaller Context) (saved : scope.caller = some caller) :
    caller.1.support ∪ (encode caller.2.1).freeVars ⊆ CollectionScope.support scope := by
  unfold CollectionScope.support
  rw [saved]
  exact Finset.subset_union_right

def childName (control : Control) (boundary : Finset String) : String :=
  freshName { control with reserved := control.reserved ∪ boundary } 0

/-- Extend the source-name boundary without replacing reached equations or
goals. This is used by the existing clause allocator. -/
def protectControl (control : Control) (boundary : Finset String) : Control :=
  {control with reserved := control.reserved ∪ boundary}

theorem protectControl_support (control : Control) (boundary : Finset String) :
    (protectControl control boundary).support = control.support ∪ boundary := by
  simp only [protectControl, Control.support]
  ac_rfl

/-- Child evaluation has its own destination; the parent continuation is not
put among the child's goals. The old equations remain actual source constraints. -/
def collapseChild (control : Control) (boundary : Finset String) (expression : Atom) : Control :=
  { bindings := control.bindings
    goals := [.evaluate expression (.var (childName control boundary))]
    destination := .var (childName control boundary)
    reserved := control.support ∪ boundary }

theorem childName_fresh (control : Control) (boundary : Finset String) :
    childName control boundary ∉ control.support ∪ boundary := by
  intro member
  apply freshName_not_mem {control with reserved := control.reserved ∪ boundary} 0
  rcases Finset.mem_union.mp member with localName | outside
  · rcases Finset.mem_union.mp localName with reserved | operand
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ reserved)
    · exact Finset.mem_union_right _ operand
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ outside)

/-- Every older active source control is included in the allocation boundary,
including its raw equations, pending goals, destination and reserved names. -/
theorem childName_avoids_retained_work {Context : Type} (configuration : CollectionConfiguration Context)
    (control : Control) (scope : CollectionScope Context) (work : CollectionWork Context)
    (present : scope ∈ configuration.scopes) (active : work ∈ scope.frontier) :
    childName control (collectionSupport configuration) ∉ work.1.support := by
  intro member
  exact childName_fresh control _ (Finset.mem_union_right _
    (scope_support configuration scope present (scope_work_support scope work active member)))

theorem collapseChild_keeps_constraints (control : Control) (boundary : Finset String)
    (expression : Atom) : (collapseChild control boundary expression).bindings = control.bindings := rfl

theorem collapseChild_saves_caller_names (control : Control) (boundary : Finset String)
    (expression : Atom) :
    control.support ∪ boundary ⊆ (collapseChild control boundary expression).support := by
  intro name member
  exact Finset.mem_union_left _ member

theorem collapseChild_wellDelimited (control : Control) (boundary : Finset String)
    (expression : Atom) : WellDelimited (collapseChild control boundary expression).goals := by
  simp [collapseChild, WellDelimited]

/-- Dispatch a literal source collapse at the retained scope boundary. Other
source work remains unserved by this operation; no branch result is supplied. -/
def enterCollapse? {Context : Type} (configuration : CollectionConfiguration Context) :
    Option (CollectionConfiguration Context) :=
  match configuration.scopes with
  | scope :: parents =>
    match scope.frontier with
    | (control, context, origins) :: pending =>
      match control.goals with
      | .evaluate (.expression [.symbol "collapse", expression]) destination :: older =>
        some (Scope.enter configuration.world scope pending parents
          (collapseChild control (collectionSupport configuration) expression, context, origins)
          ({control with goals := older}, destination, context, origins))
      | _ => none
    | [] => none
  | [] => none

theorem enterCollapse_constructs {Context : Type} (world : World)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (control : Control) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)) (expression destination : Atom) (older : List Goal)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (head : control.goals = .evaluate (.expression [.symbol "collapse", expression]) destination :: older) :
    enterCollapse? ⟨world, scope :: parents⟩ =
      some (Scope.enter world scope pending parents
        (collapseChild control (collectionSupport ⟨world, scope :: parents⟩) expression, context, origins)
        ({control with goals := older}, destination, context, origins)) := by
  simp only [enterCollapse?, frontier, head]

/-- Reflection discovers the actual selected source syntax and saved suffix.
Freshness is earned from the complete finite scope inventory. -/
theorem enterCollapse_origin {Context : Type} (before after : CollectionConfiguration Context)
    (entered : enterCollapse? before = some after) :
    ∃ scope parents control context origins pending expression destination older,
      before.scopes = scope :: parents ∧
      scope.frontier = (control, context, origins) :: pending ∧
      control.goals = .evaluate (.expression [.symbol "collapse", expression]) destination :: older ∧
      childName control (collectionSupport before) ∉ control.support ∪ collectionSupport before ∧
      after = Scope.enter before.world scope pending parents
        (collapseChild control (collectionSupport before) expression, context, origins)
        ({control with goals := older}, destination, context, origins) := by
  unfold enterCollapse? at entered
  split at entered
  · rename_i scope parents scopes
    split at entered
    · rename_i control context origins pending frontier
      split at entered
      · rename_i expression destination older head
        exact ⟨scope, parents, control, context, origins, pending, expression, destination, older,
          scopes, frontier, head, childName_fresh control _, (Option.some.inj entered).symm⟩
      · contradiction
    · contradiction
  · contradiction

theorem enterCollapse_preserves_world {Context : Type} (before after : CollectionConfiguration Context)
    (entered : enterCollapse? before = some after) : after.world = before.world := by
  obtain ⟨scope, parents, control, context, origins, pending, expression, destination, older,
    _scopes, _frontier, _head, _fresh, rfl⟩ := enterCollapse_origin before after entered
  rfl

/-- A source alternative retains the reached constraints and caller suffix.
Its occurrence index is retained even when two expressions are identical. -/
def superposeWork {Context : Type} (control : Control) (context : Context) (origins : List Nat)
    (alternatives : List Atom) (destination : Atom) (older : List Goal) : List (CollectionWork Context) :=
  alternatives.zipIdx.map fun (expression, occurrence) =>
    ({control with goals := .evaluate expression destination :: older}, context, origins ++ [occurrence])

def enterSuperpose? {Context : Type} (configuration : CollectionConfiguration Context) :
    Option (CollectionConfiguration Context) :=
  match configuration.scopes with
  | scope :: parents =>
    match scope.frontier with
    | (control, context, origins) :: pending =>
      match control.goals with
      | .evaluate (.expression [.symbol "superpose", .expression alternatives]) destination :: older =>
        some { configuration with scopes :=
          {scope with frontier := superposeWork control context origins alternatives destination older ++ pending} :: parents }
      | _ => none
    | [] => none
  | [] => none

theorem superposeWork_length {Context : Type} (control : Control) (context : Context)
    (origins : List Nat) (alternatives : List Atom) (destination : Atom) (older : List Goal) :
    (superposeWork control context origins alternatives destination older).length = alternatives.length := by
  simp [superposeWork]

theorem superposeWork_index {Context : Type} (control : Control) (context : Context)
    (origins : List Nat) (alternatives : List Atom) (destination : Atom) (older : List Goal)
    (index : Nat) (bound : index < alternatives.length) :
    (superposeWork control context origins alternatives destination older)[index]'(by
      simpa only [superposeWork_length] using bound) =
      ({control with goals := .evaluate alternatives[index] destination :: older}, context, origins ++ [index]) := by
  simp [superposeWork]

theorem superposeWork_wellDelimited {Context : Type} (control : Control) (context : Context)
    (origins : List Nat) (alternatives : List Atom) (destination : Atom) (older : List Goal)
    (valid : WellDelimited older) (work : CollectionWork Context)
    (member : work ∈ superposeWork control context origins alternatives destination older) :
    WellDelimited work.1.goals := by
  obtain ⟨⟨expression, occurrence⟩, _present, rfl⟩ := List.mem_map.mp member
  exact valid

theorem enterSuperpose_constructs {Context : Type} (world : World)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (control : Control) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)) (alternatives : List Atom)
    (destination : Atom) (older : List Goal)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (head : control.goals = .evaluate (.expression [.symbol "superpose", .expression alternatives]) destination :: older) :
    enterSuperpose? ⟨world, scope :: parents⟩ =
      some ⟨world, {scope with frontier := superposeWork control context origins alternatives destination older ++ pending} :: parents⟩ := by
  simp only [enterSuperpose?, frontier, head]

/-- A predicate body has its own cut delimiter. The caller's delimiter is
restored before its older goals resume; neither marker changes bindings. -/
def predicateEntry (retained : Nat) (selected : Control) : Control :=
  {selected with cutBoundary := retained,goals := match selected.goals with
    | [] => [.restoreCommit selected.cutBoundary]
    | body :: older => body :: .restoreCommit selected.cutBoundary :: older}

theorem predicateEntry_injective (retained : Nat) : Function.Injective (predicateEntry retained) := by
  intro first second same
  cases first with
  | mk firstBindings firstGoals firstDestination firstReserved firstBoundary =>
    cases second with
    | mk secondBindings secondGoals secondDestination secondReserved secondBoundary =>
      simp only [predicateEntry,Control.mk.injEq] at same
      obtain ⟨bindings,goals,destination,reserved,boundary⟩ := same
      subst secondBindings
      subst secondDestination
      subst secondReserved
      cases firstGoals <;> cases secondGoals <;> simp_all

theorem predicateEntry_wellDelimited (retained : Nat) (selected : Control)
    (valid : WellDelimited selected.goals) : WellDelimited (predicateEntry retained selected).goals := by
  cases goals : selected.goals with
  | nil => simp [predicateEntry,goals,WellDelimited]
  | cons goal older =>
      cases goal <;> simp_all [predicateEntry,WellDelimited]
      all_goals omega

/-- Install equation alternatives without erasing their physical source index.
The single allocation boundary includes all retained scopes. -/
def equationWork {Context : Type} (program : SpaceSemantics.Program)
    (control : Control) (boundary : Finset String) (context : Context) (origins : List Nat)
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal) (retained : Nat) :
    List (CollectionWork Context) :=
  (ClauseChoice.choices program (protectControl control boundary) head arguments destination older).map
    fun (occurrence, selected) => (predicateEntry retained selected, context, origins ++ [occurrence])

/-- Equation entry executes actual finite source selection under the reached
constraint environment. Native/primitive requests remain outside this operation. -/
def enterEquations? {Context : Type} (program : SpaceSemantics.Program)
    (configuration : CollectionConfiguration Context) : Option (CollectionConfiguration Context) :=
  match configuration.scopes with
  | scope :: parents =>
    match scope.frontier with
    | (control, context, origins) :: pending =>
      match control.goals with
      | .invoke head arguments destination :: older => do
        if Eval.ioHead head || StdLib.known head then none else do
          if !(program.equations.any (·.head == head)) then none else do
            let environment ← resolve control.bindings
            let children := equationWork program control (collectionSupport configuration) context origins
              head (arguments.map (read environment)) destination older pending.length
            pure {configuration with scopes := {scope with frontier := children ++ pending} :: parents}
      | _ => none
    | [] => none
  | [] => none

theorem enterSuperpose_origin {Context : Type} (before after : CollectionConfiguration Context)
    (entered : enterSuperpose? before = some after) :
    ∃ scope parents control context origins pending alternatives destination older,
      before.scopes = scope :: parents ∧
      scope.frontier = (control, context, origins) :: pending ∧
      control.goals = .evaluate (.expression [.symbol "superpose", .expression alternatives]) destination :: older ∧
      after = ⟨before.world,
        {scope with frontier := superposeWork control context origins alternatives destination older ++ pending} :: parents⟩ := by
  unfold enterSuperpose? at entered
  split at entered
  · rename_i scope parents scopes
    split at entered
    · rename_i control context origins pending frontier
      split at entered
      · rename_i alternatives destination older head
        exact ⟨scope, parents, control, context, origins, pending, alternatives, destination, older,
          scopes, frontier, head, (Option.some.inj entered).symm⟩
      · contradiction
    · contradiction
  · contradiction

theorem superposeWork_source_iff {Context : Type} (control : Control) (context : Context)
    (origins : List Nat) (alternatives : List Atom) (destination : Atom) (older : List Goal)
    (work : CollectionWork Context) :
    work ∈ superposeWork control context origins alternatives destination older ↔
      ∃ occurrence expression, alternatives[occurrence]? = some expression ∧
        work = ({control with goals := .evaluate expression destination :: older},
          context, origins ++ [occurrence]) := by
  simp only [superposeWork, List.mem_map]
  constructor
  · rintro ⟨⟨expression, occurrence⟩, present, rfl⟩
    exact ⟨occurrence, expression, List.mk_mem_zipIdx_iff_getElem?.mp present, rfl⟩
  · rintro ⟨occurrence, expression, present, rfl⟩
    refine ⟨(expression, occurrence), ?_, rfl⟩
    exact List.mk_mem_zipIdx_iff_getElem?.mpr present

theorem enterSuperpose_preserves_world {Context : Type} (before after : CollectionConfiguration Context)
    (entered : enterSuperpose? before = some after) : after.world = before.world := by
  obtain ⟨scope, parents, control, context, origins, pending, alternatives, destination, older,
    _scopes, _frontier, _head, rfl⟩ := enterSuperpose_origin before after entered
  rfl

/-- Every installed equation branch is justified by the independent common
solution judgment, with the exact fresh pattern/body and source occurrence. -/
theorem equationWork_source_iff {Context : Type} (program : SpaceSemantics.Program)
    (control : Control) (boundary : Finset String) (context : Context) (origins : List Nat)
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal) (retained : Nat)
    (work : CollectionWork Context) :
    work ∈ equationWork program control boundary context origins head arguments destination older retained ↔
      ∃ occurrence next equation, program.equations[occurrence]? = some equation ∧
        ClauseChoice.Selection program (protectControl control boundary) head arguments destination older
          occurrence (ClauseChoice.freshPattern (protectControl control boundary) occurrence equation)
          (ClauseChoice.freshBody (protectControl control boundary) occurrence equation) next ∧
        work = (predicateEntry retained next, context, origins ++ [occurrence]) := by
  simp only [equationWork, List.mem_map]
  constructor
  · rintro ⟨⟨occurrence, next⟩, present, rfl⟩
    obtain ⟨equation, row, selected⟩ := (ClauseChoice.choices_source_iff program
      (protectControl control boundary) head arguments destination older occurrence next).mp present
    exact ⟨occurrence, next, equation, row, selected, rfl⟩
  · rintro ⟨occurrence, next, equation, row, selected, rfl⟩
    exact ⟨(occurrence, next), (ClauseChoice.choices_source_iff program
      (protectControl control boundary) head arguments destination older occurrence next).mpr
        ⟨equation, row, selected⟩, rfl⟩

theorem enterEquations_constructs {Context : Type} (program : SpaceSemantics.Program)
    (world : World) (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (control : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (environment : Environment)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke head arguments destination :: older)
    (ordinary : (Eval.ioHead head || StdLib.known head) = false)
    (declared : program.equations.any (·.head == head) = true)
    (resolved : resolve control.bindings = some environment) :
    enterEquations? program ⟨world, scope :: parents⟩ =
      some ⟨world, {scope with frontier := (equationWork program control
        (collectionSupport ⟨world, scope :: parents⟩) context origins head
        (arguments.map (read environment)) destination older pending.length ++ pending)} :: parents⟩ := by
  simp only [enterEquations?, frontier, atCall, ordinary, Bool.false_eq_true, ↓reduceIte,
    declared, Bool.not_true, resolved, pure]
  rfl

theorem enterEquations_origin {Context : Type} (program : SpaceSemantics.Program)
    (before after : CollectionConfiguration Context)
    (entered : enterEquations? program before = some after) :
    ∃ scope parents control context origins pending head arguments destination older environment,
      before.scopes = scope :: parents ∧
      scope.frontier = (control, context, origins) :: pending ∧
      control.goals = .invoke head arguments destination :: older ∧
      (Eval.ioHead head || StdLib.known head) = false ∧
      program.equations.any (·.head == head) = true ∧
      resolve control.bindings = some environment ∧
      after = ⟨before.world, {scope with frontier := (equationWork program control
        (collectionSupport before) context origins head (arguments.map (read environment))
        destination older pending.length ++ pending)} :: parents⟩ := by
  unfold enterEquations? at entered
  split at entered
  · rename_i scope parents scopes
    split at entered
    · rename_i control context origins pending frontier
      split at entered
      · rename_i head arguments destination older atCall
        split at entered
        · contradiction
        · rename_i ordinary
          split at entered
          · contradiction
          · rename_i declared
            cases resolved : resolve control.bindings with
            | none => simp only [resolved] at entered; contradiction
            | some environment =>
              simp only [resolved, pure] at entered
              exact ⟨scope, parents, control, context, origins, pending, head, arguments, destination,
                older, environment, scopes, frontier, atCall, by simpa using ordinary,
                by simpa using declared, resolved, (Option.some.inj entered).symm⟩
      · contradiction
    · contradiction
  · contradiction

theorem equationWork_wellDelimited {Context : Type} (program : SpaceSemantics.Program)
    (control : Control) (boundary : Finset String) (context : Context) (origins : List Nat)
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal) (retained : Nat)
    (valid : WellDelimited older) (work : CollectionWork Context)
    (member : work ∈ equationWork program control boundary context origins head arguments destination older retained) :
    WellDelimited work.1.goals := by
  obtain ⟨occurrence, next, equation, row, selected, rfl⟩ :=
    (equationWork_source_iff program control boundary context origins head arguments destination older retained work).mp member
  apply predicateEntry_wellDelimited
  exact ClauseChoice.attempt_wellDelimited _ _ _ _ _ _ _ _
    ((ClauseChoice.selection_iff_attempt program _ head arguments destination older occurrence equation next row).mp selected) valid

/-- Reached equation entry uses the actual ordinary invocation request. The
additional allocation boundary changes no world, context or argument read. -/
theorem equationWork_invocation {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (cursor : Cursor Context) (boundary : Finset String) (origins : List Nat)
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal) (retained : Nat)
    (environment : Environment)
    (ordinary : (Eval.ioHead head || StdLib.known head) = false)
    (atCall : cursor.control.goals = .invoke head arguments destination :: older)
    (resolved : resolve cursor.control.bindings = some environment)
    (work : CollectionWork Context)
    (member : work ∈ equationWork program cursor.control boundary cursor.context origins head
      (arguments.map (read environment)) destination older retained) :
    (machine policy program).step cursor = some (.call
      (.invoke head (arguments.map (read environment)) destination) cursor) ∧
    work.2.1 = cursor.context ∧
    ∃ environment, resolve work.1.bindings = some environment := by
  obtain ⟨occurrence, next, equation, _row, selected, rfl⟩ :=
    (equationWork_source_iff program cursor.control boundary cursor.context origins head
      (arguments.map (read environment)) destination older retained work).mp member
  have notPrint : head ≠ "println!" := by
    intro same
    subst head
    simp [Eval.ioHead] at ordinary
  exact ⟨by simp [machine, atCall, resolved, notPrint], rfl,
    by simpa only [predicateEntry] using ClauseChoice.selected_resolves selected⟩

/-- Both source pattern and body use one earned fresh instance outside every
retained source name, not independent pointwise renamings. -/
theorem equationWork_fresh {Context : Type} (program : SpaceSemantics.Program)
    (control : Control) (boundary : Finset String) (context : Context) (origins : List Nat)
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal) (retained : Nat)
    (work : CollectionWork Context)
    (member : work ∈ equationWork program control boundary context origins head arguments destination older retained) :
    ∃ occurrence equation,
      program.equations[occurrence]? = some equation ∧
      ClauseChoice.FreshInstance (protectControl control boundary) equation
        (ClauseChoice.freshPattern (protectControl control boundary) occurrence equation)
        (ClauseChoice.freshBody (protectControl control boundary) occurrence equation) ∧
      (∀ name, ClauseChoice.rename (protectControl control boundary) occurrence
        (ClauseChoice.clauseAtoms equation) name ∉ control.support ∪ boundary) := by
  obtain ⟨occurrence, next, equation, row, _selected, _same⟩ :=
    (equationWork_source_iff program control boundary context origins head arguments destination older retained work).mp member
  refine ⟨occurrence, equation, row, ClauseChoice.fresh_clause_instance _ _ _, ?_⟩
  intro name
  rw [← protectControl_support]
  exact ClauseChoice.rename_fresh _ _ _ _

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination


set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- The copy boundary is computed from the currently retained source scopes,
including fresh intermediate destinations in nested callers. It still does
not decode opaque contexts or future world cells. -/
def collectAtCurrentScope? {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (configuration : CollectionConfiguration Context) : Option (CollectionConfiguration Context) :=
  collectAndResume? policy program (collectionSupport configuration) configuration

theorem current_copy_avoids_caller {Context : Type} (configuration : CollectionConfiguration Context)
    (scope : CollectionScope Context) (caller : CollectionCaller Context)
    (present : scope ∈ configuration.scopes) (saved : scope.caller = some caller)
    (occurrence : Nat) (value : Atom) (associated : List Atom) (name : String)
    (occurs : name ∈ Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst.typeVars
      (Collection.copyAnswer (collectionSupport configuration) occurrence value associated).1) :
    name ∉ caller.1.support ∪ (encode caller.2.1).freeVars := by
  intro captured
  exact Collection.copyAnswer_variables_fresh _ _ _ _ _ occurs
    (scope_support configuration scope present (scope_caller_support scope caller saved captured))

/-- The actual terminal return chooses the current inventory and constructs
the copied caller. No caller-supplied protected-name list is needed here. -/
theorem current_scope_terminal_constructs_caller {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (cursor : Cursor Context)
    (scope parent : CollectionScope Context) (parents : List (CollectionScope Context))
    (origins : List Nat) (caller : CollectionCaller Context) (value : Atom) (bindings : Equations)
    (frontier : scope.frontier = [(cursor.control, cursor.context, origins)])
    (saved : scope.caller = some caller)
    (ready : ∀ answer ∈ scope.collected, answer.associated = [])
    (returned : (machine policy program).step cursor = some (.finish (.value value bindings, cursor))) :
    let before : CollectionConfiguration Context := ⟨cursor.world, scope :: parent :: parents⟩
    let boundary := collectionSupport before
    let answers := scope.collected ++ [⟨value, bindings, origins, []⟩]
    let copied := copiedWork boundary answers caller
    collectAtCurrentScope? policy program before =
      some ⟨cursor.world, {parent with frontier := copied :: parent.frontier} :: parents⟩ ∧
    Collection.Copies boundary (answers.map fun answer => (answer.value, answer.associated))
      (Collection.copyAnswers boundary (answers.map fun answer => (answer.value, answer.associated))) ∧
    copied.1.bindings = caller.1.bindings ∧ copied.2 = caller.2.2 := by
  exact last_return_constructs_copied_caller policy program _ cursor cursor scope parent parents
    origins caller value bindings frontier saved ready returned

/-- Any actually completed selected branch supplies its terminal cut and its
own collected row. This applies after superpose or equation entry with the
remaining occurrence frontier intact; completion need not empty that frontier. -/
theorem selected_child_completed {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (fuel : Nat) (source reached : Cursor Context)
    (events : List Empty) (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (pending : List (CollectionWork Context)) (origins : List Nat) (value : Atom) (bindings : Equations)
    (ran : (machine policy program).run fuel source =
      (events, .finished (.value value bindings, reached))) :
    ∃ count < fuel,
      (machine policy program).run count source = ([], .exhausted reached) ∧
      collectReturned? policy program
        ⟨reached.world, retainChild scope pending origins reached :: parents⟩ =
        some ⟨reached.world, Scope.record scope pending ⟨value, bindings, origins, []⟩ :: parents⟩ ∧
      reached.control.goals = [] ∧ bindings = reached.control.bindings ∧
      ∃ environment, resolve bindings = some environment ∧ Solves environment bindings ∧
        value = read environment reached.control.destination := by
  obtain ⟨count, bound, earlier, returned⟩ :=
    completed_child_terminal_cut policy program fuel source reached events value bindings ran
  obtain ⟨_same, goals, records, actual⟩ :=
    value_return_origin policy program reached reached value bindings returned
  refine ⟨count, bound, earlier, ?_, goals, records, actual⟩
  exact collect_actual_terminal policy program reached.world
    (retainChild scope pending origins reached) parents reached.control reached.context origins
    pending value bindings rfl returned

/-- A superposed child that actually completes contributes its own indexed row
before the remaining children or older siblings can be selected. -/
theorem superpose_entry_completed_first {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (expression : Atom) (alternatives : List Atom) (destination : Atom) (older : List Goal)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (head : control.goals = .evaluate (.expression [.symbol "superpose", .expression (expression :: alternatives)]) destination :: older)
    (fuel : Nat) (reached : Cursor Context) (events : List Empty) (value : Atom) (bindings : Equations)
    (ran : (machine policy program).run fuel
      ⟨world, {control with goals := .evaluate expression destination :: older}, context⟩ =
        (events, .finished (.value value bindings, reached))) :
    let children := superposeWork control context origins (expression :: alternatives) destination older
    let enteredScope := {scope with frontier := children ++ pending}
    enterSuperpose? ⟨world, scope :: parents⟩ = some ⟨world, enteredScope :: parents⟩ ∧
    children.head? = some ({control with goals := .evaluate expression destination :: older}, context, origins ++ [0]) ∧
    ∃ count < fuel,
      (machine policy program).run count
        ⟨world, {control with goals := .evaluate expression destination :: older}, context⟩ = ([], .exhausted reached) ∧
      collectReturned? policy program
        ⟨reached.world, retainChild enteredScope (children.tail ++ pending) (origins ++ [0]) reached :: parents⟩ =
        some ⟨reached.world, Scope.record enteredScope (children.tail ++ pending)
          ⟨value, bindings, origins ++ [0], []⟩ :: parents⟩ := by
  dsimp only
  refine ⟨enterSuperpose_constructs world scope parents control context origins pending
    (expression :: alternatives) destination older frontier head, ?_, ?_⟩
  · simp [superposeWork]
  · obtain ⟨count, bound, earlier, collected, _goals, _records, _model⟩ :=
      selected_child_completed policy program fuel _ reached events
        {scope with frontier := superposeWork control context origins (expression :: alternatives) destination older ++ pending}
        parents ((superposeWork control context origins (expression :: alternatives) destination older).tail ++ pending)
        (origins ++ [0]) value bindings ran
    exact ⟨count, bound, earlier, collected⟩

/-- An actual empty superposition exhausts this child frontier without
manufacturing a value row. The existing collector then copies the complete
prior rows and resumes its saved caller, provided associated work is served. -/
theorem empty_superpose_finishes_scope {Context : Type} (world : World)
    (scope parent : CollectionScope Context) (parents : List (CollectionScope Context))
    (control : Control) (context : Context) (origins : List Nat) (destination : Atom) (older : List Goal)
    (caller : CollectionCaller Context)
    (frontier : scope.frontier = [(control, context, origins)])
    (head : control.goals = .evaluate (.expression [.symbol "superpose", .expression []]) destination :: older)
    (saved : scope.caller = some caller)
    (ready : ∀ answer ∈ scope.collected, answer.associated = []) :
    let reached : CollectionConfiguration Context :=
      ⟨world, {scope with frontier := []} :: parent :: parents⟩
    let copied := copiedWork (collectionSupport reached) scope.collected caller
    enterSuperpose? ⟨world, scope :: parent :: parents⟩ = some reached ∧
    Scope.finish? (copiedResume (collectionSupport reached)) reached =
      some ⟨world, {parent with frontier := copied :: parent.frontier} :: parents⟩ := by
  dsimp only
  constructor
  · simpa only [superposeWork, List.zipIdx_nil, List.map_nil, List.nil_append] using
      enterSuperpose_constructs world scope (parent :: parents) control context origins [] []
        destination older frontier head
  · simp only [Scope.finish?, saved, copiedResume_served _ _ _ ready,
      pure]
    rfl

/-- Actual source collapse entry supplies the child and caller used by the
existing completion theorem. The result and reached world come only from an
actual child run. This local case has no remaining sibling in the child. -/
theorem collapse_entry_completed_child {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (world : World)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (control : Control) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)) (expression destination : Atom) (older : List Goal)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (head : control.goals = .evaluate (.expression [.symbol "collapse", expression]) destination :: older)
    (fuel : Nat) (reached : Cursor Context) (events : List Empty) (value : Atom) (bindings : Equations)
    (ran : (machine policy program).run fuel
      ⟨world, collapseChild control (collectionSupport ⟨world, scope :: parents⟩) expression, context⟩ =
        (events, .finished (.value value bindings, reached))) :
    let allocation := collectionSupport ⟨world, scope :: parents⟩
    let caller : CollectionCaller Context := ({control with goals := older}, destination, context, origins)
    let childScope : CollectionScope Context :=
      ⟨[(collapseChild control allocation expression, context, origins)], [], some caller⟩
    let parent := {scope with frontier := pending}
    let before : CollectionConfiguration Context :=
      ⟨reached.world, retainChild childScope [] origins reached :: parent :: parents⟩
    let boundary := collectionSupport before
    let answers : List CollectedAnswer := [⟨value, bindings, origins, []⟩]
    let copied := copiedWork boundary answers caller
    enterCollapse? ⟨world, scope :: parents⟩ = some ⟨world, childScope :: parent :: parents⟩ ∧
    childName control allocation ∉ control.support ∪ allocation ∧
    ∃ count < fuel,
      (machine policy program).run count
        ⟨world, collapseChild control allocation expression, context⟩ = ([], .exhausted reached) ∧
      collectAtCurrentScope? policy program before =
        some ⟨reached.world, {parent with frontier := copied :: pending} :: parents⟩ ∧
      Collection.Copies boundary [(value, [])] (Collection.copyAnswers boundary [(value, [])]) ∧
      copied.1.bindings = control.bindings ∧ copied.2 = (context, origins) := by
  dsimp only
  refine ⟨enterCollapse_constructs world scope parents control context origins pending expression
    destination older frontier head, childName_fresh control _, ?_⟩
  exact completed_child_constructs_caller policy program _ fuel _ reached events
    ⟨[(collapseChild control _ expression, context, origins)], [],
      some ({control with goals := older}, destination, context, origins)⟩
    {scope with frontier := pending} parents origins
    ({control with goals := older}, destination, context, origins) value bindings
    rfl (by intro answer present; cases present) ran

/-- A scheduler pause after entry retains the actual reached world and control.
The saved caller, older frontier and prior answer rows are not re-created from
the entry state when the child resumes. -/
theorem collapse_entry_paused_child {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (world : World)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (control : Control) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)) (expression destination : Atom) (older : List Goal)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (head : control.goals = .evaluate (.expression [.symbol "collapse", expression]) destination :: older)
    (first second : Nat) (retained : Cursor Context) (events : List Empty)
    (paused : (machine policy program).run first
      ⟨world, collapseChild control (collectionSupport ⟨world, scope :: parents⟩) expression, context⟩ =
        (events, .exhausted retained)) :
    let boundary := collectionSupport ⟨world, scope :: parents⟩
    let caller : CollectionCaller Context := ({control with goals := older}, destination, context, origins)
    let childScope : CollectionScope Context :=
      ⟨[(collapseChild control boundary expression, context, origins)], [], some caller⟩
    enterCollapse? ⟨world, scope :: parents⟩ =
      some ⟨world, childScope :: {scope with frontier := pending} :: parents⟩ ∧
    (machine policy program).run (first + second)
      ⟨world, collapseChild control boundary expression, context⟩ =
      (events ++ ((machine policy program).run second retained).1,
        ((machine policy program).run second retained).2) ∧
    (retainChild childScope [] origins retained).caller = some caller ∧
    (retainChild childScope [] origins retained).collected = [] ∧
    (retainChild childScope [] origins retained).frontier = [(retained.control, retained.context, origins)] := by
  dsimp only
  exact ⟨enterCollapse_constructs world scope parents control context origins pending expression
    destination older frontier head, resume policy program first second _ retained events paused,
    rfl, rfl, rfl⟩

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination


set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination

/-- Both runnable alternatives and the saved caller retain valid lexical
delimiters. This concerns source continuation lists, not a native stack field. -/
def CollectionScope.wellDelimited {Context : Type} (scope : CollectionScope Context) : Prop :=
  (∀ work ∈ scope.frontier, WellDelimited work.1.goals) ∧
  (∀ caller, scope.caller = some caller → WellDelimited caller.1.goals)

def CollectionConfiguration.wellDelimited {Context : Type}
    (configuration : CollectionConfiguration Context) : Prop :=
  ∀ scope ∈ configuration.scopes, CollectionScope.wellDelimited scope

private theorem older_scope_delimited {Context : Type} (before : CollectionConfiguration Context)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (control : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (scopes : before.scopes = scope :: parents)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (valid : CollectionConfiguration.wellDelimited before) :
    CollectionScope.wellDelimited {scope with frontier := pending} ∧
    (∀ parent ∈ parents, CollectionScope.wellDelimited parent) ∧
    WellDelimited control.goals := by
  have selected := valid scope (by rw [scopes]; exact List.mem_cons_self)
  refine ⟨⟨?_, selected.2⟩, ?_, ?_⟩
  · intro work present
    apply selected.1 work
    rw [frontier]
    exact List.mem_cons_of_mem _ present
  · intro parent present
    apply valid parent
    rw [scopes]
    exact List.mem_cons_of_mem _ present
  · exact selected.1 _ (by rw [frontier]; exact List.mem_cons_self)

theorem enterCollapse_wellDelimited {Context : Type} (before after : CollectionConfiguration Context)
    (entered : enterCollapse? before = some after)
    (valid : CollectionConfiguration.wellDelimited before) :
    CollectionConfiguration.wellDelimited after := by
  obtain ⟨scope, parents, control, context, origins, pending, expression, destination, older,
    scopes, frontier, head, _fresh, rfl⟩ := enterCollapse_origin before after entered
  obtain ⟨parentValid, parentsValid, childValid⟩ :=
    older_scope_delimited before scope parents control context origins pending scopes frontier valid
  have olderValid : WellDelimited older := by simpa only [head, WellDelimited] using childValid
  intro target present
  rcases List.mem_cons.mp present with rfl | present
  · constructor
    · intro work member
      have same := List.mem_singleton.mp member
      subst work
      exact collapseChild_wellDelimited _ _ _
    · intro caller saved
      have same := Option.some.inj saved
      subst caller
      exact olderValid
  · rcases List.mem_cons.mp present with rfl | present
    · exact parentValid
    · exact parentsValid target present

theorem enterSuperpose_wellDelimited {Context : Type} (before after : CollectionConfiguration Context)
    (entered : enterSuperpose? before = some after)
    (valid : CollectionConfiguration.wellDelimited before) :
    CollectionConfiguration.wellDelimited after := by
  obtain ⟨scope, parents, control, context, origins, pending, alternatives, destination, older,
    scopes, frontier, head, rfl⟩ := enterSuperpose_origin before after entered
  obtain ⟨parentValid, parentsValid, childValid⟩ :=
    older_scope_delimited before scope parents control context origins pending scopes frontier valid
  have olderValid : WellDelimited older := by simpa only [head, WellDelimited] using childValid
  intro target present
  rcases List.mem_cons.mp present with rfl | present
  · refine ⟨?_, parentValid.2⟩
    intro work member
    rcases List.mem_append.mp member with chosen | pending
    · exact superposeWork_wellDelimited _ _ _ _ _ _ olderValid work chosen
    · exact parentValid.1 work pending
  · exact parentsValid target present

theorem enterEquations_wellDelimited {Context : Type} (program : SpaceSemantics.Program)
    (before after : CollectionConfiguration Context)
    (entered : enterEquations? program before = some after)
    (valid : CollectionConfiguration.wellDelimited before) :
    CollectionConfiguration.wellDelimited after := by
  obtain ⟨scope, parents, control, context, origins, pending, head, arguments, destination, older,
    environment, scopes, frontier, atCall, _ordinary, _declared, _resolved, rfl⟩ :=
    enterEquations_origin program before after entered
  obtain ⟨parentValid, parentsValid, childValid⟩ :=
    older_scope_delimited before scope parents control context origins pending scopes frontier valid
  have olderValid : WellDelimited older := by simpa only [atCall, WellDelimited] using childValid
  intro target present
  rcases List.mem_cons.mp present with rfl | present
  · refine ⟨?_, parentValid.2⟩
    intro work member
    rcases List.mem_append.mp member with chosen | pending
    · exact equationWork_wellDelimited _ _ _ _ _ _ _ _ _ _ olderValid work chosen
    · exact parentValid.1 work pending
  · exact parentsValid target present

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.EntryControls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.Logic.LP

private def emptyProgram : SpaceSemantics.Program := {equations := [], declarations := []}
private def world : World := ⟨Effects.empty, [], [.symbol "earlier"]⟩
private def alternatives : Atom := .expression [.symbol "superpose", .expression [.var "x", .var "x"]]
private def older : List Goal := [.invoke "==" [.var "a", .var "b"] (.var "out")]
private def caller : Control :=
  {bindings := [(.var "caller", .symbol "A")]
   goals := .evaluate (.expression [.symbol "collapse", alternatives])
     (.expression [.var "a", .var "b"]) :: older
   destination := .var "out"}
private def sibling : CollectionWork String :=
  ({bindings := [(.var "sibling", .symbol "B")], goals := [], destination := .var "sibling"}, "older-sibling", [3])
private def rootScope : CollectionScope String := ⟨[(caller, "caller-context", [4]), sibling], [], none⟩
private def initial : CollectionConfiguration String := ⟨world, [rootScope]⟩
private def protect := collectionSupport initial
private theorem protect_exact : protect = {"caller", "out", "sibling", "x", "a", "b"} := by
  ext name
  simp [protect, collectionSupport, initial, CollectionScope.support, rootScope, caller,
    alternatives, older, sibling, Control.support, Goal.atoms, operandSupport,
    CollectedAnswer.support, encode, Term.freeVars, Fin.exists_fin_succ]

private theorem child_name_exact : childName caller protect = "########" := by
  have supported : caller.support ⊆ protect :=
    scope_support initial rootScope (by simp [initial])
      |>.trans' (scope_work_support rootScope (caller, "caller-context", [4]) (by simp [rootScope]))
  have merged : (protectControl caller protect).support = protect := by
    rw [protectControl_support, Finset.union_eq_right.mpr supported]
  change String.replicate ((protectControl caller protect).support.sup String.length + 0 + 1) '#' = _
  rw [merged, protect_exact]
  simp only [Finset.sup_insert, Finset.sup_singleton]
  rfl

private def entered := enterCollapse? initial
private def split := entered.bind enterSuperpose?
private def child : Control :=
  {bindings := caller.bindings
   goals := [.evaluate alternatives (.var "########")]
   destination := .var "########"
   reserved := caller.support ∪ protect}
private theorem actual_child : collapseChild caller protect alternatives = child := by
  simp only [collapseChild, child_name_exact, child]
private theorem entered_exact : entered = some (Scope.enter world rootScope [sibling] []
    (child, "caller-context", [4])
    ({caller with goals := older}, .expression [.var "a", .var "b"], "caller-context", [4])) := by
  change enterCollapse? ⟨world, rootScope :: []⟩ = _
  rw [enterCollapse_constructs world rootScope [] caller "caller-context" [4] [sibling]
    alternatives (.expression [.var "a", .var "b"]) older rfl rfl]
  change some (Scope.enter world rootScope [sibling] []
    (collapseChild caller protect alternatives, "caller-context", [4]) _) = _
  rw [actual_child]

/-- Fixture driver invokes only the existing branch run and collector. It
does not supply a child value or suppress a pending/fault/request outcome. -/
private def finishHead (program : SpaceSemantics.Program) (fuel : Nat)
    (configuration : CollectionConfiguration String) : Option (CollectionConfiguration String) := do
  let scope :: parents := configuration.scopes | none
  let (control, context, origins) :: pending := scope.frontier | none
  match ((machine .relational program).run fuel ⟨configuration.world, control, context⟩).2 with
  | .finished (.value _ _, reached) =>
      collectAndResume? .relational program protect
        ⟨reached.world, retainChild scope pending origins reached :: parents⟩
  | _ => none

private def finishHeadScoped (program : SpaceSemantics.Program) (fuel : Nat)
    (configuration : CollectionConfiguration String) : Option (CollectionConfiguration String) := do
  let scope :: parents := configuration.scopes | none
  let (control, context, origins) :: pending := scope.frontier | none
  match ((machine .relational program).run fuel ⟨configuration.world, control, context⟩).2 with
  | .finished (.value _ _, reached) =>
      collectAtCurrentScope? .relational program
        ⟨reached.world, retainChild scope pending origins reached :: parents⟩
  | _ => none

private def first := split.bind (finishHead emptyProgram 3)
private def finished := first.bind (finishHead emptyProgram 3)
private def active (configuration : CollectionConfiguration String) : Option (Cursor String) := do
  let scope ← configuration.scopes.head?
  let work ← scope.frontier.head?
  pure ⟨configuration.world, work.1, work.2.1⟩
private def comparison : Option (List Atom) := do
  let configuration ← finished
  let cursor ← active configuration
  match ((machine .relational emptyProgram).run 2 cursor).2 with
  | .suspended (.invoke "==" arguments _) reached =>
      match StdLib.apply reached.world.state "==" arguments with
      | .ok (_, values) => some values
      | .error _ => none
  | _ => none

#guard entered.map (fun configuration => configuration.scopes.length) == some 2
#guard entered.map (fun configuration => configuration.world.output) == some [.symbol "earlier"]
#guard split.map (fun configuration => configuration.scopes.head?.map
  (fun scope => scope.frontier.map Prod.snd)) == some (some [("caller-context", [4, 0]), ("caller-context", [4, 1])])
#guard first.map (fun configuration => configuration.scopes.length) == some 2
#guard first.map (fun configuration => configuration.scopes.head?.map
  (fun scope => (scope.frontier.length, scope.collected.map CollectedAnswer.occurrences))) ==
    some (some (1, [[4, 0]]))
#guard finished.map (fun configuration => configuration.scopes.length) == some 1
#guard finished.map (fun configuration => configuration.scopes.head?.map
  (fun scope => scope.frontier.map Prod.snd)) == some (some [("caller-context", [4]), ("older-sibling", [3])])
#guard (finished.bind active).map (fun cursor => cursor.control.bindings) == some caller.bindings
#guard comparison == some [Effects.boolean false]
private def scopedFinished := (split.bind (finishHeadScoped emptyProgram 3)).bind (finishHeadScoped emptyProgram 3)
private def scopedComparison : Option (List Atom) := do
  let configuration ← scopedFinished
  let cursor ← active configuration
  match ((machine .relational emptyProgram).run 2 cursor).2 with
  | .suspended (.invoke "==" arguments _) reached =>
      match StdLib.apply reached.world.state "==" arguments with
      | .ok (_, values) => some values
      | .error _ => none
  | _ => none
#guard scopedComparison == some [Effects.boolean false]
#guard (split.bind (finishHead emptyProgram 1)).isNone

/-- The full literal entry path, two actual child executions and copied
caller resumption distinguish the residual answers in an ordinary context. -/
theorem entered_two_occurrences_compare_false : comparison = some [Effects.boolean false] := by
  have callerLength : "caller".length = 6 := rfl
  have outLength : "out".length = 3 := rfl
  have siblingLength : "sibling".length = 7 := rfl
  have xLength : "x".length = 1 := rfl
  have aLength : "a".length = 1 := rfl
  have bLength : "b".length = 1 := rfl
  have firstName : String.replicate 8 '#' = "########" := rfl
  have secondName : String.replicate 10 '#' = "##########" := rfl
  simp only [comparison, finished, first, split, entered_exact, Scope.enter, world, child, caller, alternatives,
    older, Control.support, List.flatMap_cons, List.flatMap_nil, List.append_nil, Goal.atoms, List.cons_append,
    List.nil_append, List.foldl_cons, encode, Term.freeVars, Finset.empty_union,
    Finset.union_empty, List.length_cons, List.length_nil, Nat.reduceAdd, id_eq, Fin.getElem_fin, Finset.insert_union,
    Finset.union_singleton, Finset.union_insert, Finset.mem_insert, String.reduceEq,
    Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and, Fin.exists_fin_two, Fin.isValue,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.getElem_cons_zero, Finset.notMem_empty, Nat.mod_succ,
    List.getElem_cons_succ, Finset.mem_singleton, or_self, or_false, or_true, Finset.insert_eq_of_mem, List.foldl_nil,
    protect_exact, sibling, rootScope, enterSuperpose?, superposeWork, Option.bind_some, List.zipIdx_cons, zero_add,
    List.zipIdx_nil, List.map_cons, List.map_nil, emptyProgram, finishHead, Machine.run, machine, resolve, equations,
    read, refine, List.map_append, prepare, replace, freshName, List.foldl_append, add_zero, ↓Char.isValue,
    List.append_assoc, encode_decode, Effects.boolean, unifyTotal, Term.occursIn, Bool.false_eq_true, ↓reduceIte,
    Subst.applyEqs, Subst.applyTerm, Subst.single, Subst.id, Option.isSome_some, Subst.applyTerm_var, Subst.comp,
    decode, collectAndResume?, collectReturned?, retainChild, Scope.record, Scope.finish?, copiedResume,
    List.all_eq_true, List.isEmpty_iff, Collection.copyAnswers, Collection.copyAnswer, Collection.copyName,
    Collection.allocation, List.map_map, Prod.mk.eta, Option.pure_def, Option.bind_eq_bind, Option.getD_none,
    List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_eq, and_self, Function.comp_apply,
    HE.Spec.Type.RuntimeRefinement.renameTypeVars, ClauseChoice.rename, Finset.union_idempotent, Finset.sup_insert,
    callerLength, outLength, siblingLength, xLength, aLength, Finset.sup_singleton, bLength, max_self, Nat.one_le_ofNat,
    sup_of_le_left, Nat.reduceLeDiff, sup_of_le_right, Nat.pair, ClauseChoice.names,
    HE.Spec.Type.Presentation.TypeSubst.typeVars, List.idxOf_cons_self, lt_self_iff_false, mul_zero, firstName,
    not_lt_zero, mul_one, secondName, Option.getD_some, active, ExceptT.stM_eq, List.head?_cons, ↓reduceDIte,
    finPairsToList, List.finRange_succ, List.finRange_zero, Fin.succ_zero_eq_one, List.cons.injEq, List.cons_ne_self,
    and_false, imp_self, implies_true, StdLib.structural_equality, Option.some.injEq, Atom.grounded.injEq,
    OSLFCore.GroundedValue.bool.injEq, beq_eq_false_iff_ne, ne_eq, Atom.var.injEq, not_false_eq_true]


/-- These are actual malformed source shapes, not failures of source work
that this component never attempted to serve. -/
private def malformed : CollectionConfiguration String :=
  ⟨world, [{rootScope with frontier :=
    [({caller with goals := [.evaluate (.expression [.symbol "collapse"]) (.var "out")]}, "caller-context", [4])]}]⟩
#guard (enterCollapse? malformed).isNone
#guard (enterSuperpose? initial).isNone

private def pair (left right : Atom) : Atom := .expression [.symbol "Pair", left, right]
private def row : SpaceSemantics.Equation := ⟨"f", [.var "x"], pair (.var "x") (.var "x")⟩
private def program : SpaceSemantics.Program := {equations := [row, row], declarations := []}
private def callControl : Control :=
  {bindings := [(.var "x", .symbol "A")]
   goals := [.invoke "f" [.symbol "B"] (.var "out")]
   destination := .var "out"}
private def callInitial : CollectionConfiguration String :=
  ⟨world, [⟨[(callControl, "call-context", [7]), sibling], [], none⟩]⟩
private def calls := enterEquations? program callInitial
private def callAnswer : Option Atom := do
  let configuration ← calls
  let cursor ← active configuration
  match ((machine .relational program).run 20 cursor).2 with
  | .finished (.value value _, _) => some value
  | _ => none

#guard calls.map (fun configuration => configuration.scopes.head?.map
  (fun scope => scope.frontier.map Prod.snd)) ==
    some (some [("call-context", [7, 0]), ("call-context", [7, 1]), ("older-sibling", [3])])
#guard callAnswer == some (pair (.symbol "B") (.symbol "B"))
#guard calls.map (fun configuration => configuration.world.output) == some [.symbol "earlier"]

private def conflicting : CollectionConfiguration String :=
  ⟨world, [⟨[({callControl with bindings := [(.var "x", .symbol "A"), (.var "x", .symbol "B")]},
    "call-context", [7]), sibling], [], none⟩]⟩
#guard (enterEquations? program conflicting).isNone
private def repeatedRow : SpaceSemantics.Equation := ⟨"g", [.var "x", .var "x"], .var "x"⟩
private def repeatedProgram : SpaceSemantics.Program := {equations := [repeatedRow], declarations := []}
private def refused : CollectionConfiguration String :=
  ⟨world, [⟨[({callControl with goals := [.invoke "g" [.symbol "A", .symbol "B"] (.var "out")]},
    "call-context", [7]), sibling], [], none⟩]⟩
#guard (enterEquations? repeatedProgram refused).map (fun configuration =>
  configuration.scopes.head?.map (fun scope => scope.frontier.map Prod.snd)) ==
    some (some [("older-sibling", [3])])
#guard (enterEquations? emptyProgram callInitial).isNone

private def effectExpression : Atom := .expression [.symbol "println!", .symbol "effect"]
private def effectCaller : Control :=
  {caller with goals := [.evaluate (.expression [.symbol "collapse", effectExpression]) (.var "answer")]}
private def effectInitial : CollectionConfiguration String :=
  ⟨world, [⟨[(effectCaller, "effect-context", [8]), sibling], [], none⟩]⟩
private def effectChild : Option (Cursor String) := (enterCollapse? effectInitial).bind active
private def effectRun (fuel : Nat) := effectChild.map (fun cursor => (machine .relational emptyProgram).run fuel cursor)
private def effectOutput (fuel : Nat) := (effectRun fuel).bind fun result =>
  (observed result.2).map (fun state => state.1.output)
private def effectResume : Option (List Atom) := do
  let result ← effectRun 4
  match result.2 with
  | .exhausted saved =>
      (observed ((machine .relational emptyProgram).run 8 saved).2).map (fun state => state.1.output)
  | _ => none

#guard effectOutput 4 == some [.symbol "earlier", .symbol "effect"]
#guard effectResume == some [.symbol "earlier", .symbol "effect"]
#guard effectOutput 12 == effectResume
#guard ((enterCollapse? effectInitial).bind (finishHead emptyProgram 4)).isNone

private def replayedEffect : Option (List Atom) := do
  let original ← effectChild
  let result ← effectRun 4
  match result.2 with
  | .exhausted saved =>
      (observed ((machine .relational emptyProgram).run 4
        {original with world := saved.world}).2).map (fun state => state.1.output)
  | _ => none
#guard replayedEffect == some [.symbol "earlier", .symbol "effect", .symbol "effect"]

private def nestedExpression : Atom := .expression [.symbol "collapse",
  .expression [.symbol "collapse", .expression [.symbol "quote", .var "x"]]]
private def nestedInitial : CollectionConfiguration String :=
  ⟨world, [⟨[({caller with goals := [.evaluate nestedExpression (.var "out")]},
    "nested-context", [6]), sibling], [], none⟩]⟩
private def twiceEntered := (enterCollapse? nestedInitial).bind enterCollapse?
private def onceClosed := twiceEntered.bind (finishHeadScoped emptyProgram 3)
private def twiceClosed := onceClosed.bind (finishHeadScoped emptyProgram 2)
private def staleBoundaryClosed := (twiceEntered.bind (finishHead emptyProgram 3)).bind (finishHead emptyProgram 2)
#guard staleBoundaryClosed.isNone
#guard twiceEntered.map (fun configuration => configuration.scopes.length) == some 3
#guard twiceEntered.map (fun configuration =>
  match configuration.scopes with
  | first :: _second :: _ =>
      (first.frontier.head?.map (fun work => work.1.destination)) !=
        (first.caller.map (fun caller => caller.2.1))
  | _ => false) == some true
#guard onceClosed.map (fun configuration => configuration.scopes.length) == some 2
#guard twiceClosed.map (fun configuration => configuration.scopes.length) == some 1
#guard twiceClosed.map (fun configuration => configuration.world.output) == some [.symbol "earlier"]

private def emptyInitial : CollectionConfiguration String :=
  ⟨world, [⟨[({caller with goals := [.evaluate (.expression [.symbol "collapse",
    .expression [.symbol "superpose", .expression []]]) (.var "out")]},
      "empty-context", [10]), sibling], [], none⟩]⟩
private def emptyEntered := (enterCollapse? emptyInitial).bind enterSuperpose?
private def emptyClosed := emptyEntered.bind fun configuration =>
  Scope.finish? (copiedResume (collectionSupport configuration)) configuration
#guard emptyEntered.map (fun configuration => configuration.scopes.head?.map
  (fun scope => (scope.frontier.length, scope.collected.length))) == some (some (0, 0))
#guard emptyClosed.map (fun configuration => configuration.scopes.length) == some 1
#guard (emptyClosed.bind active).map (fun cursor => cursor.control.goals.head?) ==
  some (some (.equate (.expression []) (.var "out")))

/-- Failed matching is not a collected answer. The reached world is retained
by the actual no-value result; this component does not silently close it. -/
private def rejectedChild : Cursor String :=
  ⟨{world with output := world.output ++ [.symbol "before-rejection"]},
    {bindings := [(.var "x", .symbol "A")]
     goals := [.equate (.symbol "B") (.var "x")]
     destination := .var "out"}, "rejected-context"⟩
#guard (match ((machine .relational emptyProgram).run 1 rejectedChild).2 with
  | .finished (.noValue bindings, reached) =>
      (bindings == rejectedChild.control.bindings) &&
        (reached.world.output == [.symbol "earlier", .symbol "before-rejection"])
  | _ => false)
#guard (collectReturned? .relational emptyProgram
  ⟨rejectedChild.world, [⟨[(rejectedChild.control, rejectedChild.context, [5])], [], none⟩]⟩).isNone

private def invalidControl : Control :=
  {caller with goals := [.argumentReturn (.var "x") (.var "out") 1]}
private def invalidInitial : CollectionConfiguration String :=
  ⟨world, [⟨[(invalidControl, "bad-delimiter", [9])], [], none⟩]⟩
#guard (enterCollapse? invalidInitial).isNone
#guard (enterSuperpose? invalidInitial).isNone
#guard (enterEquations? program invalidInitial).isNone
#guard (match ((machine .relational program).run 1
    (⟨world, invalidControl, "bad-delimiter"⟩ : Cursor String)).2 with
  | .suspended (.invalidDelimiter 1 0) _ => true
  | _ => false)

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.EntryControls


/-! ## Generative Destination scope scheduling

The existing retained scopes execute literal child entry, actual branch returns
and ordinary primitive requests. Collection allocates one identity per answer
and protects the complete current finite caller boundary. Attached work and
unserved allocation remain requests. The loading law represents the complete
initial packet; further world extensions require their local preservation laws.
-/


set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Collection

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared

/-- The finite allocator is searched, rather than receiving a purported fresh
identity from a result service. Lack of capacity is an unserved allocation. -/
def allocateAnswer? (allocator : Allocator) : Option (Allocator × Token) :=
  (List.range allocator.cells.size).findSome? (allocate? allocator)

theorem allocateAnswer_origin {allocator next : Allocator} {token : Token}
    (allocated : allocateAnswer? allocator = some (next, token)) :
    ∃ handle < allocator.cells.size, allocate? allocator handle = some (next, token) := by
  obtain ⟨handle, member, actual⟩ := List.exists_of_findSome?_eq_some allocated
  exact ⟨handle, List.mem_range.mp member, actual⟩

/-- Allocation checks the finite retained source boundary as well as actual
live identity separation. This also protects temporary source destinations
that are not yet stored under a contextual identity. -/
def allocateCopy? (allocator : Allocator) (protectedNames : Finset String)
    (value : Atom) (associated : List Atom) : Option (Allocator × Token) :=
  (List.range allocator.cells.size).findSome? fun handle => do
    let (next, token) ← allocate? allocator handle
    if ∀ name ∈ answerInventory value associated,
        allocatedName token (answerInventory value associated) name ∉ protectedNames then
      some (next, token)
    else none

theorem allocateCopy_origin {allocator next : Allocator} {token : Token}
    {protectedNames : Finset String} {value : Atom} {associated : List Atom}
    (computed : allocateCopy? allocator protectedNames value associated = some (next, token)) :
    (∃ handle, allocate? allocator handle = some (next, token)) ∧
    (∀ name ∈ answerInventory value associated,
      allocatedName token (answerInventory value associated) name ∉ protectedNames) := by
  obtain ⟨handle, _present, actual⟩ := List.exists_of_findSome?_eq_some computed
  obtain ⟨⟨middle, fresh⟩, allocated, selected⟩ := Option.bind_eq_some_iff.mp actual
  change (if ∀ name ∈ answerInventory value associated,
      allocatedName fresh (answerInventory value associated) name ∉ protectedNames then
    some (middle, fresh) else none) = some (next, token) at selected
  split at selected
  · rename_i avoided
    cases Option.some.inj selected
    exact ⟨⟨handle, allocated⟩, avoided⟩
  · contradiction

theorem copyAllocated_valid_of_avoids (protectedNames : Finset String)
    (token : Token) (value : Atom) (associated : List Atom)
    (avoids : ∀ name ∈ answerInventory value associated,
      allocatedName token (answerInventory value associated) name ∉ protectedNames) :
    IsCopy protectedNames value associated (copyAllocated token value associated) := by
  refine ⟨allocatedName token (answerInventory value associated), ?_, ?_, rfl, rfl⟩
  · intro left leftMember right rightMember same
    exact allocatedName_injective_on token _
      (by simpa [answerInventory] using leftMember)
      (by simpa [answerInventory] using rightMember) same
  · intro name member
    exact avoids name (by simpa [answerInventory] using member)

/-- Each answer allocates independently. Value and attached syntax share the
one map earned from that answer's complete inventory. -/
def copyOwnedAnswers? (allocator : Allocator) (protectedNames : Finset String) : List (Atom × List Atom) →
    Option (Allocator × List (Token × (Atom × List Atom)))
  | [] => some (allocator, [])
  | (value, associated) :: rest => do
      let (middle, token) ← allocateCopy? allocator protectedNames value associated
      let (next, copied) ← copyOwnedAnswers? middle protectedNames rest
      pure (next, (token, copyAllocated token value associated) :: copied)

/-- This is a trace of the existing allocation operations. It retains every
chosen identity and every input occurrence; it does not supply child results. -/
inductive OwnedCopies : Allocator → List (Atom × List Atom) → Allocator →
    List (Token × (Atom × List Atom)) → Prop where
  | nil (allocator) : OwnedCopies allocator [] allocator []
  | cons {allocator middle next token handle value associated rest copied}
      (allocated : allocate? allocator handle = some (middle, token))
      (later : OwnedCopies middle rest next copied) :
      OwnedCopies allocator ((value, associated) :: rest) next
        ((token, copyAllocated token value associated) :: copied)

theorem copyOwnedAnswers_trace {allocator next : Allocator}
    {source : List (Atom × List Atom)} {copied : List (Token × (Atom × List Atom))}
    {protectedNames : Finset String}
    (computed : copyOwnedAnswers? allocator protectedNames source = some (next, copied)) :
    OwnedCopies allocator source next copied := by
  induction source generalizing allocator next copied with
  | nil =>
      cases Option.some.inj computed
      exact .nil _
  | cons row rest ih =>
      rcases row with ⟨value, associated⟩
      obtain ⟨⟨middle, token⟩, allocated, later⟩ := Option.bind_eq_some_iff.mp computed
      obtain ⟨⟨final, tail⟩, copiedRest, same⟩ := Option.bind_eq_some_iff.mp later
      cases Option.some.inj same
      obtain ⟨⟨handle, actual⟩, _avoids⟩ := allocateCopy_origin allocated
      exact .cons actual (ih copiedRest)

/-- Finite caller protection is checked by the executed allocator search;
it is not an assumed expected copy or a globally reserved spelling prefix. -/
theorem copyOwnedAnswers_valid {allocator next : Allocator}
    {protectedNames : Finset String} {source : List (Atom × List Atom)}
    {copied : List (Token × (Atom × List Atom))}
    (computed : copyOwnedAnswers? allocator protectedNames source = some (next, copied)) :
    List.Forall₂ (fun raw row => IsCopy protectedNames raw.1 raw.2 row.2) source copied := by
  induction source generalizing allocator next copied with
  | nil =>
      cases Option.some.inj computed
      exact .nil
  | cons row rest ih =>
      rcases row with ⟨value, associated⟩
      obtain ⟨⟨middle, token⟩, allocated, later⟩ := Option.bind_eq_some_iff.mp computed
      obtain ⟨⟨final, tail⟩, copiedRest, same⟩ := Option.bind_eq_some_iff.mp later
      cases Option.some.inj same
      exact .cons (copyAllocated_valid_of_avoids protectedNames token value associated
        (allocateCopy_origin allocated).2) (ih copiedRest)

theorem OwnedCopies.length {allocator next : Allocator}
    {source : List (Atom × List Atom)} {copied : List (Token × (Atom × List Atom))}
    (trace : OwnedCopies allocator source next copied) : copied.length = source.length := by
  induction trace with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem OwnedCopies.preserves_live {allocator next : Allocator}
    {source : List (Atom × List Atom)} {copied : List (Token × (Atom × List Atom))}
    (trace : OwnedCopies allocator source next copied) {token : Token}
    (live : Live allocator token) : Live next token := by
  induction trace with
  | nil => exact live
  | cons allocated _ ih => exact ih (allocation_separates_live allocated live).2.1

theorem OwnedCopies.preserves_represented {allocator next : Allocator}
    {source : List (Atom × List Atom)} {copied : List (Token × (Atom × List Atom))}
    (trace : OwnedCopies allocator source next copied) {globals : List String} {name : String}
    (before : RepresentedName allocator globals name) : RepresentedName next globals name := by
  rcases before with ⟨reference, live, rfl⟩ | global
  · exact Or.inl ⟨reference, trace.preserves_live live, rfl⟩
  · exact Or.inr global

theorem OwnedCopies.preserves_world {allocator next : Allocator}
    {source : List (Atom × List Atom)} {copied : List (Token × (Atom × List Atom))}
    (trace : OwnedCopies allocator source next copied) {globals : List String} {world : World}
    (before : RepresentedWorld allocator globals world) : RepresentedWorld next globals world := by
  induction trace with
  | nil => exact before
  | cons allocated _ ih => exact ih (represented_world_allocation allocated before)

theorem OwnedCopies.rows_live {allocator next : Allocator}
    {source : List (Atom × List Atom)} {copied : List (Token × (Atom × List Atom))}
    (trace : OwnedCopies allocator source next copied)
    (row : Token × (Atom × List Atom)) (member : row ∈ copied) : Live next row.1 := by
  induction trace with
  | nil => cases member
  | cons allocated later ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact later.preserves_live (allocated_live allocated)
      · exact ih member

/-- Every copied variable is new relative to every represented old observer,
including old cells that are not enumerated by the local scope inventory. -/
theorem OwnedCopies.avoids_old {allocator next : Allocator}
    {source : List (Atom × List Atom)} {copied : List (Token × (Atom × List Atom))}
    (trace : OwnedCopies allocator source next copied) (globals : List String)
    (row : Token × (Atom × List Atom)) (member : row ∈ copied)
    (atom : Atom) (inTuple : atom ∈ row.2.1 :: row.2.2)
    (name : String) (occurs : name ∈ TypeSubst.typeVars atom) :
    ¬ RepresentedName allocator globals name := by
  induction trace with
  | nil => cases member
  | @cons allocator middle next token handle value associated rest copied allocated later ih =>
      rcases List.mem_cons.mp member with rfl | member
      · have inMap : atom ∈ (value :: associated).map
            (renameTypeVars (allocatedName token (answerInventory value associated))) := inTuple
        obtain ⟨raw, _present, rfl⟩ := List.mem_map.mp inMap
        rw [ScopeObservation.typeVars_renameTypeVars] at occurs
        obtain ⟨old, _oldMember, rfl⟩ := List.mem_map.mp occurs
        exact allocatedName_fresh allocated _ old globals
      · intro represented
        exact ih member (represented_preserved_by_allocation allocated represented)

theorem OwnedCopies.rows_represented {allocator next : Allocator}
    {source : List (Atom × List Atom)} {copied : List (Token × (Atom × List Atom))}
    (trace : OwnedCopies allocator source next copied) (globals : List String)
    (row : Token × (Atom × List Atom)) (member : row ∈ copied)
    (atom : Atom) (inTuple : atom ∈ row.2.1 :: row.2.2) :
    RepresentedAtom next globals atom := by
  induction trace with
  | nil => cases member
  | @cons allocator middle next token handle value associated rest copied allocated later ih =>
      rcases List.mem_cons.mp member with rfl | member
      · have inMap : atom ∈ (value :: associated).map
            (renameTypeVars (allocatedName token (answerInventory value associated))) := inTuple
        obtain ⟨raw, _present, rfl⟩ := List.mem_map.mp inMap
        intro name occurs
        rw [ScopeObservation.typeVars_renameTypeVars] at occurs
        obtain ⟨old, _oldMember, rfl⟩ := List.mem_map.mp occurs
        exact Or.inl ⟨token.ref ((answerInventory value associated).idxOf old),
          later.preserves_live (allocated_live allocated), rfl⟩
      · exact ih member

theorem OwnedCopies.independent_rows {allocator next : Allocator}
    {source : List (Atom × List Atom)} {copied : List (Token × (Atom × List Atom))}
    (trace : OwnedCopies allocator source next copied) :
    copied.Pairwise (fun first second => ∀ atom ∈ first.2.1 :: first.2.2,
      ∀ other ∈ second.2.1 :: second.2.2, ∀ name ∈ TypeSubst.typeVars atom,
        name ∉ TypeSubst.typeVars other) := by
  induction trace with
  | nil => exact .nil
  | @cons allocator middle next token handle value associated rest copied allocated later ih =>
      refine List.pairwise_cons.mpr ⟨?_, ih⟩
      intro row present atom inTuple other otherTuple name occurs otherOccurs
      have one : OwnedCopies allocator [(value, associated)] middle
          [(token, copyAllocated token value associated)] := .cons allocated (.nil _)
      have represented := one.rows_represented [] _ (by simp) atom inTuple name occurs
      exact later.avoids_old [] row present other otherTuple name otherOccurs represented

theorem OwnedCopies.valid_rows {allocator next : Allocator}
    {source : List (Atom × List Atom)} {copied : List (Token × (Atom × List Atom))}
    (trace : OwnedCopies allocator source next copied) (protectedNames : Finset String)
    (globals : List String)
    (represented : ∀ name ∈ protectedNames, RepresentedName allocator globals name) :
    List.Forall₂ (fun raw row => IsCopy protectedNames raw.1 raw.2 row.2) source copied := by
  induction trace with
  | nil => exact .nil
  | cons allocated _ ih =>
      exact .cons (copyAllocated_valid allocated protectedNames globals represented _ _)
        (ih (fun name member => represented_preserved_by_allocation allocated (represented name member)))

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Collection


set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- The saved scope and the shared identity authority are the entire state.
The existing world remains single and is never captured into an alternative. -/
abbrev ScopedCursor (Context : Type) := Allocator × CollectionConfiguration Context

inductive ScopeBoundary where
  | branch (request : Boundary)
  | fault (reason : Effects.Fault)
  | allocation
  | associatedWork
  | invalidScope
  deriving Repr

def allocatedWork {Context : Type} (copies : List (Token × (Atom × List Atom)))
    (caller : CollectionCaller Context) : CollectionWork Context :=
  ({caller.1 with goals := .equate (.expression (copies.map (fun row => row.2.1))) caller.2.1 :: caller.1.goals},
    caller.2.2.1, caller.2.2.2)

/-- This finish operation is reached only at a genuinely empty frontier.
Associated work is retained before any allocation is attempted. -/
def finishAllocated? {Context : Type} (source : ScopedCursor Context) : Option (ScopedCursor Context) := do
  let {frontier := [], collected := answers, caller := some caller} :: parent :: parents :=
    source.2.scopes | none
  if !(answers.all fun answer => answer.associated.isEmpty) then none else do
    let (allocator, copies) ← Collection.copyOwnedAnswers? source.1 (collectionSupport source.2)
      (answers.map fun answer => (answer.value, answer.associated))
    pure (allocator, ⟨source.2.world,
      {parent with frontier := allocatedWork copies caller :: parent.frontier} :: parents⟩)

theorem finishAllocated_origin {Context : Type} (before after : ScopedCursor Context)
    (finished : finishAllocated? before = some after) :
    ∃ answers caller parent parents copies,
      before.2.scopes = ⟨[], answers, some caller⟩ :: parent :: parents ∧
      (∀ answer ∈ answers, answer.associated = []) ∧
      Collection.copyOwnedAnswers? before.1 (collectionSupport before.2) (answers.map fun answer => (answer.value, answer.associated)) =
        some (after.1, copies) ∧
      Collection.OwnedCopies before.1 (answers.map fun answer => (answer.value, answer.associated))
        after.1 copies ∧
      after.2 = ⟨before.2.world,
        {parent with frontier := allocatedWork copies caller :: parent.frontier} :: parents⟩ := by
  unfold finishAllocated? at finished
  split at finished
  · rename_i answers caller parent parents scopes
    split at finished
    · contradiction
    · rename_i ready
      obtain ⟨⟨allocator, copies⟩, copied, same⟩ := Option.bind_eq_some_iff.mp finished
      cases Option.some.inj same
      refine ⟨answers, caller, parent, parents, copies, scopes, ?_, copied,
        Collection.copyOwnedAnswers_trace copied, rfl⟩
      simpa using ready
  · contradiction

theorem finishAllocated_completed {Context : Type} (allocator next : Allocator) (world : World)
    (answers : List CollectedAnswer) (caller : CollectionCaller Context)
    (parent : CollectionScope Context) (parents : List (CollectionScope Context))
    (copies : List (Token × (Atom × List Atom)))
    (ready : ∀ answer ∈ answers, answer.associated = [])
    (copied : Collection.copyOwnedAnswers? allocator
      (collectionSupport (⟨world, ⟨[], answers, some caller⟩ :: parent :: parents⟩ : CollectionConfiguration Context))
      (answers.map fun answer => (answer.value, answer.associated)) =
      some (next, copies)) :
    finishAllocated? (allocator, ⟨world, ⟨[], answers, some caller⟩ :: parent :: parents⟩) =
      some (next, ⟨world, {parent with frontier := allocatedWork copies caller :: parent.frontier} :: parents⟩) := by
  have allReady : answers.all (fun answer => answer.associated.isEmpty) = true := by
    apply List.all_eq_true.mpr
    intro answer member
    simp only [ready answer member, List.isEmpty_nil]
  simp [finishAllocated?, allReady, copied]

theorem finishAllocated_preserves_world {Context : Type} (before after : ScopedCursor Context)
    (finished : finishAllocated? before = some after) : after.2.world = before.2.world := by
  obtain ⟨_, _, _, _, _, _, _, _, _, same⟩ := finishAllocated_origin before after finished
  rw [same]

theorem finishAllocated_preserves_world_representation {Context : Type}
    (before after : ScopedCursor Context) (globals : List String)
    (represented : Collection.RepresentedWorld before.1 globals before.2.world)
    (finished : finishAllocated? before = some after) :
    Collection.RepresentedWorld after.1 globals after.2.world := by
  obtain ⟨_, _, _, _, _, _, _, _, trace, same⟩ := finishAllocated_origin before after finished
  rw [same]
  exact trace.preserves_world represented

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 12000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Collection.SyntaxLoading

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared

/-- Parsing produces authored syntax. This local loading operation reuses the
existing owned-copy allocator before that syntax can enter a live context.
A parse fault and an unserved allocation remain different outcomes. -/
def loadParsed? (allocator : Allocator) (protectedNames : Finset String) (text : Atom) :
    Except Effects.Fault (Option (Allocator × Token × Atom)) := do
  let raw ← StdLib.parseAtom text
  pure ((allocateCopy? allocator protectedNames raw []).map fun (next, token) =>
    (next, token, (copyAllocated token raw []).1))

theorem loadParsed_origin {allocator next : Allocator} {token : Token}
    {protectedNames : Finset String} {text loaded : Atom}
    (success : loadParsed? allocator protectedNames text = .ok (some (next, token, loaded))) :
    ∃ raw, StdLib.parseAtom text = .ok raw ∧
      allocateCopy? allocator protectedNames raw [] = some (next, token) ∧
      loaded = (copyAllocated token raw []).1 := by
  unfold loadParsed? at success
  cases parsed : StdLib.parseAtom text with
  | error reason => simp [parsed] at success
  | ok raw =>
    simp only [parsed] at success
    have mapped := Except.ok.inj success
    obtain ⟨⟨after, fresh⟩, actual, same⟩ := Option.map_eq_some_iff.mp mapped
    cases same
    exact ⟨raw, rfl, actual, rfl⟩

theorem loadParsed_completed {allocator next : Allocator} {token : Token}
    {protectedNames : Finset String} {text raw : Atom}
    (parsed : StdLib.parseAtom text = .ok raw)
    (allocated : allocateCopy? allocator protectedNames raw [] = some (next, token)) :
    loadParsed? allocator protectedNames text =
      .ok (some (next, token, (copyAllocated token raw []).1)) := by
  simp [loadParsed?, parsed, allocated]

/-- The actual parse and allocation earn the complete one-map copy law. -/
theorem loadParsed_isCopy {allocator next : Allocator} {token : Token}
    {protectedNames : Finset String} {text loaded : Atom}
    (success : loadParsed? allocator protectedNames text = .ok (some (next, token, loaded))) :
    ∃ raw, StdLib.parseAtom text = .ok raw ∧ IsCopy protectedNames raw [] (loaded, []) := by
  obtain ⟨raw, parsed, allocation, rfl⟩ := loadParsed_origin success
  refine ⟨raw, parsed, ?_⟩
  exact copyAllocated_valid_of_avoids protectedNames token raw [] (allocateCopy_origin allocation).2

/-- No spelling, including one that looks exactly like an encoded live
reference, can gain that reference's identity through this loading boundary. -/
theorem loadParsed_avoids_live_names {allocator next : Allocator} {token : Token}
    {protectedNames : Finset String} {text loaded : Atom} (globals : List String)
    (success : loadParsed? allocator protectedNames text = .ok (some (next, token, loaded)))
    (name : String) (old : RepresentedName allocator globals name) :
    name ∉ TypeSubst.typeVars loaded := by
  obtain ⟨raw, _, allocation, rfl⟩ := loadParsed_origin success
  obtain ⟨⟨handle, actual⟩, _⟩ := allocateCopy_origin allocation
  intro member
  change name ∈ TypeSubst.typeVars (renameTypeVars _ raw) at member
  rw [ScopeObservation.typeVars_renameTypeVars] at member
  obtain ⟨oldName, _, rfl⟩ := List.mem_map.mp member
  exact allocatedName_fresh actual _ oldName globals old

theorem loadParsed_represented {allocator next : Allocator} {token : Token}
    {protectedNames : Finset String} {text loaded : Atom} (globals : List String)
    (success : loadParsed? allocator protectedNames text = .ok (some (next, token, loaded))) :
    RepresentedAtom next globals loaded ∧ Live next token := by
  obtain ⟨raw, _, allocation, rfl⟩ := loadParsed_origin success
  obtain ⟨⟨handle, actual⟩, _⟩ := allocateCopy_origin allocation
  exact ⟨copyAllocated_represented (allocated_live actual) globals raw [], allocated_live actual⟩

/-- Consecutive parse calls allocate independently even for identical text. -/
theorem loadParsed_twice_disjoint {allocator middle next : Allocator} {first second : Token}
    {firstBoundary secondBoundary : Finset String} {firstText secondText firstValue secondValue : Atom}
    (firstLoaded : loadParsed? allocator firstBoundary firstText = .ok (some (middle, first, firstValue)))
    (secondLoaded : loadParsed? middle secondBoundary secondText = .ok (some (next, second, secondValue)))
    (name : String) (member : name ∈ TypeSubst.typeVars firstValue) :
    name ∉ TypeSubst.typeVars secondValue :=
  loadParsed_avoids_live_names [] secondLoaded name ((loadParsed_represented [] firstLoaded).1 name member)

/-- A parsed result can be written into the shared world with its earned
identity inventory. This is a local operation law, not a whole-run premise. -/
theorem loadParsed_putCell_represented {allocator next : Allocator} {token : Token}
    {protectedNames : Finset String} {text loaded : Atom} {globals : List String} {world : World}
    (before : RepresentedWorld allocator globals world)
    (success : loadParsed? allocator protectedNames text = .ok (some (next, token, loaded)))
    (cell : String) :
    RepresentedWorld next globals {world with state := world.state.putCell cell loaded} := by
  obtain ⟨raw, _, allocation, _⟩ := loadParsed_origin success
  obtain ⟨⟨handle, actual⟩, _⟩ := allocateCopy_origin allocation
  have retained := represented_world_allocation actual before
  exact ⟨represented_putCell retained.1 cell loaded (loadParsed_represented globals success).1, retained.2⟩

/-- The loaded syntax is precisely the existing contextual qualifier once
its actual inventory is installed; no second materializer is introduced. -/
theorem loadParsed_qualified {Payload : Type} {allocator next : Allocator} {token : Token}
    {protectedNames : Finset String} {text loaded : Atom}
    (success : loadParsed? allocator protectedNames text = .ok (some (next, token, loaded))) :
    ∃ raw, StdLib.parseAtom text = .ok raw ∧ ∀ (image : ImageOf Payload) (entry : EntryOf Payload),
      image.frameAt token.handle = some entry → entry.generation = token.generation →
      entry.frame = answerInventory raw [] → CurrentStore.qualify? image (token, raw) = some loaded := by
  obtain ⟨raw, parsed, _, rfl⟩ := loadParsed_origin success
  exact ⟨raw, parsed, fun image entry present generation inventory =>
    qualify_answer_copy image token entry present generation raw [] inventory⟩

/-- Publishing the actually allocated inventory makes the existing contextual
qualifier observe exactly the loaded syntax. All stored cells start open. -/
theorem loadParsed_publish {Payload : Type} {allocator next : Allocator} {token : Token}
    {protectedNames : Finset String} {text loaded : Atom}
    (success : loadParsed? allocator protectedNames text = .ok (some (next, token, loaded)))
    (image : ImageOf Payload) (bound : token.handle < image.entries.size) :
    ∃ raw published, StdLib.parseAtom text = .ok raw ∧
      image.publish? next token (answerInventory raw []) (fun _ => none) = some published ∧
      CurrentStore.qualify? published (token, raw) = some loaded ∧
      ∀ slot : MetavariableFrame.Slot (answerInventory raw []),
        published.lookupOwned next (token.ref slot.val) = some none := by
  obtain ⟨raw, parsed, allocation, rfl⟩ := loadParsed_origin success
  obtain ⟨⟨handle, actual⟩, _⟩ := allocateCopy_origin allocation
  have live := allocated_live actual
  let published : ImageOf Payload :=
    ⟨image.entries.setIfInBounds token.handle
      (some (EntryOf.initial token.generation (answerInventory raw []) (fun _ => none))),
      image.writeClock⟩
  have publication : image.publish? next token (answerInventory raw []) (fun _ => none) = some published := by
    simp only [ImageOf.publish?, live, bound, and_self, ↓reduceIte]
    rfl
  have present : published.frameAt token.handle = some
      (EntryOf.initial token.generation (answerInventory raw []) (fun _ => none)) := by
    rw [Snapshot.image_frameAt]
    simp only [published, Array.getElem?_setIfInBounds_self_of_lt bound, Option.getD_some]
  refine ⟨raw, published, parsed, publication,
    qualify_answer_copy published token _ present rfl raw [] rfl, ?_⟩
  intro slot
  simp only [ImageOf.lookupOwned, Token.ref, live, ↓reduceIte]
  exact Image.lookup_publish publication slot

theorem loadParsed_fault {allocator : Allocator} {protectedNames : Finset String} {text : Atom}
    {reason : Effects.Fault} (parsed : StdLib.parseAtom text = .error reason) :
    loadParsed? allocator protectedNames text = .error reason := by simp [loadParsed?, parsed]

theorem loadParsed_unserved {allocator : Allocator} {protectedNames : Finset String} {text raw : Atom}
    (parsed : StdLib.parseAtom text = .ok raw)
    (unserved : allocateCopy? allocator protectedNames raw [] = none) :
    loadParsed? allocator protectedNames text = .ok none := by simp [loadParsed?, parsed, unserved]

/-- An unlisted user spelling is encoded as a free name, never interpreted
as already possessing the authority denoted by an internal-looking string. -/
theorem unlisted_reference_spelling_not_identity (token : Token) (frame : MetavariableFrame.Frame) (reference : Ref)
    (absent : MetavariableFrame.indexOf frame (CurrentStore.referenceName reference) = none) :
    CurrentStore.nameIn token frame (CurrentStore.referenceName reference) ≠ CurrentStore.referenceName reference := by
  rw [CurrentStore.nameIn_external token frame _ absent]
  exact (CurrentStore.referenceName_ne_freeName reference _).symm

/-- Generative named-syntax source result after source occurrence binding.
The reader expands anonymous markers before this boundary; the independent
copy condition preserves the resulting variable identities and correlations.
The named inventory is earned by every successful read. -/
inductive NamedParseResult (protectedNames : Finset String) (text loaded : Atom) : Prop where
  | parsed (raw : Atom) (read : StdLib.parseAtom text = .ok raw)
      (named : "_" ∉ TypeSubst.typeVars raw)
      (copy : IsCopy protectedNames raw [] (loaded, []))

private theorem typeVars_eq_atomFreeVars (atom : Atom) :
    TypeSubst.typeVars atom = Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars atom := by
  induction atom using Atom.rec
      (motive_2 := fun atoms => TypeSubst.typeVarsList atoms =
        Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars.atomFreeVarsList atoms) with
  | symbol | var | grounded => rfl
  | expression atoms ih => exact ih
  | nil => rfl
  | cons atom atoms head tail =>
      simp only [TypeSubst.typeVarsList,
        Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars.atomFreeVarsList,head,tail]

/-- The successful reader and owned copy earn the source result together;
no post-reader variable inventory is supplied by the caller. -/
theorem loadParsed_named_result {allocator next : Allocator} {token : Token}
    {protectedNames : Finset String} {text loaded : Atom}
    (success : loadParsed? allocator protectedNames text = .ok (some (next, token, loaded))) :
    NamedParseResult protectedNames text loaded := by
  obtain ⟨raw, parsed, copied⟩ := loadParsed_isCopy success
  exact .parsed raw parsed (by simpa only [typeVars_eq_atomFreeVars] using StdLib.parseAtom_no_marker parsed) copied

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Collection.SyntaxLoading

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Primitive results preserve the reached equations and old continuation.
The result index records occurrences even when their values coincide. -/
def primitiveWork {Context : Type} (control : Control) (context : Context)
    (origins : List Nat) (destination : Atom) (older : List Goal)
    (values : List Atom) : List (CollectionWork Context) :=
  values.zipIdx.map fun (value, index) =>
    ({control with goals := .equate value destination :: older}, context, origins ++ [index])

/-- One stored occurrence is fresh for this query, using the same proved
caller-avoiding allocation as source clause selection. -/
def queryRow (control : Control) (occurrence : Nat) (row : Atom) : Atom :=
  Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars
    (ClauseChoice.rename control occurrence [row]) row

def queryAttempt (control : Control) (pattern template destination : Atom) (older : List Goal)
    (occurrence : Nat) (row : Atom) : Option Control := do
  let bindings ← refine control.bindings pattern (queryRow control occurrence row)
  pure {control with bindings, goals := .evaluate template destination :: older}

def queryChoices (control : Control) (pattern template destination : Atom) (older : List Goal)
    (rows : List Atom) (start : Nat := 0) : List (Nat × Control) :=
  (rows.zipIdx start).filterMap fun (row, occurrence) =>
    (queryAttempt control pattern template destination older occurrence row).map fun next => (occurrence, next)

def queryWork {Context : Type} (control : Control) (context : Context) (origins : List Nat)
    (pattern template destination : Atom) (older : List Goal) (rows : List Atom) : List (CollectionWork Context) :=
  (queryChoices control pattern template destination older rows).map fun (occurrence, next) =>
    (next, context, origins ++ [occurrence])

/-- Each selected stored occurrence contributes its source template under
the reached constraints. Duplicate rows remain distinct source occurrences. -/
inductive QueryFrontier (control : Control) (pattern template destination : Atom) (older : List Goal) :
    Nat → List Atom → List (Nat × Control) → Prop where
  | nil (start : Nat) : QueryFrontier control pattern template destination older start [] []
  | selected (start : Nat) (row : Atom) (rest : List Atom) (bindings : Equations)
      (tail : List (Nat × Control))
      (accepted : Refinement control.bindings pattern (queryRow control start row) (some bindings))
      (following : QueryFrontier control pattern template destination older (start + 1) rest tail) :
      QueryFrontier control pattern template destination older start (row :: rest)
        ((start, {control with bindings, goals := .evaluate template destination :: older}) :: tail)
  | refused (start : Nat) (row : Atom) (rest : List Atom) (tail : List (Nat × Control))
      (rejected : Refinement control.bindings pattern (queryRow control start row) none)
      (following : QueryFrontier control pattern template destination older (start + 1) rest tail) :
      QueryFrontier control pattern template destination older start (row :: rest) tail

theorem queryChoices_has_source (control : Control) (pattern template destination : Atom)
    (older : List Goal) (rows : List Atom) (start : Nat) :
    QueryFrontier control pattern template destination older start rows
      (queryChoices control pattern template destination older rows start) := by
  induction rows generalizing start with
  | nil => exact .nil start
  | cons row rest ih =>
      cases accepted : refine control.bindings pattern (queryRow control start row) with
      | none =>
          simpa [queryChoices, List.zipIdx_cons, queryAttempt, accepted] using
            QueryFrontier.refused start row rest _ ((refinement_iff _ _ _ _).mpr accepted) (ih (start + 1))
      | some bindings =>
          simpa [queryChoices, List.zipIdx_cons, queryAttempt, accepted] using
            QueryFrontier.selected start row rest bindings _ ((refinement_iff _ _ _ _).mpr accepted) (ih (start + 1))

theorem QueryFrontier.execution {control : Control} {pattern template destination : Atom} {older : List Goal}
    {start : Nat} {rows : List Atom} {selected : List (Nat × Control)}
    (source : QueryFrontier control pattern template destination older start rows selected) :
    queryChoices control pattern template destination older rows start = selected := by
  induction source with
  | nil => rfl
  | selected start row rest bindings tail accepted following ih =>
      simp [queryChoices, List.zipIdx_cons, queryAttempt, (refinement_iff _ _ _ _).mp accepted] at *
      exact ih
  | refused start row rest tail rejected following ih =>
      simp [queryChoices, List.zipIdx_cons, queryAttempt, (refinement_iff _ _ _ _).mp rejected] at *
      exact ih

/-- Surface query entry uses the reached space and schedules each template
recipe under the selected row's constraints. It does not materialize a
template variable into executable syntax before its source evaluation. -/
def scopedQuery {Context : Type} (source : ScopedCursor Context) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (location pattern template destination : Atom) (older : List Goal) :
    Mettapedia.GSLT.Distinction.ProductiveBlocks.Transition (ScopedCursor Context) CollectedAnswer (ScopedCursor Context) ScopeBoundary :=
  match Effects.readHandle location >>= source.2.world.state.read with
  | none => .call (.fault .invalidSpace) source
  | some rows =>
      .silent (source.1, ⟨source.2.world, {scope with frontier :=
        (queryWork (protectControl control (collectionSupport source.2)) context origins
          pattern template destination older rows ++ pending)} :: parents⟩)
/-- Interpret only the existing primitive table here. Every failed primitive
is retained as a control fault; unknown requests remain explicit. -/
def scopedInvocation {Context : Type} (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal) :
    Mettapedia.GSLT.Distinction.ProductiveBlocks.Transition (ScopedCursor Context) CollectedAnswer (ScopedCursor Context) ScopeBoundary :=
  if head = "parse" then
    match arguments with
    | [text] =>
      match Collection.SyntaxLoading.loadParsed? source.1 (collectionSupport source.2) text with
      | .error reason => .call (.fault reason) source
      | .ok none => .call .allocation source
      | .ok (some (allocator, _token, value)) =>
        .silent (allocator, ⟨source.2.world,
          {scope with frontier := primitiveWork control context origins destination older [value] ++ pending} :: parents⟩)
    | _ => .call (.fault (.invalidArguments "parse")) source
  else if StdLib.known head then
    match StdLib.apply source.2.world.state head arguments with
    | .error reason => .call (.fault reason) source
    | .ok (state, values) => .silent (source.1, ⟨{source.2.world with state},
        {scope with frontier := primitiveWork control context origins destination older values ++ pending} :: parents⟩)
  else
    match enterEquations? program source.2 with
    | some next => .silent (source.1, next)
    | none => .call (.branch (.invoke head arguments destination)) source

/-- Install the actual branch result. Refusal removes only the current
alternative, whereas a value records its reached bindings and source origin.
No driver callback supplies either result. -/
def installChild {Context : Type} (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (origins : List Nat)
    (pending : List (CollectionWork Context)) :
    Mettapedia.GSLT.Distinction.ProductiveBlocks.Transition (Cursor Context) Empty (Result × Cursor Context) Boundary →
    Mettapedia.GSLT.Distinction.ProductiveBlocks.Transition (ScopedCursor Context) CollectedAnswer (ScopedCursor Context) ScopeBoundary
  | .silent reached => .silent (source.1,
      ⟨reached.world, retainChild scope pending origins reached :: parents⟩)
  | .publish _ reached => .silent (source.1,
      ⟨reached.world, retainChild scope pending origins reached :: parents⟩)
  | .finish (.noValue _, reached) => .silent (source.1,
      ⟨reached.world, {scope with frontier := pending} :: parents⟩)
  | .finish (.value value bindings, reached) =>
      let answer : CollectedAnswer := ⟨value, bindings, origins, []⟩
      let next := (source.1, ⟨reached.world, Scope.record scope pending answer :: parents⟩)
      if scope.caller.isNone then .publish [answer] next else .silent next
  | .call .openCommit reached =>
      match reached.control.goals with
      | .openCommit :: older =>
          let resumed := {reached.control with goals := older,cutBoundary := pending.length}
          .silent (source.1, ⟨reached.world,
            {scope with frontier := (resumed,reached.context,origins) :: pending} :: parents⟩)
      | _ => .call .invalidScope source
  | .call (.commit retained) reached =>
      match reached.control.goals with
      | .commit :: older =>
          if retained ≤ pending.length then
            let kept := pending.drop (pending.length - retained)
            .silent (source.1, ⟨reached.world, {scope with frontier :=
              ({reached.control with goals := older},reached.context,origins) :: kept} :: parents⟩)
          else .call (.branch (.invalidDelimiter retained pending.length)) source
      | _ => .call .invalidScope source
  | .call (.invoke head arguments destination) reached =>
      match reached.control.goals with
      | .invoke _ _ _ :: older =>
          scopedInvocation program source scope parents reached.control reached.context origins pending
            head arguments destination older
      | _ => .call .invalidScope source
  | .call (.query location pattern template destination) reached =>
      match reached.control.goals with
      | .query _ _ _ _ :: older =>
          scopedQuery source scope parents reached.control reached.context origins pending
            location pattern template destination older
      | _ => .call .invalidScope source
  | .call request _ => .call (.branch request) source
  | .fail _ => .call .invalidScope source

/-- The scope scheduler executes the saved head, including literal child
entries, actual primitive requests, branch refusal and generative collection.
The existing productive-block driver supplies budgeting and resumption. -/
def scopeStep {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) :
    Mettapedia.GSLT.Distinction.ProductiveBlocks.Transition (ScopedCursor Context) CollectedAnswer (ScopedCursor Context) ScopeBoundary :=
  match source.2.scopes with
  | [] => .call .invalidScope source
  | scope :: parents =>
    match scope.frontier with
    | [] =>
      match scope.caller, parents with
      | none, [] => .finish source
      | some _, _ :: _ =>
          if scope.collected.all (fun answer => answer.associated.isEmpty) then
            match finishAllocated? source with
            | some next => .silent next
            | none => .call .allocation source
          else .call .associatedWork source
      | _, _ => .call .invalidScope source
    | (control, context, origins) :: pending =>
      match enterCollapse? source.2 with
      | some next => .silent (source.1, next)
      | none =>
        match enterSuperpose? source.2 with
        | some next => .silent (source.1, next)
        | none =>
          match control.goals with
          | .evaluate (.expression [.symbol "empty"]) _ :: _ =>
              .silent (source.1, ⟨source.2.world, {scope with frontier := pending} :: parents⟩)
          | _ =>
            match (machine policy program).step ⟨source.2.world, control, context⟩ with
            | some child => installChild program source scope parents origins pending child
            | none => .call .invalidScope source

theorem scopeStep_pending_associated {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (answers : List CollectedAnswer) (caller : CollectionCaller Context)
    (parent : CollectionScope Context) (parents : List (CollectionScope Context))
    (answer : CollectedAnswer) (member : answer ∈ answers) (pending : answer.associated ≠ []) :
    scopeStep policy program (allocator, ⟨world, ⟨[], answers, some caller⟩ :: parent :: parents⟩) =
      .call .associatedWork (allocator, ⟨world, ⟨[], answers, some caller⟩ :: parent :: parents⟩) := by
  have notReady : answers.all (fun answer => answer.associated.isEmpty) ≠ true := by
    intro ready
    exact pending (List.isEmpty_iff.mp (List.all_eq_true.mp ready answer member))
  simp [scopeStep, notReady]

theorem scopeStep_copied_return {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (allocator next : Allocator) (world : World)
    (answers : List CollectedAnswer) (caller : CollectionCaller Context)
    (parent : CollectionScope Context) (parents : List (CollectionScope Context))
    (copies : List (Token × (Atom × List Atom)))
    (ready : ∀ answer ∈ answers, answer.associated = [])
    (copied : Collection.copyOwnedAnswers? allocator
      (collectionSupport (⟨world, ⟨[], answers, some caller⟩ :: parent :: parents⟩ : CollectionConfiguration Context))
      (answers.map fun answer => (answer.value, answer.associated)) =
      some (next, copies)) :
    scopeStep policy program (allocator, ⟨world, ⟨[], answers, some caller⟩ :: parent :: parents⟩) =
      .silent (next, ⟨world, {parent with frontier := allocatedWork copies caller :: parent.frontier} :: parents⟩) := by
  have allReady : answers.all (fun answer => answer.associated.isEmpty) = true := by
    apply List.all_eq_true.mpr
    intro answer member
    simp only [ready answer member, List.isEmpty_nil]
  simp only [scopeStep, allReady, ↓reduceIte,
    finishAllocated_completed allocator next world answers caller parent parents copies ready copied]

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination


set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- A source refinement refusal consumes one alternative, not the enclosing
collection or the already performed world. -/
theorem scope_refused_return {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (value destination : Atom) (older : List Goal)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (head : control.goals = .equate value destination :: older)
    (refused : Refinement control.bindings value destination none) :
    scopeStep policy program (allocator, ⟨world, scope :: parents⟩) =
      .silent (allocator, ⟨world, {scope with frontier := pending} :: parents⟩) := by
  have actual := (refinement_iff _ _ _ _).mp refused
  simp only [scopeStep, frontier, enterCollapse?, head, enterSuperpose?, machine,
    actual, installChild]

/-- The reverse direction excludes an accepted return by the retained
frontier length. It cannot silently classify an update as failed search. -/
theorem scope_refused_return_iff {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (value destination : Atom) (older : List Goal)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (head : control.goals = .equate value destination :: older) :
    Refinement control.bindings value destination none ↔
      scopeStep policy program (allocator, ⟨world, scope :: parents⟩) =
        .silent (allocator, ⟨world, {scope with frontier := pending} :: parents⟩) := by
  constructor
  · exact scope_refused_return policy program allocator world scope parents control context origins
      pending value destination older frontier head
  · intro actual
    rw [refinement_iff]
    cases refined : refine control.bindings value destination with
    | none => rfl
    | some bindings =>
      simp only [scopeStep, frontier, enterCollapse?, head, enterSuperpose?, machine,
        refined, installChild] at actual
      have same := congrArg (fun result => match result with
        | .silent cursor => cursor.2.scopes.head?.map (fun (current : CollectionScope Context) => current.frontier.length)
        | _ => none) actual
      simp [retainChild] at same

theorem scope_accepted_return {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (value destination : Atom) (older : List Goal) (bindings : Equations)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (head : control.goals = .equate value destination :: older)
    (accepted : Refinement control.bindings value destination (some bindings)) :
    scopeStep policy program (allocator, ⟨world, scope :: parents⟩) =
      .silent (allocator, ⟨world, {scope with frontier :=
        ({control with bindings, goals := older}, context, origins) :: pending} :: parents⟩) := by
  have actual := (refinement_iff _ _ _ _).mp accepted
  simp only [scopeStep, frontier, enterCollapse?, head, enterSuperpose?, machine,
    actual, installChild, retainChild]

theorem scope_empty {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom) (older : List Goal)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (head : control.goals = .evaluate (.expression [.symbol "empty"]) destination :: older) :
    scopeStep policy program (allocator, ⟨world, scope :: parents⟩) =
      .silent (allocator, ⟨world, {scope with frontier := pending} :: parents⟩) := by
  simp [scopeStep, frontier, enterCollapse?, head, enterSuperpose?]

/-- This no-answer source rule already distinguishes empty search from
literal Error data and primitive faults. The scope scheduler uses it intact. -/
theorem empty_independent_source (program : SpaceSemantics.Program) (world : World)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (frames : List EagerDFS.Frame) :
    EagerDFS.LocalTransition program world
      ⟨.evaluate bindings (.expression [.symbol "empty"]), frames⟩ world (.alternatives []) :=
  .empty_enter

theorem scope_print {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (value destination : Atom) (older : List Goal) (environment : Environment)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (head : control.goals = .invoke "println!" [value] destination :: older)
    (resolved : resolve control.bindings = some environment) :
    scopeStep policy program (allocator, ⟨world, scope :: parents⟩) =
      .silent (allocator, ⟨{world with output := world.output ++ [read environment value]},
        {scope with frontier := (replace control (.equate (Effects.boolean true) destination :: older),
          context, origins) :: pending} :: parents⟩) := by
  have actual := print_step policy program (⟨world, control, context⟩ : Cursor Context)
    value destination older head resolved
  simp only [scopeStep, frontier, enterCollapse?, head, enterSuperpose?, actual, installChild, retainChild]

private theorem known_not_print {head : String} (known : StdLib.known head = true) : head ≠ "println!" := by
  rintro rfl
  simp [StdLib.known] at known

theorem scope_primitive_success {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (environment : Environment) (state : Effects.State) (values : List Atom)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke head arguments destination :: older)
    (resolved : resolve control.bindings = some environment)
    (known : StdLib.known head = true) (ordinary : head ≠ "parse")
    (applied : StdLib.apply world.state head (arguments.map (read environment)) = .ok (state, values)) :
    scopeStep policy program (allocator, ⟨world, scope :: parents⟩) =
      .silent (allocator, ⟨{world with state}, {scope with frontier := primitiveWork control context origins destination older values ++ pending} :: parents⟩) := by
  have requested := invoke_request_step policy program (⟨world, control, context⟩ : Cursor Context)
    head arguments destination older atCall (known_not_print known) resolved
  simp only [scopeStep, frontier, enterCollapse?, atCall, enterSuperpose?, requested,
    installChild, scopedInvocation, ordinary, ↓reduceIte, known, applied]

theorem scope_primitive_fault {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (environment : Environment) (reason : Effects.Fault)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke head arguments destination :: older)
    (resolved : resolve control.bindings = some environment)
    (known : StdLib.known head = true)
    (applied : StdLib.apply world.state head (arguments.map (read environment)) = .error reason) :
    scopeStep policy program (allocator, ⟨world, scope :: parents⟩) =
      .call (.fault reason) (allocator, ⟨world, scope :: parents⟩) := by
  have requested := invoke_request_step policy program (⟨world, control, context⟩ : Cursor Context)
    head arguments destination older atCall (known_not_print known) resolved
  simp only [scopeStep, frontier, enterCollapse?, atCall, enterSuperpose?, requested,
    installChild, scopedInvocation, known, ↓reduceIte, applied]
  by_cases parseHead : head = "parse"
  · subst head
    simp only [↓reduceIte]
    generalize argumentsEq : arguments.map (read environment) = operands at applied ⊢
    cases operands with
    | nil =>
      have reasonEq : Effects.Fault.invalidArguments "parse" = reason := Except.error.inj applied
      simp only [reasonEq]
    | cons text rest =>
      cases rest with
      | nil =>
        cases parsed : StdLib.parseAtom text with
        | error found =>
          change (match StdLib.parseAtom text with
            | .ok value => .ok (world.state, [value])
            | .error failure => .error failure) = Except.error reason at applied
          rw [parsed] at applied
          have reasonEq : found = reason := Except.error.inj applied
          simp only [Collection.SyntaxLoading.loadParsed?, parsed, reasonEq]
          rfl
        | ok value =>
          change (match StdLib.parseAtom text with
            | .ok value => .ok (world.state, [value])
            | .error failure => .error failure) = Except.error reason at applied
          rw [parsed] at applied
          contradiction
      | cons second rest =>
        have reasonEq : Effects.Fault.invalidArguments "parse" = reason := Except.error.inj applied
        simp only [reasonEq]
  · simp only [parseHead, ↓reduceIte]

/-- The actual primitive failure has the existing independent source rule.
It does not supply a successful child or erase the reached scope. -/
theorem primitive_fault_independent_source (program : SpaceSemantics.Program) (world : World)
    (head : String) (values : List Atom) (reason : Effects.Fault)
    (ordinary : Eval.ioHead head = false) (known : StdLib.known head = true)
    (applied : StdLib.apply world.state head values = .error reason)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (frames : List EagerDFS.Frame) :
    EagerDFS.LocalTransition program world
      ⟨.arguments bindings (.function head) [] values 0, frames⟩
      world (.next ⟨.fault reason, frames⟩) :=
  .primitive_fault ordinary known applied

theorem scope_collapse_entry {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (expression destination : Atom) (older : List Goal)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (head : control.goals = .evaluate (.expression [.symbol "collapse", expression]) destination :: older) :
    scopeStep policy program (allocator, ⟨world, scope :: parents⟩) =
      .silent (allocator, Scope.enter world scope pending parents
        (collapseChild control (collectionSupport ⟨world, scope :: parents⟩) expression, context, origins)
        ({control with goals := older}, destination, context, origins)) := by
  simp only [scopeStep, frontier,
    enterCollapse_constructs world scope parents control context origins pending expression destination older frontier head]

theorem scope_superpose_entry {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (alternatives : List Atom) (destination : Atom) (older : List Goal)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (head : control.goals = .evaluate (.expression [.symbol "superpose", .expression alternatives]) destination :: older) :
    scopeStep policy program (allocator, ⟨world, scope :: parents⟩) =
      .silent (allocator, ⟨world, {scope with frontier := superposeWork control context origins alternatives destination older ++ pending} :: parents⟩) := by
  have notCollapse : enterCollapse? (⟨world, scope :: parents⟩ : CollectionConfiguration Context) = none := by
    simp [enterCollapse?, frontier, head]
  simp only [scopeStep, frontier, notCollapse,
    enterSuperpose_constructs world scope parents control context origins pending alternatives destination older frontier head]

theorem scope_terminal_value {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (environment : Environment)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (head : control.goals = []) (resolved : resolve control.bindings = some environment) :
    let answer : CollectedAnswer := ⟨read environment control.destination, control.bindings, origins, []⟩
    let next : ScopedCursor Context := (allocator, ⟨world, Scope.record scope pending answer :: parents⟩)
    scopeStep policy program (allocator, ⟨world, scope :: parents⟩) =
      if scope.caller.isNone then .publish [answer] next else .silent next := by
  simp only [scopeStep, frontier, enterCollapse?, head, enterSuperpose?, machine, resolved, installChild]

/-- All existing source argument-return cases lift through the same saved
scope. In particular, error refusal drops one alternative, not its siblings. -/
theorem scope_argument_return {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (value destination : Atom) (younger older : List Goal)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (head : control.goals = .argumentReturn value destination older.length :: younger ++ older)
    (transition : Mettapedia.GSLT.Distinction.ProductiveBlocks.Transition
      (Cursor Context) Empty (Result × Cursor Context) Boundary)
    (source : ArgumentReturn (⟨world, control, context⟩ : Cursor Context) value destination younger older transition) :
    scopeStep policy program (allocator, ⟨world, scope :: parents⟩) =
      installChild program (allocator, ⟨world, scope :: parents⟩) scope parents origins pending transition := by
  have actual := argumentReturn_source_step policy program (⟨world, control, context⟩ : Cursor Context)
    value destination younger older head source
  simp only [scopeStep, frontier, enterCollapse?, head, List.cons_append, enterSuperpose?, actual]

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination


set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared

def Goal.rename (rename : String → String) : Goal → Goal
  | .evaluate expression destination => .evaluate (renameTypeVars rename expression) (renameTypeVars rename destination)
  | .equate value destination => .equate (renameTypeVars rename value) (renameTypeVars rename destination)
  | .branch condition yes no destination =>
      .branch (renameTypeVars rename condition) (renameTypeVars rename yes)
        (renameTypeVars rename no) (renameTypeVars rename destination)
  | .invoke head arguments destination => .invoke head (arguments.map (renameTypeVars rename)) (renameTypeVars rename destination)
  | .query location pattern template destination =>
      .query (renameTypeVars rename location) (renameTypeVars rename pattern)
        (renameTypeVars rename template) (renameTypeVars rename destination)
  | .argumentReturn value destination depth =>
      .argumentReturn (renameTypeVars rename value) (renameTypeVars rename destination) depth
  | .openCommit => .openCommit
  | .commit => .commit
  | .restoreCommit boundary => .restoreCommit boundary

def Control.atoms (control : Control) : List Atom :=
  control.destination :: control.bindings.flatMap (fun pair => [pair.1, pair.2]) ++
    control.goals.flatMap Goal.atoms

def Control.rename (rename : String → String) (control : Control) : Control :=
  {bindings := control.bindings.map (fun pair => (renameTypeVars rename pair.1, renameTypeVars rename pair.2))
   goals := control.goals.map (Goal.rename rename)
   destination := renameTypeVars rename control.destination
   reserved := control.reserved.image rename
   cutBoundary := control.cutBoundary}

theorem Goal.rename_atoms (rename : String → String) (goal : Goal) :
    (goal.rename rename).atoms = goal.atoms.map (renameTypeVars rename) := by
  cases goal <;> simp [Goal.rename, Goal.atoms]

theorem Control.rename_atoms (rename : String → String) (control : Control) :
    (control.rename rename).atoms = control.atoms.map (renameTypeVars rename) := by
  simp only [Control.rename, Control.atoms, List.flatMap_map,
    Goal.rename_atoms, List.map_cons, List.map_nil, List.map_append, List.map_flatMap]

/-- Loading uses one finite authored inventory for the whole initial packet:
state rows, cell payloads, input, active constraints and lexical observations. -/
def loadingInventory (core : List Atom) (cells : List (String × Atom)) (input : List Atom)
    (control : Control) (context : List Atom) : MetavariableFrame.Frame :=
  (ClauseChoice.names (core ++ cells.map Prod.snd ++ input ++ control.atoms ++ context) ++
    control.reserved.sort).eraseDups

def loadingState (rename : String → String) (core : List Atom) (cells : List (String × Atom)) :
    Effects.State :=
  cells.foldl (fun state cell => state.putCell cell.1 (renameTypeVars rename cell.2))
    (NamedSpaces.Store.new (core.map (renameTypeVars rename)) [])

/-- This loader performs the real authority allocation and constructs all
retained source fields. Raw spellings cannot impersonate owned identities. -/
def loadScoped? (allocator : Allocator) (core : List Atom) (cells : List (String × Atom))
    (input : List Atom) (control : Control) (context : List Atom) :
    Option (ScopedCursor (Token × List Atom)) := do
  let (next, token) ← Collection.allocateAnswer? allocator
  let rename := Collection.allocatedName token (loadingInventory core cells input control context)
  pure (next, ⟨⟨loadingState rename core cells, input.map (renameTypeVars rename), []⟩,
    [{frontier := [(control.rename rename, (token, context.map (renameTypeVars rename)), [])]}]⟩)

def RepresentedControl (allocator : Allocator) (globals : List String) (control : Control) : Prop :=
  (∀ atom ∈ control.atoms, Collection.RepresentedAtom allocator globals atom) ∧
    (∀ name ∈ control.reserved, Collection.RepresentedName allocator globals name)

theorem allocated_rename_represented (allocator : Allocator) (globals : List String)
    (token : Token) (live : Live allocator token) (inventory : MetavariableFrame.Frame)
    (atom : Atom) :
    Collection.RepresentedAtom allocator globals
      (renameTypeVars (Collection.allocatedName token inventory) atom) := by
  intro name occurs
  rw [ScopeObservation.typeVars_renameTypeVars] at occurs
  obtain ⟨old, _member, rfl⟩ := List.mem_map.mp occurs
  exact Or.inl ⟨token.ref (inventory.idxOf old), live, rfl⟩

theorem loadingState_represented (allocator : Allocator) (globals : List String)
    (token : Token) (live : Live allocator token) (inventory : MetavariableFrame.Frame)
    (core : List Atom) (cells : List (String × Atom)) :
    Collection.RepresentedState allocator globals
      (loadingState (Collection.allocatedName token inventory) core cells) := by
  have base : Collection.RepresentedState allocator globals
      (NamedSpaces.Store.new (core.map (renameTypeVars (Collection.allocatedName token inventory))) []) := by
    apply Collection.represented_new
    intro atom present
    obtain ⟨raw, _member, rfl⟩ := List.mem_map.mp present
    exact allocated_rename_represented allocator globals token live inventory raw
  unfold loadingState
  generalize NamedSpaces.Store.new (core.map (renameTypeVars (Collection.allocatedName token inventory))) [] = state at base ⊢
  induction cells generalizing state with
  | nil => exact base
  | cons cell rest ih =>
      exact ih _ (Collection.represented_putCell base cell.1 _
        (allocated_rename_represented allocator globals token live inventory cell.2))

/-- The complete loaded packet is represented by the actually allocated
token. This covers future reads of loaded cells without scanning them again
when a child collection finishes. -/
theorem loadScoped_origin (allocator : Allocator) (core : List Atom)
    (cells : List (String × Atom)) (input : List Atom) (control : Control) (context : List Atom)
    (next : ScopedCursor (Token × List Atom)) (globals : List String)
    (loaded : loadScoped? allocator core cells input control context = some next) :
    ∃ token handle,
      allocate? allocator handle = some (next.1, token) ∧ Live next.1 token ∧
      let rename := Collection.allocatedName token (loadingInventory core cells input control context)
      next.2 = ⟨⟨loadingState rename core cells, input.map (renameTypeVars rename), []⟩,
        [{frontier := [(control.rename rename, (token, context.map (renameTypeVars rename)), [])]}]⟩ ∧
      Collection.RepresentedWorld next.1 globals next.2.world ∧
      RepresentedControl next.1 globals (control.rename rename) ∧
      (∀ atom ∈ context.map (renameTypeVars rename), Collection.RepresentedAtom next.1 globals atom) ∧
      Set.InjOn rename {name | name ∈ loadingInventory core cells input control context} := by
  obtain ⟨⟨after, token⟩, allocated, same⟩ := Option.bind_eq_some_iff.mp loaded
  cases Option.some.inj same
  obtain ⟨handle, _bound, actual⟩ := Collection.allocateAnswer_origin allocated
  have live := allocated_live actual
  have every := allocated_rename_represented after globals token live
    (loadingInventory core cells input control context)
  refine ⟨token, handle, actual, live, rfl, ?_, ?_, ?_,
    Collection.allocatedName_injective_on token _⟩
  · exact ⟨loadingState_represented after globals token live _ core cells,
      fun atom member => by
        obtain ⟨raw, _present, rfl⟩ := List.mem_map.mp member
        exact every raw,
      by simp⟩
  · constructor
    · intro atom member
      rw [Control.rename_atoms] at member
      obtain ⟨raw, _present, rfl⟩ := List.mem_map.mp member
      exact every raw
    · intro name member
      obtain ⟨raw, _present, rfl⟩ := Finset.mem_image.mp member
      exact Or.inl ⟨token.ref ((loadingInventory core cells input control context).idxOf raw), live, rfl⟩
  · intro atom member
    obtain ⟨raw, _present, rfl⟩ := List.mem_map.mp member
    exact every raw

theorem loading_preserves_delimiters (rename : String → String) (goals : List Goal)
    (valid : WellDelimited goals) : WellDelimited (goals.map (Goal.rename rename)) := by
  induction goals with
  | nil => trivial
  | cons goal rest ih =>
      cases goal <;> simp only [WellDelimited, List.map_cons, Goal.rename, List.length_map] at *
      all_goals first | exact ih valid | exact ⟨valid.1, ih valid.2⟩

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination


set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared

/-- Loading's inventory is earned from every actual input position, including
cells not currently selected by a child and the caller's later observations. -/
theorem loadingInventory_covers (core : List Atom) (cells : List (String × Atom))
    (input : List Atom) (control : Control) (context : List Atom) (atom : Atom)
    (present : atom ∈ core ++ cells.map Prod.snd ++ input ++ control.atoms ++ context)
    (name : String) (occurs : name ∈ TypeSubst.typeVars atom) :
    name ∈ loadingInventory core cells input control context := by
  simp only [loadingInventory, List.mem_eraseDups, List.mem_append]
  exact Or.inl (List.mem_flatMap.mpr ⟨atom, present, occurs⟩)

/-- One allocated map preserves equality of variables across the entire
loaded tuple, rather than renaming each observed atom independently. -/
theorem loading_variable_correlation (core : List Atom) (cells : List (String × Atom))
    (input : List Atom) (control : Control) (context : List Atom) (token : Token)
    (first second : Atom) (one two : String)
    (firstPresent : first ∈ core ++ cells.map Prod.snd ++ input ++ control.atoms ++ context)
    (secondPresent : second ∈ core ++ cells.map Prod.snd ++ input ++ control.atoms ++ context)
    (firstVariable : one ∈ TypeSubst.typeVars first) (secondVariable : two ∈ TypeSubst.typeVars second) :
    Collection.allocatedName token (loadingInventory core cells input control context) one =
      Collection.allocatedName token (loadingInventory core cells input control context) two ↔ one = two := by
  constructor
  · exact Collection.allocatedName_injective_on token _
      (loadingInventory_covers core cells input control context first firstPresent one firstVariable)
      (loadingInventory_covers core cells input control context second secondPresent two secondVariable)
  · rintro rfl
    rfl

/-- The executing finish operation satisfies the independently stated copy
relation, retains raw caller constraints and the older frontier, and derives
between-answer independence from actual allocator history. -/
theorem finishAllocated_copy_observer {Context : Type} (before after : ScopedCursor Context)
    (finished : finishAllocated? before = some after) :
    ∃ answers caller parent parents copies,
      before.2.scopes = ⟨[], answers, some caller⟩ :: parent :: parents ∧
      (∀ answer ∈ answers, answer.associated = []) ∧
      Collection.OwnedCopies before.1 (answers.map fun answer => (answer.value, answer.associated))
        after.1 copies ∧
      List.Forall₂ (fun raw copied => Collection.IsCopy (collectionSupport before.2) raw.value raw.associated copied.2)
        answers copies ∧
      copies.Pairwise (fun first second => ∀ atom ∈ first.2.1 :: first.2.2,
        ∀ other ∈ second.2.1 :: second.2.2, ∀ name ∈ TypeSubst.typeVars atom,
          name ∉ TypeSubst.typeVars other) ∧
      after.2 = ⟨before.2.world,
        {parent with frontier := allocatedWork copies caller :: parent.frontier} :: parents⟩ ∧
      (allocatedWork copies caller).1.bindings = caller.1.bindings ∧
      (allocatedWork copies caller).2 = caller.2.2 := by
  obtain ⟨answers, caller, parent, parents, copies, scopes, ready, actual, trace, same⟩ :=
    finishAllocated_origin before after finished
  refine ⟨answers, caller, parent, parents, copies, scopes, ready, trace, ?_,
    trace.independent_rows, same, rfl, rfl⟩
  have valid := Collection.copyOwnedAnswers_valid actual
  simpa only [List.forall₂_map_left_iff] using valid

/-- For a reached completed child, an administrative return really executed
the allocation/copy operation. An attached-work or allocation request cannot
masquerade as a copied completion. -/
theorem scope_finish_reflects {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (answers : List CollectedAnswer)
    (caller : CollectionCaller Context) (parent : CollectionScope Context)
    (parents : List (CollectionScope Context)) (after : ScopedCursor Context)
    (stepped : scopeStep policy program
      (allocator, ⟨world, ⟨[], answers, some caller⟩ :: parent :: parents⟩) = .silent after) :
    finishAllocated? (allocator, ⟨world, ⟨[], answers, some caller⟩ :: parent :: parents⟩) = some after := by
  cases ready : answers.all (fun answer => answer.associated.isEmpty) with
  | false => simp [scopeStep, ready] at stepped
  | true =>
    simp only [scopeStep, ready, ↓reduceIte] at stepped
    cases finished : finishAllocated? (allocator, ⟨world, ⟨[], answers, some caller⟩ :: parent :: parents⟩) with
    | none => simp [finished] at stepped
    | some actual =>
      simp only [finished, Mettapedia.GSLT.Distinction.ProductiveBlocks.Transition.silent.injEq] at stepped
      subst actual
      rfl

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks

private theorem scopedInvocation_not_publish {Context : Type} (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (head : String)
    (arguments : List Atom) (destination : Atom) (older : List Goal)
    (events : List CollectedAnswer) (after : ScopedCursor Context) :
    scopedInvocation program source scope parents control context origins pending head arguments destination older ≠
      .publish events after := by
  unfold scopedInvocation
  repeat' first | (intro impossible; contradiction) | split

/-- Publication can only come from the actual value-return constructor of a
child. The wrapper cannot invent an answer from refusal or a service request. -/
theorem installChild_published_origin {Context : Type} (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (origins : List Nat)
    (pending : List (CollectionWork Context))
    (child : Mettapedia.GSLT.Distinction.ProductiveBlocks.Transition (Cursor Context) Empty (Result × Cursor Context) Boundary)
    (events : List CollectedAnswer) (after : ScopedCursor Context)
    (published : installChild program source scope parents origins pending child = .publish events after) :
    ∃ value bindings reached,
      child = .finish (.value value bindings, reached) ∧
      scope.caller = none ∧ events = [⟨value, bindings, origins, []⟩] ∧
      after = (source.1, ⟨reached.world,
        Scope.record scope pending ⟨value, bindings, origins, []⟩ :: parents⟩) := by
  cases child with
  | silent => contradiction
  | publish => contradiction
  | fail => contradiction
  | finish final =>
    rcases final with ⟨result, reached⟩
    cases result with
    | noValue => contradiction
    | value value bindings =>
      simp only [installChild] at published
      split at published
      · rename_i root
        have equal := Mettapedia.GSLT.Distinction.ProductiveBlocks.Transition.publish.inj published
        exact ⟨value, bindings, reached, rfl, Option.isNone_iff_eq_none.mp root, equal.1.symm, equal.2.symm⟩
      · contradiction
  | call request reached =>
    cases request with
    | openCommit =>
        simp only [installChild] at published
        split at published <;> cases published
    | commit retained =>
        simp only [installChild] at published
        split at published
        · split at published <;> cases published
        · cases published
    | invalidEnvironment => contradiction
    | invalidDelimiter => contradiction
    | invoke head arguments destination =>
      simp only [installChild] at published
      split at published
      · exact False.elim (scopedInvocation_not_publish _ _ _ _ _ _ _ _ _ _ _ _ _ _ published)
      · contradiction
    | query location pattern template destination =>
      simp only [installChild] at published
      split at published
      · unfold scopedQuery at published
        split at published <;> contradiction
      · contradiction

/-- Any root event has the independent solution model earned by the actual
resolver. Its raw reached constraints and occurrence origin are exact. -/
theorem scope_published_origin {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (source after : ScopedCursor Context) (events : List CollectedAnswer)
    (published : scopeStep policy program source = .publish events after) :
    ∃ scope parents control context pending value bindings origins environment,
      source.2.scopes = scope :: parents ∧
      scope.frontier = (control, context, origins) :: pending ∧
      control.goals = [] ∧ resolve control.bindings = some environment ∧
      events = [⟨value, bindings, origins, []⟩] ∧ bindings = control.bindings ∧
      value = read environment control.destination ∧ Solves environment bindings := by
  unfold scopeStep at published
  split at published
  · contradiction
  · rename_i scope parents scopes
    split at published
    · split at published
      · contradiction
      · split at published
        · split at published <;> contradiction
        · contradiction
      · contradiction
    · rename_i control context origins pending frontier
      split at published
      · contradiction
      · split at published
        · contradiction
        · split at published
          · contradiction
          · split at published
            · rename_i child stepped
              obtain ⟨value, bindings, reached, childReturn, _root, eventsEq, _after⟩ :=
                installChild_published_origin program source scope parents origins pending child events after published
              rw [childReturn] at stepped
              have goals : control.goals = [] := value_return_has_empty_goals policy program
                (⟨source.2.world, control, context⟩ : Cursor Context) reached value bindings stepped
              have reachedSame : reached = (⟨source.2.world, control, context⟩ : Cursor Context) := by
                simp only [machine, goals] at stepped
                split at stepped
                · cases Option.some.inj stepped
                · exact (congrArg Prod.snd
                    (Mettapedia.GSLT.Distinction.ProductiveBlocks.Transition.finish.inj
                      (Option.some.inj stepped))).symm
              subst reached
              obtain ⟨environment, resolved, readout, record⟩ :=
                (terminal_answer_iff policy program (⟨source.2.world, control, context⟩ : Cursor Context)
                  value bindings goals).mp stepped
              refine ⟨scope, parents, control, context, pending, value, bindings, origins, environment,
                scopes, frontier, goals, resolved, eventsEq, record, readout, ?_⟩
              rw [record]
              exact resolve_sound resolved
            · contradiction

/-- The published raw record carries the independent source model earned
by that same resolver occurrence. -/
theorem scope_published_source_model {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (source after : ScopedCursor Context) (events : List CollectedAnswer)
    (published : scopeStep policy program source = .publish events after) :
    ∃ value bindings origins environment,
      events = [⟨value, bindings, origins, []⟩] ∧ Solves environment bindings := by
  obtain ⟨_scope, _parents, _control, _context, _pending, value, bindings, origins, environment,
    _scopes, _frontier, _goals, _resolved, eventsEq, _record, _readout, solved⟩ :=
    scope_published_origin policy program source after events published
  exact ⟨value, bindings, origins, environment, eventsEq, solved⟩

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS

/-- Entering a collection uses the existing proper nesting judgment for the
same generic scope carrier; it does not add a second stack representation. -/
theorem Scope.enter_scopes_valid {Work Answer Caller : Type} (world : World)
    (scope : Scope Work Answer Caller) (pending : List Work)
    (parents : List (Scope Work Answer Caller)) (child : Work) (caller : Caller)
    (valid : ScopesValid (scope :: parents)) :
    ScopesValid (Scope.enter world scope pending parents child caller).scopes :=
  .nested _ _ _ (valid.replace_head pending scope.collected)

namespace Destination

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Proper scope nesting is constructed by loading the actual source packet. -/
theorem loadScoped_scopes_valid (allocator : Allocator) (core : List Atom)
    (cells : List (String × Atom)) (input : List Atom) (control : Control) (context : List Atom)
    (after : ScopedCursor (Token × List Atom))
    (loaded : loadScoped? allocator core cells input control context = some after) :
    ScopesValid after.2.scopes := by
  obtain ⟨token, handle, _allocated, _live, exactState, _represented, _control, _context, _injective⟩ :=
    loadScoped_origin allocator core cells input control context after [] loaded
  rw [exactState]
  exact .root _ _

theorem enterCollapse_scopes_valid {Context : Type} (before after : CollectionConfiguration Context)
    (valid : ScopesValid before.scopes) (entered : enterCollapse? before = some after) :
    ScopesValid after.scopes := by
  obtain ⟨scope, parents, control, context, origins, pending, expression, destination, older,
    scopes, _frontier, _head, _fresh, rfl⟩ := enterCollapse_origin before after entered
  rw [scopes] at valid
  exact Scope.enter_scopes_valid _ _ _ _ _ _ valid

theorem enterSuperpose_scopes_valid {Context : Type} (before after : CollectionConfiguration Context)
    (valid : ScopesValid before.scopes) (entered : enterSuperpose? before = some after) :
    ScopesValid after.scopes := by
  obtain ⟨scope, parents, control, context, origins, pending, alternatives, destination, older,
    scopes, _frontier, _head, rfl⟩ := enterSuperpose_origin before after entered
  rw [scopes] at valid
  exact valid.replace_head _ _

theorem enterEquations_scopes_valid {Context : Type} (program : SpaceSemantics.Program)
    (before after : CollectionConfiguration Context) (valid : ScopesValid before.scopes)
    (entered : enterEquations? program before = some after) : ScopesValid after.scopes := by
  unfold enterEquations? at entered
  split at entered
  · rename_i scope parents scopes
    rw [scopes] at valid
    split at entered
    · split at entered
      · split at entered
        · contradiction
        · split at entered
          · contradiction
          · obtain ⟨environment, _resolved, same⟩ := Option.bind_eq_some_iff.mp entered
            cases Option.some.inj same
            exact valid.replace_head _ _
      · contradiction
    · contradiction
  · contradiction

theorem finishAllocated_scopes_valid {Context : Type} (before after : ScopedCursor Context)
    (valid : ScopesValid before.2.scopes) (finished : finishAllocated? before = some after) :
    ScopesValid after.2.scopes := by
  obtain ⟨answers, caller, parent, parents, copies, scopes, _ready, _copied, _trace, same⟩ :=
    finishAllocated_origin before after finished
  rw [scopes] at valid
  cases valid with
  | nested _ _ _ parentValid =>
    rw [same]
    exact parentValid.replace_head _ _

/-- Every scheduler outcome retains an actual scope configuration, including
faults and requests. No branch fabricates a fault outcome with lost state. -/
def ScopesPreserved {Context : Type} :
    Mettapedia.GSLT.Distinction.ProductiveBlocks.Transition (ScopedCursor Context) CollectedAnswer
      (ScopedCursor Context) ScopeBoundary → Prop
  | .silent next | .publish _ next | .finish next | .call _ next => ScopesValid next.2.scopes
  | .fail _ => False

private theorem scopedInvocation_scopes_valid {Context : Type} (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (valid : ScopesValid source.2.scopes) (same : source.2.scopes = scope :: parents) :
    ScopesPreserved (scopedInvocation program source scope parents control context origins pending
      head arguments destination older) := by
  have headValid : ScopesValid (scope :: parents) := same ▸ valid
  unfold scopedInvocation
  repeat' first
    | exact valid
    | exact headValid.replace_head _ _
    | exact enterEquations_scopes_valid program _ _ valid (by assumption)
    | split

private theorem installChild_scopes_valid {Context : Type} (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (origins : List Nat)
    (pending : List (CollectionWork Context))
    (child : Mettapedia.GSLT.Distinction.ProductiveBlocks.Transition (Cursor Context) Empty (Result × Cursor Context) Boundary)
    (valid : ScopesValid source.2.scopes) (same : source.2.scopes = scope :: parents) :
    ScopesPreserved (installChild program source scope parents origins pending child) := by
  have headValid : ScopesValid (scope :: parents) := same ▸ valid
  cases child with
  | silent reached | publish _ reached => exact headValid.replace_head _ _
  | fail => exact valid
  | finish final =>
    rcases final with ⟨result, reached⟩
    cases result with
    | noValue => exact headValid.replace_head _ _
    | value =>
      simp only [installChild]
      split <;> exact headValid.replace_head _ _
  | call request reached =>
    cases request with
    | openCommit =>
        simp only [installChild]
        split
        · exact headValid.replace_head _ _
        · exact valid
    | commit retained =>
        simp only [installChild]
        split
        · split
          · exact headValid.replace_head _ _
          · exact valid
        · exact valid
    | invalidEnvironment => exact valid
    | invalidDelimiter => exact valid
    | invoke head arguments destination =>
      simp only [installChild]
      split
      · exact scopedInvocation_scopes_valid program source scope parents _ _ origins pending
          head arguments destination _ valid same
      · exact valid
    | query location pattern template destination =>
      simp only [installChild]
      split
      · unfold scopedQuery
        split
        · exact valid
        · exact headValid.replace_head _ _
      · exact valid

theorem scopeStep_scopes_valid {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) (valid : ScopesValid source.2.scopes) :
    ScopesPreserved (scopeStep policy program source) := by
  unfold scopeStep
  split
  · exact valid
  · rename_i scope parents scopes
    have headValid : ScopesValid (scope :: parents) := scopes ▸ valid
    split
    · split
      · exact valid
      · split
        · split
          · rename_i after finished
            exact finishAllocated_scopes_valid _ _ valid finished
          · exact valid
        · exact valid
      · exact valid
    · rename_i control context origins pending frontier
      split
      · rename_i after entered
        exact enterCollapse_scopes_valid _ _ valid entered
      · split
        · rename_i after entered
          exact enterSuperpose_scopes_valid _ _ valid entered
        · split
          · exact headValid.replace_head _ _
          · split
            · exact installChild_scopes_valid program source scope parents origins pending _ valid scopes
            · exact valid

end Destination
end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Collection

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open NamedSpaces (Handle)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects (readHandle)

/-- A successful actual insertion preserves the identity inventory precisely
when its new row has that inventory. No whole-execution premise is used. -/
theorem represented_insert {allocator : Allocator} {globals : List String}
    {state after : Effects.State} {handle : Handle} {value : Atom}
    (before : RepresentedState allocator globals state)
    (payload : RepresentedAtom allocator globals value)
    (inserted : Effects.insert state handle value = some after) :
    RepresentedState allocator globals after := by
  obtain ⟨rows, existing, written⟩ := Option.bind_eq_some_iff.mp inserted
  apply represented_write before ?_ written
  intro atom member
  rcases List.mem_append.mp member with old | new
  · exact before.1 handle rows existing atom old
  · cases List.mem_singleton.mp new
    exact payload

/-- Removing rows introduces no new variable authority and does not modify
state cells. The actual matched row filter determines the surviving data. -/
theorem represented_erase {allocator : Allocator} {globals : List String}
    {state after : Effects.State} {handle : Handle} {pattern : Atom}
    (before : RepresentedState allocator globals state)
    (erased : Effects.erase state handle pattern = some after) :
    RepresentedState allocator globals after := by
  obtain ⟨rows, existing, written⟩ := Option.bind_eq_some_iff.mp erased
  apply represented_write before ?_ written
  intro atom member
  exact before.1 handle rows existing atom (List.mem_filter.mp member).1

private theorem primitive_state_origin {state after : Effects.State}
    {head : String} {arguments answers : List Atom}
    (returned : StdLib.apply state head arguments = .ok (after, answers)) :
    after = state ∨ after = (state.allocate []).2 ∨
      (∃ handle value, value ∈ arguments ∧ Effects.insert state handle value = some after) ∨
      (∃ handle pattern, Effects.erase state handle pattern = some after) ∨
      (∃ name value, value ∈ arguments ∧ after = state.putCell name value) := by
  by_cases notNew : head = "new-space"
  · subst head
    cases arguments with
    | nil =>
      change Except.ok ((state.allocate []).2, _) = _ at returned
      cases returned
      exact Or.inr (Or.inl rfl)
    | cons first rest =>
      change Except.error _ = Except.ok _ at returned
      cases returned
  by_cases notAdd : head = "add-atom"
  · subst head
    cases arguments with
    | nil => change Except.error _ = Except.ok _ at returned; cases returned
    | cons location rest =>
      cases rest with
      | nil => change Except.error _ = Except.ok _ at returned; cases returned
      | cons value rest =>
        cases rest with
        | cons _ _ => change Except.error _ = Except.ok _ at returned; cases returned
        | nil =>
          change (match readHandle location >>= fun handle => Effects.insert state handle value with
            | some after => Except.ok (after, [Effects.boolean true])
            | none => Except.error Effects.Fault.invalidSpace) = _ at returned
          split at returned
          · rename_i after' inserted
            cases returned
            obtain ⟨handle, _, insertion⟩ := Option.bind_eq_some_iff.mp inserted
            exact Or.inr (Or.inr (Or.inl ⟨handle, value, by simp, insertion⟩))
          · cases returned
  by_cases notRemove : head = "remove-atom"
  · subst head
    cases arguments with
    | nil => change Except.error _ = Except.ok _ at returned; cases returned
    | cons location rest =>
      cases rest with
      | nil => change Except.error _ = Except.ok _ at returned; cases returned
      | cons value rest =>
        cases rest with
        | cons _ _ => change Except.error _ = Except.ok _ at returned; cases returned
        | nil =>
          change (match readHandle location with
            | none => Except.error Effects.Fault.invalidSpace
            | some handle => match state.read handle with
              | none => Except.error Effects.Fault.invalidSpace
              | some _ => match value with
                | .var _ => Except.ok (state, [Effects.boolean true])
                | .expression (_ :: _) => match Effects.erase state handle value with
                  | some after => Except.ok (after, [Effects.boolean true])
                  | none => Except.error Effects.Fault.invalidSpace
                | _ => Except.ok (state, [])) = _ at returned
          split at returned
          · cases returned
          · split at returned
            · cases returned
            · split at returned
              · cases returned; exact Or.inl rfl
              · split at returned
                · cases returned
                  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, by assumption⟩)))
                · cases returned
              · cases returned; exact Or.inl rfl
  by_cases notChange : head = "change-state!"
  · subst head
    cases arguments with
    | nil => change Except.error _ = Except.ok _ at returned; cases returned
    | cons first rest =>
      cases first with
      | symbol name =>
        cases rest with
        | nil => change Except.error _ = Except.ok _ at returned; cases returned
        | cons value rest =>
          cases rest with
          | cons _ _ => change Except.error _ = Except.ok _ at returned; cases returned
          | nil =>
            change Except.ok (state.putCell name value, _) = _ at returned
            cases returned
            exact Or.inr (Or.inr (Or.inr (Or.inr ⟨name, value, by simp, rfl⟩)))
      | var _ => change Except.error _ = Except.ok _ at returned; cases returned
      | grounded _ => change Except.error _ = Except.ok _ at returned; cases returned
      | expression _ => change Except.error _ = Except.ok _ at returned; cases returned
  exact Or.inl (StdLib.successful_apply_state notNew notAdd notRemove notChange returned)

/-- The primitive table's actual state-changing operations preserve this
local invariant. The new payload is checked at the write, rather than assuming
that every future world in a completed execution is already represented. -/
theorem primitive_state_represented {allocator : Allocator} {globals : List String}
    {state after : Effects.State} {head : String} {arguments answers : List Atom}
    (before : RepresentedState allocator globals state)
    (payloads : ∀ atom ∈ arguments, RepresentedAtom allocator globals atom)
    (returned : StdLib.apply state head arguments = .ok (after, answers)) :
    RepresentedState allocator globals after := by
  rcases primitive_state_origin returned with rfl | rfl | ⟨handle, value, member, inserted⟩ |
    ⟨handle, pattern, erased⟩ | ⟨name, value, member, rfl⟩
  · exact before
  · exact represented_allocate_space before [] (by simp)
  · exact represented_insert before (payloads value member) inserted
  · exact represented_erase before erased
  · exact represented_putCell before name value (payloads value member)

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Collection

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared

/-- At a successful primitive write, actual reached arguments establish the
new-world inventory. Input and already emitted output are retained exactly. -/
theorem primitive_world_represented {allocator : Allocator} {globals : List String}
    {world : World} {head : String} {arguments answers : List Atom} {after : Effects.State}
    (before : Collection.RepresentedWorld allocator globals world)
    (payloads : ∀ atom ∈ arguments, Collection.RepresentedAtom allocator globals atom)
    (returned : StdLib.apply world.state head arguments = .ok (after, answers)) :
    Collection.RepresentedWorld allocator globals {world with state := after} :=
  ⟨Collection.primitive_state_represented before.1 payloads returned, before.2⟩

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination


namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks

open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation

/-- The entire parsed invocation has one actual operation boundary. The
reached operands are read before parsing, and no caller or older scope is
captured into a fresh alternative. -/
theorem scope_parse_step {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (text destination : Atom) (older : List Goal) (environment : Environment)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke "parse" [text] destination :: older)
    (resolved : resolve control.bindings = some environment) :
    scopeStep policy program (allocator, ⟨world, scope :: parents⟩) =
      match Collection.SyntaxLoading.loadParsed? allocator
        (collectionSupport ⟨world, scope :: parents⟩) (read environment text) with
      | .error reason => .call (.fault reason) (allocator, ⟨world, scope :: parents⟩)
      | .ok none => .call .allocation (allocator, ⟨world, scope :: parents⟩)
      | .ok (some (next, _token, value)) =>
        .silent (next, ⟨world,
          {scope with frontier := primitiveWork control context origins destination older [value] ++ pending} :: parents⟩) := by
  have requested := invoke_request_step policy program (⟨world, control, context⟩ : Cursor Context)
    "parse" [text] destination older atCall (by decide) resolved
  simp only [scopeStep, frontier, enterCollapse?, atCall, enterSuperpose?, requested,
    installChild, scopedInvocation, ↓reduceIte, List.map_cons, List.map_nil]

/-- Successful parsing resumes the ordinary return constraint with the
freshly loaded value and the unchanged reached source context. -/
theorem scope_parse_success {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator next : Allocator) (token : Token) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (text value destination : Atom) (older : List Goal) (environment : Environment)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke "parse" [text] destination :: older)
    (resolved : resolve control.bindings = some environment)
    (loaded : Collection.SyntaxLoading.loadParsed? allocator
      (collectionSupport ⟨world, scope :: parents⟩) (read environment text) =
      .ok (some (next, token, value))) :
    scopeStep policy program (allocator, ⟨world, scope :: parents⟩) =
      .silent (next, ⟨world,
        {scope with frontier := primitiveWork control context origins destination older [value] ++ pending} :: parents⟩) := by
  rw [scope_parse_step policy program allocator world scope parents control context origins pending
    text destination older environment frontier atCall resolved, loaded]

/-- An allocation refusal keeps the exact reached call and every completed
world effect. It is not an empty result or failure of an alternative. -/
theorem scope_parse_unserved {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (text destination : Atom) (older : List Goal) (environment : Environment)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke "parse" [text] destination :: older)
    (resolved : resolve control.bindings = some environment)
    (unserved : Collection.SyntaxLoading.loadParsed? allocator
      (collectionSupport ⟨world, scope :: parents⟩) (read environment text) = .ok none) :
    scopeStep policy program (allocator, ⟨world, scope :: parents⟩) =
      .call .allocation (allocator, ⟨world, scope :: parents⟩) := by
  rw [scope_parse_step policy program allocator world scope parents control context origins pending
    text destination older environment frontier atCall resolved, unserved]

/-- Reflection recovers the actual raw read, owned allocation and exact
continuation from a successful source step. It never assumes the target
value as a service specification. -/
theorem scope_parse_silent_origin {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (text destination : Atom) (older : List Goal) (environment : Environment)
    (after : ScopedCursor Context)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke "parse" [text] destination :: older)
    (resolved : resolve control.bindings = some environment)
    (stepped : scopeStep policy program (allocator, ⟨world, scope :: parents⟩) = .silent after) :
    ∃ next token value raw,
      Collection.SyntaxLoading.loadParsed? allocator
        (collectionSupport ⟨world, scope :: parents⟩) (read environment text) = .ok (some (next, token, value)) ∧
      StdLib.parseAtom (read environment text) = .ok raw ∧
      Collection.IsCopy (collectionSupport ⟨world, scope :: parents⟩) raw [] (value, []) ∧
      after = (next, ⟨world,
        {scope with frontier := primitiveWork control context origins destination older [value] ++ pending} :: parents⟩) := by
  rw [scope_parse_step policy program allocator world scope parents control context origins pending
    text destination older environment frontier atCall resolved] at stepped
  cases loaded : Collection.SyntaxLoading.loadParsed? allocator
      (collectionSupport ⟨world, scope :: parents⟩) (read environment text) with
  | error reason => simp only [loaded] at stepped; contradiction
  | ok result =>
    cases result with
    | none => simp only [loaded] at stepped; contradiction
    | some result =>
      rcases result with ⟨next, token, value⟩
      obtain ⟨raw, parsed, copy⟩ := Collection.SyntaxLoading.loadParsed_isCopy loaded
      refine ⟨next, token, value, raw, rfl, parsed, copy, ?_⟩
      exact (Transition.silent.inj (by simpa only [loaded] using stepped)).symm

/-- The real source primitive result is generative; it is not equality with
the raw S-expression reader's result. All uses of a variable in the parsed
syntax share the same map. -/
theorem scope_parse_named_source {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (text destination : Atom) (older : List Goal) (environment : Environment)
    (after : ScopedCursor Context)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke "parse" [text] destination :: older)
    (resolved : resolve control.bindings = some environment)
    (stepped : scopeStep policy program (allocator, ⟨world, scope :: parents⟩) = .silent after) :
    ∃ next token value,
      Collection.SyntaxLoading.NamedParseResult
        (collectionSupport ⟨world, scope :: parents⟩) (read environment text) value ∧
      Collection.SyntaxLoading.loadParsed? allocator
        (collectionSupport ⟨world, scope :: parents⟩) (read environment text) = .ok (some (next, token, value)) ∧
      after = (next, ⟨world,
        {scope with frontier := primitiveWork control context origins destination older [value] ++ pending} :: parents⟩) := by
  obtain ⟨next, token, value, _, loaded, _, _, same⟩ :=
    scope_parse_silent_origin policy program allocator world scope parents control context origins pending
      text destination older environment after frontier atCall resolved stepped
  exact ⟨next, token, value, Collection.SyntaxLoading.loadParsed_named_result loaded, loaded, same⟩

/-- The allocator operation earns both the next result's identity provenance
and preservation of every previously represented world cell. -/
theorem scope_parse_world_represented {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (text destination : Atom) (older : List Goal) (environment : Environment)
    (after : ScopedCursor Context) (globals : List String)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke "parse" [text] destination :: older)
    (resolved : resolve control.bindings = some environment)
    (before : Collection.RepresentedWorld allocator globals world)
    (stepped : scopeStep policy program (allocator, ⟨world, scope :: parents⟩) = .silent after) :
    after.2.world = world ∧ Collection.RepresentedWorld after.1 globals after.2.world := by
  obtain ⟨next, token, value, _, loaded, _, _, same⟩ :=
    scope_parse_silent_origin policy program allocator world scope parents control context origins pending
      text destination older environment after frontier atCall resolved stepped
  obtain ⟨raw, _, allocated, _⟩ := Collection.SyntaxLoading.loadParsed_origin loaded
  obtain ⟨⟨handle, actual⟩, _⟩ := Collection.allocateCopy_origin allocated
  rw [same]
  exact ⟨rfl, Collection.represented_world_allocation actual before⟩

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination

/-! ## Collection freshness: a model counterexample

PeTTa renames every collected answer apart. For
`(let ($a $b) (collapse (superpose ($x $x))) (== $a $b))` the SWI reference
implementation prints `false`: the two components come from independently
renamed copies of `$x`. This model keeps one variable for the whole collected
list, so the same comparison returns `true`. The theorems record the model's
actual behaviour; they are a negative control for collection, not a target. -/

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.CollectionFreshness

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

private def program : SpaceSemantics.Program := { equations := [], declarations := [] }
private def collected : Atom := .expression [.symbol "collapse", .expression
  [.symbol "superpose", .expression [.var "x", .var "x"]]]

theorem source_collection_shares_across_answers :
    answers (advance program 8 (start Effects.empty collected)) =
      [.expression [.var "x", .var "x"]] := by
  with_unfolding_all rfl

private def compared : Atom := .expression [.symbol "let", .expression [.var "a", .var "b"],
  collected, .expression [.symbol "==", .var "a", .var "b"]]

theorem source_collection_ground_comparison :
    answers (advance program 32 (start Effects.empty compared)) = [Effects.boolean true] := by
  with_unfolding_all rfl

theorem source_does_not_match_independent_answer_comparison :
    answers (advance program 32 (start Effects.empty compared)) ≠ [Effects.boolean false] := by
  rw [source_collection_ground_comparison]
  decide

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.CollectionFreshness

/-!
## Complete ordered equation frontiers

The independent source decisions below account for every stored occurrence.
A refusal needs an incompatible head or a proof that the reached constraints
and fresh clause instance have no common finite-term solution. Selection
retains that same instance and its caller. The frontier judgment scans the
declared source positions; it never invokes the executable matcher or driver.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.ClauseChoice

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Equation Program)

/-- A complete decision at one physical equation position. Fresh spelling is
the declared source allocation policy; matching is the logical refinement
judgment, including its explicit no-solution case. -/
inductive Decision (program : Program) (control : Control) (head : String)
    (arguments : List Atom) (destination : Atom) (older : List Goal)
    (occurrence : Nat) : Option Control → Prop where
  | other (equation : Equation)
      (row : program.equations[occurrence]? = some equation)
      (different : equation.head ≠ head) :
      Decision program control head arguments destination older occurrence none
  | refused (equation : Equation)
      (row : program.equations[occurrence]? = some equation)
      (sameHead : equation.head = head)
      (incompatible : Refinement control.bindings (.expression (.symbol head :: arguments))
        (freshPattern control occurrence equation) none) :
      Decision program control head arguments destination older occurrence none
  | selected (equation : Equation) (bindings : Equations)
      (row : program.equations[occurrence]? = some equation)
      (sameHead : equation.head = head)
      (compatible : Refinement control.bindings (.expression (.symbol head :: arguments))
        (freshPattern control occurrence equation) (some bindings)) :
      Decision program control head arguments destination older occurrence
        (some { control with bindings := bindings, goals := .evaluate (freshBody control occurrence equation) destination :: older })

/-- A source scan keeps every accepted position in its original order.
Omitted positions carry an actual refusal, not merely a missing output. -/
inductive Frontier (program : Program) (control : Control) (head : String)
    (arguments : List Atom) (destination : Atom) (older : List Goal) :
    List Nat → List (Nat × Control) → Prop where
  | nil : Frontier program control head arguments destination older [] []
  | skip {occurrence : Nat} {remaining : List Nat} {answers : List (Nat × Control)}
      (decision : Decision program control head arguments destination older occurrence none)
      (rest : Frontier program control head arguments destination older remaining answers) :
      Frontier program control head arguments destination older (occurrence :: remaining) answers
  | keep {occurrence : Nat} {remaining : List Nat} {next : Control}
      {answers : List (Nat × Control)}
      (decision : Decision program control head arguments destination older occurrence (some next))
      (rest : Frontier program control head arguments destination older remaining answers) :
      Frontier program control head arguments destination older
        (occurrence :: remaining) ((occurrence, next) :: answers)

theorem decision_iff_trial (program : Program) (control : Control) (head : String)
    (arguments : List Atom) (destination : Atom) (older : List Goal)
    (occurrence : Nat) (bound : occurrence < program.equations.length) (result : Option Control) :
    Decision program control head arguments destination older occurrence result ↔
      trial program control head arguments destination older occurrence = result := by
  have row : program.equations[occurrence]? = some program.equations[occurrence] :=
    List.getElem?_eq_getElem bound
  constructor
  · intro source
    cases source with
    | other equation actual different =>
        simp only [trial, actual]
        exact wrong_head_not_selected control head arguments destination older occurrence equation different
    | refused equation actual sameHead incompatible =>
        simp only [trial, actual]
        exact (attempt_refused_iff control head arguments destination older occurrence equation sameHead).mpr incompatible
    | selected equation bindings actual sameHead compatible =>
        simp only [trial, actual]
        exact (attempt_iff control head arguments destination older occurrence equation sameHead _).mpr
          ⟨bindings, compatible, rfl⟩
  · intro computed
    simp only [trial, row] at computed
    change attempt control head arguments destination older occurrence _ = result at computed
    by_cases sameHead : program.equations[occurrence].head = head
    · cases result with
      | none =>
          exact .refused _ row sameHead
            ((attempt_refused_iff control head arguments destination older occurrence _ sameHead).mp computed)
      | some next =>
          obtain ⟨bindings, compatible, rfl⟩ :=
            (attempt_iff control head arguments destination older occurrence _ sameHead next).mp computed
          exact .selected _ bindings row sameHead compatible
    · rw [wrong_head_not_selected control head arguments destination older occurrence _ sameHead] at computed
      cases computed
      exact .other _ row sameHead

theorem frontier_iff_scan (program : Program) (control : Control) (head : String)
    (arguments : List Atom) (destination : Atom) (older : List Goal)
    (positions : List Nat) (valid : ∀ occurrence ∈ positions, occurrence < program.equations.length)
    (answers : List (Nat × Control)) :
    Frontier program control head arguments destination older positions answers ↔
      positions.filterMap (fun occurrence =>
        (trial program control head arguments destination older occurrence).map (occurrence, ·)) = answers := by
  induction positions generalizing answers with
  | nil =>
      constructor
      · intro source; cases source; rfl
      · intro same; cases same; exact .nil
  | cons occurrence remaining ih =>
      have bound := valid occurrence List.mem_cons_self
      have restValid : ∀ index ∈ remaining, index < program.equations.length :=
        fun index member => valid index (List.mem_cons_of_mem _ member)
      constructor
      · intro source
        cases source with
        | skip decision rest =>
            have actual := (decision_iff_trial program control head arguments destination older
              occurrence bound none).mp decision
            simpa only [List.filterMap_cons, actual, Option.map_none] using (ih restValid _).mp rest
        | keep decision rest =>
            have actual := (decision_iff_trial program control head arguments destination older
              occurrence bound _).mp decision
            simpa only [List.filterMap_cons, actual, Option.map_some] using
              congrArg ((occurrence, _) :: ·) ((ih restValid _).mp rest)
      · intro same
        cases actual : trial program control head arguments destination older occurrence with
        | none =>
            simp only [List.filterMap_cons, actual, Option.map_none] at same
            exact .skip ((decision_iff_trial program control head arguments destination older
              occurrence bound none).mpr actual) ((ih restValid _).mpr same)
        | some next =>
            simp only [List.filterMap_cons, actual, Option.map_some] at same
            cases same
            exact .keep ((decision_iff_trial program control head arguments destination older
              occurrence bound (some next)).mpr actual) ((ih restValid _).mpr rfl)

/-- The entire executable frontier, including order and duplicate occurrences,
is equivalent to independently justified source coverage. -/
theorem choices_iff_frontier (program : Program) (control : Control) (head : String)
    (arguments : List Atom) (destination : Atom) (older : List Goal)
    (answers : List (Nat × Control)) :
    choices program control head arguments destination older = answers ↔
      Frontier program control head arguments destination older
        (List.range program.equations.length) answers := by
  exact (frontier_iff_scan program control head arguments destination older _
    (fun _ member => List.mem_range.mp member) answers).symm

theorem Frontier.occurrences {program : Program} {control : Control} {head : String}
    {arguments : List Atom} {destination : Atom} {older : List Goal}
    {positions : List Nat} {answers : List (Nat × Control)}
    (source : Frontier program control head arguments destination older positions answers) :
    (answers.map Prod.fst).Sublist positions := by
  induction source with
  | nil => exact .slnil
  | skip _ _ ih => exact .cons _ ih
  | keep _ _ ih => exact .cons_cons _ ih

/-- Completed empty search requires refusal at every source position. -/
theorem Frontier.empty_iff (program : Program) (control : Control) (head : String)
    (arguments : List Atom) (destination : Atom) (older : List Goal) (positions : List Nat) :
    Frontier program control head arguments destination older positions [] ↔
      ∀ occurrence ∈ positions,
        Decision program control head arguments destination older occurrence none := by
  induction positions with
  | nil =>
      constructor
      · intro _; simp
      · intro _; exact .nil
  | cons occurrence remaining ih =>
      constructor
      · intro source
        cases source with
        | skip decision rest =>
            intro index member
            rcases List.mem_cons.mp member with rfl | member
            · exact decision
            · exact ih.mp rest index member
      · intro refused
        exact .skip (refused occurrence List.mem_cons_self)
          (ih.mpr (fun index member => refused index (List.mem_cons_of_mem _ member)))

/-- No reordering or duplicate source identity can be introduced by a complete
frontier. Equal payloads may still occupy distinct accepted positions. -/
theorem choices_ordered (program : Program) (control : Control) (head : String)
    (arguments : List Atom) (destination : Atom) (older : List Goal) :
    ((choices program control head arguments destination older).map Prod.fst).Pairwise (· < ·) := by
  have source := (choices_iff_frontier program control head arguments destination older _).mp rfl
  exact List.pairwise_lt_range.sublist source.occurrences

/-- A completed empty frontier is justified by a refusal at every stored row. -/
theorem choices_empty_iff (program : Program) (control : Control) (head : String)
    (arguments : List Atom) (destination : Atom) (older : List Goal) :
    choices program control head arguments destination older = [] ↔
      ∀ occurrence < program.equations.length,
        Decision program control head arguments destination older occurrence none := by
  rw [choices_iff_frontier, Frontier.empty_iff]
  simp only [List.mem_range]

/-- Complete source scans agree as lists, including occurrences and reached
constraints. This does not identify different fresh-name policies literally. -/
theorem Frontier.unique {program : Program} {control : Control} {head : String}
    {arguments : List Atom} {destination : Atom} {older : List Goal}
    {positions : List Nat} {first second : List (Nat × Control)}
    (valid : ∀ occurrence ∈ positions, occurrence < program.equations.length)
    (left : Frontier program control head arguments destination older positions first)
    (right : Frontier program control head arguments destination older positions second) :
    first = second :=
  ((frontier_iff_scan program control head arguments destination older positions valid first).mp left).symm.trans
    ((frontier_iff_scan program control head arguments destination older positions valid second).mp right)

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.ClauseChoice


namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- An actual ordinary invocation installs its complete source frontier ahead
of older work. Every child retains the reached caller and its source origin;
selection does not alter the shared world or consume an answer-copy identity. -/
theorem scope_equation_frontier {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (environment : Environment)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke head arguments destination :: older)
    (ordinary : (Eval.ioHead head || StdLib.known head) = false)
    (declared : program.equations.any (·.head == head) = true)
    (resolved : resolve control.bindings = some environment) :
    let boundary := collectionSupport (⟨world, scope :: parents⟩ : CollectionConfiguration Context)
    let selected := ClauseChoice.choices program (protectControl control boundary) head
      (arguments.map (read environment)) destination older
    ClauseChoice.Frontier program (protectControl control boundary) head
      (arguments.map (read environment)) destination older
      (List.range program.equations.length) selected ∧
    scopeStep policy program (allocator, ⟨world, scope :: parents⟩) =
      .silent (allocator, ⟨world,
        {scope with frontier := selected.map (fun row => (predicateEntry pending.length row.2, context, origins ++ [row.1])) ++ pending} :: parents⟩) := by
  dsimp only
  have entered := enterEquations_constructs program world scope parents control context origins pending
    head arguments destination older environment frontier atCall ordinary declared resolved
  have notPrint : head ≠ "println!" := by
    intro same; subst head; simp [Eval.ioHead] at ordinary
  have notParse : head ≠ "parse" := by
    intro same; subst head; simp [StdLib.known] at ordinary
  have notPrimitive : StdLib.known head = false := (Bool.or_eq_false_iff.mp ordinary).2
  have invoked := invoke_request_step policy program (⟨world, control, context⟩ : Cursor Context)
    head arguments destination older atCall notPrint resolved
  refine ⟨(ClauseChoice.choices_iff_frontier _ _ _ _ _ _ _).mp rfl, ?_⟩
  simp only [scopeStep, frontier, enterCollapse?, atCall, enterSuperpose?, invoked,
    installChild, scopedInvocation, notParse, notPrimitive, Bool.false_eq_true,
    ↓reduceIte, entered, equationWork]

/-- Reflection of ordinary invocation recovers a complete source scan, rather
than only per-child membership evidence. The reached configuration itself
fixes all older work and the unchanged world. -/
theorem scope_equation_frontier_iff {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (environment : Environment)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke head arguments destination :: older)
    (ordinary : (Eval.ioHead head || StdLib.known head) = false)
    (declared : program.equations.any (·.head == head) = true)
    (resolved : resolve control.bindings = some environment)
    (selected : List (Nat × Control)) :
    let boundary := collectionSupport (⟨world, scope :: parents⟩ : CollectionConfiguration Context)
    ClauseChoice.Frontier program (protectControl control boundary) head
      (arguments.map (read environment)) destination older
      (List.range program.equations.length) selected ↔
    scopeStep policy program (allocator, ⟨world, scope :: parents⟩) =
      .silent (allocator, ⟨world,
        {scope with frontier := selected.map (fun row => (predicateEntry pending.length row.2, context, origins ++ [row.1])) ++ pending} :: parents⟩) := by
  dsimp only
  have actual := (scope_equation_frontier policy program allocator world scope parents control context
    origins pending head arguments destination older environment frontier atCall ordinary declared resolved).2
  constructor
  · intro source
    have exactChoices := (ClauseChoice.choices_iff_frontier _ _ _ _ _ _ selected).mpr source
    simpa only [exactChoices] using actual
  · intro reached
    have same := congrArg (fun result => match result with
      | .silent (next : ScopedCursor Context) => next.2.scopes.head?.map (fun (current : CollectionScope Context) => current.frontier)
      | _ => none) (actual.symm.trans reached)
    simp only [List.head?_cons, Option.map_some, Option.some.injEq] at same
    have mapped := List.append_cancel_right same
    have injective : Function.Injective (fun row : Nat × Control =>
        (predicateEntry pending.length row.2, context, origins ++ [row.1])) := by
      rintro ⟨first, left⟩ ⟨second, right⟩ equal
      simp only [Prod.mk.injEq] at equal
      exact Prod.ext (List.singleton_inj.mp (List.append_cancel_left equal.2.2))
        (predicateEntry_injective pending.length equal.1)
    have selectedEq := (List.map_inj_right (fun _ _ same => injective same)).mp mapped
    exact (ClauseChoice.choices_iff_frontier _ _ _ _ _ _ selected).mp selectedEq

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.ClauseChoice

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program)

/-- A certified applicable source occurrence cannot be discarded by a
completed frontier, including when another occurrence has the same payload. -/
theorem selected_cannot_be_omitted {program : Program} {control : Control} {head : String}
    {arguments : List Atom} {destination : Atom} {older : List Goal}
    {occurrence : Nat} {equation : SpaceSemantics.Equation} {next : Control}
    {answers : List (Nat × Control)}
    (row : program.equations[occurrence]? = some equation)
    (selected : Selection program control head arguments destination older occurrence
      (freshPattern control occurrence equation) (freshBody control occurrence equation) next)
    (missing : (occurrence, next) ∉ answers) :
    ¬Frontier program control head arguments destination older
      (List.range program.equations.length) answers := by
  intro source
  have member := (choices_source_iff program control head arguments destination older occurrence next).mpr
    ⟨equation, row, selected⟩
  rw [(choices_iff_frontier program control head arguments destination older answers).mpr source] at member
  exact missing member

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.ClauseChoice

/-! ## Depth-first divergence with retained alternatives -/

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.DFSLoop

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- One genuine recursive equation, with no effect or primitive request. -/
def term : Atom := .expression [.symbol "dfs-loop"]

def program : SpaceSemantics.Program :=
  {equations := [{head := "dfs-loop", arguments := [], body := term}], declarations := []}

/-- The active recursive call precedes the same saved siblings and parents.
The invariant admits arbitrary solvable caller equations and caller scopes. -/
def Active {Context : Type} (allocator : Allocator) (world : World)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (pending : List (CollectionWork Context)) (destination : Atom) (older : List Goal)
    (source : ScopedCursor Context) : Prop :=
  ∃ control context origins,
    source = (allocator, ⟨world, {scope with frontier := (control, context, origins) :: pending} :: parents⟩) ∧
    (∃ saved : List Nat,
      control.goals = .invoke "dfs-loop" [] destination :: saved.map Goal.restoreCommit ++ older ∨
      control.goals = .evaluate term destination :: saved.map Goal.restoreCommit ++ older) ∧
    ∃ environment, Solves environment control.bindings

/-- The recursive head always takes a real source step, with no publication.
Later alternatives and all collection boundaries stay saved. -/
theorem progress {Context : Type} (policy : Policy)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (pending : List (CollectionWork Context))
    (destination : Atom) (older : List Goal) (source : ScopedCursor Context)
    (active : Active allocator world scope parents pending destination older source) :
    ∃ next, scopeStep policy program source = .silent next ∧
      Active allocator world scope parents pending destination older next := by
  obtain ⟨control, context, origins, rfl, ⟨saved,location⟩, model, solves⟩ := active
  rcases location with atCall | atBody
  · let boundary := collectionSupport (⟨world,
      {scope with frontier := (control, context, origins) :: pending} :: parents⟩ : CollectionConfiguration Context)
    let bindings := control.bindings ++ [(term, term)]
    let nextControl : Control :=
      {protectControl control boundary with
        bindings := bindings
        goals := .evaluate term destination :: saved.map Goal.restoreCommit ++ older}
    have accepted : refine control.bindings term term = some bindings :=
      (refine_iff control.bindings bindings term term).mpr ⟨rfl, model, solves, rfl⟩
    obtain ⟨environment, resolved⟩ := resolve_complete ⟨model, solves⟩
    simp only [term] at accepted
    have selected : ClauseChoice.choices program (protectControl control boundary)
        "dfs-loop" [] destination (saved.map Goal.restoreCommit ++ older) = [(0, nextControl)] := by
      simp [ClauseChoice.choices, ClauseChoice.trial, ClauseChoice.attempt,
        ClauseChoice.freshPattern, ClauseChoice.freshBody, ClauseChoice.pattern,
        program, term, renameTypeVars, protectControl, accepted, nextControl,
        List.range_succ]
    have stepped := (scope_equation_frontier policy program allocator world
      {scope with frontier := (control, context, origins) :: pending} parents control context origins
      pending "dfs-loop" [] destination (saved.map Goal.restoreCommit ++ older) environment rfl atCall
      (by decide) (by decide) resolved).2
    change scopeStep policy program _ = .silent (allocator, ⟨world, {scope with frontier :=
      ((ClauseChoice.choices program (protectControl control boundary) "dfs-loop" [] destination
        (saved.map Goal.restoreCommit ++ older)).map
          (fun row => (predicateEntry pending.length row.2, context, origins ++ [row.1])) ++ pending)} :: parents⟩) at stepped
    rw [selected] at stepped
    refine ⟨_, stepped, predicateEntry pending.length nextControl, context, origins ++ [0], ?_,
      ⟨control.cutBoundary :: saved,Or.inr ?_⟩,model,?_⟩
    · rfl
    · simp [predicateEntry,nextControl,protectControl]
    · intro pair member
      rcases List.mem_append.mp member with previous | added
      · exact solves pair previous
      · cases List.mem_singleton.mp added
        rfl
  · let nextControl : Control := {control with goals := .invoke "dfs-loop" [] destination :: saved.map Goal.restoreCommit ++ older}
    have prepared : prepare policy program control term destination (saved.map Goal.restoreCommit ++ older) = nextControl := by
      cases policy <;> simp [prepare, term, callable, program, Eval.ioHead, StdLib.known,
        callArguments, freshSlots, replace, nextControl]
    refine ⟨(allocator, ⟨world, {scope with frontier := (nextControl, context, origins) :: pending} :: parents⟩),
      ?_, nextControl, context, origins, rfl, ⟨saved,Or.inl rfl⟩, model, solves⟩
    simp only [scopeStep, enterCollapse?, atBody, enterSuperpose?, machine,
      installChild, retainChild]
    change (.silent (allocator, ⟨world, {scope with frontier :=
      (prepare policy program control term destination (saved.map Goal.restoreCommit ++ older), context, origins) :: pending} :: parents⟩) :
        Mettapedia.GSLT.Distinction.ProductiveBlocks.Transition (ScopedCursor Context) CollectedAnswer
          (ScopedCursor Context) ScopeBoundary) = _
    rw [prepared]

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.DFSLoop

/-!
## Independent local body expansion

These judgments describe the ordinary goal component. The enclosing scope
rules license entry: collapse, superpose and empty are handled at their own
boundaries before this component is called. Local expansion creates pending
work, never a recursively evaluated child result.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.Source

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open SpaceSemantics (Program)

/-- Lexical forms expanded before ordinary fixed-head applications. -/
def lexicalForm : Atom → Bool
  | .expression [.symbol "quote", _]
  | .expression [.symbol "let", _, _, _]
  | .expression [.symbol "cut"]
  | .expression [.symbol "if", _, _]
  | .expression [.symbol "if", _, _, _]
  | .expression [.symbol "once", _] => true
  | _ => false

/-- A syntax-directed worklist rule, independent of `prepare`, the branch
step function and the runner. Local demand/scheduling policies are shared
finite operations; no child evaluation is a premise or callback. -/
inductive Prepared (policy : Policy) (program : Program) (control : Control)
    (destination : Atom) (older : List Goal) : Atom → Control → Prop where
  | variableValue (name : String) :
      Prepared policy program control destination older (.var name)
        (replace control (.equate (.var name) destination :: older))
  | symbol (name : String) :
      Prepared policy program control destination older (.symbol name)
        (replace control (.equate (.symbol name) destination :: older))
  | grounded (value : GroundedValue) :
      Prepared policy program control destination older (.grounded value)
        (replace control (.equate (.grounded value) destination :: older))
  | quotation (value : Atom) :
      Prepared policy program control destination older (.expression [.symbol "quote", value])
        (replace control (.equate value destination :: older))
  | binding (pattern producer body : Atom) :
      Prepared policy program control destination older (.expression [.symbol "let", pattern, producer, body])
        (replace control (letGoals policy program pattern producer body destination
          (.var (freshName control 0)) ++ older))
  | cut :
      Prepared policy program control destination older (.expression [.symbol "cut"])
        (replace control (.commit :: .equate (Effects.boolean true) destination :: older))
  | once (child : Atom) :
      Prepared policy program control destination older (.expression [.symbol "once",child])
        (replace control (.openCommit :: .evaluate child destination :: .commit ::
          .restoreCommit control.cutBoundary :: older))
  | conditional (condition yes no : Atom) :
      Prepared policy program control destination older (.expression [.symbol "if", condition, yes, no])
        (replace control (.evaluate condition (.var (freshName control 0)) ::
          .branch (.var (freshName control 0)) yes no destination :: older))
  | conditionalWithoutElse (condition yes : Atom) :
      Prepared policy program control destination older (.expression [.symbol "if", condition, yes])
        (replace control (.evaluate condition (.var (freshName control 0)) ::
          .branch (.var (freshName control 0)) yes (.expression [.symbol "empty"]) destination :: older))
  | application (head : String) (arguments : List Atom)
      (ordinary : lexicalForm (.expression (.symbol head :: arguments)) = false)
      (declared : callable program head = true) :
      Prepared policy program control destination older (.expression (.symbol head :: arguments))
        (replace control (((callArguments program head arguments (freshSlots control arguments.length)).1 ++
          [.invoke head (callArguments program head arguments (freshSlots control arguments.length)).2 destination]) ++ older))
  | construction (head : String) (arguments : List Atom)
      (ordinary : lexicalForm (.expression (.symbol head :: arguments)) = false)
      (data : callable program head = false) :
      Prepared policy program control destination older (.expression (.symbol head :: arguments))
        (replace control ((match policy with
          | .relational => .equate (.expression (.symbol head :: freshSlots control arguments.length)) destination ::
              (arguments.zip (freshSlots control arguments.length)).map (fun row => .evaluate row.1 row.2)
          | .eagerValue => (arguments.zip (freshSlots control arguments.length)).map (fun row => .evaluate row.1 row.2) ++
              [.equate (.expression (.symbol head :: freshSlots control arguments.length)) destination]) ++ older))
  | tuple (children : List Atom)
      (noHead : ∀ head arguments, children ≠ .symbol head :: arguments) :
      Prepared policy program control destination older (.expression children)
        (replace control (dataGoals policy children (freshSlots control children.length) destination ++ older))

/-- Every independent expansion has the stated executable continuation,
with all incoming equations and the root destination retained. -/
theorem Prepared.execution {policy : Policy} {program : Program} {control : Control}
    {destination : Atom} {older : List Goal} {expression : Atom} {next : Control}
    (source : Prepared policy program control destination older expression next) :
    prepare policy program control expression destination older = next := by
  cases source with
  | variableValue _ => rfl
  | symbol _ => rfl
  | grounded _ => rfl
  | quotation _ => rfl
  | binding _ _ _ => rfl
  | cut => rfl
  | once _ => rfl
  | conditional _ _ _ => rfl
  | conditionalWithoutElse _ _ => rfl
  | application head arguments ordinary declared =>
      unfold prepare
      split <;> simp_all [lexicalForm, replace, List.append_assoc]
      all_goals
        rename_i _ children noHead same
        exact (noHead head arguments same.symm).elim
  | construction head arguments ordinary data =>
      unfold prepare
      split <;> simp_all [lexicalForm, replace]
      all_goals
        rename_i _ children noHead same
        exact (noHead head arguments same.symm).elim
  | tuple children noHead =>
      unfold prepare
      split <;> simp_all [replace]

/-- Reflection is by the source syntax, not by an assumed evaluator result. -/
theorem prepare_has_source (policy : Policy) (program : Program) (control : Control)
    (expression destination : Atom) (older : List Goal) :
    Prepared policy program control destination older expression
      (prepare policy program control expression destination older) := by
  unfold prepare
  split
  · exact .variableValue _
  · exact .symbol _
  · exact .grounded _
  · exact .quotation _
  · exact .binding _ _ _
  · exact .cut
  · exact .once _
  · exact .conditional _ _ _
  · exact .conditionalWithoutElse _ _
  · split
    · apply Prepared.application
      · unfold lexicalForm
        split <;> simp_all
      · assumption
    · apply Prepared.construction
      · unfold lexicalForm
        split <;> simp_all
      · simpa using ‹¬callable program _ = true›
  · apply Prepared.tuple
    intro head arguments same
    subst same
    simp_all

/-- Exact source/continuation correspondence for arbitrary incoming bindings,
source expressions and surrounding goal suffixes. -/
theorem prepare_iff_source (policy : Policy) (program : Program) (control : Control)
    (expression destination : Atom) (older : List Goal) (next : Control) :
    prepare policy program control expression destination older = next ↔
      Prepared policy program control destination older expression next := by
  constructor
  · rintro rfl
    exact prepare_has_source policy program control expression destination older
  · exact Prepared.execution

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.Source


namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.Source

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program)
open Mettapedia.GSLT.Distinction.ProductiveBlocks

abbrev Action (Context : Type) :=
  Mettapedia.GSLT.Distinction.ProductiveBlocks.Transition
    (Cursor Context) Empty (Result × Cursor Context) Boundary

/-- These forms own a scope boundary, before ordinary local expansion. -/
def scopedForm : Atom → Bool
  | .expression [.symbol "collapse", _]
  | .expression [.symbol "superpose", .expression _]
  | .expression [.symbol "empty"] => true
  | _ => false

/-- Entry to the local component is licensed by the active goal, not by an
arbitrary syntax position. Older goals remain saved until their own entry. -/
inductive Licensed (control : Control) : Prop where
  | ended (atEnd : control.goals = []) : Licensed control
  | evaluation (expression destination : Atom) (older : List Goal)
      (atGoal : control.goals = .evaluate expression destination :: older)
      (ordinary : scopedForm expression = false) : Licensed control
  | equation (value destination : Atom) (older : List Goal)
      (atGoal : control.goals = .equate value destination :: older) : Licensed control
  | conditional (condition yes no destination : Atom) (older : List Goal)
      (atGoal : control.goals = .branch condition yes no destination :: older) : Licensed control
  | argument (value destination : Atom) (depth : Nat) (remaining : List Goal)
      (atGoal : control.goals = .argumentReturn value destination depth :: remaining) : Licensed control
  | invocation (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
      (atGoal : control.goals = .invoke head arguments destination :: older) : Licensed control
  | querying (location pattern template destination : Atom) (older : List Goal)
      (atGoal : control.goals = .query location pattern template destination :: older) : Licensed control
  | opening (older : List Goal) (atGoal : control.goals = .openCommit :: older) : Licensed control
  | committing (older : List Goal) (atGoal : control.goals = .commit :: older) : Licensed control
  | restoring (boundary : Nat) (older : List Goal)
      (atGoal : control.goals = .restoreCommit boundary :: older) : Licensed control

/-- Return, conditional selection, invocation and end-of-branch inspect a solved presentation.
The finite-term solver is the existing proved logical operation. -/
inductive ReadSite (control : Control) : Prop where
  | ended (atEnd : control.goals = []) : ReadSite control
  | conditional (condition yes no destination : Atom) (older : List Goal)
      (atGoal : control.goals = .branch condition yes no destination :: older) : ReadSite control
  | argument (value destination : Atom) (depth : Nat) (remaining : List Goal)
      (atGoal : control.goals = .argumentReturn value destination depth :: remaining) : ReadSite control
  | invocation (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
      (atGoal : control.goals = .invoke head arguments destination :: older) : ReadSite control
  | querying (location pattern template destination : Atom) (older : List Goal)
      (atGoal : control.goals = .query location pattern template destination :: older) : ReadSite control

/-- Independent local branch rules. No constructor calls the branch stepper,
runner, or a recursive language evaluator. Requests retain the entire cursor;
failed refinement is a branch refusal with its reached world. -/
inductive Step {Context : Type} (policy : Policy) (program : Program)
    (cursor : Cursor Context) : Action Context → Prop where
  | opening (older : List Goal) (atGoal : cursor.control.goals = .openCommit :: older) :
      Step policy program cursor (.call .openCommit cursor)
  | committing (older : List Goal) (atGoal : cursor.control.goals = .commit :: older) :
      Step policy program cursor (.call (.commit cursor.control.cutBoundary) cursor)
  | querying (location pattern template destination : Atom) (older : List Goal) (environment : Environment)
      (atGoal : cursor.control.goals = .query location pattern template destination :: older)
      (resolved : resolve cursor.control.bindings = some environment) :
      Step policy program cursor (.call (.query (read environment location) pattern template destination) cursor)
  | restoring (boundary : Nat) (older : List Goal)
      (atGoal : cursor.control.goals = .restoreCommit boundary :: older) :
      Step policy program cursor
        (.silent {cursor with control := {cursor.control with goals := older,cutBoundary := boundary}})
  | expanded (expression destination : Atom) (older : List Goal) (next : Control)
      (atGoal : cursor.control.goals = .evaluate expression destination :: older)
      (ordinary : scopedForm expression = false)
      (source : Prepared policy program cursor.control destination older expression next) :
      Step policy program cursor (.silent {cursor with control := next})
  | accepted (value destination : Atom) (older : List Goal) (after : Equations)
      (atGoal : cursor.control.goals = .equate value destination :: older)
      (source : Refinement cursor.control.bindings value destination (some after)) :
      Step policy program cursor (.silent {cursor with control := {cursor.control with bindings := after, goals := older}})
  | refused (value destination : Atom) (older : List Goal)
      (atGoal : cursor.control.goals = .equate value destination :: older)
      (source : Refinement cursor.control.bindings value destination none) :
      Step policy program cursor (.finish (.noValue cursor.control.bindings, cursor))
  | returned (environment : Environment) (atEnd : cursor.control.goals = [])
      (resolved : resolve cursor.control.bindings = some environment) :
      Step policy program cursor
        (.finish (.value (read environment cursor.control.destination) cursor.control.bindings, cursor))
  | conditional (condition yes no destination : Atom) (older : List Goal) (environment : Environment)
      (atGoal : cursor.control.goals = .branch condition yes no destination :: older)
      (resolved : resolve cursor.control.bindings = some environment) :
      Step policy program cursor (.silent {cursor with control := (replace cursor.control
        (.evaluate (if read environment condition == Effects.boolean true then yes else no) destination :: older))})
  | inconsistent (site : ReadSite cursor.control)
      (noSolution : ¬∃ environment, Solves environment cursor.control.bindings) :
      Step policy program cursor (.call .invalidEnvironment cursor)
  | argument (value destination : Atom) (younger older : List Goal) (action : Action Context)
      (atGoal : cursor.control.goals = .argumentReturn value destination older.length :: younger ++ older)
      (source : ArgumentReturn cursor value destination younger older action) :
      Step policy program cursor action
  | invalidDelimiter (value destination : Atom) (depth : Nat) (remaining : List Goal)
      (environment : Environment)
      (atGoal : cursor.control.goals = .argumentReturn value destination depth :: remaining)
      (tooShort : remaining.length < depth)
      (resolved : resolve cursor.control.bindings = some environment) :
      Step policy program cursor (.call (.invalidDelimiter depth remaining.length) cursor)
  | printed (arguments : List Atom) (destination : Atom) (older : List Goal)
      (environment : Environment) (value : Atom)
      (atGoal : cursor.control.goals = .invoke "println!" arguments destination :: older)
      (resolved : resolve cursor.control.bindings = some environment)
      (readout : arguments.map (read environment) = [value]) :
      Step policy program cursor (.silent
        ⟨{cursor.world with output := cursor.world.output ++ [value]},
          replace cursor.control (.equate (Effects.boolean true) destination :: older), cursor.context⟩)
  | requested (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
      (environment : Environment)
      (atGoal : cursor.control.goals = .invoke head arguments destination :: older)
      (resolved : resolve cursor.control.bindings = some environment)
      (notPrint : ∀ value, head = "println!" → arguments.map (read environment) ≠ [value]) :
      Step policy program cursor (.call (.invoke head (arguments.map (read environment)) destination) cursor)

/-- Soundness covers the complete reached cursor, including context and world. -/
theorem Step.execution {Context : Type} {policy : Policy} {program : Program}
    {cursor : Cursor Context} {action : Action Context} (source : Step policy program cursor action) :
    (machine policy program).step cursor = some action := by
  cases source with
  | opening _ atGoal | committing _ atGoal | restoring _ _ atGoal => simp only [machine,atGoal]
  | querying location pattern template destination older environment atGoal resolved => simp only [machine,atGoal,resolved]
  | expanded expression destination older next atGoal _ source =>
      simp only [machine, atGoal, source.execution]
  | accepted value destination older after atGoal source =>
      simp only [machine, atGoal, (refinement_iff _ _ _ _).mp source]
  | refused value destination older atGoal source =>
      simp only [machine, atGoal, (refinement_iff _ _ _ _).mp source]
  | returned environment atEnd resolved => simp only [machine, atEnd, resolved]
  | conditional condition yes no destination older environment atGoal resolved =>
      simp only [machine, atGoal, resolved]
  | inconsistent site noSolution =>
      have invalid := (resolve_none_iff _).mpr noSolution
      cases site <;> simp_all only [machine]
  | argument value destination younger older action atGoal source =>
      exact argumentReturn_source_step policy program cursor value destination younger older atGoal source
  | invalidDelimiter value destination depth remaining environment atGoal tooShort resolved =>
      simp [machine, atGoal, resolved, callerSuffix?, Nat.not_le.mpr tooShort]
  | printed arguments destination older environment value atGoal resolved readout =>
      simp only [machine, atGoal, resolved, readout]
  | requested head arguments destination older environment atGoal resolved notPrint =>
      simp only [machine, atGoal, resolved]

/-- Every licensed inspection is justified by the source rules. The proof
constructs refinements, delimiter splits and requests at the actual reached
state; an unavailable response never becomes a completed answer. -/
theorem step_has_source {Context : Type} (policy : Policy) (program : Program)
    (cursor : Cursor Context) (licensed : Licensed cursor.control) :
    ∃ action, Step policy program cursor action ∧ (machine policy program).step cursor = some action := by
  classical
  cases licensed with
  | querying location pattern template destination older atGoal =>
      cases resolved : resolve cursor.control.bindings with
      | none => exact ⟨_, .inconsistent (.querying location pattern template destination older atGoal)
          ((resolve_none_iff _).mp resolved), by simp only [machine, atGoal, resolved]⟩
      | some environment => exact ⟨_, .querying location pattern template destination older environment atGoal resolved,
          by simp only [machine, atGoal, resolved]⟩
  | opening older atGoal => exact ⟨_,.opening older atGoal,by simp only [machine,atGoal]⟩
  | committing older atGoal => exact ⟨_,.committing older atGoal,by simp only [machine,atGoal]⟩
  | restoring boundary older atGoal => exact ⟨_,.restoring boundary older atGoal,by simp only [machine,atGoal]⟩
  | ended atEnd =>
      cases resolved : resolve cursor.control.bindings with
      | none =>
          refine ⟨_, .inconsistent (.ended atEnd) ((resolve_none_iff _).mp resolved), ?_⟩
          simp only [machine, atEnd, resolved]
      | some environment =>
          exact ⟨_, .returned environment atEnd resolved, by simp only [machine, atEnd, resolved]⟩
  | evaluation expression destination older atGoal ordinary =>
      exact ⟨_, .expanded expression destination older _ atGoal ordinary
        (prepare_has_source policy program cursor.control expression destination older),
        by simp only [machine, atGoal]⟩
  | equation value destination older atGoal =>
      cases refined : refine cursor.control.bindings value destination with
      | none =>
          exact ⟨_, .refused value destination older atGoal ((refinement_iff _ _ _ _).mpr refined),
            by simp only [machine, atGoal, refined]⟩
      | some after =>
          exact ⟨_, .accepted value destination older after atGoal ((refinement_iff _ _ _ _).mpr refined),
            by simp only [machine, atGoal, refined]⟩
  | conditional condition yes no destination older atGoal =>
      cases resolved : resolve cursor.control.bindings with
      | none =>
          exact ⟨_, .inconsistent (.conditional condition yes no destination older atGoal)
            ((resolve_none_iff _).mp resolved), by simp only [machine, atGoal, resolved]⟩
      | some environment =>
          exact ⟨_, .conditional condition yes no destination older environment atGoal resolved,
            by simp only [machine, atGoal, resolved]⟩
  | argument value destination depth remaining atGoal =>
      by_cases valid : depth ≤ remaining.length
      · let older := remaining.drop (remaining.length - depth)
        let younger := remaining.take (remaining.length - depth)
        have width : older.length = depth := by simp only [older, List.length_drop]; omega
        have partition : younger ++ older = remaining := by simp only [younger, older, List.take_append_drop]
        have atSplit : cursor.control.goals =
            .argumentReturn value destination older.length :: younger ++ older := by
          simpa only [List.cons_append, width, partition] using atGoal
        obtain ⟨action, actual⟩ : ∃ action, (machine policy program).step cursor = some action := ⟨_, rfl⟩
        exact ⟨action, .argument value destination younger older action atSplit
          (argumentReturn_step_source policy program cursor value destination younger older atSplit actual), actual⟩
      · cases resolved : resolve cursor.control.bindings with
        | none =>
            refine ⟨_, .inconsistent (.argument value destination depth remaining atGoal)
              ((resolve_none_iff _).mp resolved), ?_⟩
            simp only [machine, atGoal, resolved]
        | some environment =>
            refine ⟨_, .invalidDelimiter value destination depth remaining environment atGoal
              (by omega) resolved, ?_⟩
            simp [machine, atGoal, resolved, callerSuffix?, valid]
  | invocation head arguments destination older atGoal =>
      cases resolved : resolve cursor.control.bindings with
      | none =>
          refine ⟨_, .inconsistent (.invocation head arguments destination older atGoal)
            ((resolve_none_iff _).mp resolved), ?_⟩
          simp only [machine, atGoal, resolved]
      | some environment =>
          by_cases printing : ∃ value, head = "println!" ∧ arguments.map (read environment) = [value]
          · obtain ⟨value, rfl, readout⟩ := printing
            exact ⟨_, .printed arguments destination older environment value atGoal resolved readout,
              by simp only [machine, atGoal, resolved, readout]⟩
          · have notPrint : ∀ value, head = "println!" → arguments.map (read environment) ≠ [value] := by
              intro value same sameArgs
              exact printing ⟨value, same, sameArgs⟩
            refine ⟨_, .requested head arguments destination older environment atGoal resolved notPrint, ?_⟩
            simp only [machine, atGoal, resolved]

/-- A successful source return retains its reached cursor and equations.
The destination readout is earned by the actual solved presentation. -/
theorem Step.returned_iff {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (cursor reached : Cursor Context) (value : Atom) (bindings : Equations) :
    Step policy program cursor (.finish (.value value bindings, reached)) ↔
      reached = cursor ∧ bindings = cursor.control.bindings ∧ cursor.control.goals = [] ∧
        ∃ environment, resolve cursor.control.bindings = some environment ∧
          read environment cursor.control.destination = value := by
  constructor
  · intro source
    cases source with
    | returned environment atEnd resolved =>
        exact ⟨rfl, rfl, atEnd, environment, resolved, rfl⟩
    | argument _ _ _ _ _ _ source => cases source
  · rintro ⟨rfl, rfl, atEnd, environment, resolved, rfl⟩
    exact .returned environment atEnd resolved

/-- The local source/AM square is exact under the driver's explicit license. -/
theorem step_iff_source {Context : Type} (policy : Policy) (program : Program)
    (cursor : Cursor Context) (licensed : Licensed cursor.control) (action : Action Context) :
    (machine policy program).step cursor = some action ↔ Step policy program cursor action := by
  constructor
  · intro actual
    obtain ⟨selected, source, computed⟩ := step_has_source policy program cursor licensed
    cases Option.some.inj (computed.symm.trans actual)
    exact source
  · exact Step.execution

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.Source

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.Source

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation

/-- Generative source operations have an opaque supply carrier. Their inputs
are finite syntax packets and protected names; they cannot evaluate a body,
advance a continuation, or change the observable world. -/
structure FreshOperations (Supply : Type) where
  copies : Supply → Finset String → List (Atom × List Atom) →
    Option (Supply × List (Atom × List Atom))
  parsed : Supply → Finset String → Atom → Except Effects.Fault (Option (Supply × Atom))

namespace FreshOperations

/-- The maintained finite identity implementation is one operation instance.
Tokens stay inside it; source collection observes only the copied packets. -/
def owned : FreshOperations Allocator where
  copies allocator protectedNames source := do
    let (next, copied) ← Collection.copyOwnedAnswers? allocator protectedNames source
    pure (next, copied.map Prod.snd)
  parsed allocator protectedNames text :=
    match Collection.SyntaxLoading.loadParsed? allocator protectedNames text with
    | .error reason => .error reason
    | .ok none => .ok none
    | .ok (some (next, _token, value)) => .ok (some (next, value))

theorem owned_copies_iff (allocator next : Allocator) (protectedNames : Finset String)
    (source copied : List (Atom × List Atom)) :
    owned.copies allocator protectedNames source = some (next, copied) ↔
      ∃ tagged, Collection.copyOwnedAnswers? allocator protectedNames source = some (next, tagged) ∧
        copied = tagged.map Prod.snd := by
  cases actual : Collection.copyOwnedAnswers? allocator protectedNames source with
  | none => simp [owned, actual]
  | some packet =>
      rcases packet with ⟨after, tagged⟩
      simp [owned, actual, eq_comm]

/-- Erasing implementation tokens preserves the complete source copy contract,
including occurrence count and independence of distinct copied answers. -/
theorem owned_copies_valid {allocator next : Allocator} {protectedNames : Finset String}
    {source copied : List (Atom × List Atom)}
    (actual : owned.copies allocator protectedNames source = some (next, copied)) :
    Collection.Copies protectedNames source copied := by
  obtain ⟨tagged, computed, rfl⟩ := (owned_copies_iff _ _ _ _ _).mp actual
  have trace := Collection.copyOwnedAnswers_trace computed
  have checked : List.Forall₂ (fun raw fresh => Collection.IsCopy protectedNames raw.1 raw.2 fresh)
      source (tagged.map Prod.snd) :=
    List.forall₂_map_right_iff.mpr (Collection.copyOwnedAnswers_valid computed)
  have independent : (tagged.map Prod.snd).Pairwise (fun first second =>
      ∀ atom ∈ first.1 :: first.2, ∀ other ∈ second.1 :: second.2,
        ∀ name ∈ TypeSubst.typeVars atom, name ∉ TypeSubst.typeVars other) := by
    simpa only [List.pairwise_map] using trace.independent_rows
  refine ⟨checked.length_eq.symm, ?_, ?_⟩
  · intro index before after
    exact checked.get before after
  · intro first second firstBound secondBound different name present otherPresent
    by_cases order : first < second
    · have separated := independent.rel_get_of_lt
        (a := ⟨first, firstBound⟩) (b := ⟨second, secondBound⟩) order
      exact separated _ (by simp) _ (by simp) name present otherPresent
    · have reverse : second < first := by omega
      have separated := independent.rel_get_of_lt
        (a := ⟨second, secondBound⟩) (b := ⟨first, firstBound⟩) reverse
      exact separated _ (by simp) _ (by simp) name otherPresent present

theorem owned_parsed_iff (allocator next : Allocator) (protectedNames : Finset String)
    (text value : Atom) :
    owned.parsed allocator protectedNames text = .ok (some (next, value)) ↔
      ∃ token, Collection.SyntaxLoading.loadParsed? allocator protectedNames text =
        .ok (some (next, token, value)) := by
  cases actual : Collection.SyntaxLoading.loadParsed? allocator protectedNames text with
  | error reason => simp [owned, actual]
  | ok result =>
      cases result with
      | none => simp [owned, actual]
      | some packet =>
          rcases packet with ⟨after, token, loaded⟩
          simp [owned, actual, eq_comm]

/-- The existing named-syntax result is preserved by the abstract operation.
Anonymous expansion is supplied by the source reader before owned copying. -/
theorem owned_named_parse {allocator next : Allocator} {protectedNames : Finset String}
    {text value : Atom}
    (actual : owned.parsed allocator protectedNames text = .ok (some (next, value))) :
    Collection.SyntaxLoading.NamedParseResult protectedNames text value := by
  obtain ⟨token, parsed⟩ := (owned_parsed_iff _ _ _ _ _).mp actual
  exact Collection.SyntaxLoading.loadParsed_named_result parsed

end FreshOperations

abbrev ScopeState (Supply Context : Type) := Supply × CollectionConfiguration Context

/-- The caller consumes copied syntax, not the child's binding record. -/
def resumeCopies {Context : Type} (copied : List (Atom × List Atom))
    (caller : CollectionCaller Context) : CollectionWork Context :=
  (replace caller.1 (.equate (.expression (copied.map Prod.fst)) caller.2.1 :: caller.1.goals),
    caller.2.2.1, caller.2.2.2)

/-- Source collection completion is defined only at an exhausted child
frontier. The generative operation is independent of the saved search/caller
representation, and receives the actual completed ordered packets. -/
inductive CollectionReturn {Supply Context : Type} (fresh : FreshOperations Supply) :
    ScopeState Supply Context → ScopeState Supply Context → Prop where
  | complete (supply after : Supply) (world : World) (answers : List CollectedAnswer)
      (caller : CollectionCaller Context) (parent : CollectionScope Context)
      (parents : List (CollectionScope Context)) (copied : List (Atom × List Atom))
      (ready : ∀ answer ∈ answers, answer.associated = [])
      (returned : fresh.copies supply
        (collectionSupport (⟨world, ⟨[], answers, some caller⟩ :: parent :: parents⟩ : CollectionConfiguration Context))
        (answers.map fun answer => (answer.value, answer.associated)) = some (after, copied))
      (valid : Collection.Copies
        (collectionSupport (⟨world, ⟨[], answers, some caller⟩ :: parent :: parents⟩ : CollectionConfiguration Context))
        (answers.map fun answer => (answer.value, answer.associated)) copied) :
      CollectionReturn fresh (supply, ⟨world, ⟨[], answers, some caller⟩ :: parent :: parents⟩)
        (after, ⟨world, {parent with frontier := resumeCopies copied caller :: parent.frontier} :: parents⟩)

theorem resumeCopies_erase {Context : Type} (copied : List (Token × (Atom × List Atom)))
    (caller : CollectionCaller Context) :
    resumeCopies (copied.map Prod.snd) caller = allocatedWork copied caller := by
  simp only [resumeCopies, allocatedWork, replace, List.map_map, Function.comp_def]

theorem CollectionReturn.preserves_world {Supply Context : Type} {fresh : FreshOperations Supply}
    {before after : ScopeState Supply Context} (source : CollectionReturn fresh before after) :
    after.2.world = before.2.world := by cases source; rfl

/-- Both directions of the maintained generative completion square. Source
completion never assumes a completed evaluator reply or a supplied answer bag. -/
theorem collection_return_iff {Context : Type} (before after : ScopedCursor Context) :
    finishAllocated? before = some after ↔ CollectionReturn FreshOperations.owned before after := by
  constructor
  · intro actual
    rcases before with ⟨supply, ⟨world, scopes⟩⟩
    rcases after with ⟨next, ⟨afterWorld, afterScopes⟩⟩
    obtain ⟨answers, caller, parent, parents, tagged, scopeEq, ready, copied, _trace, afterEq⟩ :=
      finishAllocated_origin _ _ actual
    have worldEq : afterWorld = world := congrArg Configuration.world afterEq
    have scopesEq : afterScopes =
        {parent with frontier := allocatedWork tagged caller :: parent.frontier} :: parents :=
      congrArg Configuration.scopes afterEq
    change scopes = ⟨[], answers, some caller⟩ :: parent :: parents at scopeEq
    subst scopes
    subst afterWorld
    subst afterScopes
    have returned := (FreshOperations.owned_copies_iff _ _ _ _ _).mpr ⟨tagged, copied, rfl⟩
    simpa only [resumeCopies_erase] using
      CollectionReturn.complete supply next world answers caller parent parents (tagged.map Prod.snd)
        ready returned (FreshOperations.owned_copies_valid returned)
  · intro source
    cases source with
    | complete supply after world answers caller parent parents copied ready returned _valid =>
      obtain ⟨tagged, actual, rfl⟩ := (FreshOperations.owned_copies_iff _ _ _ _ _).mp returned
      have allReady : answers.all (fun answer => answer.associated.isEmpty) = true := by
        exact List.all_eq_true.mpr (fun answer present => by simp [ready answer present])
      simp only [finishAllocated?, allReady, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        actual, pure, resumeCopies_erase]
      rfl

/-- Partial aggregates cannot be source collection completions. -/
theorem collection_return_no_pending {Supply Context : Type} (fresh : FreshOperations Supply)
    (supply : Supply) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (work : CollectionWork Context)
    (pending : List (CollectionWork Context)) (frontier : scope.frontier = work :: pending)
    (after : ScopeState Supply Context) :
    ¬CollectionReturn fresh (supply, ⟨world, scope :: parents⟩) after := by
  intro source
  cases source
  simp at frontier

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.Source

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.Source

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open SpaceSemantics (Program)

/-- Source rules enter ordinary expansion only at a licensed active goal. -/
theorem Step.licensed {Context : Type} {policy : Policy} {program : Program}
    {cursor : Cursor Context} {action : Action Context} (source : Step policy program cursor action) :
    Licensed cursor.control := by
  cases source with
  | querying location pattern template destination older environment atGoal resolved =>
      exact .querying location pattern template destination older atGoal
  | opening older atGoal => exact .opening older atGoal
  | committing older atGoal => exact .committing older atGoal
  | restoring boundary older atGoal => exact .restoring boundary older atGoal
  | expanded expression destination older next atGoal ordinary _ =>
      exact .evaluation expression destination older atGoal ordinary
  | accepted value destination older _ atGoal _ | refused value destination older atGoal _ =>
      exact .equation value destination older atGoal
  | returned _ atEnd _ => exact .ended atEnd
  | conditional condition yes no destination older _ atGoal _ =>
      exact .conditional condition yes no destination older atGoal
  | inconsistent site _ =>
      cases site with
      | ended atEnd => exact .ended atEnd
      | conditional condition yes no destination older atGoal =>
          exact .conditional condition yes no destination older atGoal
      | argument value destination depth remaining atGoal => exact .argument value destination depth remaining atGoal
      | invocation head arguments destination older atGoal => exact .invocation head arguments destination older atGoal
      | querying location pattern template destination older atGoal => exact .querying location pattern template destination older atGoal
  | argument value destination younger older action atGoal _ =>
      exact .argument value destination older.length (younger ++ older) (by simpa only [List.cons_append] using atGoal)
  | invalidDelimiter value destination depth remaining _ atGoal _ _ =>
      exact .argument value destination depth remaining atGoal
  | printed arguments destination older _ _ atGoal _ _ =>
      exact .invocation "println!" arguments destination older atGoal
  | requested head arguments destination older _ atGoal _ _ =>
      exact .invocation head arguments destination older atGoal

theorem Licensed.ordinary {control : Control} (licensed : Licensed control)
    {expression destination : Atom} {older : List Goal}
    (atGoal : control.goals = .evaluate expression destination :: older) :
    scopedForm expression = false := by
  cases licensed <;> simp_all

/-- The actual scope dispatcher respects the source license. Neither a child
collection nor source choice nor empty search is delegated as ordinary work. -/
theorem licensed_scope_guards {Context : Type} (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (licensed : Licensed control) :
    enterCollapse? (⟨world, scope :: parents⟩ : CollectionConfiguration Context) = none ∧
    enterSuperpose? (⟨world, scope :: parents⟩ : CollectionConfiguration Context) = none ∧
    (∀ destination older,
      control.goals ≠ .evaluate (.expression [.symbol "empty"]) destination :: older) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold enterCollapse?
    simp only [frontier]
    split
    · rename_i expression destination older atGoal
      have impossible := licensed.ordinary atGoal
      simp [scopedForm] at impossible
    · rfl
  · unfold enterSuperpose?
    simp only [frontier]
    split
    · rename_i alternatives destination older atGoal
      have impossible := licensed.ordinary atGoal
      simp [scopedForm] at impossible
    · rfl
  · intro destination older atGoal
    have impossible := licensed.ordinary atGoal
    simp [scopedForm] at impossible

/-- A complete source local action enters the existing retained scope
operation with its actual world, context, origins and older work. This law
holds before serving a request; it does not assume a recursive child answer. -/
theorem source_step_scope {Context : Type} (policy : Policy) (program : Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (action : Action Context) (source : Step policy program (⟨world, control, context⟩ : Cursor Context) action) :
    scopeStep policy program (allocator, ⟨world, scope :: parents⟩) =
      installChild program (allocator, ⟨world, scope :: parents⟩) scope parents origins pending action := by
  obtain ⟨notCollapse, notSuperpose, notEmpty⟩ :=
    licensed_scope_guards world scope parents control context origins pending frontier source.licensed
  have actual := source.execution
  simp only [scopeStep, frontier, notCollapse, notSuperpose, actual]

/-- Reflection constructs a source local action at the actual active cursor.
Outer services and collection completion are separate source boundaries. -/
theorem scope_has_local_source {Context : Type} (policy : Policy) (program : Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (licensed : Licensed control) :
    ∃ action, Step policy program (⟨world, control, context⟩ : Cursor Context) action ∧
      scopeStep policy program (allocator, ⟨world, scope :: parents⟩) =
        installChild program (allocator, ⟨world, scope :: parents⟩) scope parents origins pending action := by
  obtain ⟨action, source, _actual⟩ := step_has_source policy program (⟨world, control, context⟩ : Cursor Context) licensed
  exact ⟨action, source, source_step_scope policy program allocator world scope parents control context origins
    pending frontier action source⟩

/-- A retained source body cannot discard its surrounding binding record while
it is merely being expanded into pending work. -/
theorem Prepared.retains_frame {policy : Policy} {program : Program} {control next : Control}
    {destination expression : Atom} {older : List Goal}
    (source : Prepared policy program control destination older expression next) :
    next.bindings = control.bindings ∧ next.destination = control.destination ∧ next.reserved = control.reserved := by
  cases source <;> exact ⟨rfl, rfl, rfl⟩

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.Source


namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.Source

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open SpaceSemantics (Program)

/-- A source scope boundary cannot be passed off as ordinary body work. -/
theorem scoped_form_has_no_local_step {Context : Type} {policy : Policy} {program : Program}
    {cursor : Cursor Context} {expression destination : Atom} {older : List Goal}
    (atGoal : cursor.control.goals = .evaluate expression destination :: older)
    (captured : scopedForm expression = true) (action : Action Context) :
    ¬Step policy program cursor action := by
  intro source
  have ordinary := source.licensed.ordinary atGoal
  rw [captured] at ordinary
  cases ordinary

/-- Equal open answer payloads must still have independent copied variables.
The result contract rejects one shared residual name across both occurrences. -/
theorem shared_residual_copies_refused (protectedNames : Finset String)
    (source : List (Atom × List Atom)) (name : String) :
    ¬Collection.Copies protectedNames source [(.var name, []), (.var name, [])] := by
  intro valid
  have separated := valid.2.2 0 1 (by simp) (by simp) (by simp) name
    (by simp [TypeSubst.typeVars])
  exact separated (by simp [TypeSubst.typeVars])

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.Source


/-!
## Scoped source execution

The source rules compose pending bodies, complete equation frontiers and
collection delimiters. Generative operations remain local parameters. Neither
an invocation nor a collection rule assumes a recursively evaluated reply.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.Source

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open SpaceSemantics (Program)
open Mettapedia.GSLT.Distinction.ProductiveBlocks

abbrev ScopeAction (Supply Context : Type) :=
  Mettapedia.GSLT.Distinction.ProductiveBlocks.Transition
    (ScopeState Supply Context) CollectedAnswer (ScopeState Supply Context) ScopeBoundary

/-- Invocation schedules a complete source frontier or the results of a local
operation. All callers, older alternatives and occurrence paths stay explicit.
The environment is the reached readout at the invocation boundary. -/
inductive Invocation {Supply Context : Type} (fresh : FreshOperations Supply) (program : Program)
    (supply : Supply) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (environment : Environment) : ScopeAction Supply Context → Prop where
  | parsed (text value : Atom) (after : Supply) (parseHead : head = "parse")
      (input : arguments.map (read environment) = [text])
      (returned : fresh.parsed supply (collectionSupport ⟨world, scope :: parents⟩) text =
        .ok (some (after, value))) :
      Invocation fresh program supply world scope parents control context origins pending head arguments destination older environment
        (.silent (after, ⟨world, {scope with frontier := (primitiveWork control context origins destination older [value] ++ pending)} :: parents⟩))
  | parseFault (text : Atom) (reason : Effects.Fault) (parseHead : head = "parse")
      (input : arguments.map (read environment) = [text])
      (returned : fresh.parsed supply (collectionSupport ⟨world, scope :: parents⟩) text = .error reason) :
      Invocation fresh program supply world scope parents control context origins pending head arguments destination older environment
        (.call (.fault reason) (supply, ⟨world, scope :: parents⟩))
  | parseAllocation (text : Atom) (parseHead : head = "parse")
      (input : arguments.map (read environment) = [text])
      (returned : fresh.parsed supply (collectionSupport ⟨world, scope :: parents⟩) text = .ok none) :
      Invocation fresh program supply world scope parents control context origins pending head arguments destination older environment
        (.call .allocation (supply, ⟨world, scope :: parents⟩))
  | parseArity (parseHead : head = "parse")
      (input : ∀ text, arguments.map (read environment) ≠ [text]) :
      Invocation fresh program supply world scope parents control context origins pending head arguments destination older environment
        (.call (.fault (.invalidArguments "parse")) (supply, ⟨world, scope :: parents⟩))
  | primitive (state : Effects.State) (values : List Atom) (ordinary : head ≠ "parse")
      (known : StdLib.known head = true)
      (returned : StdLib.apply world.state head (arguments.map (read environment)) = .ok (state, values)) :
      Invocation fresh program supply world scope parents control context origins pending head arguments destination older environment
        (.silent (supply, ⟨{world with state}, {scope with frontier := (primitiveWork control context origins destination older values ++ pending)} :: parents⟩))
  | primitiveFault (reason : Effects.Fault) (ordinary : head ≠ "parse")
      (known : StdLib.known head = true)
      (returned : StdLib.apply world.state head (arguments.map (read environment)) = .error reason) :
      Invocation fresh program supply world scope parents control context origins pending head arguments destination older environment
        (.call (.fault reason) (supply, ⟨world, scope :: parents⟩))
  | equations (selected : List (Nat × Control)) (ordinary : head ≠ "parse")
      (known : StdLib.known head = false) (notIO : Eval.ioHead head = false)
      (declared : program.equations.any (·.head == head) = true)
      (frontier : ClauseChoice.Frontier program
        (protectControl control (collectionSupport ⟨world, scope :: parents⟩)) head
        (arguments.map (read environment)) destination older
        (List.range program.equations.length) selected) :
      Invocation fresh program supply world scope parents control context origins pending head arguments destination older environment
        (.silent (supply, ⟨world, {scope with frontier := (selected.map (fun row => (predicateEntry pending.length row.2, context, origins ++ [row.1])) ++ pending)} :: parents⟩))
  | unserved (ordinary : head ≠ "parse") (known : StdLib.known head = false)
      (unavailable : Eval.ioHead head = true ∨ program.equations.any (·.head == head) = false) :
      Invocation fresh program supply world scope parents control context origins pending head arguments destination older environment
        (.call (.branch (.invoke head (arguments.map (read environment)) destination))
          (supply, ⟨world, scope :: parents⟩))

/-- The maintained invocation implements the independent local source cases.
Equation children are installed, not evaluated inside this operation. -/
theorem Invocation.execution {Context : Type} {program : Program}
    {supply : Allocator} {world : World} {scope : CollectionScope Context}
    {parents : List (CollectionScope Context)} {control : Control} {context : Context}
    {origins : List Nat} {pending : List (CollectionWork Context)}
    {head : String} {arguments : List Atom} {destination : Atom} {older : List Goal}
    {environment : Environment} {action : ScopeAction Allocator Context}
    (source : Invocation FreshOperations.owned program supply world scope parents control context origins pending
      head arguments destination older environment action)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke head arguments destination :: older)
    (resolved : resolve control.bindings = some environment) :
    scopedInvocation program (supply, ⟨world, scope :: parents⟩) scope parents control context origins pending
      head (arguments.map (read environment)) destination older = action := by
  cases source with
  | parsed text value after parseHead input returned =>
      obtain ⟨token, actual⟩ := (FreshOperations.owned_parsed_iff _ _ _ _ _).mp returned
      simp [scopedInvocation, parseHead, input, actual]
  | parseFault text reason parseHead input returned =>
      cases actual : Collection.SyntaxLoading.loadParsed? supply (collectionSupport ⟨world, scope :: parents⟩) text with
      | error found =>
          have same : found = reason := by simpa only [FreshOperations.owned, actual, Except.error.injEq] using returned
          subst found
          simp only [scopedInvocation, parseHead, ↓reduceIte, input, actual]
      | ok packet =>
          rcases packet with _ | ⟨after, token, value⟩ <;> simp [FreshOperations.owned, actual] at returned
  | parseAllocation text parseHead input returned =>
      cases actual : Collection.SyntaxLoading.loadParsed? supply (collectionSupport ⟨world, scope :: parents⟩) text with
      | error found => simp [FreshOperations.owned, actual] at returned
      | ok packet =>
          rcases packet with _ | ⟨after, token, value⟩
          · simp only [scopedInvocation, parseHead, ↓reduceIte, input, actual]
          · simp [FreshOperations.owned, actual] at returned
  | parseArity parseHead input =>
      subst head
      unfold scopedInvocation
      split <;> simp_all
  | primitive state values ordinary known returned => simp [scopedInvocation, ordinary, known, returned]
  | primitiveFault reason ordinary known returned => simp [scopedInvocation, ordinary, known, returned]
  | equations selected ordinary known notIO declared rows =>
      have entered := enterEquations_constructs program world scope parents control context origins pending
        head arguments destination older environment frontier atCall (by simp [notIO, known]) declared resolved
      have exactRows := (ClauseChoice.choices_iff_frontier _ _ _ _ _ _ _).mpr rows
      simp [scopedInvocation, ordinary, known, entered, equationWork, exactRows]
  | unserved ordinary known unavailable =>
      have notEntered : enterEquations? program (⟨world, scope :: parents⟩ : CollectionConfiguration Context) = none := by
        rcases unavailable with notIO | notDeclared
        · simp [enterEquations?, frontier, atCall, notIO]
        · simp [enterEquations?, frontier, atCall, known, notDeclared]
      simp [scopedInvocation, ordinary, known, notEntered]

/-- Every local invocation has source evidence, including explicit faults or
unserved requests. Complete equation coverage uses the independently proved
frontier theorem; no successful evaluator response is assumed. -/
theorem invocation_has_source {Supply Context : Type} (fresh : FreshOperations Supply) (program : Program)
    (supply : Supply) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (environment : Environment) :
    ∃ action, Invocation fresh program supply world scope parents control context origins pending
      head arguments destination older environment action := by
  by_cases parseHead : head = "parse"
  · by_cases input : ∃ text, arguments.map (read environment) = [text]
    · obtain ⟨text, input⟩ := input
      cases returned : fresh.parsed supply (collectionSupport ⟨world, scope :: parents⟩) text with
      | error reason => exact ⟨_, .parseFault text reason parseHead input returned⟩
      | ok packet =>
        cases packet with
        | none => exact ⟨_, .parseAllocation text parseHead input returned⟩
        | some packet => exact ⟨_, .parsed text packet.2 packet.1 parseHead input returned⟩
    · exact ⟨_, .parseArity parseHead (by simpa using input)⟩
  · by_cases known : StdLib.known head = true
    · cases returned : StdLib.apply world.state head (arguments.map (read environment)) with
      | error reason => exact ⟨_, .primitiveFault reason parseHead known returned⟩
      | ok packet => exact ⟨_, .primitive packet.1 packet.2 parseHead known returned⟩
    · have unknown : StdLib.known head = false := by simpa using known
      by_cases notIO : Eval.ioHead head = false
      · by_cases declared : program.equations.any (·.head == head) = true
        · exact ⟨_, .equations _ parseHead unknown notIO declared
            ((ClauseChoice.choices_iff_frontier _ _ _ _ _ _ _).mp rfl)⟩
        · exact ⟨_, .unserved parseHead unknown (Or.inr (by simpa using declared))⟩
      · exact ⟨_, .unserved parseHead unknown (Or.inl (by simpa using notIO))⟩

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.Source


namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.Source

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open SpaceSemantics (Program)
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Source control at one focused work item. Local rules earn their action;
invocations earn a complete operation frontier. Child scope entry is a
structural continuation rule, with the parent's unfinished work saved. -/
inductive ActiveStep {Supply Context : Type} (fresh : FreshOperations Supply)
    (policy : Policy) (program : Program) (supply : Supply) (world : World)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (control : Control) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)) : ScopeAction Supply Context → Prop where
  | opening (older : List Goal) (atGoal : control.goals = .openCommit :: older) :
      ActiveStep fresh policy program supply world scope parents control context origins pending
        (.silent (supply, ⟨world, {scope with frontier :=
          ({control with goals := older,cutBoundary := pending.length},context,origins) :: pending} :: parents⟩))
  | committing (older : List Goal) (younger kept : List (CollectionWork Context))
      (atGoal : control.goals = .commit :: older)
      (partition : pending = younger ++ kept) (boundary : kept.length = control.cutBoundary) :
      ActiveStep fresh policy program supply world scope parents control context origins pending
        (.silent (supply, ⟨world, {scope with frontier :=
          ({control with goals := older},context,origins) :: kept} :: parents⟩))
  | invalidCommit (older : List Goal) (atGoal : control.goals = .commit :: older)
      (tooShort : pending.length < control.cutBoundary) :
      ActiveStep fresh policy program supply world scope parents control context origins pending
        (.call (.branch (.invalidDelimiter control.cutBoundary pending.length))
          (supply, ⟨world, scope :: parents⟩))
  | next (reached : Cursor Context)
      (source : Step policy program ⟨world, control, context⟩ (.silent reached)) :
      ActiveStep fresh policy program supply world scope parents control context origins pending
        (.silent (supply, ⟨reached.world, retainChild scope pending origins reached :: parents⟩))
  | refused (bindings : Equations) (reached : Cursor Context)
      (source : Step policy program ⟨world, control, context⟩ (.finish (.noValue bindings, reached))) :
      ActiveStep fresh policy program supply world scope parents control context origins pending
        (.silent (supply, ⟨reached.world, {scope with frontier := pending} :: parents⟩))
  | answered (value : Atom) (bindings : Equations) (reached : Cursor Context)
      (source : Step policy program ⟨world, control, context⟩ (.finish (.value value bindings, reached))) :
      ActiveStep fresh policy program supply world scope parents control context origins pending
        (let answer : CollectedAnswer := ⟨value, bindings, origins, []⟩
         let after := (supply, ⟨reached.world, Scope.record scope pending answer :: parents⟩)
         if scope.caller.isNone then .publish [answer] after else .silent after)
  | boundary (request : Boundary) (saved : Cursor Context)
      (source : Step policy program ⟨world, control, context⟩ (.call request saved))
      (notInvocation : ∀ head arguments destination, request ≠ .invoke head arguments destination)
      (notQuery : ∀ location pattern template destination, request ≠ .query location pattern template destination)
      (notOpening : request ≠ .openCommit) (notCommit : ∀ retained, request ≠ .commit retained) :
      ActiveStep fresh policy program supply world scope parents control context origins pending
        (.call (.branch request) (supply, ⟨world, scope :: parents⟩))
  | invocation (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
      (environment : Environment) (action : ScopeAction Supply Context)
      (atCall : control.goals = .invoke head arguments destination :: older)
      (resolved : resolve control.bindings = some environment)
      (notPrint : ∀ value, head = "println!" → arguments.map (read environment) ≠ [value])
      (served : Invocation fresh program supply world scope parents control context origins pending
        head arguments destination older environment action) :
      ActiveStep fresh policy program supply world scope parents control context origins pending action
  | queried (location pattern template destination : Atom) (older : List Goal) (environment : Environment)
      (rows : List Atom) (selected : List (Nat × Control))
      (atQuery : control.goals = .query location pattern template destination :: older)
      (resolved : resolve control.bindings = some environment)
      (readRows : (Effects.readHandle (read environment location) >>= world.state.read) = some rows)
      (frontier : QueryFrontier (protectControl control (collectionSupport ⟨world, scope :: parents⟩))
        pattern template destination older 0 rows selected) :
      ActiveStep fresh policy program supply world scope parents control context origins pending
        (.silent (supply, ⟨world, {scope with frontier :=
          (selected.map (fun row => (row.2, context, origins ++ [row.1])) ++ pending)} :: parents⟩))
  | queryFault (location pattern template destination : Atom) (older : List Goal) (environment : Environment)
      (atQuery : control.goals = .query location pattern template destination :: older)
      (resolved : resolve control.bindings = some environment)
      (noSpace : (Effects.readHandle (read environment location) >>= world.state.read) = none) :
      ActiveStep fresh policy program supply world scope parents control context origins pending
        (.call (.fault .invalidSpace) (supply, ⟨world, scope :: parents⟩))
  | collapsed (expression destination : Atom) (older : List Goal)
      (atGoal : control.goals = .evaluate (.expression [.symbol "collapse", expression]) destination :: older) :
      ActiveStep fresh policy program supply world scope parents control context origins pending
        (.silent (supply, Scope.enter world scope pending parents
          (collapseChild control (collectionSupport ⟨world, scope :: parents⟩) expression, context, origins)
          ({control with goals := older}, destination, context, origins)))
  | choice (alternatives : List Atom) (destination : Atom) (older : List Goal)
      (atGoal : control.goals = .evaluate (.expression [.symbol "superpose", .expression alternatives]) destination :: older) :
      ActiveStep fresh policy program supply world scope parents control context origins pending
        (.silent (supply, ⟨world, {scope with frontier :=
          (superposeWork control context origins alternatives destination older ++ pending)} :: parents⟩))
  | empty (destination : Atom) (older : List Goal)
      (atGoal : control.goals = .evaluate (.expression [.symbol "empty"]) destination :: older) :
      ActiveStep fresh policy program supply world scope parents control context origins pending
        (.silent (supply, ⟨world, {scope with frontier := pending} :: parents⟩))

/-- Focused source rules implement one actual retained scope step. -/
theorem ActiveStep.execution {Context : Type} {policy : Policy} {program : Program}
    {supply : Allocator} {world : World} {scope : CollectionScope Context}
    {parents : List (CollectionScope Context)} {control : Control} {context : Context}
    {origins : List Nat} {pending : List (CollectionWork Context)} {action : ScopeAction Allocator Context}
    (source : ActiveStep FreshOperations.owned policy program supply world scope parents control context origins pending action)
    (frontier : scope.frontier = (control, context, origins) :: pending) :
    scopeStep policy program (supply, ⟨world, scope :: parents⟩) = action := by
  cases source with
  | opening older atGoal =>
      rw [source_step_scope policy program supply world scope parents control context origins pending frontier _
        (.opening older atGoal)]
      simp only [installChild,atGoal]
  | committing older younger kept atGoal partition boundary =>
      rw [source_step_scope policy program supply world scope parents control context origins pending frontier _
        (.committing older atGoal)]
      simp [installChild,atGoal,partition,←boundary]
  | invalidCommit older atGoal tooShort =>
      rw [source_step_scope policy program supply world scope parents control context origins pending frontier _
        (.committing older atGoal)]
      simp [installChild,atGoal,Nat.not_le.mpr tooShort]
  | next reached localStep =>
      rw [source_step_scope policy program supply world scope parents control context origins pending frontier _ localStep]
      rfl
  | refused bindings reached localStep =>
      rw [source_step_scope policy program supply world scope parents control context origins pending frontier _ localStep]
      rfl
  | answered value bindings reached localStep =>
      rw [source_step_scope policy program supply world scope parents control context origins pending frontier _ localStep]
      rfl
  | boundary request saved localStep notInvocation notQuery notOpening notCommit =>
      rw [source_step_scope policy program supply world scope parents control context origins pending frontier _ localStep]
      cases request with
      | invoke head arguments destination => exact False.elim (notInvocation _ _ _ rfl)
      | query location pattern template destination => exact False.elim (notQuery _ _ _ _ rfl)
      | openCommit => exact False.elim (notOpening rfl)
      | commit retained => exact False.elim (notCommit _ rfl)
      | invalidEnvironment | invalidDelimiter => rfl
  | invocation head arguments destination older environment action atCall resolved notPrint served =>
      have localStep := Step.requested (cursor := (⟨world, control, context⟩ : Cursor Context))
        (policy := policy) (program := program) head arguments destination older environment atCall resolved notPrint
      rw [source_step_scope policy program supply world scope parents control context origins pending frontier _ localStep]
      simpa only [installChild, atCall] using served.execution frontier atCall resolved
  | queried location pattern template destination older environment rows selected atQuery resolved readRows selectedRows =>
      have localStep := Step.querying (cursor := (⟨world, control, context⟩ : Cursor Context))
        (policy := policy) (program := program) location pattern template destination older environment atQuery resolved
      rw [source_step_scope policy program supply world scope parents control context origins pending frontier _ localStep]
      simp [installChild, atQuery, scopedQuery, readRows, queryWork, selectedRows.execution]
  | queryFault location pattern template destination older environment atQuery resolved noSpace =>
      have localStep := Step.querying (cursor := (⟨world, control, context⟩ : Cursor Context))
        (policy := policy) (program := program) location pattern template destination older environment atQuery resolved
      rw [source_step_scope policy program supply world scope parents control context origins pending frontier _ localStep]
      simp [installChild, atQuery, scopedQuery, noSpace]
  | collapsed expression destination older atGoal =>
      exact scope_collapse_entry policy program supply world scope parents control context origins pending
        expression destination older frontier atGoal
  | choice alternatives destination older atGoal =>
      exact scope_superpose_entry policy program supply world scope parents control context origins pending
        alternatives destination older frontier atGoal
  | empty destination older atGoal =>
      simp [scopeStep, frontier, enterCollapse?, atGoal, enterSuperpose?]

/-- The full source scope step. Empty root search completes; empty child
search must perform fresh collection return. Pending associated work or an
unserved allocation remains a request with the same complete saved state. -/
inductive ScopedStep {Supply Context : Type} (fresh : FreshOperations Supply)
    (policy : Policy) (program : Program) : ScopeState Supply Context → ScopeAction Supply Context → Prop where
  | active (supply : Supply) (world : World) (scope : CollectionScope Context)
      (parents : List (CollectionScope Context)) (control : Control) (context : Context)
      (origins : List Nat) (pending : List (CollectionWork Context)) (action : ScopeAction Supply Context)
      (frontier : scope.frontier = (control, context, origins) :: pending)
      (source : ActiveStep fresh policy program supply world scope parents control context origins pending action) :
      ScopedStep fresh policy program (supply, ⟨world, scope :: parents⟩) action
  | finished (supply : Supply) (world : World) (answers : List CollectedAnswer) :
      ScopedStep fresh policy program (supply, ⟨world, [⟨[], answers, none⟩]⟩)
        (.finish (supply, ⟨world, [⟨[], answers, none⟩]⟩))
  | collected {before after : ScopeState Supply Context} (source : CollectionReturn fresh before after) :
      ScopedStep fresh policy program before (.silent after)
  | associated (supply : Supply) (world : World) (answers : List CollectedAnswer)
      (caller : CollectionCaller Context) (parent : CollectionScope Context)
      (parents : List (CollectionScope Context)) (answer : CollectedAnswer)
      (member : answer ∈ answers) (pending : answer.associated ≠ []) :
      ScopedStep fresh policy program (supply, ⟨world, ⟨[], answers, some caller⟩ :: parent :: parents⟩)
        (.call .associatedWork (supply, ⟨world, ⟨[], answers, some caller⟩ :: parent :: parents⟩))
  | allocation (supply : Supply) (world : World) (answers : List CollectedAnswer)
      (caller : CollectionCaller Context) (parent : CollectionScope Context)
      (parents : List (CollectionScope Context)) (ready : ∀ answer ∈ answers, answer.associated = [])
      (unserved : fresh.copies supply
        (collectionSupport (⟨world, ⟨[], answers, some caller⟩ :: parent :: parents⟩ : CollectionConfiguration Context))
        (answers.map fun answer => (answer.value, answer.associated)) = none) :
      ScopedStep fresh policy program (supply, ⟨world, ⟨[], answers, some caller⟩ :: parent :: parents⟩)
        (.call .allocation (supply, ⟨world, ⟨[], answers, some caller⟩ :: parent :: parents⟩))

/-- Soundness of the complete scoped rule family, including recursive child
entry, publication, branch refusal and the reached collection return. -/
theorem ScopedStep.execution {Context : Type} {policy : Policy} {program : Program}
    {before : ScopedCursor Context} {action : ScopeAction Allocator Context}
    (source : ScopedStep FreshOperations.owned policy program before action) :
    scopeStep policy program before = action := by
  cases source with
  | active _ _ _ _ _ _ _ _ _ frontier source => exact source.execution frontier
  | finished supply world answers => rfl
  | collected source =>
      cases source with
      | complete supply after world answers caller parent parents copied ready returned valid =>
          obtain ⟨tagged, actual, rfl⟩ := (FreshOperations.owned_copies_iff _ _ _ _ _).mp returned
          simpa only [resumeCopies_erase] using
            scopeStep_copied_return policy program supply after world answers caller parent parents tagged ready actual
  | associated supply world answers caller parent parents answer member pending =>
      exact scopeStep_pending_associated policy program supply world answers caller parent parents answer member pending
  | allocation supply world answers caller parent parents ready unserved =>
      have actual : Collection.copyOwnedAnswers? supply
          (collectionSupport (⟨world, ⟨[], answers, some caller⟩ :: parent :: parents⟩ : CollectionConfiguration Context))
          (answers.map fun answer => (answer.value, answer.associated)) = none := by
        cases copied : Collection.copyOwnedAnswers? supply _ _ with
        | none => rfl
        | some packet => simp [FreshOperations.owned, copied] at unserved
      have allReady : answers.all (fun answer => answer.associated.isEmpty) = true :=
        List.all_eq_true.mpr (fun answer member => by simp [ready answer member])
      simp [scopeStep, allReady, finishAllocated?, actual]

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.Source


namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.Source

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open SpaceSemantics (Program)
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Every focused source goal is ordinary licensed work or an explicit scope
boundary. The classification inspects syntax, never a completed child result. -/
theorem active_has_source {Supply Context : Type} (fresh : FreshOperations Supply)
    (policy : Policy) (program : Program) (supply : Supply) (world : World)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (control : Control) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)) :
    ∃ action, ActiveStep fresh policy program supply world scope parents control context origins pending action := by
  classical
  by_cases collapse : ∃ expression destination older,
      control.goals = .evaluate (.expression [.symbol "collapse", expression]) destination :: older
  · obtain ⟨expression, destination, older, atGoal⟩ := collapse
    exact ⟨_, .collapsed expression destination older atGoal⟩
  by_cases choice : ∃ alternatives destination older,
      control.goals = .evaluate (.expression [.symbol "superpose", .expression alternatives]) destination :: older
  · obtain ⟨alternatives, destination, older, atGoal⟩ := choice
    exact ⟨_, .choice alternatives destination older atGoal⟩
  by_cases empty : ∃ destination older,
      control.goals = .evaluate (.expression [.symbol "empty"]) destination :: older
  · obtain ⟨destination, older, atGoal⟩ := empty
    exact ⟨_, .empty destination older atGoal⟩
  have licensed : Licensed control := by
    cases atGoal : control.goals with
    | nil => exact .ended atGoal
    | cons goal older =>
      cases goal with
      | openCommit => exact .opening older atGoal
      | commit => exact .committing older atGoal
      | restoreCommit boundary => exact .restoring boundary older atGoal
      | equate value destination => exact .equation value destination older atGoal
      | branch condition yes no destination => exact .conditional condition yes no destination older atGoal
      | invoke head arguments destination => exact .invocation head arguments destination older atGoal
      | query location pattern template destination => exact .querying location pattern template destination older atGoal
      | argumentReturn value destination depth => exact .argument value destination depth older atGoal
      | evaluate expression destination =>
        apply Licensed.evaluation expression destination older atGoal
        unfold scopedForm
        split <;> simp_all
  obtain ⟨action, source, _actual⟩ := step_has_source policy program (⟨world, control, context⟩ : Cursor Context) licensed
  have original := source
  cases source with
  | opening older atGoal => exact ⟨_,.opening older atGoal⟩
  | committing older atGoal =>
      by_cases bound : control.cutBoundary ≤ pending.length
      · let kept := pending.drop (pending.length - control.cutBoundary)
        let younger := pending.take (pending.length - control.cutBoundary)
        refine ⟨_,.committing older younger kept atGoal (List.take_append_drop _ _).symm ?_⟩
        simp only [kept,List.length_drop]
        omega
      · exact ⟨_,.invalidCommit older atGoal (by omega)⟩
  | restoring => exact ⟨_,.next _ original⟩
  | expanded => exact ⟨_, .next _ original⟩
  | conditional => exact ⟨_, .next _ original⟩
  | accepted => exact ⟨_, .next _ original⟩
  | refused => exact ⟨_, .refused _ _ original⟩
  | returned => exact ⟨_, .answered _ _ _ original⟩
  | inconsistent => exact ⟨_, .boundary _ _ original (by simp) (by simp) (by simp) (by simp)⟩
  | invalidDelimiter => exact ⟨_, .boundary _ _ original (by simp) (by simp) (by simp) (by simp)⟩
  | querying location pattern template destination older environment atQuery resolved =>
      cases readRows : (Effects.readHandle (read environment location) >>= world.state.read) with
      | none => exact ⟨_, .queryFault location pattern template destination older environment atQuery resolved readRows⟩
      | some rows => exact ⟨_, .queried location pattern template destination older environment rows _ atQuery resolved readRows
          (queryChoices_has_source _ _ _ _ _ _ _)⟩
  | printed => exact ⟨_, .next _ original⟩
  | argument value destination younger older action atGoal returned =>
      cases returned with
      | ordinary => exact ⟨_, .next _ original⟩
      | propagated => exact ⟨_, .next _ original⟩
      | refused => exact ⟨_, .refused _ _ original⟩
      | invalid => exact ⟨_, .boundary _ _ original (by simp) (by simp) (by simp) (by simp)⟩
  | requested head arguments destination older environment atGoal resolved notPrint =>
      obtain ⟨action, served⟩ := invocation_has_source fresh program supply world scope parents control context origins pending
        head arguments destination older environment
      exact ⟨_, .invocation head arguments destination older environment action atGoal resolved notPrint served⟩

/-- Reflection constructs the complete source scope step from any properly
nested retained configuration. Successful, refused and incomplete boundaries
all remain distinct; no source answer is supplied by a driver callback. -/
theorem scoped_has_source {Context : Type} (policy : Policy) (program : Program)
    (before : ScopedCursor Context) (valid : ScopesValid before.2.scopes) :
    ∃ action, ScopedStep FreshOperations.owned policy program before action := by
  classical
  rcases before with ⟨supply, world, scopes⟩
  cases valid with
  | root work answers =>
      cases work with
      | nil => exact ⟨_, .finished supply world answers⟩
      | cons work pending =>
          rcases work with ⟨control, context, origins⟩
          obtain ⟨action, source⟩ := active_has_source FreshOperations.owned policy program supply world
            ⟨(control, context, origins) :: pending, answers, none⟩ [] control context origins pending
          exact ⟨_, .active supply world _ [] control context origins pending action rfl source⟩
  | @nested parents work answers caller valid =>
      cases work with
      | cons work pending =>
          rcases work with ⟨control, context, origins⟩
          obtain ⟨action, source⟩ := active_has_source FreshOperations.owned policy program supply world
            ⟨(control, context, origins) :: pending, answers, some caller⟩ parents control context origins pending
          exact ⟨_, .active supply world _ parents control context origins pending action rfl source⟩
      | nil =>
          cases parents with
          | nil => exact False.elim (valid.nonempty rfl)
          | cons parent parents =>
              by_cases ready : ∀ answer ∈ answers, answer.associated = []
              · cases copied : FreshOperations.owned.copies supply
                    (collectionSupport (⟨world, ⟨[], answers, some caller⟩ :: parent :: parents⟩ : CollectionConfiguration Context))
                    (answers.map fun answer => (answer.value, answer.associated)) with
                | none => exact ⟨_, .allocation supply world answers caller parent parents ready copied⟩
                | some packet =>
                    exact ⟨_, .collected (.complete supply packet.1 world answers caller parent parents packet.2
                      ready copied (FreshOperations.owned_copies_valid copied))⟩
              · obtain ⟨answer, member, pending⟩ : ∃ answer ∈ answers, answer.associated ≠ [] := by
                  simpa only [not_forall, Classical.not_imp, exists_prop] using ready
                exact ⟨_, .associated supply world answers caller parent parents answer member pending⟩

/-- Exact source/AM correspondence for the entire retained scope dispatcher,
not merely successful local branches or closed calls. -/
theorem scoped_step_iff_source {Context : Type} (policy : Policy) (program : Program)
    (before : ScopedCursor Context) (valid : ScopesValid before.2.scopes)
    (action : ScopeAction Allocator Context) :
    scopeStep policy program before = action ↔ ScopedStep FreshOperations.owned policy program before action := by
  constructor
  · intro actual
    obtain ⟨selected, source⟩ := scoped_has_source policy program before valid
    have same : selected = action := source.execution.symm.trans actual
    cases same
    exact source
  · exact ScopedStep.execution

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.Source

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared

/-- Cut discards precisely the younger prefix, keeping the current bindings,
reached world, outer alternatives, scope stack and source origins. -/
theorem scope_commit_split {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (younger kept : List (CollectionWork Context)) (older : List Goal)
    (frontier : scope.frontier = (control,context,origins) :: younger ++ kept)
    (atGoal : control.goals = .commit :: older) (boundary : control.cutBoundary = kept.length) :
    scopeStep policy program (allocator,⟨world,scope :: parents⟩) =
      .silent (allocator,⟨world,{scope with frontier :=
        ({control with goals := older},context,origins) :: kept} :: parents⟩) :=
  (Source.ActiveStep.committing older younger kept atGoal rfl boundary.symm).execution frontier

/-- An invalid saved delimiter is a retained control request, never a
completed refusal or an authorization to discard all remaining work. -/
theorem scope_commit_invalid {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (older : List Goal)
    (frontier : scope.frontier = (control,context,origins) :: pending)
    (atGoal : control.goals = .commit :: older) (invalid : pending.length < control.cutBoundary) :
    scopeStep policy program (allocator,⟨world,scope :: parents⟩) =
      .call (.branch (.invalidDelimiter control.cutBoundary pending.length))
        (allocator,⟨world,scope :: parents⟩) :=
  (Source.ActiveStep.invalidCommit older atGoal invalid).execution frontier

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination
