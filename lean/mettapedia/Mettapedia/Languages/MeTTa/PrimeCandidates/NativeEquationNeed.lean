import Lean.Meta.Tactic.Cbv
import Mettapedia.Machines.BranchLocalNeed.InferenceControl
import Mettapedia.Machines.BranchLocalNeed.SharedContinuationInstance
import Mettapedia.GSLT.Core.DemandExecution
import Mettapedia.Languages.ProcessCalculi.MORK.Syntax
import Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

/-!
# Authored equations on the branch-state Need machine

The source is ordinary MeTTa atoms and physical equation rows. This pure
fragment admits variable-only, distinct-variable equation arguments, integer
addition, lazy `let`, and normalized constructor returns. Arguments are
allocated before rule choice. Substitution binds variables to cell identities;
it does not copy an unevaluated argument at each use.

The existing rich Need semantics is the source execution contract; its
independently implemented receipt-erased and shared-continuation machines are
realizations. Native rule admission is proved against an independent row and
binding relation below. Recursive right-hand sides are never evaluated during
admission or inside a state instruction.

Effects, foreign calls, constrained argument patterns and arbitrary nested
scope expressions are outside this fragment. Their separate admission and
observation interfaces do not become silent errors in an ordinary dialect.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeEquationNeed

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Machines.BranchLocalNeed.NeedReference
open Mettapedia.Machines.BranchLocalNeed
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.InferenceControl

abbrev Environment := List (String × CellId)

def lookup (environment : Environment) (name : String) : Option CellId :=
  (environment.find? (fun entry => entry.1 == name)).map Prod.snd

structure Equation where
  head : String
  parameters : List String
  body : Atom
  deriving Repr

def Equation.lhs (equation : Equation) : Atom :=
  .expression (.symbol equation.head :: equation.parameters.map Atom.var)

def Equation.command (equation : Equation) :
    Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation.ProgramCommand Atom :=
  .defineEq equation.lhs equation.body

abbrev Program := List Equation

/-- Source-side binding. Physical row positions are retained separately from
the values of the equations; duplicate rows remain different activations. -/
inductive Binds : List String → List CellId → Environment → Prop where
  | nil : Binds [] [] []
  | cons {name names cell cells environment} :
      Binds names cells environment →
      Binds (name :: names) (cell :: cells) ((name, cell) :: environment)

theorem binds_iff (names : List String) (cells : List CellId) (environment : Environment) :
    Binds names cells environment ↔
      names.length = cells.length ∧ environment = names.zip cells := by
  induction names generalizing cells environment with
  | nil =>
      cases cells <;> constructor
      · intro h; cases h; simp
      · intro h; rcases h with ⟨_, rfl⟩; exact .nil
      · intro h; cases h
      · intro h; simp at h
  | cons name names ih =>
      cases cells with
      | nil => constructor <;> intro h
               · cases h
               · simp at h
      | cons cell cells =>
          constructor
          · intro h
            cases h with
            | cons rest =>
                obtain ⟨length, same⟩ := (ih _ _).mp rest
                simp [same, length]
          · rintro ⟨length, rfl⟩
            exact .cons ((ih _ _).mpr ⟨by simpa using length, rfl⟩)

inductive Rule where
  | builtin
  | equation (row : Nat)
  deriving Repr, DecidableEq

inductive Origin where
  | expression (term : Atom) (environment : Environment)
  | application (head : String) (arguments : List CellId)
  deriving Repr, DecidableEq

inductive Operation where
  | constructor (head : String)
  | application (head : String)
  | add
  deriving Repr, DecidableEq

inductive Local where
  | evaluate (term : Atom) (environment : Environment)
  | output (value : Produced Atom Empty String)
  | arguments (operation : Operation) (accumulated : List CellId)
      (remaining : List Atom) (environment : Environment)
  | normalize (operation : Operation) (accumulated : List Atom) (remaining : List CellId)
  | forward (cell : CellId)
  | bind (name : String) (value body : Atom) (environment : Environment)
  deriving Repr, DecidableEq

inductive Resume where
  | allocatedArgument (operation : Operation) (accumulated : List CellId)
      (remaining : List Atom) (environment : Environment)
  | normalizedChild (operation : Operation) (accumulated : List Atom) (remaining : List CellId)
  | applicationAllocated
  | forward
  | letAllocated (name : String) (body : Atom) (environment : Environment)
  deriving Repr, DecidableEq

abbrev Outcome := Produced Atom Empty String
abbrev NativeAction := Action Origin Local Resume Atom Empty String Empty
abbrev NativeMachine := Machine Origin Local Resume Rule Atom Empty String Empty

def failure (message : String) : Local := .output (.retryableFault (.domain message))

def finishedOperation : Operation → List Atom → Local
  | .constructor head, values => .output (.value (.expression (.symbol head :: values)))
  | .add, [.grounded (.int left), .grounded (.int right)] =>
      .output (.value (.grounded (.int (left + right))))
  | .add, _ => failure "integer arguments required"
  | .application _, _ => failure "application normalization is not a return"

def defined (program : Program) (head : String) : Bool :=
  program.any (fun equation => equation.head == head)

/-- Dispatch only inspects finite syntax. It neither recursively evaluates an
argument nor enumerates an argument's answer space. -/
def start (program : Program) : Atom → Environment → Local
  | .var name, environment =>
      match lookup environment name with
      | some cell => .forward cell
      | none => failure "unbound variable"
  | .expression [.symbol "let", .var name, value, body], environment =>
      .bind name value body environment
  | .expression (.symbol "+" :: arguments), environment =>
      .arguments .add [] arguments environment
  | .expression (.symbol head :: arguments), environment =>
      .arguments (if defined program head then .application head else .constructor head)
        [] arguments environment
  | value, _ => .output (.value value)

def rowCandidates (program : Program) (head : String) (arguments : List CellId) :
    List (Rule × Local) :=
  program.zipIdx.filterMap fun (equation, row) =>
    if equation.head = head ∧ equation.parameters.Nodup ∧
        equation.parameters.length = arguments.length then
      some (.equation row, .evaluate equation.body (equation.parameters.zip arguments))
    else none

/-- Independent source activation: a physical authored row and the positional
variable-binding derivation. No evaluator successor is a premise. -/
inductive Activates (program : Program) (head : String) (arguments : List CellId) :
    Rule → Local → Prop where
  | row {equation row environment}
      (member : (equation, row) ∈ program.zipIdx)
      (sameHead : equation.head = head)
      (distinct : equation.parameters.Nodup)
      (binding : Binds equation.parameters arguments environment) :
      Activates program head arguments (.equation row) (.evaluate equation.body environment)

theorem rowCandidates_iff (program : Program) (head : String) (arguments : List CellId)
    (rule : Rule) (state : Local) :
    (rule, state) ∈ rowCandidates program head arguments ↔
      Activates program head arguments rule state := by
  constructor
  · intro member
    obtain ⟨⟨equation, row⟩, located, result⟩ := List.mem_filterMap.mp member
    dsimp only at result
    split at result
    next valid =>
      have same := Option.some.inj result
      cases same
      exact .row located valid.1 valid.2.1
        ((binds_iff _ _ _).mpr ⟨valid.2.2, rfl⟩)
    next invalid => cases result
  · intro activation
    cases activation with
    | @row equation row environment member same distinct binding =>
        obtain ⟨length, rfl⟩ := (binds_iff _ _ _).mp binding
        exact List.mem_filterMap.mpr
          ⟨(equation, row), member, by simp [same, distinct, length]⟩

def alternatives (program : Program) : Origin → List (Rule × Local)
  | .expression term environment => [(.builtin, start program term environment)]
  | .application head arguments => rowCandidates program head arguments

def action : Local → NativeAction
  | .evaluate term environment =>
      .allocate (.expression term environment) .applicationAllocated
  | .output value => .done value
  | .forward cell => .demand cell .forward
  | .bind name value body environment =>
      .allocate (.expression value environment) (.letAllocated name body environment)
  | .arguments operation accumulated (first :: rest) environment =>
      .allocate (.expression first environment)
        (.allocatedArgument operation accumulated rest environment)
  | .arguments (.application head) accumulated [] _ =>
      .allocate (.application head accumulated) .applicationAllocated
  | .arguments operation accumulated [] _ =>
      match accumulated with
      | [] => .done (match finishedOperation operation [] with
          | .output outcome => outcome
          | _ => .retryableFault (.domain "invalid return"))
      | first :: rest => .demand first (.normalizedChild operation [] rest)
  | .normalize operation accumulated (first :: rest) =>
      .demand first (.normalizedChild operation accumulated rest)
  | .normalize operation accumulated [] =>
      .done (match finishedOperation operation accumulated with
        | .output outcome => outcome
        | _ => .retryableFault (.domain "invalid return"))

def afterDemand : Resume → Outcome → Local
  | .normalizedChild operation accumulated remaining, .value value =>
      .normalize operation (accumulated ++ [value]) remaining
  | .normalizedChild _ _ _, outcome => .output outcome
  | .forward, outcome => .output outcome
  | _, _ => failure "invalid demand return"

def afterAllocation : Resume → CellId → Local
  | .allocatedArgument operation accumulated remaining environment, cell =>
      .arguments operation (accumulated ++ [cell]) remaining environment
  | .applicationAllocated, cell => .forward cell
  | .letAllocated name body environment, cell =>
      .evaluate body ((name, cell) :: environment)
  | _, _ => failure "invalid allocation return"

def specification (program : Program) : Spec Origin Local Resume Rule Atom Empty String Empty where
  alternatives := alternatives program
  action := action
  afterDemand := afterDemand
  afterAllocation := afterAllocation

theorem no_foreign_effect (state : Local) (effect : Empty) (next : Local) :
    action state ≠ .perform effect next := by cases effect

/-- Every application successor is justified by a physical row and actual
positional bindings, and every such source activation is admitted. -/
theorem application_authority (program : Program) (head : String)
    (arguments : List CellId) (rule : Rule) (state : Local) :
    (rule, state) ∈ (specification program).alternatives (.application head arguments) ↔
      Activates program head arguments rule state :=
  rowCandidates_iff program head arguments rule state

def rootCell : CellId := ⟨1, [], 0, 0⟩

def initial (term : Atom) : NativeMachine where
  world :=
    { lineage := 1
      path := []
      heap :=
        { current := fun cell => if cell = rootCell then
            some { origin := .expression term [], cache := .suspended } else none
          spine := [.allocate rootCell (.expression term [])] }
      receipts := ReceiptGraph.empty
      nextCell := 1
      nextEvaluator := 1 }
  control := .force rootCell []

/-- The authored root's live map is exactly its retained allocation. -/
theorem initial_heap_recorded (term : Atom) : (initial term).world.heap.Recorded := by
  intro cell
  rfl

theorem initial_receipts_valid (term : Atom) : (initial term).world.receipts.Valid :=
  ReceiptGraph.empty_valid

def occurrenceSystem (program : Program) :=
  NeedInferenceControl.Reference.occurrenceSystem (specification program)

/-- The native source instance accepts any occurrence-preserving controller
and decidable answer demand. The controller may be the realization of an
authored command language; it does not supply application authority. -/
def executeControlled {Memory : Type*}
    (controller : Controller (WorkOccurrence NativeMachine) (Outcome × List Nat) Memory)
    (program : Program) (term : Atom) (goal : List (Outcome × List Nat) → Bool)
    (allowance : Nat) :=
  Mettapedia.GSLT.Core.DemandExecution.run (occurrenceSystem program)
    controller goal allowance
    (Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial
      controller [WorkOccurrence.root (initial term)])

/-- The actual authored controller preserves checkable receipt graphs in
every emitted answer and every retained work occurrence. The projection
checks recorded predecessors, without inferring minimal dependencies. -/
theorem controlled_receipts_check {Memory : Type*}
    (controller : Controller (WorkOccurrence NativeMachine) (Outcome × List Nat) Memory)
    (program : Program) (term : Atom) (goal : List (Outcome × List Nat) → Bool)
    (allowance : Nat) :
    (∀ occurrence ∈ (executeControlled controller program term goal allowance).search.frontier,
      occurrence.state.world.receipts.toCausalReceipt.check [] = true) ∧
    (∀ event ∈ (executeControlled controller program term goal allowance).search.events,
      event.origin.state.world.receipts.toCausalReceipt.check [] = true) := by
  exact NeedInferenceControl.Reference.demanded_receipts_check
    (specification program) controller goal allowance (initial_receipts_valid term)
    (initial_sound (occurrenceSystem program) [WorkOccurrence.root (initial term)])

/-- Breadth-first occurrence demand is one client of the same native control
interface, rather than a separate execution semantics. -/
def execute (program : Program) (term : Atom) (requested allowance : Nat) :=
  Mettapedia.GSLT.Core.DemandExecution.run (occurrenceSystem program)
    (Controller.fixed Scheduler.breadthFirst)
    (Mettapedia.GSLT.Core.DemandExecution.atLeast requested) allowance
    (Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial
      (Controller.fixed Scheduler.breadthFirst) [WorkOccurrence.root (initial term)])

theorem execute_eq_controlled (program : Program) (term : Atom)
    (requested allowance : Nat) :
    execute program term requested allowance =
      executeControlled (Controller.fixed Scheduler.breadthFirst) program term
        (Mettapedia.GSLT.Core.DemandExecution.atLeast requested) allowance :=
  rfl

/-- Rich source and independently implemented answer-only realization agree
on the whole successor list, including duplicate rule occurrences. -/
theorem native_step_erases (program : Program) (machine : NativeMachine) :
    (NeedReference.step (specification program) machine).map NeedExecution.eraseMachine =
      NeedExecution.step (specification program) (NeedExecution.eraseMachine machine) :=
  NeedExecution.step_commutes (specification program) machine

theorem native_core_no_invention (program : Program) (machine : NativeMachine)
    (next : NeedExecution.CoreMachine Origin Local Resume Rule Atom Empty String Empty)
    (member : next ∈ NeedExecution.step (specification program)
      (NeedExecution.eraseMachine machine)) :
    ∃ source ∈ NeedReference.step (specification program) machine,
      NeedExecution.eraseMachine source = next :=
  NeedExecution.core_step_lifts (specification program) member

/-- An authored control program and its answer goal publish only source
executions. Bindings, shared cells and return frames remain in the endpoint. -/
theorem controlled_emitted_source_path {Memory : Type*}
    (controller : Controller (WorkOccurrence NativeMachine) (Outcome × List Nat) Memory)
    (program : Program) (term : Atom) (goal : List (Outcome × List Nat) → Bool)
    (allowance : Nat)
    (event : Emission (WorkOccurrence NativeMachine) (Outcome × List Nat))
    (member : event ∈
      (executeControlled controller program term goal allowance).search.events) :
    Steps (specification program) event.origin.trace.length (initial term) event.origin.state ∧
      haltedOutcome event.origin.state = some event.value.1 ∧
      event.value.2 = event.origin.trace := by
  exact NeedInferenceControl.Reference.demanded_emission_has_steps
    (specification program) controller goal allowance
    (initial := initial term)
    (snapshot := Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial
      controller [WorkOccurrence.root (initial term)])
    (initial_sound (occurrenceSystem program) [WorkOccurrence.root (initial term)]) member

/-- The ordinary breadth-first client inherits the same source-path law. -/
theorem emitted_source_path (program : Program) (term : Atom) (requested allowance : Nat)
    (event : Emission (WorkOccurrence NativeMachine) (Outcome × List Nat))
    (member : event ∈ (execute program term requested allowance).search.events) :
    Steps (specification program) event.origin.trace.length (initial term) event.origin.state ∧
      haltedOutcome event.origin.state = some event.value.1 ∧
      event.value.2 = event.origin.trace := by
  exact controlled_emitted_source_path (Controller.fixed Scheduler.breadthFirst)
    program term (Mettapedia.GSLT.Core.DemandExecution.atLeast requested) allowance event member

def values (program : Program) (term : Atom) (requested allowance : Nat) : List Atom :=
  (execute program term requested allowance).search.events.filterMap fun event =>
    match event.value.1 with
    | .value value => some value
    | _ => none

/-- The independently defined receipt-erased machine realizes the same
breadth-first answer demand. The rich executor remains the source contract. -/
def executeCore (program : Program) (term : Atom) (requested allowance : Nat) :=
  Mettapedia.GSLT.Core.DemandExecution.run
    (NeedInferenceControl.Erasure.coreOccurrenceSystem (specification program))
    (Controller.fixed Scheduler.breadthFirst)
    (Mettapedia.GSLT.Core.DemandExecution.atLeast requested) allowance
    (Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial
      (Controller.fixed Scheduler.breadthFirst)
      [WorkOccurrence.root (NeedExecution.eraseMachine (initial term))])

def coreValues (program : Program) (term : Atom) (requested allowance : Nat) : List Atom :=
  (executeCore program term requested allowance).search.events.filterMap fun event =>
    match event.value.1 with
    | .value value => some value
    | _ => none

/-- Answers may be checked on the smaller realization without reducing the
causal receipt DAG. The proof preserves the original observation budget. -/
theorem values_eq_coreValues (program : Program) (term : Atom)
    (requested allowance : Nat) :
    values program term requested allowance = coreValues program term requested allowance := by
  have realized := NeedInferenceControl.Erasure.demanded_breadthFirst_run_erases
    (specification program) (Mettapedia.GSLT.Core.DemandExecution.atLeast requested) allowance
    (Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial
      (Controller.fixed Scheduler.breadthFirst) [WorkOccurrence.root (initial term)])
  have observed := congrArg (fun state => state.search.events.filterMap fun event =>
    match event.value.1 with
    | .value value => some value
    | _ => none) realized
  simpa [values, execute, coreValues, executeCore, occurrenceSystem,
    Mettapedia.GSLT.Core.InferenceControl.Snapshot.mapNodes,
    Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial,
    Mettapedia.GSLT.Core.BranchingTemporal.Snapshot.mapNodes,
    Mettapedia.GSLT.Core.BranchingTemporal.Emission.mapOrigin,
    Mettapedia.GSLT.Core.BranchingTemporal.initial,
    NeedInferenceControl.Erasure.eraseOccurrence, WorkOccurrence.root,
    List.filterMap_map, Function.comp_def] using observed

namespace Controls

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

def integer (value : Int) : Atom := .grounded (.int value)
def call (head : String) (arguments : List Atom := []) : Atom :=
  .expression (.symbol head :: arguments)
def coin : Program := [⟨"coin", [], integer 0⟩, ⟨"coin", [], integer 1⟩]
def twice : Equation := ⟨"twice", ["x"], call "Pair" [.var "x", .var "x"]⟩
def program : Program := coin ++ [twice,
  ⟨"integers", ["n"], call "integers" [call "+" [.var "n", integer 1]]⟩,
  ⟨"integers", ["n"], .var "n"⟩,
  ⟨"trees", [], call "S" [call "trees"]⟩,
  ⟨"trees", [], .symbol "Z"⟩]

example : (values program (call "twice" [call "coin"]) 4 400).length = 2 := by decide +kernel
example : values program (call "twice" [call "coin"]) 4 400 =
    [call "Pair" [integer 0, integer 0], call "Pair" [integer 1, integer 1]] := by decide +kernel
example : (values program (call "Pair" [call "coin", call "coin"]) 4 400).length = 4 := by decide +kernel

private abbrev CoreState := Mettapedia.GSLT.Core.DemandExecution.State
  (WorkOccurrence (NeedExecution.CoreMachine Origin Local Resume Rule Atom Empty String Empty))
  (Outcome × List Nat) Unit

private def coreStart (term : Atom) : CoreState :=
  Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial
    (Controller.fixed Scheduler.breadthFirst)
    [WorkOccurrence.root (NeedExecution.eraseMachine (initial term))]

private def coreRun (fuel : Nat) (state : CoreState) : CoreState :=
  Mettapedia.GSLT.Core.DemandExecution.run
    (NeedInferenceControl.Erasure.coreOccurrenceSystem (specification program))
    (Controller.fixed Scheduler.breadthFirst)
    (Mettapedia.GSLT.Core.DemandExecution.atLeast 7) fuel state

private def coreStopped (state : CoreState) : Bool :=
  Mettapedia.GSLT.Core.DemandExecution.stopped
    (Mettapedia.GSLT.Core.DemandExecution.atLeast 7) state

private theorem coreRun_add (first second : Nat) (state : CoreState) :
    coreRun (first + second) state = coreRun second (coreRun first state) :=
  Mettapedia.GSLT.Core.DemandExecution.run_add _ _ _ _ _ _

private theorem coreRun_of_stopped (fuel : Nat) (state : CoreState)
    (done : coreStopped state = true) : coreRun fuel state = state :=
  Mettapedia.GSLT.Core.DemandExecution.run_of_stopped _ _ _ _ _ done

private def coreObservation (state : CoreState) : List Atom :=
  state.search.events.filterMap fun event =>
    match event.value.1 with
    | .value value => some value
    | _ => none

private theorem values_observation_head (source : Program) (term : Atom) (requested : Nat) :
    values source term requested =
      fun fuel => coreObservation (executeCore source term requested fuel) := by
  funext fuel
  exact values_eq_coreValues source term requested fuel

private theorem execution_head (term : Atom) :
    executeCore program term 7 = fun fuel => coreRun fuel (coreStart term) := rfl

private theorem values_head (term : Atom) :
    values program term 7 = fun fuel => coreObservation (coreRun fuel (coreStart term)) :=
  (values_observation_head program term 7).trans
    (congrArg (fun runner => fun fuel => coreObservation (runner fuel)) (execution_head term))

private theorem checkpoint_observation (term : Atom) (fuel : Nat) (state : CoreState)
    (same : coreRun fuel (coreStart term) = state) :
    values program term 7 fuel = coreObservation state :=
  (congrFun (values_head term) fuel).trans (congrArg coreObservation same)

open Lean Meta Elab Command Term

local elab "checked_need_checkpoint " checkpoint:ident " := " expression:term : command => do
  let name := mkPrivateName (← getEnv) ((← getCurrNamespace) ++ checkpoint.getId)
  liftTermElabM do
    let original ← elabTermEnsuringType expression (mkConst ``CoreState)
    synthesizeSyntheticMVarsNoPostponing
    let original ← instantiateMVars original
    let arguments := original.getAppArgs
    unless original.isAppOfArity ``coreRun 2 do
      throwError "A Need checkpoint must use the existing core runner"
    let stoppedExpression := mkApp (mkConst ``coreStopped) arguments[1]!
    let stopped ← whnf stoppedExpression
    let (result, proof) ← if stopped.isConstOf ``Bool.true then do
        let proof ← mkAppM ``coreRun_of_stopped
          #[arguments[0]!, arguments[1]!, ← mkEqRefl (mkConst ``Bool.true)]
        pure (arguments[1]!, proof)
      else do
        let reduced ← Lean.Meta.Tactic.Cbv.cbvEntry original
        let proof ← match reduced with
          | .rfl .. => mkEqRefl original
          | .step _ proof .. => pure proof
        pure (reduced.getResultExpr original, proof)
    let type ← inferType original
    let environment ← getEnv
    if type.hasMVar || result.hasMVar || proof.hasMVar || type.hasFVar ||
        result.hasFVar || proof.hasFVar || type.hasSorry || result.hasSorry || proof.hasSorry ||
        environment.hasUnsafe type || environment.hasUnsafe result || environment.hasUnsafe proof then
      throwError "A Need checkpoint requires a closed safe proof"
    withOptions (fun options => debug.skipKernelTC.set (Elab.async.set options false) false) do
      addDecl <| .defnDecl {
        name, levelParams := [], type, value := result,
        hints := .regular 0, safety := .safe }
      addDecl <| .thmDecl {
        name := name ++ `checked, levelParams := [],
        type := ← mkEq original (mkConst name), value := proof }

/-- Emit separate kernel-checked lemmas, then compose the existing split-run
law. This controls proof reduction without changing the evaluator or budget. -/
local macro "checked_need_run " final:ident " from " initial:term:max " fuel " allowance:num :
    command => do
  let startName := Lean.mkIdent (final.getId ++ `start)
  let startProof := Lean.mkIdent (final.getId ++ `startPrefix)
  let start ← `(command| private def $startName : CoreState := $initial)
  let startReceipt ← `(command|
    private theorem $startProof : coreRun 0 $startName = $startName := rfl)
  let mut commands := #[start, startReceipt]
  let mut previous := startName
  let mut previousProof := startProof
  let mut used := 0
  let mut index := 0
  let total := allowance.getNat
  while used < total do
    let count := min (if used < 1500 then 50 else 10) (total - used)
    index := index + 1
    let checkpoint := Lean.mkIdent (Lean.Name.str final.getId ("checkpoint" ++ toString index))
    let checked := Lean.mkIdent (checkpoint.getId ++ `checked)
    let prefixName := Lean.mkIdent (checkpoint.getId ++ `prefix)
    let beforeSyntax : Lean.TSyntax `num := ⟨Lean.Syntax.mkNumLit (toString used)⟩
    let countSyntax : Lean.TSyntax `num := ⟨Lean.Syntax.mkNumLit (toString count)⟩
    let totalSyntax : Lean.TSyntax `num := ⟨Lean.Syntax.mkNumLit (toString (used + count))⟩
    let computed ← `(command|
      checked_need_checkpoint $checkpoint := coreRun $countSyntax $previous)
    let receipt ← `(command|
      private theorem $prefixName : coreRun $totalSyntax $startName = $checkpoint := by
        calc
          coreRun $totalSyntax $startName =
            coreRun $countSyntax (coreRun $beforeSyntax $startName) :=
              coreRun_add $beforeSyntax $countSyntax $startName
          _ = coreRun $countSyntax $previous := congrArg (coreRun $countSyntax) $previousProof
          _ = $checkpoint := $checked)
    commands := commands.push computed |>.push receipt
    previous := checkpoint
    previousProof := prefixName
    used := used + count
  let value ← `(command| private noncomputable def $final : CoreState := $previous)
  let finalProof := Lean.mkIdent (final.getId ++ `checked)
  let receipt ← `(command|
    private theorem $finalProof : coreRun $allowance $startName = $final := $previousProof)
  commands := commands.push value |>.push receipt
  return ⟨Lean.mkNullNode (commands.map (·.raw))⟩


private def integerQuery : Atom := call "integers" [integer 0]
private def additionQuery : Atom := call "+" [integer 10, integerQuery]

checked_need_run integerRun from (coreStart integerQuery) fuel 3000
checked_need_run additionRun from (coreStart additionQuery) fuel 3000

/-- Recursive-first equations retain the original seven-answer budget. -/
theorem recursive_integers_seven :
    (values program (call "integers" [integer 0]) 7 3000).length = 7 := by
  exact (congrArg List.length
    (checkpoint_observation integerQuery 3000 integerRun integerRun.checked)).trans
    (by decide +kernel)

example : (values program (call "trees") 7 3000).length = 7 := by decide +kernel

/-- A non-tail return adds ten after recursive answer production. -/
theorem recursive_addition_seven :
    values program (call "+" [integer 10, call "integers" [integer 0]]) 7 3000 =
      (List.range 7).map (fun n => integer (Int.ofNat n + 10)) := by
  exact (checkpoint_observation additionQuery 3000 additionRun additionRun.checked).trans
    (by decide +kernel)

end Controls

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeEquationNeed
