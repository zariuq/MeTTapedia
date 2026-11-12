import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckpointReturn
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedEquationSource

/-!
# Exact clause-selection seeds also earn the region checkpoint invariant

The source equation operation installs the selected controls without a second
protection pass over the generated frontier. This entry uses that existing
seed, keeping its reserved fields exact. It does not identify the seed with
the separately protected body-entry adapter or assume whole-call placement.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSeededRegionEntry

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay PettaFrameScopes
open PettaBodyFrameEmbedding PettaBodySourceEmbedding PettaBodyRegionTransport PettaBodyCheckpoint

def readyRoot {User : Type} (allocator : Allocator) (world : EagerDFS.World)
    (control : DControl) (user : User) (origins : List Nat) (saved : CallFrame) : State User :=
  (allocator, ⟨world, [⟨[(control, ⟨user, [saved]⟩, origins)], [], none⟩]⟩)

/-- The actual source equation operation installs the exact seed and reads
the ready argument recipes at the reached solver. This is not the additional
protection pass used by the convenience entry adapter. -/
theorem canonical_equation_entry {User : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : EagerDFS.World) (control : DControl)
    (user : User) (origins : List Nat) (saved : CallFrame)
    (head : String) (arguments : List Atom) (destination : Atom) (environment : Environment)
    (atCall : control.goals = [.invoke head arguments destination])
    (ordinary : (Eval.ioHead head || StdLib.known head) = false)
    (declared : program.equations.any (·.head == head) = true)
    (resolved : resolve control.bindings = some environment) :
    let before := readyRoot allocator world control user origins saved
    let selectedControl := protectControl control (collectionSupport before.2)
    enterEquations? program before.2 = some
      (state saved (PettaCallerReturnEntry.seed program selectedControl head (arguments.map (read environment))
        destination user origins allocator world)).2 := by
  dsimp only
  have entered := enterEquations_constructs program world
    (⟨[(control, (⟨user, [saved]⟩ : Context User), origins)], [], none⟩ : Scope User)
    [] control (⟨user, [saved]⟩ : Context User) origins [] head arguments destination [] environment
    rfl atCall ordinary declared resolved
  simpa only [readyRoot, equationWork, PettaCallerReturnEntry.seed, PettaCallerReturnEntry.selectedWork,
    state, scope, work, context, List.length_nil, List.map_cons, List.map_nil, List.map_map,
    List.append_nil, List.nil_append, Function.comp_def, Option.map_none] using entered

theorem source_check_derives_equation_presence (program : SpaceSemantics.Program)
    (head : String) (index inspectionFuel : Nat)
    (checked : Bridges.ScopedReturnFunction.checksHead program head index inspectionFuel = true) :
    program.equations.any (·.head == head) = true := by
  obtain ⟨equation, present, named⟩ := Bridges.ScopedReturnFunction.checked_has_head program head index inspectionFuel checked
  exact List.any_eq_true.mpr ⟨equation, present, by simpa using named⟩

/-- A real ready typed activation enters the exact fresh clause frontier.
The output is still unbound and the head is an ordinary equation head;
special case ownership is not bypassed by the admission. -/
theorem actual_ready_body_entry {User : Type} (operations : Services User)
    (program : SpaceSemantics.Program) (allocator : Allocator) (world : EagerDFS.World)
    (control : DControl) (user : User) (origins : List Nat) (saved : CallFrame)
    (environment : Environment) (resultName : String)
    (atCall : control.goals = [.invoke saved.head saved.ready saved.callDestination])
    (resolved : resolve control.bindings = some environment)
    (unbound : read environment saved.callDestination = .var resultName)
    (unknown : StdLib.known saved.head = false) (notIO : Eval.ioHead saved.head = false)
    (notCase : saved.head ≠ "case") (declared : program.equations.any (·.head == saved.head) = true)
    (phase : saved.phase = .body) (depth : saved.scopeDepth = 1) :
    let before := readyRoot allocator world control user origins saved
    let selectedControl := protectControl control (collectionSupport before.2)
    PettaOccurrenceOverlay.step operations .eagerValue program before = .silent
      (state saved (PettaCallerReturnEntry.seed program selectedControl saved.head (saved.ready.map (read environment))
        saved.callDestination user origins allocator world)) := by
  dsimp only
  let before := readyRoot allocator world control user origins saved
  let selectedControl := protectControl control (collectionSupport before.2)
  let selected := ClauseChoice.choices program selectedControl saved.head (saved.ready.map (read environment))
    saved.callDestination []
  let after := state saved (PettaCallerReturnEntry.seed program selectedControl saved.head (saved.ready.map (read environment))
    saved.callDestination user origins allocator world)
  have notParse : saved.head ≠ "parse" := by
    intro same
    simp [same, StdLib.known] at unknown
  have notMatch : saved.head ≠ "match" := by
    intro same
    simp [same, StdLib.known] at unknown
  have entered := Bridges.ScopedQuerySource.Equations.enter .eagerValue program allocator world
    (⟨[(control, (⟨user, [saved]⟩ : Context User), origins)], [], none⟩ : Scope User) []
    control (⟨user, [saved]⟩ : Context User) origins [] saved.head saved.ready saved.callDestination []
    environment resultName selected rfl atCall resolved unbound notParse unknown notIO declared
    ((ClauseChoice.choices_iff_frontier _ _ _ _ _ _ _).mp rfl)
  have base : Bridges.ScopedQuerySource.step .eagerValue program before = .silent after := by
    apply Option.some.inj
    simpa only [Bridges.ScopedQuerySource.machine, before, after, selected, selectedControl, readyRoot,
      PettaCallerReturnEntry.seed, PettaCallerReturnEntry.selectedWork, state, scope, work, context,
      List.length_nil, List.map_cons, List.map_nil, List.map_map, Function.comp_def,
      List.append_nil, List.nil_append, Option.map_none] using entered
  have noEntry : Bridges.ScopedCaseSource.entryStep before = none := by
    simp [Bridges.ScopedCaseSource.entryStep, before, readyRoot, atCall]
  have noCase : Bridges.ScopedCaseSource.readyStep Bridges.ScopedQuerySource.plainQueryPattern before = none := by
    simp only [Bridges.ScopedCaseSource.readyStep, before, readyRoot, atCall]
    split
    next key rows destination older same =>
      have headEq : saved.head = "case" := by
        simp only [List.cons.injEq, Goal.invoke.injEq] at same
        tauto
      exact (notCase headEq).elim
    next => rfl
  have noOwnership : Bridges.ScopedQuerySource.ownershipStep program before = none := by
    simp [Bridges.ScopedQuerySource.ownershipStep, before, readyRoot, atCall, notMatch]
  have owned := Bridges.ScopedQuerySource.owned_keeps_completed_step .eagerValue program before after
    noOwnership noEntry noCase base
  simp only [PettaOccurrenceOverlay.step, readyRoot, depth, List.length_cons, List.length_nil,
    if_true, phase, atCall, List.isEmpty_cons, Bool.false_eq_true, if_false, delegate]
  exact congrArg liftSource owned

theorem seed_frames_bounded {User : Type} (program : SpaceSemantics.Program) (control : DControl)
    (head : String) (arguments : List Atom) (destination : Atom) (user : User) (origins : List Nat)
    (allocator : Allocator) (world : EagerDFS.World) :
    Bounded (PettaCallerReturnEntry.seed program control head arguments destination user origins allocator world) := by
  apply Scoped.root
  intro item member
  obtain ⟨choice, _selected, rfl⟩ := List.mem_map.mp member
  exact CallsAt.empty _ user

theorem checked_seed_invariant {User : Type} (program : SpaceSemantics.Program)
    (head : String) (index inspectionFuel : Nat)
    (checked : Bridges.ScopedReturnFunction.checksHead program head index inspectionFuel = true)
    (control : DControl) (arguments : List Atom) (argument destination : Atom)
    (actual : arguments[index]? = some argument) (target : control.destination = destination)
    (user : User) (origins : List Nat) (allocator : Allocator) (world : EagerDFS.World) :
    PettaCallerReturnMachine.Invariant (fun _ : User => argument)
      (PettaCallerReturnEntry.seed program control head arguments destination user origins allocator world) := by
  refine ⟨.root _ _, ?_⟩
  change Bridges.ScopedReturnScopes.Stack (fun _ : Context User => argument) [PettaCallerReturnView.scope _]
  apply Bridges.ScopedReturnScopes.Stack.root
  intro item member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  apply (PettaCallerReturnView.work_iff (fun _ : User => argument) original).mpr
  exact PettaCallerReturnEntry.checked_selected_work program head index inspectionFuel checked control arguments
    argument destination actual target user origins original present

theorem checked_seed_checkpoint {User : Type} (saved : CallFrame) (original : Services User)
    (program : SpaceSemantics.Program) (head : String) (index inspectionFuel : Nat)
    (checked : Bridges.ScopedReturnFunction.checksHead program head index inspectionFuel = true)
    (control : DControl) (arguments : List Atom) (argument destination : Atom)
    (actual : arguments[index]? = some argument) (target : control.destination = destination)
    (user : User) (origins : List Nat) (allocator : Allocator) (world : EagerDFS.World)
    (phase : saved.phase = .body) (depth : saved.scopeDepth = 1) (fuel : Nat) (final : State User)
    (captured : ((PettaBodyRegionTransport.machine carriedExit original program).run fuel
      (state saved (PettaCallerReturnEntry.seed program control head arguments destination
        user origins allocator world))).2 = .suspended (.inl ()) final) :
    ∃ reached, final = state saved reached ∧ Nonempty (ExitView (fun _ : User => argument) reached) := by
  exact PettaCheckpointReturn.carried_checkpoint_view (fun _ : User => argument) saved original program fuel _ final phase depth
    (checked_seed_invariant program head index inspectionFuel checked control arguments argument destination actual target
      user origins allocator world)
    (seed_frames_bounded program control head arguments destination user origins allocator world) captured

/-- The source-ready activation, its actual first equation-entry step and
all following body-region steps earn the checkpoint contract together.
Neither the body result nor successful execution is supplied as a premise. -/
theorem ready_checkpoint_contract {User : Type} (operations : Services User)
    (program : SpaceSemantics.Program) (allocator : Allocator) (world : EagerDFS.World)
    (control : DControl) (user : User) (origins : List Nat) (saved : CallFrame)
    (environment : Environment) (resultName : String) (index inspectionFuel : Nat) (argument : Atom)
    (checked : Bridges.ScopedReturnFunction.checksHead program saved.head index inspectionFuel = true)
    (atCall : control.goals = [.invoke saved.head saved.ready saved.callDestination])
    (target : control.destination = saved.callDestination)
    (actual : (saved.ready.map (read environment))[index]? = some argument)
    (resolved : resolve control.bindings = some environment)
    (unbound : read environment saved.callDestination = .var resultName)
    (unknown : StdLib.known saved.head = false) (notIO : Eval.ioHead saved.head = false)
    (notCase : saved.head ≠ "case") (phase : saved.phase = .body) (depth : saved.scopeDepth = 1)
    (fuel : Nat) (final : State User)
    (captured : ((PettaBodyRegionTransport.machine carriedExit operations program).run (fuel + 1)
      (readyRoot allocator world control user origins saved)).2 = .suspended (.inl ()) final) :
    ∃ reached, final = state saved reached ∧ Nonempty (ExitView (fun _ : User => argument) reached) := by
  let before := readyRoot allocator world control user origins saved
  let selectedControl := protectControl control (collectionSupport before.2)
  let seeded := PettaCallerReturnEntry.seed program selectedControl saved.head
    (saved.ready.map (read environment)) saved.callDestination user origins allocator world
  have entered : PettaOccurrenceOverlay.step operations .eagerValue program before = .silent (state saved seeded) :=
    actual_ready_body_entry operations program allocator world control user origins saved environment resultName
      atCall resolved unbound unknown notIO notCase
      (source_check_derives_equation_presence program saved.head index inspectionFuel checked) phase depth
  have notStopped : carriedExit before = false := by
    simp [before, readyRoot, carriedExit, atCall]
  have first : PettaBodyRegionTransport.step carriedExit operations program before = .silent (state saved seeded) := by
    simp only [PettaBodyRegionTransport.step, notStopped, Bool.false_eq_true, if_false, entered, Transition.relabel]
  have remainder : ((PettaBodyRegionTransport.machine carriedExit operations program).run fuel (state saved seeded)).2 =
      .suspended (.inl ()) final := by
    have firstMachine : (PettaBodyRegionTransport.machine carriedExit operations program).step before =
        some (.silent (state saved seeded)) := by
      simpa only [PettaBodyRegionTransport.machine_step] using congrArg some first
    have afterEntry := (PettaBodyRegionTransport.machine carriedExit operations program).run_succ_silent
      (fuel := fuel) firstMachine
    have observed : ((PettaBodyRegionTransport.machine carriedExit operations program).run (fuel + 1) before).2 =
        .suspended (.inl ()) final := captured
    rw [afterEntry] at observed
    exact observed
  exact checked_seed_checkpoint saved operations program saved.head index inspectionFuel checked selectedControl
    (saved.ready.map (read environment)) argument saved.callDestination actual target user origins allocator world
    phase depth fuel final remainder

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSeededRegionEntry
