import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnMachine
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnFunction

/-!
# Actual checked clause frontiers enter the typed body region

The existing source checker inspects every equation of the named head. The
existing clause selector supplies fresh matching records, and the ordinary
typed overlay executes the resulting body frontier. No body-success or
already-implements-the-return premise is supplied.

The entry here is the post-selection body region. The enclosing typed call's
argument/result frame and final publication remain separate joins.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnEntry

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS (World)
open EagerDFS.Destination
open PettaOccurrenceOverlay PettaCallerReturnFrames

def selectedWork {User : Type} (program : SpaceSemantics.Program) (control : DControl)
    (head : String) (arguments : List Atom) (destination : Atom) (user : User) (origins : List Nat) : List (Work User) :=
  (ClauseChoice.choices program control head arguments destination []).map fun choice =>
    (predicateEntry 0 choice.2, ⟨user, []⟩, origins ++ [choice.1])

def seed {User : Type} (program : SpaceSemantics.Program) (control : DControl)
    (head : String) (arguments : List Atom) (destination : Atom) (user : User) (origins : List Nat)
    (allocator : Allocator) (world : World) : State User :=
  (allocator, ⟨world, [⟨selectedWork program control head arguments destination user origins, [], none⟩]⟩)

def enter {User : Type} (services : Services User) (program : SpaceSemantics.Program) (control : DControl)
    (head : String) (arguments : List Atom) (destination : Atom) (user : User) (origins : List Nat)
    (allocator : Allocator) (world : World) : State User :=
  let before := seed program control head arguments destination user origins allocator world
  let work := (selectedWork program control head arguments destination user origins).map fun item =>
    (protect services before item.1 item.2.1, item.2)
  (allocator, ⟨world, [⟨work, [], none⟩]⟩)

theorem checked_selected_work {User : Type} (program : SpaceSemantics.Program) (head : String)
    (index inspectionFuel : Nat)
    (checked : Bridges.ScopedReturnFunction.checksHead program head index inspectionFuel = true)
    (control : DControl) (arguments : List Atom) (argument destination : Atom)
    (actual : arguments[index]? = some argument) (target : control.destination = destination)
    (user : User) (origins : List Nat) :
    ∀ item ∈ selectedWork program control head arguments destination user origins,
      Frames argument item.1 item.2.1.calls := by
  intro item member
  obtain ⟨choice, present, rfl⟩ := List.mem_map.mp member
  exact .root (Bridges.ScopedReturnFunction.checked_frontier_aliases program head index inspectionFuel checked
    control arguments argument destination actual target choice present)

theorem checked_entry_invariant {User : Type} (services : Services User) (program : SpaceSemantics.Program)
    (head : String) (index inspectionFuel : Nat)
    (checked : Bridges.ScopedReturnFunction.checksHead program head index inspectionFuel = true)
    (control : DControl) (arguments : List Atom) (argument destination : Atom)
    (actual : arguments[index]? = some argument) (target : control.destination = destination)
    (user : User) (origins : List Nat) (allocator : Allocator) (world : World) :
    PettaCallerReturnMachine.Invariant (fun _ : User => argument)
      (enter services program control head arguments destination user origins allocator world) := by
  refine ⟨.root _ _, ?_⟩
  change Bridges.ScopedReturnScopes.Stack (fun _ : Context User => argument)
    [PettaCallerReturnView.scope _]
  apply Bridges.ScopedReturnScopes.Stack.root
  intro item member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  apply (PettaCallerReturnView.work_iff (fun _ : User => argument) original).mpr
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp present
  exact (checked_selected_work program head index inspectionFuel checked control arguments argument destination actual target
    user origins source sourceMember).protect services _ _

/-- This instantiates the all-phase theorem with the earned source entry,
including actual typed calls in prefix computations. The conclusion concerns
retained states, not yet arbitrary published values. -/
theorem checked_body_run_retained {User : Type} (services : Services User) (program : SpaceSemantics.Program)
    (head : String) (index inspectionFuel : Nat)
    (checked : Bridges.ScopedReturnFunction.checksHead program head index inspectionFuel = true)
    (control : DControl) (arguments : List Atom) (argument destination : Atom)
    (actual : arguments[index]? = some argument) (target : control.destination = destination)
    (user : User) (origins : List Nat) (allocator : Allocator) (world : World) (fuel : Nat) :
    ∀ final, PettaCallerReturnMachine.exitState
      ((PettaOccurrenceOverlay.machine services .eagerValue program).run fuel
        (enter services program control head arguments destination user origins allocator world)).2 = some final →
      PettaCallerReturnMachine.Invariant (fun _ : User => argument) final :=
  PettaCallerReturnMachine.run_retained_invariant (fun _ : User => argument) services program fuel _
    (checked_entry_invariant services program head index inspectionFuel checked control arguments argument destination
      actual target user origins allocator world)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnEntry
