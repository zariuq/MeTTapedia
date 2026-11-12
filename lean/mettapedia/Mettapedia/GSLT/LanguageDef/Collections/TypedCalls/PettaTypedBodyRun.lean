import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaFrameScopeMachine
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnEntry

/-!
# Source-checked typed body regions preserve complete answer prefixes

The return invariant and scope-indexed frame invariant are both derived at
entry and preserved by the actual occurrence overlay. Publication consequently
reads the original argument through each packet's reached logical record.
No successful execution, termination or precomputed body answer is assumed.

This body-region theorem permits typed calls in arbitrary prefix computations.
The enclosing typed root frame, constructor formal recipes and native metadata
representation remain separate connections.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTypedBodyRun

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open PettaOccurrenceOverlay PettaFrameScopes

theorem packets_read_input {User : Type} (inputs : User → Atom) (services : Services User)
    (program : SpaceSemantics.Program) (fuel : Nat) (source : State User)
    (valid : PettaCallerReturnMachine.Invariant inputs source) (bounded : Bounded source) :
    ∀ packet ∈ ((PettaOccurrenceOverlay.machine services .eagerValue program).run fuel source).1,
      Bridges.ScopedReturnPublication.PacketReadsInput inputs packet := by
  induction fuel generalizing source with
  | zero => simp [Machine.run]
  | succ fuel ih =>
      have callsSafe := PettaFrameScopeMachine.step_keeps services program source bounded
      have returnSafe := PettaCallerReturnMachine.step_invariant inputs services program source valid
      cases advanced : PettaOccurrenceOverlay.step services .eagerValue program source with
      | silent next =>
          rw [advanced] at callsSafe returnSafe
          simpa only [Machine.run, PettaOccurrenceOverlay.machine, advanced] using
            ih next (returnSafe next (by simp [PettaOccurrenceBinding.retained]))
              (callsSafe next (by simp [PettaOccurrenceBinding.retained]))
      | publish events next =>
          have observed := PettaCallerReturnPublication.published_packets_read_input inputs services program
            source next events valid (root_depths source bounded) advanced
          rw [advanced] at callsSafe returnSafe
          have later := ih next (returnSafe next (by simp [PettaOccurrenceBinding.retained]))
            (callsSafe next (by simp [PettaOccurrenceBinding.retained]))
          simp only [Machine.run, PettaOccurrenceOverlay.machine, advanced]
          intro packet member
          rcases List.mem_append.mp member with current | remaining
          · exact observed packet current
          · exact later packet remaining
      | finish final => simp [Machine.run, PettaOccurrenceOverlay.machine, advanced]
      | call request retained => simp [Machine.run, PettaOccurrenceOverlay.machine, advanced]
      | fail events => exact False.elim (PettaFrameScopeMachine.step_no_failure services program source bounded events advanced)

theorem entered_frames_bounded {User : Type} (services : Services User) (program : SpaceSemantics.Program)
    (control : DControl) (head : String) (arguments : List Atom) (destination : Atom)
    (user : User) (origins : List Nat) (allocator : Allocator) (world : World) :
    Bounded (PettaCallerReturnEntry.enter services program control head arguments destination user origins allocator world) := by
  apply Scoped.root
  intro work member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨row, _selected, rfl⟩ := List.mem_map.mp present
  exact CallsAt.empty _ user

/-- Actual complete clause selection earns the initial return obligation.
Both invariants then hold for every observed finite prefix, even when a
producer refuses, recurses forever or suspends at an unserved guard. -/
theorem checked_body_packets {User : Type} (services : Services User) (program : SpaceSemantics.Program)
    (head : String) (index inspectionFuel : Nat)
    (checked : Bridges.ScopedReturnFunction.checksHead program head index inspectionFuel = true)
    (control : DControl) (arguments : List Atom) (argument destination : Atom)
    (actual : arguments[index]? = some argument) (target : control.destination = destination)
    (user : User) (origins : List Nat) (allocator : Allocator) (world : World) (fuel : Nat) :
    ∀ packet ∈ ((PettaOccurrenceOverlay.machine services .eagerValue program).run fuel
      (PettaCallerReturnEntry.enter services program control head arguments destination user origins allocator world)).1,
      ∃ environment, resolve packet.bindings = some environment ∧ packet.value = read environment argument := by
  have packets := packets_read_input (fun _ : User => argument) services program fuel _
    (PettaCallerReturnEntry.checked_entry_invariant services program head index inspectionFuel checked
      control arguments argument destination actual target user origins allocator world)
    (entered_frames_bounded services program control head arguments destination user origins allocator world)
  intro packet present
  obtain ⟨_user, environment, resolved, observed⟩ := packets packet present
  exact ⟨environment, resolved, observed⟩

/-- The complete ordered value prefix retains every actual occurrence.
There is no conversion to a set, deduplication or assumption of success. -/
theorem checked_ground_body_values {User : Type} (services : Services User) (program : SpaceSemantics.Program)
    (head : String) (index inspectionFuel : Nat)
    (checked : Bridges.ScopedReturnFunction.checksHead program head index inspectionFuel = true)
    (control : DControl) (arguments : List Atom) (argument destination : Atom)
    (actual : arguments[index]? = some argument) (target : control.destination = destination)
    (user : User) (origins : List Nat) (allocator : Allocator) (world : World) (fuel : Nat)
    (ground : (encode argument).isGround) :
    let packets := ((PettaOccurrenceOverlay.machine services .eagerValue program).run fuel
      (PettaCallerReturnEntry.enter services program control head arguments destination user origins allocator world)).1
    packets.map CollectedAnswer.value = List.replicate packets.length argument := by
  dsimp only
  apply List.map_eq_replicate_iff.mpr
  intro packet present
  obtain ⟨environment, _resolved, observed⟩ := checked_body_packets services program head index inspectionFuel checked
    control arguments argument destination actual target user origins allocator world fuel packet present
  exact observed.trans (ProtectedSlots.read_ground environment argument ground)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTypedBodyRun
