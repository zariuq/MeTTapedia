import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnPublication
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnAliasEntry

/-!
# Composed source-to-packet alias theorem

Every finite run prefix of the maintained owned source driver preserves its
return invariant and publishes only packets tied to the reached input read.
The theorem does not assume completion, successful body execution, or a
value-only callee result. Clause entry earns the initial obligation from the
actual source matcher and the return-syntax checker.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnRun

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open ScopedReturnScopes ScopedReturnPublication

theorem run_packets_read_input {Context : Type} (inputs : Context → Atom) (program : SpaceSemantics.Program)
    (fuel : Nat) (source : ScopedCursor Context)
    (validScopes : EagerDFS.ScopesValid source.2.scopes) (valid : Stack inputs source.2.scopes) :
    ∀ packet ∈ ((ScopedQuerySource.ownedMachine .eagerValue program).run fuel source).1,
      PacketReadsInput inputs packet := by
  induction fuel generalizing source with
  | zero => simp [Machine.run]
  | succ fuel ih =>
      have scopeSafe := ScopedReturnOwned.owned_step_scope_validity program source validScopes
      have returnSafe := ScopedReturnOwned.owned_step_preserves inputs program source validScopes valid
      cases step : ScopedQuerySource.ownedStep .eagerValue program source with
      | silent next =>
          rw [step] at scopeSafe returnSafe
          have continued := ih next scopeSafe (returnSafe next (by simp [RefinementTransport.actionStates]))
          simpa only [Machine.run, ScopedQuerySource.ownedMachine, step] using continued
      | publish events next =>
          have published := published_packets_read_input inputs program source next events validScopes valid step
          rw [step] at scopeSafe returnSafe
          have continued := ih next scopeSafe (returnSafe next (by simp [RefinementTransport.actionStates]))
          simp only [Machine.run, ScopedQuerySource.ownedMachine, step]
          intro packet member
          rcases List.mem_append.mp member with current | later
          · exact published packet current
          · exact continued packet later
      | finish final => simp [Machine.run, ScopedQuerySource.ownedMachine, step]
      | call request retained => simp [Machine.run, ScopedQuerySource.ownedMachine, step]
      | fail events => exact False.elim (owned_has_no_failure_packets program source validScopes events step)

/-- A body region starts with the actual selected source record. Equal
context labels do not choose or reset the recipe; clause freshening earned
that recipe from the common head equation. -/
theorem checked_clause_body_run {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (context : Context) (origins : List Nat)
    (control : Control) (head : String) (arguments : List Atom) (destination : Atom)
    (occurrence : Nat) (equation : SpaceSemantics.Equation) (next : Control)
    (index : Nat) (argument : Atom) (formalName : String) (inspectionFuel fuel : Nat)
    (selected : ClauseChoice.attempt control head arguments destination [] occurrence equation = some next)
    (actual : arguments[index]? = some argument) (formal : equation.arguments[index]? = some (.var formalName))
    (target : control.destination = destination)
    (checked : ScopedReturnSyntax.checksSurfaceReturn (.var formalName) inspectionFuel equation.body = true) :
    ∀ packet ∈ ((ScopedQuerySource.ownedMachine .eagerValue program).run fuel
      (allocator, ⟨world, [⟨[(next, context, origins ++ [occurrence])], [], none⟩]⟩)).1,
      ∃ environment, resolve packet.bindings = some environment ∧
        packet.value = read environment argument := by
  have entered := ScopedReturnAliasEntry.selected_variable_alias_contract control head arguments destination []
    occurrence equation next index argument formalName inspectionFuel selected actual formal target checked
  have allPackets := run_packets_read_input (fun _ : Context => argument) program fuel
    (allocator, ⟨world, [⟨[(next, context, origins ++ [occurrence])], [], none⟩]⟩)
    (.root _ _) (.root _ (by intro work member; cases List.mem_singleton.mp member; exact entered))
  intro packet present
  obtain ⟨_context, environment, resolved, observed⟩ := allPackets packet present
  exact ⟨environment, resolved, observed⟩

/-- Ground input packets retain the exact produced occurrence count and
order: this is a list equation, not set membership or a deduplicated bag. -/
theorem checked_ground_clause_body_run {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (context : Context) (origins : List Nat)
    (control : Control) (head : String) (arguments : List Atom) (destination : Atom)
    (occurrence : Nat) (equation : SpaceSemantics.Equation) (next : Control)
    (index : Nat) (argument : Atom) (formalName : String) (inspectionFuel fuel : Nat)
    (selected : ClauseChoice.attempt control head arguments destination [] occurrence equation = some next)
    (actual : arguments[index]? = some argument) (formal : equation.arguments[index]? = some (.var formalName))
    (target : control.destination = destination)
    (checked : ScopedReturnSyntax.checksSurfaceReturn (.var formalName) inspectionFuel equation.body = true)
    (ground : (encode argument).isGround) :
    let packets := ((ScopedQuerySource.ownedMachine .eagerValue program).run fuel
      (allocator, ⟨world, [⟨[(next, context, origins ++ [occurrence])], [], none⟩]⟩)).1
    packets.map CollectedAnswer.value = List.replicate packets.length argument := by
  dsimp only
  apply List.map_eq_replicate_iff.mpr
  intro packet present
  obtain ⟨environment, _resolved, observed⟩ := checked_clause_body_run program allocator world context origins
    control head arguments destination occurrence equation next index argument formalName inspectionFuel fuel
    selected actual formal target checked packet present
  exact observed.trans (ProtectedSlots.read_ground environment argument ground)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnRun
