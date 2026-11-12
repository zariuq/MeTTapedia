import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnOwned
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnEntry
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnPublication

/-!
# Authored compound returns through every finite owned-source run

Clause matching earns the initial recipe and record relation. The complete
maintained dispatcher preserves them through the reached frames, and every
published packet observes that reached input read. No terminating run,
successful body, completed result service or native plan adequacy is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnRun

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open DestinationDataReturnScopes
open ScopedReturnPublication (PacketReadsInput)

theorem published_input_witness {Context : Type} (inputs : Context → Atom) (program : SpaceSemantics.Program)
    (before after : ScopedCursor Context) (events : List CollectedAnswer)
    (validScopes : EagerDFS.ScopesValid before.2.scopes) (valid : Stack program inputs before.2.scopes)
    (published : scopeStep .eagerValue program before = .publish events after) :
    ∃ scope control context pending value bindings origins environment,
      before.2.scopes = [scope] ∧ scope.frontier = (control, context, origins) :: pending ∧
      events = [⟨value, bindings, origins, []⟩] ∧ bindings = control.bindings ∧
      resolve bindings = some environment ∧ value = read environment (inputs context) := by
  have derivation := (Source.scoped_step_iff_source .eagerValue program before validScopes _).mp published
  obtain ⟨root, rootScopes⟩ := ScopedReturnPublication.source_publication_is_root derivation validScopes events rfl
  obtain ⟨scope, parents, control, context, pending, value, bindings, origins, environment,
    scopes, frontier, terminal, resolved, emitted, records, output, solved⟩ :=
    scope_published_origin .eagerValue program before after events published
  have roots : scope :: parents = [root] := scopes.symm.trans rootScopes
  cases roots
  have holds := (rootScopes ▸ valid).root_work (control, context, origins) (frontier ▸ List.mem_cons_self)
  refine ⟨_, control, context, pending, value, bindings, origins, environment,
    rootScopes, frontier, emitted, records, ?_, ?_⟩
  · simpa only [records] using resolved
  · rw [output]
    exact DestinationDataReturnState.terminal_alias_observation holds terminal environment resolved

theorem published_packets_read_input {Context : Type} (inputs : Context → Atom) (program : SpaceSemantics.Program)
    (before after : ScopedCursor Context) (events : List CollectedAnswer)
    (validScopes : EagerDFS.ScopesValid before.2.scopes) (valid : Stack program inputs before.2.scopes)
    (published : ScopedQuerySource.ownedStep .eagerValue program before = .publish events after) :
    ∀ packet ∈ events, PacketReadsInput inputs packet := by
  have raw := ScopedQueryBinding.owned_publication_is_raw .eagerValue program before after events published
  obtain ⟨scope, control, context, pending, value, bindings, origins, environment,
    scopes, frontier, emitted, records, resolved, output⟩ :=
    published_input_witness inputs program before after events validScopes valid raw
  intro packet present
  rw [emitted] at present
  cases List.mem_singleton.mp present
  exact ⟨context, environment, resolved, output⟩

theorem run_packets_read_input {Context : Type} (inputs : Context → Atom) (program : SpaceSemantics.Program)
    (fuel : Nat) (source : ScopedCursor Context)
    (validScopes : EagerDFS.ScopesValid source.2.scopes) (valid : Stack program inputs source.2.scopes) :
    ∀ packet ∈ ((ScopedQuerySource.ownedMachine .eagerValue program).run fuel source).1,
      PacketReadsInput inputs packet := by
  induction fuel generalizing source with
  | zero => simp [Machine.run]
  | succ fuel ih =>
      have scopeSafe := ScopedReturnOwned.owned_step_scope_validity program source validScopes
      have returnSafe := DestinationDataReturnOwned.owned_step_preserves inputs program source validScopes valid
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
      | fail events => exact (ScopedReturnPublication.owned_has_no_failure_packets program source validScopes events step).elim

def CursorGood {Context : Type} (program : SpaceSemantics.Program) (inputs : Context → Atom)
    (source : ScopedCursor Context) : Prop :=
  EagerDFS.ScopesValid source.2.scopes ∧ Stack program inputs source.2.scopes

theorem run_retains_obligation {Context : Type} (inputs : Context → Atom) (program : SpaceSemantics.Program)
    (fuel : Nat) (source : ScopedCursor Context) (valid : CursorGood program inputs source) :
    match ((ScopedQuerySource.ownedMachine .eagerValue program).run fuel source).2 with
    | .finished final | .exhausted final | .suspended _ final | .stuck final => CursorGood program inputs final
    | .faulted => False := by
  induction fuel generalizing source with
  | zero => exact valid
  | succ fuel ih =>
      have scopeSafe := ScopedReturnOwned.owned_step_scope_validity program source valid.1
      have returnSafe := DestinationDataReturnOwned.owned_step_preserves inputs program source valid.1 valid.2
      cases step : ScopedQuerySource.ownedStep .eagerValue program source with
      | silent next =>
          rw [step] at scopeSafe returnSafe
          simpa only [Machine.run, ScopedQuerySource.ownedMachine, step] using
            ih next ⟨scopeSafe, returnSafe next (by simp [RefinementTransport.actionStates])⟩
      | publish events next =>
          rw [step] at scopeSafe returnSafe
          simpa only [Machine.run, ScopedQuerySource.ownedMachine, step] using
            ih next ⟨scopeSafe, returnSafe next (by simp [RefinementTransport.actionStates])⟩
      | finish final =>
          rw [step] at scopeSafe returnSafe
          simp only [Machine.run, ScopedQuerySource.ownedMachine, step]
          exact ⟨scopeSafe, returnSafe final (by simp [RefinementTransport.actionStates])⟩
      | call request retained =>
          rw [step] at scopeSafe returnSafe
          simp only [Machine.run, ScopedQuerySource.ownedMachine, step]
          exact ⟨scopeSafe, returnSafe retained (by simp [RefinementTransport.actionStates])⟩
      | fail events => exact (ScopedReturnPublication.owned_has_no_failure_packets program source valid.1 events step).elim

/-- Every actually published occurrence reads the matched input in that
occurrence's own record, for every finite budget. -/
theorem checked_clause_body_run {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (context : Context) (origins : List Nat)
    (control : Control) (head : String) (arguments : List Atom) (destination : Atom)
    (occurrence : Nat) (equation : SpaceSemantics.Equation) (next : Control)
    (index : Nat) (argument recipe : Atom) (inspectionFuel fuel : Nat)
    (selected : ClauseChoice.attempt control head arguments destination [] occurrence equation = some next)
    (actual : arguments[index]? = some argument) (formal : equation.arguments[index]? = some recipe)
    (data : DestinationDataRecipe.Recipe program recipe) (target : control.destination = destination)
    (checked : ScopedReturnSyntax.checksSurfaceReturn recipe inspectionFuel equation.body = true) :
    ∀ packet ∈ ((ScopedQuerySource.ownedMachine .eagerValue program).run fuel
      (allocator, ⟨world, [⟨[(next, context, origins ++ [occurrence])], [], none⟩]⟩)).1,
      ∃ environment, resolve packet.bindings = some environment ∧ packet.value = read environment argument := by
  have entered := DestinationDataReturnEntry.selected_return_entry program control head arguments destination []
    occurrence equation next index argument recipe inspectionFuel selected actual formal data checked target
  have allPackets := run_packets_read_input (fun _ : Context => argument) program fuel
    (allocator, ⟨world, [⟨[(next, context, origins ++ [occurrence])], [], none⟩]⟩)
    (.root _ _) (.root _ (by intro work member; cases List.mem_singleton.mp member; exact entered))
  intro packet present
  obtain ⟨_context, environment, resolved, observed⟩ := allPackets packet present
  exact ⟨environment, resolved, observed⟩

/-- The list equation preserves every published occurrence and its order;
it does not replace the actual source packet count by a guessed count. -/
theorem checked_ground_clause_body_run {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (context : Context) (origins : List Nat)
    (control : Control) (head : String) (arguments : List Atom) (destination : Atom)
    (occurrence : Nat) (equation : SpaceSemantics.Equation) (next : Control)
    (index : Nat) (argument recipe : Atom) (inspectionFuel fuel : Nat)
    (selected : ClauseChoice.attempt control head arguments destination [] occurrence equation = some next)
    (actual : arguments[index]? = some argument) (formal : equation.arguments[index]? = some recipe)
    (data : DestinationDataRecipe.Recipe program recipe) (target : control.destination = destination)
    (checked : ScopedReturnSyntax.checksSurfaceReturn recipe inspectionFuel equation.body = true)
    (ground : (encode argument).isGround) :
    let packets := ((ScopedQuerySource.ownedMachine .eagerValue program).run fuel
      (allocator, ⟨world, [⟨[(next, context, origins ++ [occurrence])], [], none⟩]⟩)).1
    packets.map CollectedAnswer.value = List.replicate packets.length argument := by
  dsimp only
  apply List.map_eq_replicate_iff.mpr
  intro packet present
  obtain ⟨environment, _resolved, observed⟩ := checked_clause_body_run program allocator world context origins
    control head arguments destination occurrence equation next index argument recipe inspectionFuel fuel
    selected actual formal data target checked packet present
  exact observed.trans (ProtectedSlots.read_ground environment argument ground)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnRun
