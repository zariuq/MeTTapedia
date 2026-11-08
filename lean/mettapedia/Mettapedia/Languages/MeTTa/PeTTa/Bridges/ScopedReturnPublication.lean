import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnOwned

/-!
# Published source packets retain their input alias

Publication is reflected to its actual root frontier occurrence and actual
most-general solver result. Inner collection rows are not publications of
the owning body. Context labels may be equal; each packet keeps its own
record and source origin.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnPublication

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS.Destination
open ScopedReturnScopes

theorem source_publication_is_root {Context : Type} {policy : Policy} {program : SpaceSemantics.Program}
    {before after : ScopedCursor Context} {action : Source.ScopeAction Allocator Context}
    (source : Source.ScopedStep Source.FreshOperations.owned policy program before action)
    (valid : EagerDFS.ScopesValid before.2.scopes) (events : List CollectedAnswer)
    (published : action = .publish events after) : ∃ scope, before.2.scopes = [scope] := by
  cases source with
  | active allocator world scope parents control context origins pending action frontier active =>
      cases active with
      | answered value bindings reached localStep =>
          cases valid with
          | root => exact ⟨_, rfl⟩
          | nested => simp at published
      | invocation head arguments destination older environment action atCall resolved notPrint served =>
          cases served <;> cases published
      | opening | committing | invalidCommit | next | refused | boundary | queried | queryFault | collapsed |
          choice | empty => cases published
  | finished | collected | associated | allocation => cases published

theorem source_has_no_failure_packets {Context : Type} {policy : Policy} {program : SpaceSemantics.Program}
    {before : ScopedCursor Context} {action : Source.ScopeAction Allocator Context}
    (source : Source.ScopedStep Source.FreshOperations.owned policy program before action)
    (events : List CollectedAnswer) : action ≠ .fail events := by
  intro failed
  cases source with
  | active allocator world scope parents control context origins pending action frontier active =>
      cases active with
      | answered value bindings reached localStep => split at failed <;> cases failed
      | invocation head arguments destination older environment action atCall resolved notPrint served =>
          cases served <;> cases failed
      | opening | committing | invalidCommit | next | refused | boundary | queried | queryFault | collapsed |
          choice | empty => cases failed
  | finished | collected | associated | allocation => cases failed

theorem local_has_no_failure_packets {Context : Type} {source : ScopedCursor Context}
    {action : ScopedQuerySource.Action Context} (localAction : ScopedQueryBinding.Local source action)
    (events : List CollectedAnswer) : action ≠ .fail events := by cases localAction <;> simp

theorem base_has_no_failure_packets {Context : Type} (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) (valid : EagerDFS.ScopesValid source.2.scopes)
    (events : List CollectedAnswer) : ScopedQuerySource.step .eagerValue program source ≠ .fail events := by
  intro failed
  unfold ScopedQuerySource.step at failed
  repeat' first
    | exact local_has_no_failure_packets (ScopedQueryBinding.syntax_local source _ (by assumption)) events failed
    | exact local_has_no_failure_packets (ScopedQueryBinding.constrained_local source _ (by assumption)) events failed
    | exact local_has_no_failure_packets (ScopedQueryBinding.mutation_local source _ (by assumption)) events failed
    | exact local_has_no_failure_packets (ScopedQueryBinding.query_local source _ (by assumption)) events failed
    | exact source_has_no_failure_packets
        ((Source.scoped_step_iff_source .eagerValue program source valid _).mp rfl) events failed
    | split at failed

theorem owned_has_no_failure_packets {Context : Type} (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) (valid : EagerDFS.ScopesValid source.2.scopes)
    (events : List CollectedAnswer) : ScopedQuerySource.ownedStep .eagerValue program source ≠ .fail events := by
  intro failed
  unfold ScopedQuerySource.ownedStep at failed
  split at failed
  · exact local_has_no_failure_packets (ScopedQueryBinding.case_entry_local source _ (by assumption)) events failed
  · split at failed
    · exact local_has_no_failure_packets (ScopedQueryBinding.case_ready_local _ source _ (by assumption)) events failed
    · split at failed
      · exact local_has_no_failure_packets (ScopedQueryBinding.ownership_local program source _ (by assumption)) events failed
      · dsimp only at failed
        split at failed
        · cases extended : ScopedQuerySource.unifyingQueryStep source with
          | none =>
              simp only [extended, Option.getD_none] at failed
              exact base_has_no_failure_packets program source valid events failed
          | some action =>
              simp only [extended, Option.getD_some] at failed
              exact local_has_no_failure_packets (ScopedQueryBinding.unifying_local source action extended) events failed
        · exact base_has_no_failure_packets program source valid events failed

/-- The record and context below come from the actual publishing source
occurrence. The equality is at its computed solver, not an arbitrary model. -/
theorem published_input_witness {Context : Type} (inputs : Context → Atom) (program : SpaceSemantics.Program)
    (before after : ScopedCursor Context) (events : List CollectedAnswer)
    (validScopes : EagerDFS.ScopesValid before.2.scopes) (valid : Stack inputs before.2.scopes)
    (published : scopeStep .eagerValue program before = .publish events after) :
    ∃ scope control context pending value bindings origins environment,
      before.2.scopes = [scope] ∧ scope.frontier = (control, context, origins) :: pending ∧
      events = [⟨value, bindings, origins, []⟩] ∧ bindings = control.bindings ∧
      resolve bindings = some environment ∧ value = read environment (inputs context) := by
  have derivation := (Source.scoped_step_iff_source .eagerValue program before validScopes _).mp published
  obtain ⟨root, rootScopes⟩ := source_publication_is_root derivation validScopes events rfl
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
    exact ScopedReturnLocal.terminal_alias_observation (inputs context)
      (⟨before.2.world, control, context⟩ : Cursor Context) holds terminal environment resolved

def PacketReadsInput {Context : Type} (inputs : Context → Atom) (packet : CollectedAnswer) : Prop :=
  ∃ context environment, resolve packet.bindings = some environment ∧
    packet.value = read environment (inputs context)

theorem published_packets_read_input {Context : Type} (inputs : Context → Atom) (program : SpaceSemantics.Program)
    (before after : ScopedCursor Context) (events : List CollectedAnswer)
    (validScopes : EagerDFS.ScopesValid before.2.scopes) (valid : Stack inputs before.2.scopes)
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

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnPublication
