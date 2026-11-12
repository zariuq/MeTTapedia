import Mettapedia.Languages.MeTTa.ContextualTransform.ConcreteStorePrograms
import Mettapedia.Data.List.RetainedOccurrenceAllocation

/-!
# Existing store programs with a retained-identity allocation profile

The same ordered tcalc interpreter uses the stronger concrete allocator.
Value observations and actual event realization remain the existing source
contracts. Once retired held IDs are absent from a store, every later command
keeps them absent. Retention is a caller-supplied finite live inventory; release
can choose the original allocator again. Native inventory and pointer lifetime
correspondence are not supplied by this interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.RetainedStorePrograms

open Mettapedia.Machines
open Mettapedia.Data.List
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Interface
open ConcreteStorePrograms (Id label knowledge consistent)
open AdaptiveStorePrograms
open RetainedOccurrenceAllocation

def allocation (retained : List Id) : Allocation label where
  make live values := reserve live retained values
  values live values := reserve_values live retained values
  distinct live values := reserve_nodup live retained values
  fresh live values := fresh live retained values

def backend (retained : List Id) := target label knowledge consistent (allocation retained)

theorem value_observations_exact (retained : List Id) {Answer : Type}
    (program : ReadOnlyQuery.Program Command Reply Answer) (state : State Id) :
    QueryState.run source program (decode label state) =
      OperatorChoice.ObserverContracts.eraseObservation (decode label)
        (QueryState.run (backend retained) program state) :=
  adaptive_exact label knowledge consistent (allocation retained) program state

theorem step_does_not_revive (retained : List Id) (state : State Id)
    (absent : Avoids retained state.val) (command : Command) :
    Avoids retained (backend retained state command).2.val := by
  change Avoids retained (OrderedStore.publish state.val
    (lower label (allocation retained) state command).selection)
  cases command with
  | append values =>
      simpa [lower, StoreOperations.appendRequest, OrderedStore.publish, OrderedStore.survivors,
        allocation] using avoids_append retained state.val (reserve state.val retained values)
          absent (reserve_avoids state.val retained values)
  | remove select =>
      simp only [lower, StoreOperations.removeRequest, OrderedStore.publish, List.append_nil]
      apply avoids_subset retained _ state.val absent
      intro occurrence member
      exact (List.mem_filter.mp member).1
  | query select =>
      simpa [lower, StoreOperations.readRequest, OrderedStore.publish, OrderedStore.survivors] using absent

theorem program_does_not_revive (retained : List Id) {Answer : Type}
    (program : ReadOnlyQuery.Program Command Reply Answer) (state : State Id)
    (absent : Avoids retained state.val) :
    Avoids retained (QueryState.run (backend retained) program state).state.val :=
  QueryState.state_invariant (backend retained) (fun state => Avoids retained state.val)
    (step_does_not_revive retained) program state absent

/-- Distinct identity/value pairs alone would not certify unique numeric
identities. The concrete allocation maintains the stronger representation law. -/
theorem step_distinct_identities (retained : List Id) (state : State Id)
    (distinct : (state.val.map (fun row => row.identity)).Nodup) (command : Command) :
    (((backend retained state command).2.val).map (fun row => row.identity)).Nodup := by
  change ((OrderedStore.publish state.val
    (lower label (allocation retained) state command).selection).map (fun row => row.identity)).Nodup
  cases command with
  | append values =>
      simp only [lower, StoreOperations.appendRequest, OrderedStore.publish, OrderedStore.survivors]
      simp only [List.not_mem_nil, not_false_eq_true, decide_true, List.filter_true, List.map_append]
      apply List.nodup_append.mpr
      refine ⟨distinct, reserve_distinct_identities state.val retained values, ?_⟩
      intro old oldMember made madeMember same
      obtain ⟨oldRow, oldPresent, rfl⟩ := List.mem_map.mp oldMember
      obtain ⟨newRow, newPresent, rfl⟩ := List.mem_map.mp madeMember
      exact fresh_live state.val retained values newRow oldRow newPresent oldPresent same.symm
  | remove select =>
      simp only [lower, StoreOperations.removeRequest, OrderedStore.publish, List.append_nil]
      exact (List.Sublist.map _ List.filter_sublist).nodup distinct
  | query select =>
      simpa [lower, StoreOperations.readRequest, OrderedStore.publish, OrderedStore.survivors] using distinct

theorem program_distinct_identities (retained : List Id) {Answer : Type}
    (program : ReadOnlyQuery.Program Command Reply Answer) (state : State Id)
    (distinct : (state.val.map (fun row => row.identity)).Nodup) :
    ((QueryState.run (backend retained) program state).state.val.map (fun row => row.identity)).Nodup :=
  QueryState.state_invariant (backend retained) (fun state => (state.val.map (fun row => row.identity)).Nodup)
    (step_distinct_identities retained) program state distinct

theorem empty_start_constructs_distinct_identities (retained : List Id) {Answer : Type}
    (program : ReadOnlyQuery.Program Command Reply Answer) :
    ((QueryState.run (backend retained) program ⟨[], List.nodup_nil⟩).state.val.map
      (fun row => row.identity)).Nodup :=
  program_distinct_identities retained program _ List.nodup_nil

theorem actual_run_keeps_knowledge (retained : List Id) {Answer : Type}
    (program : ReadOnlyQuery.Program Command Reply Answer) (state : State Id) :
    (realization label knowledge consistent (allocation retained) program state).last.1 = knowledge := by
  rw [realization_last]

namespace Controls

def held : List Id := [⟨0, .symbol "a"⟩]
def empty : State Id := ⟨[], List.nodup_nil⟩
def cycle : ReadOnlyQuery.Program Command Reply (List Reply) :=
  .read (.append [.symbol "a"]) fun added =>
    .read (.remove (fun _ => true)) fun removed =>
      .read (.append [.symbol "a"]) fun addedAgain =>
        .read (.query (fun _ => true)) fun observed =>
          .pure [added, removed, addedAgain, observed]

theorem retired_ids_stay_absent_through_store_updates :
    (QueryState.run (backend held) cycle empty).state.val = [⟨1, .symbol "a"⟩] ∧
      (QueryState.run (backend held) cycle empty).answer =
        [.count 1, .changed true, .count 1, .rows [.symbol "a"]] := by decide

theorem releasing_retention_allows_reuse_without_changing_values :
    (QueryState.run (backend []) cycle empty).state.val = held ∧
      (QueryState.run (backend []) cycle empty).answer =
        (QueryState.run (backend held) cycle empty).answer := by decide

theorem pair_distinctness_does_not_prove_identity_distinctness :
    ([⟨0, .symbol "a"⟩, ⟨0, .symbol "b"⟩] : List Id).Nodup ∧
      ¬ (([⟨0, .symbol "a"⟩, ⟨0, .symbol "b"⟩] : List Id).map (fun row => row.identity)).Nodup := by decide

end Controls

end Mettapedia.Languages.MeTTa.ContextualTransform.RetainedStorePrograms
