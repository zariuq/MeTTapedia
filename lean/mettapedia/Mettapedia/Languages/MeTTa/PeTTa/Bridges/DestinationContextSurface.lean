import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationContextOperations

/-! # Context transport through owned query and case entrances -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationContextMap

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination

variable {A B : Type}

theorem syntax_step (map : A → B) (source : ScopedCursor A) :
    ScopedQuerySource.syntaxStep (state map source) =
      (ScopedQuerySource.syntaxStep source).map (action map) := by
  rcases source with ⟨allocator, world, items⟩
  cases items with
  | nil => rfl
  | cons current parents =>
      cases front : current.frontier with
      | nil => simp [ScopedQuerySource.syntaxStep, state, configuration, scope, front]
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          simp only [ScopedQuerySource.syntaxStep, state, configuration, scope, front, List.map_cons, work]
          repeat' first
            | rfl
            | (split <;> try simp_all [action, state, configuration, scope, work])

theorem constrained_call (map : A → B) (source : ScopedCursor A) :
    ScopedQuerySource.constrainedCall (state map source) =
      (ScopedQuerySource.constrainedCall source).map (action map) := by
  rcases source with ⟨allocator, world, items⟩
  cases items with
  | nil => rfl
  | cons current parents =>
      cases front : current.frontier with
      | nil => simp [ScopedQuerySource.constrainedCall, state, configuration, scope, front]
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          cases resolved : resolve control.bindings <;>
            simp only [ScopedQuerySource.constrainedCall, state, configuration, scope, front, List.map_cons, work,
              bind, resolved, Option.bind_none, Option.bind_some]
          all_goals repeat' first
            | rfl
            | (split <;> try simp_all [action, state, configuration, scope, work])

theorem mutation_call (map : A → B) (source : ScopedCursor A) :
    ScopedQuerySource.mutationCall (state map source) =
      (ScopedQuerySource.mutationCall source).map (action map) := by
  rcases source with ⟨allocator, world, items⟩
  cases items with
  | nil => rfl
  | cons current parents =>
      cases front : current.frontier with
      | nil => simp [ScopedQuerySource.mutationCall, state, configuration, scope, front]
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          cases resolved : resolve control.bindings <;>
            simp only [ScopedQuerySource.mutationCall, state, configuration, scope, front, List.map_cons, work,
              bind, resolved, Option.bind_none, Option.bind_some]
          all_goals repeat' first
            | rfl
            | (split <;> try simp_all [action, state, configuration, scope, work])

theorem query_step (map : A → B) (source : ScopedCursor A) :
    ScopedQuerySource.queryStep (state map source) =
      (ScopedQuerySource.queryStep source).map (action map) := by
  rcases source with ⟨allocator, world, items⟩
  cases items with
  | nil => rfl
  | cons current parents =>
      cases front : current.frontier with
      | nil => simp [ScopedQuerySource.queryStep, state, configuration, scope, front]
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          cases resolved : resolve control.bindings <;>
            simp only [ScopedQuerySource.queryStep, state, configuration, scope, front, List.map_cons, work,
              bind, resolved, Option.bind_none, Option.bind_some]
          all_goals repeat' first
            | rfl
            | (split <;> try simp_all [action, state, configuration, scope, ScopedQuerySource.work, work])

theorem ownership_step (map : A → B) (program : SpaceSemantics.Program) (source : ScopedCursor A) :
    ScopedQuerySource.ownershipStep program (state map source) =
      (ScopedQuerySource.ownershipStep program source).map (action map) := by
  rcases source with ⟨allocator, world, items⟩
  cases items with
  | nil => simp [ScopedQuerySource.ownershipStep, state, configuration]
  | cons current parents =>
      cases front : current.frontier with
      | nil => simp [ScopedQuerySource.ownershipStep, state, configuration, scope, front]
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          simp only [ScopedQuerySource.ownershipStep, state, configuration, scope, front, List.map_cons, work]
          repeat' first
            | rfl
            | (split <;> try simp_all [action, state, configuration, scope, work])

theorem unifying_query_step (map : A → B) (source : ScopedCursor A) :
    ScopedQuerySource.unifyingQueryStep (state map source) =
      (ScopedQuerySource.unifyingQueryStep source).map (action map) := by
  rcases source with ⟨allocator, world, items⟩
  cases items with
  | nil => rfl
  | cons current parents =>
      cases front : current.frontier with
      | nil => simp [ScopedQuerySource.unifyingQueryStep, state, configuration, scope, front]
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          simp only [ScopedQuerySource.unifyingQueryStep, state, configuration, scope, front, List.map_cons, work]
          repeat' first
            | rfl
            | (split <;> try simp_all [action, state, configuration, scope, work])

theorem case_entry (map : A → B) (source : ScopedCursor A) :
    ScopedCaseSource.entryStep (state map source) =
      (ScopedCaseSource.entryStep source).map (action map) := by
  rcases source with ⟨allocator, world, items⟩
  cases items with
  | nil => rfl
  | cons current parents =>
      cases front : current.frontier with
      | nil => simp [ScopedCaseSource.entryStep, state, configuration, scope, front]
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          simp only [ScopedCaseSource.entryStep, state, configuration, scope, front, List.map_cons, work]
          repeat' first
            | rfl
            | (split <;> try simp_all [action, state, configuration, scope, work])

theorem case_ready (map : A → B) (admitPattern : Atom → Bool) (source : ScopedCursor A) :
    ScopedCaseSource.readyStep admitPattern (state map source) =
      (ScopedCaseSource.readyStep admitPattern source).map (action map) := by
  rcases source with ⟨allocator, world, items⟩
  cases items with
  | nil => rfl
  | cons current parents =>
      cases front : current.frontier with
      | nil => simp [ScopedCaseSource.readyStep, state, configuration, scope, front]
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          cases resolved : resolve control.bindings <;>
            simp only [ScopedCaseSource.readyStep, state, configuration, scope, front, List.map_cons, work,
              bind, resolved, Option.bind_none, Option.bind_some]
          all_goals repeat' first
            | rfl
            | (split <;> try simp_all [action, state, configuration, scope, work])

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationContextMap
