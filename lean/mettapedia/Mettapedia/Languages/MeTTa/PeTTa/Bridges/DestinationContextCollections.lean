import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationContextMap

/-! # Context transport through actual collection and equation entry -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationContextMap

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination

variable {A B : Type}

theorem collection_enter (map : A → B) (world : EagerDFS.World) (original : CollectionScope A)
    (pending : List (CollectionWork A)) (parents : List (CollectionScope A))
    (child : CollectionWork A) (saved : CollectionCaller A) :
    configuration map (EagerDFS.Scope.enter world original pending parents child saved) =
      EagerDFS.Scope.enter world (scope map original) (pending.map (work map))
        (parents.map (scope map)) (work map child) (caller map saved) := by
  simp [configuration, scope, EagerDFS.Scope.enter]

theorem superpose_work (map : A → B) (control : Control) (context : A) (origins : List Nat)
    (alternatives : List Atom) (destination : Atom) (older : List Goal) :
    superposeWork control (map context) origins alternatives destination older =
      (superposeWork control context origins alternatives destination older).map (work map) := by
  simp [superposeWork, List.map_map, work]

theorem collapse_entry (map : A → B) (original : CollectionConfiguration A) :
    enterCollapse? (configuration map original) = (enterCollapse? original).map (configuration map) := by
  cases items : original.scopes with
  | nil => simp [enterCollapse?, configuration, items]
  | cons current parents =>
      cases front : current.frontier with
      | nil => simp [enterCollapse?, configuration, scope, items, front]
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          have support := configuration_support map original
          simp only [configuration, items, List.map_cons] at support
          simp only [enterCollapse?, configuration, items, List.map_cons, scope, front, work]
          repeat' first
            | rfl
            | (split <;> try simp_all only [configuration, scope, work, caller,
                EagerDFS.Scope.enter, List.map_cons, List.map_nil, Option.map_some])

theorem superpose_entry (map : A → B) (original : CollectionConfiguration A) :
    enterSuperpose? (configuration map original) = (enterSuperpose? original).map (configuration map) := by
  cases items : original.scopes with
  | nil => simp [enterSuperpose?, configuration, items]
  | cons current parents =>
      cases front : current.frontier with
      | nil => simp [enterSuperpose?, configuration, scope, items, front]
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          simp only [enterSuperpose?, configuration, items, List.map_cons, scope, front, work]
          repeat' first
            | rfl
            | (split <;> try simp_all only [configuration, scope, superpose_work,
                List.map_cons, List.map_append, Option.map_some])

theorem equation_entry (map : A → B) (program : SpaceSemantics.Program)
    (original : CollectionConfiguration A) :
    enterEquations? program (configuration map original) =
      (enterEquations? program original).map (configuration map) := by
  cases items : original.scopes with
  | nil => simp [enterEquations?, configuration, items]
  | cons current parents =>
      cases front : current.frontier with
      | nil => simp [enterEquations?, configuration, scope, items, front]
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          have support := configuration_support map original
          simp only [configuration, items, List.map_cons] at support
          simp only [enterEquations?, configuration, items, List.map_cons, scope, front, work]
          repeat' first
            | rfl
            | (split <;> try simp_all only [bind, Option.pure_def, Option.map_bind,
                scope, equation_work, List.map_cons, List.length_map])
          apply congrArg ((resolve control.bindings).bind)
          funext environment
          simp only [work] at support ⊢
          simp only [Function.comp_apply, Option.map_some, configuration, scope,
            List.map_cons, List.map_append, support]

theorem allocated_finish (map : A → B) (source : ScopedCursor A) :
    finishAllocated? (state map source) = (finishAllocated? source).map (state map) := by
  rcases source with ⟨allocator, world, items⟩
  cases items with
  | nil => rfl
  | cons current parents =>
      rcases current with ⟨frontier, answers, saved⟩
      cases frontier with
      | cons item pending => rfl
      | nil =>
          cases saved with
          | none => rfl
          | some saved =>
              cases parents with
              | nil => rfl
              | cons parent parents =>
                  have support := configuration_support map
                    (⟨world, ⟨[], answers, some saved⟩ :: parent :: parents⟩ : CollectionConfiguration A)
                  simp only [configuration, scope, List.map_cons, List.map_nil, Option.map_some] at support
                  simp only [finishAllocated?, state, configuration, scope, List.map_cons, List.map_nil,
                    Option.map_some, support]
                  repeat' first
                    | rfl
                    | (split <;> try simp_all only [bind, Option.pure_def, Option.map_bind, allocatedWork, caller])

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationContextMap
