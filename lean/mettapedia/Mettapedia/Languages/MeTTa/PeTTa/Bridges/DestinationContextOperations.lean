import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationContextCollections

/-! # Actual source operations retain context transport -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationContextMap

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination

variable {A B : Type}

theorem query_work (map : A → B) (control : Control) (context : A) (origins : List Nat)
    (pattern template destination : Atom) (older : List Goal) (rows : List Atom) :
    queryWork control (map context) origins pattern template destination older rows =
      (queryWork control context origins pattern template destination older rows).map (work map) := by
  simp [queryWork, List.map_map, work]

theorem scoped_query (map : A → B) (source : ScopedCursor A) (current : CollectionScope A)
    (parents : List (CollectionScope A)) (control : Control) (context : A)
    (origins : List Nat) (pending : List (CollectionWork A))
    (location pattern template destination : Atom) (older : List Goal) :
    scopedQuery (state map source) (scope map current) (parents.map (scope map)) control (map context)
      origins (pending.map (work map)) location pattern template destination older =
      action map (scopedQuery source current parents control context origins pending
        location pattern template destination older) := by
  simp only [scopedQuery, state, configuration_world, configuration_support]
  repeat' first
    | rfl
    | (split <;> try simp_all only [action, state, configuration, scope, query_work, List.map_cons, List.map_append])

theorem scoped_invocation (map : A → B) (program : SpaceSemantics.Program)
    (source : ScopedCursor A) (current : CollectionScope A) (parents : List (CollectionScope A))
    (control : Control) (context : A) (origins : List Nat) (pending : List (CollectionWork A))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal) :
    scopedInvocation program (state map source) (scope map current) (parents.map (scope map)) control
      (map context) origins (pending.map (work map)) head arguments destination older =
      action map (scopedInvocation program source current parents control context origins pending
        head arguments destination older) := by
  by_cases parsing : head = "parse"
  · subst head
    cases arguments with
    | nil => rfl
    | cons text rest =>
        cases rest with
        | cons second tail => rfl
        | nil =>
            simp only [scopedInvocation, if_true, state, configuration_world, configuration_support]
            cases parsed : EagerDFS.Collection.SyntaxLoading.loadParsed? source.1 (collectionSupport source.2) text with
            | error reason => rfl
            | ok result =>
                cases result with
                | none => rfl
                | some result =>
                    rcases result with ⟨allocator, token, value⟩
                    simp [action, state, configuration, scope, primitive_work]
  · by_cases known : StdLib.known head = true
    · simp only [scopedInvocation, if_neg parsing, known, if_true, state, configuration_world]
      cases applied : StdLib.apply source.2.world.state head arguments with
      | error reason => rfl
      | ok result =>
          rcases result with ⟨next, values⟩
          simp [action, state, configuration, scope, primitive_work]
    · have entry := equation_entry map program source.2
      simp only [scopedInvocation, if_neg parsing, known, state, equation_entry]
      cases entered : enterEquations? program source.2 <;> rfl

theorem install_child (map : A → B) (program : SpaceSemantics.Program)
    (source : ScopedCursor A) (current : CollectionScope A) (parents : List (CollectionScope A))
    (origins : List Nat) (pending : List (CollectionWork A))
    (child : Transition (Cursor A) Empty (Result × Cursor A) Boundary) :
    installChild program (state map source) (scope map current) (parents.map (scope map))
      origins (pending.map (work map)) (localAction map child) =
      action map (installChild program source current parents origins pending child) := by
  cases child with
  | silent reached => rfl
  | publish events reached => rfl
  | finish final =>
      rcases final with ⟨result, reached⟩
      cases result with
      | noValue bindings => rfl
      | value value bindings =>
          simp only [localAction, installChild, cursor]
          cases saved : current.caller <;> simp [scope, saved, action, state, configuration, EagerDFS.Scope.record]
  | fail events => rfl
  | call request reached =>
      cases request with
      | openCommit =>
          simp only [localAction, installChild, cursor]
          repeat' first
            | rfl
            | (split <;> try simp_all only [action, state, configuration, scope, List.map_cons, work, List.length_map])
      | commit retained =>
          simp only [localAction, installChild, cursor]
          repeat' first
            | rfl
            | (split <;> try simp_all only [action, state, configuration, scope, List.map_cons, work,
                List.length_map, List.map_drop])
      | invoke head arguments destination =>
          cases goals : reached.control.goals with
          | nil => simp [localAction, installChild, cursor, goals, action]
          | cons goal older =>
              cases goal <;> simp only [localAction, installChild, cursor, goals]
              all_goals first
                | rfl
                | exact scoped_invocation map program source current parents reached.control reached.context origins pending
                    head arguments destination older
      | query location pattern template destination =>
          cases goals : reached.control.goals with
          | nil => simp [localAction, installChild, cursor, goals, action]
          | cons goal older =>
              cases goal <;> simp only [localAction, installChild, cursor, goals]
              all_goals first
                | rfl
                | exact scoped_query map source current parents reached.control reached.context origins pending
                    location pattern template destination older
      | invalidEnvironment | invalidDelimiter callerDepth available => rfl

theorem scope_step (map : A → B) (policy : Policy) (program : SpaceSemantics.Program)
    (source : ScopedCursor A) :
    scopeStep policy program (state map source) = action map (scopeStep policy program source) := by
  rcases source with ⟨allocator, world, items⟩
  cases items with
  | nil => rfl
  | cons current parents =>
      rcases current with ⟨frontier, answers, saved⟩
      cases frontier with
      | nil =>
          cases saved with
          | none => cases parents <;> rfl
          | some saved =>
              cases parents with
              | nil => rfl
              | cons parent parents =>
                  let original : ScopedCursor A := (allocator, ⟨world, ⟨[], answers, some saved⟩ :: parent :: parents⟩)
                  have finished := allocated_finish map original
                  simp only [scopeStep, state, configuration, scope, List.map_cons, List.map_nil, Option.map_some]
                  simp only [original, state, configuration, scope, List.map_cons, List.map_nil, Option.map_some] at finished
                  rw [finished]
                  by_cases ready : (answers.all fun answer => answer.associated.isEmpty) = true
                  · simp only [ready, if_true]
                    cases finish : finishAllocated? original <;> rfl
                  · simp only [ready]
                    rfl
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          let current : CollectionScope A := ⟨(control, context, origins) :: pending, answers, saved⟩
          let original : ScopedCursor A := (allocator, ⟨world, current :: parents⟩)
          have collapsed := collapse_entry map original.2
          have superposed := superpose_entry map original.2
          have localStepMap := local_step map policy program (⟨world, control, context⟩ : Cursor A)
          simp only [original, current, configuration, scope, work, List.map_cons] at collapsed superposed
          simp only [cursor] at localStepMap
          simp only [scopeStep, state, configuration, scope, List.map_cons, work]
          rw [collapsed]
          cases collapse : enterCollapse? original.2 with
          | some next => rfl
          | none =>
              simp only [Option.map_none]
              rw [superposed]
              cases superpose : enterSuperpose? original.2 with
              | some next => rfl
              | none =>
                  simp only [Option.map_none]
                  cases childStep : (EagerDFS.Destination.machine policy program).step
                      (⟨world, control, context⟩ : Cursor A) with
                  | none =>
                      rw [childStep] at localStepMap
                      simp only [Option.map_none] at localStepMap
                      rw [localStepMap]
                      repeat' first
                        | rfl
                        | (split <;> try simp_all only [])
                  | some child =>
                      rw [childStep] at localStepMap
                      simp only [Option.map_some] at localStepMap
                      rw [localStepMap]
                      repeat' first
                        | rfl
                        | exact install_child map program original current parents origins pending child
                        | (split <;> try simp_all only [])

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationContextMap
