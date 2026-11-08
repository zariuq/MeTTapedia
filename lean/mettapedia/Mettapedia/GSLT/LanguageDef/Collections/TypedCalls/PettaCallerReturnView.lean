import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnPhases
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnScopes

/-!
# A return-obligation view of typed source scopes

This projection is used only to state an invariant. It retains the actual
binding record and substitutes the suspended outer continuation when typed
prefix calls are active. No simulation or equality of executions is inferred
merely from the existence of this view.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnView

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay PettaCallerReturnFrames

def work {User : Type} (item : Work User) : Work User :=
  (viewControl item.1 item.2.1.calls, item.2)

def caller {User : Type} (saved : CollectionCaller (Context User)) : CollectionCaller (Context User) :=
  (viewControl saved.1 saved.2.2.1.calls, saved.2)

def scope {User : Type} (source : Scope User) : Scope User :=
  {source with frontier := source.frontier.map work, caller := source.caller.map caller}

def state {User : Type} (source : State User) : State User :=
  (source.1, {source.2 with scopes := source.2.scopes.map scope})

def Holds {User : Type} (inputs : User → Atom) (source : State User) : Prop :=
  Bridges.ScopedReturnScopes.Stack (fun context => inputs context.user) (state source).2.scopes

theorem work_iff {User : Type} (inputs : User → Atom) (item : Work User) :
    Bridges.ScopedReturnScopes.WorkReturns (fun context => inputs context.user) (work item) ↔
      PettaCallerReturnPhases.WorkHolds inputs item :=
  (frames_iff_view _ _ _).symm

theorem caller_iff {User : Type} (inputs : User → Atom) (saved : CollectionCaller (Context User)) :
    Bridges.ScopedReturnLocal.AliasHolds (inputs saved.2.2.1.user) (caller saved).1 ↔
      Frames (inputs saved.2.2.1.user) saved.1 saved.2.2.1.calls :=
  (frames_iff_view _ _ _).symm

theorem state_world {User : Type} (source : State User) :
    (state source).1 = source.1 ∧ (state source).2.world = source.2.world := ⟨rfl, rfl⟩

theorem state_depth {User : Type} (source : State User) :
    (state source).2.scopes.length = source.2.scopes.length := by simp [state]

theorem scope_frontier {User : Type} (source : Scope User) (frontier : List (Work User)) :
    scope {source with frontier} = {scope source with frontier := frontier.map work} := rfl

theorem scope_collected {User : Type} (source : Scope User) (collected : List CollectedAnswer) :
    scope {source with collected} = {scope source with collected} := rfl

theorem scope_record {User : Type} (source : Scope User) (pending : List (Work User)) (answer : CollectedAnswer) :
    scope (EagerDFS.Scope.record source pending answer) =
      EagerDFS.Scope.record (scope source) (pending.map work) answer := rfl

theorem valid_scopes {User : Type} (source : State User)
    (valid : EagerDFS.ScopesValid source.2.scopes) : EagerDFS.ScopesValid (state source).2.scopes := by
  change EagerDFS.ScopesValid (source.2.scopes.map scope)
  generalize scopes : source.2.scopes = items at valid ⊢
  clear scopes
  induction valid with
  | root => exact .root _ _
  | nested frontier collected saved valid ih => exact .nested _ _ _ ih

theorem root_work {User : Type} (inputs : User → Atom) (source : State User) (root : Scope User)
    (roots : source.2.scopes = [root]) (held : Holds inputs source) :
    ∀ item ∈ root.frontier, PettaCallerReturnPhases.WorkHolds inputs item := by
  have actual : Bridges.ScopedReturnScopes.Stack (fun context => inputs context.user) [scope root] := by
    simpa only [Holds, state, roots, List.map_cons, List.map_nil] using held
  intro item present
  exact (work_iff inputs item).mp (actual.root_work (work item) (List.mem_map.mpr ⟨item, present, rfl⟩))

theorem install_preserves {User : Type} (inputs : User → Atom) (source : State User)
    (current : Scope User) (parents : List (Scope User)) (control : DControl) (context : Context User)
    (origins : List Nat) (pending generated : List (Work User))
    (held : Holds inputs source) (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (produced : Frames (inputs context.user) control context.calls →
      ∀ item ∈ generated, PettaCallerReturnPhases.WorkHolds inputs item) :
    Holds inputs (install source current parents generated pending) := by
  have prior : Bridges.ScopedReturnScopes.Stack (fun context => inputs context.user)
      (scope current :: parents.map scope) := by
    simpa only [Holds, state, scopes, List.map_cons] using held
  have advanced := prior.replace_active (viewControl control context.calls) context origins (pending.map work)
    (generated.map work) current.collected
    (by simp only [scope, frontier, List.map_cons, work]) (by
      intro captured item member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact (work_iff inputs original).mpr (produced (frames_of_view _ _ _ captured) original present))
  simpa only [Holds, state, install, List.map_cons, scope, List.map_append] using advanced

theorem replace_active {User : Type} (inputs : User → Atom) (source : State User)
    (current : Scope User) (parents : List (Scope User)) (control : DControl) (context : Context User)
    (origins : List Nat) (pending generated : List (Work User)) (collected : List CollectedAnswer)
    (allocator : Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Allocator) (world : EagerDFS.World)
    (held : Holds inputs source) (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (produced : Frames (inputs context.user) control context.calls →
      ∀ item ∈ generated, PettaCallerReturnPhases.WorkHolds inputs item) :
    Holds inputs (allocator, ⟨world, {current with frontier := generated ++ pending, collected} :: parents⟩) := by
  have prior : Bridges.ScopedReturnScopes.Stack (fun context => inputs context.user)
      (scope current :: parents.map scope) := by
    simpa only [Holds, state, scopes, List.map_cons] using held
  have advanced := prior.replace_active (viewControl control context.calls) context origins (pending.map work)
    (generated.map work) collected
    (by simp only [scope, frontier, List.map_cons, work]) (by
      intro captured item member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact (work_iff inputs original).mpr (produced (frames_of_view _ _ _ captured) original present))
  simpa only [Holds, state, List.map_cons, scope, List.map_append] using advanced

theorem replace_root {User : Type} (inputs : User → Atom) (source : State User)
    (current : Scope User) (parents : List (Scope User)) (frontier : List (Work User))
    (collected : List CollectedAnswer)
    (allocator : Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Allocator) (world : EagerDFS.World)
    (held : Holds inputs source) (scopes : source.2.scopes = current :: parents)
    (produced : parents = [] → ∀ item ∈ frontier, PettaCallerReturnPhases.WorkHolds inputs item) :
    Holds inputs (allocator, ⟨world, {current with frontier, collected} :: parents⟩) := by
  have prior : Bridges.ScopedReturnScopes.Stack (fun context => inputs context.user)
      (scope current :: parents.map scope) := by
    simpa only [Holds, state, scopes, List.map_cons] using held
  have advanced := prior.replace_head (frontier.map work) collected (by
    intro root item member
    have noParents : parents = [] := List.map_eq_nil_iff.mp root
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact (work_iff inputs original).mpr (produced noParents original present))
  simpa only [Holds, state, List.map_cons, scope] using advanced

theorem push_scope {User : Type} (inputs : User → Atom) (source : State User)
    (current : Scope User) (parents : List (Scope User)) (child : Scope User) (pending : List (Work User))
    (allocator : Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Allocator) (world : EagerDFS.World)
    (held : Holds inputs source) (scopes : source.2.scopes = current :: parents)
    (retained : parents = [] → ∀ item ∈ pending, PettaCallerReturnPhases.WorkHolds inputs item)
    (saved : parents = [] → ∀ saved, child.caller = some saved →
      Frames (inputs saved.2.2.1.user) saved.1 saved.2.2.1.calls) :
    Holds inputs (allocator, ⟨world, child :: {current with frontier := pending} :: parents⟩) := by
  have prior : Bridges.ScopedReturnScopes.Stack (fun context => inputs context.user)
      (scope current :: parents.map scope) := by
    simpa only [Holds, state, scopes, List.map_cons] using held
  have advanced := prior.push (scope child) (pending.map work) (by
    intro root item member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact (work_iff inputs original).mpr (retained (List.map_eq_nil_iff.mp root) original present)) (by
    intro root viewed atCaller
    obtain ⟨original, present, rfl⟩ := Option.map_eq_some_iff.mp atCaller
    exact (caller_iff inputs original).mpr (saved (List.map_eq_nil_iff.mp root) original present))
  simpa only [Holds, state, List.map_cons, scope] using advanced

theorem resume_scope {User : Type} (inputs : User → Atom) (source : State User)
    (child parent : Scope User) (parents : List (Scope User)) (saved : CollectionCaller (Context User))
    (resumed : Work User)
    (allocator : Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Allocator) (world : EagerDFS.World)
    (held : Holds inputs source) (scopes : source.2.scopes = child :: parent :: parents)
    (atCaller : child.caller = some saved)
    (returned : Frames (inputs saved.2.2.1.user) saved.1 saved.2.2.1.calls →
      PettaCallerReturnPhases.WorkHolds inputs resumed) :
    Holds inputs (allocator, ⟨world, {parent with frontier := resumed :: parent.frontier} :: parents⟩) := by
  have prior : Bridges.ScopedReturnScopes.Stack (fun context => inputs context.user)
      (scope child :: scope parent :: parents.map scope) := by
    simpa only [Holds, state, scopes, List.map_cons] using held
  have advanced := prior.resume (caller saved) (by simp [scope, atCaller]) (work resumed) (by
    intro captured
    exact (work_iff inputs resumed).mpr (returned ((caller_iff inputs saved).mp captured)))
  simpa only [Holds, state, List.map_cons, scope] using advanced

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnView
