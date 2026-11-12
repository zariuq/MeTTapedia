import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceBinding

/-!
# Context-only facts through the existing owned source transitions

The source owner treats contexts opaquely. A fact about the complete context,
independent of logical bindings, is therefore preserved through all its source
handlers. Typed operations still have to justify their actual context updates.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaContextFacts

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay

def predicate {User : Type} (property : Context User → Prop) : RefinementTransport.BindingPredicate (Context User) where
  holds context _ := property context
  closed _ _ _ good _ := good

def Safe {User : Type} (property : Context User → Prop) (source : State User) : Prop :=
  Bridges.ScopedQueryBinding.Safe (predicate property) source

def Keeps {User : Type} (property : Context User → Prop) (reply : Step User) : Prop :=
  ∀ next ∈ PettaOccurrenceBinding.retained reply, Safe property next

theorem silent_keeps {User : Type} {property : Context User → Prop} (source : State User)
    (good : Safe property source) : Keeps property (.silent source) := by
  simpa only [Keeps, PettaOccurrenceBinding.retained, List.mem_singleton, forall_eq] using good

theorem call_keeps {User : Type} {property : Context User → Prop} (source : State User)
    (request : Request) (good : Safe property source) : Keeps property (.call request source) := by
  simpa only [Keeps, PettaOccurrenceBinding.retained, List.mem_singleton, forall_eq] using good

theorem source_keeps {User : Type} (property : Context User → Prop) (policy : Policy)
    (program : SpaceSemantics.Program) (source : State User) (good : Safe property source) :
    Keeps property (liftSource (Bridges.ScopedQuerySource.ownedStep policy program source)) := by
  obtain ⟨valid, held⟩ := Bridges.ScopedQueryBinding.owned_step_safe (predicate property) policy program source good
  generalize actionEq : Bridges.ScopedQuerySource.ownedStep policy program source = reply at valid held ⊢
  cases reply <;> simp_all [Keeps, Safe, Bridges.ScopedQueryBinding.Safe,
    PettaOccurrenceBinding.retained, liftSource, ScopesPreserved,
    RefinementTransport.ActionGood, RefinementTransport.actionStates]

theorem active {User : Type} {property : Context User → Prop} (source : State User)
    (current : Scope User) (parents : List (Scope User)) (control : DControl) (context : Context User)
    (origins : List Nat) (pending : List (Work User)) (good : Safe property source)
    (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending) : property context :=
  (RefinementTransport.focus_good (scopes ▸ good.2) frontier).2.2.1

theorem install_keeps {User : Type} {property : Context User → Prop} (source : State User)
    (current : Scope User) (parents : List (Scope User)) (control : DControl) (context : Context User)
    (origins : List Nat) (pending generated : List (Work User)) (good : Safe property source)
    (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (produced : property context → ∀ item ∈ generated, property item.2.1) :
    Safe property (install source current parents generated pending) := by
  have valid : EagerDFS.ScopesValid (current :: parents) := scopes ▸ good.1
  obtain ⟨currentGood, parentsGood, activeGood, pendingGood⟩ :=
    RefinementTransport.focus_good (scopes ▸ good.2) frontier
  refine ⟨valid.replace_head _ _, RefinementTransport.scopes_cons ?_ parentsGood⟩
  apply currentGood.frontier
  intro item member
  rcases List.mem_append.mp member with fresh | older
  · exact produced activeGood item fresh
  · exact pendingGood item older

theorem root_frontier_safe {User : Type} (property : Context User → Prop) (allocator : Allocator)
    (world : EagerDFS.World) (frontier : List (Work User))
    (held : ∀ item ∈ frontier, property item.2.1) :
    Safe property (allocator, ⟨world, [⟨frontier, [], none⟩]⟩) := by
  refine ⟨.root _ _, ?_⟩
  intro current member
  cases List.mem_singleton.mp member
  refine ⟨held, ?_, ?_⟩
  · intro answer impossible
    cases impossible
  · intro caller impossible
    cases impossible

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaContextFacts
