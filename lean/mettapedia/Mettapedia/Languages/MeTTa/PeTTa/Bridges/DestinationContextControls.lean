import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationContextTransport

/-! # Actual source resumption must transport its saved caller -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationContextMap.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination

def program : SpaceSemantics.Program := {equations := [], declarations := []}
def control : Control := ⟨[], [], .var "result", ∅, 0⟩
def parent : CollectionScope Nat := ⟨[], [], none⟩
def child : CollectionScope Nat := ⟨[], [], some (control, .var "result", 7, [3])⟩
def source : ScopedCursor Nat :=
  (Allocator.empty 8 64, ⟨{state := Effects.loaded program, output := [.symbol "already"]}, [child, parent]⟩)

/-- This mutation transports runnable work but leaves the saved caller old. -/
def forgottenCaller : ScopedCursor Nat :=
  (source.1, {source.2 with scopes := source.2.scopes.map fun original =>
    {original with frontier := original.frontier.map (work Nat.succ)}})

def resumedContext : ScopedQuerySource.Action Nat → Option Nat
  | .silent next => do
      let current ← next.2.scopes.head?
      let item ← current.frontier.head?
      pure item.2.1
  | _ => none

theorem actual_collection_resumes_the_transported_caller :
    resumedContext (ScopedQuerySource.ownedStep .eagerValue program (state Nat.succ source)) = some 8 := by cbv

theorem frontier_only_mutation_resumes_the_wrong_caller :
    resumedContext (ScopedQuerySource.ownedStep .eagerValue program forgottenCaller) = some 7 := by cbv

theorem every_budget_preserves_the_complete_source_packets (fuel : Nat) :
    ((ScopedQuerySource.ownedMachine .eagerValue program).run fuel (state Nat.succ source)).1 =
      ((ScopedQuerySource.ownedMachine .eagerValue program).run fuel source).1 :=
  owned_run_packets Nat.succ .eagerValue program fuel source

theorem zero_budget_retains_the_transported_world :
    ((ScopedQuerySource.ownedMachine .eagerValue program).run 0 (state Nat.succ source)).2 =
      .exhausted (state Nat.succ source) ∧ (state Nat.succ source).2.world.output = [.symbol "already"] := by cbv

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationContextMap.Controls
