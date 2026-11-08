import Mettapedia.Languages.MeTTa.PeTTa.DestinationProtectedSlots

/-! Actual scoped refusal with a distinct saved branch and reached effects. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open ProtectedSlots.Controls (slot seven eight seven_fixed)

def program : SpaceSemantics.Program := {equations := [], declarations := []}
def refusing : Control :=
  {bindings := [(slot, seven)], goals := [.equate slot eight], destination := slot}
def sibling : Control :=
  {bindings := [(slot, eight)], goals := [], destination := slot}

def pending : List (CollectionWork Unit) := [(sibling, (), [1])]
def scope : CollectionScope Unit := ⟨(refusing, (), [0]) :: pending, [], none⟩

theorem refused_branch_keeps_exact_sibling_and_world (allocator : Allocator) (world : World) :
    scopeStep .eagerValue program (allocator, ⟨world, [scope]⟩) =
      .silent (allocator, ⟨world, [{scope with frontier := pending}]⟩) := by
  apply scope_refused_return .eagerValue program allocator world scope [] refusing () [0] pending
    slot eight [] rfl rfl
  exact ProtectedSlots.conflicting_return_refused seven_fixed
    (by simp [eight, encode, Mettapedia.Logic.LP.Term.isGround]) (by decide)

theorem both_occurrences_have_separate_ground_witnesses :
    ScopesGood (ProtectedSlots.groundSlot (fun _ : Unit => slot)) [scope] := by
  intro selected present
  cases List.mem_singleton.mp present
  refine ⟨?_, ?_, ?_⟩
  · intro work member
    simp only [scope, pending, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ProtectedSlots.Controls.same_context_can_retain_distinct_ground_occurrences.1
    · exact ProtectedSlots.Controls.same_context_can_retain_distinct_ground_occurrences.2.1
  · intro answer member
    cases member
  · intro caller present
    cases present

theorem actual_refusal_preserves_the_other_ground_value (allocator : Allocator) (world : World) :
    ActionGood (ProtectedSlots.groundSlot (fun _ : Unit => slot))
      (scopeStep .eagerValue program (allocator, ⟨world, [scope]⟩)) :=
  actual_scope_preserves .eagerValue program _ _ (.root _ _) both_occurrences_have_separate_ground_witnesses

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.Controls
