import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessInterference

/-!
# Actual reordered producers need fresh scope transport and disjoint outputs

The two outputs contain private locals; the second also mentions a shared
caller capture. Both original firing paths exist. Their raw private names
differ, while the explicit endpoint renaming identifies their inventories.
A repeated output identity is refused by the original firing admission.
Equation-only interference outside this profile remains visible in the
imported completed-firing control.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutationControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualExecutionCommutation ContextualExecutionCommutationNames
open ContextualSelectionViews.Controls (base locals captures raw privateVariable pair)
open ContextualGuardedExecutionControls (initial)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)
local instance : Quiver (Endpoint locals Nat [] ()) := ContextualExecution.graph locals Nat

def first : Producer initial where
  made := [99]
  distinct := by decide
  fresh := by decide
  value _ := privateVariable
  covered := by intro _ _; change (∅ : Finset Nat) ⊆ initial.occupied; exact Finset.empty_subset _

def second : Producer initial where
  made := [100]
  distinct := by decide
  fresh := by decide
  value _ := pair privateVariable (generator raw (.inr 0))
  covered := by intro _ _; change (∅ : Finset Nat) ⊆ initial.occupied; exact Finset.empty_subset _

theorem separate_outputs : Disjoint second.made.toFinset first.made.toFinset := by decide
theorem initial_scope_bound (name : Nat) : initial.scopes name ⊆ initial.occupied := Finset.empty_subset _

def forwardTarget := first.twoTarget second rfl separate_outputs
def reverseTarget := second.twoTarget first rfl separate_outputs.symm
def forwardPath : Quiver.Path initial forwardTarget := first.twoPath second rfl separate_outputs
def reversePath : Quiver.Path initial reverseTarget := second.twoPath first rfl separate_outputs.symm
def endpointMap : EndpointRenaming forwardTarget reverseTarget :=
  producerEndpointRenaming first second rfl separate_outputs initial_scope_bound

theorem both_actual_orders_and_their_complete_endpoint_correspondence :
    Nonempty (Quiver.Path initial forwardTarget) ∧ Nonempty (Quiver.Path initial reverseTarget) ∧
      Nonempty (EndpointRenaming forwardTarget reverseTarget) ∧
      selections forwardPath = [⟨[], [], [99]⟩, ⟨[], [], [100]⟩] ∧
      selections reversePath = [⟨[], [], [100]⟩, ⟨[], [], [99]⟩] ∧
      forwardTarget.inventory.configuration.present = {7, 99, 100} ∧
      reverseTarget.inventory.configuration.present = {7, 99, 100} := by
  exact ⟨⟨forwardPath⟩, ⟨reversePath⟩, ⟨endpointMap⟩, rfl, rfl, by decide +kernel, by decide +kernel⟩

theorem actual_private_blocks_are_different_and_are_exchanged :
    firstScope initial.occupied = 8 ∧ secondScope initial.occupied = 10 ∧
      endpointMap.names (earlier (V := Nat) (Mettapedia.Logic.LP.ScopedVar.at 8 0)) =
        later (V := Nat) (Mettapedia.Logic.LP.ScopedVar.at 10 0) ∧
      endpointMap.names (earlier (V := Nat) (Mettapedia.Logic.LP.ScopedVar.at 8 0)) ≠
        earlier (V := Nat) (Mettapedia.Logic.LP.ScopedVar.at 8 0) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, ?_⟩
  · change later (V := Nat) (scopeMap (Equiv.swap 8 10) (Mettapedia.Logic.LP.ScopedVar.at 8 0)) =
      later (V := Nat) (Mettapedia.Logic.LP.ScopedVar.at 10 0)
    rfl
  · exact exchange_is_not_identity (swapScopes initial.occupied) _

theorem caller_capture_is_fixed (name : Nat) :
    endpointMap.names (oldCapture (Local := Nat) name) = oldCapture name := rfl

theorem both_helpers_are_retained_and_fixed (firstHelper : Mettapedia.Logic.LP.ScopedVar Nat ⊕ Nat)
    (lastHelper : Mettapedia.Logic.LP.ScopedVar Nat ⊕ Names Nat Nat) :
    endpointMap.names (.inl (.inr (.inr (.inl firstHelper)))) = .inl (.inr (.inr (.inl firstHelper))) ∧
      endpointMap.names (.inr (.inl lastHelper)) = .inr (.inl lastHelper) := ⟨rfl, rfl⟩

theorem raw_private_outputs_require_scope_transport :
    forwardTarget.inventory.rows 99 ≠ reverseTarget.inventory.rows 99 := by
  intro same
  have formula := (Producer.two_target_rows first second rfl separate_outputs 99).symm.trans
    (same.trans (Producer.two_target_rows second first rfl separate_outputs.symm 99))
  have left : 99 ∈ first.made := by decide
  have right : 99 ∉ second.made := by decide
  simp only [if_pos left, if_neg right] at formula
  have terms := ContextualStoredRows.Row.shared.inj formula
  have supports := congrArg support terms
  change [earlier (V := Nat) (Mettapedia.Logic.LP.ScopedVar.at 8 0)] =
    [later (V := Nat) (Mettapedia.Logic.LP.ScopedVar.at 10 0)] at supports
  cases supports

theorem overlapping_output_identity_cannot_be_the_second_firing
    {target : Endpoint locals Nat [] ()} (edge : Firing locals (first.target rfl) target) :
    edge.selection.made ≠ [99] := by
  intro same
  have fresh := edge.admitted.occurrences.fresh
  change Disjoint edge.selection.made.toFinset (first.target rfl).inventory.configuration.present at fresh
  have made : 99 ∈ edge.selection.made.toFinset := by rw [same]; decide
  exact Finset.disjoint_left.mp fresh made (by decide +kernel)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutationControls
