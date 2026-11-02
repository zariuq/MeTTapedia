import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutationCoverage
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutationControls

/-!
# Actual adjacent swaps after an existing family-changing source prefix

The existing first firing leaves infinitely many unused scoped declarations.
Those names need not be covered globally. The next two producers nevertheless
swap as actual paths, preserving the full inventory and all term-formation
observations under the constructed declaration isomorphism.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutationCoverageControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualExecutionCommutation ContextualExecutionCommutationNames
open ContextualSelectionViews.Controls (base locals privateVariable)
open ContextualGuardedExecutionControls (initial)
open ContextualExecutionCommutationControls (first second separate_outputs)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)
local instance : Quiver (Endpoint locals Nat [] ()) := ContextualExecution.graph locals Nat

def third : Producer initial where
  made := [101]
  distinct := by decide
  fresh := by decide
  value _ := privateVariable
  covered := by intro _ _; change (∅ : Finset Nat) ⊆ initial.occupied; exact Finset.empty_subset _

def middle := first.target rfl
def secondAfter : Producer middle := first.after second rfl separate_outputs
def thirdAfter : Producer middle := first.after third rfl (by decide)
theorem later_separate : Disjoint thirdAfter.made.toFinset secondAfter.made.toFinset := by decide

def left := secondAfter.twoTarget thirdAfter (first.target_empty rfl) later_separate
def right := thirdAfter.twoTarget secondAfter (first.target_empty rfl) later_separate.symm
def leftPath : Quiver.Path initial left := (Quiver.Hom.toPath (first.firing rfl)).comp
  (secondAfter.twoPath thirdAfter (first.target_empty rfl) later_separate)
def rightPath : Quiver.Path initial right := (Quiver.Hom.toPath (first.firing rfl)).comp
  (thirdAfter.twoPath secondAfter (first.target_empty rfl) later_separate.symm)

def unused : middle.Names := .inl (.inl (Mettapedia.Logic.LP.ScopedVar.at 1000 0))

theorem prior_actual_endpoint_is_covered_but_not_every_unused_name_is :
    ContextualWorldScopeLedger.CoveredWorld locals middle.declarations middle.scopes middle.occupied middle.inventory ∧
      ¬ (∀ name, middle.scopes name ⊆ middle.occupied) := by
  refine ⟨middle.covered, ?_⟩
  intro all
  have forbidden := all unused (by decide : 1000 ∈ middle.scopes unused)
  exact (by decide +kernel : 1000 ∉ middle.occupied) forbidden

def correspondence : EndpointCoverageRenaming left right :=
  producerCoverageRenaming secondAfter thirdAfter (first.target_empty rfl) later_separate

theorem source_prefix_then_both_actual_swapped_suffixes :
    Nonempty (Quiver.Path initial left) ∧ Nonempty (Quiver.Path initial right) ∧
      Nonempty (EndpointCoverageRenaming left right) ∧
      selections leftPath = [⟨[], [], [99]⟩, ⟨[], [], [100]⟩, ⟨[], [], [101]⟩] ∧
      selections rightPath = [⟨[], [], [99]⟩, ⟨[], [], [101]⟩, ⟨[], [], [100]⟩] :=
  ⟨⟨leftPath⟩, ⟨rightPath⟩, ⟨correspondence⟩, rfl, rfl⟩

theorem every_later_term_has_the_same_formation_test {context : Ctx base} {result : base.Srt}
    (term : Term (signature base left.declarations) context result) :
    ContextualScopeSupport.Covered right.scopes right.occupied
        (instantiate (reindex correspondence.names correspondence.declarations) term) ↔
      ContextualScopeSupport.Covered left.scopes left.occupied term :=
  correspondence.term_formation_iff term

theorem the_previous_firings_captures_remain_fixed (name : middle.Names) :
    correspondence.names
      (namesAlong (secondAfter.twoPath thirdAfter (first.target_empty rfl) later_separate) name) =
        namesAlong (thirdAfter.twoPath secondAfter (first.target_empty rfl) later_separate.symm) name :=
  actual_captures_preserved_without_unused_scope_bound _ _ _ _ name

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutationCoverageControls
