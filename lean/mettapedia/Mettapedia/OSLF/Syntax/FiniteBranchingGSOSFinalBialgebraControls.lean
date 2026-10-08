import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSFinalBialgebra
import Mettapedia.OSLF.Syntax.FiniteBranchingFinalSemanticsControls

/-!
# A final algebra action with two independently distinguishable futures

The actual choice law acts on independently unfolded delayed coalgebras.
Both arguments initially offer the same action, but only one continuation
offers a later action. The final compatible action retains both complete
future trees, and omitting either distinct continuation fails its readout.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.FinalBialgebra.Controls

open _root_.CategoryTheory Mettapedia.CategoryTheory Mettapedia.TypeTheory
open GSOSControls
open Classical

def leftAt (state : Nat) : FiniteActionTree.Tree Nat PUnit :=
  (FinalSemantics.observe Mettapedia.OSLF.FiniteBranching.Controls.signature
    Mettapedia.OSLF.FiniteBranching.Controls.actions
    FinalSemantics.Controls.delayedLeft).f PUnit.unit () state

def rightAt (state : Nat) : FiniteActionTree.Tree Nat PUnit :=
  (FinalSemantics.observe Mettapedia.OSLF.FiniteBranching.Controls.signature
    Mettapedia.OSLF.FiniteBranching.Controls.actions
    FinalSemantics.Controls.delayedRight).f PUnit.unit () state

theorem left_initial_step : FiniteActionTree.Tree.step (leftAt 0) 7 = {leftAt 1} := by
  rw [leftAt, FinalSemantics.observe_step]
  change FinitePowerset.map _ ({1} : Finset Nat) = _
  exact FinitePowerset.map_singleton _ _

theorem right_initial_step : FiniteActionTree.Tree.step (rightAt 0) 7 = {rightAt 1} := by
  rw [rightAt, FinalSemantics.observe_step]
  change FinitePowerset.map _ ({1} : Finset Nat) = _
  exact FinitePowerset.map_singleton _ _

theorem left_later_step : FiniteActionTree.Tree.step (leftAt 1) 9 = {leftAt 2} := by
  rw [leftAt, FinalSemantics.observe_step]
  change FinitePowerset.map _
    (if (1 : Nat) = 0 then if (9 : Nat) = 7 then ({1} : Finset Nat) else ∅
      else if (1 : Nat) = 1 ∧ (9 : Nat) = 9 then {2} else ∅) = _
  simp only [show (1 : Nat) ≠ 0 by decide, ↓reduceIte]
  exact FinitePowerset.map_singleton _ _

theorem right_later_step : FiniteActionTree.Tree.step (rightAt 1) 9 = ∅ := by
  rw [rightAt, FinalSemantics.observe_step]
  change FinitePowerset.map _
    (if (1 : Nat) = 0 ∧ (9 : Nat) = 7 then ({1} : Finset Nat) else ∅) = ∅
  simp [FinitePowerset.map]

theorem later_readouts_differ : leftAt 1 ≠ rightAt 1 := by
  intro same
  have related := (FinalSemantics.kernel_iff_bisimilar
    Mettapedia.OSLF.FiniteBranching.Controls.signature
    Mettapedia.OSLF.FiniteBranching.Controls.actions
    FinalSemantics.Controls.delayedLeft FinalSemantics.Controls.delayedRight
    PUnit.unit () 1 1).1 same
  exact FinalSemantics.Controls.later_states_are_not_bisimilar related

abbrev finalColours : signature.Families := (FinalSemantics.finalObject signature actions).V

def twoFutureInput : signature.Term finalColours () :=
  choose (pure (leftAt 0)) (pure (rightAt 0))

def actual : FiniteActionTree.Tree Nat PUnit :=
  (finalAlgebra law).a.f PUnit.unit () twoFutureInput

theorem action_pure (tree : FiniteActionTree.Tree Nat PUnit) :
    (finalAlgebra law).a.f PUnit.unit () (pure (X := finalColours) tree) = tree :=
  congrArg (fun arrow => arrow PUnit.unit () tree) (action_unit law)

theorem complete_two_future_readout :
    FiniteActionTree.Tree.step actual 7 = {leftAt 1, rightAt 1} := by
  rw [actual, action_successors, twoFutureInput, operational_choice]
  change FinitePowerset.map ((finalAlgebra law).a.f PUnit.unit ())
    (FinitePowerset.map (pure (X := finalColours)) (FiniteActionTree.Tree.step (leftAt 0) 7) ∪
      FinitePowerset.map (pure (X := finalColours)) (FiniteActionTree.Tree.step (rightAt 0) 7)) = _
  rw [left_initial_step, right_initial_step, FinitePowerset.map_singleton,
    FinitePowerset.map_singleton]
  simp only [FinitePowerset.map, Finset.singleton_union, Finset.image_insert,
    Finset.image_singleton, action_pure]

theorem both_distinct_futures_retained :
    leftAt 1 ∈ FiniteActionTree.Tree.step actual 7 ∧
      rightAt 1 ∈ FiniteActionTree.Tree.step actual 7 ∧ leftAt 1 ≠ rightAt 1 := by
  rw [complete_two_future_readout]
  exact ⟨by simp, by simp, later_readouts_differ⟩

theorem actual_successor_count : (FiniteActionTree.Tree.step actual 7).card = 2 := by
  rw [complete_two_future_readout]
  simp [later_readouts_differ]

theorem omitting_the_later_enabled_future_fails :
    FiniteActionTree.Tree.step actual 7 ≠ {rightAt 1} := by
  intro omitted
  have member := both_distinct_futures_retained.1
  rw [omitted, Finset.mem_singleton] at member
  exact later_readouts_differ member

end Mettapedia.OSLF.FiniteBranching.FinalBialgebra.Controls
