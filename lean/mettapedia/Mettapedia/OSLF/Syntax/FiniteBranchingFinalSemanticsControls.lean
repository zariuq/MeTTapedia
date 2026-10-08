import Mettapedia.OSLF.Syntax.FiniteBranchingFinalSemantics
import Mettapedia.OSLF.Syntax.FiniteBranchingBisimulationControls
import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSCongruenceControls

/-!
# Complete final behavior, erased multiplicity and delayed distinctions

Two independently authored coalgebras with different successor counts have
the same complete final observation through a genuine many-to-one
bisimulation. No successor-count decoder exists for that observation.
Stopped behavior remains distinguishable, and two systems agreeing at the
initial step can differ at a later label. Constructor controls use the
actual nondeterministic GSOS law and the already proved full-context
congruence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.FinalSemantics.Controls

open _root_.CategoryTheory Mettapedia.CategoryTheory
open Mettapedia.OSLF.FiniteBranching.Controls
open Bisimulation.Controls

theorem actual_many_to_one_final_observation :
    (observe signature actions leftObject).f PUnit.unit () 5 =
      (observe signature actions rightObject).f PUnit.unit () 0 :=
  observe_of_admitted signature actions related admitted PUnit.unit () rfl

theorem actual_complete_fork_readout :
    FiniteActionTree.Tree.step
      ((observe signature actions leftObject).f PUnit.unit () 5) 7 =
        FinitePowerset.map ((observe signature actions leftObject).f PUnit.unit ())
          {11, 21} := by
  rw [observe_step]
  rfl

theorem no_successor_count_decoder :
    ¬ ∃ decode : FiniteActionTree.Tree Nat PUnit → Nat,
      ∀ (object : Endofunctor.Coalgebra (behaviourFunctor signature actions))
        (state : object.V PUnit.unit ()),
        decode ((observe signature actions object).f PUnit.unit () state) =
          (object.str PUnit.unit () state 7).card := by
  rintro ⟨decode, recovers⟩
  have first := recovers leftObject 5
  have second := recovers rightObject 0
  have readings := congrArg decode actual_many_to_one_final_observation
  rw [first, second] at readings
  change ({11, 21} : Finset Nat).card = ({0} : Finset Nat).card at readings
  simp at readings

theorem stopped_final_observation_is_different :
    (observe signature actions leftObject).f PUnit.unit () 5 ≠
      (observe signature actions stoppedObject).f PUnit.unit () 0 := by
  intro same
  have related := (kernel_iff_bisimilar signature actions leftObject stoppedObject
    PUnit.unit () 5 0).1 same
  have unavailable := (Bisimulation.bisimilar_availability
    (left := leftObject) (right := stoppedObject) (value := 5) (other := 0)
    PUnit.unit () related 7).2 rfl
  change ({11, 21} : Finset Nat) = ∅ at unavailable
  exact Finset.notMem_empty 11 (unavailable ▸ (by simp : 11 ∈ ({11, 21} : Finset Nat)))

abbrev delayedLeft : Endofunctor.Coalgebra (behaviourFunctor signature actions) where
  V := naturals
  str _ _ := ↾(fun state action =>
    if state = 0 then if action = 7 then {1} else ∅
    else if state = 1 ∧ action = 9 then {2} else ∅)

abbrev delayedRight : Endofunctor.Coalgebra (behaviourFunctor signature actions) where
  V := naturals
  str _ _ := ↾(fun state action => if state = 0 ∧ action = 7 then {1} else ∅)

theorem initial_one_step_agreement (action : Nat) :
    delayedLeft.str PUnit.unit () 0 action = delayedRight.str PUnit.unit () 0 action := by
  change (if action = 7 then ({1} : Finset Nat) else ∅) =
    (if (0 : Nat) = 0 ∧ action = 7 then {1} else ∅)
  simp

theorem later_states_are_not_bisimilar :
    ¬ Bisimulation.Bisimilar delayedLeft delayedRight PUnit.unit () 1 1 := by
  intro related
  have disabled : delayedRight.str PUnit.unit () 1 9 = ∅ := by
    change (if (1 : Nat) = 0 ∧ (9 : Nat) = 7 then ({1} : Finset Nat) else ∅) = ∅
    simp
  have unavailable := (Bisimulation.bisimilar_availability
    (left := delayedLeft) (right := delayedRight) (value := 1) (other := 1)
    PUnit.unit () related 9).2 disabled
  have enabled : delayedLeft.str PUnit.unit () 1 9 = {2} := by
    change (if (1 : Nat) = 0 then if (9 : Nat) = 7 then ({1} : Finset Nat) else ∅
      else if (1 : Nat) = 1 ∧ (9 : Nat) = 9 then {2} else ∅) = {2}
    simp
  rw [enabled] at unavailable
  exact Finset.singleton_ne_empty 2 unavailable

theorem initial_states_are_not_bisimilar :
    ¬ Bisimulation.Bisimilar delayedLeft delayedRight PUnit.unit () 0 0 := by
  intro related
  have enabled : 1 ∈ delayedLeft.str PUnit.unit () 0 7 := by
    change 1 ∈ ({1} : Finset Nat)
    simp
  obtain ⟨other, member, paired⟩ :=
    (Bisimulation.bisimilar_admitted delayedLeft delayedRight PUnit.unit () 0 0 related 7).1
      1 enabled
  have same : other = 1 := by
    change other ∈ ({1} : Finset Nat) at member
    exact Finset.mem_singleton.mp member
  subst other
  exact later_states_are_not_bisimilar paired

theorem delayed_final_observations_are_different :
    (observe signature actions delayedLeft).f PUnit.unit () 0 ≠
      (observe signature actions delayedRight).f PUnit.unit () 0 :=
  fun same => initial_states_are_not_bisimilar
    ((kernel_iff_bisimilar signature actions delayedLeft delayedRight PUnit.unit () 0 0).1 same)

theorem actual_nested_gsos_final_observation :
    (observe GSOSControls.signature GSOSControls.actions
      Bisimulation.CongruenceControls.liftedInputs).f PUnit.unit ()
        Bisimulation.CongruenceControls.firstTerm =
      (observe GSOSControls.signature GSOSControls.actions
        Bisimulation.CongruenceControls.liftedInputs).f PUnit.unit ()
          Bisimulation.CongruenceControls.secondTerm :=
  (kernel_iff_bisimilar GSOSControls.signature GSOSControls.actions
    Bisimulation.CongruenceControls.liftedInputs Bisimulation.CongruenceControls.liftedInputs
    PUnit.unit () _ _).2 Bisimulation.CongruenceControls.actual_nested_context_congruence

theorem equivalent_nested_gsos_terms_remain_distinct :
    Bisimulation.CongruenceControls.firstTerm ≠ Bisimulation.CongruenceControls.secondTerm :=
  Bisimulation.CongruenceControls.full_related_terms_are_distinct

theorem actual_stopped_gsos_final_observation_is_different :
    (observe GSOSControls.signature GSOSControls.actions
      Bisimulation.CongruenceControls.liftedInputs).f PUnit.unit () GSOSControls.stopped ≠
      (observe GSOSControls.signature GSOSControls.actions
        Bisimulation.CongruenceControls.liftedInputs).f PUnit.unit () (GSOSControls.pure 10) :=
  fun same => Bisimulation.CongruenceControls.stopped_is_not_bisimilar_to_enabled
    ((kernel_iff_bisimilar GSOSControls.signature GSOSControls.actions
      Bisimulation.CongruenceControls.liftedInputs Bisimulation.CongruenceControls.liftedInputs
      PUnit.unit () _ _).1 same)

end Mettapedia.OSLF.FiniteBranching.FinalSemantics.Controls
