import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSDistributive
import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSControls
import Mettapedia.CategoryTheory.FiniteActionTreeObservations

/-!
# Actual finite GSOS distributive trees and future controls

A real choice term over the constructed cofree input trees is transposed
by the earned distributive law. Its entire successor set retains both
child successors and their shared successor. Future steps preserve the
original coloured state and independently supplied dependent finite witness.
Root-only and omitted-child interpretations fail
the same complete readout. The operational recovery uses the actual cofree
unit, rather than a supplied compatibility or independently chosen decoder.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.CofreeControls

open _root_.CategoryTheory Mettapedia.CategoryTheory Mettapedia.TypeTheory
open GSOSControls
open Classical

abbrev inputTrees : signature.Families := (Cofree.comonad signature actions).obj naturals
abbrev cofreeInputs := (Cofree.functor signature actions).obj naturals
abbrev indexedLaw := lawEquiv signature actions law

def inputTree (state : Nat) : inputTrees PUnit.unit () :=
  ((Cofree.adjunction signature actions).unit.app inputs).f PUnit.unit () state

theorem input_tree_readout (state : Nat) :
    inputTree state = FiniteActionTree.Tree.coiterate (inputSteps PUnit.unit ()) id state := rfl

theorem input_tree_root (state : Nat) : FiniteActionTree.Tree.root (inputTree state) = state :=
  FiniteActionTree.Tree.root_coiterate (inputSteps PUnit.unit ()) id state

theorem input_tree_successors (state : Nat) :
    FiniteActionTree.Tree.step (inputTree state) 7 = {inputTree (state + 1), inputTree 31} := by
  rw [input_tree_readout, FiniteActionTree.Tree.step_coiterate]
  change FinitePowerset.map (FiniteActionTree.Tree.coiterate (inputSteps PUnit.unit ()) id)
    {state + 1, 31} = _
  simp [FinitePowerset.map, input_tree_readout]

def treePure (state : Nat) : signature.Term inputTrees () := pure (inputTree state)

def treeInput : signature.Term inputTrees () :=
  signature.termMonad.map ((Cofree.adjunction signature actions).unit.app inputs).f
    PUnit.unit () choiceTerm

theorem mapped_pure_readout (state : Nat) :
    signature.termMonad.map ((Cofree.adjunction signature actions).unit.app inputs).f
      PUnit.unit () (pureNat state) = treePure state := rfl

theorem tree_input_operational_successors :
    Operational.coalgebra law cofreeInputs.str PUnit.unit () treeInput 7 =
      {treePure 11, treePure 21, treePure 31} := by
  have square := congrArg (fun arrow => arrow PUnit.unit () choiceTerm 7)
    (IndexedGSOS.Operational.liftMap indexedLaw
      ((Cofree.adjunction signature actions).unit.app inputs)).h
  change FinitePowerset.map
    (signature.termMonad.map ((Cofree.adjunction signature actions).unit.app inputs).f
      PUnit.unit ())
    (((Operational.liftedMonad law).obj inputs).str PUnit.unit () choiceTerm 7) =
      Operational.coalgebra law cofreeInputs.str PUnit.unit () treeInput 7 at square
  rw [actual_choice_successors] at square
  exact square.symm.trans (by simp [FinitePowerset.map]; rfl)

def actualImage : FiniteActionTree.Tree Nat (signature.Term naturals ()) :=
  (Distributive.lawOverCofree law).app naturals PUnit.unit () treeInput

def targetTree (state : Nat) : FiniteActionTree.Tree Nat (signature.Term naturals ()) :=
  FiniteActionTree.Tree.map pureNat (inputTree state)

def colourAlgebra : signature.polynomial.Algebra naturals where
  act := fun _ _ layer => match layer with
    | ⟨.stopped, _⟩ => 0
    | ⟨.choose, children⟩ => children false + children true

def colourReadout : signature.Term naturals () → Nat :=
  IndexedPolynomial.Free.fold signature.polynomial (fun _ _ value => value)
    colourAlgebra PUnit.unit ()

theorem actual_pure_image (state : Nat) :
    (Distributive.lawOverCofree law).app naturals PUnit.unit () (treePure state) =
      targetTree state :=
  Distributive.pure_readout law naturals PUnit.unit () (inputTree state)

theorem actual_distributive_root : FiniteActionTree.Tree.root actualImage = choiceTerm := by
  calc
    FiniteActionTree.Tree.root actualImage =
        signature.termMonad.map ((Cofree.comonad signature actions).ε.app naturals)
          PUnit.unit () treeInput :=
      Distributive.root_readout law naturals PUnit.unit () treeInput
    _ = signature.termMonad.map
        (((Cofree.adjunction signature actions).unit.app inputs).f ≫
          (Cofree.comonad signature actions).ε.app naturals) PUnit.unit () choiceTerm := by
      exact (congrArg (fun arrow => arrow PUnit.unit () choiceTerm)
        (signature.termMonad.map_comp
          ((Cofree.adjunction signature actions).unit.app inputs).f
          ((Cofree.comonad signature actions).ε.app naturals))).symm
    _ = choiceTerm := by
      have cancellation : ((Cofree.adjunction signature actions).unit.app inputs).f ≫
          (Cofree.comonad signature actions).ε.app naturals = 𝟙 naturals :=
        (Cofree.adjunction signature actions).left_triangle_components inputs
      rw [cancellation]
      exact congrArg (fun arrow => arrow PUnit.unit () choiceTerm)
        (signature.termMonad.map_id naturals)

theorem actual_distributive_successors :
    FiniteActionTree.Tree.step actualImage 7 = {targetTree 11, targetTree 21, targetTree 31} := by
  rw [actualImage, Distributive.step_readout, tree_input_operational_successors]
  simp only [FinitePowerset.map, Finset.image_insert, Finset.image_singleton]
  exact congrArg₂ (fun tree (others : Finset (FiniteActionTree.Tree Nat
      (signature.Term naturals ()))) => insert tree others) (actual_pure_image 11)
    (congrArg₂ (fun tree (others : Finset (FiniteActionTree.Tree Nat
      (signature.Term naturals ()))) => insert tree others) (actual_pure_image 21)
      (congrArg (fun tree : FiniteActionTree.Tree Nat (signature.Term naturals ()) =>
        ({tree} : Finset _)) (actual_pure_image 31)))

theorem target_tree_root (state : Nat) :
    FiniteActionTree.Tree.root (targetTree state) = pureNat state := by
  rw [targetTree, FiniteActionTree.Tree.root_map, input_tree_root]

theorem complete_target_root_set :
    FinitePowerset.map FiniteActionTree.Tree.root (FiniteActionTree.Tree.step actualImage 7) =
      {pureNat 11, pureNat 21, pureNat 31} := by
  rw [actual_distributive_successors]
  simp [FinitePowerset.map, target_tree_root]

theorem complete_future_successors (state : Nat) :
    FiniteActionTree.Tree.step (targetTree state) 7 = {targetTree (state + 1), targetTree 31} := by
  rw [targetTree, FiniteActionTree.Tree.step_map, input_tree_successors]
  simp [FinitePowerset.map, targetTree]

theorem actual_successor_future_colours :
    FinitePowerset.map FiniteActionTree.Tree.root (FiniteActionTree.Tree.step (targetTree 11) 7) =
      {pureNat 12, pureNat 31} := by
  rw [complete_future_successors]
  simp [FinitePowerset.map, target_tree_root]

theorem whole_target_trees_are_distinct : targetTree 11 ≠ targetTree 21 := by
  intro same
  have roots := congrArg FiniteActionTree.Tree.root same
  rw [target_tree_root, target_tree_root] at roots
  have impossible : (11 : Nat) = 21 := congrArg colourReadout roots
  exact (by decide : (11 : Nat) ≠ 21) impossible

theorem dropping_the_second_child_is_false :
    FiniteActionTree.Tree.step actualImage 7 ≠ {targetTree 11, targetTree 31} := by
  intro same
  have member : targetTree 21 ∈ ({targetTree 11, targetTree 31} :
      Finset (FiniteActionTree.Tree Nat (signature.Term naturals ()))) := by
    rw [← same, actual_distributive_successors]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with first | last
  · exact whole_target_trees_are_distinct first.symm
  · have roots := congrArg FiniteActionTree.Tree.root last
    rw [target_tree_root, target_tree_root] at roots
    have impossible : (21 : Nat) = 31 := congrArg colourReadout roots
    exact (by decide : (21 : Nat) ≠ 31) impossible

def rootOnly : FiniteActionTree.Tree Nat (signature.Term naturals ()) :=
  FiniteActionTree.Tree.coiterate (fun _ _ => ∅) (fun _ : Unit => choiceTerm) ()

theorem root_only_agrees : FiniteActionTree.Tree.root rootOnly =
    FiniteActionTree.Tree.root actualImage := by
  rw [rootOnly, FiniteActionTree.Tree.root_coiterate, actual_distributive_root]

theorem root_only_fails_complete_behavior : rootOnly ≠ actualImage := by
  intro same
  have disabled : FiniteActionTree.Tree.step rootOnly 7 = ∅ := by
    rw [rootOnly, FiniteActionTree.Tree.step_coiterate, FinitePowerset.map_empty]
  have impossible : targetTree 11 ∈ (∅ :
      Finset (FiniteActionTree.Tree Nat (signature.Term naturals ()))) := by
    rw [← disabled, same, actual_distributive_successors]
    simp
  exact Finset.notMem_empty _ impossible

/-- The original operational set is read through the actual distributive
image, actual cofree unit and independently computed constructor law. -/
theorem actual_operational_recovery :
    FinitePowerset.map FiniteActionTree.Tree.root
      (FiniteActionTree.Tree.step ((Distributive.lawOverCofree law).app naturals PUnit.unit ()
        (signature.termMonad.map ((Cofree.adjunction signature actions).unit.app inputs).f
          PUnit.unit () choiceTerm)) 7) = {pureNat 11, pureNat 21, pureNat 31} :=
  complete_target_root_set

abbrev DependentColour := Σ size : Nat, Fin (size + 2)
abbrev dependentFamily : signature.Families := fun _ _ => DependentColour

def grow (state : DependentColour) (action : Nat) : DependentColour :=
  ⟨state.1 + (action + 1),
    Fin.castLE (Nat.add_le_add_right (Nat.le_add_right state.1 (action + 1)) 2) state.2⟩

def dependentSteps : DependentColour → Nat → Finset DependentColour :=
  fun state action => {grow state action}

def dependentTree (state : DependentColour) : FiniteActionTree.Tree Nat DependentColour :=
  FiniteActionTree.Tree.coiterate dependentSteps id state

def dependentImage (state : DependentColour) :
    FiniteActionTree.Tree Nat (signature.Term dependentFamily ()) :=
  (Distributive.lawOverCofree law).app dependentFamily PUnit.unit ()
    (pure (X := (Cofree.comonad signature actions).obj dependentFamily) (dependentTree state))

theorem dependent_image_readout (state : DependentColour) :
    dependentImage state = FiniteActionTree.Tree.map
      (pure (X := dependentFamily)) (dependentTree state) :=
  Distributive.pure_readout law dependentFamily PUnit.unit () (dependentTree state)

abbrev readoutFamily : signature.Families := fun _ _ => Nat × Nat

def dependentReadoutAlgebra : signature.polynomial.Algebra readoutFamily where
  act := fun _ _ layer => match layer with
    | ⟨.stopped, _⟩ => (0, 0)
    | ⟨.choose, children⟩ =>
      ((children false).1 + (children true).1, (children false).2 + (children true).2)

def dependentReadout : signature.Term dependentFamily () → Nat × Nat :=
  IndexedPolynomial.Free.fold signature.polynomial
    (fun _ _ value => (value.1, value.2.val)) dependentReadoutAlgebra PUnit.unit ()

theorem dependent_root_readout (state : DependentColour) :
    dependentReadout (FiniteActionTree.Tree.root (dependentImage state)) =
      (state.1, state.2.val) := by
  rw [dependent_image_readout, FiniteActionTree.Tree.root_map,
    dependentTree, FiniteActionTree.Tree.root_coiterate]
  rfl

theorem dependent_image_successors (state : DependentColour) (action : Nat) :
    FiniteActionTree.Tree.step (dependentImage state) action =
      {dependentImage (grow state action)} := by
  rw [dependent_image_readout, FiniteActionTree.Tree.step_map]
  have oneStep : FiniteActionTree.Tree.step (dependentTree state) action =
      {dependentTree (grow state action)} :=
    (FiniteActionTree.Tree.step_coiterate dependentSteps id state action).trans
      (FinitePowerset.map_singleton _ _)
  rw [oneStep, FinitePowerset.map_singleton, ← dependent_image_readout]

theorem dependent_future_readout (state : DependentColour) (action : Nat) :
    FinitePowerset.map (dependentReadout ∘ FiniteActionTree.Tree.root)
      (FiniteActionTree.Tree.step (dependentImage state) action) =
        {(state.1 + (action + 1), state.2.val)} := by
  rw [dependent_image_successors, FinitePowerset.map_singleton]
  change {dependentReadout (FiniteActionTree.Tree.root (dependentImage (grow state action)))} = _
  rw [dependent_root_readout]
  rfl

def suppliedDependentColour : DependentColour := ⟨0, 1⟩

theorem actual_dependent_future_domain_and_position :
    FinitePowerset.map (dependentReadout ∘ FiniteActionTree.Tree.root)
      (FiniteActionTree.Tree.step
        (dependentImage (grow suppliedDependentColour 7)) 2) = {(11, 1)} :=
  dependent_future_readout (grow suppliedDependentColour 7) 2

theorem actual_dependent_position_not_erased :
    FinitePowerset.map (dependentReadout ∘ FiniteActionTree.Tree.root)
      (FiniteActionTree.Tree.step
        (dependentImage (grow suppliedDependentColour 7)) 2) ≠ {(11, 0)} := by
  rw [actual_dependent_future_domain_and_position]
  intro same
  have impossible : (11, 1) = (11, 0) := Finset.singleton_injective same
  exact (by decide : (1 : Nat) ≠ 0) (congrArg Prod.snd impossible)

end Mettapedia.OSLF.FiniteBranching.CofreeControls
