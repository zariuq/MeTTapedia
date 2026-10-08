import Mettapedia.CategoryTheory.FiniteActionTreeCofree
import Mettapedia.CategoryTheory.FiniteActionTreeObservations

/-!
# Fork, loop, colour and occurrence-erasure controls

The complete coiteration retains two differently coloured fork successors,
and an actual loop has its whole tree as a successor. Every natural-number
label may be enabled while each label has one successor. Reordered raw
branches and duplicated bisimilar branches become the same quotient tree;
neither their slot order nor their occurrence count can be decoded from it.
The categorical controls read the actual cofree adjunction and derived
comonad rather than a separate stipulated tree interpretation.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.FiniteActionTree.Controls

open _root_.CategoryTheory
open Classical

def leaf (colour : Nat) : Raw Unit Nat :=
  node colour (fun _ => 0) (fun _ slot => Fin.elim0 slot)

@[simp] theorem root_leaf (colour : Nat) : root (leaf colour) = colour := rfl

@[simp] theorem step_leaf (colour : Nat) (action : Unit) : step (leaf colour) action = ∅ := by
  simp [leaf, step_node, FinitePowerset.map]

def rawFork (left right : Nat) : Raw Unit Nat :=
  node 0 (fun _ => 2) (fun _ slot => if slot = 0 then leaf left else leaf right)

theorem step_rawFork (left right : Nat) (action : Unit) :
    step (rawFork left right) action = {leaf left, leaf right} := by
  classical
  simp [rawFork, step_node, FinitePowerset.map, Finset.univ_fin2]

def fork (left right : Nat) : Tree Unit Nat := project (rawFork left right)

theorem step_fork (left right : Nat) (action : Unit) :
    Tree.step (fork left right) action = {project (leaf left), project (leaf right)} := by
  classical
  rw [fork, Tree.step_project, step_rawFork]
  simp [FinitePowerset.map]

theorem differently_coloured_leaves (left right : Nat) (different : left ≠ right) :
    project (leaf left) ≠ project (leaf right) := by
  intro same
  exact different (congrArg Tree.root same)

theorem fork_retains_both_distinct_colours :
    Tree.step (fork 11 21) () = {project (leaf 11), project (leaf 21)} ∧
      project (leaf 11) ≠ project (leaf 21) :=
  ⟨step_fork 11 21 (), differently_coloured_leaves 11 21 (by decide)⟩

theorem fork_branch_order_is_forgotten (left right : Nat) : fork left right = fork right left := by
  apply Tree.ext
  · rfl
  · intro action
    rw [step_fork, step_fork]
    exact Finset.pair_comm _ _

def firstColour (tree : Raw Unit Nat) : Option Nat :=
  if present : 0 < count tree () then some (root (child tree () ⟨0, present⟩)) else none

theorem first_colour_before_swap : firstColour (rawFork 11 21) = some 11 := rfl
theorem first_colour_after_swap : firstColour (rawFork 21 11) = some 21 := rfl

theorem reordered_raw_trees_are_distinct : rawFork 11 21 ≠ rawFork 21 11 := by
  intro same
  have reading := congrArg firstColour same
  rw [first_colour_before_swap, first_colour_after_swap] at reading
  have impossible : (11 : Nat) = 21 := Option.some.inj reading
  exact (by decide : (11 : Nat) ≠ 21) impossible

theorem no_branch_order_decoder :
    ¬ ∃ decode : Tree Unit Nat → Option Nat,
      ∀ raw, decode (project raw) = firstColour raw := by
  rintro ⟨decode, recovers⟩
  have same := congrArg decode (fork_branch_order_is_forgotten 11 21)
  change decode (project (rawFork 11 21)) = decode (project (rawFork 21 11)) at same
  rw [recovers, recovers, first_colour_before_swap, first_colour_after_swap] at same
  exact (by decide : (11 : Nat) ≠ 21) (Option.some.inj same)

def rawSingle (colour : Nat) : Raw Unit Nat :=
  node 0 (fun _ => 1) (fun _ _ => leaf colour)

theorem duplicate_branch_is_forgotten (colour : Nat) :
    fork colour colour = project (rawSingle colour) := by
  classical
  apply Tree.ext
  · rfl
  · intro action
    rw [step_fork, Tree.step_project]
    simp [rawSingle, step_node, FinitePowerset.map]

theorem no_occurrence_count_decoder :
    ¬ ∃ decode : Tree Unit Nat → Nat, ∀ raw, decode (project raw) = count raw () := by
  rintro ⟨decode, recovers⟩
  have same := congrArg decode (duplicate_branch_is_forgotten 7)
  change decode (project (rawFork 7 7)) = decode (project (rawSingle 7)) at same
  rw [recovers, recovers] at same
  change (2 : Nat) = 1 at same
  exact (by decide : (2 : Nat) ≠ 1) same

def system : Nat → Nat → Finset Nat := fun state action =>
  if action = 7 then if state = 0 then {11, 21} else {state} else ∅

def actualTree (state : Nat) : Tree Nat Nat := Tree.coiterate system id state

theorem actual_root (state : Nat) : Tree.root (actualTree state) = state :=
  Tree.root_coiterate system id state

theorem actual_fork_successors :
    Tree.step (actualTree 0) 7 = {actualTree 11, actualTree 21} := by
  classical
  rw [actualTree, Tree.step_coiterate]
  simp [system, FinitePowerset.map, actualTree]

theorem actual_loop_successor : Tree.step (actualTree 11) 7 = {actualTree 11} := by
  rw [actualTree, Tree.step_coiterate]
  have actual : system 11 7 = {11} := by simp [system]
  rw [actual, FinitePowerset.map_singleton]

theorem actual_fork_subtrees_are_distinct : actualTree 11 ≠ actualTree 21 := by
  intro same
  have impossible : (11 : Nat) = 21 := (actual_root 11).symm.trans
    ((congrArg Tree.root same).trans (actual_root 21))
  exact (by decide : (11 : Nat) ≠ 21) impossible

theorem actual_colour_map_readout (state : Nat) :
    Tree.root (Tree.map (fun colour : Nat => colour + 9) (actualTree state)) = state + 9 := by
  rw [Tree.root_map, actual_root]

theorem actual_colour_map_retains_complete_fork :
    Tree.step (Tree.map (fun colour : Nat => colour + 9) (actualTree 0)) 7 =
      {Tree.map (fun colour : Nat => colour + 9) (actualTree 11),
        Tree.map (fun colour : Nat => colour + 9) (actualTree 21)} := by
  classical
  rw [Tree.step_map, actual_fork_successors]
  simp [FinitePowerset.map]

def collapsedSystem : Unit → Nat → Finset Unit :=
  fun _ action => if action = 7 then {()} else ∅

theorem state_collapse_square (state action : Nat) :
    FinitePowerset.map (fun _ : Nat => ()) (system state action) =
      collapsedSystem () action := by
  by_cases enabled : action = 7
  · subst action
    by_cases initial : state = 0 <;>
      simp [system, collapsedSystem, initial, FinitePowerset.map]
  · simp [system, collapsedSystem, enabled, FinitePowerset.map]

def collapsedTree : Tree Nat Unit := Tree.coiterate collapsedSystem id ()

theorem actual_state_identification (state : Nat) :
    Tree.map (fun _ : Nat => ()) (actualTree state) = collapsedTree := by
  rw [actualTree, Tree.map_coiterate]
  exact Tree.coiterate_natural system collapsedSystem (fun _ => ())
    state_collapse_square id state

theorem actual_branch_collision :
    Tree.step (Tree.map (fun _ : Nat => ()) (actualTree 0)) 7 = {collapsedTree} := by
  classical
  rw [Tree.step_map, actual_fork_successors]
  change FinitePowerset.map (Tree.map (fun _ : Nat => ()))
    {actualTree 11, actualTree 21} = _
  simp [FinitePowerset.map, actual_state_identification]

theorem no_original_colour_decoder :
    ¬ ∃ decode : Tree Nat Unit → Nat,
      ∀ state, decode (Tree.map (fun _ : Nat => ()) (actualTree state)) = state := by
  rintro ⟨decode, recovers⟩
  have same : Tree.map (fun _ : Nat => ()) (actualTree 11) =
      Tree.map (fun _ : Nat => ()) (actualTree 21) :=
    (actual_state_identification 11).trans (actual_state_identification 21).symm
  have reading := congrArg decode same
  rw [recovers, recovers] at reading
  exact (by decide : (11 : Nat) ≠ 21) reading

def infiniteLabels : Nat → Nat → Finset Nat := fun state action => {state + action + 1}

def allLabelsTree : Tree Nat Nat := Tree.coiterate infiniteLabels id 0

theorem every_label_has_one_supplied_successor (action : Nat) :
    Tree.step allLabelsTree action = {Tree.coiterate infiniteLabels id (action + 1)} := by
  rw [allLabelsTree, Tree.step_coiterate, infiniteLabels, FinitePowerset.map_singleton]
  simp only [Nat.zero_add]

theorem no_finite_enabled_label_support :
    ¬ ∃ support : Finset Nat,
      ∀ action, Tree.step allLabelsTree action ≠ ∅ → action ∈ support := by
  rintro ⟨support, covers⟩
  obtain ⟨action, missing⟩ := Infinite.exists_notMem_finset support
  apply missing
  apply covers action
  rw [every_label_has_one_supplied_successor]
  exact Finset.singleton_ne_empty _

abbrev family : FiniteActionTreeCofree.Families Unit (fun _ => Unit) := fun _ _ => Nat
abbrev actions : ∀ base : Unit, (fun _ : Unit => Unit) base → Type := fun _ _ => Nat

abbrev input : Endofunctor.Coalgebra (FiniteActionTreeCofree.behavior Unit (fun _ => Unit) actions) where
  V := family
  str _ _ := ↾system

def suppliedColour : input.V ⟶ family := fun _ _ => ↾(fun state : Nat => state + 5)

theorem actual_adjunction_transpose (state : Nat) :
    (((FiniteActionTreeCofree.adjunction Unit (fun _ => Unit) actions).homEquiv input family)
      suppliedColour).f () () state = Tree.coiterate system (fun value => value + 5) state :=
  FiniteActionTreeCofree.transpose_readout Unit (fun _ => Unit) actions
    input family suppliedColour () () state

theorem actual_adjunction_root (state : Nat) :
    Tree.root ((((FiniteActionTreeCofree.adjunction Unit (fun _ => Unit) actions).homEquiv
      input family) suppliedColour).f () () state) = state + 5 := by
  rw [actual_adjunction_transpose, Tree.root_coiterate]

theorem actual_comonad_counit (state : Nat) :
    ((FiniteActionTreeCofree.comonad Unit (fun _ => Unit) actions).ε.app family) () ()
      (actualTree state) = state := actual_root state

theorem actual_comonad_duplication_root (state : Nat) :
    Tree.root (((FiniteActionTreeCofree.comonad Unit (fun _ => Unit) actions).δ.app family)
      () () (actualTree state)) = actualTree state :=
  FiniteActionTreeCofree.comultiplication_root Unit (fun _ => Unit) actions
    family () () (actualTree state)

theorem actual_comonad_duplication_complete_fork :
    Tree.step (((FiniteActionTreeCofree.comonad Unit (fun _ => Unit) actions).δ.app family)
      () () (actualTree 0)) 7 = {Tree.duplicate (actualTree 11), Tree.duplicate (actualTree 21)} := by
  classical
  change Tree.step (Tree.duplicate (actualTree 0)) 7 = _
  rw [Tree.step_duplicate, actual_fork_successors]
  simp [FinitePowerset.map]
  rfl

end Mettapedia.CategoryTheory.FiniteActionTree.Controls
