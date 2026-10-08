import Mettapedia.CategoryTheory.FiniteActionTreeFinalSemantics

/-!
# Varying indexed controls for final finite observations

An actual growing index family supplies distinct complete successor sets.
Every natural-number action can be enabled while each set remains finite.
The final observation retains the stopped/active distinction. A coalgebra
map may identify original states, so finality supplies no state decoder.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.FiniteActionTreeFinalSemanticsControls

open _root_.CategoryTheory
open Classical

abbrev Index (base : Nat) := Fin (base + 1)
abbrev Actions (base : Nat) (_ : Index base) := Nat

def successors (base : Nat) (index : Index base) (state action : Nat) : Finset Nat :=
  if state = 0 then ∅ else {state - 1, base + index.val + action + 1}

abbrev behavior := FiniteActionTreeCofree.behavior.{0, 0, 0, 0} Nat Index Actions

abbrev system : Endofunctor.Coalgebra behavior where
  V _ _ := Nat
  str base index := ↾(successors base index)

def observe (base : Nat) (index : Index base) (state : Nat) :=
  (FiniteActionTreeFinalSemantics.observe Nat Index Actions system).f base index state

theorem whole_successors (base : Nat) (index : Index base) (state action : Nat) :
    FiniteActionTree.Tree.step (observe base index state) action =
      FinitePowerset.map (observe base index) (successors base index state action) :=
  FiniteActionTreeFinalSemantics.observe_step Nat Index Actions system base index state action

theorem growing_index_successors :
    successors 0 ⟨0, by decide⟩ 2 0 = {1} ∧
      successors 1 ⟨1, by decide⟩ 2 0 = {1, 3} := by
  decide +kernel

theorem every_action_enabled (base : Nat) (index : Index base) (action : Nat) :
    successors base index 1 action ≠ ∅ := by
  simp [successors]

theorem stopped_observation (base : Nat) (index : Index base) (action : Nat) :
    FiniteActionTree.Tree.step (observe base index 0) action = ∅ := by
  rw [whole_successors]
  simp [successors]
  rfl

theorem no_total_finite_support (base : Nat) (index : Index base) :
    ¬ ∃ enabled : Finset Nat,
      ∀ action, successors base index 1 action ≠ ∅ → action ∈ enabled := by
  rintro ⟨enabled, contains⟩
  have member := contains (enabled.sup id + 1)
    (every_action_enabled base index (enabled.sup id + 1))
  have bound : enabled.sup id + 1 ≤ enabled.sup id := Finset.le_sup (f := id) member
  omega

theorem active_not_stopped (base : Nat) (index : Index base) :
    observe base index 1 ≠ observe base index 0 := by
  intro same
  have sameStep := congrArg (fun tree => FiniteActionTree.Tree.step tree 7) same
  rw [whole_successors, stopped_observation] at sameStep
  exact every_action_enabled base index 7
    ((FinitePowerset.map_eq_empty_iff _ _).1 sameStep)

/-- Many distinct states admit the same whole infinite-loop observation. -/
abbrev loops : Endofunctor.Coalgebra behavior where
  V _ _ := Nat
  str _ _ := ↾(fun state _ => {state})

theorem loops_related (base : Nat) (index : Index base) (first second : Nat) :
    (FiniteActionTreeFinalSemantics.observe Nat Index Actions loops).f base index first =
      (FiniteActionTreeFinalSemantics.observe Nat Index Actions loops).f base index second := by
  apply (FiniteActionTreeFinalSemantics.kernel_iff_bisimilar
    Nat Index Actions loops loops base index first second).2
  refine ⟨fun _ _ state other =>
    (state = first ∨ state = second) ∧ (other = first ∨ other = second),
    ?_, Or.inl rfl, Or.inr rfl⟩
  intro _ _ state other held action
  constructor
  · intro target member
    change target ∈ ({state} : Finset Nat) at member
    have same := Finset.mem_singleton.mp member
    exact ⟨other, by change other ∈ ({other} : Finset Nat); simp, same ▸ held⟩
  · intro target member
    change target ∈ ({other} : Finset Nat) at member
    have same := Finset.mem_singleton.mp member
    exact ⟨state, by change state ∈ ({state} : Finset Nat); simp, same ▸ held⟩

theorem no_original_state_decoder (base : Nat) (index : Index base) :
    ¬ ∃ decode : FiniteActionTree.Tree Nat PUnit → Nat,
      ∀ state, decode
        ((FiniteActionTreeFinalSemantics.observe Nat Index Actions loops).f base index state) =
          state := by
  rintro ⟨decode, readout⟩
  have same := congrArg decode (loops_related base index 11 21)
  rw [readout, readout] at same
  omega

end Mettapedia.CategoryTheory.FiniteActionTreeFinalSemanticsControls
