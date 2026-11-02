import Mettapedia.Algebra.Order.FixedPointIteration
import Mathlib.Data.Set.Lattice

/-!
# Independent path meaning for the CTL fixed-point core

Existential next is a relational predecessor. Existential until is an inductive
finite path; existential globally is an infinite path. Their correspondence
with least and greatest fixed points is proved rather than used as their
definition. Deadlocks are not silently given successors: adding stuttering
changes the relation and can change the answer.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.CTLFixedPoints

variable {State : Type}

def pre (relation : State → State → Prop) (target : Set State) : Set State :=
  { state | ∃ next, relation state next ∧ next ∈ target }

theorem pre_mono (relation : State → State → Prop) : Monotone (pre relation) := by
  intro first second included state
  rintro ⟨next, edge, member⟩
  exact ⟨next, edge, included member⟩

def untilOperator (relation : State → State → Prop) (holds goal : Set State) : Set State →o Set State where
  toFun target := goal ∪ (holds ∩ pre relation target)
  monotone' first second included state member := by
    rcases member with goalReached | ⟨holding, next⟩
    · exact Or.inl goalReached
    · exact Or.inr ⟨holding, pre_mono relation included next⟩

def globallyOperator (relation : State → State → Prop) (holds : Set State) : Set State →o Set State where
  toFun target := holds ∩ pre relation target
  monotone' _ _ included _ member := ⟨member.1, pre_mono relation included member.2⟩

inductive Until (relation : State → State → Prop) (holds goal : Set State) : State → Prop
  | reached {state : State} : state ∈ goal → Until relation holds goal state
  | advance {state next : State} : state ∈ holds → relation state next →
      Until relation holds goal next → Until relation holds goal state

theorem until_iff_lfp (relation : State → State → Prop) (holds goal : Set State) (state : State) :
    Until relation holds goal state ↔ state ∈ (untilOperator relation holds goal).lfp := by
  constructor
  · intro path
    induction path with
    | reached member =>
      rw [← OrderHom.map_lfp]
      exact Or.inl member
    | @advance current next member edge _ ih =>
      rw [← OrderHom.map_lfp]
      exact Or.inr ⟨member, next, edge, ih⟩
  · intro member
    have included : (untilOperator relation holds goal).lfp ⊆ { state | Until relation holds goal state } := by
      apply OrderHom.lfp_le
      intro current generated
      rcases generated with reached | ⟨holding, next, edge, tail⟩
      · exact .reached reached
      · exact .advance holding edge tail
    exact included member

def Globally (relation : State → State → Prop) (holds : Set State) (state : State) : Prop :=
  ∃ path : Nat → State, path 0 = state ∧ ∀ i, path i ∈ holds ∧ relation (path i) (path (i + 1))

theorem globally_iff_gfp (relation : State → State → Prop) (holds : Set State) (state : State) :
    Globally relation holds state ↔ state ∈ (globallyOperator relation holds).gfp := by
  constructor
  · intro path
    have included : { state | Globally relation holds state } ⊆ (globallyOperator relation holds).gfp := by
      apply OrderHom.le_gfp
      intro current witness
      obtain ⟨path, start, valid⟩ := witness
      subst current
      refine ⟨(valid 0).1, path 1, (valid 0).2, ?_⟩
      exact ⟨fun i => path (i + 1), rfl, fun i => valid (i + 1)⟩
    exact included path
  · intro member
    classical
    let operator := globallyOperator relation holds
    have unroll (current : State) (inside : current ∈ operator.gfp) :
        current ∈ holds ∧ ∃ next, relation current next ∧ next ∈ operator.gfp := by
      rw [← operator.map_gfp] at inside
      exact inside
    let Live := { current : State // current ∈ operator.gfp }
    have successor : ∀ current : Live, ∃ next : Live, relation current.val next.val := by
      intro current
      obtain ⟨next, edge, inside⟩ := (unroll current.val current.property).2
      exact ⟨⟨next, inside⟩, edge⟩
    let move : Live → Live := fun current => Classical.choose (successor current)
    have edge (current : Live) : relation current.val (move current).val := Classical.choose_spec (successor current)
    let initial : Live := ⟨state, member⟩
    refine ⟨fun i => ((move^[i]) initial).val, rfl, ?_⟩
    intro i
    refine ⟨(unroll ((move^[i]) initial).val ((move^[i]) initial).property).1, ?_⟩
    dsimp only
    rw [Function.iterate_succ_apply']
    exact edge ((move^[i]) initial)

def stutter (relation : State → State → Prop) (before after : State) : Prop :=
  relation before after ∨ (¬ ∃ next, relation before next) ∧ after = before

theorem deadlock_not_globally (relation : State → State → Prop) (holds : Set State) (state : State)
    (dead : ¬ ∃ next, relation state next) : ¬ Globally relation holds state := by
  rintro ⟨path, start, valid⟩
  apply dead
  exact ⟨path 1, start ▸ (valid 0).2⟩

theorem stuttering_deadlock_globally (relation : State → State → Prop) (holds : Set State) (state : State)
    (dead : ¬ ∃ next, relation state next) (holding : state ∈ holds) : Globally (stutter relation) holds state := by
  exact ⟨fun _ => state, rfl, fun _ => ⟨holding, Or.inr ⟨dead, rfl⟩⟩⟩

namespace Controls

theorem deadlock_policy_changes_truth :
    ¬ Globally (fun _ _ : Unit => False) Set.univ () ∧
      Globally (stutter (fun _ _ : Unit => False)) Set.univ () := by
  exact ⟨deadlock_not_globally _ _ _ (by simp), stuttering_deadlock_globally _ _ _ (by simp) (by simp)⟩

theorem goal_may_hold_without_a_successor : Until (fun _ _ : Unit => False) ∅ Set.univ () :=
  .reached (by simp)

end Controls
end Mettapedia.Logic.CTLFixedPoints
