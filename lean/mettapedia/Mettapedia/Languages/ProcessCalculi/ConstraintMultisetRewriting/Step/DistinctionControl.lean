import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DistinctionContracts
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DistinctionMachine

/-!
# Choice ownership and bounded control guarantees

At an agent-owned state, the agent chooses an enabled label and all of that
label's possible outcomes must satisfy the postcondition. At an environment-
owned state every enabled outcome must do so. Non-emptiness prevents deadlock
from proving a vacuous guarantee. This is certain bounded reachability under
demonic outcomes, not a probability-of-success calculation.

Bisimulation preserves the guarantee when it preserves choice ownership and
the goal. The actual transform control shows that hiding ownership can retain
ordinary observations and branching behavior while changing the guarantee.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionControl
open Interface
universe uOb uT uH uO uS uF uL
variable {Obj : Type uOb} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uO} [DecidableEq O] {State : Type uS}
  {Fir : State → Type uF} {L : Type uL}
  (P : Interface.Step X O State Fir) (offers : L → (s : State) → Fir s → Prop)

def Pre (owner : State → Bool) (post : State → Prop) (s : State) : Prop :=
  if owner s then
    ∃ a, (∃ t, Race.Generic.Moves P offers s a t) ∧
      ∀ t, Race.Generic.Moves P offers s a t → post t
  else
    (∃ a t, Race.Generic.Moves P offers s a t) ∧
      ∀ a t, Race.Generic.Moves P offers s a t → post t

def ForceWithin (owner : State → Bool) (goal : State → Prop) : Nat → State → Prop
  | 0, s => goal s
  | n + 1, s => goal s ∨ Pre P offers owner (ForceWithin owner goal n) s

theorem pre_related {R : State → State → Prop}
    (bisim : (Race.Generic.system P offers).IsBisimulation R)
    {owner : State → Bool} (owners : ∀ s t, R s t → owner s = owner t)
    {post : State → Prop} (posts : ∀ s t, R s t → post s → post t)
    {s t : State} (related : R s t) : Pre P offers owner post s → Pre P offers owner post t := by
  have same := owners s t related
  by_cases agent : owner s = true
  · have agent' : owner t = true := same ▸ agent
    simp only [Pre, agent, agent', if_true]
    rintro ⟨a, ⟨s', moved⟩, all⟩
    obtain ⟨t', moved', _⟩ := bisim.1 related a moved
    refine ⟨a, ⟨t', moved'⟩, ?_⟩
    intro u step
    obtain ⟨v, step', rel⟩ := bisim.2.1 related a step
    exact posts v u rel (all v step')
  · have agent' : owner t ≠ true := by rwa [← same]
    simp only [Pre, agent, agent']
    rintro ⟨⟨a, s', moved⟩, all⟩
    obtain ⟨t', moved', _⟩ := bisim.1 related a moved
    refine ⟨⟨a, t', moved'⟩, ?_⟩
    intro b u step
    obtain ⟨v, step', rel⟩ := bisim.2.1 related b step
    exact posts v u rel (all b v step')

theorem force_related {R : State → State → Prop}
    (bisim : (Race.Generic.system P offers).IsBisimulation R)
    {owner : State → Bool} (owners : ∀ s t, R s t → owner s = owner t)
    {goal : State → Prop} (goals : ∀ s t, R s t → (goal s ↔ goal t)) (n : Nat) :
    ∀ s t, R s t → ForceWithin P offers owner goal n s → ForceWithin P offers owner goal n t := by
  induction n with
  | zero => exact fun s t related holds => (goals s t related).mp holds
  | succ n ih =>
      intro s t related holds
      rcases holds with done | later
      · exact Or.inl ((goals s t related).mp done)
      · exact Or.inr (pre_related P offers bisim owners ih related later)

theorem force_congr {R : State → State → Prop}
    (bisim : (Race.Generic.system P offers).IsBisimulation R)
    {owner : State → Bool} (owners : ∀ s t, R s t → owner s = owner t)
    {goal : State → Prop} (goals : ∀ s t, R s t → (goal s ↔ goal t))
    (n : Nat) {s t : State} (related : R s t) :
    ForceWithin P offers owner goal n s ↔ ForceWithin P offers owner goal n t := by
  have reversed : (Race.Generic.system P offers).IsBisimulation (fun x y => R y x) :=
    ⟨fun _ _ h a _ step => bisim.2.1 h a step,
      fun _ _ h a _ step => bisim.1 h a step,
      fun _ _ h atom => (bisim.2.2 h atom).symm⟩
  exact ⟨force_related P offers bisim owners goals n s t related,
    force_related P offers reversed (fun x y h => (owners y x h).symm)
      (fun x y h => (goals y x h).symm) n t s related⟩

/-- An exact observer that retains owner and goal preserves every bounded certain guarantee. -/
theorem force_of_exact {Code : Type*} (encode : State → Code)
    (owner goal : State → Bool)
    (certified : DistinctionObserver.Stable P offers encode ∧
      DistinctionObserver.Reads encode (fun s => (owner s, goal s)))
    (n : Nat) {s t : State} (same : encode s = encode t) :
    ForceWithin P offers owner (fun x => goal x = true) n s ↔
      ForceWithin P offers owner (fun x => goal x = true) n t := by
  have exactView := (DistinctionObserver.exact_iff_kernel_bisimulation P offers encode
    (fun s => (owner s, goal s))).mp certified
  have base : (Race.Generic.system P offers).IsBisimulation (fun s t => encode s = encode t) :=
    ⟨exactView.1, exactView.2.1, fun _ _ _ atom => atom.elim⟩
  apply force_congr P offers base
    (fun x y h => congrArg Prod.fst (certified.2 x y h))
    (fun x y h => ?_) n same
  have equal : goal x = goal y := congrArg Prod.snd (certified.2 x y h)
  rw [equal]

namespace Controls
open DistinctionFinite

def machine : Machine (Bool × Bool) Bool Bool :=
  ⟨Prod.snd, fun s a => [(s.1, a)]⟩
def owner (s : Nat × (Bool × Bool)) : Bool := s.2.1
def goal (s : Nat × (Bool × Bool)) : Prop := s.2.2 = true

theorem ownership_hidden_by_exact_branching_view : machine.checkEncoding Prod.snd = true := by decide

theorem agent_can_ensure : ForceWithin machine.step.toStep Machine.offers owner goal 1 (0, true, false) := by
  right
  change ∃ a, (∃ t, Race.Generic.Moves machine.step.toStep Machine.offers (0, true, false) a t) ∧
    ∀ t, Race.Generic.Moves machine.step.toStep Machine.offers (0, true, false) a t → goal t
  refine ⟨true, ⟨(1, true, true), machine.every_successor_fires _ _ _ (List.mem_singleton_self _)⟩, ?_⟩
  intro t moved
  have target := List.mem_singleton.mp (machine.no_extra_successor _ _ _ moved)
  exact congrArg Prod.snd target

theorem environment_can_prevent : ¬ ForceWithin machine.step.toStep Machine.offers owner goal 1 (0, false, false) := by
  rintro (done | later)
  · cases done
  · have all := later.2
    have falseGoal := all false (1, false, false)
      (machine.every_successor_fires _ _ _ (List.mem_singleton_self _))
    cases falseGoal

end Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionControl
