import Mathlib.Logic.Relation
import Mathlib.Data.Setoid.Basic

/-!
# Exploring a finer key partition by representatives

A key need not identify every pair in the semantic equation relation.
If it identifies only equivalent states, and those equations transport
actual steps in either direction, stepping the key's representative
preserves and reflects reachable terminal observations.

The qualifier is necessary. A finer equality is not a matcher, a
coherence theorem, a schedule, or a guarantee at fixed fuel. The
observation must also ignore the distinctions being quotiented out.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.RefinedStateExploration

universe u v w

open Relation
variable {State : Type u} {Key : Type v} {Obs : Type w}

structure Keys (State : Type u) (Key : Type v) where
  encode : State → Key
  representative : Key → State
  roundTrip : ∀ key, encode (representative key) = key

/-- A fibre may split a semantic class but may not combine two. -/
def Keys.FinerThan (coding : Keys State Key) (equations : Setoid State) : Prop :=
  ∀ ⦃a b⦄, coding.encode a = coding.encode b → equations.r a b

theorem Keys.representative_equivalent (coding : Keys State Key) {equations : Setoid State}
    (fine : coding.FinerThan equations) (state : State) :
    equations.r (coding.representative (coding.encode state)) state :=
  fine (coding.roundTrip (coding.encode state))

def StepTransport (equations : Setoid State) (step : State → State → Prop) : Prop :=
  ∀ ⦃source source' target⦄, equations.r source source' → step source target →
    ∃ target', step source' target' ∧ equations.r target target'

def Keys.step (coding : Keys State Key) (raw : State → State → Prop) (source dest : Key) : Prop :=
  ∃ result, raw (coding.representative source) result ∧ coding.encode result = dest

section Reach

variable (coding : Keys State Key) {equations : Setoid State} {raw : State → State → Prop}

theorem reaches_representative (fine : coding.FinerThan equations)
    (transport : StepTransport equations raw)
    {source target : State} (run : ReflTransGen raw source target) :
    ∃ result, ReflTransGen (coding.step raw) (coding.encode source) result ∧
      equations.r (coding.representative result) target := by
  induction run with
  | refl => exact ⟨_, .refl, coding.representative_equivalent fine _⟩
  | tail _ next ih =>
      obtain ⟨displayed, earlier, before⟩ := ih
      obtain ⟨result, step, after⟩ := transport (equations.iseqv.symm before) next
      exact ⟨coding.encode result, earlier.tail ⟨result, step, rfl⟩,
        equations.iseqv.trans (coding.representative_equivalent fine result) (equations.iseqv.symm after)⟩

theorem reaches_raw (fine : coding.FinerThan equations)
    (transport : StepTransport equations raw) {source : State} {result : Key}
    (run : ReflTransGen (coding.step raw) (coding.encode source) result) :
    ∃ target, ReflTransGen raw source target ∧ equations.r target (coding.representative result) := by
  induction run with
  | refl => exact ⟨_, .refl, equations.iseqv.symm (coding.representative_equivalent fine source)⟩
  | tail _ next ih =>
      obtain ⟨earlier, executed, before⟩ := ih
      obtain ⟨displayed, step, rfl⟩ := next
      obtain ⟨result, rawStep, after⟩ := transport (equations.iseqv.symm before) step
      exact ⟨result, executed.tail rawStep, equations.iseqv.symm
        (equations.iseqv.trans (coding.representative_equivalent fine displayed) after)⟩

def terminal {A : Type*} (step : A → A → Prop) (state : A) : Prop :=
  ∀ target, ¬ step state target

theorem terminal_iff_of_equivalent (transport : StepTransport equations raw)
    {key : Key} {state : State}
    (same : equations.r (coding.representative key) state) :
    terminal (coding.step raw) key ↔ terminal raw state := by
  constructor
  · intro stop target choice
    obtain ⟨partner, step, _⟩ := transport (equations.iseqv.symm same) choice
    exact stop (coding.encode partner) ⟨partner, step, rfl⟩
  · rintro stop _ ⟨_, step, _⟩
    obtain ⟨target, move, _⟩ := transport same step
    exact stop target move

/-- This is an endpoint theorem, not an equivalence of runs picked
by unrelated priority orders. The run is allowed to choose any edge. -/
theorem terminal_outcomes_iff (fine : coding.FinerThan equations)
    (transport : StepTransport equations raw) (observe : State → Obs)
    (invariant : ∀ ⦃a b⦄, equations.r a b → observe a = observe b)
    (source : State) (answer : Obs) :
    (∃ result, ReflTransGen (coding.step raw) (coding.encode source) result ∧
      terminal (coding.step raw) result ∧ observe (coding.representative result) = answer) ↔
    (∃ target, ReflTransGen raw source target ∧ terminal raw target ∧ observe target = answer) := by
  constructor
  · rintro ⟨result, run, stop, emits⟩
    obtain ⟨target, reached, same⟩ := reaches_raw coding fine transport run
    exact ⟨target, reached, (terminal_iff_of_equivalent coding transport (equations.iseqv.symm same)).mp stop,
      (invariant same).trans emits⟩
  · rintro ⟨target, run, stop, emits⟩
    obtain ⟨result, reached, same⟩ := reaches_representative coding fine transport run
    exact ⟨result, reached, (terminal_iff_of_equivalent coding transport same).mpr stop,
      (invariant same).trans emits⟩

end Reach

namespace Controls

inductive Phase where
  | left
  | right
  | done
  deriving DecidableEq

private def done : Phase → Bool
  | .done => true
  | _ => false

private def phaseEq : Setoid Phase := Setoid.ker done

private def coding : Keys Phase Bool :=
  ⟨done, fun b => if b then .done else .left, by intro b; cases b <;> rfl⟩

private theorem coding_fine : coding.FinerThan phaseEq := by
  intro _ _ same
  exact same

inductive Both : Phase → Phase → Prop where
  | left : Both .left .done
  | right : Both .right .done

private theorem both_transport : StepTransport phaseEq Both := by
  intro source source' target equivalent next
  cases next <;> cases source'
  all_goals try exact ⟨.done, .left, rfl⟩
  all_goals try exact ⟨.done, .right, rfl⟩
  all_goals cases equivalent

theorem different_spellings_can_share_the_same_terminal_answer :
    ∃ key, ReflTransGen (coding.step Both) (coding.encode .right) key ∧
      terminal (coding.step Both) key ∧ done (coding.representative key) = true := by
  apply (terminal_outcomes_iff coding coding_fine both_transport done
    (by intro _ _ same; exact same) .right true).mpr
  refine ⟨.done, .single .right, ?_, rfl⟩
  intro _ impossible
  cases impossible

inductive RightOnly : Phase → Phase → Prop where
  | right : RightOnly .right .done

/-- An exact class key cannot repair a missing representative edge.
This is the risk in substituting a raw spelling sorter for a matcher. -/
theorem fine_key_without_transport_can_lose_a_step :
    coding.FinerThan phaseEq ∧
      RightOnly .right .done ∧ terminal (coding.step RightOnly) (coding.encode .right) := by
  refine ⟨coding_fine, .right, ?_⟩
  rintro _ ⟨_, missing, _⟩
  cases missing

theorem raw_spelling_is_not_a_class_observer :
    ¬ ∃ display : Bool → Phase, ∀ state, display (coding.encode state) = state := by
  rintro ⟨display, exactSpelling⟩
  have wrong : Phase.left = Phase.right := (exactSpelling .left).symm.trans (exactSpelling .right)
  cases wrong

end Controls

#print axioms reaches_representative
#print axioms reaches_raw
#print axioms terminal_outcomes_iff
#print axioms Controls.different_spellings_can_share_the_same_terminal_answer
#print axioms Controls.fine_key_without_transport_can_lose_a_step
#print axioms Controls.raw_spelling_is_not_a_class_observer

end Mettapedia.GSLT.Contracts.RefinedStateExploration
