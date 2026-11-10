import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Interface

/-! # Budgeted evaluation under a fixed admission profile

An external strategy proposes one attempted candidate at the current state.
Acceptance carries admission evidence; refusal refutes only that candidate.
Unresolved work makes no negative claim. A bounded driver composes actual
admitted firings and stops before consulting the strategy when its budget is
zero. Its budget counts attempts, not machine instructions.

The strategy is a pure function in this model. Observable effects of candidate
discovery must be included in the state or a separate interaction contract.
No completeness, fairness, preferred schedule or enumeration policy is built
into the calculus.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Step.Evaluation

universe uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} (P : Step X O State Firing)

inductive Attempt (state : State) where
  | admitted (firing : Firing state) (permission : P.Admits firing)
  | refused (firing : Firing state) (refutation : ¬ P.Admits firing)
  | unresolved (candidate : Option (Firing state))

inductive Halt (state : State) where
  | refused (firing : Firing state) (refutation : ¬ P.Admits firing)
  | unresolved (candidate : Option (Firing state))
  | budgetExhausted

structure Result (state : State) where
  run : P.Run state
  halt : Halt P run.last

def evaluate (strategy : (state : State) → Attempt P state) :
    Nat → (state : State) → Result P state
  | 0, state => ⟨.nil state, .budgetExhausted⟩
  | fuel + 1, state =>
      match strategy state with
      | .admitted firing permission =>
          let later := evaluate strategy fuel (P.result firing permission)
          ⟨.cons firing permission later.run, later.halt⟩
      | .refused firing refutation => ⟨.nil state, .refused firing refutation⟩
      | .unresolved candidate => ⟨.nil state, .unresolved candidate⟩

theorem zero_budget_keeps_state (strategy : (state : State) → Attempt P state) (state : State) :
    (evaluate P strategy 0 state).run.last = state := rfl

theorem zero_budget_keeps_word (strategy : (state : State) → Attempt P state) (state : State) :
    (evaluate P strategy 0 state).run.word = [] := rfl

theorem zero_budget_does_not_select
    (first second : (state : State) → Attempt P state) (state : State) :
    evaluate P first 0 state = evaluate P second 0 state := rfl

theorem selected_refusal_keeps_state (strategy : (state : State) → Attempt P state)
    (fuel : Nat) (state : State) (firing : Firing state) (refutation : ¬P.Admits firing)
    (selected : strategy state = .refused firing refutation) :
    (evaluate P strategy (fuel + 1) state).run = .nil state := by
  simp [evaluate, selected]

theorem unresolved_keeps_state (strategy : (state : State) → Attempt P state)
    (fuel : Nat) (state : State) (candidate : Option (Firing state))
    (selected : strategy state = .unresolved candidate) :
    (evaluate P strategy (fuel + 1) state).run = .nil state := by
  simp [evaluate, selected]

theorem length_le_budget (strategy : (state : State) → Attempt P state) :
    ∀ fuel state, (evaluate P strategy fuel state).run.word.length ≤ fuel
  | 0, _ => Nat.le_refl 0
  | fuel + 1, state => by
      cases selected : strategy state with
      | admitted firing permission =>
          simpa only [evaluate, selected, Run.word, List.length_cons] using
            Nat.succ_le_succ (length_le_budget strategy fuel (P.result firing permission))
      | refused firing refutation => simp [evaluate, selected, Run.word]
      | unresolved candidate => simp [evaluate, selected, Run.word]

/-- Every event in an actual execution retains its own admission evidence. -/
theorem run_word_admitted : ∀ {state : State} (run : P.Run state)
    (entry : (s : State) × Firing s), entry ∈ run.word → P.Admits entry.2
  | _, .nil _, _, member => by simp [Run.word] at member
  | _, .cons firing admitted rest, entry, member => by
      rcases List.mem_cons.mp member with rfl | later
      · exact admitted
      · exact run_word_admitted rest entry later

theorem evaluator_cannot_bypass (strategy : (state : State) → Attempt P state)
    (fuel : Nat) (state : State) (entry : (s : State) × Firing s)
    (executed : entry ∈ (evaluate P strategy fuel state).run.word) : P.Admits entry.2 :=
  run_word_admitted P _ entry executed

theorem evaluation_refines (strategy : (state : State) → Attempt P state)
    (fuel : Nat) (state : State) {b : Obj}
    (solution : Hom (P.frame (evaluate P strategy fuel state).run.last) b)
    (solved : X.Models solution (P.knowledge (evaluate P strategy fuel state).run.last)) :
    X.Models (X.comp solution (evaluate P strategy fuel state).run.toLast) (P.knowledge state) :=
  (evaluate P strategy fuel state).run.models_start solution solved

theorem unresolved_is_not_refusal (state : State) (candidate : Option (Firing state))
    (firing : Firing state) (refutation : ¬P.Admits firing) :
    Halt.unresolved candidate ≠ (Halt.refused firing refutation : Halt P state) := by
  intro impossible
  cases impossible

theorem budget_is_not_refusal (state : State) (firing : Firing state)
    (refutation : ¬P.Admits firing) :
    Halt.budgetExhausted ≠ (Halt.refused firing refutation : Halt P state) := by
  intro impossible
  cases impossible

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Step.Evaluation
