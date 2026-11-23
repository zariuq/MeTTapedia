import MeTTaIL.Semantics.Eval

/-! Guarded simulation for the deterministic fuel-bounded evaluator. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GuardedEvaluation

open MeTTaIL

/-- Simulate the prefix that takes actual steps. Its length is bounded by the
source fuel. The target agrees at every index within that prefix. -/
theorem eval_prefix
    (source target : Presentation) (wrap : AST → AST) (guard : AST → Prop)
    (step : ∀ s t, guard s → oneStep source s = some t →
      oneStep target (wrap s) = some (wrap t))
    (fuel : Nat) (state : AST)
    (active : ∀ k, k < fuel → guard (eval source k state)) :
    ∃ used, used ≤ fuel ∧ eval source used state = eval source fuel state ∧
      (∀ k, k ≤ used → eval target k (wrap state) = wrap (eval source k state)) ∧
      (∀ k, k < used → ∃ next, oneStep source (eval source k state) = some next) ∧
      (used < fuel → oneStep source (eval source used state) = none) := by
  induction fuel generalizing state with
  | zero =>
      refine ⟨0, Nat.le_refl 0, rfl, ?_, ?_, ?_⟩
      · intro k bounded
        obtain rfl := Nat.eq_zero_of_le_zero bounded
        rfl
      · intro k before
        exact (Nat.not_lt_zero k before).elim
      · intro before
        exact (Nat.lt_irrefl 0 before).elim
  | succ fuel ih =>
      cases sourceStep : oneStep source state with
      | none =>
          refine ⟨0, Nat.zero_le _, by simp only [eval, sourceStep], ?_, ?_, ?_⟩
          · intro k bounded
            obtain rfl := Nat.eq_zero_of_le_zero bounded
            rfl
          · intro k before
            exact (Nat.not_lt_zero k before).elim
          · intro _
            exact sourceStep
      | some next =>
          have targetStep := step state next (active 0 (Nat.zero_lt_succ fuel)) sourceStep
          have nextActive : ∀ k, k < fuel → guard (eval source k next) := by
            intro k bounded
            simpa only [eval, sourceStep] using active (k + 1) (Nat.succ_lt_succ bounded)
          obtain ⟨used, budget, final, follows, progresses, stops⟩ := ih next nextActive
          refine ⟨used + 1, Nat.succ_le_succ budget, ?_, ?_, ?_, ?_⟩
          · simpa only [eval, sourceStep] using final
          · intro k bounded
            cases k with
            | zero => rfl
            | succ k =>
                simpa only [eval, sourceStep, targetStep] using
                  follows k (Nat.le_of_succ_le_succ bounded)
          · intro k before
            cases k with
            | zero => exact ⟨next, sourceStep⟩
            | succ k => simpa only [eval, sourceStep] using
                progresses k (Nat.lt_of_succ_lt_succ before)
          · intro before
            simpa only [eval, sourceStep] using stops (Nat.lt_of_succ_lt_succ before)

/-- A guard preserved by the wrapping map holds at each proper target prefix. -/
theorem eval_with_guard
    (source target : Presentation) (wrap : AST → AST)
    (sourceGuard targetGuard : AST → Prop)
    (guard : ∀ s, sourceGuard s → targetGuard (wrap s))
    (step : ∀ s t, sourceGuard s → oneStep source s = some t →
      oneStep target (wrap s) = some (wrap t))
    (fuel : Nat) {state value : AST} (evaluated : eval source fuel state = value)
    (active : ∀ k, k < fuel → sourceGuard (eval source k state)) :
    ∃ used, eval target used (wrap state) = wrap value ∧
      ∀ k, k < used → targetGuard (eval target k (wrap state)) := by
  obtain ⟨used, budget, final, follows, _, _⟩ :=
    eval_prefix source target wrap sourceGuard step fuel state active
  refine ⟨used, ?_, ?_⟩
  · rw [follows used (Nat.le_refl used), final, evaluated]
  · intro k bounded
    rw [follows k (Nat.le_of_lt bounded)]
    exact guard _ (active k (Nat.lt_of_lt_of_le bounded budget))

/-- Read the terminal result from a simulated prefix. -/
theorem eval_result
    (source target : Presentation) (wrap : AST → AST) (guard : AST → Prop)
    (step : ∀ s t, guard s → oneStep source s = some t →
      oneStep target (wrap s) = some (wrap t))
    (fuel : Nat) {state value : AST} (evaluated : eval source fuel state = value)
    (active : ∀ k, k < fuel → guard (eval source k state)) :
    ∃ used, eval target used (wrap state) = wrap value := by
  obtain ⟨used, _, final, follows, _, _⟩ :=
    eval_prefix source target wrap guard step fuel state active
  exact ⟨used, (follows used (Nat.le_refl used)).trans (congrArg wrap (final.trans evaluated))⟩

/-- Read the terminal result when the wrapping map transports every source step. -/
theorem eval_result_of_step
    (source target : Presentation) (wrap : AST → AST)
    (step : ∀ s t, oneStep source s = some t →
      oneStep target (wrap s) = some (wrap t))
    (fuel : Nat) {state value : AST} (evaluated : eval source fuel state = value) :
    ∃ used, eval target used (wrap state) = wrap value :=
  eval_result source target wrap
    (fun s => ∀ t, oneStep source s = some t → oneStep target (wrap s) = some (wrap t))
    (fun _ t transports next => transports t next) fuel evaluated (fun _ _ => step _)

/-- A wrapper with a guarded image supplies the guard at every simulated step. -/
theorem eval_with_wrapper
    (source target : Presentation) (wrap : AST → AST) (guard : AST → Prop)
    (inside : ∀ s, guard (wrap s))
    (step : ∀ s t, oneStep source s = some t →
      oneStep target (wrap s) = some (wrap t))
    (fuel : Nat) {state value : AST} (evaluated : eval source fuel state = value) :
    ∃ used, eval target used (wrap state) = wrap value ∧
      ∀ k, k < used → guard (eval target k (wrap state)) :=
  eval_with_guard source target wrap (fun s => guard (wrap s)) guard
    (fun _ allowed => allowed) (fun s t _ => step s t)
    fuel evaluated (fun _ _ => inside _)

/-- Joining two guarded runs preserves the guard at every proper prefix. -/
theorem eval_guard_append (p : Presentation) {guard : AST → Prop}
    {first second : Nat} {state mid : AST}
    (reached : eval p first state = mid)
    (prefixGuard : ∀ k, k < first → guard (eval p k state))
    (suffixGuard : ∀ k, k < second → guard (eval p k mid)) :
    ∀ k, k < first + second → guard (eval p k state) := by
  intro k beforeEnd
  by_cases beforeSplit : k < first
  · exact prefixGuard k beforeSplit
  · have afterSplit := Nat.le_of_not_gt beforeSplit
    have withinSuffix := (Nat.sub_lt_iff_lt_add afterSplit).mpr
      (Nat.add_comm first second ▸ beforeEnd)
    have position := Nat.add_sub_of_le afterSplit
    rw [← position, eval_add, reached]
    exact suffixGuard _ withinSuffix

/-- A step invariant holds at every evaluation index, including a halted run. -/
theorem eval_invariant (p : Presentation) (invariant : AST → Prop)
    (preserves : ∀ s t, invariant s → oneStep p s = some t → invariant t)
    {state : AST} (start : invariant state) (fuel : Nat) :
    invariant (eval p fuel state) := by
  induction fuel generalizing state with
  | zero => exact start
  | succ fuel ih =>
      cases nextStep : oneStep p state with
      | none => simpa only [eval, nextStep] using start
      | some next =>
          simpa only [eval, nextStep] using ih (preserves state next start nextStep)

private def symbol (name : String) : AST := .sexp (.id name) []

private def stopped : Presentation := .mk [] [] [] [] []

private def advancing : Presentation :=
  .mk [] [] []
    [{ name := "advance", rw := .base (symbol "before") (symbol "after") }] []

example : eval advancing 1 (symbol "before") = symbol "after" := by rfl

/-- A target can keep stepping after the source has stopped. -/
example : (eval advancing 1 (symbol "before") == eval stopped 1 (symbol "before")) =
    false := by rfl

end Mettapedia.GSLT.LanguageDef.GuardedEvaluation
