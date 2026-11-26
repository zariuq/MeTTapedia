import Mettapedia.GSLT.Distinction.ProductiveBlocks

namespace Mettapedia.GSLT.Distinction.ProductiveBlocks.Machine

/-- Agreement on an invariant region gives equal finite runs, including the
ordered events and the exact terminal, suspended, or exhausted outcome. Only
silent and publishing steps need to stay in the region, since a run stops at
an external call and retains its saved continuation. -/
theorem run_eq_of_step_eq_on {State Event Verdict Request : Type}
    {first second : Machine State Event Verdict Request} {region : State → Prop}
    (agrees : ∀ state, region state → first.step state = second.step state)
    (silent : ∀ {before after}, region before →
      second.step before = some (.silent after) → region after)
    (publish : ∀ {before after events}, region before →
      second.step before = some (.publish events after) → region after)
    (fuel : Nat) (state : State) (inside : region state) :
    first.run fuel state = second.run fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      rw [Machine.run, Machine.run, agrees state inside]
      cases stepped : second.step state with
      | none => rfl
      | some transition =>
          cases transition with
          | silent after => exact ih after (silent inside stepped)
          | publish _ after => simp only [ih after (publish inside stepped)]
          | finish _ => rfl
          | fail _ => rfl
          | call _ _ => rfl

end Mettapedia.GSLT.Distinction.ProductiveBlocks.Machine
