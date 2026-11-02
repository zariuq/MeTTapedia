import Mettapedia.GSLT.Parsing.ClassAwareChartDemandExecution

/-! A retained checkpoint for independent chart construction. Advancing a
checkpoint in chunks gives exactly the same state as uninterrupted work.
Coverage is published only after the existing fixed-point check succeeds. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareChartDemand

open ClassAwareParserPackCorrespondence ParserProfileSemantics

def advance (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) (input : List Nat) :
    Nat → State → State
  | 0, state => state
  | rounds + 1, state => advance profile plan input rounds (step profile plan input state)

theorem advance_add (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) (input : List Nat)
    (first second : Nat) (state : State) :
    advance profile plan input (first + second) state =
      advance profile plan input second (advance profile plan input first state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, advance]
  | succ first ih => simpa only [Nat.succ_add, advance] using ih (step profile plan input state)

theorem advance_fixed {profile : ParserProfileLayer} {plan : CompiledParserPackPlan} {input : List Nat}
    {state : State} (fixed : step profile plan input state = state) (rounds : Nat) :
    advance profile plan input rounds state = state := by
  induction rounds with
  | zero => rfl
  | succ rounds ih => simpa only [advance, fixed] using ih

theorem finish?_after_advance {profile : ParserProfileLayer} {plan : CompiledParserPackPlan} {input : List Nat}
    (first second : Nat) (state : State) (result : ClassAwarePackedForest.Forest)
    (finished : finish? profile plan input second (advance profile plan input first state) = some result) :
    finish? profile plan input (first + second) state = some result := by
  induction first generalizing state with
  | zero => simpa only [Nat.zero_add, advance] using finished
  | succ first ih =>
    rw [Nat.succ_add, finish?]
    split
    · rename_i fixed
      have same : step profile plan input state = state := by simpa only [beq_iff_eq] using fixed
      rw [advance_fixed same] at finished
      cases second with
      | zero => cases finished
      | succ second => simpa only [finish?, same, beq_self_eq_true, ↓reduceIte] using finished
    · exact ih (step profile plan input state) finished

end Mettapedia.GSLT.Parsing.ClassAwareChartDemand
