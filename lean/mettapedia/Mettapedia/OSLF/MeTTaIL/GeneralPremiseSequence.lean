import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSemantics

/-! Composition of retained premise sequences preserves their authored
indices and concatenates their actual event histories. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax ScopedRuleMatching

def Context.after (context : Context) : Nat → Context
  | 0 => context
  | count + 1 => context.next.after count

@[simp] theorem Context.after_rule (context : Context) (count : Nat) :
    (context.after count).rule = context.rule := by
  induction count generalizing context with
  | zero => rfl
  | succ count ih => simpa only [after,Context.next] using ih context.next

@[simp] theorem Context.after_spec (context : Context) (count : Nat) :
    (context.after count).spec = context.spec := by
  induction count generalizing context with
  | zero => rfl
  | succ count ih => simpa only [after,Context.next] using ih context.next

@[simp] theorem Context.after_bound (context : Context) (count : Nat) :
    (context.after count).bound = context.bound := by
  induction count generalizing context with
  | zero => rfl
  | succ count ih => simpa only [after,Context.next] using ih context.next

@[simp] theorem Context.after_index (context : Context) (count : Nat) :
    (context.after count).premiseIndex = context.premiseIndex + count := by
  induction count generalizing context with
  | zero => simp [after]
  | succ count ih => simpa only [after,Context.next,Nat.add_assoc,Nat.add_comm 1 count] using ih context.next

theorem Context.after_depth {context : Context} (depth : context.quantifierDepth = 0) (count : Nat) :
    (context.after count).quantifierDepth = 0 := by
  induction count generalizing context with
  | zero => exact depth
  | succ count ih => exact ih (context := context.next) rfl

theorem PremisesHold.append {environment : Environment} {context : Context}
    {first second : List Premise} {initial middle final : Assignment}
    {firstHistory secondHistory : List Event}
    (left : PremisesHold environment context first initial middle firstHistory)
    (right : PremisesHold environment (context.after first.length) second middle final secondHistory) :
    PremisesHold environment context (first ++ second) initial final (firstHistory ++ secondHistory) := by
  induction first generalizing context initial firstHistory with
  | nil => cases left; exact right
  | cons head tail ih =>
    cases left with
    | cons firstHeld restHeld => exact .cons firstHeld (ih restHeld right)

#print axioms PremisesHold.append

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
