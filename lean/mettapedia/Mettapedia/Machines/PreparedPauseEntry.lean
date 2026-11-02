import Mettapedia.Machines.ReadOnlyQuery
import Mettapedia.Machines.SourceWordAdmission

/-!
# Pause an optimization inquiry before preparing its operands

Preparation reads metadata without executing source work. The reference
prepares first and then consults the route gate; the target consults that gate
first and omits preparation when ordinary execution was selected. They select
exactly the same invocation or ordinary continuation, including preparation
refusal. Ordinary execution is retained, not replaced by a logical failure.

Read certificates may differ. The source/physical join preserves the complete
contextual state once the selected continuation enters. Countdown and authority
observations below concern optimization hints only; they certify no permanent
program refusal. Native authority construction, allocation, source purity and
C storage remain separate correspondence obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PreparedPauseEntry

open ReadOnlyQuery

variable {Key Value Argument : Type}

inductive Route (Argument : Type) where
  | ordinary
  | prepared (arguments : Argument)
  deriving DecidableEq, Repr

def afterPreparation (gate : Program Key Value Bool)
    (prepare : Program Key Value (Option Argument)) : Program Key Value (Route Argument) :=
  bind prepare fun result => match result with
  | none => .pure .ordinary
  | some argument => map (fun allowed => if allowed then .prepared argument else .ordinary) gate

def beforePreparation (gate : Program Key Value Bool)
    (prepare : Program Key Value (Option Argument)) : Program Key Value (Route Argument) :=
  bind gate fun allowed =>
    if allowed then map (fun result => match result with
      | none => .ordinary
      | some argument => .prepared argument) prepare
    else .pure .ordinary

/-- Both stages are independently interpreted against the same metadata view.
The equality includes the actual selected arguments, not just a success bit. -/
theorem route_refines (store : Key → Value) (gate : Program Key Value Bool)
    (prepare : Program Key Value (Option Argument)) :
    (run store (beforePreparation gate prepare)).answer =
      (run store (afterPreparation gate prepare)).answer := by
  simp only [beforePreparation, afterPreparation, run_bind]
  cases prepared : (run store prepare).answer <;>
    cases allowed : (run store gate).answer <;>
    simp [run, run_map, prepared, allowed]

/-- A paused inquiry reads the gate alone. No argument or source preparation
runs, even when the omitted preparation would itself decline. -/
theorem paused_omits_preparation (store : Key → Value) (gate : Program Key Value Bool)
    (prepare : Program Key Value (Option Argument))
    (paused : (run store gate).answer = false) :
    run store (beforePreparation gate prepare) =
      ⟨.ordinary, (run store gate).reads⟩ := by
  simp [beforePreparation, run_bind, paused, run]

/-- For an eligible inquiry the exact omitted suffix is its preparation
certificate. Gate and preparation reads remain separately visible. -/
theorem paused_read_saving (store : Key → Value) (gate : Program Key Value Bool)
    (prepare : Program Key Value (Option Argument)) (argument : Argument)
    (prepared : (run store prepare).answer = some argument)
    (paused : (run store gate).answer = false) :
    (run store (afterPreparation gate prepare)).reads =
      (run store prepare).reads ++ (run store (beforePreparation gate prepare)).reads := by
  simp [afterPreparation, beforePreparation, run_bind, run_map, run, prepared, paused]

/-- Source and physical budgets attach to the selected computation. Metadata
routing neither pays a source debit nor changes bindings, effects or frames. -/
theorem bounded_continuation_refines
    {Call Effect Fault Delay Suspension Context World Worker : Type}
    (sem : ContextualCBPV.Semantics Value Call Effect Fault Delay Suspension Context World Worker)
    (store : Key → Value) (gate : Program Key Value Bool)
    (prepare : Program Key Value (Option Argument))
    (interpret : Route Argument → ContextualCBPV.Code Value Call Effect Fault Delay Suspension)
    (context : Context) (maximum : Nat) (limit : Option Nat)
    (occurrence : SourceAccounting.Origin) (debit : Nat)
    (state : SourceWordAdmission.Native Value Call Effect Fault Delay Suspension Context World Worker) :
    let enter := fun route => {state with meter := {state.meter with state :=
      {state.meter.state with focus := ⟨.compute context (interpret route), state.meter.state.focus.frames⟩}}}
    SourceWordAdmission.nativeStep sem maximum limit occurrence debit
      (enter (run store (beforePreparation gate prepare)).answer) =
    SourceWordAdmission.nativeStep sem maximum limit occurrence debit
      (enter (run store (afterPreparation gate prepare)).answer) := by
  dsimp only
  rw [route_refines]

/-- The selected target continuation joins the independent source annotation
and physical countdown, including exact refusal at either allowance. -/
theorem bounded_source_join
    {Call Effect Fault Delay Suspension Context World Worker : Type}
    (sem : ContextualCBPV.Semantics Value Call Effect Fault Delay Suspension Context World Worker)
    (store : Key → Value) (gate : Program Key Value Bool)
    (prepare : Program Key Value (Option Argument))
    (interpret : Route Argument → ContextualCBPV.Code Value Call Effect Fault Delay Suspension)
    (context : Context) (maximum : Nat) (limit : Option Nat)
    (occurrence : SourceAccounting.Origin) (debit : Nat)
    (state : SourceWordAdmission.Native Value Call Effect Fault Delay Suspension Context World Worker)
    (inRange : state.meter.state.spent + state.meter.remaining ≤ maximum) :
    let enter := fun route => {state with meter := {state.meter with state :=
      {state.meter.state with focus := ⟨.compute context (interpret route), state.meter.state.focus.frames⟩}}}
    (SourceWordAdmission.nativeStep sem maximum limit occurrence debit
      (enter (run store (beforePreparation gate prepare)).answer)).map
        (ContextualSourceAdmission.decode limit) =
    SourceWordAdmission.referenceStep sem occurrence debit
      (ContextualSourceAdmission.decode limit
        (enter (run store (afterPreparation gate prepare)).answer)) := by
  dsimp only
  rw [route_refines]
  exact SourceWordAdmission.step_refines sem maximum limit occurrence debit _ inRange

structure Hint (Stamp Inquiry : Type) where
  authority : Stamp
  inquiry : Inquiry
  remaining : Nat
  deriving DecidableEq, Repr

/-- All authority and inquiry fields must agree before consuming a hint. -/
def paused {Stamp Inquiry : Type} [DecidableEq Stamp] [DecidableEq Inquiry]
    (authority : Stamp) (inquiry : Inquiry) (hint : Hint Stamp Inquiry) : Bool :=
  decide (hint.authority = authority) && decide (hint.inquiry = inquiry) &&
    decide (0 < hint.remaining)

def consume {Stamp Inquiry : Type} [DecidableEq Stamp] [DecidableEq Inquiry]
    (authority : Stamp) (inquiry : Inquiry) (hint : Hint Stamp Inquiry) :
    Bool × Hint Stamp Inquiry :=
  if paused authority inquiry hint then
    (true, {hint with remaining := hint.remaining - 1})
  else (false, hint)

/-- The reference destructures the countdown only after both stamps match. -/
def referenceConsume {Stamp Inquiry : Type} [DecidableEq Stamp] [DecidableEq Inquiry]
    (authority : Stamp) (inquiry : Inquiry) (hint : Hint Stamp Inquiry) :
    Bool × Hint Stamp Inquiry :=
  if hint.authority = authority ∧ hint.inquiry = inquiry then
    match hint.remaining with
    | 0 => (false, hint)
    | next + 1 => (true, {hint with remaining := next})
  else (false, hint)

theorem consume_refines {Stamp Inquiry : Type} [DecidableEq Stamp] [DecidableEq Inquiry]
    (authority : Stamp) (inquiry : Inquiry) (hint : Hint Stamp Inquiry) :
    consume authority inquiry hint = referenceConsume authority inquiry hint := by
  by_cases sameAuthority : hint.authority = authority <;>
    by_cases sameInquiry : hint.inquiry = inquiry <;>
    cases remaining : hint.remaining <;>
    simp [consume, referenceConsume, paused, sameAuthority, sameInquiry, remaining]

theorem zero_retries {Stamp Inquiry : Type} [DecidableEq Stamp] [DecidableEq Inquiry]
    (authority : Stamp) (inquiry : Inquiry) (hint : Hint Stamp Inquiry)
    (empty : hint.remaining = 0) : (consume authority inquiry hint).1 = false := by
  simp [consume, paused, empty]

theorem stale_never_pauses {Stamp Inquiry : Type} [DecidableEq Stamp] [DecidableEq Inquiry]
    (authority : Stamp) (inquiry : Inquiry) (hint : Hint Stamp Inquiry)
    (stale : hint.authority ≠ authority) : paused authority inquiry hint = false := by
  simp [paused, stale]

theorem different_inquiry_never_pauses {Stamp Inquiry : Type}
    [DecidableEq Stamp] [DecidableEq Inquiry]
    (authority : Stamp) (inquiry : Inquiry) (hint : Hint Stamp Inquiry)
    (different : hint.inquiry ≠ inquiry) : paused authority inquiry hint = false := by
  simp [paused, different]

example : paused 3 (false, true) ⟨3, (false, true), 7⟩ = true := by decide
example : paused 4 (false, true) ⟨3, (false, true), 7⟩ = false := by decide
example : paused 3 (true, true) ⟨3, (false, true), 7⟩ = false := by decide
example : paused 3 (false, false) ⟨3, (false, true), 7⟩ = false := by decide

end Mettapedia.Machines.PreparedPauseEntry

#print axioms Mettapedia.Machines.PreparedPauseEntry.route_refines
#print axioms Mettapedia.Machines.PreparedPauseEntry.paused_omits_preparation
#print axioms Mettapedia.Machines.PreparedPauseEntry.paused_read_saving
#print axioms Mettapedia.Machines.PreparedPauseEntry.bounded_continuation_refines
#print axioms Mettapedia.Machines.PreparedPauseEntry.stale_never_pauses
#print axioms Mettapedia.Machines.PreparedPauseEntry.different_inquiry_never_pauses

#print axioms Mettapedia.Machines.PreparedPauseEntry.consume_refines
#print axioms Mettapedia.Machines.PreparedPauseEntry.zero_retries

#print axioms Mettapedia.Machines.PreparedPauseEntry.bounded_source_join
