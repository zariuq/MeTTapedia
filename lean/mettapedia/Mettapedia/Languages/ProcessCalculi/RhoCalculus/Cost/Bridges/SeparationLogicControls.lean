import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Bridges.SeparationLogic

/-!
# Funded rho controls for separation specifications

One sealed receiver/sender pair and its purse form a complete local footprint.
An added pair can contend for that same purse. The local firing remains
possible, while the contender gives another actual `CostStep` with a different
endpoint. Equal additional purses remain separate occurrences and are retained
when the original selected event is fired.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Bridges.SeparationLogicControls

open Mettapedia.GSLT.Causality.ResourceInteraction
open Mettapedia.GSLT.Logic.ResourceFrame
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.PaidControls
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Bridges.SeparationLogic

/-- The first and second meetings choose the same one-cell purse. -/
def firstEntry : (costResourceSystem ℕ).Entry := ⟨channel, paid first []⟩

def secondEntry : (costResourceSystem ℕ).Entry := ⟨channel, paid second []⟩

/-- The actual first local communication and its one-cell purse. -/
def localSource : CostConfig ℕ := (CostResourceWave.event firstEntry).consumed

/-- An additional sealed communication, without an additional purse. -/
def competingFrame : CostConfig ℕ := {endpointsOf second}

/-- One additional purse with exactly the same value as the selected purse. -/
def duplicatePurseFrame : CostConfig ℕ := {purseTerm (channel, [stamp])}

/-- A nonempty frame containing no communication endpoint or purse. -/
def inertTerm : CostTerm ℕ := .signed .nil {99}

def inertFrame : CostConfig ℕ := {inertTerm}

/-- No funded event consumes the inert process, whatever its funding choices. -/
theorem inert_not_consumed (event : CostedEvent ℕ) : inertTerm ∉ event.consumed := by
  rw [CostedEvent.consumed, Multiset.mem_add]
  rintro (endpoint | purse)
  · cases event <;> simp [CostedEvent.endpoints, inertTerm] at endpoint
  · rw [event.fundingBefore_eq_map] at purse
    obtain ⟨chosen, _, equal⟩ := Multiset.mem_map.mp purse
    change CostTerm.purse chosen.1 (CostStack.ofList chosen.2) = .signed .nil {99} at equal
    cases equal

/-- This nonempty frame is inert at every state, hence at all actual prefixes. -/
theorem inert_no_new (owned : CostConfig ℕ) :
    NoNewEnabled (costResourceSystem ℕ) (fun _ => True) owned inertFrame := by
  apply noNewEnabled_of_apart _ owned inertFrame
  intro entry _ resource member
  have same : resource = inertTerm := Multiset.mem_singleton.mp member
  subst resource
  rw [demand, costResourceSystem_consume, costResourceSystem_read, add_zero]
  change inertTerm ∉ (CostResourceWave.event entry).consumed
  exact inert_not_consumed (CostResourceWave.event entry)

theorem local_source_exact :
    localSource = {endpointsOf first, purseTerm (channel, [stamp])} := by decide

theorem local_target_exact :
    (CostResourceWave.event firstEntry).produced = {first, purseTerm (channel, [])} := by decide

/-- The first actual funded communication remains available in the presence
of a contender, with its own debit and endpoint. -/
theorem actual_first_frames :
    CostStep (localSource + competingFrame) channel stamp
      ((CostResourceWave.event firstEntry).produced + competingFrame) := by
  have localStep := (CostResourceWave.event firstEntry).toCostStepIn 0
  simp only [zero_add] at localStep
  exact costStep_add_frame localStep competingFrame

/-- Another equal purse is retained as an occurrence after the chosen event. -/
theorem duplicate_purse_retained :
    CostStep (localSource + duplicatePurseFrame) channel stamp
      ({first, purseTerm (channel, [])} + duplicatePurseFrame) := by
  have localStep := (CostResourceWave.event firstEntry).toCostStepIn 0
  simp only [zero_add] at localStep
  rw [← local_target_exact]
  exact costStep_add_frame localStep duplicatePurseFrame

/-- The separating precondition permits the local footprint beside the
contender. It imposes no operational noninterference condition. -/
theorem competing_separating_pre :
    sepConj (fun owned => owned = localSource) (fun extension => extension = competingFrame)
      (localSource + competingFrame) :=
  ⟨localSource, competingFrame, trivial, rfl, rfl, rfl⟩

/-- The additional endpoints enable an event that was absent locally. -/
theorem contender_newly_enabled :
    ¬ (costResourceSystem ℕ).Enables localSource secondEntry.2 ∧
      (costResourceSystem ℕ).Enables (localSource + competingFrame) secondEntry.2 := by
  constructor <;> unfold System.Enables <;> decide

/-- The operational side condition of the demonic frame theorem fails. -/
theorem contender_not_inert :
    ¬ NoNewEnabled (costResourceSystem ℕ) (fun _ => True) localSource competingFrame := by
  intro inert
  exact contender_newly_enabled.1 (inert secondEntry trivial contender_newly_enabled.2)

/-- The alternative is an ordinary funded rho transition, not merely an
event in a separate scheduling model. -/
theorem actual_contender_fires :
    CostStep (localSource + competingFrame) channel stamp
      ((costResourceSystem ℕ).fire (localSource + competingFrame) secondEntry.2) :=
  CostResourceWave.enabled_costStep _ secondEntry contender_newly_enabled.2

/-- The contender's actual endpoint violates the framed first-event
postcondition. Existential preservation cannot imply all-schedule correctness. -/
theorem actual_contender_violates_post :
    ¬ sepConj (fun owned => owned = (CostResourceWave.event firstEntry).produced)
      (fun extension => extension = competingFrame)
      ((costResourceSystem ℕ).fire (localSource + competingFrame) secondEntry.2) := by
  rintro ⟨owned, extension, _, target, rfl, rfl⟩
  have different : (costResourceSystem ℕ).fire (localSource + competingFrame) secondEntry.2 ≠
      (CostResourceWave.event firstEntry).produced + competingFrame := by
    unfold System.fire
    decide
  exact different target

/-- A location and a debit alone do not identify a firing: the two actual
steps have the same payment labels and different resulting configurations. -/
theorem same_payment_different_endpoints :
    CostStep (localSource + competingFrame) channel stamp
      ((CostResourceWave.event firstEntry).produced + competingFrame) ∧
    CostStep (localSource + competingFrame) channel stamp
      ((costResourceSystem ℕ).fire (localSource + competingFrame) secondEntry.2) ∧
    (CostResourceWave.event firstEntry).produced + competingFrame ≠
      (costResourceSystem ℕ).fire (localSource + competingFrame) secondEntry.2 := by
  refine ⟨actual_first_frames, actual_contender_fires, ?_⟩
  unfold System.fire
  decide

/-- Once the contested cell pays for the first event, it cannot pay the
contender. This is actual resource conflict rather than a channel-name test. -/
theorem actual_contender_disabled_after_first :
    ¬ (costResourceSystem ℕ).Enables
      ((costResourceSystem ℕ).fire (localSource + competingFrame) firstEntry.2) secondEntry.2 := by
  unfold System.Enables System.fire
  decide

/-- Exact trace reflection has a real nonempty-frame instance. The given
trace may use arbitrary schedules and labels; its supplied endpoint is retained. -/
theorem actual_trace_reflects_inert_frame
    {labels : List (CostName ℕ × CostSig ℕ)} {actualTarget : CostConfig ℕ}
    (trace : CostTrace (localSource + inertFrame) labels actualTarget) :
    ∃ ownedTarget, CostTrace localSource labels ownedTarget ∧
      actualTarget = ownedTarget + inertFrame :=
  costTrace_reflect_frame inertFrame (fun _ owned _ => inert_no_new owned) trace

/-- The one-step actual trace satisfies that nonempty-frame reflection
contract, including its original payment label. -/
theorem positive_framed_trace :
    CostTrace (localSource + inertFrame) [(channel, stamp)]
      ((CostResourceWave.event firstEntry).produced + inertFrame) := by
  have localStep := (CostResourceWave.event firstEntry).toCostStepIn 0
  simp only [zero_add] at localStep
  exact CostTrace.cons (costStep_add_frame localStep inertFrame) (CostTrace.nil _)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Bridges.SeparationLogicControls
