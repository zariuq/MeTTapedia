import Mettapedia.GSLT.Logic.ResourceFrame
import Mettapedia.GSLT.Causality.ResourceReads

/-!
# Operational controls for separation framing

An extra message can race for a receiver, so a specification of every possible
firing does not frame merely because two bags are separate. A shared equation
or persistent receiver can also enable a call without being consumed: the
complete demand, rather than consumption alone, is the relevant footprint.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Logic.ResourceFrameControls

open Mettapedia.GSLT.Causality.ResourceInteraction
open Mettapedia.GSLT.Causality.ResourceInteraction.Controls
open Mettapedia.GSLT.Logic.ResourceFrame
open Mettapedia.GSLT.SeparationAlgebra

/-- One local message and its receiver. -/
def localMessage : Multiset Res := {Res.message 1, Res.receiver}

/-- Another message, which introduces a race for the same receiver. -/
def competingMessage : Multiset Res := {Res.message 2}

/-- Without the competing message the full resource relation has one outcome. -/
theorem local_receiver_safe :
    SafeTriple linearReceiver (fun _ => True)
      (fun M => M = localMessage) (fun N => N = {Res.received 1}) := by
  intro M equal
  subst M
  have enabled : linearReceiver.Enables localMessage (take 1) := by
    unfold System.Enables localMessage linearReceiver take
    decide
  refine ⟨⟨linearReceiver.fire localMessage (take 1),
    ⟨⟨(), take 1⟩, trivial, enabled, rfl⟩⟩, ?_⟩
  rintro N ⟨⟨site, value⟩, _, permitted, rfl⟩
  cases site
  change ℕ at value
  have messagePresent : Res.message value ∈ localMessage :=
    Multiset.mem_of_le
      (le_trans (Multiset.le_add_right _ _) permitted)
      (by simp [linearReceiver])
  have same : value = (1 : ℕ) := by
    apply Res.message.inj
    simpa [localMessage] using messagePresent
  subst value
  unfold System.fire localMessage linearReceiver
  decide

/-- The known local firing remains possible with a competing message beside it. -/
theorem local_receiver_may_frame :
    MayTriple linearReceiver (fun _ => True)
      (sepConj (fun M => M = localMessage) (fun F => F = competingMessage))
      (sepConj (fun N => N = {Res.received 1}) (fun F => F = competingMessage)) :=
  mayTriple_frame linearReceiver (SafeTriple.may linearReceiver local_receiver_safe)

/-- Bag separation does not justify the demonic frame rule: the new sender
can take the receiver and leave the original message unanswered. -/
theorem local_receiver_not_safe_frame :
    ¬ SafeTriple linearReceiver (fun _ => True)
      (sepConj (fun M => M = localMessage) (fun F => F = competingMessage))
      (sepConj (fun N => N = {Res.received 1}) (fun F => F = competingMessage)) := by
  intro specification
  have pre : sepConj (fun M => M = localMessage) (fun F => F = competingMessage)
      (localMessage + competingMessage) :=
    ⟨localMessage, competingMessage, trivial, rfl, rfl, rfl⟩
  have enabled : linearReceiver.Enables (localMessage + competingMessage) (take 2) := by
    unfold System.Enables localMessage competingMessage linearReceiver take
    decide
  have badStep : selectedStep linearReceiver (fun _ => True)
      (localMessage + competingMessage)
      (linearReceiver.fire (localMessage + competingMessage) (take 2)) :=
    ⟨⟨(), take 2⟩, trivial, enabled, rfl⟩
  obtain ⟨x, y, _, target, rfl, rfl⟩ := (specification _ pre).2 _ badStep
  have different : linearReceiver.fire (localMessage + competingMessage) (take 2) ≠
      ({Res.received 1} : Multiset Res) + competingMessage := by
    unfold System.fire localMessage competingMessage linearReceiver take
    decide
  exact different target

/-- Restricting control to the original instance gives a valid demonic frame
specification, even though the environment contains another sender. -/
theorem selected_receiver_safe_frame :
    SafeTriple linearReceiver (fun candidate => candidate = ⟨(), take 1⟩)
      (sepConj (fun M => M = localMessage) (fun F => F = competingMessage))
      (sepConj (fun N => N = {Res.received 1}) (fun F => F = competingMessage)) := by
  simpa [demand, linearReceiver, localMessage, take] using
    footprint_safeTriple_frame linearReceiver ⟨(), take 1⟩ (fun F => F = competingMessage)

/-- A persistent receiver is disjoint from the consumption but supplies a
missing read. It enables a new firing, invalidating a consumption-only test. -/
theorem consumption_only_misses_read :
    (∀ r ∈ ({Res.receiver} : Multiset Res),
      r ∉ persistentReceiver.consume (takeAgain 1)) ∧
    ¬ persistentReceiver.Enables {Res.message 1} (takeAgain 1) ∧
    persistentReceiver.Enables ({Res.message 1} + {Res.receiver}) (takeAgain 1) ∧
    ¬ NoNewEnabled persistentReceiver (fun candidate => candidate = ⟨(), takeAgain 1⟩)
      {Res.message 1} {Res.receiver} := by
  have missing : ¬ persistentReceiver.Enables {Res.message 1} (takeAgain 1) := by
    unfold System.Enables persistentReceiver takeAgain
    decide
  have supplied : persistentReceiver.Enables ({Res.message 1} + {Res.receiver})
      (takeAgain 1) := by
    unfold System.Enables persistentReceiver takeAgain
    decide
  refine ⟨by simp [persistentReceiver, takeAgain], missing, supplied, ?_⟩
  intro inert
  exact missing (inert ⟨(), takeAgain 1⟩ rfl supplied)

/-- The actual read-bearing footprint retains the persistent receiver. -/
theorem persistent_receiver_footprint :
    SafeTriple persistentReceiver (fun candidate => candidate = ⟨(), takeAgain 1⟩)
      (fun M => M = {Res.message 1, Res.receiver})
      (fun N => N = {Res.receiver, Res.received 1}) := by
  simpa [demand, persistentReceiver, takeAgain] using
    footprint_safeTriple persistentReceiver ⟨(), takeAgain 1⟩

end Mettapedia.GSLT.Logic.ResourceFrameControls
