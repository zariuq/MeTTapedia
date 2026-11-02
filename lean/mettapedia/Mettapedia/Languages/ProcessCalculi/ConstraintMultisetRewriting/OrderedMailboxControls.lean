import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OrderedMailboxOccurrence

/-!
# Controls for ordered-state mailbox firings

The positive cases construct ordinary occurrence firings, including repeated
receives. The negative cases retain the source order obstruction, reject an
incorrect residual, and distinguish a missing occurrence from a newly made
occurrence containing the same queue value.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OrderedMailboxControls

open Mettapedia.Languages.Erlang
open OrderedMailboxComputation OrderedMailboxOccurrence

def acceptTwo (message : Nat) : Option Nat := if message = 2 then some message else none

def queue (messages : List Nat) : Occurrence Nat Nat := (0, .queue messages)

def initial (messages : List Nat) : Configuration (Cell Nat Nat) (Occurrence Nat Nat) :=
  ⟨[], {queue messages}⟩

theorem initial_consistent (messages : List Nat) :
    closedAction.Consistent (initial messages).equations :=
  ⟨(), closedAction.models_nil ()⟩

theorem initial_unique_queue (messages : List Nat) :
    QueueState (initial messages).present (queue messages) messages := by
  refine ⟨by simp [initial], rfl, ?_⟩
  intro occurrence present _ _
  simpa [initial] using present

theorem skipped_prefix_and_duplicate_actual_firing :
    ∃ after, Fires acceptTwo (initial [0, 1, 2, 2, 3]) (queue [0, 1, 2, 2, 3])
      2 [0, 1, 2, 3] after :=
  source_has_firing acceptTwo _ _ _ _ _ (by simp [initial]) rfl
    (initial_consistent _) rfl

theorem successive_receives_keep_the_same_prefix :
    ∃ middle nextQueue after,
      Fires acceptTwo (initial [0, 1, 2, 2, 3]) (queue [0, 1, 2, 2, 3])
        2 [0, 1, 2, 3] middle ∧
      label nextQueue = .queue [0, 1, 2, 3] ∧
      Fires acceptTwo middle nextQueue 2 [0, 1, 3] after := by
  obtain ⟨middle, first⟩ := skipped_prefix_and_duplicate_actual_firing
  obtain ⟨nextQueue, after, atQueue, second⟩ := first.continue acceptTwo 2 [0, 1, 3] rfl
  exact ⟨middle, nextQueue, after, first, atQueue, second⟩

theorem queue_uniqueness_survives_the_receive :
    ∃ after nextQueue,
      Fires acceptTwo (initial [0, 1, 2, 2, 3]) (queue [0, 1, 2, 2, 3])
        2 [0, 1, 2, 3] after ∧
      QueueState after.present nextQueue [0, 1, 2, 3] := by
  obtain ⟨after, firing⟩ := skipped_prefix_and_duplicate_actual_firing
  obtain ⟨nextQueue, nextState⟩ := firing.preserves_unique_queue (initial_unique_queue _)
  exact ⟨after, nextQueue, firing, nextState⟩

/-- Removing both equal matching messages would be an incorrect receive. -/
theorem dropping_the_second_duplicate_is_rejected
    (after : Configuration (Cell Nat Nat) (Occurrence Nat Nat)) :
    ¬ Fires acceptTwo (initial [0, 1, 2, 2, 3]) (queue [0, 1, 2, 2, 3])
      2 [0, 1, 3] after := by
  intro firing
  have source := (source_iff_firing acceptTwo _ _ _ 2 [0, 1, 3]
    (by simp [initial]) rfl (initial_consistent _)).mpr ⟨after, firing⟩
  simp [Mailbox.selectFirst, acceptTwo] at source

theorem unmatched_queue_has_no_receive (result : Nat) (remaining : List Nat)
    (after : Configuration (Cell Nat Nat) (Occurrence Nat Nat)) :
    ¬ Fires acceptTwo (initial [0, 1]) (queue [0, 1]) result remaining after := by
  apply no_match_no_firing acceptTwo _ _ _ [0, 1] _ _ rfl
  intro message member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

def replacementQueue : Occurrence Nat Nat := (1, .queue [2])

def replaced : Configuration (Cell Nat Nat) (Occurrence Nat Nat) :=
  ⟨[], {replacementQueue}⟩

/-- Equal queue payloads do not make a stale physical token current. -/
theorem stale_identity_rejected_same_payload_accepted :
    label (queue [2]) = label replacementQueue ∧
      (∀ result remaining after, ¬ Fires acceptTwo replaced (queue [2]) result remaining after) ∧
      ∃ after, Fires acceptTwo replaced replacementQueue 2 [] after := by
  refine ⟨rfl, ?_, ?_⟩
  · intro result remaining after
    apply no_stale_firing
    decide +kernel
  · apply source_has_firing acceptTwo replaced replacementQueue [2] 2 []
    · simp [replaced]
    · rfl
    · exact ⟨(), closedAction.models_nil ()⟩
    · rfl

/-- Bag equality does not identify the explicitly ordered queue cells. -/
theorem same_message_bag_different_queue_state :
    ([0, 1] : Multiset Nat) = [1, 0] ∧
      (Cell.queue [0, 1] : Cell Nat Nat) ≠ .queue [1, 0] ∧
      compute (fun message : Nat => some message) [0, 1] ≠
        compute (fun message : Nat => some message) [1, 0] := by
  decide +kernel

/-- The extra order-bearing cell is essential. An unordered bag of messages
alone cannot implement the source receive contract. -/
theorem no_bag_only_receive :
    ¬ ∃ receive : Multiset Nat → Option (Nat × List Nat),
      ∀ messages : List Nat, receive (messages : Multiset Nat) =
        Mailbox.selectFirst (fun message => some message) messages := by
  apply Mailbox.no_perm_invariant_receive (fun messages : List Nat => (messages : Multiset Nat))
    (fun _ _ permutation => Quot.sound permutation)
    (first := 0) (second := 1) (left := 0) (right := 1) rfl rfl
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OrderedMailboxControls
