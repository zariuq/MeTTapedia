import Mettapedia.Languages.Erlang.MailboxSelection

/-! Ordered point-to-point channels for the local Erlang machine. A network
is a finite sequence of envelopes. Its sequence records send order, but a
delivery may select any envelope with no earlier envelope on the same
sender/receiver channel. Thus independent channels may overtake one another;
messages on a single channel may not. Delivery and receive are separate.

The declaration of delivery does not call the executable index selector.
The equivalence below checks that selector against the declaration. Process
evaluation, pid allocation and the complete configuration are separate. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Erlang

structure ChannelKey where
  sender : Nat
  receiver : Nat
  deriving Repr, DecidableEq, BEq

structure Envelope (α : Type*) where
  key : ChannelKey
  payload : α
  deriving Repr, DecidableEq, BEq

namespace Network

variable {α : Type*}

def channel (key : ChannelKey) (network : List (Envelope α)) : List α :=
  network.filterMap fun message => if message.key = key then some message.payload else none

def send (message : Envelope α) (network : List (Envelope α)) : List (Envelope α) :=
  network ++ [message]

/-- A delivery removes one occurrence, and only the first occurrence on its
point-to-point channel. The receiver's mailbox is updated by the scheduler. -/
inductive Delivers : List (Envelope α) → Envelope α → List (Envelope α) → Prop where
  | take (before after : List (Envelope α)) (message : Envelope α)
      (first : ∀ earlier ∈ before, earlier.key ≠ message.key) :
      Delivers (before ++ message :: after) message (before ++ after)

def deliverAt? (index : Nat) (network : List (Envelope α)) :
    Option (Envelope α × List (Envelope α)) :=
  match network.drop index with
  | [] => none
  | message :: after =>
      if (network.take index).any (fun earlier => decide (earlier.key = message.key)) then none
      else some (message, network.take index ++ after)

theorem deliverAt_prefix_nil (before : List (Envelope α)) (index : Nat) :
    deliverAt? (before.length + index) before = none := by
  have empty : before.drop (before.length + index) = [] := List.drop_eq_nil_of_le (by omega)
  simp only [deliverAt?, empty]

theorem deliverAt_prefix_zero (before : List (Envelope α)) (message : Envelope α) (after : List (Envelope α)) :
    deliverAt? before.length (before ++ message :: after) =
      if before.any (fun earlier => decide (earlier.key = message.key)) then none
      else some (message, before ++ after) := by
  simp [deliverAt?]

theorem deliverAt_prefix_succ (before : List (Envelope α)) (message : Envelope α) (after : List (Envelope α)) (index : Nat) :
    deliverAt? (before.length + (index + 1)) (before ++ message :: after) =
      deliverAt? ((before ++ [message]).length + index) ((before ++ [message]) ++ after) := by
  have offset : (before ++ [message]).length + index = before.length + (index + 1) := by simp; omega
  rw [offset]
  simp only [List.append_assoc, List.singleton_append]

theorem channel_append (key : ChannelKey) (first second : List (Envelope α)) :
    channel key (first ++ second) = channel key first ++ channel key second := by
  simp [channel]

theorem channel_send (key : ChannelKey) (message : Envelope α) (network : List (Envelope α)) :
    channel key (send message network) =
      channel key network ++ if message.key = key then [message.payload] else [] := by
  by_cases equal : message.key = key <;> simp [send, channel, equal]

theorem channel_empty_iff (key : ChannelKey) (network : List (Envelope α)) :
    channel key network = [] ↔ ∀ message ∈ network, message.key ≠ key := by
  induction network with
  | nil => simp [channel]
  | cons message rest _ =>
      by_cases equal : message.key = key
      · simp [channel, equal]
      · simp [channel, equal]

theorem deliverAt_sound {index : Nat} {network rest : List (Envelope α)} {message : Envelope α}
    (selected : deliverAt? index network = some (message, rest)) :
    Delivers network message rest := by
  unfold deliverAt? at selected
  cases suffix : network.drop index with
  | nil => simp [suffix] at selected
  | cons head tail =>
      simp only [suffix] at selected
      by_cases earlier : (network.take index).any (fun other => decide (other.key = head.key)) = true
      · simp only [earlier, if_true, reduceCtorEq] at selected
      · rw [if_neg earlier] at selected
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj selected)
        have apart : ∀ other ∈ network.take index, other.key ≠ head.key := by
          simpa only [Bool.not_eq_true, List.any_eq_false, decide_eq_true_eq] using earlier
        have shape : network = network.take index ++ head :: tail := by
          rw [← suffix, List.take_append_drop]
        have delivered := Delivers.take (network.take index) tail head apart
        rw [← shape] at delivered
        exact delivered

theorem deliverAt_complete {network rest : List (Envelope α)} {message : Envelope α}
    (delivered : Delivers network message rest) :
    ∃ index, deliverAt? index network = some (message, rest) := by
  cases delivered with
  | take before after message first =>
      refine ⟨before.length, ?_⟩
      have absent : before.any (fun earlier => decide (earlier.key = message.key)) = false := by
        simpa only [List.any_eq_false, decide_eq_true_eq] using first
      simp [deliverAt?, absent]

theorem delivers_iff_index {network rest : List (Envelope α)} {message : Envelope α} :
    Delivers network message rest ↔ ∃ index, deliverAt? index network = some (message, rest) :=
  ⟨deliverAt_complete, fun ⟨_, selected⟩ => deliverAt_sound selected⟩

/-- No later message on the selected channel can be delivered first. -/
theorem delivered_channel_head {network rest : List (Envelope α)} {message : Envelope α}
    (delivered : Delivers network message rest) :
    channel message.key network = message.payload :: channel message.key rest := by
  cases delivered with
  | take before after message first =>
      have empty := (channel_empty_iff message.key before).mpr first
      rw [channel_append, channel_append, empty]
      simp [channel]

/-- Delivering on one channel cannot remove an occurrence from another. -/
theorem delivered_other_channel {network rest : List (Envelope α)} {message : Envelope α}
    (delivered : Delivers network message rest) (key : ChannelKey) (apart : message.key ≠ key) :
    channel key network = channel key rest := by
  cases delivered with
  | take before after message first => simp [channel, apart]

theorem delivery_conserves_occurrences {network rest : List (Envelope α)} {message : Envelope α}
    (delivered : Delivers network message rest) : rest.length + 1 = network.length := by
  cases delivered
  simp only [List.length_append, List.length_cons]
  omega

/-- The target channel's queue and the receiver's ordered mailbox describe
one and the same transfer. In particular, delivery does not select a receive
clause or consume an unmatched mailbox prefix. -/
theorem delivery_mailbox {network rest : List (Envelope α)} {message : Envelope α}
    (delivered : Delivers network message rest) (mailbox : Mailbox α) :
    channel message.key network = message.payload :: channel message.key rest ∧
      (mailbox.deliver message.payload).contents = mailbox.contents ++ [message.payload] :=
  ⟨delivered_channel_head delivered, Mailbox.contents_deliver _ _⟩

end Network
end Mettapedia.Languages.Erlang
