import Mathlib.Tactic

/-!
# A chat channel's spool between its service and the loop

An IRC or Mattermost channel has a service process of its own, which records
each message it admits into an inbox, one file a message. The loop reads the
inbox at each turn: a message whose identity the ledger already committed is
dropped unread, the rest are presented. The turn commits the identities it
presented, and only then are the presented messages removed from the inbox.

Invariants proved here:
* no message is lost: every message that arrived is in the inbox or committed,
  whatever the order of arrivals, reads, commits and settlements;
* a committed message is never presented again;
* a settlement before the commit removes nothing;
* settling after the commit leaves no presented message in the inbox.

The counterexample is the adapter this replaces for IRC: one slot that each
arrival overwrites. Two messages arriving between two reads lose the first.

This is an abstract contract, not a refinement proof of
`channels/chat_spool.metta`.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.ChatSpoolDelivery

/-- Delivery identities. -/
abbrev Msg := ℕ

/-- The inbox (oldest first), the identities the ledger committed, and what the
last read presented. -/
structure Spool where
  inbox : List Msg
  committed : List Msg
  presented : List Msg

/-- The service records a message. -/
def arrive (s : Spool) (m : Msg) : Spool := { s with inbox := s.inbox ++ [m] }

/-- The loop reads: committed messages are dropped unread, the rest presented. -/
def receive (s : Spool) : Spool :=
  let pending := s.inbox.filter (fun m => !s.committed.contains m)
  { s with inbox := pending, presented := pending }

/-- The turn that read the messages commits their identities. -/
def commit (s : Spool) : Spool := { s with committed := s.committed ++ s.presented }

/-- Settlement: once every presented identity is committed, the presented
messages leave the inbox. -/
def ack (s : Spool) : Spool :=
  if s.presented.all (fun m => s.committed.contains m) then
    { s with inbox := s.inbox.filter (fun m => !s.presented.contains m), presented := [] }
  else s

/-- A message is accounted for while it is in the inbox or committed. -/
def Accounted (s : Spool) (m : Msg) : Prop := m ∈ s.inbox ∨ m ∈ s.committed

theorem arrive_accounts (s : Spool) (m : Msg) : Accounted (arrive s m) m := by
  simp [Accounted, arrive]

theorem arrive_keeps (s : Spool) (m n : Msg) (h : Accounted s n) : Accounted (arrive s m) n := by
  rcases h with h | h
  · exact Or.inl (by simp [arrive, h])
  · exact Or.inr (by simpa [arrive] using h)

theorem receive_keeps (s : Spool) (n : Msg) (h : Accounted s n) : Accounted (receive s) n := by
  by_cases hc : n ∈ s.committed
  · exact Or.inr (by simpa [receive] using hc)
  · rcases h with h | h
    · exact Or.inl (by simp [receive, List.mem_filter, h, hc])
    · exact absurd h hc

theorem commit_keeps (s : Spool) (n : Msg) (h : Accounted s n) : Accounted (commit s) n := by
  rcases h with h | h
  · exact Or.inl (by simpa [commit] using h)
  · exact Or.inr (by simp [commit, h])

theorem ack_keeps (s : Spool) (n : Msg) (h : Accounted s n) : Accounted (ack s) n := by
  unfold ack
  split_ifs with hall
  · rcases h with h | h
    · by_cases hp : n ∈ s.presented
      · have : s.committed.contains n = true := by
          have := List.all_eq_true.mp hall n hp
          simpa using this
        exact Or.inr (by simpa using this)
      · exact Or.inl (by simp [List.mem_filter, h, hp])
    · exact Or.inr h
  · exact h

/-- The operations of either side. -/
inductive Step
  | arrive (m : Msg)
  | receive
  | commit
  | ack

def apply (s : Spool) : Step → Spool
  | .arrive m => arrive s m
  | .receive => receive s
  | .commit => commit s
  | .ack => ack s

def run (s : Spool) (steps : List Step) : Spool := steps.foldl apply s

/-- No loss: whatever happens after a message is accounted for, it stays so. -/
theorem no_loss (s : Spool) (n : Msg) (h : Accounted s n) (steps : List Step) :
    Accounted (run s steps) n := by
  induction steps generalizing s with
  | nil => simpa [run] using h
  | cons step rest ih =>
    simp only [run, List.foldl_cons] at *
    apply ih
    cases step with
    | arrive m => exact arrive_keeps s m n h
    | receive => exact receive_keeps s n h
    | commit => exact commit_keeps s n h
    | ack => exact ack_keeps s n h

/-- Every message that arrives is accounted for from then on. -/
theorem arrival_never_lost (s : Spool) (m : Msg) (steps : List Step) :
    Accounted (run (arrive s m) steps) m :=
  no_loss _ m (arrive_accounts s m) steps

/-- A read never presents a committed message. -/
theorem committed_never_presented (s : Spool) (m : Msg) (hm : m ∈ s.committed) :
    m ∉ (receive s).presented := by
  simp [receive, List.mem_filter, hm]

/-- A settlement before the commit removes nothing. -/
theorem ack_waits_for_commit (s : Spool) (m : Msg) (hp : m ∈ s.presented) (hc : m ∉ s.committed) :
    ack s = s := by
  unfold ack
  split_ifs with hall
  · exfalso
    have := List.all_eq_true.mp hall m hp
    simp [hc] at this
  · rfl

/-- After the commit, settlement leaves no presented message in the inbox. -/
theorem settled_after_commit (s : Spool) (m : Msg) (hp : m ∈ s.presented) :
    m ∉ (ack (commit s)).inbox := by
  have hall : (commit s).presented.all (fun m => (commit s).committed.contains m) = true := by
    apply List.all_eq_true.mpr
    intro x hx
    simp [commit] at hx ⊢
    exact Or.inr hx
  unfold ack
  rw [if_pos hall]
  simp [commit, hp]

/-! The replaced adapter: one slot, each arrival overwriting it. -/

def arriveSlot (_slot : Option Msg) (m : Msg) : Option Msg := some m

theorem slot_loses_the_first :
    ∃ first second : Msg, arriveSlot (arriveSlot none first) second ≠ some first := by
  exact ⟨1, 2, by simp [arriveSlot]⟩

end Mettapedia.Protocols.Agents.ChatSpoolDelivery
