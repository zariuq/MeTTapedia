import Mettapedia.Protocols.Agents.InputSettlement

/-!
# Captured delivery scopes across a turn

A turn captures the identities it presents once. Its eventual checkpoint settles
that frame, even if further deliveries arrive before publication. Re-reading the
transport's current batch at checkpoint time would consume unpresented work.

The definitions use the existing mailbox transitions and presenter contract.
The late-arrival theorem derives non-membership in the captured frame from the
presenter's pending-membership law and freshness in the earlier mailbox; it does
not assume that the desired delivery survives. The resampling theorem uses the
same mailbox and arrival to demonstrate the competing rule's failure.

This models delivery settlement, not task achievement, transport durability or
the implementation's refinement of these transitions.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.CapturedInputScope

open Mettapedia.Protocols.Mail
open Mettapedia.Protocols.Agents.InputSettlement

/-- Immutable identities selected by one presentation. -/
structure Frame where
  ids : List MessageId

def capture (p : Presenter) (b : Mailbox) : Frame :=
  ⟨(p.batch b).map Message.id⟩

/-- The commit consumes exactly the captured identities, not a new presentation. -/
def checkpoint (f : Frame) (current : Mailbox) : Mailbox :=
  ackAll current f.ids

theorem captured_id_was_stored (p : Presenter) (b : Mailbox) {id : MessageId}
    (h : id ∈ (capture p b).ids) : id ∈ b.ids := by
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp h
  have pending := p.batch_pending b m hm
  have stored : m ∈ b.stored := (List.mem_filter.mp pending).1
  exact List.mem_map.mpr ⟨m, stored, rfl⟩

theorem checkpoint_pending (f : Frame) (current : Mailbox) :
    (checkpoint f current).unread = current.unread.filter (fun m => m.id ∉ f.ids) :=
  unread_ackAll current f.ids

/-- New input survives a checkpoint of the earlier frame, whatever its text. -/
theorem fresh_arrival_survives (p : Presenter) {b : Mailbox} (hb : b.Valid)
    {m : Message} (fresh : m.id ∉ b.ids) :
    m ∈ (checkpoint (capture p b) (b.deliver m)).unread ∧
      Wakes (checkpoint (capture p b) (b.deliver m)) := by
  have outside : m.id ∉ (capture p b).ids :=
    fun h => fresh (captured_id_was_stored p b h)
  have pending := (fresh_delivery_wakes hb fresh).1
  have survives : m ∈ (checkpoint (capture p b) (b.deliver m)).unread := by
    rw [checkpoint_pending]
    exact List.mem_filter.mpr ⟨pending, by simpa using outside⟩
  exact ⟨survives, List.ne_nil_of_mem survives⟩

/-- Every occurrence in the old presentation is excluded after that frame commits. -/
theorem captured_occurrence_settled (p : Presenter) (before current : Mailbox)
    {m : Message} (shown : m ∈ p.batch before) :
    m ∉ (checkpoint (capture p before) current).unread := by
  rw [checkpoint_pending]
  intro h
  have outside : m.id ∉ (capture p before).ids := by
    simpa using (List.mem_filter.mp h).2
  exact outside (List.mem_map.mpr ⟨m, shown, rfl⟩)

/-- The plausible competing implementation re-reads all pending input at commit. -/
def resampledCheckpoint (current : Mailbox) : Mailbox :=
  ackAll current (current.unread.map Message.id)

theorem resampling_consumes_pending (current : Mailbox) {m : Message}
    (pending : m ∈ current.unread) : m ∉ (resampledCheckpoint current).unread := by
  rw [resampledCheckpoint, unread_ackAll]
  intro h
  have outside : m.id ∉ current.unread.map Message.id := by
    simpa using (List.mem_filter.mp h).2
  exact outside (List.mem_map.mpr ⟨m, pending, rfl⟩)

/-- The two rules disagree on a genuinely fresh late arrival, not on a fabricated tag. -/
theorem captured_vs_resampled (p : Presenter) {b : Mailbox} (hb : b.Valid)
    {m : Message} (fresh : m.id ∉ b.ids) :
    m ∈ (checkpoint (capture p b) (b.deliver m)).unread ∧
      m ∉ (resampledCheckpoint (b.deliver m)).unread :=
  ⟨(fresh_arrival_survives p hb fresh).1,
    resampling_consumes_pending _ (fresh_delivery_wakes hb fresh).1⟩

end Mettapedia.Protocols.Agents.CapturedInputScope
