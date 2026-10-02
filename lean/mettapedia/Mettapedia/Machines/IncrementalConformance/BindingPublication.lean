import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

/-!
# Publishing bindings from changed-key notifications

The reference receiver replays assignments in order. The incremental receiver
reads the final retained store only at notified keys. Agreement is proved when
notifications cover every assigned key; duplicates and notification order do
not matter because every read sees the same final store.

This is a replacement-update algebra, unlike append-only transport. It does not
prove that SWI attribute hooks generate every necessary notification, that a
native alias graph realizes the store, or that the C/FFI implementation is safe.
Those are separate integration obligations. In particular, a branch must restore
both its retained state and its notification queue on rollback.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.IncrementalConformance.BindingPublication

variable {Key Value : Type*} [DecidableEq Key]

def replay : (Key → Value) → List (Key × Value) → Key → Value
  | old, [] => old
  | old, (key, value) :: writes => replay (Function.update old key value) writes

def publish : (Key → Value) → (Key → Value) → List Key → (Key → Value) × Nat
  | old, _, [] => (old, 0)
  | old, final, key :: keys =>
      let tail := publish (Function.update old key (final key)) final keys
      (tail.1, tail.2 + 1)

theorem publish_apply (old final : Key → Value) (keys : List Key) (key : Key) :
    (publish old final keys).1 key = if key ∈ keys then final key else old key := by
  induction keys generalizing old with
  | nil => simp [publish]
  | cons head tail ih =>
      simp only [publish, ih, List.mem_cons]
      by_cases h : key = head
      · subst head
        simp
      · simp [h]

theorem publish_visits (old final : Key → Value) (keys : List Key) :
    (publish old final keys).2 = keys.length := by
  induction keys generalizing old with
  | nil => rfl
  | cons head tail ih => simp [publish, ih]

theorem replay_untouched (old : Key → Value) (writes : List (Key × Value))
    (key : Key) (h : key ∉ writes.map Prod.fst) : replay old writes key = old key := by
  induction writes generalizing old with
  | nil => rfl
  | cons write writes ih =>
      rcases write with ⟨head, value⟩
      simp only [List.map_cons, List.mem_cons, not_or] at h
      rw [replay, ih _ h.2, Function.update_of_ne h.1]

theorem publication_agrees (old : Key → Value) (writes : List (Key × Value))
    (keys : List Key) (covers : ∀ key ∈ writes.map Prod.fst, key ∈ keys) :
    (publish old (replay old writes) keys).1 = replay old writes := by
  funext key
  rw [publish_apply]
  by_cases h : key ∈ keys
  · simp [h]
  · have untouched : key ∉ writes.map Prod.fst := fun hw => h (covers key hw)
    simp [h, replay_untouched old writes key untouched]

theorem recorded_keys_suffice (old : Key → Value) (writes : List (Key × Value)) :
    (publish old (replay old writes) (writes.map Prod.fst)).1 = replay old writes :=
  publication_agrees old writes _ (fun _ h => h)

theorem publication_order_irrelevant (old final : Key → Value) (a b : List Key)
    (same : ∀ key, key ∈ a ↔ key ∈ b) :
    (publish old final a).1 = (publish old final b).1 := by
  funext key
  simp only [publish_apply, same key]

namespace Controls

def zero : Nat → Nat := fun _ => 0

theorem repeated_assignment_reads_latest :
    (publish zero (replay zero [(1, 3), (1, 7)]) [1]).1 1 = 7 := by
  simp [publish, replay]

theorem duplicated_notifications_preserve_answer :
    (publish zero (replay zero [(1, 7)]) [1, 1]).1 =
      (publish zero (replay zero [(1, 7)]) [1]).1 := by
  apply publication_order_irrelevant
  simp

theorem missed_notification_loses_assignment :
    (publish zero (replay zero [(1, 7)]) []).1 1 ≠ replay zero [(1, 7)] 1 := by
  simp [publish, replay, zero]

theorem stale_notification_changes_restored_branch :
    (publish zero (replay zero [(1, 7)]) [1]).1 1 ≠ zero 1 := by
  simp [publish, replay, zero]

end Controls
end Mettapedia.Machines.IncrementalConformance.BindingPublication
