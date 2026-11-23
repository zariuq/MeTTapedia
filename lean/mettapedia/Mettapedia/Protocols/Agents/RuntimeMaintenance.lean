import Std

/-!
# Maintenance preserves the admitted view and the committed turn

A hot context is a suffix of the original ordered records. Its offset includes
records omitted by an earlier checkpoint. Source identities and multiplicity
survive; a request can retrieve the preceding records from the original ledger.

A hierarchy copy stages whole partitions before the binding moves. Publication
requires exact ordered readback of the partitions and an unchanged source
coordinate. Implementations using digests must establish that their encoding
is faithful and treat digest equality as a cryptographic check, not as a proof
of structural equality. This model assumes the source revision identifies an
immutable logical snapshot.

Recycling is a request to leave after the current turn reaches a durable
checkpoint. A returned provider response alone does not establish settlement.
-/

set_option autoImplicit false
namespace Mettapedia.Protocols.Agents.RuntimeMaintenance

universe u
variable {Record : Type u}

structure Window (Record : Type u) where
  archive : List Record
  recent : List Record
  used : Nat
  deriving Repr

def weight (size : Record → Nat) (records : List Record) : Nat :=
  (records.map size).sum

/-- A suffix of whole records, with room reserved for the frame and handoff. -/
def select (size : Record → Nat) (room : Nat) : List Record → Window Record
  | [] => ⟨[], [], 0⟩
  | row :: rows =>
    let suffix := select size room rows
    if suffix.archive.isEmpty && size row + suffix.used ≤ room then
      ⟨[], row :: suffix.recent, size row + suffix.used⟩
    else
      ⟨row :: suffix.archive, suffix.recent, suffix.used⟩

theorem select_partition (size : Record → Nat) (room : Nat) (rows : List Record) :
    (select size room rows).archive ++ (select size room rows).recent = rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simp only [select]
    split
    · next fit =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at fit
      have h : (select size room rows).archive = [] :=
        List.isEmpty_iff.mp fit.1
      simpa [h] using congrArg (List.cons row) ih
    · exact congrArg (List.cons row) ih

theorem select_cost (size : Record → Nat) (room : Nat) (rows : List Record) :
    (select size room rows).used = weight size (select size room rows).recent ∧
      (select size room rows).used ≤ room := by
  induction rows with
  | nil => simp [select, weight]
  | cons row rows ih =>
    simp only [select]
    split
    · next fit =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at fit
      refine ⟨?_, fit.2⟩
      exact congrArg (fun n => size row + n) ih.1
    · exact ih

theorem absolute_offset (size : Record → Nat) (room : Nat) (old rows : List Record) :
    old.length + (select size room rows).archive.length +
      (select size room rows).recent.length = (old ++ rows).length := by
  have h := congrArg List.length (select_partition size room rows)
  simp only [List.length_append] at h ⊢
  omega

theorem relative_offset_loses_a_prefix :
    let selected := select (fun (_ : Nat) => 1) 1 [7, 7]
    selected.archive.length ≠ [3, 4].length + selected.archive.length := by
  decide

structure Space (Record : Type u) where
  identity : Nat
  revision : Nat
  partitions : List (List Record)
  deriving DecidableEq

/-- Transfer checks the captured binding, then all the archived occurrences.
The destination has its own storage identity and revision. -/
def publish [DecidableEq Record] (captured current staged : Space Record) :
    Option (Space Record) :=
  if current.identity = captured.identity ∧ current.revision = captured.revision ∧
      staged.partitions = captured.partitions then some staged else none

theorem publish_preserves_occurrences [DecidableEq Record]
    {captured current staged next : Space Record}
    (h : publish captured current staged = some next) :
    next.partitions.flatten = captured.partitions.flatten ∧
    current.identity = captured.identity ∧ current.revision = captured.revision := by
  unfold publish at h
  split at h
  · next checked =>
    have hs : staged = next := Option.some.inj h
    subst next
    exact ⟨congrArg List.flatten checked.2.2, checked.1, checked.2.1⟩
  · cases h

theorem equal_counts_do_not_authorize_copy :
    let source : Space Nat := ⟨1, 3, [[7, 7], [9]]⟩
    let wrong : Space Nat := ⟨2, 1, [[7, 9], [9]]⟩
    source.partitions.flatten.length = wrong.partitions.flatten.length ∧
    publish source source wrong = none := by
  decide

theorem stale_source_does_not_authorize_copy [DecidableEq Record]
    (captured current staged : Space Record) (h : current.revision ≠ captured.revision) :
    publish captured current staged = none := by
  simp [publish, h]

/-! ## Sharing append-only membership across revisions

A revision with only appended children is a prefix of the same ordered
occurrence sequence. A versioned prefix length can therefore replace the
copied membership list. Arbitrary removal and reordering would need explicit
edits or an independently stored generation.
-/

def membershipAt (members : List Record) (through : Nat) : Option (List Record) :=
  if through ≤ members.length then some (members.take through) else none

theorem append_preserves_old_membership (members added : List Record) (through : Nat)
    (h : through ≤ members.length) :
    membershipAt (members ++ added) through = membershipAt members through := by
  have hall : through ≤ (members ++ added).length := by
    simp only [List.length_append]
    omega
  simp only [membershipAt, if_pos h, if_pos hall]
  rw [List.take_append_of_le_length h]

theorem equal_members_still_have_separate_occurrences :
    membershipAt ([7, 7, 9] : List Nat) 2 = some [7, 7] := by
  decide

/-- Reuse a generation only after checking its actual ordered prefix.
A caller must still publish the delta and version reference atomically. -/
def membershipDelta [DecidableEq Record] (old next : List Record) : Option (List Record) :=
  if old = next.take old.length then some (next.drop old.length) else none

theorem membership_delta_preserves_prefix [DecidableEq Record] {old next delta : List Record}
    (accepted : membershipDelta old next = some delta) :
    old ++ delta = next := by
  unfold membershipDelta at accepted
  split at accepted
  · next ordered =>
    have h := Option.some.inj accepted
    rw [← h]
    exact (congrArg (fun p => p ++ next.drop old.length) ordered).trans
      (List.take_append_drop old.length next)
  · cases accepted

theorem equal_lengths_can_have_different_membership :
    ([1, 2] : List Nat).length = [2, 1].length ∧ membershipDelta [1, 2] [2, 1] = none := by
  decide

theorem deduplication_can_lose_the_prefix :
    membershipDelta ([9, 1, 9] : List Nat) [9, 1, 2] = none := by
  decide

/-- Member slots needed when all lists after single additions are copied.
This counts member slots, excluding the common per-version metadata. -/
def copiedMemberSlots : Nat → Nat
  | 0 => 0
  | n + 1 => copiedMemberSlots n + (n + 1)

theorem copied_member_slots_quadratic (n : Nat) :
    2 * copiedMemberSlots n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [copiedMemberSlots, Nat.mul_add, ih, Nat.add_mul]
    omega

theorem shared_member_slots_at_128 :
    copiedMemberSlots 128 = 8256 ∧ (List.range 128).length = 128 := by
  have h : 2 * copiedMemberSlots 128 = 2 * 8256 := copied_member_slots_quadratic 128
  exact ⟨Nat.eq_of_mul_eq_mul_left (by decide) h, List.length_range⟩

inductive Phase where
  | boundary | provider | settling
  deriving DecidableEq, Repr

structure Loop where
  phase : Phase
  checkpoint : Nat
  requested : Bool
  deriving DecidableEq, Repr

def requestRecycle (s : Loop) : Loop := {s with requested := true}
def canRecycle (s : Loop) : Bool := s.requested && (s.phase == .boundary)

def finishProvider (s : Loop) : Loop :=
  if s.phase = .provider then {s with phase := .settling} else s

def settle (s : Loop) (committed : Bool) : Loop :=
  if committed && (s.phase == .settling) then
    {s with phase := .boundary, checkpoint := s.checkpoint + 1}
  else s

theorem live_provider_keeps_its_owner (n : Nat) :
    canRecycle (requestRecycle ⟨.provider, n, false⟩) = false := rfl

theorem failed_checkpoint_cannot_recycle (n : Nat) :
    canRecycle (settle (finishProvider (requestRecycle ⟨.provider, n, false⟩)) false)
      = false := rfl

theorem successful_checkpoint_can_recycle (n : Nat) :
    let settled := settle (finishProvider (requestRecycle ⟨.provider, n, false⟩)) true
    canRecycle settled = true ∧ settled.checkpoint = n + 1 := ⟨rfl, rfl⟩

end Mettapedia.Protocols.Agents.RuntimeMaintenance
