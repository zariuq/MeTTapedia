import Mathlib.Tactic

/-!
# Byte fragments: shared bytes, streamed in order

A request body is a list of immutable fragments. Each fragment carries a
reference count, and its bytes live while the count is positive. The worker
takes a reference to every fragment when it admits a job and gives it back
when it retires the job, so the caller may give back its own reference as
soon as it has submitted.

The worker sends a body through a read callback. Its cursor is a fragment
and an offset inside that fragment, not an absolute byte offset; a seek
callback moves it to an absolute offset when the transport must send the
body again.

Invariants proved here:
* a fragment's count is the number of references taken and not given back,
  so while the job holds one the bytes are alive, whatever the caller does;
* one read answers the next bytes of the concatenation from the cursor's
  absolute offset, as many as the buffer holds, and moves the cursor by
  exactly that many;
* a seek to any offset within the body names that offset;
* successive reads from any offset answer the rest of the body, whatever
  the buffer sizes, once their room covers it.

The counterexample is a worker that keeps the caller's reference instead of
taking its own: when the caller gives it back after submitting, the count
is zero while the job still has bytes to send.

This is an abstract contract, not a refinement proof of `src/http_worker.c`.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.ByteFragments

/-! ## Reference counts -/

/-- A step on one fragment's references, by a holder. -/
inductive Step (H : Type)
  | take (h : H)
  | giveBack (h : H)

/-- References held: a multiset of holders, and the count the fragment keeps. -/
structure Refs (H : Type) where
  holders : Multiset H
  count : ℕ

variable {H : Type} [DecidableEq H]

/-- A holder gives back only a reference it holds; anything else is refused. -/
def apply (r : Refs H) : Step H → Option (Refs H)
  | .take h => some ⟨h ::ₘ r.holders, r.count + 1⟩
  | .giveBack h =>
    if h ∈ r.holders then some ⟨r.holders.erase h, r.count - 1⟩ else none

def run (r : Refs H) : List (Step H) → Option (Refs H)
  | [] => some r
  | s :: rest => (apply r s).bind (fun r' => run r' rest)

/-- The count stays the number of references held. -/
def Counted (r : Refs H) : Prop := r.count = Multiset.card r.holders

theorem apply_counted (r r' : Refs H) (s : Step H) (hc : Counted r)
    (hs : apply r s = some r') : Counted r' := by
  cases s with
  | take h =>
    simp only [apply, Option.some.injEq] at hs
    subst hs
    unfold Counted at hc ⊢
    simp [hc]
  | giveBack h =>
    simp only [apply] at hs
    split_ifs at hs with hm
    simp only [Option.some.injEq] at hs
    subst hs
    unfold Counted at hc ⊢
    simp [hc, Multiset.card_erase_of_mem hm]

theorem run_counted (steps : List (Step H)) :
    ∀ (r r' : Refs H), Counted r → run r steps = some r' → Counted r' := by
  induction steps with
  | nil => intro r r' hc hs; simp only [run, Option.some.injEq] at hs; exact hs ▸ hc
  | cons s rest ih =>
    intro r r' hc hs
    simp only [run] at hs
    cases ha : apply r s with
    | none => simp [ha] at hs
    | some r'' => simp only [ha, Option.bind_some] at hs; exact ih r'' r' (apply_counted r r'' s hc ha) hs

/-- The bytes live while the count is positive. -/
def Alive (r : Refs H) : Prop := 0 < r.count

omit [DecidableEq H] in
/-- While a holder holds a reference, the bytes are alive. -/
theorem held_alive (r : Refs H) (h : H) (hc : Counted r) (hm : h ∈ r.holders) : Alive r := by
  unfold Alive; rw [hc]; exact Multiset.card_pos_iff_exists_mem.mpr ⟨h, hm⟩

/-- Created by the caller, admitted by the job, given back by the caller: the
job still holds a reference, so the bytes are alive for every read. -/
theorem caller_gives_back_job_reads (caller job : H) (hne : caller ≠ job) :
    ∃ r', run ⟨{caller}, 1⟩ [.take job, .giveBack caller] = some r' ∧ job ∈ r'.holders ∧ Alive r' := by
  refine ⟨⟨({caller} : Multiset H).cons job |>.erase caller, 1⟩, ?_, ?_, ?_⟩
  · simp [run, apply]
  · simp [Multiset.mem_erase_of_ne (Ne.symm hne)]
  · simp [Alive]

/-! ## Counterexample: keeping the caller's reference -/

/-- A worker that takes no reference of its own: the job reads through the
caller's. When the caller gives it back, the count is zero. -/
theorem borrowed_reference_dies (caller : H) :
    run ⟨{caller}, 1⟩ [.giveBack caller] = some ⟨0, 0⟩ ∧ ¬ Alive (⟨0, 0⟩ : Refs H) := by
  constructor
  · simp [run, apply]
  · simp [Alive]

/-! ## The read cursor -/

variable {α : Type}

/-- One read with room for `room` bytes, from the fragments at and after the
cursor's fragment, at offset `off` in the first. It answers the bytes, how
many fragments the cursor moved past, and the offset in the fragment it
stops in. A fragment with nothing left is passed; the buffer stops a read. -/
def readFrom : List (List α) → ℕ → ℕ → List α × ℕ × ℕ
  | [], off, _ => ([], 0, off)
  | f :: rest, off, room =>
    if room = 0 then ([], 0, off)
    else if f.length - off < room then
      let r := readFrom rest 0 (room - (f.length - off))
      (f.drop off ++ r.1, r.2.1 + 1, r.2.2)
    else ((f.drop off).take room, 0, off + room)

/-- One read answers the next `room` bytes of the rest of the body. -/
theorem readFrom_bytes (fs : List (List α)) :
    ∀ (off room : ℕ), off ≤ (fs.headD []).length →
      (readFrom fs off room).1 = ((fs.flatten).drop off).take room := by
  induction fs with
  | nil => intro off room _; simp [readFrom]
  | cons f rest ih =>
    intro off room hoff
    simp only [List.headD_cons] at hoff
    simp only [readFrom, List.flatten_cons]
    rw [List.drop_append_of_le_length hoff]
    split_ifs with h0 hlt
    · simp [h0]
    · have hl : (f.drop off).length = f.length - off := List.length_drop ..
      rw [ih 0 _ (Nat.zero_le _), List.drop_zero, List.take_append,
        List.take_of_length_le (l := f.drop off) (i := room) (by rw [hl]; omega), hl]
    · have hl : (f.drop off).length = f.length - off := List.length_drop ..
      rw [List.take_append_of_le_length (l₁ := f.drop off) (l₂ := rest.flatten) (i := room)
        (by rw [hl]; omega)]

/-- Where a cursor is, as an absolute offset into the body. -/
def absolute (fs : List (List α)) (index off : ℕ) : ℕ :=
  ((fs.take index).map List.length).sum + off

/-- A cursor whose offset lies within its fragment. -/
def Within (fs : List (List α)) (index off : ℕ) : Prop :=
  off ≤ ((fs.drop index).headD []).length

/-- One read moves the cursor by exactly the bytes it answered, and leaves it
within a fragment. -/
theorem readFrom_moves (fs : List (List α)) :
    ∀ (off room : ℕ), off ≤ (fs.headD []).length →
      absolute fs (readFrom fs off room).2.1 (readFrom fs off room).2.2 =
          off + (readFrom fs off room).1.length ∧
        Within fs (readFrom fs off room).2.1 (readFrom fs off room).2.2 := by
  induction fs with
  | nil => intro off room hoff; simp [readFrom, absolute, Within]; simpa using hoff
  | cons f rest ih =>
    intro off room hoff
    simp only [List.headD_cons] at hoff
    simp only [readFrom]
    split_ifs with h0 hlt
    · simp [absolute, Within, hoff]
    · obtain ⟨ha, hw⟩ := ih 0 (room - (f.length - off)) (Nat.zero_le _)
      refine ⟨?_, ?_⟩
      · simp only [absolute, List.take_succ_cons, List.map_cons, List.sum_cons] at ha ⊢
        rw [Nat.add_assoc, ha, List.length_append, List.length_drop]
        omega
      · simpa [Within] using hw
    · simp only [absolute, Within, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add,
        List.drop_zero, List.headD_cons, List.length_take, List.length_drop]
      omega

/-! ## Seeking -/

/-- A seek to `k`: pass every fragment that ends at or before `k`, while some
of `k` is left, and stop in the fragment where `k` falls. -/
def seekFrom : List (List α) → ℕ → ℕ × ℕ
  | [], left => (0, left)
  | f :: rest, left =>
    if left = 0 ∨ left < f.length then (0, left)
    else let r := seekFrom rest (left - f.length); (r.1 + 1, r.2)

/-- A seek within the body names the offset it was asked for. -/
theorem seek_absolute (fs : List (List α)) :
    ∀ k, k ≤ (fs.map List.length).sum →
      absolute fs (seekFrom fs k).1 (seekFrom fs k).2 = k ∧ Within fs (seekFrom fs k).1 (seekFrom fs k).2 := by
  induction fs with
  | nil => intro k hk; simp at hk; subst hk; simp [seekFrom, absolute, Within]
  | cons f rest ih =>
    intro k hk
    simp only [List.map_cons, List.sum_cons] at hk
    simp only [seekFrom]
    split_ifs with h
    · refine ⟨by simp [absolute], ?_⟩
      rcases h with h | h
      · simp [Within, h]
      · simp [Within]; omega
    · obtain ⟨ha, hw⟩ := ih (k - f.length) (by omega)
      refine ⟨?_, by simpa [Within] using hw⟩
      simp only [absolute, List.take_succ_cons, List.map_cons, List.sum_cons] at ha ⊢
      omega

/-! ## Streaming the rest of a body -/

/-- Successive reads from absolute offset `p`, with buffers of the given sizes. -/
def readAll (body : List α) : ℕ → List ℕ → List α
  | _, [] => []
  | p, room :: rooms =>
    let out := (body.drop p).take room
    out ++ readAll body (p + out.length) rooms

theorem readAll_eq (body : List α) (rooms : List ℕ) :
    ∀ p, readAll body p rooms = (body.drop p).take rooms.sum := by
  induction rooms with
  | nil => intro p; simp [readAll]
  | cons room rooms ih =>
    intro p
    simp only [readAll, List.sum_cons, ih]
    rw [List.take_add]
    congr 2
    rw [List.length_take, List.length_drop]
    rcases le_total room (body.length - p) with h | h
    · rw [Nat.min_eq_left h, List.drop_drop]
    · rw [Nat.min_eq_right h, List.drop_eq_nil_of_le (as := body) (by omega),
        List.drop_eq_nil_of_le (as := body.drop p) (by rw [List.length_drop]; omega)]

/-- Once their room covers it, successive reads answer the body from `p` on,
in particular the whole body again after a seek to its start. -/
theorem readAll_rest (body : List α) (rooms : List ℕ) (p : ℕ)
    (hroom : body.length - p ≤ rooms.sum) : readAll body p rooms = body.drop p := by
  rw [readAll_eq]; exact List.take_of_length_le (by simpa using hroom)

end Mettapedia.Protocols.Agents.ByteFragments
