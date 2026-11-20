/-!
# HOLR deliveries: what an `EMIT` record commits

HOLR is CeTTa's stream format for HOL Light proofs.  Two of its laws concern
what a replay hands to its reader:

* records are atomic: a record commits all of its outputs (ids, labels,
  deliveries) or none;
* `DROP` says that an id is never used again.

This file models the part of a replay that concerns them, over any kernel.
A record defines an id by an operation on the live theorems, emits or labels
a live id, or drops a live id.  An output of `EMIT` or `LABEL` can be read in
two ways:

* committed: the theorem is taken when the record commits (the stream
  document);
* late: the id is kept, and the theorem is looked up when the output is read
  (CeTTa's replayer before it was corrected).

Read late, a committed output is lost by a later `DROP`
(`late_reading_loses_a_committed_output`), and what is read depends on when
it is read (`late_reading_depends_on_when`).  Read as committed, the outputs
of a stream extend the outputs of each of its prefixes (`delivered_prefix`).
The two readings agree on every stream that does not drop an id after
emitting or labelling it (`late_eq_committed_of_safe`).  The stream
compactor keeps such ids alive, which is why no generated proof showed the
difference.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.HOLRDeliveries

/-- The records that concern outputs: an operation defines an id, an id is
emitted or labelled, an id is dropped. -/
inductive Record (Op : Type) where
  | define (id : Nat) (op : Op)
  | emit (id : Nat)
  | label (id : Nat) (name : String)
  | drop (id : Nat)

inductive Slot (Thm : Type) where
  | live (t : Thm)
  | dropped

/-- An output for the reader: an `EMIT` has no name, a `LABEL` has one. -/
structure Out (α : Type) where
  name : Option String
  value : α
  deriving DecidableEq, Repr

/-- The id table, the outputs as committed, and the ids of the outputs as the
late reading keeps them. -/
structure State (Thm : Type) where
  table : Nat → Option (Slot Thm)
  delivered : List (Out Thm)
  pending : List (Out Nat)

def State.empty {Thm : Type} : State Thm := ⟨fun _ => none, [], []⟩

def update {β : Type} (f : Nat → β) (k : Nat) (v : β) : Nat → β :=
  fun j => if j = k then v else f j

/-- The theorem an id names now: defined and not dropped. -/
def live {Thm : Type} (table : Nat → Option (Slot Thm)) (id : Nat) : Option Thm :=
  match table id with
  | some (.live t) => some t
  | _ => none

inductive Outcome (Thm : Type) where
  | ok (s : State Thm)
  | malformed
  | refused

section Replay

variable {Op Thm : Type} (run : Op → (Nat → Option Thm) → Option Thm)

/-- An `EMIT` (no name) or `LABEL` (a name) of a live id commits one output. -/
def output (s : State Thm) (name : Option String) (id : Nat) : Outcome Thm :=
  match live s.table id with
  | some t => .ok { s with delivered := s.delivered ++ [⟨name, t⟩], pending := s.pending ++ [⟨name, id⟩] }
  | none => .malformed

/-- One record.  An operand that is not live (not defined, or dropped) makes
the stream malformed; an operation the kernel refuses is refused. -/
def step (s : State Thm) : Record Op → Outcome Thm
  | .define id op =>
      match s.table id with
      | some _ => .malformed
      | none =>
          match run op (live s.table) with
          | some t => .ok { s with table := update s.table id (some (.live t)) }
          | none => .refused
  | .emit id => output s none id
  | .label id name => output s (some name) id
  | .drop id =>
      match live s.table id with
      | some _ => .ok { s with table := update s.table id (some .dropped) }
      | none => .malformed

def replay (s : State Thm) : List (Record Op) → Outcome Thm
  | [] => .ok s
  | r :: rs =>
      match step run s r with
      | .ok s' => replay s' rs
      | .malformed => .malformed
      | .refused => .refused

/-- The late reading: each kept id looked up now; `none` where one was dropped
since (CeTTa's "output STALE"). -/
def resolve (table : Nat → Option (Slot Thm)) : List (Out Nat) → Option (List (Out Thm))
  | [] => some []
  | o :: os =>
      match live table o.value, resolve table os with
      | some t, some ts => some (⟨o.name, t⟩ :: ts)
      | _, _ => none

def readLate (s : State Thm) : Option (List (Out Thm)) := resolve s.table s.pending

/-! ## Read as committed, a prefix's outputs are final -/

theorem step_delivered {s s' : State Thm} {r : Record Op} (h : step run s r = .ok s') :
    ∃ d, s'.delivered = s.delivered ++ d := by
  cases r with
  | define id op =>
      simp only [step] at h
      split at h
      · cases h
      · split at h
        · cases h; exact ⟨[], by simp⟩
        · cases h
  | emit id =>
      simp only [step, output] at h
      split at h
      · cases h; exact ⟨_, rfl⟩
      · cases h
  | label id name =>
      simp only [step, output] at h
      split at h
      · cases h; exact ⟨_, rfl⟩
      · cases h
  | drop id =>
      simp only [step] at h
      split at h
      · cases h; exact ⟨[], by simp⟩
      · cases h

theorem replay_delivered {s s' : State Thm} {rs : List (Record Op)}
    (h : replay run s rs = .ok s') : ∃ d, s'.delivered = s.delivered ++ d := by
  induction rs generalizing s with
  | nil => simp only [replay] at h; cases h; exact ⟨[], by simp⟩
  | cons r rs ih =>
      simp only [replay] at h
      split at h
      · rename_i s₁ h₁
        obtain ⟨d₁, e₁⟩ := step_delivered run h₁
        obtain ⟨d₂, e₂⟩ := ih h
        exact ⟨d₁ ++ d₂, by rw [e₂, e₁, List.append_assoc]⟩
      · cases h
      · cases h

theorem replay_append (s : State Thm) (p q : List (Record Op)) :
    replay run s (p ++ q) =
      (match replay run s p with
       | .ok s₁ => replay run s₁ q
       | .malformed => .malformed
       | .refused => .refused) := by
  induction p generalizing s with
  | nil => simp [replay]
  | cons r rs ih =>
      simp only [List.cons_append, replay]
      split <;> simp_all

/-- The outputs of a stream extend the outputs of each of its prefixes: what
a record committed stays delivered, whatever follows it. -/
theorem delivered_prefix {s s₂ : State Thm} {p q : List (Record Op)}
    (h : replay run s (p ++ q) = .ok s₂) :
    ∃ s₁, replay run s p = .ok s₁ ∧ ∃ d, s₂.delivered = s₁.delivered ++ d := by
  rw [replay_append] at h
  split at h
  · rename_i s₁ h₁
    exact ⟨s₁, h₁, replay_delivered run h⟩
  · cases h
  · cases h

/-! ## Read late, the two readings agree exactly when no output's id is
dropped afterwards -/

/-- No id is dropped after it was emitted or labelled; `P` holds the ids
emitted or labelled so far. -/
def Safe (P : List Nat) : List (Record Op) → Prop
  | [] => True
  | .define _ _ :: rs => Safe P rs
  | .emit id :: rs => Safe (id :: P) rs
  | .label id _ :: rs => Safe (id :: P) rs
  | .drop id :: rs => id ∉ P ∧ Safe P rs

theorem resolve_live {table : Nat → Option (Slot Thm)} {os : List (Out Nat)} {ts : List (Out Thm)}
    (h : resolve table os = some ts) : ∀ o ∈ os, ∃ t, live table o.value = some t := by
  induction os generalizing ts with
  | nil => intro o ho; cases ho
  | cons o os ih =>
      simp only [resolve] at h
      split at h
      · rename_i t ts' h₁ h₂
        intro o' ho'
        rcases List.mem_cons.mp ho' with rfl | ho'
        · exact ⟨t, h₁⟩
        · exact ih h₂ o' ho'
      · cases h

theorem resolve_update_other {table : Nat → Option (Slot Thm)} {k : Nat} {v : Option (Slot Thm)}
    {os : List (Out Nat)} (hk : ∀ o ∈ os, o.value ≠ k) :
    resolve (update table k v) os = resolve table os := by
  induction os with
  | nil => rfl
  | cons o os ih =>
      have hne : o.value ≠ k := hk o (List.mem_cons_self ..)
      have hrest : ∀ o' ∈ os, o'.value ≠ k := fun o' ho' => hk o' (List.mem_cons_of_mem _ ho')
      have hlive : live (update table k v) o.value = live table o.value := by
        simp [live, update, hne]
      simp only [resolve, hlive, ih hrest]

theorem resolve_snoc {table : Nat → Option (Slot Thm)} {os : List (Out Nat)} {ts : List (Out Thm)}
    {name : Option String} {id : Nat} {t : Thm}
    (h : resolve table os = some ts) (ht : live table id = some t) :
    resolve table (os ++ [⟨name, id⟩]) = some (ts ++ [⟨name, t⟩]) := by
  induction os generalizing ts with
  | nil => simp only [resolve] at h; cases h; simp [resolve, ht]
  | cons o os ih =>
      simp only [resolve] at h
      split at h
      · rename_i t₀ ts' h₁ h₂
        cases h
        simp only [List.cons_append, resolve, h₁, ih h₂, List.cons_append]
      · cases h

theorem step_agree {s s' : State Thm} {r : Record Op}
    (h : step run s r = .ok s')
    (hs : readLate s = some s.delivered)
    (hdrop : ∀ id, r = .drop id → id ∉ s.pending.map Out.value) :
    readLate s' = some s'.delivered := by
  unfold readLate at hs ⊢
  cases r with
  | define id op =>
      simp only [step] at h
      split at h
      · cases h
      · rename_i hfree
        split at h
        · cases h
          have hk : ∀ o ∈ s.pending, o.value ≠ id := by
            intro o ho heq
            obtain ⟨t, ht⟩ := resolve_live hs o ho
            rw [heq] at ht
            simp [live, hfree] at ht
          simp only [resolve_update_other hk, hs]
        · cases h
  | emit id =>
      simp only [step, output] at h
      split at h
      · rename_i t ht
        cases h
        exact resolve_snoc hs ht
      · cases h
  | label id name =>
      simp only [step, output] at h
      split at h
      · rename_i t ht
        cases h
        exact resolve_snoc hs ht
      · cases h
  | drop id =>
      simp only [step] at h
      split at h
      · cases h
        have hk : ∀ o ∈ s.pending, o.value ≠ id := by
          intro o ho heq
          exact hdrop id rfl (List.mem_map.mpr ⟨o, ho, heq⟩)
        simp only [resolve_update_other hk, hs]
      · cases h

theorem safe_perm {P Q : List Nat} {rs : List (Record Op)} (h : Safe P rs) (hPQ : ∀ x, x ∈ P ↔ x ∈ Q) :
    Safe Q rs := by
  induction rs generalizing P Q with
  | nil => trivial
  | cons r rs ih =>
      cases r with
      | define _ _ => exact ih (by simpa only [Safe] using h) hPQ
      | emit id =>
          simp only [Safe] at h ⊢
          exact ih h (fun x => by simp [List.mem_cons, hPQ x])
      | label id _ =>
          simp only [Safe] at h ⊢
          exact ih h (fun x => by simp [List.mem_cons, hPQ x])
      | drop id =>
          simp only [Safe] at h ⊢
          exact ⟨fun hq => h.1 ((hPQ id).mpr hq), ih h.2 hPQ⟩

theorem step_safe {s s₁ : State Thm} {r : Record Op} {rs : List (Record Op)}
    (h : step run s r = .ok s₁) (hsafe : Safe (s.pending.map Out.value) (r :: rs)) :
    Safe (s₁.pending.map Out.value) rs := by
  cases r with
  | define id op =>
      simp only [step] at h
      split at h
      · cases h
      · split at h
        · cases h; simpa only [Safe] using hsafe
        · cases h
  | emit id =>
      simp only [step, output] at h
      split at h
      · cases h
        simp only [Safe] at hsafe
        simp only [List.map_append, List.map_cons, List.map_nil]
        exact safe_perm hsafe (fun x => by simp [List.mem_cons, List.mem_append, or_comm])
      · cases h
  | label id name =>
      simp only [step, output] at h
      split at h
      · cases h
        simp only [Safe] at hsafe
        simp only [List.map_append, List.map_cons, List.map_nil]
        exact safe_perm hsafe (fun x => by simp [List.mem_cons, List.mem_append, or_comm])
      · cases h
  | drop id =>
      simp only [step] at h
      split at h
      · cases h; simp only [Safe] at hsafe; exact hsafe.2
      · cases h

/-- On a stream that never drops an id after emitting or labelling it, the
late reading gives exactly the committed outputs. -/
theorem late_eq_committed_of_safe {s s' : State Thm} {rs : List (Record Op)}
    (h : replay run s rs = .ok s')
    (hs : readLate s = some s.delivered)
    (hsafe : Safe (s.pending.map Out.value) rs) :
    readLate s' = some s'.delivered := by
  induction rs generalizing s with
  | nil => simp only [replay] at h; cases h; exact hs
  | cons r rs ih =>
      simp only [replay] at h
      split at h
      · rename_i s₁ h₁
        have hdrop : ∀ id, r = .drop id → id ∉ s.pending.map Out.value := by
          intro id hr
          subst hr
          simp only [Safe] at hsafe
          exact hsafe.1
        exact ih h (step_agree run h₁ hs hdrop) (step_safe run h₁ hsafe)
      · cases h
      · cases h

end Replay

/-! ## Examples -/

/-- A kernel whose every operation gives the theorem `7`. -/
def sevens : Unit → (Nat → Option Nat) → Option Nat := fun _ _ => some 7

/-- `REFL x; EMIT r; DROP_THM r`. -/
def emitThenDrop : List (Record Unit) := [.define 0 (), .emit 0, .drop 0]

def readBoth (rs : List (Record Unit)) : List (Out Nat) × Option (List (Out Nat)) :=
  match replay sevens State.empty rs with
  | .ok s => (s.delivered, readLate s)
  | _ => ([], none)

/-- Negative: the stream is accepted and its `EMIT` committed one output, and
the late reading has lost it. -/
theorem late_reading_loses_a_committed_output :
    readBoth emitThenDrop = ([⟨none, 7⟩], none) := by decide

/-- Negative: read after the second record, the late reading gives the
output; read after the third, it gives none. -/
theorem late_reading_depends_on_when :
    (readBoth (emitThenDrop.take 2)).2 = some [⟨none, 7⟩] ∧ (readBoth emitThenDrop).2 = none := by
  decide

/-- Positive: a stream that drops only an id it never emitted.  Both readings
give the same outputs, as `late_eq_committed_of_safe` says of every such
stream. -/
def emitThenDropOther : List (Record Unit) := [.define 0 (), .define 1 (), .emit 0, .label 0 "r", .drop 1]

theorem readings_agree_on_a_safe_stream :
    readBoth emitThenDropOther = ([⟨none, 7⟩, ⟨some "r", 7⟩], some [⟨none, 7⟩, ⟨some "r", 7⟩]) := by
  decide

theorem emitThenDropOther_safe : Safe ([] : List Nat) emitThenDropOther := by
  simp [Safe, emitThenDropOther]

theorem emitThenDrop_not_safe : ¬ Safe ([] : List Nat) emitThenDrop := by
  simp [Safe, emitThenDrop]

end Mettapedia.Languages.HOLLight.HOLRDeliveries
