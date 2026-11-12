import Mathlib.Data.List.Nodup

/-!
# Admitting waits on a shared mail service

A mail service that several accounts share lets a client wait: the service
holds the request until mail arrives or a timeout passes. Each held wait
occupies a slot of a fixed pool. A waiting client re-arms when its wait ends,
so a waiter that nobody reads any more still holds its slot.

**The rules in use.**
- `liveAdmit` holds any request while the pool has a free slot. Copies of one
  waiter fill the whole pool, and then every account is refused, the service's
  owner included (`live_copies_fill`, `live_copies_lock_out`).
- `cappedAdmit` adds a cap per account. One waiter's copies still lock out
  the other names of its own account (`capped_copies_lock_out_siblings`), and
  two accounts at their caps lock out a third
  (`capped_two_accounts_lock_out`).
- A write to an account's mail wakes every wait the account holds
  (`accountWakes`). With copies, one message wakes all of them (`live_wakes`).

**The repaired rule** (`admit`).
- A wait is keyed by its account and the name it waits on.
- A new wait replaces the held waits with its key. If one of them belongs to a
  newer waiter, the new wait is refused instead. The generation is the
  waiter's start, used like a fencing token.
- Each account has its own allowance of names.

**What the repaired rule guarantees.**
- A key holds at most one slot, however many copies of its waiter run
  (`keyed_run`, `key_holds_at_most_one`). So an account uses at most its
  allowance (`usage_run_le`).
- Whether a wait is admitted depends only on its own account's waits
  (`admit_isSome_own`). An account below its allowance is never locked out by
  others (`admitted_below_allowance`).
- A pool as large as the sum of the allowances is never the limit
  (`length_le_sum_allowance`).
- An older waiter cannot take a key from a newer one (`newer_kept`). A newer
  waiter's wait ends the older one's (`older_replaced`).
- A message for a key wakes at most one wait (`key_wakes_at_most_one`).
-/

namespace Mettapedia.Protocols.Mail.WaitAdmission

variable {P N : Type} [DecidableEq P] [DecidableEq N]

/-- A held wait: the account that asked, the name it waits on, and the
generation of the waiting client (when it started). -/
structure Wait (P N : Type) where
  account : P
  name : N
  generation : Nat
deriving DecidableEq

/-- The key a wait occupies: its account and name. -/
def Wait.key (w : Wait P N) : P × N := (w.account, w.name)

/-- The held waits. -/
abbrev Held (P N : Type) := List (Wait P N)

/-- Slots an account holds. -/
def usage (s : Held P N) (p : P) : Nat := s.countP (fun v => v.account = p)

/-- Process requests in order; a refused request leaves the held waits as
they were. -/
def run (admit : Held P N → Wait P N → Option (Held P N)) :
    Held P N → List (Wait P N) → Held P N
  | s, [] => s
  | s, w :: ws => run admit ((admit s w).getD s) ws

/-! ## The rules in use -/

/-- One pool of `C` slots for every account. Any request is held while a slot
is free, including another copy of a waiter already held. -/
def liveAdmit (C : Nat) (s : Held P N) (w : Wait P N) : Option (Held P N) :=
  if s.length < C then some (w :: s) else none

/-- The same pool, and at most `A` slots per account. -/
def cappedAdmit (C A : Nat) (s : Held P N) (w : Wait P N) : Option (Held P N) :=
  if s.length < C ∧ usage s w.account < A then some (w :: s) else none

omit [DecidableEq P] [DecidableEq N] in
theorem live_run_copies (C : Nat) (w : Wait P N) :
    ∀ k m, k + m ≤ C →
      run (liveAdmit C) (List.replicate k w) (List.replicate m w) =
        List.replicate (k + m) w := by
  intro k m
  induction m generalizing k with
  | zero => intro _; rfl
  | succ m ih =>
    intro h
    have hk : (List.replicate k w).length < C := by
      simp only [List.length_replicate]; omega
    simp only [List.replicate_succ, run, liveAdmit, hk, if_true, Option.getD_some]
    have := ih (k + 1) (by omega)
    rw [← List.replicate_succ] at *
    simpa [Nat.add_assoc, Nat.add_comm 1 m] using this

omit [DecidableEq P] [DecidableEq N] in
/-- Copies of one waiter fill the pool. -/
theorem live_copies_fill (C : Nat) (w : Wait P N) :
    run (liveAdmit C) [] (List.replicate C w) = List.replicate C w := by
  simpa using live_run_copies C w 0 C (by omega)

omit [DecidableEq P] [DecidableEq N] in
/-- Once copies of one waiter fill the pool, every request is refused,
whatever its account or name. -/
theorem live_copies_lock_out (C : Nat) (w v : Wait P N) :
    liveAdmit C (List.replicate C w) v = none := by
  simp [liveAdmit]

omit [DecidableEq N] in
/-- `A` copies of one waiter use its account's whole cap, so the account's
other names are refused. -/
theorem capped_copies_lock_out_siblings (C A : Nat) (w v : Wait P N)
    (hv : v.account = w.account) :
    cappedAdmit C A (List.replicate A w) v = none := by
  have : usage (List.replicate A w) v.account = A := by
    simp [usage, List.countP_replicate, hv]
  simp [cappedAdmit, this]

omit [DecidableEq N] in
/-- Two accounts at a cap of half the pool fill it, and a third account is
refused. -/
theorem capped_two_accounts_lock_out (A : Nat) (w v u : Wait P N) :
    cappedAdmit (A + A) A (List.replicate A w ++ List.replicate A v) u = none := by
  simp [cappedAdmit]

/-- The waits a write to account `p`'s mail wakes when waits watch the whole
account. -/
def accountWakes (s : Held P N) (p : P) : Held P N :=
  s.filter (fun v => v.account = p)

omit [DecidableEq N] in
/-- With copies, one message wakes every copy. -/
theorem live_wakes (n : Nat) (w : Wait P N) :
    (accountWakes (List.replicate n w) w.account).length = n := by
  simp [accountWakes]

/-! ## The repaired rule -/

/-- The held waits with keys other than `w`'s. -/
def others (s : Held P N) (w : Wait P N) : Held P N :=
  s.filter (fun v => v.key ≠ w.key)

/-- A held wait for `w`'s key belongs to a newer waiter. -/
def newerHeld (s : Held P N) (w : Wait P N) : Prop :=
  ∃ v ∈ s, v.key = w.key ∧ w.generation < v.generation

instance (s : Held P N) (w : Wait P N) : Decidable (newerHeld s w) := by
  unfold newerHeld; infer_instance

/-- A wait replaces the held waits with its key, unless one of them belongs
to a newer waiter. It is held while its account is below its allowance `Q`. -/
def admit (Q : P → Nat) (s : Held P N) (w : Wait P N) : Option (Held P N) :=
  if newerHeld s w then none
  else if usage (others s w) w.account < Q w.account then some (w :: others s w)
  else none

/-- No two held waits share a key. -/
def Keyed (s : Held P N) : Prop := (s.map Wait.key).Nodup

theorem key_not_mem_others (s : Held P N) (w : Wait P N) :
    w.key ∉ (others s w).map Wait.key := by
  simp [others, List.mem_map, List.mem_filter]

theorem others_sublist (s : Held P N) (w : Wait P N) : (others s w).Sublist s :=
  List.filter_sublist

theorem admit_keyed {Q : P → Nat} {s s' : Held P N} {w : Wait P N}
    (hs : Keyed s) (h : admit Q s w = some s') : Keyed s' := by
  unfold admit at h
  split_ifs at h with h₁ h₂
  cases h
  unfold Keyed
  rw [List.map_cons, List.nodup_cons]
  exact ⟨key_not_mem_others s w, hs.sublist ((others_sublist s w).map _)⟩

theorem run_keyed (Q : P → Nat) :
    ∀ (ws : List (Wait P N)) (s : Held P N), Keyed s → Keyed (run (admit Q) s ws)
  | [], _, hs => hs
  | w :: ws, s, hs => by
    unfold run
    cases h : admit Q s w with
    | none => exact run_keyed Q ws s hs
    | some s' => exact run_keyed Q ws s' (admit_keyed hs h)

/-- Every run of the repaired rule keeps one wait per key. -/
theorem keyed_run (Q : P → Nat) (ws : List (Wait P N)) :
    Keyed (run (admit Q) [] ws) :=
  run_keyed Q ws [] List.nodup_nil

/-- With one wait per key, a key holds at most one slot. -/
theorem key_holds_at_most_one {s : Held P N} (hs : Keyed s) (k : P × N) :
    s.countP (fun v => v.key = k) ≤ 1 := by
  have h := (List.nodup_iff_count_le_one.mp hs) k
  rw [List.count_eq_countP, List.countP_map] at h
  have e : s.countP (fun v => v.key = k) = s.countP ((fun x => x == k) ∘ Wait.key) := by
    apply List.countP_congr
    intro v _
    simp
  omega

/-- A message for a key wakes the waits with that key. -/
def keyWakes (s : Held P N) (k : P × N) : Held P N :=
  s.filter (fun v => v.key = k)

theorem key_wakes_at_most_one {s : Held P N} (hs : Keyed s) (k : P × N) :
    (keyWakes s k).length ≤ 1 := by
  simpa [keyWakes, List.countP_eq_length_filter] using key_holds_at_most_one hs k

theorem usage_others_le (s : Held P N) (w : Wait P N) (p : P) :
    usage (others s w) p ≤ usage s p := by
  unfold usage
  exact (others_sublist s w).countP_le

theorem admit_usage_le {Q : P → Nat} {s s' : Held P N} {w : Wait P N}
    (hs : ∀ p, usage s p ≤ Q p) (h : admit Q s w = some s') :
    ∀ p, usage s' p ≤ Q p := by
  unfold admit at h
  split_ifs at h with h₁ h₂
  cases h
  intro p
  by_cases hp : w.account = p
  · subst hp
    simp only [usage, List.countP_cons, decide_true, if_true] at h₂ ⊢
    omega
  · have := usage_others_le s w p
    have hq := hs p
    simp only [usage, List.countP_cons, hp, decide_false] at this hq ⊢
    simp
    omega

theorem run_usage_le (Q : P → Nat) :
    ∀ (ws : List (Wait P N)) (s : Held P N), (∀ p, usage s p ≤ Q p) →
      ∀ p, usage (run (admit Q) s ws) p ≤ Q p
  | [], _, hs => hs
  | w :: ws, s, hs => by
    unfold run
    cases h : admit Q s w with
    | none => exact run_usage_le Q ws s hs
    | some s' => exact run_usage_le Q ws s' (admit_usage_le hs h)

/-- Every account stays within its allowance, however many copies of its
waiters run. -/
theorem usage_run_le (Q : P → Nat) (ws : List (Wait P N)) (p : P) :
    usage (run (admit Q) [] ws) p ≤ Q p :=
  run_usage_le Q ws [] (by simp [usage]) p

/-- The waits an account holds. -/
def own (s : Held P N) (p : P) : Held P N := s.filter (fun v => v.account = p)

omit [DecidableEq N] in
theorem newerHeld_own (s : Held P N) (w : Wait P N) :
    newerHeld (own s w.account) w ↔ newerHeld s w := by
  unfold newerHeld own
  constructor
  · rintro ⟨v, hv, hk, hg⟩
    exact ⟨v, (List.mem_filter.mp hv).1, hk, hg⟩
  · rintro ⟨v, hv, hk, hg⟩
    have ha : v.account = w.account := congrArg Prod.fst hk
    exact ⟨v, List.mem_filter.mpr ⟨hv, by simpa using ha⟩, hk, hg⟩

theorem usage_others_own (s : Held P N) (w : Wait P N) :
    usage (others (own s w.account) w) w.account = usage (others s w) w.account := by
  unfold usage others own
  rw [List.filter_filter, List.countP_filter, List.countP_filter]
  congr 1
  funext v
  by_cases h : v.account = w.account <;> simp [h]

/-- Admission depends only on the waits of the requesting account. -/
theorem admit_isSome_own (Q : P → Nat) (s : Held P N) (w : Wait P N) :
    (admit Q (own s w.account) w).isSome = (admit Q s w).isSome := by
  unfold admit
  rw [usage_others_own]
  by_cases h : newerHeld s w
  · have h' : newerHeld (own s w.account) w := (newerHeld_own s w).mpr h
    simp [h, h']
  · have h' : ¬ newerHeld (own s w.account) w := fun hn => h ((newerHeld_own s w).mp hn)
    simp only [h, h', if_false]
    split_ifs <;> rfl

/-- An account below its allowance, with no newer waiter on the key, is
admitted, whatever other accounts hold. -/
theorem admitted_below_allowance (Q : P → Nat) (s : Held P N) (w : Wait P N)
    (hnew : ¬ newerHeld (own s w.account) w)
    (hroom : usage (others (own s w.account) w) w.account < Q w.account) :
    (admit Q s w).isSome := by
  rw [← admit_isSome_own]
  simp [admit, hnew, hroom]

/-- An older waiter cannot take a key from a newer one. -/
theorem newer_kept (Q : P → Nat) (s : Held P N) (v w : Wait P N)
    (hv : v ∈ s) (hk : v.key = w.key) (hg : w.generation < v.generation) :
    admit Q s w = none := by
  have : newerHeld s w := ⟨v, hv, hk, hg⟩
  simp [admit, this]

/-- A newer waiter's admitted wait ends every other held wait for its key. -/
theorem older_replaced {Q : P → Nat} {s s' : Held P N} {v w : Wait P N}
    (h : admit Q s w = some s') (hk : v.key = w.key) (hvw : v ≠ w) :
    v ∉ s' := by
  unfold admit at h
  split_ifs at h with h₁ h₂
  cases h
  simp [others, List.mem_filter, hk, hvw]

omit [DecidableEq P] [DecidableEq N] in
theorem sum_map_le {f g : P → Nat} :
    ∀ (l : List P), (∀ p, f p ≤ g p) → (l.map f).sum ≤ (l.map g).sum
  | [], _ => Nat.le_refl _
  | p :: ps, h => by
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h p) (sum_map_le ps h)

omit [DecidableEq N] in
theorem length_eq_sum_usage :
    ∀ (accts : List P) (s : Held P N), accts.Nodup →
      (∀ v ∈ s, v.account ∈ accts) →
      s.length = (accts.map (usage s)).sum
  | [], s, _, hs => by
    cases s with
    | nil => rfl
    | cons v _ => exact absurd (hs v List.mem_cons_self) (by simp)
  | p :: ps, s, hnd, hs => by
    have hnd' := List.nodup_cons.mp hnd
    have hrest : ∀ v ∈ s.filter (fun v => v.account ≠ p), v.account ∈ ps := by
      intro v hv
      have ⟨hvs, hvp⟩ := List.mem_filter.mp hv
      have := hs v hvs
      simp only [decide_eq_true_eq] at hvp
      rcases List.mem_cons.mp this with h | h
      · exact absurd h hvp
      · exact h
    have ih := length_eq_sum_usage ps _ hnd'.2 hrest
    have hsplit : s.length =
        s.countP (fun v => v.account = p) + (s.filter (fun v => v.account ≠ p)).length := by
      rw [← List.countP_eq_length_filter]
      have := List.length_eq_countP_add_countP (fun v : Wait P N => decide (v.account = p)) (l := s)
      simpa using this
    have hmap : ps.map (usage (s.filter (fun v => v.account ≠ p))) = ps.map (usage s) := by
      apply List.map_congr_left
      intro q hq
      have hqp : q ≠ p := fun h => hnd'.1 (h ▸ hq)
      unfold usage
      rw [List.countP_filter]
      congr 1
      funext v
      by_cases h : v.account = q
      · simp [h, hqp]
      · simp [h]
    rw [List.map_cons, List.sum_cons, hsplit, ih, hmap]
    rfl

omit [DecidableEq N] in
/-- With every held wait from a listed account and every account within its
allowance, a pool as large as the sum of the allowances has room for all of
them: the pool is never the limit. -/
theorem length_le_sum_allowance (Q : P → Nat) (accts : List P) (s : Held P N)
    (hnd : accts.Nodup) (hs : ∀ v ∈ s, v.account ∈ accts)
    (hq : ∀ p, usage s p ≤ Q p) :
    s.length ≤ (accts.map Q).sum := by
  rw [length_eq_sum_usage accts s hnd hs]
  exact sum_map_le accts (fun p => hq p)

end Mettapedia.Protocols.Mail.WaitAdmission
