/-!
# The LLM call ledger as native transitions

The agent's LLM ledger (requests, call lifetimes, the call history and provider cooldowns) moved from
a SQLite file to transitions of the agent's native store. The live code's operations are kept; what
changes is where their transaction boundaries are.

* The host's Python path completed a request and settled its call in two transactions. A crash
  between them left a durable state in which the request is completed and its call is still active.
  The native completion is one transition, so no durable state of a native run has that shape
  (`split_completion_exposes`, `native_completion_closes`). The same holds for a failure and its
  call (`split_failure_exposes`, `native_failure_closes`).
* The native completion asks for the call's epoch where the Python path asked nothing: with the epoch
  owning the active call it is exactly the two steps in sequence (`native_complete_refines`); a stale
  epoch changes nothing (`stale_epoch_changes_nothing`).
* A request's failure and its provider's cooldown commit together, and a cooldown never shortens
  (`cooldown_monotone`, `native_fail_cools`).
* The history keeps the first event of each (call, event) pair (`event_first_wins`), and an
  operation repeated under its request id returns its first answer without a second effect
  (`replay_idempotent`).
* The status listing reads a newest-first list of the turn calls: inserting a call keeps it ordered
  by creation time, calls of one time in their arrival order, as SQLite's index lists them
  (`insert_sorted`, `insert_perm`, `insert_ties_after`).

Scope: requests, calls and cooldowns are abstracted to their status fields and one cooldown per
provider; the store's transaction is modelled as one function application. It says nothing about the
engine's commit or about the provider's side of a call.
-/

namespace PettaClaw.LlmLedger

inductive RStatus where
  | pending | completed | failed | unknown
  deriving DecidableEq, Repr

inductive CState where
  | claimed | submitted | completed | failed | uncertain | abandoned | late
  deriving DecidableEq, Repr

def CState.active : CState → Bool
  | .claimed => true
  | .submitted => true
  | _ => false

structure Call where
  epoch : Nat
  state : CState
  deriving DecidableEq, Repr

structure Ledger where
  request : Nat → Option RStatus
  call : Nat → Option Call
  provider : Nat → Nat
  cooldown : Nat → Nat

def setRequest (s : Ledger) (t : Nat) (r : RStatus) : Ledger :=
  { s with request := fun u => if u = t then some r else s.request u }

def setCall (s : Ledger) (t : Nat) (c : Call) : Ledger :=
  { s with call := fun u => if u = t then some c else s.call u }

/-- The call of `t` is active and held by epoch `e`. -/
def owns (s : Ledger) (t e : Nat) : Prop :=
  ∃ c, s.call t = some c ∧ c.epoch = e ∧ c.state.active = true

instance (s : Ledger) (t e : Nat) : Decidable (owns s t e) :=
  match h : s.call t with
  | none => isFalse (by intro ⟨c, hc, _⟩; rw [h] at hc; cases hc)
  | some c =>
    if he : c.epoch = e ∧ c.state.active = true then isTrue ⟨c, h, he.1, he.2⟩
    else isFalse (by
      intro ⟨c', hc, h1, h2⟩
      rw [h] at hc; cases hc; exact he ⟨h1, h2⟩)

/-- A completed request whose call is still active: the window the split path leaves. -/
def exposed (s : Ledger) (t : Nat) : Prop :=
  (s.request t = some .completed ∨ s.request t = some .failed) ∧ ∃ c, s.call t = some c ∧ c.state.active = true

/-! ## The SQLite path's two steps and the native transition -/

/-- llm_policy.complete: a pending request completes (no epoch is asked). -/
def completeRequest (s : Ledger) (t : Nat) : Ledger :=
  if s.request t = some .pending then setRequest s t .completed else s

/-- native_lifetime.settle(completed): the active call of epoch `e` completes. -/
def settleCall (s : Ledger) (t e : Nat) (to : CState) : Ledger :=
  match s.call t with
  | some c => if c.epoch = e ∧ c.state.active = true then setCall s t { c with state := to } else s
  | none => s

/-- llm-complete with an epoch: both, or nothing, in one transition. -/
def nativeComplete (s : Ledger) (t e : Nat) : Ledger :=
  if s.request t = some .pending ∧ owns s t e then settleCall (setRequest s t .completed) t e .completed else s

theorem settleCall_request (s : Ledger) (t e : Nat) (to : CState) :
    (settleCall s t e to).request = s.request := by
  unfold settleCall; split
  · split <;> rfl
  · rfl

theorem setRequest_call (s : Ledger) (t : Nat) (r : RStatus) : (setRequest s t r).call = s.call := rfl

theorem native_complete_refines (s : Ledger) (t e : Nat)
    (hp : s.request t = some .pending) (ho : owns s t e) :
    nativeComplete s t e = settleCall (completeRequest s t) t e .completed := by
  simp [nativeComplete, completeRequest, hp, ho]

theorem stale_epoch_changes_nothing (s : Ledger) (t e : Nat) (ho : ¬ owns s t e) :
    nativeComplete s t e = s := by
  simp [nativeComplete, ho]

/-- The durable states of a run that may stop after any transaction: the start and each prefix. -/
def splitStates (s : Ledger) (t e : Nat) : List Ledger :=
  [s, completeRequest s t, settleCall (completeRequest s t) t e .completed]

def nativeStates (s : Ledger) (t e : Nat) : List Ledger := [s, nativeComplete s t e]

theorem split_completion_exposes (s : Ledger) (t e : Nat)
    (hp : s.request t = some .pending) (ho : owns s t e) :
    ∃ m ∈ splitStates s t e, exposed m t := by
  obtain ⟨c, hc, _, ha⟩ := ho
  refine ⟨completeRequest s t, by simp [splitStates], ?_, ?_⟩
  · left; simp [completeRequest, hp, setRequest]
  · exact ⟨c, by simp [completeRequest, hp, setRequest, hc], ha⟩

theorem setCall_same (s : Ledger) (t : Nat) (c : Call) : (setCall s t c).call t = some c := by
  simp [setCall]

theorem native_completion_closes (s : Ledger) (t e : Nat) (h0 : ¬ exposed s t) :
    ∀ m ∈ nativeStates s t e, ¬ exposed m t := by
  intro m hm
  simp [nativeStates] at hm
  rcases hm with rfl | rfl
  · exact h0
  · unfold nativeComplete
    split
    · rename_i h
      obtain ⟨_, c, hc, he, ha⟩ := h
      intro ⟨_, c', hc', ha'⟩
      have : (settleCall (setRequest s t .completed) t e .completed).call t
          = some { c with state := .completed } := by
        simp [settleCall, setRequest_call, hc, he, ha, setCall]
      rw [this] at hc'; cases hc'; simp [CState.active] at ha'
    · exact h0

/-! ## Failure: the request, its event's effect and the cooldown together -/

/-- llm_policy.fail: a pending request fails and, for a managed 402/429, raises its provider's
cooldown to `till` (never lowering it). -/
def raise (s : Ledger) (p till : Nat) : Ledger :=
  { s with cooldown := fun q => if q = p then max (s.cooldown q) till else s.cooldown q }

def failRequest (s : Ledger) (t till : Nat) : Ledger :=
  if s.request t = some .pending then raise (setRequest s t .failed) (s.provider t) till else s

def nativeFail (s : Ledger) (t e till : Nat) (to : CState) : Ledger :=
  if s.request t = some .pending ∧ owns s t e then settleCall (failRequest s t till) t e to else s

theorem cooldown_monotone (s : Ledger) (p till q : Nat) : s.cooldown q ≤ (raise s p till).cooldown q := by
  simp only [raise]; split
  · exact Nat.le_max_left _ _
  · exact Nat.le_refl _

theorem settleCall_cooldown (s : Ledger) (t e : Nat) (to : CState) :
    (settleCall s t e to).cooldown = s.cooldown := by
  unfold settleCall; split
  · split <;> rfl
  · rfl

theorem native_fail_cools (s : Ledger) (t e till : Nat)
    (hp : s.request t = some .pending) (ho : owns s t e) (to : CState) :
    (nativeFail s t e till to).request t = some .failed ∧ till ≤ (nativeFail s t e till to).cooldown (s.provider t) := by
  simp only [nativeFail, hp, ho, and_self, if_true]
  constructor
  · rw [settleCall_request]; simp [failRequest, hp, raise, setRequest]
  · rw [settleCall_cooldown]; simp [failRequest, hp, raise]; exact Nat.le_max_right _ _

def splitFailStates (s : Ledger) (t e till : Nat) (to : CState) : List Ledger :=
  [s, failRequest s t till, settleCall (failRequest s t till) t e to]

theorem split_failure_exposes (s : Ledger) (t e till : Nat)
    (hp : s.request t = some .pending) (ho : owns s t e) (to : CState) :
    ∃ m ∈ splitFailStates s t e till to, exposed m t := by
  obtain ⟨c, hc, _, ha⟩ := ho
  refine ⟨failRequest s t till, by simp [splitFailStates], ?_, ?_⟩
  · right; simp [failRequest, hp, raise, setRequest]
  · exact ⟨c, by simp [failRequest, hp, raise, setRequest, hc], ha⟩

theorem native_failure_closes (s : Ledger) (t e till : Nat) (to : CState) (hto : to.active = false)
    (h0 : ¬ exposed s t) : ∀ m ∈ [s, nativeFail s t e till to], ¬ exposed m t := by
  intro m hm
  simp at hm
  rcases hm with rfl | rfl
  · exact h0
  · unfold nativeFail
    split
    · rename_i h
      obtain ⟨hp, c, hc, he, ha⟩ := h
      intro ⟨_, c', hc', ha'⟩
      have hcall : (failRequest s t till).call t = some c := by
        simp [failRequest, hp, raise, setRequest, hc]
      have : (settleCall (failRequest s t till) t e to).call t = some { c with state := to } := by
        simp [settleCall, hcall, he, ha, setCall]
      rw [this] at hc'; cases hc'; simp [hto] at ha'
    · exact h0

/-! ## The history and the receipts -/

/-- INSERT OR IGNORE under UNIQUE(call, event): the first detail of a pair stays. -/
def addEvent (h : List (Nat × Nat × String)) (call event : Nat) (detail : String) : List (Nat × Nat × String) :=
  if h.any (fun x => x.1 = call ∧ x.2.1 = event) then h else h ++ [(call, event, detail)]

theorem event_first_wins (h : List (Nat × Nat × String)) (call event : Nat) (d₁ d₂ : String) :
    addEvent (addEvent h call event d₁) call event d₂ = addEvent h call event d₁ := by
  unfold addEvent
  split
  · simp_all
  · simp

/-- A write under a request id: a recorded receipt answers for it (the same operation), a new one
runs the operation and records its answer. -/
structure Receipts (σ α : Type) where
  find : String → Option (Nat × α)

def apply {σ α : Type} (op : Nat) (f : σ → σ × α) (rq : String) (s : σ) (r : Receipts σ α) :
    σ × Option α × Receipts σ α :=
  match r.find rq with
  | some (op', a) => if op' = op then (s, some a, r) else (s, none, r)
  | none =>
    let (s', a) := f s
    (s', some a, { find := fun q => if q = rq then some (op, a) else r.find q })

theorem replay_idempotent {σ α : Type} (op : Nat) (f : σ → σ × α) (rq : String) (s : σ) (r : Receipts σ α) :
    let first := apply op f rq s r
    apply op f rq first.1 first.2.2 = (first.1, first.2.1, first.2.2) := by
  cases h : r.find rq with
  | some p =>
    obtain ⟨op', a⟩ := p
    by_cases hop : op' = op
    · simp [apply, h, hop]
    · simp [apply, h, hop]
  | none => simp [apply, h]

/-! ## The newest-first list of the turn calls -/

/-- Newest first; a new call goes after every call created at or after its time. -/
def insert (x : Nat × Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [x]
  | y :: ys => if y.2 < x.2 then x :: y :: ys else y :: insert x ys

/-- Non-increasing creation times. -/
def Sorted : List (Nat × Nat) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => b.2 ≤ a.2 ∧ Sorted (b :: rest)

theorem sorted_tail {a : Nat × Nat} {l : List (Nat × Nat)} (h : Sorted (a :: l)) : Sorted l := by
  cases l with
  | nil => trivial
  | cons b rest => exact h.2

theorem insert_head (x y : Nat × Nat) (ys : List (Nat × Nat)) :
    (insert x (y :: ys)).head? = some x ∨ (insert x (y :: ys)).head? = some y := by
  unfold insert; split <;> simp

theorem sorted_cons (a : Nat × Nat) : ∀ l, Sorted l → (∀ b, l.head? = some b → b.2 ≤ a.2) → Sorted (a :: l)
  | [], _, _ => trivial
  | b :: _, hl, hh => ⟨hh b rfl, hl⟩

theorem insert_sorted (x : Nat × Nat) : ∀ l, Sorted l → Sorted (insert x l)
  | [], _ => trivial
  | y :: ys, h => by
    unfold insert
    split
    · rename_i hlt
      exact sorted_cons x (y :: ys) h (fun b hb => by cases hb; exact Nat.le_of_lt hlt)
    · rename_i hge
      have hle : x.2 ≤ y.2 := Nat.le_of_not_lt hge
      refine sorted_cons y (insert x ys) (insert_sorted x ys (sorted_tail h)) ?_
      intro b hb
      cases ys with
      | nil => simp [insert] at hb; subst hb; exact hle
      | cons z zs =>
        rcases insert_head x z zs with hx | hz
        · rw [hx] at hb; cases hb; exact hle
        · rw [hz] at hb; cases hb; exact h.1

theorem insert_perm (x : Nat × Nat) : ∀ l, List.Perm (insert x l) (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insert; split
    · exact List.Perm.refl _
    · exact (List.Perm.cons y (insert_perm x ys)).trans (List.Perm.swap x y ys)

/-- Calls created at x's time, or later, all stay in front of x: ties keep their arrival order. -/
theorem insert_ties_after (x : Nat × Nat) : ∀ l, Sorted l →
    insert x l = l.takeWhile (fun y => decide (x.2 ≤ y.2)) ++ x :: l.dropWhile (fun y => decide (x.2 ≤ y.2))
  | [], _ => rfl
  | y :: ys, h => by
    unfold insert
    split
    · rename_i hlt
      have : ¬ x.2 ≤ y.2 := Nat.not_le_of_lt hlt
      simp [List.takeWhile, List.dropWhile, this]
    · rename_i hge
      have hle : x.2 ≤ y.2 := Nat.le_of_not_lt hge
      rw [insert_ties_after x ys (sorted_tail h)]
      simp [List.takeWhile, List.dropWhile, hle]

#print axioms native_complete_refines
#print axioms stale_epoch_changes_nothing
#print axioms split_completion_exposes
#print axioms native_completion_closes
#print axioms cooldown_monotone
#print axioms native_fail_cools
#print axioms split_failure_exposes
#print axioms native_failure_closes
#print axioms event_first_wins
#print axioms replay_idempotent
#print axioms insert_sorted
#print axioms insert_perm
#print axioms insert_ties_after

end PettaClaw.LlmLedger
