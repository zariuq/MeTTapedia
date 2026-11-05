/-!
# ObservedReceipts — a result counts as seen once an answered prompt carried it

An action's receipt is its command results, written once. The ledger marks an
action *observed* when the model has been shown those results, and two
things depend on that mark (`TurnLedger.attest`, `TurnLedger.finish`):

* a trusted check may attest a receipt, and a checker may finish its request,
  only when the action is observed: work is never closed on results the model
  did not see;
* the protected request view lists, after the focus's newest receipt, the
  oldest receipts not yet observed (`inView`): results still waiting to be
  seen.

The model sees results in the prompts it answers. Here `send marks s p` is one
answered prompt: `p t i` says the prompt carried call `i` of action `t` with
its result, and `presents` holds when it carried every recorded call of an
action that has its receipt. A ghost field `shown` remembers every action an
answered prompt presented.

* **The defect** (`marks = false`, the ledger since the observe call was
  removed): no step marks anything, so no action created since stays
  observed-free forever (`unmarked_never_observes`), however often its results
  are shown. Then nothing created since can be attested or finished
  (`unmarked_never_checkable`), a shown action stays unobserved
  (`unmarked_shown_not_observed`: a concrete four-step trace), and once two
  receipts wait, no later receipt ever enters the view, not even the focus's
  newest (`unmarked_view_starves`).
* **The fix** (`marks = true`): an answered prompt marks what it presented.
  Observed then means exactly shown (`marked_observed_iff_shown`): nothing is
  marked that was not shown, and everything shown is marked. A shown action
  with its receipt is checkable for good (`marked_shown_checkable`), and the
  view's waiting receipts are exactly those never shown
  (`marked_view_unseen`).

Tickets are natural numbers handed out in order, a receipt is an opaque digest
and a request an identifier.
-/

namespace ObservedReceipts

structure Action where
  request : Nat
  calls : List Nat          -- the positions whose results are recorded
  receipt : Option Nat      -- the results' digest, written once
  observed : Bool
  deriving DecidableEq, Repr

structure State where
  act : Nat → Option Action   -- by ticket
  next : Nat                  -- the next ticket
  shown : Nat → Bool          -- ghost: an answered prompt presented the action

def upd {β} (f : Nat → β) (k : Nat) (v : β) : Nat → β := fun x => if x = k then v else f x

theorem upd_same {β} (f : Nat → β) (k : Nat) (v : β) : upd f k v k = v := by simp [upd]
theorem upd_other {β} (f : Nat → β) (k x : Nat) (v : β) (h : x ≠ k) : upd f k v x = f x := by
  simp [upd, h]

/-- The prompt carried every recorded result of action `t`, which has its receipt. -/
def presents (s : State) (p : Nat → Nat → Bool) (t : Nat) : Bool :=
  match s.act t with
  | some a => a.receipt.isSome && !a.calls.isEmpty && a.calls.all (p t)
  | none => false

/-- One answered prompt; `marks` says whether it marks what it presented. -/
def send (marks : Bool) (s : State) (p : Nat → Nat → Bool) : State :=
  { s with
    act := fun t => if marks && presents s p t then (s.act t).map (fun a => { a with observed := true })
                    else s.act t,
    shown := fun t => s.shown t || presents s p t }

inductive Step (marks : Bool) : State → State → Prop where
  | decide (s : State) (q : Nat) :
      Step marks s { s with act := upd s.act s.next (some ⟨q, [], none, false⟩), next := s.next + 1 }
  | attempt (s : State) (t i : Nat) (a : Action) (ha : s.act t = some a) (hr : a.receipt = none) :
      Step marks s { s with act := upd s.act t (some { a with calls := i :: a.calls }) }
  | report (s : State) (t d : Nat) (a : Action) (ha : s.act t = some a) (hr : a.receipt = none) :
      Step marks s { s with act := upd s.act t (some { a with receipt := some d }) }
  | answer (s : State) (p : Nat → Nat → Bool) : Step marks s (send marks s p)

inductive Reach (marks : Bool) : State → State → Prop where
  | refl (s : State) : Reach marks s s
  | tail {s u v : State} : Reach marks s u → Step marks u v → Reach marks s v

/-- Attest and finish need an observed action with its receipt. -/
def checkable (s : State) (t : Nat) : Prop :=
  ∃ a, s.act t = some a ∧ a.observed = true ∧ a.receipt.isSome = true

/-- No ticket at or past `next` is in use, or was ever shown. -/
def Fresh (s : State) : Prop := ∀ t, s.next ≤ t → s.act t = none ∧ s.shown t = false

theorem Fresh.step {m : Bool} {s s' : State} (h : Step m s s') (hf : Fresh s) : Fresh s' := by
  cases h with
  | decide q =>
    intro t ht
    have hne : t ≠ s.next := by simp at ht; omega
    exact ⟨by simp [upd_other _ _ _ _ hne]; exact (hf t (by simp at ht; omega)).1,
           (hf t (by simp at ht; omega)).2⟩
  | attempt t' i a ha hr =>
    intro t ht
    have hne : t ≠ t' := fun e => by subst e; simp [(hf t ht).1] at ha
    exact ⟨by simp [upd_other _ _ _ _ hne]; exact (hf t ht).1, (hf t ht).2⟩
  | report t' d a ha hr =>
    intro t ht
    have hne : t ≠ t' := fun e => by subst e; simp [(hf t ht).1] at ha
    exact ⟨by simp [upd_other _ _ _ _ hne]; exact (hf t ht).1, (hf t ht).2⟩
  | answer p =>
    intro t ht
    have hp : presents s p t = false := by simp [presents, (hf t ht).1]
    refine ⟨?_, ?_⟩
    · simp [send, hp, (hf t ht).1]
    · simp [send, hp, (hf t ht).2]

theorem Fresh.reach {m : Bool} {s s' : State} (h : Reach m s s') (hf : Fresh s) : Fresh s' := by
  induction h with
  | refl => exact hf
  | tail _ hs ih => exact ih.step hs

/-! ## Facts every step keeps -/

/-- The receipt of an action is never lost or changed. -/
theorem receipt_kept {m : Bool} {s s' : State} (h : Step m s s') (hf : Fresh s) (t : Nat) (a : Action)
    (ha : s.act t = some a) (hr : a.receipt.isSome = true) :
    ∃ a', s'.act t = some a' ∧ a'.receipt = a.receipt := by
  cases h with
  | decide q =>
    have hne : t ≠ s.next := fun e => by subst e; simp [(hf s.next (Nat.le_refl _)).1] at ha
    exact ⟨a, by simp [upd_other _ _ _ _ hne, ha], rfl⟩
  | attempt t' i b hb hbr =>
    by_cases e : t = t'
    · subst e; rw [ha] at hb; cases hb; simp [hbr] at hr
    · exact ⟨a, by simp [upd_other _ _ _ _ e, ha], rfl⟩
  | report t' d b hb hbr =>
    by_cases e : t = t'
    · subst e; rw [ha] at hb; cases hb; simp [hbr] at hr
    · exact ⟨a, by simp [upd_other _ _ _ _ e, ha], rfl⟩
  | answer p =>
    by_cases hp : (m && presents s p t) = true
    · exact ⟨{ a with observed := true }, by simp only [send]; rw [if_pos hp, ha]; rfl, rfl⟩
    · exact ⟨a, by simp only [send]; rw [if_neg hp, ha], rfl⟩

theorem receipt_reach {m : Bool} {s s' : State} (h : Reach m s s') (hf : Fresh s) (t : Nat) (a : Action)
    (ha : s.act t = some a) (hr : a.receipt.isSome = true) :
    ∃ a', s'.act t = some a' ∧ a'.receipt = a.receipt := by
  induction h with
  | refl => exact ⟨a, ha, rfl⟩
  | tail hsu hs ih =>
    obtain ⟨b, hb, hbr⟩ := ih
    obtain ⟨c, hc, hcr⟩ := receipt_kept hs (hf.reach hsu) t b hb (by rw [hbr]; exact hr)
    exact ⟨c, hc, hcr.trans hbr⟩

theorem next_mono {m : Bool} {s s' : State} (h : Reach m s s') : s.next ≤ s'.next := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ hs ih => cases hs <;> simp_all [send] <;> omega

/-! ## The defect: an answered prompt that marks nothing -/

/-- Without marking, every step keeps an existing action's mark as it was. -/
theorem unmarked_step_keeps {s s' : State} (h : Step false s s') (hf : Fresh s) (t : Nat) (a : Action)
    (ha : s.act t = some a) : ∃ a', s'.act t = some a' ∧ a'.observed = a.observed := by
  cases h with
  | decide q =>
    have hne : t ≠ s.next := fun e => by subst e; simp [(hf s.next (Nat.le_refl _)).1] at ha
    exact ⟨a, by simp [upd_other _ _ _ _ hne, ha], rfl⟩
  | attempt t' i b hb hbr =>
    by_cases e : t = t'
    · subst e; rw [ha] at hb; cases hb; exact ⟨{ a with calls := i :: a.calls }, by simp [upd_same], rfl⟩
    · exact ⟨a, by simp [upd_other _ _ _ _ e, ha], rfl⟩
  | report t' d b hb hbr =>
    by_cases e : t = t'
    · subst e; rw [ha] at hb; cases hb; exact ⟨{ a with receipt := some d }, by simp [upd_same], rfl⟩
    · exact ⟨a, by simp [upd_other _ _ _ _ e, ha], rfl⟩
  | answer p => exact ⟨a, by simp [send, ha], rfl⟩

theorem unmarked_reach_keeps {s s' : State} (h : Reach false s s') (hf : Fresh s) (t : Nat) (a : Action)
    (ha : s.act t = some a) : ∃ a', s'.act t = some a' ∧ a'.observed = a.observed := by
  induction h with
  | refl => exact ⟨a, ha, rfl⟩
  | tail hsu hs ih =>
    obtain ⟨b, hb, hbo⟩ := ih
    obtain ⟨c, hc, hco⟩ := unmarked_step_keeps hs (hf.reach hsu) t b hb
    exact ⟨c, hc, hco.trans hbo⟩

/-- Without marking, no action created after `s` is ever observed. -/
theorem unmarked_never_observes {s s' : State} (h : Reach false s s') (hf : Fresh s) :
    ∀ t, s.next ≤ t → ∀ a, s'.act t = some a → a.observed = false := by
  induction h with
  | refl => intro t ht a ha; simp [(hf t ht).1] at ha
  | tail hsu hs ih =>
    rename_i u v
    intro t ht a ha
    have hfu := hf.reach hsu
    cases hs with
    | decide q =>
      by_cases e : t = u.next
      · subst e; simp [upd_same] at ha; rw [← ha]
      · simp [upd_other _ _ _ _ e] at ha; exact ih t ht a ha
    | attempt t' i b hb hbr =>
      by_cases e : t = t'
      · subst e; simp [upd_same] at ha; rw [← ha]; exact ih t ht b hb
      · simp [upd_other _ _ _ _ e] at ha; exact ih t ht a ha
    | report t' d b hb hbr =>
      by_cases e : t = t'
      · subst e; simp [upd_same] at ha; rw [← ha]; exact ih t ht b hb
      · simp [upd_other _ _ _ _ e] at ha; exact ih t ht a ha
    | answer p => simp [send] at ha; exact ih t ht a ha

/-- Without marking, nothing created after `s` can be attested or finished. -/
theorem unmarked_never_checkable {s s' : State} (h : Reach false s s') (hf : Fresh s) (t : Nat)
    (ht : s.next ≤ t) : ¬ checkable s' t := by
  rintro ⟨a, ha, hobs, _⟩
  rw [unmarked_never_observes h hf t ht a ha] at hobs
  exact Bool.false_ne_true hobs

/-- The empty ledger. -/
def empty : State := ⟨fun _ => none, 0, fun _ => false⟩

theorem empty_fresh : Fresh empty := fun _ _ => ⟨rfl, rfl⟩

/-- The defect occurs: decide, record one result, report it, answer a prompt that carried
it. The action was shown, is not observed, and is never checkable afterwards. -/
theorem unmarked_shown_not_observed :
    ∃ s, Reach false empty s ∧ s.shown 0 = true ∧
      (∀ a, s.act 0 = some a → a.observed = false) ∧ ∀ s', Reach false s s' → ¬ checkable s' 0 := by
  let s1 : State := { empty with act := upd empty.act 0 (some ⟨7, [], none, false⟩), next := 1 }
  let s2 : State := { s1 with act := upd s1.act 0 (some ⟨7, [0], none, false⟩) }
  let s3 : State := { s2 with act := upd s2.act 0 (some ⟨7, [0], some 42, false⟩) }
  let s4 : State := send false s3 (fun _ _ => true)
  have r1 : Reach false empty s1 := .tail (.refl _) (.decide empty 7)
  have r2 : Reach false empty s2 :=
    .tail r1 (.attempt s1 0 0 ⟨7, [], none, false⟩ (by simp [s1, upd_same]) rfl)
  have r3 : Reach false empty s3 :=
    .tail r2 (.report s2 0 42 ⟨7, [0], none, false⟩ (by simp [s2, upd_same]) rfl)
  have r4 : Reach false empty s4 := .tail r3 (.answer s3 _)
  refine ⟨s4, r4, ?_, ?_, ?_⟩
  · simp [s4, send, presents, s3, s2, s1, upd_same]
  · intro a ha; simp [s4, send, s3, upd_same] at ha; rw [← ha]
  · intro s' h' ⟨a, ha, hobs, _⟩
    have hf4 : Fresh s4 := empty_fresh.reach r4
    obtain ⟨b, hb, hbo⟩ := unmarked_reach_keeps h' hf4 0 ⟨7, [0], some 42, false⟩
      (by simp [s4, send, s3, upd_same])
    rw [ha] at hb; cases hb
    simp at hbo; rw [hbo] at hobs; exact Bool.false_ne_true hobs

/-! ## The protected view: the focus's newest receipt, then the oldest waiting -/

/-- Action `t` belongs to request `f` and has its receipt. -/
def ownReceipt (s : State) (f t : Nat) : Bool :=
  match s.act t with
  | some a => a.request == f && a.receipt.isSome
  | none => false

/-- `t` is the newest ticket of request `f` with a receipt. -/
def newestOwn (s : State) (f t : Nat) : Bool :=
  ownReceipt s f t && ((List.range s.next).all fun u => !(t < u && ownReceipt s f u))

/-- The SQL's `receipt IS NOT NULL AND (observed = 0 OR ticket = <focus's newest>)`. -/
def qualifies (s : State) (f t : Nat) : Bool :=
  match s.act t with
  | some a => a.receipt.isSome && (!a.observed || newestOwn s f t)
  | none => false

/-- How many tickets below `n` satisfy `q`. -/
def countBelow (q : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => countBelow q n + if q n then 1 else 0

theorem countBelow_mono (q : Nat → Bool) {m n : Nat} (h : m ≤ n) : countBelow q m ≤ countBelow q n := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => simp [countBelow]; omega

theorem countBelow_two (q : Nat → Bool) {a b n : Nat} (hab : a < b) (hbn : b < n)
    (ha : q a = true) (hb : q b = true) : 2 ≤ countBelow q n := by
  have h1 : 1 ≤ countBelow q (a + 1) := by simp [countBelow, ha]
  have h2 : countBelow q (a + 1) ≤ countBelow q b := countBelow_mono q hab
  have h3 : countBelow q b + 1 ≤ countBelow q (b + 1) := by simp [countBelow, hb]
  have h4 : countBelow q (b + 1) ≤ countBelow q n := countBelow_mono q hbn
  omega

/-- ORDER BY ticket LIMIT 2: a qualifying ticket with fewer than two qualifying before it. -/
def inView (s : State) (f t : Nat) : Prop :=
  qualifies s f t = true ∧ countBelow (qualifies s f) t < 2

theorem newestOwn_request {s : State} {f t : Nat} (h : newestOwn s f t = true) :
    ∃ a, s.act t = some a ∧ a.request = f := by
  simp only [newestOwn, Bool.and_eq_true] at h
  have := h.1
  unfold ownReceipt at this
  split at this
  · rename_i a ha; simp at this; exact ⟨a, ha, this.1⟩
  · simp at this

theorem waiting_qualifies {s : State} {f t : Nat} {a : Action} (ha : s.act t = some a)
    (hr : a.receipt.isSome = true) (ho : a.observed = false) : qualifies s f t = true := by
  simp [qualifies, ha, hr, ho]

/-- Without marking, two waiting receipts close the view: no later receipt ever enters
it, not even the focus's newest (the query keeps the first two by ticket). -/
theorem unmarked_view_starves {s s' : State} (h : Reach false s s') (hf : Fresh s) (f : Nat)
    {t₁ t₂ : Nat} {a₁ a₂ : Action} (h₁ : s.act t₁ = some a₁) (h₂ : s.act t₂ = some a₂) (hlt : t₁ < t₂)
    (hr₁ : a₁.receipt.isSome = true) (hr₂ : a₂.receipt.isSome = true)
    (ho₁ : a₁.observed = false) (ho₂ : a₂.observed = false)
    (t : Nat) (hlater : t₂ < t) : ¬ inView s' f t := by
  rintro ⟨hq, hcount⟩
  have keep : ∀ {u a}, s.act u = some a → a.receipt.isSome = true → a.observed = false →
      qualifies s' f u = true := by
    intro u a hu hr ho
    obtain ⟨b, hb, hbr⟩ := receipt_reach h hf u a hu hr
    obtain ⟨c, hc, hco⟩ := unmarked_reach_keeps h hf u a hu
    rw [hb] at hc; cases hc
    exact waiting_qualifies hb (by rw [hbr]; exact hr) (by rw [hco]; exact ho)
  have := countBelow_two (qualifies s' f) hlt hlater (keep h₁ hr₁ ho₁) (keep h₂ hr₂ ho₂)
  omega

/-! ## The fix: an answered prompt marks what it presented -/

/-- Observed exactly when shown, for every action. -/
def Sync (s : State) : Prop := ∀ t a, s.act t = some a → (a.observed = true ↔ s.shown t = true)

theorem empty_sync : Sync empty := fun _ _ h => by simp [empty] at h

theorem Sync.step {s s' : State} (h : Step true s s') (hf : Fresh s) (hs : Sync s) : Sync s' := by
  cases h with
  | decide q =>
    intro t a ha
    by_cases e : t = s.next
    · subst e; simp [upd_same] at ha; rw [← ha]; simp [(hf s.next (Nat.le_refl _)).2]
    · simp [upd_other _ _ _ _ e] at ha; exact hs t a ha
  | attempt t' i b hb hbr =>
    intro t a ha
    by_cases e : t = t'
    · subst e; simp [upd_same] at ha; rw [← ha]; exact hs t b hb
    · simp [upd_other _ _ _ _ e] at ha; exact hs t a ha
  | report t' d b hb hbr =>
    intro t a ha
    by_cases e : t = t'
    · subst e; simp [upd_same] at ha; rw [← ha]; exact hs t b hb
    · simp [upd_other _ _ _ _ e] at ha; exact hs t a ha
  | answer p =>
    intro t a ha
    cases hst : s.act t with
    | none =>
      have hp : presents s p t = false := by simp [presents, hst]
      simp [send, hp, hst] at ha
    | some b =>
      by_cases hp : presents s p t = true
      · simp [send, hp, hst] at ha; rw [← ha]; simp [send, hp]
      · have hp' : presents s p t = false := by simpa using hp
        simp [send, hp', hst] at ha; rw [← ha]; simp [send, hp']; exact Bool.eq_iff_iff.2 (hs t b hst)

theorem Sync.reach {s s' : State} (h : Reach true s s') (hf : Fresh s) (hs : Sync s) : Sync s' := by
  induction h with
  | refl => exact hs
  | tail hsu hst ih => exact Sync.step hst (hf.reach hsu) ih

/-- With marking, observed means shown: nothing is marked that an answered prompt did not
present, and everything one presented is marked. -/
theorem marked_observed_iff_shown {s : State} (h : Reach true empty s) (t : Nat) (a : Action)
    (ha : s.act t = some a) : a.observed = true ↔ s.shown t = true :=
  Sync.reach h empty_fresh empty_sync t a ha

/-- `shown` only grows. -/
theorem shown_mono {m : Bool} {s s' : State} (h : Reach m s s') (t : Nat) (hs : s.shown t = true) :
    s'.shown t = true := by
  induction h with
  | refl => exact hs
  | tail _ hst ih => cases hst <;> simp_all [send]

/-- With marking, a shown action with its receipt stays checkable. -/
theorem marked_shown_checkable {s s' : State} (h₀ : Reach true empty s) (h : Reach true s s')
    (t : Nat) (a : Action) (ha : s.act t = some a) (hr : a.receipt.isSome = true)
    (hshown : s.shown t = true) : checkable s' t := by
  have hall : Reach true empty s' := by
    clear ha hr hshown
    induction h with
    | refl => exact h₀
    | tail _ hst ih => exact .tail ih hst
  obtain ⟨b, hb, hbr⟩ := receipt_reach h (empty_fresh.reach h₀) t a ha hr
  exact ⟨b, hb, (marked_observed_iff_shown hall t b hb).2 (shown_mono h t hshown), by rw [hbr]; exact hr⟩

/-- With marking, the view's waiting receipts are exactly those never shown: apart from
the focus's newest, a receipt in the view has not been presented to the model. -/
theorem marked_view_unseen {s : State} (h : Reach true empty s) (f t : Nat) (hv : inView s f t) :
    newestOwn s f t = true ∨ s.shown t = false := by
  obtain ⟨hq, _⟩ := hv
  unfold qualifies at hq
  split at hq
  · rename_i a ha
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hq
    rcases hq.2 with ho | hn
    · right
      cases hsh : s.shown t
      · rfl
      · have hobs := (marked_observed_iff_shown h t a ha).2 hsh
        rw [ho] at hobs; exact absurd hobs (by decide)
    · left; exact hn
  · simp at hq

end ObservedReceipts

#print axioms ObservedReceipts.unmarked_never_observes
#print axioms ObservedReceipts.unmarked_never_checkable
#print axioms ObservedReceipts.unmarked_shown_not_observed
#print axioms ObservedReceipts.unmarked_view_starves
#print axioms ObservedReceipts.marked_observed_iff_shown
#print axioms ObservedReceipts.marked_shown_checkable
#print axioms ObservedReceipts.marked_view_unseen
