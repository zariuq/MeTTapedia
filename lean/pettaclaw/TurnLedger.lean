/-!
# TurnLedger — the agent ledger's transitions and the promises they keep

The turn ledger records what happens to an agent's inputs, requests, turns
and commands. Its SQLite implementation spreads one meaning over many tables;
a native store must keep the same meaning. This file states the ledger as one
state machine and proves the promises any implementation has to keep:

* **No silent re-authorization.** Only deciding the pending captured turn
  creates an action (`new_action_only_by_decide`); recovery marks issued
  actions uncertain and never re-issues them (`never_back_to_issued`); each
  turn serial authorizes at most one action, because a pending serial never
  has one (`Inv.pending_fresh`).
* **Write-once results.** A recorded receipt never changes
  (`receipt_write_once`).
* **No achievement without a check.** A request becomes achieved only through
  a finish on an observed, successful receipt for that request
  (`achieved_only_by_check`); workflow dispositions never achieve.
* **Atomic checkpoint, and processed is forever.** A checkpoint sets the
  working set, settles its inputs and processes its request in one step
  (`checkpoint_commits_together`), and a processed input stays processed
  (`processed_monotone`).

Identifiers are natural numbers, a ticket is its turn serial, and a working
set or receipt payload is an opaque digest. The model covers the promises,
not the presentation queries.
-/

namespace TurnLedger

inductive RStatus where
  | active | processed | waitingUser | deferred | addressed | achieved | cancelled | covered
  deriving DecidableEq, Repr

inductive AStatus where
  | issued | uncertain | returned
  deriving DecidableEq, Repr

structure Receipt where
  payload : Nat
  returned : Bool    -- the result came back (not failed or uncertain)
  success : Bool     -- a trusted check attested domain success
  deriving DecidableEq, Repr

structure Action where
  request : Nat
  status : AStatus
  receipt : Option Receipt
  observed : Bool
  deriving DecidableEq, Repr

structure State where
  req : Nat → Option RStatus
  checked : Nat → Bool          -- the request has a configured checker
  act : Nat → Option Action     -- by ticket (= the turn serial)
  pending : Option Nat          -- the captured turn awaiting its decision
  nextSample : Nat
  processedIn : Nat → Bool      -- settled input identities
  working : Nat                 -- the current working set (a digest)
  focus : Nat                   -- the request a captured turn works on

def upd {β} (f : Nat → β) (k : Nat) (v : β) : Nat → β := fun x => if x = k then v else f x

/-- Workflow dispositions; none of them is an achievement. -/
inductive Disposition where
  | keep | waitingUser | defer | addressed | reopen
  deriving DecidableEq

def Disposition.status : Disposition → RStatus
  | .keep => .active | .waitingUser => .waitingUser | .defer => .deferred
  | .addressed => .addressed | .reopen => .active

def settle (f : Nat → Bool) : List Nat → Nat → Bool
  | [], x => f x
  | i :: is, x => if x = i then true else settle f is x

/-- One transition of the ledger. Each constructor is one transaction. -/
inductive Step : State → State → Prop where
  | accept (s : State) (r : Nat) (hnew : s.req r = none) :
      Step s { s with req := upd s.req r (some .active) }
  | capture (s : State) (focus : Nat) :
      Step s { s with pending := some s.nextSample, nextSample := s.nextSample + 1, focus := focus }
  | decideText (s : State) (t : Nat) (hp : s.pending = some t) :
      Step s { s with pending := none }
  | decideCommand (s : State) (t : Nat) (hp : s.pending = some t) :
      Step s { s with pending := none,
                      act := upd s.act t (some ⟨s.focus, .issued, none, false⟩) }
  | restore (s : State) :
      Step s { s with pending := none,
                      act := fun t => (s.act t).map fun a =>
                        if a.status = .issued then { a with status := .uncertain } else a }
  | report (s : State) (t : Nat) (a : Action) (r : Receipt)
      (ha : s.act t = some a) (hnone : a.receipt = none) (hst : a.status ≠ .returned) :
      Step s { s with act := upd s.act t (some { a with status := .returned, receipt := some r }) }
  | observe (s : State) (t : Nat) (a : Action) (r : Receipt)
      (ha : s.act t = some a) (hr : a.receipt = some r) :
      Step s { s with act := upd s.act t (some { a with observed := true }) }
  | attest (s : State) (t : Nat) (a : Action) (r : Receipt)
      (ha : s.act t = some a) (hr : a.receipt = some r) (hret : r.returned = true)
      (hobs : a.observed = true) (hact : s.req a.request = some .active) :
      Step s { s with act := upd s.act t (some { a with receipt := some { r with success := true } }) }
  | finish (s : State) (q t : Nat) (a : Action) (r : Receipt)
      (hq : s.req q = some .active) (ha : s.act t = some a) (hreq : a.request = q)
      (hobs : a.observed = true) (hr : a.receipt = some r) (hok : r.returned = true ∧ r.success = true)
      (hchk : s.checked q = true) :
      Step s { s with req := upd s.req q (some .achieved) }
  | dispose (s : State) (q : Nat) (d : Disposition) (st : RStatus)
      (hq : s.req q = some st) (hopen : st ≠ .achieved ∧ st ≠ .cancelled) :
      Step s { s with req := upd s.req q (some d.status) }
  | cancel (s : State) (q : Nat) (hq : s.req q = some .active) :
      Step s { s with req := upd s.req q (some .cancelled) }
  | checkpoint (s : State) (w : Nat) (ins : List Nat) (q : Option Nat) :
      Step s { s with working := w, processedIn := settle s.processedIn ins,
                      req := match q with
                        | some r => if s.req r = some .active then upd s.req r (some .processed) else s.req
                        | none => s.req }

/-! ## The invariant: tickets come from past turns, and the pending turn is fresh -/

structure Inv (s : State) : Prop where
  tickets_past : ∀ t, (s.act t).isSome → t < s.nextSample
  pending_fresh : ∀ p, s.pending = some p → s.act p = none ∧ p < s.nextSample

theorem upd_same {β} (f : Nat → β) (k : Nat) (v : β) : upd f k v k = v := by simp [upd]
theorem upd_other {β} (f : Nat → β) (k x : Nat) (v : β) (h : x ≠ k) : upd f k v x = f x := by simp [upd, h]

theorem Inv.step {s s' : State} (h : Step s s') (hi : Inv s) : Inv s' := by
  cases h with
  | accept => exact ⟨hi.tickets_past, hi.pending_fresh⟩
  | capture =>
    refine ⟨fun t ht => Nat.lt_succ_of_lt (hi.tickets_past t ht), ?_⟩
    intro p hp
    simp at hp; subst hp
    refine ⟨?_, Nat.lt_succ_self _⟩
    cases hx : s.act s.nextSample with
    | none => rfl
    | some v => have := hi.tickets_past s.nextSample (by rw [hx]; rfl); omega
  | decideText t hp => exact ⟨hi.tickets_past, fun p h => by simp at h⟩
  | decideCommand t hp =>
    refine ⟨?_, fun p h => by simp at h⟩
    intro x hx
    by_cases e : x = t
    · subst e; exact (hi.pending_fresh x hp).2
    · simp [upd_other _ _ _ _ e] at hx; exact hi.tickets_past x (by simpa using hx)
  | restore =>
    refine ⟨fun t ht => hi.tickets_past t (by simpa using ht), fun p h => by simp at h⟩
  | report t a r ha =>
    refine ⟨?_, ?_⟩
    · intro x hx
      by_cases e : x = t
      · subst e; exact hi.tickets_past x (by simp [ha])
      · simp [upd_other _ _ _ _ e] at hx; exact hi.tickets_past x (by simpa using hx)
    · intro p hp
      have ⟨hn, hl⟩ := hi.pending_fresh p hp
      refine ⟨?_, hl⟩
      have : p ≠ t := fun e => by subst e; simp [ha] at hn
      simp [upd_other _ _ _ _ this, hn]
  | observe t a r ha =>
    refine ⟨?_, ?_⟩
    · intro x hx
      by_cases e : x = t
      · subst e; exact hi.tickets_past x (by simp [ha])
      · simp [upd_other _ _ _ _ e] at hx; exact hi.tickets_past x (by simpa using hx)
    · intro p hp
      have ⟨hn, hl⟩ := hi.pending_fresh p hp
      refine ⟨?_, hl⟩
      have : p ≠ t := fun e => by subst e; simp [ha] at hn
      simp [upd_other _ _ _ _ this, hn]
  | attest t a r ha =>
    refine ⟨?_, ?_⟩
    · intro x hx
      by_cases e : x = t
      · subst e; exact hi.tickets_past x (by simp [ha])
      · simp [upd_other _ _ _ _ e] at hx; exact hi.tickets_past x (by simpa using hx)
    · intro p hp
      have ⟨hn, hl⟩ := hi.pending_fresh p hp
      refine ⟨?_, hl⟩
      have : p ≠ t := fun e => by subst e; simp [ha] at hn
      simp [upd_other _ _ _ _ this, hn]
  | finish => exact ⟨hi.tickets_past, hi.pending_fresh⟩
  | dispose => exact ⟨hi.tickets_past, hi.pending_fresh⟩
  | cancel => exact ⟨hi.tickets_past, hi.pending_fresh⟩
  | checkpoint => exact ⟨hi.tickets_past, hi.pending_fresh⟩

/-! ## No silent re-authorization -/

/-- A ticket that did not exist before a step exists after it only because the
step decided the pending captured turn as a command. -/
theorem new_action_only_by_decide {s s' : State} (h : Step s s') (t : Nat)
    (hbefore : s.act t = none) (hafter : (s'.act t).isSome) :
    s.pending = some t ∧ s'.pending = none := by
  cases h with
  | decideCommand u hp =>
    by_cases e : t = u
    · subst e; exact ⟨hp, rfl⟩
    · simp [upd_other _ _ _ _ e, hbefore] at hafter
  | restore => simp [hbefore] at hafter
  | report u a r ha =>
    by_cases e : t = u
    · subst e; simp [ha] at hbefore
    · simp [upd_other _ _ _ _ e, hbefore] at hafter
  | observe u a r ha =>
    by_cases e : t = u
    · subst e; simp [ha] at hbefore
    · simp [upd_other _ _ _ _ e, hbefore] at hafter
  | attest u a r ha =>
    by_cases e : t = u
    · subst e; simp [ha] at hbefore
    · simp [upd_other _ _ _ _ e, hbefore] at hafter
  | accept => simp [hbefore] at hafter
  | capture => simp [hbefore] at hafter
  | decideText => simp [hbefore] at hafter
  | finish => simp [hbefore] at hafter
  | dispose => simp [hbefore] at hafter
  | cancel => simp [hbefore] at hafter
  | checkpoint => simp [hbefore] at hafter

/-- An action that left the issued state never returns to it: recovering an
uncertain execution can resolve it, never re-issue it. -/
theorem never_back_to_issued {s s' : State} (h : Step s s') (hi : Inv s) (t : Nat) (a : Action)
    (ha : s.act t = some a) (hnot : a.status ≠ .issued) :
    ∀ a', s'.act t = some a' → a'.status ≠ .issued := by
  intro a' ha'
  cases h with
  | decideCommand u hp =>
    by_cases e : t = u
    · subst e; have := (hi.pending_fresh t hp).1; simp [this] at ha
    · simp [upd_other _ _ _ _ e, ha] at ha'; subst ha'; exact hnot
  | restore =>
    simp [ha] at ha'; subst ha'
    by_cases hs : a.status = .issued
    · exact absurd hs hnot
    · simp [hs, hnot]
  | report u b r hb =>
    by_cases e : t = u
    · subst e; simp [upd_same] at ha'; subst ha'; simp
    · simp [upd_other _ _ _ _ e, ha] at ha'; subst ha'; exact hnot
  | observe u b r hb =>
    by_cases e : t = u
    · subst e; simp [upd_same] at ha'; subst ha'; rw [hb] at ha; cases ha; simpa using hnot
    · simp [upd_other _ _ _ _ e, ha] at ha'; subst ha'; exact hnot
  | attest u b r hb =>
    by_cases e : t = u
    · subst e; simp [upd_same] at ha'; subst ha'; rw [hb] at ha; cases ha; simpa using hnot
    · simp [upd_other _ _ _ _ e, ha] at ha'; subst ha'; exact hnot
  | accept => simp [ha] at ha'; subst ha'; exact hnot
  | capture => simp [ha] at ha'; subst ha'; exact hnot
  | decideText => simp [ha] at ha'; subst ha'; exact hnot
  | finish => simp [ha] at ha'; subst ha'; exact hnot
  | dispose => simp [ha] at ha'; subst ha'; exact hnot
  | cancel => simp [ha] at ha'; subst ha'; exact hnot
  | checkpoint => simp [ha] at ha'; subst ha'; exact hnot

/-! ## Write-once results -/

/-- A recorded result keeps its payload through every step; attestation only
adds the success mark. -/
theorem receipt_write_once {s s' : State} (h : Step s s') (hi : Inv s) (t : Nat) (a : Action)
    (r : Receipt) (ha : s.act t = some a) (hr : a.receipt = some r) :
    ∃ a', s'.act t = some a' ∧ a'.receipt.map Receipt.payload = some r.payload := by
  cases h with
  | decideCommand u hp =>
    by_cases e : t = u
    · subst e; have := (hi.pending_fresh t hp).1; simp [this] at ha
    · exact ⟨a, by simp [upd_other _ _ _ _ e, ha], by simp [hr]⟩
  | restore =>
    refine ⟨if a.status = .issued then { a with status := .uncertain } else a, by simp [ha], ?_⟩
    by_cases hs : a.status = .issued <;> simp [hs, hr]
  | report u b r' hb hnone =>
    by_cases e : t = u
    · subst e; rw [hb] at ha; cases ha; simp [hr] at hnone
    · exact ⟨a, by simp [upd_other _ _ _ _ e, ha], by simp [hr]⟩
  | observe u b r' hb =>
    by_cases e : t = u
    · subst e; rw [hb] at ha; cases ha; exact ⟨_, upd_same _ _ _, by simp [hr]⟩
    · exact ⟨a, by simp [upd_other _ _ _ _ e, ha], by simp [hr]⟩
  | attest u b r' hb hr' =>
    by_cases e : t = u
    · subst e; rw [hb] at ha; cases ha; rw [hr] at hr'; cases hr'
      exact ⟨_, upd_same _ _ _, by simp⟩
    · exact ⟨a, by simp [upd_other _ _ _ _ e, ha], by simp [hr]⟩
  | accept => exact ⟨a, ha, by simp [hr]⟩
  | capture => exact ⟨a, ha, by simp [hr]⟩
  | decideText => exact ⟨a, ha, by simp [hr]⟩
  | finish => exact ⟨a, ha, by simp [hr]⟩
  | dispose => exact ⟨a, ha, by simp [hr]⟩
  | cancel => exact ⟨a, ha, by simp [hr]⟩
  | checkpoint => exact ⟨a, ha, by simp [hr]⟩

/-! ## No achievement without a check -/

/-- A request that becomes achieved does so by a finish: its own observed
action carries a returned, successful receipt and the request has a checker.
No disposition, cancellation or checkpoint achieves. -/
theorem achieved_only_by_check {s s' : State} (h : Step s s') (q : Nat)
    (hbefore : s.req q ≠ some .achieved) (hafter : s'.req q = some .achieved) :
    ∃ t a r, s.act t = some a ∧ a.request = q ∧ a.observed = true ∧
      a.receipt = some r ∧ r.returned = true ∧ r.success = true ∧ s.checked q = true := by
  cases h with
  | finish q' t a r hq ha hreq hobs hr hok hchk =>
    by_cases e : q = q'
    · subst e; exact ⟨t, a, r, ha, hreq, hobs, hr, hok.1, hok.2, hchk⟩
    · simp [upd_other _ _ _ _ e] at hafter; exact absurd hafter hbefore
  | accept r hnew =>
    by_cases e : q = r
    · subst e; simp [upd_same] at hafter
    · simp [upd_other _ _ _ _ e] at hafter; exact absurd hafter hbefore
  | dispose q' d st hq hopen =>
    by_cases e : q = q'
    · subst e; simp [upd_same] at hafter; cases d <;> simp [Disposition.status] at hafter
    · simp [upd_other _ _ _ _ e] at hafter; exact absurd hafter hbefore
  | cancel q' hq =>
    by_cases e : q = q'
    · subst e; simp [upd_same] at hafter
    · simp [upd_other _ _ _ _ e] at hafter; exact absurd hafter hbefore
  | checkpoint w ins qo =>
    cases qo with
    | none => exact absurd hafter hbefore
    | some r =>
      simp only at hafter
      split at hafter
      · by_cases e : q = r
        · subst e; simp [upd_same] at hafter
        · simp [upd_other _ _ _ _ e] at hafter; exact absurd hafter hbefore
      · exact absurd hafter hbefore
  | capture => exact absurd hafter hbefore
  | decideText => exact absurd hafter hbefore
  | decideCommand => exact absurd hafter hbefore
  | restore => exact absurd hafter hbefore
  | report => exact absurd hafter hbefore
  | observe => exact absurd hafter hbefore
  | attest => exact absurd hafter hbefore

/-! ## Atomic checkpoint, and processed is forever -/

theorem settle_mem (f : Nat → Bool) (ins : List Nat) (i : Nat) (h : i ∈ ins) : settle f ins i = true := by
  induction ins with
  | nil => simp at h
  | cons x xs ih =>
    simp only [settle]
    by_cases e : i = x
    · simp [e]
    · simp [e]; exact ih (by simpa [e] using h)

theorem settle_keeps (f : Nat → Bool) (ins : List Nat) (i : Nat) (h : f i = true) : settle f ins i = true := by
  induction ins with
  | nil => simpa [settle] using h
  | cons x xs ih => simp only [settle]; split <;> simp_all

/-- One checkpoint step sets the working set, settles every listed input and
processes its active request: there is no state in which only some of these
hold. -/
theorem checkpoint_commits_together (s : State) (w : Nat) (ins : List Nat) (q : Nat)
    (hq : s.req q = some .active) :
    let s' : State := { s with working := w, processedIn := settle s.processedIn ins,
                               req := if s.req q = some .active then upd s.req q (some .processed) else s.req }
    s'.working = w ∧ (∀ i ∈ ins, s'.processedIn i = true) ∧ s'.req q = some .processed := by
  refine ⟨rfl, fun i hi => settle_mem _ _ _ hi, ?_⟩
  simp [hq, upd_same]

/-- A settled input stays settled across every step, so it is never presented
to cognition again. -/
theorem processed_monotone {s s' : State} (h : Step s s') (i : Nat) (hp : s.processedIn i = true) :
    s'.processedIn i = true := by
  cases h with
  | checkpoint w ins q => exact settle_keeps _ _ _ hp
  | _ => exact hp

end TurnLedger

#print axioms TurnLedger.Inv.step
#print axioms TurnLedger.new_action_only_by_decide
#print axioms TurnLedger.never_back_to_issued
#print axioms TurnLedger.receipt_write_once
#print axioms TurnLedger.achieved_only_by_check
#print axioms TurnLedger.checkpoint_commits_together
#print axioms TurnLedger.processed_monotone
