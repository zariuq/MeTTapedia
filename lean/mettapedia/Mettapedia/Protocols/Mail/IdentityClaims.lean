import Mathlib.Data.List.Nodup

/-!
# Agent identities: claims, fencing and adoption

An agent's work outlives its sessions. A session ends, is compacted or is
replaced, and the terminal window that showed it is renumbered or renamed.
So the name that others write to, and that waits are keyed by, belongs to an
identity rather than to a session. The identity holds an inbox, a profile
(what the agent is working on) and its waits. A session acts as the identity
while it holds the identity's current claim.

The rules:
- A claim is never refused (`claim_holds`). It issues the next generation and
  makes the claimant the holder. Claiming an idle identity is adoption.
  Claiming a held one supersedes its holder: there is no lock to wait on.
- An act as the identity (a wait, an acknowledgement, a profile update)
  carries the actor's generation. It is accepted exactly when the actor is
  the current holder with that generation (`act_accepted_iff`).
- The superseded holder's acts are refused from then on (`superseded`), so it
  learns that it no longer holds the name. The generation works as a fencing
  token.

The theorems:
- `run_unique_actor`: in any run, all accepted acts with one generation come
  from one session. Two sessions never act as one identity under the same
  claim.
- `claim_keeps_status`: a claim leaves the profile as it was, so an adopting
  session reads what its predecessor was doing. The inbox is keyed by the
  identity and no claim touches it.
- `run_keeps_status`: only the holder's own updates change the profile.
- `idle_of_quiet`: an identity whose holder has not acted for the lease
  length shows as idle. Idleness is shown, not enforced: adopting an identity
  that still has a live holder is allowed, and that holder is told.
-/

namespace Mettapedia.Protocols.Mail.IdentityClaims

variable {S Status : Type} [DecidableEq S]

/-- One identity's record: its holder (session and generation), the number of
generations issued, every claim made (generation and session), the profile,
and when the holder last acted. -/
structure Entry (S Status : Type) where
  holder : Option (S × Nat)
  issued : Nat
  claims : List (Nat × S)
  status : Status
  lastSeen : Nat

/-- An event on one identity. -/
inductive Event (S Status : Type) where
  | claim (s : S) (t : Nat)
  | act (s : S) (g : Nat) (t : Nat)
  | update (s : S) (g : Nat) (t : Nat) (status : Status)
  | release (s : S) (g : Nat)

/-- A claim issues the next generation to its claimant. -/
def claim (s : S) (t : Nat) (e : Entry S Status) : Entry S Status :=
  { e with holder := some (s, e.issued + 1), issued := e.issued + 1,
           claims := (e.issued + 1, s) :: e.claims, lastSeen := t }

/-- An act by the holder of the current claim; anything else is refused. -/
def act (s : S) (g t : Nat) (e : Entry S Status) : Option (Entry S Status) :=
  if e.holder = some (s, g) then some { e with lastSeen := t } else none

/-- A profile update by the holder of the current claim. -/
def update (s : S) (g t : Nat) (st : Status) (e : Entry S Status) :
    Option (Entry S Status) :=
  if e.holder = some (s, g) then some { e with lastSeen := t, status := st } else none

/-- The holder gives the identity up. -/
def release (s : S) (g : Nat) (e : Entry S Status) : Option (Entry S Status) :=
  if e.holder = some (s, g) then some { e with holder := none } else none

/-- One step, and the act it accepted, if any. -/
def step (e : Entry S Status) : Event S Status → Entry S Status × Option (S × Nat)
  | .claim s t => (claim s t e, none)
  | .act s g t => match act s g t e with
    | some e' => (e', some (s, g))
    | none => (e, none)
  | .update s g t st => match update s g t st e with
    | some e' => (e', some (s, g))
    | none => (e, none)
  | .release s g => ((release s g e).getD e, none)

/-- Run events in order, collecting the accepted acts. -/
def run : Entry S Status → List (Event S Status) → Entry S Status × List (S × Nat)
  | e, [] => (e, [])
  | e, ev :: evs =>
    let (e₁, a) := step e ev
    let (e₂, as) := run e₁ evs
    (e₂, a.toList ++ as)

/-- The record is coherent: the holder's claim is recorded, every recorded
generation was issued, and no generation was issued twice. -/
def Coherent (e : Entry S Status) : Prop :=
  (∀ h, e.holder = some h → (h.2, h.1) ∈ e.claims) ∧
  (∀ c ∈ e.claims, c.1 ≤ e.issued) ∧
  (e.claims.map Prod.fst).Nodup

omit [DecidableEq S] in
/-- A claim is never refused: the claimant holds the next generation. -/
theorem claim_holds (s : S) (t : Nat) (e : Entry S Status) :
    (claim s t e).holder = some (s, e.issued + 1) := rfl

theorem act_accepted_iff (s : S) (g t : Nat) (e : Entry S Status) :
    (act s g t e).isSome ↔ e.holder = some (s, g) := by
  unfold act; split_ifs with h <;> simp [h]

/-- After another claim, the previous holder's acts are refused. -/
theorem superseded (s s' : S) (g t t' : Nat) (e : Entry S Status)
    (hc : Coherent e) (hh : e.holder = some (s, g)) :
    act s g t' (claim s' t e) = none := by
  have hg : g ≤ e.issued := hc.2.1 (g, s) (hc.1 (s, g) hh)
  unfold act claim
  have : ¬ (some (s', e.issued + 1) = some (s, g)) := by
    intro h; cases h; omega
  simp [this]

omit [DecidableEq S] in
theorem claim_coherent (s : S) (t : Nat) {e : Entry S Status} (hc : Coherent e) :
    Coherent (claim s t e) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h hh
    simp only [claim, Option.some.injEq] at hh
    subst hh
    exact List.mem_cons_self
  · intro c hc'
    rcases List.mem_cons.mp hc' with h | h
    · subst h; exact Nat.le_refl _
    · exact Nat.le_succ_of_le (hc.2.1 c h)
  · simp only [claim, List.map_cons, List.nodup_cons]
    refine ⟨?_, hc.2.2⟩
    intro hm
    obtain ⟨c, hcm, hc1⟩ := List.mem_map.mp hm
    have := hc.2.1 c hcm
    omega

omit [DecidableEq S] in
/-- A claim leaves the profile as it was: an adopting session reads what its
predecessor was doing. -/
theorem claim_keeps_status (s : S) (t : Nat) (e : Entry S Status) :
    (claim s t e).status = e.status := rfl

theorem step_coherent {e : Entry S Status} (hc : Coherent e) (ev : Event S Status) :
    Coherent (step e ev).1 := by
  cases ev with
  | claim s t => exact claim_coherent s t hc
  | act s g t =>
    simp only [step]
    unfold act
    split_ifs with h
    · exact ⟨hc.1, hc.2.1, hc.2.2⟩
    · exact hc
  | update s g t st =>
    simp only [step]
    unfold update
    split_ifs with h
    · exact ⟨hc.1, hc.2.1, hc.2.2⟩
    · exact hc
  | release s g =>
    simp only [step]
    unfold release
    split_ifs with h
    · refine ⟨?_, hc.2.1, hc.2.2⟩
      intro h' hh; simp at hh
    · exact hc

/-- Claims are only ever added. -/
theorem step_claims_grow (e : Entry S Status) (ev : Event S Status) :
    ∀ c ∈ e.claims, c ∈ (step e ev).1.claims := by
  intro c hc
  cases ev with
  | claim s t => exact List.mem_cons_of_mem _ hc
  | act s g t =>
    simp only [step]; unfold act; split_ifs <;> exact hc
  | update s g t st =>
    simp only [step]; unfold update; split_ifs <;> exact hc
  | release s g =>
    simp only [step]; unfold release; split_ifs <;> exact hc

/-- An accepted act's generation and session form a recorded claim. -/
theorem step_accepted_claimed {e : Entry S Status} (hc : Coherent e)
    (ev : Event S Status) :
    ∀ a, (step e ev).2 = some a → (a.2, a.1) ∈ (step e ev).1.claims := by
  intro a ha
  cases ev with
  | claim s t => simp [step] at ha
  | act s g t =>
    simp only [step] at ha ⊢
    unfold act at ha ⊢
    split_ifs at ha ⊢ with h
    · simp only [Option.some.injEq] at ha
      subst ha
      exact hc.1 (s, g) h
  | update s g t st =>
    simp only [step] at ha ⊢
    unfold update at ha ⊢
    split_ifs at ha ⊢ with h
    · simp only [Option.some.injEq] at ha
      subst ha
      exact hc.1 (s, g) h
  | release s g => simp [step] at ha

theorem run_accepted_claimed :
    ∀ (evs : List (Event S Status)) (e : Entry S Status), Coherent e →
      Coherent (run e evs).1 ∧
      (∀ c ∈ e.claims, c ∈ (run e evs).1.claims) ∧
      (∀ a ∈ (run e evs).2, (a.2, a.1) ∈ (run e evs).1.claims)
  | [], e, hc => ⟨hc, fun _ h => h, by simp [run]⟩
  | ev :: evs, e, hc => by
    have hc₁ := step_coherent hc ev
    obtain ⟨hc₂, hgrow, hacc⟩ := run_accepted_claimed evs (step e ev).1 hc₁
    refine ⟨hc₂, fun c h => hgrow c (step_claims_grow e ev c h), ?_⟩
    intro a ha
    simp only [run, List.mem_append] at ha
    rcases ha with ha | ha
    · cases h : (step e ev).2 with
      | none => simp [h] at ha
      | some a' =>
        simp [h] at ha
        subst ha
        exact hgrow _ (step_accepted_claimed hc ev _ h)
    · exact hacc a ha

/-- In any run, all accepted acts with one generation come from one session. -/
theorem run_unique_actor (evs : List (Event S Status)) (e : Entry S Status)
    (hc : Coherent e) (s s' : S) (g : Nat)
    (h : (s, g) ∈ (run e evs).2) (h' : (s', g) ∈ (run e evs).2) : s = s' := by
  obtain ⟨hcoh, _, hacc⟩ := run_accepted_claimed evs e hc
  have m := hacc _ h
  have m' := hacc _ h'
  have hnd := hcoh.2.2
  have := List.inj_on_of_nodup_map hnd m m' rfl
  simpa using congrArg Prod.snd this

/-- Only the holder's own updates change the profile. -/
theorem step_status (e : Entry S Status) (ev : Event S Status) :
    (step e ev).1.status = e.status ∨
      ∃ s g t st, ev = .update s g t st ∧ e.holder = some (s, g) ∧
        (step e ev).1.status = st := by
  cases ev with
  | claim s t => left; rfl
  | act s g t => left; simp only [step]; unfold act; split_ifs <;> rfl
  | update s g t st =>
    simp only [step]; unfold update
    split_ifs with h
    · right; exact ⟨s, g, t, st, rfl, h, rfl⟩
    · left; rfl
  | release s g => left; simp only [step]; unfold release; split_ifs <;> rfl

/-- A run with no accepted profile update keeps the profile. -/
theorem run_keeps_status :
    ∀ (evs : List (Event S Status)) (e : Entry S Status),
      (∀ s g t st, Event.update s g t st ∉ evs) → (run e evs).1.status = e.status
  | [], _, _ => rfl
  | ev :: evs, e, hno => by
    have hrest : ∀ s g t st, Event.update s g t st ∉ evs :=
      fun s g t st hm => hno s g t st (List.mem_cons_of_mem _ hm)
    have ih := run_keeps_status evs (step e ev).1 hrest
    simp only [run]
    rw [ih]
    rcases step_status e ev with h | ⟨s, g, t, st, rfl, _, _⟩
    · exact h
    · exact absurd List.mem_cons_self (hno s g t st)

/-- An identity is idle when it has no holder, or its holder has not acted
for `T`. Idleness is shown, never enforced. -/
def idle (T t : Nat) (e : Entry S Status) : Bool :=
  e.holder.isNone || decide (e.lastSeen + T ≤ t)

omit [DecidableEq S] in
theorem idle_of_quiet (T t : Nat) (e : Entry S Status) (h : e.lastSeen + T ≤ t) :
    idle T t e = true := by
  simp [idle, h]

end Mettapedia.Protocols.Mail.IdentityClaims
