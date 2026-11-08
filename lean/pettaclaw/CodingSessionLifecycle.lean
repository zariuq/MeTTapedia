/-!
# Coding-session lifecycle: the resume check and the agent's view of his sessions

A coding session freezes a runtime bundle at first launch and resumes on it. Three things are
modelled here.

1. **What a resume on the pin needs**, as we state it: `SafeOnPin`. No worker runs. The
   bundle's files are present. It uses no retired service. Its engine binary exists and, if a
   hash was recorded, still has that hash.
2. **The classifier** (`classify`, `guard`). Under the given world, the guard is equivalent to
   `SafeOnPin` (`guard_iff_safe`). It refuses no resume that the predicate allows, and allows
   none that it forbids. Each refusal names a reason that holds in that world (`reason_holds`).
   Allowing a legacy pin that has no engine hash is a chosen policy. Such a pin is labelled
   `unverified`, never `resumable` (`unverified_is_not_resumable`). A dependency whose backend
   selection cannot be read is also shown `unverified` (`unknown_is_not_resumable`). Its resume
   is refused, retryably, because "legacy active" and "native but unreachable" look the same
   (`unknown_refused`). The display verdict and the permission are separate.
3. **The view.** The unbounded view lists every listed session (`view_complete`), only those
   (`view_sound`), and each at most once (`view_nodup`).
   * Recomputing it is idempotent: however many triggers ran, the snapshot is the view of the
     current state, so no queue accumulates (`level_triggered`). This is not a statement that a
     session is ever reviewed.
   * A running session is always listed (`running_listed`).
   * A held session stays out until its review date (`held_quiet_until_review`,
     `held_listed_when_due`). A session held without a date stays out until the agent changes
     the hold (`held_indefinitely_quiet`).
   * The view does not change between review dates (`view_stable_between_reviews`).
   * The rendered view is bounded. It shows a prefix of the lines, the number left out, and the
     count of every verdict over all sessions. A listed session is shown or counted as omitted
     (`shown_or_omitted`), and every session is counted under its verdict whatever the bound
     (`counted`). A long tail can stay hidden indefinitely. Nothing here is a fairness claim.

Scope: this is a model of the classifier and the view, not of real runs. Bundles, services and
engines are opaque numbers, and the world is one snapshot. Outside the model:
* whether the current code can decode a checkpoint;
* whether the retirement table lists every dependency of a bundle;
* whether the files read form a coherent snapshot;
* launch races;
* whether an unhashed legacy engine is the one a bundle was built with.
The effects of a run, the re-pin and the authority of a run are separate models
(`CodingSessionRepin`, `CodingSessionAuthority`).
-/

namespace PettaClaw.CodingSessionLifecycle

inductive Status where
  | running | done | failed | stopped | interrupted | archived
  deriving DecidableEq, Repr

/-- A pin: the frozen bundle, the services it depends on (by retirement id), the engine binary
it names and that binary's recorded hash, if any. -/
structure Pin where
  bundle : Nat
  uses : List Nat
  binary : Nat
  engine : Option Nat
  deriving DecidableEq, Repr

/-- A hold recorded by the agent: none, until a review day, or without a date. -/
inductive Hold where
  | free
  | reviewOn (day : Nat)
  | indefinite
  deriving DecidableEq, Repr

def Hold.due (today : Nat) : Hold → Bool
  | .free => true
  | .reviewOn d => decide (d ≤ today)
  | .indefinite => false

structure Session where
  id : Nat
  status : Status
  pin : Option Pin
  /-- The bundle's files are present on disk. -/
  present : Bool
  held : Hold
  deriving DecidableEq, Repr

structure World where
  retired : List Nat
  /-- Services whose retirement state could not be read (importing, unsupported, unreachable). -/
  unknown : List Nat
  /-- The current hash of the file at a binary path; `none` when the file is gone. -/
  engineAt : Nat → Option Nat
  scopeActive : Nat → Bool
  today : Nat

inductive Reason where
  | runtimeMissing
  | engineGone
  | engineChanged
  | retired (service : Nat)
  deriving DecidableEq, Repr

inductive Compat where
  | unpinned
  | resumable
  | unverified
  | needsCurrent (reason : Reason)
  deriving DecidableEq, Repr

/-- The first service of a bundle that has been retired. -/
def firstRetired (retired : List Nat) : List Nat → Option Nat
  | [] => none
  | s :: rest => if s ∈ retired then some s else firstRetired retired rest

def classifyPin (w : World) (present : Bool) (p : Pin) : Compat :=
  if present = false then .needsCurrent .runtimeMissing else
  match firstRetired w.retired p.uses with
  | some s => .needsCurrent (.retired s)
  | none =>
    match w.engineAt p.binary, p.engine with
    | none, _ => .needsCurrent .engineGone
    | some _, none => .unverified
    | some now, some recorded =>
      if now = recorded then (if p.uses.any (· ∈ w.unknown) then .unverified else .resumable)
      else .needsCurrent .engineChanged

def classify (w : World) (s : Session) : Compat :=
  match s.pin with
  | none => .unpinned
  | some p => classifyPin w s.present p

def Compat.allows : Compat → Bool
  | .needsCurrent _ => false
  | _ => true

/-- A dependency whose backend selection is unknown: the display says `unverified`, but the
resume is refused, retryably. -/
def unavailable (w : World) (s : Session) : Bool :=
  match s.pin with
  | none => false
  | some p => p.uses.any (· ∈ w.unknown)

/-- The check `work-resume` makes before launching on the pin. The display verdict and the
permission are separate: an unknown selection is shown `unverified` and refused. -/
def guard (w : World) (s : Session) : Bool :=
  !w.scopeActive s.id && (classify w s).allows && !unavailable w s

/-- What a resume on the pin needs, stated without the classifier. No worker runs. An unpinned
session takes the current runtime, which qualification made compatible. A pinned one needs:
* its files;
* every service it uses known to be on its legacy backend (neither retired nor of unknown
  selection);
* its engine binary;
* if a hash was recorded, that same hash.
A missing engine hash is allowed by policy. -/
def SafeOnPin (w : World) (s : Session) : Prop :=
  w.scopeActive s.id = false ∧
  ∀ p, s.pin = some p →
    s.present = true ∧ (∀ x ∈ p.uses, x ∉ w.retired) ∧ (w.engineAt p.binary).isSome ∧
    (∀ h, p.engine = some h → w.engineAt p.binary = some h) ∧ (∀ x ∈ p.uses, x ∉ w.unknown)

theorem firstRetired_none {r : List Nat} :
    ∀ {l : List Nat}, firstRetired r l = none ↔ ∀ x ∈ l, x ∉ r
  | [] => by simp [firstRetired]
  | s :: rest => by
    unfold firstRetired
    by_cases h : s ∈ r
    · simp [h]
    · simp [h, firstRetired_none (l := rest)]

theorem firstRetired_some {r : List Nat} :
    ∀ {l : List Nat} {x : Nat}, firstRetired r l = some x → x ∈ l ∧ x ∈ r
  | [], _, h => by simp [firstRetired] at h
  | s :: rest, x, h => by
    unfold firstRetired at h
    by_cases hs : s ∈ r
    · simp [hs] at h; subst h; exact ⟨by simp, hs⟩
    · simp [hs] at h
      have := firstRetired_some h
      exact ⟨by simp [this.1], this.2⟩

theorem classifyPin_allows (w : World) (present : Bool) (p : Pin) :
    (classifyPin w present p).allows = true ↔
      present = true ∧ (∀ x ∈ p.uses, x ∉ w.retired) ∧ (w.engineAt p.binary).isSome ∧
      ∀ h, p.engine = some h → w.engineAt p.binary = some h := by
  cases present
  · simp [classifyPin, Compat.allows]
  · cases hr : firstRetired w.retired p.uses with
    | some x =>
      have := firstRetired_some hr
      simp only [classifyPin, hr, Compat.allows, Bool.true_eq_false, ↓reduceIte, true_and]
      simp only [Bool.false_eq_true, false_iff, not_and]
      intro hall
      exact absurd this.2 (hall x this.1)
    | none =>
      have hall := (firstRetired_none).1 hr
      cases he : w.engineAt p.binary with
      | none => simp [classifyPin, hr, he, Compat.allows]
      | some now =>
        cases hp : p.engine with
        | none => simp [classifyPin, hr, he, hp, Compat.allows]; exact hall
        | some recorded =>
          by_cases heq : now = recorded
          · subst heq
            simp only [classifyPin, hr, he, hp, Bool.true_eq_false, ↓reduceIte, true_and,
              Option.isSome_some]
            split <;> simp [Compat.allows] <;> exact hall
          · simp [classifyPin, hr, he, hp, Compat.allows, heq]

/-- The resume check is the weakest precondition of `SafeOnPin`: it refuses exactly the resumes
that would break it, and nothing else. -/
theorem guard_iff_safe (w : World) (s : Session) : guard w s = true ↔ SafeOnPin w s := by
  unfold guard SafeOnPin classify unavailable
  cases s.pin with
  | none => simp [Compat.allows]
  | some p =>
    simp only [Bool.and_eq_true, Bool.not_eq_true', Option.some.injEq, forall_eq']
    rw [classifyPin_allows]
    simp only [List.any_eq_false, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨hs, ⟨hp, hr, he, hh⟩⟩, hu⟩; exact ⟨hs, hp, hr, he, hh, hu⟩
    · rintro ⟨hs, hp, hr, he, hh, hu⟩; exact ⟨⟨hs, ⟨hp, hr, he, hh⟩⟩, hu⟩

/-- An unknown backend selection that the pin depends on refuses the resume, whatever the display
verdict. -/
theorem unknown_refused (w : World) (s : Session) (p : Pin) (x : Nat)
    (hp : s.pin = some p) (hx : x ∈ p.uses) (hu : x ∈ w.unknown) : guard w s = false := by
  have : unavailable w s = true := by
    unfold unavailable; rw [hp]; exact List.any_eq_true.2 ⟨x, hx, by simp [hu]⟩
  unfold guard; simp [this]

/-- What a refusal says holds in the world. -/
def Reason.Holds (w : World) (s : Session) (p : Pin) : Reason → Prop
  | .runtimeMissing => s.present = false
  | .engineGone => w.engineAt p.binary = none
  | .engineChanged => ∃ now recorded, w.engineAt p.binary = some now ∧ p.engine = some recorded ∧
      now ≠ recorded
  | .retired x => x ∈ p.uses ∧ x ∈ w.retired

theorem reason_holds (w : World) (s : Session) (r : Reason)
    (h : classify w s = .needsCurrent r) : ∃ p, s.pin = some p ∧ r.Holds w s p := by
  unfold classify at h
  cases hpin : s.pin with
  | none => simp [hpin] at h
  | some p =>
    refine ⟨p, rfl, ?_⟩
    simp only [hpin] at h
    unfold classifyPin at h
    cases hpres : s.present
    · simp [hpres] at h; subst h; exact hpres
    · simp only [hpres, Bool.true_eq_false, ↓reduceIte] at h
      cases hr : firstRetired w.retired p.uses with
      | some x =>
        simp only [hr, Compat.needsCurrent.injEq] at h; subst h
        exact firstRetired_some hr
      | none =>
        simp only [hr] at h
        cases he : w.engineAt p.binary with
        | none => simp only [he, Compat.needsCurrent.injEq] at h; subst h; exact he
        | some now =>
          cases hp : p.engine with
          | none => simp [he, hp] at h
          | some recorded =>
            by_cases heq : now = recorded
            · simp only [he, hp, heq, ↓reduceIte] at h; split at h <;> simp at h
            · simp only [he, hp, heq, ↓reduceIte, Compat.needsCurrent.injEq] at h; subst h
              exact ⟨now, recorded, he, hp, heq⟩

/-- A pin with a dependency whose retirement state is unknown is allowed, but is never called
`resumable`. -/
theorem unknown_is_not_resumable (w : World) (s : Session) (p : Pin) (x : Nat)
    (hp : s.pin = some p) (hx : x ∈ p.uses) (hu : x ∈ w.unknown) : classify w s ≠ .resumable := by
  have hany : p.uses.any (· ∈ w.unknown) = true := List.any_eq_true.2 ⟨x, hx, by simp [hu]⟩
  unfold classify classifyPin
  simp only [hp]
  cases s.present <;> simp only [↓reduceIte, ne_eq]
  · simp
  · cases firstRetired w.retired p.uses with
    | some _ => simp
    | none =>
      cases w.engineAt p.binary with
      | none => simp
      | some now =>
        cases p.engine with
        | none => simp
        | some recorded =>
          by_cases h : now = recorded
          · simp [h, hany]
          · simp [h]

/-- A pin with no recorded engine hash is allowed, but is never called `resumable`. -/
theorem unverified_is_not_resumable (w : World) (s : Session) (p : Pin)
    (hp : s.pin = some p) (he : p.engine = none) : classify w s ≠ .resumable := by
  unfold classify classifyPin
  simp only [hp]
  cases s.present <;> simp only [↓reduceIte, ne_eq]
  · simp
  · cases firstRetired w.retired p.uses with
    | some _ => simp
    | none =>
      cases w.engineAt p.binary with
      | none => simp
      | some _ => simp [he]

/-! ## The view -/

/-- Listed: running, or neither done nor archived and not held past today. -/
def listed (w : World) (s : Session) : Bool :=
  s.status == .running || (s.status != .done && s.status != .archived && s.held.due w.today)

def line (w : World) (s : Session) : Nat × Status × Compat := (s.id, s.status, classify w s)

def view (w : World) (sessions : List Session) : List (Nat × Status × Compat) :=
  (sessions.filter (listed w)).map (line w)

theorem view_complete (w : World) (sessions : List Session) (s : Session)
    (hs : s ∈ sessions) (hl : listed w s = true) : line w s ∈ view w sessions := by
  unfold view
  exact List.mem_map_of_mem (List.mem_filter.2 ⟨hs, hl⟩)

theorem view_sound (w : World) (sessions : List Session) (x : Nat × Status × Compat)
    (hx : x ∈ view w sessions) : ∃ s ∈ sessions, listed w s = true ∧ line w s = x := by
  unfold view at hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
  exact ⟨s, (List.mem_filter.1 hs).1, (List.mem_filter.1 hs).2, rfl⟩

/-- Session ids come from a directory listing, so they are distinct; each session then has at
most one line. -/
theorem view_nodup (w : World) (sessions : List Session)
    (h : (sessions.map Session.id).Nodup) : ((view w sessions).map Prod.fst).Nodup := by
  unfold view
  rw [List.map_map]
  show ((sessions.filter (listed w)).map Session.id).Nodup
  exact List.Nodup.sublist (List.filter_sublist.map _) h

/-- A reconciler that rewrites the snapshot on each trigger. However many triggers ran, the
snapshot is the view of the current state; nothing accumulates. -/
def reconcile (w : World) (sessions : List Session) (snapshot : List (Nat × Status × Compat))
    (triggers : List Unit) : List (Nat × Status × Compat) :=
  triggers.foldl (fun _ _ => view w sessions) snapshot

theorem level_triggered (w : World) (sessions : List Session) (snapshot) (triggers : List Unit)
    (h : triggers ≠ []) : reconcile w sessions snapshot triggers = view w sessions := by
  unfold reconcile
  induction triggers generalizing snapshot with
  | nil => exact absurd rfl h
  | cons t rest ih =>
    cases rest with
    | nil => rfl
    | cons t' rest' => exact ih (view w sessions) (List.cons_ne_nil _ _)

theorem running_listed (w : World) (s : Session) (h : s.status = .running) :
    listed w s = true := by
  unfold listed; simp [h]

theorem held_quiet_until_review (w : World) (s : Session) (d : Nat)
    (hh : s.held = .reviewOn d) (hd : w.today < d) (hr : s.status ≠ .running) :
    listed w s = false := by
  unfold listed; simp [hh, hr, Hold.due]; omega

theorem held_indefinitely_quiet (w : World) (s : Session)
    (hh : s.held = .indefinite) (hr : s.status ≠ .running) : listed w s = false := by
  unfold listed; simp [hh, hr, Hold.due]

theorem held_listed_when_due (w : World) (s : Session) (d : Nat) (hh : s.held = .reviewOn d)
    (hd : d ≤ w.today) (hopen : s.status ≠ .done ∧ s.status ≠ .archived) :
    listed w s = true := by
  unfold listed; simp [hh, hd, hopen.1, hopen.2, Hold.due]

/-- Between review dates the view does not change: it depends on the day only through the
held sessions' review dates. -/
theorem view_stable_between_reviews (w : World) (t₁ t₂ : Nat) (sessions : List Session)
    (h : ∀ s ∈ sessions, ∀ d, s.held = .reviewOn d → (d ≤ t₁ ↔ d ≤ t₂)) :
    view { w with today := t₁ } sessions = view { w with today := t₂ } sessions := by
  unfold view
  have hl : ∀ s ∈ sessions, listed { w with today := t₁ } s = listed { w with today := t₂ } s := by
    intro s hs
    unfold listed
    cases hh : s.held with
    | free => rfl
    | indefinite => rfl
    | reviewOn d => simp only [Hold.due, h s hs d hh]
  have hline : ∀ s, line { w with today := t₁ } s = line { w with today := t₂ } s := fun _ => rfl
  rw [List.filter_congr hl]
  exact List.map_congr_left (fun s _ => hline s)

/-! ## The bounded rendering -/

structure Bounded where
  shown : List (Nat × Status × Compat)
  omitted : Nat
  counts : Compat → Nat

def countOf (w : World) (sessions : List Session) (c : Compat) : Nat :=
  (sessions.filter (fun s => classify w s == c)).length

def bounded (w : World) (sessions : List Session) (n : Nat) : Bounded :=
  { shown := (view w sessions).take n, omitted := (view w sessions).length - n,
    counts := countOf w sessions }

theorem shown_or_omitted (w : World) (sessions : List Session) (n : Nat) (s : Session)
    (hs : s ∈ sessions) (hl : listed w s = true) :
    line w s ∈ (bounded w sessions n).shown ∨ 0 < (bounded w sessions n).omitted := by
  have hv := view_complete w sessions s hs hl
  rw [← List.take_append_drop n (view w sessions), List.mem_append] at hv
  rcases hv with h | h
  · exact Or.inl h
  · right
    have hpos := List.length_pos_of_mem h
    rw [List.length_drop] at hpos
    exact hpos

theorem counted (w : World) (sessions : List Session) (n : Nat) (s : Session)
    (hs : s ∈ sessions) : 0 < (bounded w sessions n).counts (classify w s) := by
  show 0 < (sessions.filter (fun x => classify w x == classify w s)).length
  exact List.length_pos_of_mem (List.mem_filter.2 ⟨hs, by simp⟩)

/-! ## The live case, as a check -/

/-- The 10-23 session: pinned to a bundle that uses the retired SQLite ledger (service 1),
with no recorded engine hash. -/
def stopped1023 : Session :=
  { id := 1023, status := .stopped, pin := some { bundle := 7, uses := [1], binary := 3, engine := none },
    present := true, held := .free }

def today1106 : World :=
  { retired := [1], unknown := [], engineAt := fun _ => some 42, scopeActive := fun _ => false, today := 1106 }

example : classify today1106 stopped1023 = .needsCurrent (.retired 1) := by decide
example : guard today1106 stopped1023 = false := by decide
example : listed today1106 stopped1023 = true := by decide

end PettaClaw.CodingSessionLifecycle

#print axioms PettaClaw.CodingSessionLifecycle.guard_iff_safe
#print axioms PettaClaw.CodingSessionLifecycle.unknown_refused
#print axioms PettaClaw.CodingSessionLifecycle.reason_holds
#print axioms PettaClaw.CodingSessionLifecycle.unverified_is_not_resumable
#print axioms PettaClaw.CodingSessionLifecycle.unknown_is_not_resumable
#print axioms PettaClaw.CodingSessionLifecycle.view_complete
#print axioms PettaClaw.CodingSessionLifecycle.view_sound
#print axioms PettaClaw.CodingSessionLifecycle.view_nodup
#print axioms PettaClaw.CodingSessionLifecycle.level_triggered
#print axioms PettaClaw.CodingSessionLifecycle.running_listed
#print axioms PettaClaw.CodingSessionLifecycle.held_quiet_until_review
#print axioms PettaClaw.CodingSessionLifecycle.held_indefinitely_quiet
#print axioms PettaClaw.CodingSessionLifecycle.held_listed_when_due
#print axioms PettaClaw.CodingSessionLifecycle.view_stable_between_reviews
#print axioms PettaClaw.CodingSessionLifecycle.shown_or_omitted
#print axioms PettaClaw.CodingSessionLifecycle.counted
