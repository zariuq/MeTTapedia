import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Waves

/-!
# The commit protocol a runtime implements, and why it refines the atomic semantics

This module is a specification at the level of a C implementation. It describes the state the
runtime keeps, the steps it takes, and the guards on each step. It then proves that every run of
the protocol is a run of the atomic semantics of `Commits`.

## State (`ProtocolState`)

* `store`: the live occurrences, claimed or not. This is the abstract store.
* `born`: every occurrence identity ever allocated. Identities are never reused, so a removed
  occurrence never comes back. An occurrence identity is not a content identity: two equal
  messages are two occurrences with one label.
* `claim`: the transaction, if any, that has claimed each occurrence.
* `epoch`: a counter per region (a predicate on labels). A commit bumps the counter of every
  region in which it takes or makes an occurrence.
* `phase`: each transaction is `idle`, `active` with the epochs it saw when it began, or `done`.

Each transaction `t` has one commit `txn t`, fixed in advance and matched when it begins; a retry
after an abort is a new transaction.

## Steps (`Step`)

1. **begin** `t`: an idle transaction whose commit is enabled at the current store records the
   current epochs and becomes active.
2. **claim** `t o`: compare-and-swap an unclaimed live occurrence that `t` takes, to `t`, in
   canonical order (every smaller occurrence `t` takes is already claimed by `t`).
3. **commit** `t`: guarded by all of `t`'s takes claimed by `t`, its keeps live, the region of every
   predicate query at the epoch it saw, and its fresh identities unborn. The step publishes the
   firing, records the new identities as born, clears `t`'s claims and bumps the epochs of the
   regions written.
4. **abort** `t`: release `t`'s claims; `t` is done.

## Theorems

* **Refinement** (`Run.refines`): the commits of any protocol run, in commit order, are an
  executable sequence of the atomic semantics from the initial store, and the protocol's store is
  where that sequence ends.
* **A stale epoch aborts** (`Run.stale_never_commits`): once the region of a predicate query of an
  active transaction has a newer epoch than it saw, that transaction commits in no continuation.
* **A lost claim aborts** (`Run.gone_never_commits`): once an occurrence that a transaction must
  take is gone, that transaction commits in no continuation.
* **Canonical order prevents deadlock** (`waitsFor_acyclic`): a transaction waiting for a claim
  held by another waits on a smaller occurrence than any the other waits on, so the waits-for
  relation has no cycle.
* **The wave commit** (`Run.wave`): committing an acyclic, clash-free batch of ready transactions
  one by one in a ranking order is a protocol run. The cycle test of `Waves` is exact.
* **What a wait index must report** (`positive_woken_by_make`, `absence_woken_by_take`,
  `woken_requires_write`): a parked guard that one commit makes true was flipped by an event of its
  kind. A positive guard is flipped only by a make in its region, an absence guard only by a take
  from it, and a predicate query by some write in it. An index keyed by region and event kind that
  reports those events therefore sees every flip. The index itself is not modeled here.

Controls: a lost claim (`Controls.lost_claim_aborts`: two rivals for one token; once the first
commits, the second commits in no continuation), a stale epoch (`Controls.stale_epoch_aborts`: a
lock maker commits after an absence reader began; the reader never commits), and a reachable,
well-formed state with a waits-for edge (`Controls.waitsFor_inhabited`), so the acyclicity theorem
is not vacuous.

## Every runtime model refines one atomic semantics

The models of a runtime in this development end in one statement: their commits, in commit
order, are an `Executable` sequence of `Waves`.

* this protocol: `Run.refines`; re-matching over attempts: `Liveness.AttemptRun.refines`;
* optimistic attempts under serializable validation: `Liveness.exec_refines`;
* a scheduler's split-phase runs in `serializable` mode: `executable_history_of_serializable`;
* publication validated by one revision per space: `SerializedPublication.revision_run_refines`;
* placed commits on a network: `Coordination.HomeLocation.run_refines`, with located identities
  `Coordination.LocatedIdentities.lrun_refines`, with moves `Coordination.Colocation.moved_run_refines`;
* the chosen log of failover: `Coordination.OwnerFailover.chosen_legal`.

A fenced lease owner refines an atomic take instead (`Coordination.FencedLeases.step_refines`),
and its claims, expiries and effects each fire one commit of the occurrence store
(`FencedLeases.encode_step_claim`, `encode_step_expire`, `encode_step_effect`).

## For the implementer

* Epochs here are kept per region predicate, the finest choice. A runtime may key epochs by coarser
  regions (a head symbol, a path prefix, a channel), provided the region of every predicate query
  lies inside the key it validates: a write into the queried region then bumps that key, so the
  refinement argument is unchanged and only spurious aborts are added.
* `begin` is where the matcher runs: the commit must be enabled at the store the transaction
  read. Claims and the commit step may interleave with other transactions' steps arbitrarily.
* The commit step must be atomic with respect to other commit steps: its guards and its effect
  happen at one instant. Claims make the takes exclusive; the epoch check makes predicate queries
  exact; keeps need no lock because a kept occurrence can only disappear through a commit that takes
  it, and that commit must hold its claim.
-/


set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v w

variable {O : Type u} [LinearOrder O] {R : Type v} {T : Type w} [DecidableEq T]

/-- The phase of a transaction. -/
inductive Phase (R : Type v) where
  | idle
  | active (seen : (R → Bool) → ℕ)
  | done

/-- The state a runtime keeps. -/
structure ProtocolState (O : Type u) (R : Type v) (T : Type w) where
  store : Finset O
  born : Finset O
  claim : O → Option T
  epoch : (R → Bool) → ℕ
  phase : T → Phase R

variable (label : O → R) (txn : T → Commit O R)

/-- The state after transaction `t` commits. -/
def commitState (t : T) (σ : ProtocolState O R T) : ProtocolState O R T where
  store := fire σ.store (txn t)
  born := σ.born ∪ (txn t).made
  claim := fun o => if o ∈ (txn t).taken then none else σ.claim o
  epoch := fun region => if Writes label (txn t) region then σ.epoch region + 1 else σ.epoch region
  phase := Function.update σ.phase t .done

/-- The state after transaction `t` aborts. -/
def abortState (t : T) (σ : ProtocolState O R T) : ProtocolState O R T where
  store := σ.store
  born := σ.born
  claim := fun o => if σ.claim o = some t then none else σ.claim o
  epoch := σ.epoch
  phase := Function.update σ.phase t .done

/-- One protocol step; a commit step reports the transaction and its commit. -/
inductive Step : ProtocolState O R T → Option (T × Commit O R) → ProtocolState O R T → Prop
  | begin (σ : ProtocolState O R T) (t : T) (idle : σ.phase t = .idle)
      (enabled : Enabled label σ.store (txn t)) :
      Step σ none { σ with phase := Function.update σ.phase t (.active σ.epoch) }
  | claim (σ : ProtocolState O R T) (t : T) (seen : (R → Bool) → ℕ) (o : O)
      (active : σ.phase t = .active seen) (taken : o ∈ (txn t).taken) (live : o ∈ σ.store)
      (free : σ.claim o = none)
      (canonical : ∀ o' ∈ (txn t).taken, o' < o → σ.claim o' = some t) :
      Step σ none { σ with claim := Function.update σ.claim o (some t) }
  | commit (σ : ProtocolState O R T) (t : T) (seen : (R → Bool) → ℕ)
      (active : σ.phase t = .active seen)
      (claimed : ∀ o ∈ (txn t).taken, σ.claim o = some t)
      (keptLive : (txn t).kept ⊆ σ.store)
      (epochsFresh : ∀ read ∈ (txn t).queries, σ.epoch read.region = seen read.region)
      (unborn : Disjoint (txn t).made σ.born) :
      Step σ (some (t, txn t)) (commitState label txn t σ)
  | abort (σ : ProtocolState O R T) (t : T) (seen : (R → Bool) → ℕ)
      (active : σ.phase t = .active seen) :
      Step σ none (abortState t σ)

/-- A protocol run, with the commit steps it took, in order. -/
inductive Run : ProtocolState O R T → List (T × Commit O R) → ProtocolState O R T → Prop
  | refl (σ : ProtocolState O R T) : Run σ [] σ
  | step {σ σ' σ'' : ProtocolState O R T} {out : Option (T × Commit O R)}
      {trace : List (T × Commit O R)} (first : Step label txn σ out σ')
      (rest : Run σ' trace σ'') : Run σ (out.toList ++ trace) σ''

/-- The invariant every reachable state satisfies. -/
structure WellFormed (σ : ProtocolState O R T) : Prop where
  store_born : σ.store ⊆ σ.born
  claim_live : ∀ o t, σ.claim o = some t →
    o ∈ σ.store ∧ o ∈ (txn t).taken ∧ ∃ seen, σ.phase t = .active seen
  seen_le : ∀ t seen, σ.phase t = .active seen → ∀ region, seen region ≤ σ.epoch region
  queries_valid : ∀ t seen, σ.phase t = .active seen → ∀ read ∈ (txn t).queries,
    σ.epoch read.region = seen read.region → read.Holds label σ.store
  apart : ∀ t seen, σ.phase t = .active seen → Disjoint (txn t).taken (txn t).kept
  canonical : ∀ t o, σ.claim o = some t → ∀ o' ∈ (txn t).taken, o' < o → σ.claim o' = some t

/-- An initial state: no claims, every transaction idle, the store born. -/
def Initial (σ : ProtocolState O R T) : Prop :=
  σ.store ⊆ σ.born ∧ (∀ o, σ.claim o = none) ∧ ∀ t, σ.phase t = .idle

variable {label txn}

omit [DecidableEq T] in
theorem wellFormed_of_initial {σ : ProtocolState O R T} (initial : Initial σ) :
    WellFormed label txn σ where
  store_born := initial.1
  claim_live := fun o t claimed => by rw [initial.2.1 o] at claimed; cases claimed
  seen_le := fun t seen active => by rw [initial.2.2 t] at active; cases active
  queries_valid := fun t seen active => by rw [initial.2.2 t] at active; cases active
  apart := fun t seen active => by rw [initial.2.2 t] at active; cases active
  canonical := fun t o claimed => by rw [initial.2.1 o] at claimed; cases claimed

omit [DecidableEq T] in
/-- **At a commit step, the commit is enabled at the abstract store.** -/
theorem enabled_of_commit_guard {σ : ProtocolState O R T} (wf : WellFormed label txn σ) {t : T}
    {seen : (R → Bool) → ℕ} (active : σ.phase t = .active seen)
    (claimed : ∀ o ∈ (txn t).taken, σ.claim o = some t) (keptLive : (txn t).kept ⊆ σ.store)
    (epochsFresh : ∀ read ∈ (txn t).queries, σ.epoch read.region = seen read.region)
    (unborn : Disjoint (txn t).made σ.born) : Enabled label σ.store (txn t) where
  taken_subset := fun o taken => (wf.claim_live o t (claimed o taken)).1
  kept_subset := keptLive
  apart := wf.apart t seen active
  fresh := Finset.disjoint_of_subset_right wf.store_born unborn
  queries_hold := fun read member => wf.queries_valid t seen active read member (epochsFresh read member)

theorem epoch_le_commitState (σ : ProtocolState O R T) (t : T) (region : R → Bool) :
    σ.epoch region ≤ (commitState label txn t σ).epoch region := by
  simp only [commitState]
  split <;> omega

/-- **Every step keeps the invariant.** -/
theorem Step.wellFormed {σ σ' : ProtocolState O R T} {out : Option (T × Commit O R)}
    (step : Step label txn σ out σ') (wf : WellFormed label txn σ) : WellFormed label txn σ' := by
  cases step with
  | begin t idle enabled =>
      refine ⟨wf.store_born, ?_, ?_, ?_, ?_, wf.canonical⟩
      · intro o t' claimed
        obtain ⟨live, taken, seen, active⟩ := wf.claim_live o t' claimed
        refine ⟨live, taken, ?_⟩
        by_cases same : t' = t
        · subst same; rw [idle] at active; cases active
        · exact ⟨seen, by simpa [Function.update_of_ne same] using active⟩
      · intro t' seen active region
        by_cases same : t' = t
        · subst same
          simp only [Function.update_self, Phase.active.injEq] at active
          subst active; exact le_rfl
        · exact wf.seen_le t' seen (by simpa [Function.update_of_ne same] using active) region
      · intro t' seen active read member fresh
        by_cases same : t' = t
        · subst same
          exact enabled.queries_hold read member
        · exact wf.queries_valid t' seen (by simpa [Function.update_of_ne same] using active) read
            member fresh
      · intro t' seen active
        by_cases same : t' = t
        · subst same; exact enabled.apart
        · exact wf.apart t' seen (by simpa [Function.update_of_ne same] using active)
  | claim t seen o active taken live free canonical =>
      refine ⟨wf.store_born, ?_, wf.seen_le, wf.queries_valid, wf.apart, ?_⟩
      · intro o' t' claimed
        by_cases same : o' = o
        · subst same
          simp only [Function.update_self, Option.some.injEq] at claimed
          subst claimed
          exact ⟨live, taken, seen, active⟩
        · exact wf.claim_live o' t' (by simpa [Function.update_of_ne same] using claimed)
      · intro t' o' claimed o'' taken'' smaller
        by_cases same : o' = o
        · subst same
          simp only [Function.update_self, Option.some.injEq] at claimed
          subst claimed
          have := canonical o'' taken'' smaller
          dsimp only
          rw [Function.update_of_ne (ne_of_lt smaller)]
          exact this
        · have claimed' : σ.claim o' = some t' := by simpa [Function.update_of_ne same] using claimed
          have := wf.canonical t' o' claimed' o'' taken'' smaller
          by_cases same' : o'' = o
          · subst same'; rw [free] at this; cases this
          · dsimp only; rw [Function.update_of_ne same']; exact this
  | commit t seen active claimed keptLive epochsFresh unborn =>
      have enabled := enabled_of_commit_guard wf active claimed keptLive epochsFresh unborn
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro o member
        rcases mem_fire.mp member with ⟨inStore, _⟩ | made
        · exact Finset.mem_union_left _ (wf.store_born inStore)
        · exact Finset.mem_union_right _ made
      · intro o t' claimedO
        simp only [commitState] at claimedO
        split at claimedO
        · cases claimedO
        · next notTaken =>
          obtain ⟨live, taken, seen', active'⟩ := wf.claim_live o t' claimedO
          have different : t' ≠ t := by
            rintro rfl
            exact notTaken taken
          refine ⟨mem_fire.mpr (Or.inl ⟨live, notTaken⟩), taken, seen', ?_⟩
          simpa [commitState, Function.update_of_ne different] using active'
      · intro t' seen' active' region
        by_cases same : t' = t
        · subst same; simp [commitState] at active'
        · have active'' : σ.phase t' = .active seen' := by
            simpa [commitState, Function.update_of_ne same] using active'
          exact (wf.seen_le t' seen' active'' region).trans (epoch_le_commitState σ t region)
      · intro t' seen' active' read member fresh'
        by_cases same : t' = t
        · subst same; simp [commitState] at active'
        · have active'' : σ.phase t' = .active seen' := by
            simpa [commitState, Function.update_of_ne same] using active'
          have le := wf.seen_le t' seen' active'' read.region
          -- the epoch of the region did not move, so the commit wrote nothing in it
          have noWrite : ¬ Writes label (txn t) read.region := by
            intro writes
            have bumped : (commitState label txn t σ).epoch read.region = σ.epoch read.region + 1 := by
              simp [commitState, writes]
            omega
          have still : σ.epoch read.region = seen' read.region := by
            have : (commitState label txn t σ).epoch read.region = σ.epoch read.region := by
              simp [commitState, noWrite]
            omega
          have holds := wf.queries_valid t' seen' active'' read member still
          unfold PredicateQuery.Holds at holds ⊢
          simp only [commitState]
          rw [← holds]
          ext o
          simp only [mem_regionOf, mem_fire]
          constructor
          · rintro ⟨⟨inStore, _⟩ | made, inRegion⟩
            · exact ⟨inStore, inRegion⟩
            · exact absurd ⟨o, Finset.mem_union_right _ made, inRegion⟩ noWrite
          · rintro ⟨inStore, inRegion⟩
            refine ⟨Or.inl ⟨inStore, fun taken => ?_⟩, inRegion⟩
            exact noWrite ⟨o, Finset.mem_union_left _ taken, inRegion⟩
      · intro t' seen' active'
        by_cases same : t' = t
        · subst same; simp [commitState] at active'
        · exact wf.apart t' seen' (by simpa [commitState, Function.update_of_ne same] using active')
      · intro t' o claimedO o' taken' smaller
        simp only [commitState] at claimedO ⊢
        split at claimedO
        · cases claimedO
        · next notTaken =>
          have claimedO' := wf.canonical t' o claimedO o' taken' smaller
          have different : t' ≠ t := fun equal =>
            notTaken (equal ▸ (wf.claim_live o t' claimedO).2.1)
          split
          · next takenByT =>
            have := claimed o' takenByT
            rw [claimedO'] at this
            exact absurd (Option.some.inj this) different
          · exact claimedO'
  | abort t seen active =>
      refine ⟨wf.store_born, ?_, ?_, ?_, ?_, ?_⟩
      · intro o t' claimedO
        simp only [abortState] at claimedO
        split at claimedO
        · cases claimedO
        · next notT =>
          obtain ⟨live, taken, seen', active'⟩ := wf.claim_live o t' claimedO
          have different : t' ≠ t := by rintro rfl; exact notT claimedO
          exact ⟨live, taken, seen', by simpa [abortState, Function.update_of_ne different] using active'⟩
      · intro t' seen' active' region
        by_cases same : t' = t
        · subst same; simp [abortState] at active'
        · exact wf.seen_le t' seen' (by simpa [abortState, Function.update_of_ne same] using active') region
      · intro t' seen' active' read member fresh'
        by_cases same : t' = t
        · subst same; simp [abortState] at active'
        · exact wf.queries_valid t' seen' (by simpa [abortState, Function.update_of_ne same] using active')
            read member fresh'
      · intro t' seen' active'
        by_cases same : t' = t
        · subst same; simp [abortState] at active'
        · exact wf.apart t' seen' (by simpa [abortState, Function.update_of_ne same] using active')
      · intro t' o claimedO o' taken' smaller
        simp only [abortState] at claimedO ⊢
        split at claimedO
        · cases claimedO
        · next notT =>
          have different : t' ≠ t := by rintro rfl; exact notT claimedO
          have := wf.canonical t' o claimedO o' taken' smaller
          rw [this]
          simp [different]

/-- **Refinement.** The commits of a protocol run from a well-formed state are an executable
sequence of the atomic semantics from its store, ending at the protocol's store. -/
theorem Run.refines {σ σ' : ProtocolState O R T} {trace : List (T × Commit O R)}
    (run : Run label txn σ trace σ') (wf : WellFormed label txn σ) :
    Executable label σ.store (trace.map Prod.snd) ∧ σ'.store = fireList σ.store (trace.map Prod.snd) ∧
      WellFormed label txn σ' := by
  induction run with
  | refl σ => exact ⟨.nil _, rfl, wf⟩
  | @step σ σ₁ σ₂ out trace first rest ih =>
      obtain ⟨executable, endStore, wf₂⟩ := ih (first.wellFormed wf)
      cases first with
      | begin => exact ⟨executable, endStore, wf₂⟩
      | claim => exact ⟨executable, endStore, wf₂⟩
      | abort => exact ⟨executable, endStore, wf₂⟩
      | commit t seen active claimed keptLive epochsFresh unborn =>
          exact ⟨.cons (enabled_of_commit_guard wf active claimed keptLive epochsFresh unborn)
            executable, endStore, wf₂⟩

/-! ## Aborting rather than committing -/

theorem Step.phase_other {σ σ' : ProtocolState O R T} {out : Option (T × Commit O R)}
    (step : Step label txn σ out σ') {t : T} (notT : ∀ c, out ≠ some (t, c))
    (notBegin : σ.phase t ≠ .idle) : σ'.phase t = σ.phase t ∨ σ'.phase t = .done := by
  cases step with
  | begin t' idle _ =>
      by_cases same : t = t'
      · subst same; exact absurd idle notBegin
      · left; simp [Function.update_of_ne same]
  | claim => left; rfl
  | commit t' _ _ _ _ _ _ =>
      by_cases same : t = t'
      · subst same; exact absurd rfl (notT _)
      · left; simp [commitState, Function.update_of_ne same]
  | abort t' _ _ =>
      by_cases same : t = t'
      · subst same; right; simp [abortState]
      · left; simp [abortState, Function.update_of_ne same]

theorem Step.epoch_mono {σ σ' : ProtocolState O R T} {out : Option (T × Commit O R)}
    (step : Step label txn σ out σ') (region : R → Bool) : σ.epoch region ≤ σ'.epoch region := by
  cases step with
  | begin => exact le_rfl
  | claim => exact le_rfl
  | commit t _ _ _ _ _ _ => exact epoch_le_commitState σ t region
  | abort => exact le_rfl

/-- A transaction is blocked by a stale epoch: it is done, or active with a region it queries at
a newer epoch than it saw. -/
def StaleOrDone (t : T) (seen : (R → Bool) → ℕ) (region : R → Bool) (σ : ProtocolState O R T) : Prop :=
  σ.phase t = .done ∨ (σ.phase t = .active seen ∧ seen region < σ.epoch region)

/-- **A stale epoch aborts rather than commits.** If an active transaction queries a region whose
epoch has moved since it began, it commits in no continuation. -/
theorem Run.stale_never_commits {σ σ' : ProtocolState O R T} {trace : List (T × Commit O R)}
    (run : Run label txn σ trace σ') {t : T} {seen : (R → Bool) → ℕ} {read : PredicateQuery O R}
    (member : read ∈ (txn t).queries) (blocked : StaleOrDone t seen read.region σ) :
    ∀ entry ∈ trace, entry.1 ≠ t := by
  induction run with
  | refl => simp
  | @step σ σ₁ σ₂ out trace first rest ih =>
      have notCommitT : ∀ c, out ≠ some (t, c) := by
        intro c equal
        subst equal
        cases first with
        | commit _ seen' active _ _ epochsFresh _ =>
            have fresh := epochsFresh read member
            rcases blocked with done | ⟨active', stale⟩
            · rw [done] at active; cases active
            · rw [active'] at active
              cases active
              omega
      have blockedNext : StaleOrDone t seen read.region σ₁ := by
        have notIdle : σ.phase t ≠ .idle := by
          rcases blocked with done | ⟨active', _⟩ <;> simp [*]
        rcases first.phase_other notCommitT notIdle with same | done
        · rcases blocked with done' | ⟨active', stale⟩
          · exact Or.inl (same.trans done')
          · exact Or.inr ⟨same.trans active', lt_of_lt_of_le stale (first.epoch_mono read.region)⟩
        · exact Or.inl done
      intro entry inTrace
      rcases List.mem_append.mp inTrace with inOut | inRest
      · cases out with
        | none => simp at inOut
        | some pair =>
            simp only [Option.toList_some, List.mem_singleton] at inOut
            subst inOut
            intro equal
            exact notCommitT entry.2 (by rw [← equal])
      · exact ih blockedNext entry inRest

/-- **A lost claim aborts rather than commits.** Once an occurrence that a transaction must take
has been born and is gone, that transaction commits in no continuation from a well-formed
state. -/
theorem Run.gone_never_commits {σ σ' : ProtocolState O R T} {trace : List (T × Commit O R)}
    (run : Run label txn σ trace σ') (wf : WellFormed label txn σ) {t : T} {o : O}
    (taken : o ∈ (txn t).taken) (born : o ∈ σ.born) (gone : o ∉ σ.store) :
    ∀ entry ∈ trace, entry.1 ≠ t := by
  induction run with
  | refl => simp
  | @step σ σ₁ σ₂ out trace first rest ih =>
      have notCommitT : ∀ c, out ≠ some (t, c) := by
        intro c equal
        subst equal
        cases first with
        | commit _ _ _ claimed _ _ _ =>
            exact gone (wf.claim_live o t (claimed o taken)).1
      have bornNext : o ∈ σ₁.born ∧ o ∉ σ₁.store := by
        cases first with
        | begin => exact ⟨born, gone⟩
        | claim => exact ⟨born, gone⟩
        | abort => exact ⟨born, gone⟩
        | commit t' _ _ _ _ _ unborn =>
            refine ⟨Finset.mem_union_left _ born, fun inFire => ?_⟩
            rcases mem_fire.mp inFire with ⟨inStore, _⟩ | made
            · exact gone inStore
            · exact Finset.disjoint_left.mp unborn made born
      intro entry inTrace
      rcases List.mem_append.mp inTrace with inOut | inRest
      · cases out with
        | none => simp at inOut
        | some pair =>
            simp only [Option.toList_some, List.mem_singleton] at inOut
            subst inOut
            intro equal
            exact notCommitT entry.2 (by rw [← equal])
      · exact ih (first.wellFormed wf) bornNext.1 bornNext.2 entry inRest

/-! ## Canonical order prevents deadlock -/

/-- The occurrence a transaction claims next: the least one it takes and has not claimed. -/
def NextNeeded (σ : ProtocolState O R T) (t : T) (o : O) : Prop :=
  o ∈ (txn t).taken ∧ σ.claim o ≠ some t ∧ ∀ o' ∈ (txn t).taken, o' < o → σ.claim o' = some t

/-- `t` waits for `t'`: the occurrence `t` needs next is claimed by `t'`. -/
def WaitsFor (σ : ProtocolState O R T) (t t' : T) : Prop :=
  ∃ o, NextNeeded (txn := txn) σ t o ∧ σ.claim o = some t'

omit [DecidableEq T] in
theorem nextNeeded_unique {σ : ProtocolState O R T} {t : T} {o o' : O}
    (first : NextNeeded (txn := txn) σ t o) (second : NextNeeded (txn := txn) σ t o') : o = o' := by
  rcases lt_trichotomy o o' with lt | eq | gt
  · exact absurd (second.2.2 o first.1 lt) first.2.1
  · exact eq
  · exact absurd (first.2.2 o' second.1 gt) second.2.1

omit [DecidableEq T] in
/-- Waiting goes up: the occurrence the waiter needs is smaller than the one its holder needs. -/
theorem waitsFor_increases {σ : ProtocolState O R T} (wf : WellFormed label txn σ) {t t' : T}
    (waits : WaitsFor (txn := txn) σ t t') {o o' : O} (needT : NextNeeded (txn := txn) σ t o)
    (needT' : NextNeeded (txn := txn) σ t' o') : o < o' := by
  obtain ⟨o₀, need₀, held⟩ := waits
  have same := nextNeeded_unique needT need₀
  subst same
  rcases lt_trichotomy o o' with lt | eq | gt
  · exact lt
  · subst eq; exact absurd held needT'.2.1
  · exact absurd (wf.canonical t' o held o' needT'.1 gt) needT'.2.1

omit [DecidableEq T] in
/-- **No waits-for cycle.** With claims taken in canonical order, no transaction waits, through any
chain, on itself. -/
theorem waitsFor_acyclic {σ : ProtocolState O R T} (wf : WellFormed label txn σ) (t : T) :
    ¬ Relation.TransGen (WaitsFor (txn := txn) σ) t t := by
  have chain : ∀ {a b}, Relation.TransGen (WaitsFor (txn := txn) σ) a b →
      ∀ {oa ob}, NextNeeded (txn := txn) σ a oa → NextNeeded (txn := txn) σ b ob → oa < ob := by
    intro a b path
    induction path with
    | single waits => exact fun needA needB => waitsFor_increases wf waits needA needB
    | tail _ waits ih =>
        intro oa ob needA needB
        obtain ⟨om, needM, _⟩ := id waits
        exact (ih needA needM).trans (waitsFor_increases wf waits needM needB)
  intro cycle
  obtain ⟨b, ⟨oa, needA, _⟩, _⟩ := Relation.TransGen.head'_iff.mp cycle
  exact lt_irrefl _ (chain cycle needA needA)

/-! ## The wait index -/

section WaitIndex

variable {label : O → R}

omit [LinearOrder O] in
/-- **A parked guard on a region is woken only by a commit that writes the region**, by the frame
law of regions (`regionOf_fire_of_no_write`). -/
theorem woken_requires_write [DecidableEq O] {store : Finset O} {d : Commit O R}
    {region : R → Bool} {test : Finset O → Prop}
    (before : ¬ test (regionOf label store region))
    (after : test (regionOf label (fire store d) region)) :
    Writes label d region := by
  by_contra noWrite
  unfold Writes at noWrite
  push Not at noWrite
  have same : regionOf label (fire store d) region = regionOf label store region :=
    regionOf_fire_of_no_write fun o written => by simpa using noWrite o written
  rw [same] at after
  exact before after

omit [LinearOrder O] in
/-- **A positive guard is woken only by a make in its region.** -/
theorem positive_woken_by_make [DecidableEq O] {store : Finset O} {d : Commit O R}
    {region : R → Bool} {test : Finset O → Prop}
    (upward : ∀ ⦃small large : Finset O⦄, small ⊆ large → test small → test large)
    (before : ¬ test (regionOf label store region))
    (after : test (regionOf label (fire store d) region)) :
    ∃ o ∈ d.made, region (label o) = true := by
  by_contra noMake
  push Not at noMake
  exact before (upward (regionOf_fire_subset_of_no_make fun o made => by simpa using noMake o made) after)

omit [LinearOrder O] in
/-- **An absence guard, or any downward-closed one, is woken only by a take from its region.** -/
theorem absence_woken_by_take [DecidableEq O] {store : Finset O} {d : Commit O R}
    {region : R → Bool} {test : Finset O → Prop}
    (downward : ∀ ⦃small large : Finset O⦄, small ⊆ large → test large → test small)
    (before : ¬ test (regionOf label store region))
    (after : test (regionOf label (fire store d) region)) :
    ∃ o ∈ d.taken, region (label o) = true := by
  by_contra noTake
  push Not at noTake
  exact before (downward (regionOf_subset_fire_of_no_take fun o taken => by simpa using noTake o taken) after)

end WaitIndex

/-! ## The wave commit -/

/-- A transaction is ready: active, with its takes claimed, its keeps live, the regions of its
predicate queries at the epochs it saw, and its fresh identities unborn. -/
def Ready (σ : ProtocolState O R T) (t : T) : Prop :=
  ∃ seen, σ.phase t = .active seen ∧ (∀ o ∈ (txn t).taken, σ.claim o = some t) ∧
    (txn t).kept ⊆ σ.store ∧ (∀ read ∈ (txn t).queries, σ.epoch read.region = seen read.region) ∧
    Disjoint (txn t).made σ.born

/-- A ready transaction can commit: its commit is a step of the protocol. -/
theorem Ready.step {σ : ProtocolState O R T} {t : T} (ready : Ready (txn := txn) σ t) :
    ∃ σ', Step label txn σ (some (t, txn t)) σ' := by
  obtain ⟨seen, active, claimed, keptLive, epochsFresh, unborn⟩ := ready
  exact ⟨_, .commit σ t seen active claimed keptLive epochsFresh unborn⟩

/-- Committing one ready transaction keeps every other ready transaction ready, unless it clashes
with it or spoils it. -/
theorem ready_commitState {σ : ProtocolState O R T} {t t' : T} (different : t' ≠ t)
    (ready : Ready (txn := txn) σ t') (noClash : ¬ Clash (txn t) (txn t'))
    (noSpoil : ¬ Spoils label (txn t) (txn t')) :
    Ready (txn := txn) (commitState label txn t σ) t' := by
  obtain ⟨seen, active, claimed, keptLive, epochsFresh, unborn⟩ := ready
  unfold Clash at noClash
  unfold Spoils at noSpoil
  push Not at noClash noSpoil
  refine ⟨seen, by simp [commitState, Function.update_of_ne different, active], ?_, ?_, ?_, ?_⟩
  · intro o taken
    have notT : o ∉ (txn t).taken := fun takenT =>
      Finset.disjoint_left.mp noClash.1 takenT taken
    simp [commitState, notT, claimed o taken]
  · intro o kept
    exact mem_fire.mpr (Or.inl ⟨keptLive kept, fun takenT =>
      Finset.disjoint_left.mp noSpoil.1 takenT kept⟩)
  · intro read member
    have noWrite : ¬ Writes label (txn t) read.region :=
      fun ⟨o, written, inRegion⟩ => noSpoil.2 ⟨read, member, o, written, inRegion⟩
    simp [commitState, noWrite, epochsFresh read member]
  · exact Finset.disjoint_union_right.mpr ⟨unborn, noClash.2.symm⟩

/-- Ready transactions in an order where none clashes with or spoils a later one commit one after
another. -/
theorem Run.commit_all : ∀ (l : List T) (σ : ProtocolState O R T), l.Nodup →
    (∀ t ∈ l, Ready (txn := txn) σ t) →
    l.Pairwise (fun a b => ¬ Clash (txn a) (txn b) ∧ ¬ Spoils label (txn a) (txn b)) →
    ∃ σ', Run label txn σ (l.map fun t => (t, txn t)) σ'
  | [], σ, _, _, _ => ⟨σ, .refl σ⟩
  | t :: rest, σ, nodup, ready, pairwise => by
      obtain ⟨seen, active, claimed, keptLive, epochsFresh, unborn⟩ := ready t List.mem_cons_self
      have readyRest : ∀ t' ∈ rest, Ready (txn := txn) (commitState label txn t σ) t' := by
        intro t' inRest
        have different : t' ≠ t := fun equal => (List.nodup_cons.mp nodup).1 (equal ▸ inRest)
        exact ready_commitState different (ready t' (List.mem_cons_of_mem _ inRest))
          ((List.pairwise_cons.mp pairwise).1 t' inRest).1 ((List.pairwise_cons.mp pairwise).1 t' inRest).2
      obtain ⟨σ', run⟩ := Run.commit_all rest (commitState label txn t σ) (List.nodup_cons.mp nodup).2
        readyRest (List.pairwise_cons.mp pairwise).2
      exact ⟨σ', .step (.commit σ t seen active claimed keptLive epochsFresh unborn) run⟩

open Classical in
/-- **The wave commit.** A batch of distinct ready transactions whose commits do not clash and have
acyclic precedence commits, one by one in a ranking order, as a protocol run. -/
theorem Run.wave {σ : ProtocolState O R T} {W : List T} (nodup : W.Nodup)
    (ready : ∀ t ∈ W, Ready (txn := txn) σ t)
    (noClash : (W.map txn).Pairwise (fun e d => ¬ Clash e d)) (acyclic : Acyclic label (W.map txn)) :
    ∃ l : List T, l.Perm W ∧ ∃ σ', Run label txn σ (l.map fun t => (t, txn t)) σ' := by
  obtain ⟨rank, ranked⟩ := ranked_of_acyclic acyclic
  let le : T → T → Bool := fun a b => decide (rank (txn a) ≤ rank (txn b))
  have perm := List.mergeSort_perm W le
  refine ⟨W.mergeSort le, perm, ?_⟩
  have sorted : (W.mergeSort le).Pairwise (fun a b => le a b = true) :=
    List.pairwise_mergeSort (fun a b c hab hbc => by
        simp only [le, decide_eq_true_eq] at hab hbc ⊢; omega)
      (fun a b => by simp only [le, Bool.or_eq_true, decide_eq_true_eq]; omega) W
  have noClashW : W.Pairwise (fun a b => ¬ Clash (txn a) (txn b)) := List.pairwise_map.mp noClash
  have noClashSorted : (W.mergeSort le).Pairwise (fun a b => ¬ Clash (txn a) (txn b)) :=
    (perm.pairwise_iff fun {x y} noXY clash => noXY clash.symm).mpr noClashW
  have members : (W.mergeSort le).Pairwise (fun a b => a ∈ W ∧ b ∈ W) :=
    List.pairwise_of_forall_mem_list fun a inA b inB => ⟨perm.subset inA, perm.subset inB⟩
  refine Run.commit_all _ σ (perm.nodup_iff.mpr nodup) (fun t member => ready t (perm.subset member)) ?_
  refine ((sorted.and noClashSorted).and members).imp ?_
  rintro a b ⟨⟨ordered, noClashAB⟩, inA, inB⟩
  refine ⟨noClashAB, fun spoils => ?_⟩
  simp only [le, decide_eq_true_eq] at ordered
  by_cases same : txn b = txn a
  · rw [same] at spoils
    exact not_spoils_self_of_not_clash (by rw [same] at noClashAB; exact noClashAB) spoils
  · have := ranked (txn b) (txn a) ⟨List.mem_map_of_mem inB, List.mem_map_of_mem inA, same, spoils⟩
    omega

/-! ## Controls -/

namespace Controls

open Atom

/-- The initial state of the controls: the token, born, nothing claimed, every transaction idle. -/
def protocolStart : ProtocolState ℕ Atom Bool where
  store := {0}
  born := {0}
  claim := fun _ => none
  epoch := fun _ => 0
  phase := fun _ => .idle

theorem protocolStart_initial : Initial protocolStart := ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩

/-- Two transactions that take the one token. -/
def rivals : Bool → Commit ℕ Atom
  | true => taker
  | false => taker₂

/-- **A lost claim aborts.** Both rivals begin; the first claims the token and commits. The token
is then gone, and in no continuation does the second commit. -/
theorem lost_claim_aborts :
    ∃ σ, Run Controls.label rivals protocolStart [(true, taker)] σ ∧
      ∀ σ' trace, Run Controls.label rivals σ trace σ' → ∀ entry ∈ trace, entry.1 ≠ false := by
  have run : Run Controls.label rivals protocolStart [(true, taker)] _ :=
    .step (.begin _ true rfl taker_enabled)
      (.step (.begin _ false rfl taker₂_enabled)
        (.step (.claim _ true (fun _ => 0) 0 rfl (by simp [rivals, taker]) (by decide) rfl
            (by simp [rivals, taker]))
          (.step (.commit _ true (fun _ => 0) rfl (by simp [rivals, taker]) (by simp [rivals, taker])
              (by simp [rivals, taker]) (by decide))
            (.refl _))))
  refine ⟨_, run, fun σ' trace later => ?_⟩
  obtain ⟨_, endStore, wf⟩ := run.refines (wellFormed_of_initial protocolStart_initial)
  refine later.gone_never_commits wf (o := 0) (by simp [rivals, taker₂]) ?_ ?_
  · simp [commitState, protocolStart]
  · rw [endStore]; decide

/-- An absence reader and a lock maker. -/
def lockRace : Bool → Commit ℕ Atom
  | true => unlessLocked
  | false => lockMaker

/-- **A stale epoch aborts.** Both begin; the lock maker commits, which moves the epoch of the lock
region; the absence reader is then stale and commits in no continuation. -/
theorem stale_epoch_aborts :
    ∃ σ, Run Controls.label lockRace protocolStart [(false, lockMaker)] σ ∧
      ∀ σ' trace, Run Controls.label lockRace σ trace σ' → ∀ entry ∈ trace, entry.1 ≠ true := by
  have run : Run Controls.label lockRace protocolStart [(false, lockMaker)] _ :=
    .step (.begin _ true rfl absence_holds_empty)
      (.step (.begin _ false rfl lockMaker_enabled)
        (.step (.commit _ false (fun _ => 0) rfl (by simp [lockRace, lockMaker])
            (by simp [lockRace, lockMaker]) (by simp [lockRace, lockMaker]) (by decide))
          (.refl _)))
  refine ⟨_, run, fun σ' trace later => ?_⟩
  refine later.stale_never_commits (t := true) (seen := fun _ => 0) (read := ⟨isLock, ∅⟩)
    (by simp [lockRace, unlessLocked]) (Or.inr ⟨?_, ?_⟩)
  · simp [commitState, protocolStart]
  · simp only [commitState]
    rw [if_pos ⟨1, by simp [lockRace, lockMaker], rfl⟩]
    simp

/-- The first rival has begun. -/
def firstBegun : ProtocolState ℕ Atom Bool :=
  { protocolStart with
    phase := Function.update protocolStart.phase true (.active protocolStart.epoch) }

/-- Both rivals have begun. -/
def bothBegun : ProtocolState ℕ Atom Bool :=
  { firstBegun with phase := Function.update firstBegun.phase false (.active firstBegun.epoch) }

/-- Both rivals have begun and the first has claimed the token. -/
def firstClaimed : ProtocolState ℕ Atom Bool :=
  { bothBegun with claim := Function.update bothBegun.claim 0 (some true) }

theorem firstClaimed_reachable : Run Controls.label rivals protocolStart [] firstClaimed :=
  .step (.begin _ true rfl taker_enabled)
    (.step (.begin _ false rfl taker₂_enabled)
      (.step (.claim _ true (fun _ => 0) 0 rfl (by simp [rivals, taker]) (by decide) rfl
          (by simp [rivals, taker]))
        (.refl _)))

theorem firstClaimed_wellFormed : WellFormed Controls.label rivals firstClaimed :=
  (firstClaimed_reachable.refines (wellFormed_of_initial protocolStart_initial)).2.2

/-- **The wait index is not vacuous**: at a reachable, well-formed state the second rival waits
for the first. -/
theorem waitsFor_inhabited : WaitsFor (txn := rivals) firstClaimed false true := by
  refine ⟨0, ⟨by simp [rivals, taker₂], ?_, ?_⟩, ?_⟩
  · simp [firstClaimed, bothBegun, firstBegun, protocolStart]
  · intro o' _ lt
    omega
  · simp [firstClaimed]

/-- ... and, as `waitsFor_acyclic` says, the second rival does not wait for itself. -/
theorem waitsFor_instance_acyclic :
    ¬ Relation.TransGen (WaitsFor (txn := rivals) firstClaimed) false false :=
  waitsFor_acyclic firstClaimed_wellFormed false

/-! ### Ready transactions -/

/-- **Positive control**: the first rival is ready: active, holding the claim on the token it
takes, keeping nothing, querying nothing, and its output unborn. -/
theorem taker_ready : Ready (txn := rivals) firstClaimed true := by
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · simp [rivals, taker, firstClaimed]
  · simp [rivals, taker]
  · simp [rivals, taker]
  · decide

/-- **Negative control**: the second rival is active too, but the token's claim is the first
rival's, so it is not ready. -/
theorem taker₂_not_ready : ¬ Ready (txn := rivals) firstClaimed false := by
  rintro ⟨seen, -, claimed, -⟩
  have := claimed 0 (by simp [rivals, taker₂])
  simp [firstClaimed] at this

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
