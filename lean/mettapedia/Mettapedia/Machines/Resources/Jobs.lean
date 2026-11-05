import Mettapedia.Machines.Resources.StateIndexed

/-!+# Persistent jobs and one-use effect authority

The ledger, not algebraic compatibility alone, controls issuance. Issued job
identities are never forgotten, including after termination. Transfer and
parking retain a single entry; an effect consumes its permission before a
terminal result can be reported. Scheduler fairness is not a consequence of
registering a wake source.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Resources.Jobs

inductive Outcome where
  | complete | failed | superseded | indeterminate
  deriving DecidableEq, Repr

inductive Phase where
  | running | parked | terminal (outcome : Outcome)
  deriving DecidableEq, Repr

structure Entry where
  holder : Nat
  phase : Phase
  wakeSource : Option Nat
  wakePending : Bool
  effectSpent : Bool
  deriving DecidableEq, Repr

structure Ledger where
  entries : JobId → Option Entry
  issued : Finset JobId
  effects : Finset JobId

def Valid (s : Ledger) : Prop :=
  (∀ id, (s.entries id).isSome = true ↔ id ∈ s.issued) ∧
  (∀ id entry, s.entries id = some entry → (entry.effectSpent = true ↔ id ∈ s.effects)) ∧
  s.effects ⊆ s.issued

def initial : Ledger := ⟨fun _ => none, ∅, ∅⟩

theorem initial_valid : Valid initial := by simp [Valid, initial]

def mint (s : Ledger) (actor : Nat) (id : JobId) : Option Ledger :=
  if actor = id.owner ∧ 0 < id.number ∧ id ∉ s.issued then
    some ⟨Function.update s.entries id (some ⟨actor, .running, none, false, false⟩),
      insert id s.issued, s.effects⟩
  else none

def modify (s : Ledger) (actor : Nat) (id : JobId) (f : Entry → Option Entry) : Option Ledger := do
  let entry ← s.entries id
  if entry.holder ≠ actor then none else do
    let next ← f entry
    return { s with entries := Function.update s.entries id (some next) }

def transfer (s : Ledger) (actor target : Nat) (id : JobId) : Option Ledger :=
  modify s actor id fun entry =>
    if entry.phase = .running then some { entry with holder := target } else none

def registerWake (s : Ledger) (actor : Nat) (id : JobId) (source : Nat) : Option Ledger :=
  modify s actor id fun entry =>
    if entry.phase = .running ∧ entry.wakeSource = none then
      some { entry with wakeSource := some source } else none

def wake (s : Ledger) (id : JobId) (source : Nat) : Option Ledger := do
  let entry ← s.entries id
  if entry.wakeSource = some source ∧
      (entry.phase = .running ∨ entry.phase = .parked) then
    some { s with entries := Function.update s.entries id (some { entry with wakePending := true }) }
  else none

def park (s : Ledger) (actor : Nat) (id : JobId) : Option Ledger :=
  modify s actor id fun entry =>
    if entry.phase = .running ∧ entry.wakeSource.isSome then
      some { entry with phase := (if entry.wakePending then .running else .parked), wakePending := false } else none

def resume (s : Ledger) (actor : Nat) (id : JobId) : Option Ledger :=
  modify s actor id fun entry =>
    if entry.phase = .parked ∧ entry.wakePending then
      some { entry with phase := .running, wakePending := false } else none

/-- Effect issuance and consumption are separate. Retrying transport does
not call mint and cannot recover the spent permission. -/
def spendEffect (s : Ledger) (actor : Nat) (id : JobId) : Option Ledger :=
  match s.entries id with
  | none => none
  | some entry =>
    if entry.holder = actor ∧ entry.phase = .running ∧ entry.effectSpent = false then
      some ⟨Function.update s.entries id (some { entry with effectSpent := true }), s.issued, insert id s.effects⟩
    else none

def finish (s : Ledger) (actor : Nat) (id : JobId) (outcome : Outcome) : Option Ledger :=
  modify s actor id fun entry =>
    if entry.phase = .running ∧ (outcome = .indeterminate ∨ entry.effectSpent = true ∨
        outcome = .failed ∨ outcome = .superseded) then
      some { entry with phase := .terminal outcome, wakeSource := none, wakePending := false }
    else none

theorem modify_found {s next : Ledger} {actor : Nat} {id : JobId} {f : Entry → Option Entry}
    (accepted : modify s actor id f = some next) :
    ∃ entry changed, s.entries id = some entry ∧ entry.holder = actor ∧
      f entry = some changed ∧ next = { s with entries := Function.update s.entries id (some changed) } := by
  unfold modify at accepted
  cases found : s.entries id with
  | none => simp [found] at accepted
  | some entry =>
    by_cases owner : entry.holder = actor
    · cases updated : f entry with
      | none => simp [found, owner, updated] at accepted
      | some changed =>
        simp [found, owner, updated] at accepted
        exact ⟨entry, changed, rfl, owner, updated, accepted.symm⟩
    · simp [found, owner] at accepted

theorem modify_preserves_issuance {s next : Ledger} {actor : Nat} {id : JobId}
    {f : Entry → Option Entry} (accepted : modify s actor id f = some next) :
    next.issued = s.issued ∧ next.effects = s.effects ∧ (next.entries id).isSome = true := by
  obtain ⟨_, changed, _, _, _, rfl⟩ := modify_found accepted
  simp

theorem modify_preserves_valid {s next : Ledger} (valid : Valid s) {actor : Nat}
    {id : JobId} {f : Entry → Option Entry}
    (sameEffect : ∀ entry changed, f entry = some changed → changed.effectSpent = entry.effectSpent)
    (accepted : modify s actor id f = some next) : Valid next := by
  obtain ⟨entry, changed, found, _, updated, rfl⟩ := modify_found accepted
  have issued := (valid.1 id).mp (by simp [found])
  constructor
  · intro key
    by_cases same : key = id
    · subst key; simpa using issued
    · simpa [same] using valid.1 key
  · refine ⟨?_, valid.2.2⟩
    intro key value stored
    by_cases same : key = id
    · subst key
      simp only [Function.update_self, Option.some.injEq] at stored
      subst value
      simpa [sameEffect entry changed updated] using valid.2.1 id entry found
    · exact valid.2.1 key value (by simpa [same] using stored)

theorem mint_preserves_valid {s next : Ledger} (valid : Valid s) (actor : Nat) (id : JobId)
    (accepted : mint s actor id = some next) : Valid next := by
  unfold mint at accepted
  split at accepted
  · rename_i allowed
    have unspent : id ∉ s.effects := fun spent => allowed.2.2 (valid.2.2 spent)
    cases Option.some.inj accepted
    constructor
    · intro key
      by_cases same : key = id
      · subst key; simp
      · simpa [same] using valid.1 key
    · refine ⟨?_, fun key member => Finset.mem_insert_of_mem (valid.2.2 member)⟩
      intro key entry stored
      by_cases same : key = id
      · subst key
        simp only [Function.update_self, Option.some.injEq] at stored
        subst entry
        simpa using unspent
      · exact valid.2.1 key entry (by simpa [same] using stored)
  · cases accepted

theorem spend_preserves_valid {s next : Ledger} (valid : Valid s) (actor : Nat) (id : JobId)
    (accepted : spendEffect s actor id = some next) : Valid next := by
  unfold spendEffect at accepted
  cases found : s.entries id with
  | none => simp [found] at accepted
  | some entry =>
    simp only [found] at accepted
    split at accepted
    · have issued := (valid.1 id).mp (by simp [found])
      cases Option.some.inj accepted
      constructor
      · intro key
        by_cases same : key = id
        · subst key; simpa using issued
        · simpa [same] using valid.1 key
      · constructor
        · intro key value stored
          by_cases same : key = id
          · subst key
            simp only [Function.update_self, Option.some.injEq] at stored
            subst value
            simp
          · simpa [same] using valid.2.1 key value (by simpa [same] using stored)
        · intro key member
          rcases Finset.mem_insert.mp member with same | old
          · simpa [same] using issued
          · exact valid.2.2 old
    · cases accepted

def Holds (s : Ledger) (actor : Nat) (id : JobId) : Prop :=
  ∃ entry, s.entries id = some entry ∧ entry.holder = actor

theorem holder_unique (s : Ledger) (id : JobId) (a b : Nat)
    (left : Holds s a id) (right : Holds s b id) : a = b := by
  obtain ⟨entry, found, owns⟩ := left
  obtain ⟨other, foundOther, ownsOther⟩ := right
  have same : entry = other := Option.some.inj (found.symm.trans foundOther)
  exact owns.symm.trans (same ▸ ownsOther)

theorem mint_requires_issuer {s next : Ledger} (actor : Nat) (id : JobId)
    (accepted : mint s actor id = some next) : actor = id.owner := by
  unfold mint at accepted
  split at accepted
  · rename_i allowed; exact allowed.1
  · cases accepted

theorem spend_marks_consumed {s next : Ledger} (actor : Nat) (id : JobId)
    (accepted : spendEffect s actor id = some next) :
    ∃ entry, next.entries id = some entry ∧ entry.effectSpent = true := by
  unfold spendEffect at accepted
  cases found : s.entries id with
  | none => simp [found] at accepted
  | some entry =>
    simp only [found] at accepted
    split at accepted
    · cases Option.some.inj accepted
      exact ⟨{ entry with effectSpent := true }, by simp, rfl⟩
    · cases accepted

theorem transfer_preserves_valid {s next : Ledger} (valid : Valid s)
    (actor target : Nat) (id : JobId) (accepted : transfer s actor target id = some next) :
    Valid next := by
  apply modify_preserves_valid valid _ accepted
  intro entry changed updated
  split at updated
  · cases Option.some.inj updated; rfl
  · cases updated

theorem park_preserves_valid {s next : Ledger} (valid : Valid s)
    (actor : Nat) (id : JobId) (accepted : park s actor id = some next) : Valid next := by
  apply modify_preserves_valid valid _ accepted
  intro entry changed updated
  split at updated
  · cases Option.some.inj updated; rfl
  · cases updated

theorem resume_preserves_valid {s next : Ledger} (valid : Valid s)
    (actor : Nat) (id : JobId) (accepted : resume s actor id = some next) : Valid next := by
  apply modify_preserves_valid valid _ accepted
  intro entry changed updated
  split at updated
  · cases Option.some.inj updated; rfl
  · cases updated

theorem registerWake_preserves_valid {s next : Ledger} (valid : Valid s)
    (actor : Nat) (id : JobId) (source : Nat)
    (accepted : registerWake s actor id source = some next) : Valid next := by
  apply modify_preserves_valid valid _ accepted
  intro entry changed updated
  split at updated
  · cases Option.some.inj updated; rfl
  · cases updated

theorem finish_preserves_valid {s next : Ledger} (valid : Valid s)
    (actor : Nat) (id : JobId) (outcome : Outcome)
    (accepted : finish s actor id outcome = some next) : Valid next := by
  apply modify_preserves_valid valid _ accepted
  intro entry changed updated
  split at updated
  · cases Option.some.inj updated; rfl
  · cases updated

theorem wake_preserves_valid {s next : Ledger} (valid : Valid s)
    (id : JobId) (source : Nat) (accepted : wake s id source = some next) : Valid next := by
  cases found : s.entries id with
  | none => simp [wake, found] at accepted
  | some entry =>
    have asModify : wake s id source = modify s entry.holder id (fun old =>
        if old.wakeSource = some source ∧ (old.phase = .running ∨ old.phase = .parked)
        then some { old with wakePending := true } else none) := by
      by_cases ready : entry.wakeSource = some source ∧ (entry.phase = .running ∨ entry.phase = .parked)
      · simp [wake, modify, found, ready]
      · simp [wake, modify, found, ready]
    rw [asModify] at accepted
    apply modify_preserves_valid valid _ accepted
    intro old changed updated
    split at updated
    · cases Option.some.inj updated; rfl
    · cases updated

theorem terminal_cannot_spend (s : Ledger) (actor : Nat) (id : JobId) (entry : Entry)
    (outcome : Outcome) (found : s.entries id = some entry)
    (terminal : entry.phase = .terminal outcome) : spendEffect s actor id = none := by
  simp [spendEffect, found, terminal]

theorem retired_cannot_remint (s : Ledger) (actor : Nat) (id : JobId) (issued : id ∈ s.issued) :
    mint s actor id = none := by simp [mint, issued]

theorem wrong_holder_cannot_transfer (s : Ledger) (actor target : Nat) (id : JobId)
    (entry : Entry) (found : s.entries id = some entry) (wrong : entry.holder ≠ actor) :
    transfer s actor target id = none := by simp [transfer, modify, found, wrong]

theorem spent_cannot_repeat (s : Ledger) (actor : Nat) (id : JobId) (entry : Entry)
    (found : s.entries id = some entry) (spent : entry.effectSpent = true) :
    spendEffect s actor id = none := by simp [spendEffect, found, spent]

theorem no_wake_no_park (s : Ledger) (actor : Nat) (id : JobId) (entry : Entry)
    (found : s.entries id = some entry) (noneRegistered : entry.wakeSource = none) :
    park s actor id = none := by simp [park, modify, found, noneRegistered]

theorem park_conserves_obligation {s next : Ledger} (actor : Nat) (id : JobId)
    (accepted : park s actor id = some next) :
    next.issued = s.issued ∧ next.effects = s.effects ∧ (next.entries id).isSome = true :=
  modify_preserves_issuance accepted

theorem resume_conserves_obligation {s next : Ledger} (actor : Nat) (id : JobId)
    (accepted : resume s actor id = some next) :
    next.issued = s.issued ∧ next.effects = s.effects ∧ (next.entries id).isSome = true :=
  modify_preserves_issuance accepted

def Outstanding (s : Ledger) (id : JobId) : Prop :=
  ∃ entry, s.entries id = some entry ∧ ∀ result, entry.phase ≠ .terminal result

/-- Normal shutdown must exhibit terminal entries for every issued identity;
omitting a ledger entry is not a discharge rule. -/
def MayShutdown (s : Ledger) : Prop :=
  ∀ id ∈ s.issued, ∃ entry result, s.entries id = some entry ∧ entry.phase = .terminal result

theorem outstanding_prevents_shutdown (s : Ledger) (valid : Valid s) (id : JobId)
    (pending : Outstanding s id) : ¬ MayShutdown s := by
  obtain ⟨entry, found, live⟩ := pending
  intro shutdown
  have issued := (valid.1 id).mp (by simp [found])
  obtain ⟨other, result, same, terminal⟩ := shutdown id issued
  have : other = entry := Option.some.inj (same.symm.trans found)
  subst other
  exact live result terminal

namespace Controls

def job : JobId := ⟨3, 1⟩
def issued : Ledger := (mint initial 3 job).getD initial
def registered : Ledger := (registerWake issued 3 job 9).getD initial
def earlyWake : Ledger := (wake registered job 9).getD initial
def parked : Ledger := (park registered 3 job).getD initial

theorem wrong_issuer_refused : mint initial 4 job = none := by decide
theorem zero_job_refused : mint initial 3 ⟨3, 0⟩ = none := by decide
theorem no_source_cannot_park : park issued 3 job = none := by decide
theorem early_wake_not_lost :
    ((park earlyWake 3 job).getD initial).entries job = some ⟨3, .running, some 9, false, false⟩ := by decide
theorem duplicate_wake_remains_pending :
    (wake earlyWake job 9).map (fun ledger => ledger.entries job) =
      some (some ⟨3, .running, some 9, true, false⟩) := by decide
theorem parked_requires_notification : resume parked 3 job = none := by decide
theorem foreign_wake_refused : wake parked job 8 = none := by decide
theorem matching_wake_resumes :
    (((wake parked job 9).bind fun s => resume s 3 job).getD initial).entries job =
      some ⟨3, .running, some 9, false, false⟩ := by decide
theorem effect_is_not_reissued :
    ((spendEffect issued 3 job).bind fun s => spendEffect s 3 job) = none := by decide
theorem transferred_holder_is_exclusive :
    ((transfer issued 3 4 job).bind fun s => transfer s 3 5 job) = none := by decide
theorem terminal_job_cannot_be_minted_again :
    ((finish issued 3 job .superseded).bind fun s => mint s 3 job) = none := by decide
theorem unperformed_effect_cannot_claim_completion : finish issued 3 job .complete = none := by decide
theorem holder_death_can_discharge_as_indeterminate :
    (finish issued 3 job .indeterminate).isSome = true := by decide

end Controls

#print axioms park_preserves_valid
#print axioms resume_preserves_valid
#print axioms outstanding_prevents_shutdown

end Mettapedia.Machines.Resources.Jobs
