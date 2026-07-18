import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.AtomicResourceLockOrder

/-!
# Speculative all-or-rollback occurrence claims

This module gives an executable reference model for claiming the exact finite
occurrence family of one atomic resource join.  Individual claims are tried in
list order.  A failed attempt returns the original ownership state, so no
partially acquired prefix is observable.  This is a protocol obligation, not
an encoding of the operation into binary rho.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed

namespace SpeculativeOccurrenceClaims

universe v w

/-- Ownership of a finite family of resource occurrences. -/
structure State (Transaction : Type v) (Resource : Type w) where
  owner : Resource → Option Transaction

/-- Claim one currently unowned occurrence. -/
def claimOne [DecidableEq Transaction] [DecidableEq Resource]
    (state : State Transaction Resource)
    (transaction : Transaction) (resource : Resource) :
    Option (State Transaction Resource) :=
  if state.owner resource = none then
    some ⟨Function.update state.owner resource (some transaction)⟩
  else
    none

/-- Try the requested occurrences in the supplied order.  Failure is kept as
`none`; the public `attempt` operation below performs the rollback. -/
def acquireAll [DecidableEq Transaction] [DecidableEq Resource]
    (state : State Transaction Resource)
    (transaction : Transaction) : List Resource →
    Option (State Transaction Resource)
  | [] => some state
  | resource :: rest =>
      (claimOne state transaction resource).bind fun next =>
        acquireAll next transaction rest

/-- Observable result of an all-or-rollback claim attempt. -/
inductive Outcome (Transaction : Type v) (Resource : Type w)
  | committed (state : State Transaction Resource)
  | contended (state : State Transaction Resource)

/-- Try all occurrences, exposing the committed ownership state only after
every claim succeeds.  Any failed prefix rolls back to the original state. -/
def attempt [DecidableEq Transaction] [DecidableEq Resource]
    (state : State Transaction Resource)
    (transaction : Transaction) (resources : List Resource) :
    Outcome Transaction Resource :=
  match acquireAll state transaction resources with
  | some target => .committed target
  | none => .contended state

/-- A successful single claim starts from a free occurrence and changes only
that occurrence's owner. -/
theorem claimOne_success
    [DecidableEq Transaction] [DecidableEq Resource]
    {state target : State Transaction Resource}
    {transaction : Transaction} {resource : Resource}
    (success : claimOne state transaction resource = some target) :
    state.owner resource = none ∧
      ∀ queried, target.owner queried =
        if queried = resource then some transaction else state.owner queried := by
  by_cases free : state.owner resource = none
  · have target_eq :
        (⟨Function.update state.owner resource (some transaction)⟩ :
          State Transaction Resource) = target := by
      simpa [claimOne, free] using success
    subst target
    refine ⟨free, ?_⟩
    intro queried
    by_cases same : queried = resource
    · subst queried
      simp
    · simp [Function.update, same]
  · simp [claimOne, free] at success

/-- Successful sequential acquisition has a nonduplicated request family,
starts with every requested occurrence free, and changes exactly those
owners. -/
theorem acquireAll_success
    [DecidableEq Transaction] [DecidableEq Resource]
    {state target : State Transaction Resource}
    {transaction : Transaction} {resources : List Resource}
    (success : acquireAll state transaction resources = some target) :
    resources.Nodup ∧
      (∀ resource ∈ resources, state.owner resource = none) ∧
      ∀ resource, target.owner resource =
        if resource ∈ resources then some transaction else state.owner resource := by
  induction resources generalizing state target with
  | nil =>
      simp [acquireAll] at success ⊢
      subst target
      intro resource
      rfl
  | cons head tail ih =>
      simp only [acquireAll] at success
      cases claim_eq : claimOne state transaction head with
      | none =>
          simp [claim_eq] at success
      | some next =>
          have tail_success :
              acquireAll next transaction tail = some target := by
            simpa [claim_eq] using success
          obtain ⟨head_free, next_owner⟩ := claimOne_success claim_eq
          obtain ⟨tail_nodup, tail_free, target_owner⟩ := ih tail_success
          have head_not_mem : head ∉ tail := by
            intro head_mem
            have next_free := tail_free head head_mem
            have next_claimed := next_owner head
            simp at next_claimed
            rw [next_claimed] at next_free
            contradiction
          refine ⟨List.nodup_cons.mpr ⟨head_not_mem, tail_nodup⟩, ?_, ?_⟩
          · intro resource resource_mem
            rcases List.mem_cons.mp resource_mem with rfl | resource_mem
            · exact head_free
            · have free_next := tail_free resource resource_mem
              have distinct : resource ≠ head := by
                intro same
                exact head_not_mem (same ▸ resource_mem)
              rw [next_owner resource, if_neg distinct] at free_next
              exact free_next
          · intro resource
            rw [target_owner resource]
            by_cases same : resource = head
            · subst resource
              simp [head_not_mem, next_owner]
            · simp [same, next_owner resource]

/-- A failed public attempt exposes exactly the state from before its first
claim, never an intermediate prefix. -/
theorem attempt_contended_iff
    [DecidableEq Transaction] [DecidableEq Resource]
    {state exposed : State Transaction Resource}
    {transaction : Transaction} {resources : List Resource} :
    attempt state transaction resources = .contended exposed ↔
      acquireAll state transaction resources = none ∧ exposed = state := by
  unfold attempt
  cases acquired : acquireAll state transaction resources with
  | none => simp [eq_comm]
  | some target => simp

/-- A committed public attempt owns exactly its duplicate-free resource
family and preserves every owner outside it. -/
theorem attempt_committed
    [DecidableEq Transaction] [DecidableEq Resource]
    {state target : State Transaction Resource}
    {transaction : Transaction} {resources : List Resource}
    (committed : attempt state transaction resources = .committed target) :
    resources.Nodup ∧
      (∀ resource ∈ resources, state.owner resource = none) ∧
      ∀ resource, target.owner resource =
        if resource ∈ resources then some transaction else state.owner resource := by
  unfold attempt at committed
  cases acquired : acquireAll state transaction resources with
  | none => simp [acquired] at committed
  | some actual =>
      simp [acquired] at committed
      subst target
      exact acquireAll_success acquired

/-- A duplicate-free family of free occurrences can be acquired completely. -/
theorem acquireAll_complete
    [DecidableEq Transaction] [DecidableEq Resource]
    {state : State Transaction Resource}
    {transaction : Transaction} {resources : List Resource}
    (nodup : resources.Nodup)
    (free : ∀ resource ∈ resources, state.owner resource = none) :
    ∃ target, acquireAll state transaction resources = some target := by
  induction resources generalizing state with
  | nil =>
      exact ⟨state, rfl⟩
  | cons head tail ih =>
      have head_free : state.owner head = none := free head (by simp)
      let next : State Transaction Resource :=
        ⟨Function.update state.owner head (some transaction)⟩
      have claim_eq : claimOne state transaction head = some next := by
        simp [claimOne, head_free, next]
      have tail_nodup : tail.Nodup := (List.nodup_cons.mp nodup).2
      have head_not_mem : head ∉ tail := (List.nodup_cons.mp nodup).1
      have tail_free : ∀ resource ∈ tail, next.owner resource = none := by
        intro resource resource_mem
        have distinct : resource ≠ head := by
          intro same
          exact head_not_mem (same ▸ resource_mem)
        rw [show next.owner resource = state.owner resource by
          simp [next, Function.update, distinct]]
        exact free resource (by simp [resource_mem])
      obtain ⟨target, tail_success⟩ := ih tail_nodup tail_free
      exact ⟨target, by simp [acquireAll, claim_eq, tail_success]⟩

/-- A public attempt commits exactly when its resource family is duplicate-free
and every requested occurrence was free initially. -/
theorem exists_attempt_committed_iff
    [DecidableEq Transaction] [DecidableEq Resource]
    {state : State Transaction Resource}
    {transaction : Transaction} {resources : List Resource} :
    (∃ target, attempt state transaction resources = .committed target) ↔
      resources.Nodup ∧
        ∀ resource ∈ resources, state.owner resource = none := by
  constructor
  · rintro ⟨target, committed⟩
    obtain ⟨nodup, free, _exact⟩ := attempt_committed committed
    exact ⟨nodup, free⟩
  · rintro ⟨nodup, free⟩
    obtain ⟨target, acquired⟩ :=
      acquireAll_complete (transaction := transaction) nodup free
    exact ⟨target, by simp [attempt, acquired]⟩

/-- The raw runtime's canonical lock plan is therefore admissible whenever
all of its enabled source occurrences are currently unowned. -/
theorem enabled_lockOrder_complete
    [DecidableEq Transaction]
    {state : State Transaction Nat} {transaction : Transaction}
    {config : RawCostConfig} {step : RawRuntimeStep}
    (enabled : step ∈ runtimeCostCandidatesFromConfig config)
    (free : ∀ resource ∈ step.lockOrder, state.owner resource = none) :
    ∃ target, acquireAll state transaction step.lockOrder = some target := by
  exact acquireAll_complete (step.lockOrder_nodup enabled) free

end SpeculativeOccurrenceClaims

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed
