import Mettapedia.Machines.ReadOnlyQuery
import Mettapedia.GSLT.Core.DerivedCacheInvalidationAlgebra

/-!
# Reuse of read-certified pure observations

An existing authority-indexed entry carries an observation of a fixed query
family. Reuse checks its authority, query key and complete read certificate.
The population path evaluates the query and records its reads; the hit path
validates those reads without rerunning the query. These are different
algorithms, and their results are proved equal.

Authority includes the identity and governing version of the program that
defines the query family. Keys include modes and input operands. A live binding
payload, an effectful classifier or an in-progress producer is not an immutable
fact of this interface. Materialization remains per invocation.

The work counter records fresh query executions only. Certificate validation,
lookup, allocation and physical runtime costs are not included.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ReadCertifiedQueryReuse

open ReadOnlyQuery

universe u v w x y z

variable {Authority : Type u} {Query : Type v} {Key : Type w}
variable {Value : Type x} {Answer : Type y}

abbrev Entry (Authority : Type u) (Query : Type v) (Key : Type w)
    (Value : Type x) (Answer : Type y) :=
  Mettapedia.GSLT.Core.DerivedCacheInvalidationAlgebra.AuthorityIndexed.Entry
    Authority Query (Observation Key Value Answer)

namespace Supported

/-- An independently specified observer with a finite read certificate.
Changing its state under the same semantic authority preserves the answer
when the historical certificate still agrees. The certificate may be a
conservative support rather than the exact execution trace. -/
structure Family (State : Type z) (Authority : Type u) (Query : Type v)
    (Key : Type w) (Value : Type x) (Answer : Type y) where
  authority : State → Authority
  memory : State → Key → Value
  observe : State → Query → Observation Key Value Answer
  certifies : ∀ state query, Agrees (memory state) (observe state query).reads
  stable : ∀ first second query, authority second = authority first →
    Agrees (memory second) (observe first query).reads →
      (observe second query).answer = (observe first query).answer

variable {State : Type z}

/-- A stored result and its authority come from the same historical state.
An arbitrary entry with an empty read list does not establish this invariant. -/
def Recorded (family : Family State Authority Query Key Value Answer)
    (entry : Entry Authority Query Key Value Answer) : Prop :=
  ∃ state, entry.authority = family.authority state ∧
    entry.value = family.observe state entry.key

def populate (family : Family State Authority Query Key Value Answer)
    (state : State) (query : Query) : Entry Authority Query Key Value Answer :=
  ⟨family.authority state, query, family.observe state query⟩

theorem populate_recorded (family : Family State Authority Query Key Value Answer)
    (state : State) (query : Query) : Recorded family (populate family state query) :=
  ⟨state, rfl, rfl⟩

def admissible [DecidableEq Authority] [DecidableEq Query] [DecidableEq Value]
    (family : Family State Authority Query Key Value Answer)
    (state : State) (query : Query) (entry : Entry Authority Query Key Value Answer) : Bool :=
  decide (entry.authority = family.authority state ∧ entry.key = query) &&
    checkReads (family.memory state) entry.value.reads

theorem admissible_iff [DecidableEq Authority] [DecidableEq Query] [DecidableEq Value]
    (family : Family State Authority Query Key Value Answer)
    (state : State) (query : Query) (entry : Entry Authority Query Key Value Answer) :
    admissible family state query entry = true ↔
      entry.authority = family.authority state ∧ entry.key = query ∧
        Agrees (family.memory state) entry.value.reads := by
  simp [admissible, checkReads_iff, and_assoc]

/-- Validation is a distinct algorithm from evaluating the observer. -/
def reuse [DecidableEq Authority] [DecidableEq Query] [DecidableEq Value]
    (family : Family State Authority Query Key Value Answer)
    (state : State) (query : Query) (entry : Entry Authority Query Key Value Answer) :
    Answer × Nat :=
  if admissible family state query entry then (entry.value.answer, 0)
  else ((family.observe state query).answer, 1)

/-- The common reuse law needs both historical provenance and an independently
proved support law. It preserves the entire answer, not only answer support. -/
theorem reuse_exact [DecidableEq Authority] [DecidableEq Query] [DecidableEq Value]
    (family : Family State Authority Query Key Value Answer)
    (state : State) (query : Query) (entry : Entry Authority Query Key Value Answer)
    (recorded : Recorded family entry) :
    (reuse family state query entry).1 = (family.observe state query).answer := by
  unfold reuse
  split
  · rename_i accepted
    obtain ⟨old, authority, history⟩ := recorded
    obtain ⟨sameAuthority, sameQuery, reads⟩ :=
      (admissible_iff family state query entry).mp accepted
    have retainedAuthority : family.authority state = family.authority old :=
      sameAuthority.symm.trans authority
    rw [history] at reads ⊢
    have stable := family.stable old state entry.key retainedAuthority reads
    simpa only [sameQuery] using stable.symm
  · rfl

/-- Fresh invocation materialization follows reuse of immutable facts. -/
theorem materialized_exact [DecidableEq Authority] [DecidableEq Query] [DecidableEq Value]
    {Invocation : Type*} {Result : Type*}
    (family : Family State Authority Query Key Value Answer)
    (state : State) (query : Query) (entry : Entry Authority Query Key Value Answer)
    (recorded : Recorded family entry)
    (materialize : Invocation → Answer → Result) (invocation : Invocation) :
    materialize invocation (reuse family state query entry).1 =
      materialize invocation (family.observe state query).answer := by
  rw [reuse_exact family state query entry recorded]

theorem unchanged_reuses [DecidableEq Authority] [DecidableEq Query] [DecidableEq Value]
    (family : Family State Authority Query Key Value Answer) (state : State) (query : Query) :
    reuse family state query (populate family state query) =
      ((family.observe state query).answer, 0) := by
  have accepted : admissible family state query (populate family state query) = true :=
    (admissible_iff _ _ _ _).mpr ⟨rfl, rfl, family.certifies state query⟩
  unfold reuse
  rw [if_pos accepted]
  rfl

/-! ### The authority-indexed law as the family that reads nothing

A derivation determined by its authority and query alone is a supported
family with no keys.  Its reuse algorithm is the earlier authority-indexed
`reuseOrRecompute`, and an entry is recorded exactly when it is sound in the
earlier sense, so `reuseOrRecompute_exact` is the instance of `reuse_exact`
at this family. -/

/-- The family of a derivation that depends on authority and query only. -/
def ofDerivation (derive : Authority → Query → Answer) :
    Family Authority Authority Query Empty Unit Answer where
  authority := id
  memory := fun _ key => key.elim
  observe := fun authority query => ⟨derive authority query, []⟩
  certifies := by
    intro authority query read member
    cases member
  stable := by
    intro first second query same _
    cases same
    rfl

/-- There are no keys, so every certificate of this family is empty. -/
theorem reads_eq_nil : ∀ reads : Reads Empty Unit, reads = []
  | [] => rfl
  | read :: _ => read.1.elim

theorem recorded_ofDerivation_iff (derive : Authority → Query → Answer)
    (entry : Entry Authority Query Empty Unit Answer) :
    Recorded (ofDerivation derive) entry ↔
      entry.value.answer = derive entry.authority entry.key := by
  constructor
  · rintro ⟨authority, same, history⟩
    change entry.authority = authority at same
    rw [history, same]
    rfl
  · intro sound
    refine ⟨entry.authority, rfl, ?_⟩
    obtain ⟨authority, query, answer, reads⟩ := entry
    cases reads_eq_nil reads
    dsimp only at sound
    subst sound
    rfl

theorem reuse_ofDerivation [DecidableEq Authority] [DecidableEq Query]
    (derive : Authority → Query → Answer) (authority : Authority) (query : Query)
    (entry : Entry Authority Query Empty Unit Answer) :
    (reuse (ofDerivation derive) authority query entry).1 =
      Mettapedia.GSLT.Core.DerivedCacheInvalidationAlgebra.AuthorityIndexed.reuseOrRecompute
        derive authority query ⟨entry.authority, entry.key, entry.value.answer⟩ := by
  obtain ⟨entryAuthority, entryQuery, answer, reads⟩ := entry
  cases reads_eq_nil reads
  by_cases agrees : entryAuthority = authority ∧ entryQuery = query
  · have accepted : admissible (ofDerivation derive) authority query
        ⟨entryAuthority, entryQuery, ⟨answer, []⟩⟩ = true :=
      (admissible_iff _ _ _ _).mpr ⟨agrees.1, agrees.2, fun _ member => by cases member⟩
    simp only [reuse, accepted, if_true,
      Mettapedia.GSLT.Core.DerivedCacheInvalidationAlgebra.AuthorityIndexed.reuseOrRecompute,
      if_pos agrees]
  · have rejected : admissible (ofDerivation derive) authority query
        ⟨entryAuthority, entryQuery, ⟨answer, []⟩⟩ = false := by
      apply Bool.eq_false_iff.mpr
      intro accepted
      obtain ⟨sameAuthority, sameQuery, _⟩ := (admissible_iff _ _ _ _).mp accepted
      exact agrees ⟨sameAuthority, sameQuery⟩
    simp only [reuse, rejected, Bool.false_eq_true, if_false,
      Mettapedia.GSLT.Core.DerivedCacheInvalidationAlgebra.AuthorityIndexed.reuseOrRecompute,
      if_neg agrees]
    rfl

end Supported

/-- Exact adaptive traces instantiate the common support interface. -/
def programObserver (family : Authority → Query → Program Key Value Answer) :
    Supported.Family (Authority × (Key → Value)) Authority Query Key Value Answer where
  authority := Prod.fst
  memory := Prod.snd
  observe := fun state query => run state.2 (family state.1 query)
  certifies := fun state query => run_agrees state.2 (family state.1 query)
  stable := by
    intro first second query authority reads
    change second.1 = first.1 at authority
    change Agrees second.2 (run first.2 (family first.1 query)).reads at reads
    rw [authority]
    exact congrArg Observation.answer (run_eq_of_agrees first.2 second.2 _ reads)

/-- The entry has a real historical execution of its own program as origin. -/
def Recorded (family : Authority → Query → Program Key Value Answer)
    (entry : Entry Authority Query Key Value Answer) : Prop :=
  Supported.Recorded (programObserver family) entry

/-- Population executes the actual query once and retains its read certificate. -/
def populate (family : Authority → Query → Program Key Value Answer)
    (authority : Authority) (query : Query) (store : Key → Value) :
    Entry Authority Query Key Value Answer :=
  Supported.populate (programObserver family) (authority, store) query

theorem populate_recorded (family : Authority → Query → Program Key Value Answer)
    (authority : Authority) (query : Query) (store : Key → Value) :
    Recorded family (populate family authority query store) :=
  Supported.populate_recorded _ _ _

def admissible [DecidableEq Authority] [DecidableEq Query] [DecidableEq Value]
    (authority : Authority) (query : Query) (store : Key → Value)
    (entry : Entry Authority Query Key Value Answer) : Bool :=
  decide (entry.authority = authority ∧ entry.key = query) &&
    checkReads store entry.value.reads

theorem admissible_iff [DecidableEq Authority] [DecidableEq Query] [DecidableEq Value]
    (authority : Authority) (query : Query) (store : Key → Value)
    (entry : Entry Authority Query Key Value Answer) :
    admissible authority query store entry = true ↔
      entry.authority = authority ∧ entry.key = query ∧ Agrees store entry.value.reads := by
  simp [admissible, checkReads_iff, and_assoc]

/-- Program queries use the same validation and reuse algorithm. -/
def reuse [DecidableEq Authority] [DecidableEq Query] [DecidableEq Value]
    (family : Authority → Query → Program Key Value Answer)
    (authority : Authority) (query : Query) (store : Key → Value)
    (entry : Entry Authority Query Key Value Answer) : Answer × Nat :=
  Supported.reuse (programObserver family) (authority, store) query entry

/-- Reuse preserves the complete answer, including order, duplicate proof
occurrences and immutable evidence whenever those are in `Answer`. -/
theorem reuse_exact [DecidableEq Authority] [DecidableEq Query] [DecidableEq Value]
    (family : Authority → Query → Program Key Value Answer)
    (authority : Authority) (query : Query) (store : Key → Value)
    (entry : Entry Authority Query Key Value Answer) (recorded : Recorded family entry) :
    (reuse family authority query store entry).1 =
      (run store (family authority query)).answer :=
  Supported.reuse_exact (programObserver family) (authority, store) query entry recorded

/-- Fresh materialization is performed on the current invocation after reuse. -/
theorem materialized_exact [DecidableEq Authority] [DecidableEq Query] [DecidableEq Value]
    {Invocation : Type*} {Result : Type*}
    (family : Authority → Query → Program Key Value Answer)
    (authority : Authority) (query : Query) (store : Key → Value)
    (entry : Entry Authority Query Key Value Answer) (recorded : Recorded family entry)
    (materialize : Invocation → Answer → Result) (invocation : Invocation) :
    materialize invocation (reuse family authority query store entry).1 =
      materialize invocation (run store (family authority query)).answer :=
  Supported.materialized_exact (programObserver family) (authority, store) query
    entry recorded materialize invocation

theorem accepted_skips_query [DecidableEq Authority] [DecidableEq Query] [DecidableEq Value]
    (family : Authority → Query → Program Key Value Answer)
    (authority : Authority) (query : Query) (store : Key → Value)
    (entry : Entry Authority Query Key Value Answer)
    (accepted : admissible authority query store entry = true) :
    (reuse family authority query store entry).2 = 0 := by
  have valid : Supported.admissible (programObserver family) (authority, store)
      query entry = true := accepted
  unfold reuse Supported.reuse
  rw [if_pos valid]

theorem rejected_executes_query [DecidableEq Authority] [DecidableEq Query] [DecidableEq Value]
    (family : Authority → Query → Program Key Value Answer)
    (authority : Authority) (query : Query) (store : Key → Value)
    (entry : Entry Authority Query Key Value Answer)
    (rejected : admissible authority query store entry = false) :
    (reuse family authority query store entry).2 = 1 := by
  have invalid : Supported.admissible (programObserver family) (authority, store)
      query entry = false := rejected
  unfold reuse Supported.reuse
  simp only [invalid, Bool.false_eq_true, ↓reduceIte]

/-- An array trace that leaves all observed coordinates unchanged permits
reuse even when unrelated coordinates changed. -/
theorem reuse_after_trace [DecidableEq Authority] [DecidableEq Query]
    [DecidableEq Value] [DecidableEq Key]
    (family : Authority → Query → Program Key Value Answer)
    (authority : Authority) (query : Query) (initial : Key → Value)
    (writes : Nat → Option (Mettapedia.Logic.ArrayInvariants.UpdateTrace.Write Key Value))
    (start finish : Nat) (ordered : start ≤ finish)
    (untouched : ∀ read ∈ (run
      (Mettapedia.Logic.ArrayInvariants.UpdateTrace.trace initial writes start)
      (family authority query)).reads, ∀ i, start ≤ i → i < finish →
      ¬ Mettapedia.Logic.ArrayInvariants.UpdateTrace.Updates writes i read.1) :
    let entry := populate family authority query
      (Mettapedia.Logic.ArrayInvariants.UpdateTrace.trace initial writes start)
    (reuse family authority query
      (Mettapedia.Logic.ArrayInvariants.UpdateTrace.trace initial writes finish) entry).2 = 0 := by
  apply accepted_skips_query
  apply (admissible_iff _ _ _ _).mpr
  refine ⟨rfl, rfl, ?_⟩
  exact trace_preserves_reads initial writes start finish _
    (run_agrees _ _) ordered untouched

namespace Controls

inductive Cell where
  | alias (next : Nat)
  | value (payload : Nat)
  deriving DecidableEq, Repr

/-- A bounded alias follower records every lookup, including an unbound
terminal. Exhaustion remains distinguishable from an unbound terminal. -/
def follow : Nat → Nat → Program Nat (Option Cell) (Option (Sum Nat Nat))
  | 0, _ => .pure none
  | fuel + 1, root => .read root fun cell =>
      match cell with
      | none => .pure (some (.inl root))
      | some (.value payload) => .pure (some (.inr payload))
      | some (.alias next) => follow fuel next

def family (_authority : Nat) (root : Nat) := follow 4 root

def openBranch : Nat → Option Cell
  | 0 => some (.alias 1)
  | _ => none

def firstBranch : Nat → Option Cell := Function.update openBranch 1 (some (.value 7))
def secondBranch : Nat → Option Cell := Function.update openBranch 1 (some (.value 17))

theorem open_terminal_recorded :
    (run openBranch (family 1 0)).reads = [(0, some (.alias 1)), (1, none)] := rfl

/-- Appending a binding to the formerly unbound terminal invalidates its
cached absence, then recomputes the grounded result. -/
theorem appended_binding_changes_open_terminal :
    reuse family 1 0 firstBranch (populate family 1 0 openBranch) =
      (some (.inr 7), 1) := by decide

/-- The root row survives rollback, but its result changes when the alias
target is rebound in the next branch. -/
theorem rollback_rebind_cannot_reuse_closed_result :
    firstBranch 0 = secondBranch 0 ∧
      reuse family 1 0 secondBranch (populate family 1 0 firstBranch) =
        (some (.inr 17), 1) := by decide

theorem unrelated_binding_keeps_result :
    reuse family 1 0 (Function.update firstBranch 8 (some (.value 99)))
      (populate family 1 0 firstBranch) = (some (.inr 7), 0) := by decide

/-- Equal payloads in different owners cannot authorize a cross-owner hit. -/
theorem different_owner_recomputes :
    reuse family 2 0 firstBranch (populate family 1 0 firstBranch) =
      (some (.inr 7), 1) := by decide

theorem different_query_recomputes :
    reuse family 1 1 firstBranch (populate family 1 0 firstBranch) =
      (some (.inr 7), 1) := by decide

theorem unchanged_branch_reuses :
    reuse family 1 0 firstBranch (populate family 1 0 firstBranch) =
      (some (.inr 7), 0) := by decide

/-- A no-read program still has a specific, governing meaning. -/
def constantFamily (answer : Nat) (_authority _query : Nat) : Program Nat Nat Nat :=
  .pure answer

def forgedEntry : Entry Nat Nat Nat Nat Nat := ⟨1, 0, ⟨99, []⟩⟩

/-- Validation alone does not supply historical provenance. -/
theorem empty_forged_certificate_is_not_sufficient :
    admissible 1 0 (fun _ => 0) forgedEntry = true ∧
      reuse (constantFamily 7) 1 0 (fun _ => 0) forgedEntry = (99, 0) ∧
      ¬ Recorded (constantFamily 7) forgedEntry := by
  refine ⟨by decide, by decide, ?_⟩
  rintro ⟨old, _, history⟩
  have impossible : (99 : Nat) = 7 := congrArg Observation.answer history
  omega

/-- Keeping the same authority/key for a changed program cannot license
reuse: the stored entry lacks an execution of the new program as origin. -/
theorem changed_program_requires_new_authority :
    let old := populate (constantFamily 7) 1 0 (fun _ => 0)
    admissible 1 0 (fun _ => 0) old = true ∧
      reuse (constantFamily 9) 1 0 (fun _ => 0) old = (7, 0) ∧
      ¬ Recorded (constantFamily 9) old := by
  refine ⟨by decide, by decide, ?_⟩
  rintro ⟨old, _, history⟩
  have impossible : (7 : Nat) = 9 := congrArg Observation.answer history
  omega

end Controls

end Mettapedia.Machines.ReadCertifiedQueryReuse
