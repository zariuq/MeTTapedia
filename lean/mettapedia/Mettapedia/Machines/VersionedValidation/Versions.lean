import Mettapedia.Machines.VersionedValidation.Clock
import Mettapedia.Machines.RevisionDependencySet

/-!
# Version-guarded reuse of retained decisions

A retained decision is the complete observation of a pure adaptive query
(`ReadOnlyQuery.Program`): its answer and every read it made, absent lookups
included. It is valid at a store exactly when those reads agree with the store
(`ReadOnlyQuery.run_eq_of_agrees`). Checking every read is the slow path.
Version counters replace it by a check of counters.

A *history* is a finite word of stores, one at each cut of `Cut steps`, as in
`ReadWindowCuts`. A *class map* sends every key to a class. It is a function,
hence total: a key that is absent, never read or never written still has a class,
and a change to it moves its class counter. A *versioning* assigns a counter to
every class at every cut. It is the discipline of `ReadWindowCuts` for the
single-region footprint `classFootprint cls` (`IsVersioning`): counters never
decrease, and a change of a key strictly increases the counter of its class at
that step (`IsVersioning.covering`, `IsVersioning.of_laws`). A footprint of
several regions is the general case (`Controls.two_region_footprint`). A *stamp*
taken at cut `t0` records the counter of each class read, at `t0`.

* `IsVersioning.not_classChangedAt`: equal counters at `t0` and `t` mean that no
  key of that class changed at any step in between. The endpoint form is
  `Discipline.same_of_stamps`, from which `agrees_of_stampAgrees` follows.
* `reuse_sound`: an agreeing stamp licenses reuse of the whole observation.
* `use_record`, `use_recomputed_iff`, `serve_record`: the validating strategy
  (stamp check, then read check, then recomputation) returns the fresh
  observation at every use and recomputes exactly when the reads disagree. The
  class map and the versioning decide only how often the read check runs
  (`serve_granularity_invariant`).
* `countingVersion`: the canonical versioning, counting the steps at which some
  key of a class changed. It is a versioning and it is exact: its counters move
  only at such steps.

## Bridge to revision environments

The counters at a cut form a `RevisionEnvironment K ℕ` (`environment`), and a
stamp is a `RevisionDependencySet K ℕ` over classes (`stampDependencies`), each
entry being the occurrence at logical position zero of its class counter, as for
a captured binding. Stamp agreement is `ValidAt` of that dependency set
(`stampAgrees_iff_validAt`), and for a taken stamp it is `AgreesOn` of the class
support (`stampAgrees_takeStamp_iff_agreesOn`). The locality theorems of
`RevisionDependencySet` then apply unchanged (`stampAgrees_iff_of_agreesOn`,
`stampAgrees_bump_outside_iff`, `not_stampAgrees_bump_inside`). Those definitions
live in `Type`, so the bridge takes classes in `Type`.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.VersionedValidation

open ReadOnlyQuery
open Mettapedia.GSLT.Contracts.ReadWindowCuts (Cut Discipline)

universe u v w x

/-- A history of `steps` steps: the store at each cut. -/
abbrev History (steps : ℕ) (Key : Type u) (Value : Type v) := Cut steps → Key → Value

/-! ## Versionings -/

section Versionings

variable {steps : ℕ} {Key : Type u} {Value : Type v} {K : Type w}

/-- The single-region footprint of a class map: each key is guarded by its class. -/
def classFootprint (cls : Key → K) (n : Key) : Set K :=
  {cls n}

theorem mem_classFootprint {cls : Key → K} {n : Key} {k : K} :
    k ∈ classFootprint cls n ↔ k = cls n :=
  Iff.rfl

/-- A versioning `ver` of the history `store` under the total class map `cls`: the
discipline of `ReadWindowCuts` for the class footprint. -/
abbrev IsVersioning (store : History steps Key Value) (cls : Key → K)
    (ver : Cut steps → K → ℕ) : Prop :=
  Discipline store (classFootprint cls) ver

/-- Some key of class `k` changes at step `i`. -/
def ClassChangedAt (store : History steps Key Value) (cls : Key → K) (k : K) (i : Fin steps) :
    Prop :=
  ∃ n, cls n = k ∧ store i.succ n ≠ store i.castSucc n

instance ClassChangedAt.decidablePred [Fintype Key] [DecidableEq K] [DecidableEq Value]
    (store : History steps Key Value) (cls : Key → K) (k : K) :
    DecidablePred (ClassChangedAt store cls k) := fun i =>
  inferInstanceAs (Decidable (∃ n, cls n = k ∧ store i.succ n ≠ store i.castSucc n))

/-- A versioning is exact when a counter moves only at a step where some key of
its class changed. Exactness is the converse of covering, at the class level. -/
def IsExact (store : History steps Key Value) (cls : Key → K) (ver : Cut steps → K → ℕ) :
    Prop :=
  ∀ (i : Fin steps) k, ver i.castSucc k ≠ ver i.succ k → ClassChangedAt store cls k i

variable {store : History steps Key Value} {cls : Key → K} {ver : Cut steps → K → ℕ}

/-- A change of a key strictly increases the counter of its class at that step. -/
theorem IsVersioning.covering (versioning : IsVersioning store cls ver) (i : Fin steps)
    (n : Key) (changed : store i.succ n ≠ store i.castSucc n) :
    ver i.castSucc (cls n) < ver i.succ (cls n) := by
  rcases Nat.lt_or_eq_of_le (versioning.advance i (cls n)) with lt | eq
  · exact lt
  · exact absurd (versioning.frame i n fun region member => by
      rw [mem_classFootprint.mp member]
      exact eq).symm changed

/-- Monotone counters that move at every change of a key of their class are a
versioning. -/
theorem IsVersioning.of_laws (advance : ∀ (i : Fin steps) k, ver i.castSucc k ≤ ver i.succ k)
    (covering : ∀ (i : Fin steps) n, store i.succ n ≠ store i.castSucc n →
      ver i.castSucc (cls n) < ver i.succ (cls n)) :
    IsVersioning store cls ver :=
  ⟨advance, fun i n same => by
    by_contra differs
    have bumped := covering i n (Ne.symm differs)
    have equal := same (show cls n ∈ classFootprint cls n from rfl)
    omega⟩

/-- If the counter of a class is equal at `t0` and `t`, no key of that class
changed at any step in between. -/
theorem IsVersioning.not_classChangedAt (versioning : IsVersioning store cls ver)
    {t0 t : Cut steps} {k : K} (same : ver t0 k = ver t k) {i : Fin steps}
    (lo : t0 ≤ i.castSucc) (hi : i.succ ≤ t) : ¬ ClassChangedAt store cls k i := by
  rintro ⟨n, rfl, changed⟩
  have first := versioning.stamp_mono (cls n) lo
  have last := versioning.stamp_mono (cls n) hi
  have bumped := versioning.covering i n changed
  simp only at first last
  omega

/-- An exact counter does not move across a window in which no key of its class
changed. -/
theorem IsExact.version_eq (exact : IsExact store cls ver) {t0 t : Cut steps} (le : t0 ≤ t)
    {k : K} (quiet : ∀ i : Fin steps, t0 ≤ i.castSucc → i.succ ≤ t →
      ¬ ClassChangedAt store cls k i) :
    ver t k = ver t0 k :=
  eq_of_steps (f := fun cut => ver cut k) le fun i lo hi => by
    by_contra moved
    exact quiet i lo hi (exact i k moved)

/-- The canonical counting versioning: the counter of class `k` at cut `t` is the
number of steps before `t` at which some key of class `k` changed. It is
computable whenever those changes are decidable, e.g. for finitely many keys. -/
def countingVersion (store : History steps Key Value) (cls : Key → K)
    [∀ k, DecidablePred (ClassChangedAt store cls k)] (t : Cut steps) (k : K) : ℕ :=
  Nat.count (fun s => ∃ h : s < steps, ClassChangedAt store cls k ⟨s, h⟩) t

section Counting

variable [∀ k, DecidablePred (ClassChangedAt store cls k)]

theorem countingVersion_zero (k : K) : countingVersion store cls 0 k = 0 :=
  Nat.count_zero _

theorem countingVersion_succ (i : Fin steps) (k : K) :
    countingVersion store cls i.succ k =
      countingVersion store cls i.castSucc k + if ClassChangedAt store cls k i then 1 else 0 := by
  unfold countingVersion
  rw [Fin.val_succ, Fin.val_castSucc, Nat.count_succ]
  have here : (∃ h : (i : ℕ) < steps, ClassChangedAt store cls k ⟨i, h⟩) ↔
      ClassChangedAt store cls k i :=
    ⟨fun ⟨_, changed⟩ => changed, fun changed => ⟨i.isLt, changed⟩⟩
  by_cases changed : ClassChangedAt store cls k i
  · rw [if_pos (here.mpr changed), if_pos changed]
  · rw [if_neg (fun found => changed (here.mp found)), if_neg changed]

theorem countingVersion_isVersioning : IsVersioning store cls (countingVersion store cls) :=
  IsVersioning.of_laws
    (fun i k => by
      rw [countingVersion_succ]
      exact Nat.le_add_right _ _)
    (fun i n changed => by
      rw [countingVersion_succ, if_pos ⟨n, rfl, changed⟩]
      exact Nat.lt_succ_self _)

theorem countingVersion_isExact : IsExact store cls (countingVersion store cls) := by
  intro i k moved
  by_contra quiet
  rw [countingVersion_succ, if_neg quiet, Nat.add_zero] at moved
  exact moved rfl

/-- A counting counter is unchanged across a window exactly when no key of its
class changed in that window. -/
theorem countingVersion_eq_iff {t0 t : Cut steps} (le : t0 ≤ t) {k : K} :
    countingVersion store cls t0 k = countingVersion store cls t k ↔
      ∀ i : Fin steps, t0 ≤ i.castSucc → i.succ ≤ t → ¬ ClassChangedAt store cls k i :=
  ⟨fun same _ lo hi => countingVersion_isVersioning.not_classChangedAt same lo hi,
    fun quiet => (countingVersion_isExact.version_eq le quiet).symm⟩

end Counting

end Versionings

/-! ## Stamps -/

/-- A stamp: classes together with the counters they had when it was taken. -/
abbrev Stamp (K : Type w) := List (K × ℕ)

section Stamps

variable {steps : ℕ} {Key : Type u} {Value : Type v} {K : Type w}

/-- Every recorded counter still has its recorded value at cut `t`. -/
def StampAgrees (ver : Cut steps → K → ℕ) (t : Cut steps) (stamp : Stamp K) : Prop :=
  ∀ entry ∈ stamp, ver t entry.1 = entry.2

/-- The executable stamp check: one comparison per entry. -/
def checkStamp (ver : Cut steps → K → ℕ) (t : Cut steps) (stamp : Stamp K) : Bool :=
  stamp.all fun entry => decide (ver t entry.1 = entry.2)

theorem checkStamp_iff (ver : Cut steps → K → ℕ) (t : Cut steps) (stamp : Stamp K) :
    checkStamp ver t stamp = true ↔ StampAgrees ver t stamp := by
  simp [checkStamp, StampAgrees]

instance StampAgrees.decidable (ver : Cut steps → K → ℕ) (t : Cut steps) (stamp : Stamp K) :
    Decidable (StampAgrees ver t stamp) :=
  decidable_of_iff _ (checkStamp_iff ver t stamp)

theorem stampAgrees_map_iff {ver : Cut steps → K → ℕ} {t0 t : Cut steps}
    {subscribed : List K} :
    StampAgrees ver t (subscribed.map fun k => (k, ver t0 k)) ↔
      ∀ k ∈ subscribed, ver t k = ver t0 k := by
  simp [StampAgrees]

variable [DecidableEq K]

/-- The distinct classes of the keys read, in first-read order. -/
def classes (cls : Key → K) (reads : Reads Key Value) : List K :=
  (reads.map fun read => cls read.1).dedup

theorem mem_classes {cls : Key → K} {reads : Reads Key Value} {k : K} :
    k ∈ classes cls reads ↔ ∃ read ∈ reads, cls read.1 = k := by
  simp [classes]

theorem classes_nodup (cls : Key → K) (reads : Reads Key Value) :
    (classes cls reads).Nodup :=
  List.nodup_dedup _

theorem classes_eq_keys (cls : Key → K) (reads : Reads Key Value) :
    classes cls reads = ((reads.map Prod.fst).map cls).dedup := by
  unfold classes
  rw [List.map_map]
  rfl

/-- The stamp taken at cut `t0` for a read list: the counter at `t0` of the class
of every read key, absent lookups included, one entry per distinct class. -/
def takeStamp (cls : Key → K) (ver : Cut steps → K → ℕ) (t0 : Cut steps)
    (reads : Reads Key Value) : Stamp K :=
  (classes cls reads).map fun k => (k, ver t0 k)

theorem takeStamp_length (cls : Key → K) (ver : Cut steps → K → ℕ) (t0 : Cut steps)
    (reads : Reads Key Value) :
    (takeStamp cls ver t0 reads).length = (classes cls reads).length :=
  List.length_map _

theorem stampAgrees_takeStamp_iff {cls : Key → K} {ver : Cut steps → K → ℕ}
    {t0 t : Cut steps}
    {reads : Reads Key Value} :
    StampAgrees ver t (takeStamp cls ver t0 reads) ↔
      ∀ read ∈ reads, ver t (cls read.1) = ver t0 (cls read.1) := by
  rw [takeStamp, stampAgrees_map_iff]
  constructor
  · intro agrees read member
    exact agrees (cls read.1) (mem_classes.mpr ⟨read, member, rfl⟩)
  · intro agrees k member
    obtain ⟨read, readMember, rfl⟩ := mem_classes.mp member
    exact agrees read readMember

/-- A stamp agreeing at `t` is the stamp that would be taken at `t`. -/
theorem takeStamp_eq_of_stampAgrees {cls : Key → K} {ver : Cut steps → K → ℕ}
    {t0 t : Cut steps} {reads : Reads Key Value}
    (agrees : StampAgrees ver t (takeStamp cls ver t0 reads)) :
    takeStamp cls ver t reads = takeStamp cls ver t0 reads := by
  unfold takeStamp
  apply List.map_congr_left
  intro k member
  have same := agrees (k, ver t0 k) (List.mem_map_of_mem member)
  simp only at same
  rw [same]

/-! ## Soundness -/

variable {store : History steps Key Value} {cls : Key → K} {ver : Cut steps → K → ℕ}

/-- Reads taken from `store t0` still agree at `t ≥ t0` when their stamp agrees,
from `Discipline.same_of_stamps`. -/
theorem agrees_of_stampAgrees (versioning : IsVersioning store cls ver) {t0 t : Cut steps}
    (le : t0 ≤ t) {reads : Reads Key Value} (taken : Agrees (store t0) reads)
    (agrees : StampAgrees ver t (takeStamp cls ver t0 reads)) : Agrees (store t) reads := by
  intro read member
  have same := stampAgrees_takeStamp_iff.mp agrees read member
  have unchanged := versioning.same_of_stamps read.1 le fun region inside => by
    rw [mem_classFootprint.mp inside]
    exact same.symm
  exact unchanged.symm.trans (taken read member)

/-- **Soundness of version-guarded reuse.** If the stamp of a run at `t0` agrees
at `t ≥ t0`, the fresh run at `t` is that run: same answer, same reads. -/
theorem reuse_sound {Answer : Type x} (versioning : IsVersioning store cls ver)
    {t0 t : Cut steps} (le : t0 ≤ t) (program : Program Key Value Answer)
    (agrees : StampAgrees ver t (takeStamp cls ver t0 (run (store t0) program).reads)) :
    run (store t) program = run (store t0) program :=
  run_eq_of_agrees _ _ program
    (agrees_of_stampAgrees versioning le (run_agrees _ program) agrees)

/-- A stamp disagrees although the reads still agree: the slow check runs and
finds nothing changed. -/
def FalseAlarm (store : History steps Key Value) (ver : Cut steps → K → ℕ) (t : Cut steps)
    (stamp : Stamp K) (reads : Reads Key Value) : Prop :=
  ¬ StampAgrees ver t stamp ∧ Agrees (store t) reads

end Stamps

/-! ## The validating strategy -/

/-- A retained decision: a complete observation and the stamp that guards it. -/
structure Decision (K : Type w) (Key : Type u) (Value : Type v) (Answer : Type x) where
  observation : Observation Key Value Answer
  stamp : Stamp K

/-- What a use did: reused on an agreeing stamp, restamped after the reads were
checked and still agreed, or recomputed. -/
inductive Outcome where
  | reused
  | restamped
  | recomputed
  deriving DecidableEq, Repr

section Strategy

variable {steps : ℕ} {Key : Type u} {Value : Type v} {K : Type w} {Answer : Type x}
variable [DecidableEq K] [DecidableEq Value]

/-- The fresh decision at cut `t`: run, then stamp its reads at `t`. -/
def record (cls : Key → K) (ver : Cut steps → K → ℕ) (store : History steps Key Value)
    (program : Program Key Value Answer) (t : Cut steps) : Decision K Key Value Answer :=
  ⟨run (store t) program, takeStamp cls ver t (run (store t) program).reads⟩

/-- One use at cut `t`: reuse when the stamp agrees; otherwise check the reads,
and reuse and restamp when they agree; otherwise recompute. -/
def use (cls : Key → K) (ver : Cut steps → K → ℕ) (store : History steps Key Value)
    (program : Program Key Value Answer) (t : Cut steps)
    (decision : Decision K Key Value Answer) : Decision K Key Value Answer × Outcome :=
  if checkStamp ver t decision.stamp then (decision, .reused)
  else if checkReads (store t) decision.observation.reads then
    (⟨decision.observation, takeStamp cls ver t decision.observation.reads⟩, .restamped)
  else (record cls ver store program t, .recomputed)

variable {store : History steps Key Value} {cls : Key → K} {ver : Cut steps → K → ℕ}

/-- **The strategy is the fresh decision.** A decision recorded at `t0` and used at
`t ≥ t0` becomes exactly the decision recorded at `t`, whichever branch runs. -/
theorem use_record (versioning : IsVersioning store cls ver)
    (program : Program Key Value Answer) {t0 t : Cut steps} (le : t0 ≤ t) :
    (use cls ver store program t (record cls ver store program t0)).1 =
      record cls ver store program t := by
  unfold use
  split_ifs with stampOk readsOk
  · have agrees := (checkStamp_iff _ _ _).mp stampOk
    have same := reuse_sound versioning le program agrees
    simp only [record] at agrees ⊢
    rw [same, takeStamp_eq_of_stampAgrees agrees]
  · have same := run_eq_of_agrees _ _ program ((checkReads_iff _ _).mp readsOk)
    simp only [record]
    rw [same]
  · rfl

/-- Every use returns the fresh observation. -/
theorem use_fresh (versioning : IsVersioning store cls ver)
    (program : Program Key Value Answer) {t0 t : Cut steps} (le : t0 ≤ t) :
    (use cls ver store program t (record cls ver store program t0)).1.observation =
      run (store t) program := by
  rw [use_record versioning program le]
  rfl

/-- The strategy reuses without reading exactly when the stamp agrees. -/
theorem use_reused_iff (program : Program Key Value Answer) (t0 t : Cut steps) :
    (use cls ver store program t (record cls ver store program t0)).2 = .reused ↔
      StampAgrees ver t (takeStamp cls ver t0 (run (store t0) program).reads) := by
  rw [← checkStamp_iff]
  unfold use
  split_ifs with stampOk readsOk <;> simp_all [record]

/-- The strategy restamps exactly on a false alarm. -/
theorem use_restamped_iff (program : Program Key Value Answer) (t0 t : Cut steps) :
    (use cls ver store program t (record cls ver store program t0)).2 = .restamped ↔
      FalseAlarm store ver t (takeStamp cls ver t0 (run (store t0) program).reads)
        (run (store t0) program).reads := by
  unfold FalseAlarm
  rw [← checkStamp_iff, ← checkReads_iff]
  unfold use
  split_ifs with stampOk readsOk <;> simp_all [record]

/-- **Exactness.** The strategy recomputes exactly when the recorded reads
disagree with the current store. -/
theorem use_recomputed_iff (versioning : IsVersioning store cls ver)
    (program : Program Key Value Answer) {t0 t : Cut steps} (le : t0 ≤ t) :
    (use cls ver store program t (record cls ver store program t0)).2 = .recomputed ↔
      ¬ Agrees (store t) (run (store t0) program).reads := by
  constructor
  · intro recomputed agrees
    unfold use at recomputed
    split_ifs at recomputed with stampOk readsOk
    exact readsOk ((checkReads_iff _ _).mpr agrees)
  · intro disagrees
    have stampBad : checkStamp ver t (record cls ver store program t0).stamp = false := by
      apply Bool.eq_false_iff.mpr
      intro stampOk
      exact disagrees (agrees_of_stampAgrees versioning le (run_agrees _ program)
        ((checkStamp_iff _ _ _).mp stampOk))
    have readsBad :
        checkReads (store t) (record cls ver store program t0).observation.reads = false :=
      Bool.eq_false_iff.mpr fun readsOk => disagrees ((checkReads_iff _ _).mp readsOk)
    unfold use
    rw [stampBad, readsBad]
    rfl

/-- Serve a sequence of uses, threading the retained decision. -/
def serve (cls : Key → K) (ver : Cut steps → K → ℕ) (store : History steps Key Value)
    (program : Program Key Value Answer) :
    Decision K Key Value Answer → List (Cut steps) →
      List (Observation Key Value Answer × Outcome)
  | _, [] => []
  | decision, t :: times =>
      let next := use cls ver store program t decision
      (next.1.observation, next.2) :: serve cls ver store program next.1 times

/-- The recomputations forced by the store alone: at each use, whether the reads
of the fresh run at the previous use disagree with the current store. No class
map and no versioning occurs in it. -/
def recomputations (store : History steps Key Value) (program : Program Key Value Answer) :
    Cut steps → List (Cut steps) → List Bool
  | _, [] => []
  | t0, t :: times =>
      (!checkReads (store t) (run (store t0) program).reads) ::
        recomputations store program t times

/-- **Serving a sequence of uses.** At cuts `t0 ≤ t₁ ≤ t₂ ≤ …`, the strategy
returns the fresh observation at every use and recomputes exactly at the uses
listed by `recomputations`. -/
theorem serve_record (versioning : IsVersioning store cls ver)
    (program : Program Key Value Answer) {t0 : Cut steps} {times : List (Cut steps)}
    (sorted : List.IsChain (· ≤ ·) (t0 :: times)) :
    (serve cls ver store program (record cls ver store program t0) times).map Prod.fst =
        times.map (fun t => run (store t) program) ∧
      (serve cls ver store program (record cls ver store program t0) times).map
          (fun result => decide (result.2 = .recomputed)) =
        recomputations store program t0 times := by
  induction times generalizing t0 with
  | nil => exact ⟨rfl, rfl⟩
  | cons t times ih =>
      obtain ⟨le, rest⟩ := List.isChain_cons_cons.mp sorted
      obtain ⟨observations, flags⟩ := ih rest
      have next := use_record versioning program le
      have flag : decide ((use cls ver store program t
          (record cls ver store program t0)).2 = .recomputed) =
          !checkReads (store t) (run (store t0) program).reads := by
        by_cases agrees : checkReads (store t) (run (store t0) program).reads = true
        · rw [agrees]
          simp only [Bool.not_true, decide_eq_false_iff_not]
          rw [use_recomputed_iff versioning program le, not_not]
          exact (checkReads_iff _ _).mp agrees
        · rw [Bool.eq_false_iff.mpr agrees]
          simp only [Bool.not_false, decide_eq_true_eq]
          rw [use_recomputed_iff versioning program le]
          exact fun valid => agrees ((checkReads_iff _ _).mpr valid)
      simp only [serve, List.map_cons, next, observations, flags]
      refine ⟨?_, ?_⟩
      · rw [← use_fresh versioning program le, next]
      · rw [flag]
        rfl

/-- **Granularity decides only how often the read check runs.** Two strategies
with any class maps and any versionings give the same observations and
recompute at the same uses. -/
theorem serve_granularity_invariant {K' : Type*} [DecidableEq K']
    {cls' : Key → K'} {ver' : Cut steps → K' → ℕ}
    (versioning : IsVersioning store cls ver) (versioning' : IsVersioning store cls' ver')
    (program : Program Key Value Answer) {t0 : Cut steps} {times : List (Cut steps)}
    (sorted : List.IsChain (· ≤ ·) (t0 :: times)) :
    (serve cls ver store program (record cls ver store program t0) times).map Prod.fst =
        (serve cls' ver' store program (record cls' ver' store program t0) times).map
          Prod.fst ∧
      (serve cls ver store program (record cls ver store program t0) times).map
          (fun result => decide (result.2 = .recomputed)) =
        (serve cls' ver' store program (record cls' ver' store program t0) times).map
          (fun result => decide (result.2 = .recomputed)) := by
  obtain ⟨observations, flags⟩ := serve_record versioning program sorted
  obtain ⟨observations', flags'⟩ := serve_record versioning' program sorted
  exact ⟨observations.trans observations'.symm, flags.trans flags'.symm⟩

end Strategy

/-! ## Bridge to revision environments -/

section Bridge

variable {steps : ℕ} {Key : Type u} {Value : Type v} {K : Type} [DecidableEq K]

/-- The counters at cut `t`, as the current revision of every class. -/
def environment (ver : Cut steps → K → ℕ) (t : Cut steps) : RevisionEnvironment K ℕ :=
  ⟨ver t⟩

/-- The finite set of classes a read list depends on. -/
def classSupport (cls : Key → K) (reads : Reads Key Value) : Finset K :=
  (classes cls reads).toFinset

/-- A stamp as a dependency set: each entry names the counter of its class at the
recorded revision, at logical position zero. -/
def stampDependencies (stamp : Stamp K) : RevisionDependencySet K ℕ :=
  stamp.toFinset.image fun entry => ⟨⟨entry.1, entry.2⟩, 0⟩

theorem stampAgrees_iff_validAt (ver : Cut steps → K → ℕ) (t : Cut steps) (stamp : Stamp K) :
    StampAgrees ver t stamp ↔
      RevisionDependencySet.ValidAt (environment ver t) (stampDependencies stamp) := by
  constructor
  · intro agrees occurrence member
    obtain ⟨entry, entryMember, rfl⟩ := Finset.mem_image.mp member
    exact agrees entry (List.mem_toFinset.mp entryMember)
  · intro valid entry member
    exact valid ⟨⟨entry.1, entry.2⟩, 0⟩
      (Finset.mem_image.mpr ⟨entry, List.mem_toFinset.mpr member, rfl⟩)

theorem storeSupport_takeStamp (cls : Key → K) (ver : Cut steps → K → ℕ) (t0 : Cut steps)
    (reads : Reads Key Value) :
    (stampDependencies (takeStamp cls ver t0 reads)).storeSupport = classSupport cls reads := by
  ext k
  simp only [RevisionDependencySet.storeSupport, stampDependencies, takeStamp, classSupport,
    Finset.mem_image, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨_, ⟨_, ⟨k', member, rfl⟩, rfl⟩, rfl⟩
    exact member
  · intro member
    exact ⟨_, ⟨_, ⟨k, member, rfl⟩, rfl⟩, rfl⟩

/-- A taken stamp agrees at `t` exactly when the environments at `t` and at the
stamp cut agree on the class support. -/
theorem stampAgrees_takeStamp_iff_agreesOn {cls : Key → K} {ver : Cut steps → K → ℕ}
    {t0 t : Cut steps} {reads : Reads Key Value} :
    StampAgrees ver t (takeStamp cls ver t0 reads) ↔
      RevisionEnvironment.AgreesOn (classSupport cls reads) (environment ver t)
        (environment ver t0) := by
  rw [stampAgrees_takeStamp_iff]
  simp only [RevisionEnvironment.AgreesOn, classSupport, List.mem_toFinset, mem_classes,
    environment]
  constructor
  · rintro agrees k ⟨read, member, rfl⟩
    exact agrees read member
  · intro agrees read member
    exact agrees (cls read.1) ⟨read, member, rfl⟩

/-- Locality, from `validAt_iff_of_agreesOn_storeSupport`: agreement of a stamp
depends only on the counters of its class support. -/
theorem stampAgrees_iff_of_agreesOn {cls : Key → K} {ver : Cut steps → K → ℕ}
    {t0 t t' : Cut steps} {reads : Reads Key Value}
    (agree : RevisionEnvironment.AgreesOn (classSupport cls reads) (environment ver t)
      (environment ver t')) :
    StampAgrees ver t (takeStamp cls ver t0 reads) ↔
      StampAgrees ver t' (takeStamp cls ver t0 reads) := by
  rw [stampAgrees_iff_validAt, stampAgrees_iff_validAt]
  apply RevisionDependencySet.validAt_iff_of_agreesOn_storeSupport
  rw [storeSupport_takeStamp]
  exact agree

/-- A step that moves only the counter of class `k`. -/
theorem environment_succ_of_bump {ver : Cut steps → K → ℕ} {i : Fin steps} {k : K}
    {revision : ℕ} (step : ver i.succ = Function.update (ver i.castSucc) k revision) :
    environment ver i.succ = (environment ver i.castSucc).update k revision := by
  simp only [environment, RevisionEnvironment.update, step]

/-- Locality, from `validAt_update_iff_of_not_mem_storeSupport`: moving a counter
outside the class support leaves stamp agreement unchanged. -/
theorem stampAgrees_bump_outside_iff {cls : Key → K} {ver : Cut steps → K → ℕ}
    {t0 : Cut steps} {i : Fin steps} {reads : Reads Key Value} {k : K} {revision : ℕ}
    (step : ver i.succ = Function.update (ver i.castSucc) k revision)
    (outside : k ∉ classSupport cls reads) :
    StampAgrees ver i.succ (takeStamp cls ver t0 reads) ↔
      StampAgrees ver i.castSucc (takeStamp cls ver t0 reads) := by
  rw [stampAgrees_iff_validAt, stampAgrees_iff_validAt, environment_succ_of_bump step]
  apply RevisionDependencySet.validAt_update_iff_of_not_mem_storeSupport
  rw [storeSupport_takeStamp]
  exact outside

/-- Invalidation, from `not_validAt_update_of_mem`: moving a counter of the class
support to a revision other than the recorded one breaks the stamp. -/
theorem not_stampAgrees_bump_inside {cls : Key → K} {ver : Cut steps → K → ℕ}
    {t0 : Cut steps} {i : Fin steps} {reads : Reads Key Value} {k : K} {revision : ℕ}
    (step : ver i.succ = Function.update (ver i.castSucc) k revision)
    (inside : k ∈ classSupport cls reads) (moved : revision ≠ ver t0 k) :
    ¬ StampAgrees ver i.succ (takeStamp cls ver t0 reads) := by
  rw [stampAgrees_iff_validAt, environment_succ_of_bump step]
  apply RevisionDependencySet.not_validAt_update_of_mem (environment ver i.castSucc) _
    ⟨⟨k, ver t0 k⟩, 0⟩ _ revision moved
  exact Finset.mem_image.mpr ⟨(k, ver t0 k),
    List.mem_toFinset.mpr (List.mem_map_of_mem (List.mem_toFinset.mp inside)), rfl⟩

/-- For a versioning, a bump of a class read since the stamp breaks the stamp. -/
theorem not_stampAgrees_versioning_bump {store : History steps Key Value} {cls : Key → K}
    {ver : Cut steps → K → ℕ} (versioning : IsVersioning store cls ver) {t0 : Cut steps}
    {i : Fin steps} (le : t0 ≤ i.castSucc) {reads : Reads Key Value} {k : K}
    (step : ver i.succ = Function.update (ver i.castSucc) k (ver i.castSucc k + 1))
    (inside : k ∈ classSupport cls reads) :
    ¬ StampAgrees ver i.succ (takeStamp cls ver t0 reads) := by
  apply not_stampAgrees_bump_inside step inside
  have := versioning.stamp_mono k le
  simp only at this
  omega

end Bridge

end Mettapedia.Machines.VersionedValidation
