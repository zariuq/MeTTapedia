import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.LaneSpecialization

/-!
# Admitting a per-region fast path behind the one transform

A region may run an operation by a specialized path instead of the generic transform instance,
when the region's kind makes that safe. This module states what such a path must prove to be
admitted, and works one example: `add-atom` into a set-kind region.

## Region kinds and operations

A **region kind** (`RegionKind`) says how the atoms an operation makes merge into the region's
bag (`merge`: plain addition for a bag, insertion without duplicates for a set) and which stores
the kind keeps (`Inv`). An operation is given by what it makes, computed at a snapshot of the
region (`Delta`). Run alone it is `step`. Two operations computed at one snapshot and both
committed without validation are `par`: the effect of concurrency without coordination.

## The obligation

A fast path for an operation is **admitted** (`Admitted`) when, on every store of the kind, it
reaches what the generic instance reaches, and it keeps the kind's stores. Then any sequence of
operations, each run by an admitted fast path, ends where the generic instances end
(`run_admitted`): the lane observes the same in every sequential context, the statement form of
`Equivalence.LaneSpecialization` with the context a program (`admitted_specializes`).

A fast path is **admitted for unvalidated concurrency** with another (`ParallelSafe`) when committing
both from one snapshot reaches what running them in order reaches. A path whose effect does not
depend on its snapshot (it reads nothing: a monotone commit) is parallel-safe with every other such
path, whatever the kind (`parallelSafe_of_snapshotFree`). This is where a region kind earns a fast
path: it can make an operation read nothing.

## The worked example: `add-atom` into a set

For a set kept by the program, the generic add must first check that the atom is absent: a guard
that queries the region (`guardedAdd`). Under a set kind the merge itself is idempotent, so
the fast path makes the atom unconditionally (`setKind`, `setAdd`):

* it is admitted (`setAdd_admitted`): on duplicate-free stores it reaches the guarded add, and it
  keeps stores duplicate-free;
* it is parallel-safe with every set add (`setAdd_parallelSafe`), so two adds need no validation,
  no epoch and no claim;
* the guarded add over a bag is not (`Controls.guarded_parallel_duplicates`): two guarded adds of
  one atom, from one snapshot without it, both pass the guard and store it twice, which breaks the
  set the program meant to keep; validating the guard (serializable mode) is what prevents it;
* the same fast path is refused for a bag kind (`Controls.bag_kind_refuses`): there `add-atom`
  adds a copy, and inserting without duplicates disagrees as soon as the atom is present.

The fast path is not an encoding of the guarded commit in the sense of the basis module
(`Basis.Encodes`): it is independent of commits the guarded add conflicts with. It is admitted for
the kind's observation, not for the identity of commits.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.LaneSpecializations

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.Lanes

universe u

variable {T : Type u}

/-- A region kind: how made atoms merge into the region, and the stores the kind keeps. -/
structure RegionKind (T : Type u) where
  merge : Multiset T → Multiset T → Multiset T
  Inv : Multiset T → Prop

/-- An operation, by what it makes, computed at a snapshot of the region. -/
abbrev Delta (T : Type u) := Multiset T → Multiset T

namespace RegionKind

variable (k : RegionKind T)

/-- Run an operation alone. -/
def step (δ : Delta T) (M : Multiset T) : Multiset T := k.merge M (δ M)

/-- Two operations computed at one snapshot, both committed without validation. -/
def par (δ δ' : Delta T) (M : Multiset T) : Multiset T := k.merge (k.merge M (δ M)) (δ' M)

/-- Run a sequence of operations. -/
def run : List (Delta T) → Multiset T → Multiset T
  | [], M => M
  | δ :: rest, M => run rest (k.step δ M)

end RegionKind

/-- **A fast path is admitted** for an operation of a kind when, on the kind's stores, it reaches
the generic instance's store and keeps the kind's stores. -/
structure Admitted (k : RegionKind T) (generic : Multiset T → Multiset T) (fast : Delta T) : Prop where
  agrees : ∀ M, k.Inv M → k.step fast M = generic M
  preserves : ∀ M, k.Inv M → k.Inv (k.step fast M)

/-- Run a sequence of generic instances. -/
def runGeneric : List (Multiset T → Multiset T) → Multiset T → Multiset T
  | [], M => M
  | g :: rest, M => runGeneric rest (g M)

/-- **Admitted fast paths run every program as the generic instances do**, from every store the
kind keeps. -/
theorem run_admitted (k : RegionKind T) :
    ∀ (ops : List ((Multiset T → Multiset T) × Delta T)),
      (∀ op ∈ ops, Admitted k op.1 op.2) → ∀ M, k.Inv M →
        k.run (ops.map Prod.snd) M = runGeneric (ops.map Prod.fst) M := by
  intro ops
  induction ops with
  | nil => intro _ M _; rfl
  | cons op rest ih =>
      intro admitted M inv
      have here := admitted op (List.mem_cons_self ..)
      simp only [List.map_cons, RegionKind.run, runGeneric]
      rw [← here.agrees M inv]
      exact ih (fun o member => admitted o (List.mem_cons_of_mem _ member)) _ (here.preserves M inv)

/-- **The statement form**: under the lane that observes the final store, a program of admitted
fast paths specializes the program of generic instances, in every context the kind keeps. -/
theorem admitted_specializes (k : RegionKind T) (ops : List ((Multiset T → Multiset T) × Delta T))
    (admitted : ∀ op ∈ ops, Admitted k op.1 op.2) :
    (bagLane {M : Multiset T // k.Inv M} T).Specializes (fun M => k.run (ops.map Prod.snd) M.1)
      (fun M => runGeneric (ops.map Prod.fst) M.1) :=
  fun M => run_admitted k ops admitted M.1 M.2

/-- **Parallel-safe**: committing both from one snapshot reaches what running them in order does. -/
def ParallelSafe (k : RegionKind T) (δ δ' : Delta T) : Prop :=
  ∀ M, k.Inv M → k.par δ δ' M = k.step δ' (k.step δ M)

/-- An operation that does not depend on its snapshot: it reads nothing. -/
def SnapshotFree (δ : Delta T) : Prop := ∀ M N, δ M = δ N

/-- **Operations that read nothing are parallel-safe, for every kind.** -/
theorem parallelSafe_of_snapshotFree (k : RegionKind T) {δ δ' : Delta T} (free' : SnapshotFree δ') :
    ParallelSafe k δ δ' := fun M _ => by
  unfold RegionKind.par RegionKind.step
  rw [free' M (k.merge M (δ M))]

/-! ## The worked example: `add-atom` into a set -/

section SetKind

variable [DecidableEq T]

/-- **The set kind**: made atoms are inserted without duplicates; stores are duplicate-free. -/
def setKind : RegionKind T := ⟨fun M made => made.ndunion M, Multiset.Nodup⟩

/-- **The bag kind**: made atoms are added; every store is kept. -/
def bagKind : RegionKind T := ⟨fun M made => M + made, fun _ => True⟩

/-- The generic add into a set kept by the program: make the atom when it is absent. -/
def guardedAdd (a : T) (M : Multiset T) : Multiset T := if a ∈ M then M else a ::ₘ M

/-- The guard as an operation: what it makes depends on the snapshot. -/
def guardedDelta (a : T) : Delta T := fun M => if a ∈ M then 0 else {a}

/-- **The fast path**: make the atom, unconditionally. -/
def setAdd (a : T) : Delta T := fun _ => {a}

theorem setKind_step_setAdd (a : T) (M : Multiset T) : setKind.step (setAdd a) M = M.ndinsert a := by
  show ({a} : Multiset T).ndunion M = M.ndinsert a
  rw [← Multiset.cons_zero, Multiset.cons_ndunion, Multiset.zero_ndunion]

/-- **The set fast path is admitted.** -/
theorem setAdd_admitted (a : T) : Admitted setKind (guardedAdd a) (setAdd a) where
  agrees M _ := by
    rw [setKind_step_setAdd]
    unfold guardedAdd
    split_ifs with present
    · exact Multiset.ndinsert_of_mem present
    · exact Multiset.ndinsert_of_notMem present
  preserves M inv := by
    rw [setKind_step_setAdd]
    exact Multiset.Nodup.ndinsert a inv

/-- **Set adds need no validation**: any two are parallel-safe. -/
theorem setAdd_parallelSafe (a b : T) : ParallelSafe setKind (setAdd a) (setAdd b) :=
  parallelSafe_of_snapshotFree setKind fun _ _ => rfl

/-- The guarded add as an operation over a bag reaches the guarded add. -/
theorem bagKind_step_guarded (a : T) (M : Multiset T) :
    bagKind.step (guardedDelta a) M = guardedAdd a M := by
  show M + guardedDelta a M = guardedAdd a M
  unfold guardedDelta guardedAdd
  split_ifs
  · simp
  · rw [add_comm]; rfl

end SetKind

/-! ## Controls -/

namespace Controls

/-- **Two guarded adds from one snapshot store the atom twice**: both see it absent. Run in order,
the second sees it and adds nothing. The result is not a set. -/
theorem guarded_parallel_duplicates :
    bagKind.par (guardedDelta 1) (guardedDelta 1) (0 : Multiset ℕ) = {1, 1} ∧
      bagKind.step (guardedDelta 1) (bagKind.step (guardedDelta 1) (0 : Multiset ℕ)) = {1} ∧
      ¬ ({1, 1} : Multiset ℕ).Nodup ∧ ¬ ParallelSafe bagKind (guardedDelta 1) (guardedDelta (1 : ℕ)) := by
  refine ⟨by decide, by decide, by decide, fun safe => ?_⟩
  have := safe 0 trivial
  revert this
  decide

/-- **The set fast path is refused for a bag kind**: there `add-atom` adds a copy. -/
theorem bag_kind_refuses :
    ¬ Admitted bagKind (fun M => M + {(1 : ℕ)}) (fun M => if 1 ∈ M then 0 else {1}) := by
  intro admitted
  have := admitted.agrees {1} trivial
  revert this
  decide

/-- The set fast path on a concrete store. -/
theorem setAdd_instance :
    setKind.step (setAdd 1) ({1, 2} : Multiset ℕ) = {1, 2} ∧
      setKind.step (setAdd 3) ({1, 2} : Multiset ℕ) = {3, 1, 2} := by
  decide

/-- **Admitted, positive**: the set fast path for `add-atom 1` is admitted for the set kind.
(`bag_kind_refuses` is the negative control.) -/
theorem setAdd_one_admitted : Admitted setKind (guardedAdd (1 : ℕ)) (setAdd 1) := setAdd_admitted 1

/-- **Parallel-safe, positive**: two set adds from one snapshot reach what running them in order
does. (`guarded_parallel_duplicates` contains the negative control.) -/
theorem setAdd_parallel_instance : ParallelSafe setKind (setAdd (1 : ℕ)) (setAdd 2) :=
  setAdd_parallelSafe 1 2

/-- **Snapshot-free, positive and negative**: the set add makes `{1}` whatever it read; the guarded
add makes `{1}` at the empty snapshot and nothing at `{1}`. -/
theorem setAdd_snapshotFree :
    SnapshotFree (setAdd (1 : ℕ)) ∧ ¬ SnapshotFree (guardedDelta (1 : ℕ)) := by
  refine ⟨fun _ _ => rfl, fun free => ?_⟩
  have := free 0 {1}
  revert this
  decide

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.LaneSpecializations
