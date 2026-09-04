import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Infix
import Mettapedia.GSLT.Core.BranchCaptureAlgebra

/-!
# Capability-indexed binding-store representations

Logical substitution and physical branch storage are different interfaces.
This module states the common refinement laws without selecting a WAM trail,
a persistent map, a copied image, or a temporal prefix graph globally.

There are three results.

1. A `LinearRollbackStore` that implements the stated denotation laws may run
   any finite sequence of writes after a checkpoint and roll back exactly.
2. A current-store observation cannot reconstruct an arbitrary live sibling
   frontier.  Directly resumable siblings therefore require a forkable
   component.  A checkpoint plus an update path instead supports exact replay,
   with its recomputation cost kept explicit.
3. In the explicit prefix-edge cost model, a linear trail stores exactly the
   nonempty prefixes of its one live path.  It is storage-minimal among prefix
   graphs that retain that path; retaining a genuinely new sibling prefix is
   strictly more expensive.  This is a conditional optimality theorem, not a
   claim about cache behavior, constant factors, or every unification workload.

The prefix-graph model describes temporal branch sharing.  It has the same
prefix-sharing combinatorics as a trie, but it is not PathMap: PathMap indexes
term structure in a large space, whereas this graph indexes resumable execution
histories.  A runtime may profitably use both on these different axes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.BindingStoreCapabilityAlgebra

universe uLogical uPhysical uMark uUpdate uQuery uResult

/-! ## Denotational interfaces -/

/-- A physical binding representation with one authoritative logical
denotation.  `write_exact` prevents caches, slots, or trails from becoming a
second binding authority. -/
structure BindingStore
    (Logical : Type uLogical) (Physical : Type uPhysical)
    (Update : Type uUpdate) where
  denote : Physical → Logical
  logicalWrite : Logical → Update → Logical
  write : Physical → Update → Physical
  write_exact : ∀ physical update,
    denote (write physical update) = logicalWrite (denote physical) update

namespace BindingStore

variable {Logical : Type uLogical} {Physical : Type uPhysical}
  {Update : Type uUpdate}

/-- Apply a finite update path in the physical representation. -/
def writeMany (store : BindingStore Logical Physical Update) :
    Physical → List Update → Physical
  | physical, [] => physical
  | physical, update :: updates =>
      writeMany store (store.write physical update) updates

/-- Apply the same path in the authoritative logical semantics. -/
def logicalWriteMany (store : BindingStore Logical Physical Update) :
    Logical → List Update → Logical
  | logical, [] => logical
  | logical, update :: updates =>
      logicalWriteMany store (store.logicalWrite logical update) updates

/-- Every finite physical update path refines the corresponding logical path. -/
theorem writeMany_exact (store : BindingStore Logical Physical Update)
    (physical : Physical) (updates : List Update) :
    store.denote (store.writeMany physical updates) =
      store.logicalWriteMany (store.denote physical) updates := by
  induction updates generalizing physical with
  | nil => rfl
  | cons update updates inductionHypothesis =>
      simp only [writeMany, logicalWriteMany]
      rw [inductionHypothesis, store.write_exact]

/-- A replay descriptor retains a checkpoint image and the authored update
path to run from it.  Unlike a forked image, it does not promise constant-time
resumption: rebuilding the endpoint performs `updates.length` logical writes.
The checkpoint itself must remain lawfully owned for as long as the descriptor
is retained. -/
structure ReplayDescriptor
    (Physical : Type uPhysical) (Update : Type uUpdate) where
  checkpoint : Physical
  updates : List Update

/-- Reconstruct the endpoint named by a replay descriptor. -/
def replay (store : BindingStore Logical Physical Update)
    (descriptor : ReplayDescriptor Physical Update) : Physical :=
  store.writeMany descriptor.checkpoint descriptor.updates

/-- Replay refines execution of the same authored update path from the
checkpoint's authoritative logical meaning. -/
theorem replay_exact (store : BindingStore Logical Physical Update)
    (descriptor : ReplayDescriptor Physical Update) :
    store.denote (store.replay descriptor) =
      store.logicalWriteMany (store.denote descriptor.checkpoint)
        descriptor.updates :=
  store.writeMany_exact descriptor.checkpoint descriptor.updates

/-! ## Inert physical components -/

/-- Adjoin a physical component which binding updates cannot inspect or
modify.  The auxiliary component may carry a cache, allocator, or another
runtime capability, but this construction applies only while that capability
is inactive for the represented execution region. -/
def withInertPhysical
    (store : BindingStore Logical Physical Update)
    (Auxiliary : Type uPhysical) :
    BindingStore Logical (Physical × Auxiliary) Update where
  denote physical := store.denote physical.1
  logicalWrite := store.logicalWrite
  write physical update := (store.write physical.1 update, physical.2)
  write_exact physical update := store.write_exact physical.1 update

/-- A finite binding-update path leaves an inert physical component exactly
unchanged.  This is a physical equality, not merely equality after logical
denotation. -/
@[simp] theorem withInertPhysical_writeMany_snd
    (store : BindingStore Logical Physical Update)
    (Auxiliary : Type uPhysical) (physical : Physical)
    (auxiliary : Auxiliary) (updates : List Update) :
    ((store.withInertPhysical Auxiliary).writeMany
      (physical, auxiliary) updates).2 = auxiliary := by
  induction updates generalizing physical with
  | nil => rfl
  | cons update updates inductionHypothesis =>
      exact inductionHypothesis (store.write physical update)

end BindingStore

/-! ## Observer-specific forcing -/

/-- An exact observer of a physical binding representation.  The physical
observer returns a possibly optimized representation so dereference may apply
path compression or fill a cache.  Its result must agree with observation of
the authoritative logical substitution, and its representation-only mutation
must preserve that substitution.

Variable dereference, occurs checks, projections, and selected-path matching
are intended instances.  The interface does not require eager construction of
a globally substituted term. -/
structure BindingObservation
    {Logical : Type uLogical} {Physical : Type uPhysical}
    {Update : Type uUpdate}
    (store : BindingStore Logical Physical Update)
    (Query : Type uQuery) (Result : Type uResult) where
  observeLogical : Logical → Query → Result
  observe : Physical → Query → Result × Physical
  result_exact : ∀ physical query,
    (observe physical query).1 = observeLogical (store.denote physical) query
  state_preserved : ∀ physical query,
    store.denote (observe physical query).2 = store.denote physical

namespace BindingObservation

variable {Logical : Type uLogical} {Physical : Type uPhysical}
  {Update : Type uUpdate} {Query : Type uQuery} {Result : Type uResult}
  {store : BindingStore Logical Physical Update}

/-- Exact forcing after an arbitrary finite update path. -/
theorem observe_writeMany_result_exact
    (observation : BindingObservation store Query Result)
    (physical : Physical) (updates : List Update) (query : Query) :
    (observation.observe (store.writeMany physical updates) query).1 =
      observation.observeLogical
        (store.logicalWriteMany (store.denote physical) updates) query := by
  rw [observation.result_exact, store.writeMany_exact]

/-- Representation-level work performed by an observer, such as path
compression, cannot change the logical substitution. -/
theorem observe_writeMany_state_preserved
    (observation : BindingObservation store Query Result)
    (physical : Physical) (updates : List Update) (query : Query) :
    store.denote
        (observation.observe (store.writeMany physical updates) query).2 =
      store.logicalWriteMany (store.denote physical) updates := by
  rw [observation.state_preserved, store.writeMany_exact]

end BindingObservation

/-- A stack-disciplined rollback capability.  A mark remains valid through
later writes, and its saved meaning is stable while those writes accumulate.
The interface does not claim that every physical store has this capability. -/
structure LinearRollbackStore
    (Logical : Type uLogical) (Physical : Type uPhysical)
    (Mark : Type uMark) (Update : Type uUpdate)
    extends BindingStore Logical Physical Update where
  save : Physical → Mark
  valid : Physical → Mark → Prop
  savedMeaning : Physical → Mark → Logical
  save_valid : ∀ physical, valid physical (save physical)
  save_exact : ∀ physical,
    savedMeaning physical (save physical) = denote physical
  valid_write : ∀ physical mark update,
    valid physical mark → valid (write physical update) mark
  savedMeaning_write : ∀ physical mark update,
    valid physical mark →
      savedMeaning (write physical update) mark =
        savedMeaning physical mark
  rollback : Physical → Mark → Physical
  rollback_exact : ∀ physical mark,
    valid physical mark →
      denote (rollback physical mark) = savedMeaning physical mark

namespace LinearRollbackStore

variable {Logical : Type uLogical} {Physical : Type uPhysical}
  {Mark : Type uMark} {Update : Type uUpdate}

/-- A checkpoint remains valid after every finite extension of its path. -/
theorem valid_writeMany
    (store : LinearRollbackStore Logical Physical Mark Update)
    (physical : Physical) (mark : Mark) (updates : List Update)
    (valid : store.valid physical mark) :
    store.valid (store.toBindingStore.writeMany physical updates) mark := by
  induction updates generalizing physical with
  | nil => exact valid
  | cons update updates inductionHypothesis =>
      simp only [BindingStore.writeMany]
      exact inductionHypothesis (store.write physical update)
        (store.valid_write physical mark update valid)

/-- Later writes do not change the logical meaning named by an older valid
checkpoint. -/
theorem savedMeaning_writeMany
    (store : LinearRollbackStore Logical Physical Mark Update)
    (physical : Physical) (mark : Mark) (updates : List Update)
    (valid : store.valid physical mark) :
    store.savedMeaning
        (store.toBindingStore.writeMany physical updates) mark =
      store.savedMeaning physical mark := by
  induction updates generalizing physical with
  | nil => rfl
  | cons update updates inductionHypothesis =>
      simp only [BindingStore.writeMany]
      rw [inductionHypothesis (store.write physical update)
        (store.valid_write physical mark update valid)]
      exact store.savedMeaning_write physical mark update valid

/-- The exact transactional law.  An arbitrary finite write path after a
fresh checkpoint rolls back to the checkpoint's logical denotation. -/
theorem rollback_after_writeMany_exact
    (store : LinearRollbackStore Logical Physical Mark Update)
    (physical : Physical) (updates : List Update) :
    store.denote
        (store.rollback
          (store.toBindingStore.writeMany physical updates)
          (store.save physical)) =
      store.denote physical := by
  let mark := store.save physical
  have validAtStart : store.valid physical mark := store.save_valid physical
  have validAtEnd :
      store.valid
        (store.toBindingStore.writeMany physical updates) mark :=
    store.valid_writeMany physical mark updates validAtStart
  rw [store.rollback_exact _ _ validAtEnd]
  rw [store.savedMeaning_writeMany physical mark updates validAtStart]
  exact store.save_exact physical

/-- Extend a rollback store by an inert physical component without extending
its checkpoint type.  The original mark is sufficient because every write
and rollback preserves the current auxiliary value definitionally. -/
def withInertPhysical
    (store : LinearRollbackStore Logical Physical Mark Update)
    (Auxiliary : Type uPhysical) :
    LinearRollbackStore Logical (Physical × Auxiliary) Mark Update where
  toBindingStore := store.toBindingStore.withInertPhysical Auxiliary
  save physical := store.save physical.1
  valid physical mark := store.valid physical.1 mark
  savedMeaning physical mark := store.savedMeaning physical.1 mark
  save_valid physical := store.save_valid physical.1
  save_exact physical := store.save_exact physical.1
  valid_write physical mark update valid :=
    store.valid_write physical.1 mark update valid
  savedMeaning_write physical mark update valid :=
    store.savedMeaning_write physical.1 mark update valid
  rollback physical mark :=
    (store.rollback physical.1 mark, physical.2)
  rollback_exact physical mark valid :=
    store.rollback_exact physical.1 mark valid

/-- A rollback through the binding-only mark preserves the inert component
physically, including after an arbitrary finite binding-update path. -/
@[simp] theorem withInertPhysical_rollback_writeMany_snd
    (store : LinearRollbackStore Logical Physical Mark Update)
    (Auxiliary : Type uPhysical) (physical : Physical)
    (auxiliary : Auxiliary) (updates : List Update) :
    ((store.withInertPhysical Auxiliary).rollback
      ((store.withInertPhysical Auxiliary).toBindingStore.writeMany
        (physical, auxiliary) updates)
      ((store.withInertPhysical Auxiliary).save
        (physical, auxiliary))).2 = auxiliary := by
  rw [withInertPhysical]
  exact store.toBindingStore.withInertPhysical_writeMany_snd
    Auxiliary physical auxiliary updates

/-- The logical rollback theorem transfers unchanged to the smaller mark
representation. -/
theorem withInertPhysical_rollback_after_writeMany_exact
    (store : LinearRollbackStore Logical Physical Mark Update)
    (Auxiliary : Type uPhysical) (physical : Physical)
    (auxiliary : Auxiliary) (updates : List Update) :
    (store.withInertPhysical Auxiliary).denote
        ((store.withInertPhysical Auxiliary).rollback
          ((store.withInertPhysical Auxiliary).toBindingStore.writeMany
            (physical, auxiliary) updates)
          ((store.withInertPhysical Auxiliary).save
            (physical, auxiliary))) =
      store.denote physical := by
  exact (store.withInertPhysical Auxiliary).rollback_after_writeMany_exact
    (physical, auxiliary) updates

end LinearRollbackStore

/-- A physical representation whose branch images can be independently
owned.  The seed stands for whatever fresh ownership identities, arenas, or
regions the implementation needs. -/
structure ForkableStore
    (Logical : Type uLogical) (Physical : Type uPhysical)
    (Seed : Type uMark) (Update : Type uUpdate)
    extends BindingStore Logical Physical Update where
  fork : Physical → Seed → Physical × Physical
  fork_left_exact : ∀ physical seed,
    denote (fork physical seed).1 = denote physical
  fork_right_exact : ∀ physical seed,
    denote (fork physical seed).2 = denote physical

namespace ForkableStore

variable {Logical : Type uLogical} {Physical : Type uPhysical}
  {Seed : Type uMark} {Update : Type uUpdate}

/-- Evolving the left returned image performs exactly one logical write while
the right image retains the fork-point meaning.  Physical non-aliasing remains
an implementation obligation; this theorem is its denotational consequence. -/
theorem write_left_keep_right_exact
    (store : ForkableStore Logical Physical Seed Update)
    (physical : Physical) (seed : Seed) (update : Update) :
    store.denote (store.write (store.fork physical seed).1 update) =
        store.logicalWrite (store.denote physical) update ∧
      store.denote (store.fork physical seed).2 = store.denote physical := by
  constructor
  · rw [store.write_exact, store.fork_left_exact]
  · exact store.fork_right_exact physical seed

/-- Both owned images initially denote the same logical substitution. -/
theorem fork_denotations_equal
    (store : ForkableStore Logical Physical Seed Update)
    (physical : Physical) (seed : Seed) :
    store.denote (store.fork physical seed).1 =
      store.denote (store.fork physical seed).2 := by
  rw [store.fork_left_exact, store.fork_right_exact]

end ForkableStore

/-! ## Materialization-free observation -/

/-- A consumer may avoid constructing a fully materialized value exactly when
it supplies a direct observation that commutes with the reference
materialize-then-observe path.  The closure may contain a term, a binding
environment, revision identity, and any other immutable source view.

This is an admission interface: consumers without a `commutes` proof must use
the materializing path. -/
structure DelayedObservation
    (Closure : Type uPhysical) (Materialized : Type uLogical)
    (Result : Type uUpdate) where
  materialize : Closure → Materialized
  observeMaterialized : Closure → Materialized → Result
  observeDirect : Closure → Result
  commutes : ∀ closure,
    observeDirect closure =
      observeMaterialized closure (materialize closure)

namespace DelayedObservation

variable {Closure : Type uPhysical} {Materialized : Type uLogical}
  {Result : Type uUpdate}

/-- The direct path is an exact replacement for materialization for this
declared observer. -/
theorem observeDirect_exact
    (observation : DelayedObservation Closure Materialized Result)
    (closure : Closure) :
    observation.observeDirect closure =
      observation.observeMaterialized closure
        (observation.materialize closure) :=
  observation.commutes closure

end DelayedObservation

/-! ## A concrete chronological-history model -/

/-- The simplest append-only logical history.  It is a semantic reference
model, not a claim about the physical layout of a production matcher. -/
structure History (Update : Type uUpdate) where
  updates : List Update
deriving DecidableEq, Repr

namespace History

variable {Update : Type uUpdate}

/-- A mark is only a depth.  Earlier contents remain available because valid
histories are append-only until rollback. -/
abbrev Mark := Nat

def store : LinearRollbackStore
    (List Update) (History Update) Mark Update where
  denote physical := physical.updates
  logicalWrite logical update := logical ++ [update]
  write physical update := ⟨physical.updates ++ [update]⟩
  write_exact _ _ := rfl
  save physical := physical.updates.length
  valid physical mark := mark ≤ physical.updates.length
  savedMeaning physical mark := physical.updates.take mark
  save_valid physical := Nat.le_refl physical.updates.length
  save_exact physical := by simp
  valid_write physical mark update valid := by
    simpa using Nat.le.step valid
  savedMeaning_write physical mark update valid := by
    simp [List.take_append, valid]
  rollback physical mark := ⟨physical.updates.take mark⟩
  rollback_exact _ _ _ := rfl

@[simp] theorem denote_store (history : History Update) :
    store.denote history = history.updates := rfl

end History

/-! ## Current-path versus frontier observations -/

/-- No decoder from one current logical history can recover every possible
live sibling frontier.  The counterexample uses two frontiers with the same
selected current path and a different retained sibling.

This is the information-theoretic boundary behind branch capture: a trail
plus no additional owned state can serve current-path observation, but cannot
serve an arbitrary direct-frontier observation.  Replay avoids the no-go only
because its checkpoint and update path are additional retained information. -/
theorem no_frontier_observation_factors_through_current
    {Update : Type uUpdate} (update : Update) :
    ¬ ∃ decode : List Update → List (List Update),
        ∀ frontier current,
          current ∈ frontier → decode current = frontier := by
  rintro ⟨decode, exactForEveryFrontier⟩
  have singleton := exactForEveryFrontier [[update]] [update] (by simp)
  have withSibling :=
    exactForEveryFrontier [[update], []] [update] (by simp)
  have impossible : [[update]] = [[update], []] :=
    singleton.symm.trans withSibling
  simp at impossible

/-! ## Prefix-graph cost model -/

section PrefixCost

variable {Update : Type uUpdate}

/-- All prefixes of a path are distinct because they have distinct lengths. -/
theorem inits_nodup (path : List Update) : path.inits.Nodup := by
  induction path with
  | nil => simp
  | cons update path inductionHypothesis =>
      rw [List.inits_cons]
      refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · simp
      · exact inductionHypothesis.map fun left right equal => by
          simpa using congrArg List.tail equal

variable [DecidableEq Update]

/-- The explicit nonempty path prefixes retained by one linear trail. -/
def nonemptyPrefixes (path : List Update) : Finset (List Update) :=
  path.inits.tail.toFinset

/-- The shared temporal-prefix graph retained for a directly resumable
frontier.  This is not a term index. -/
def frontierPrefixes (frontier : List (List Update)) : Finset (List Update) :=
  (frontier.flatMap fun path => path.inits.tail).toFinset

/-- Unit-edge storage charged to one trail. -/
def trailPrefixCost (path : List Update) : Nat := path.length

/-- Unit-edge storage charged to the shared prefix graph of a frontier. -/
def frontierPrefixCost (frontier : List (List Update)) : Nat :=
  (frontierPrefixes frontier).card

theorem nonemptyPrefixes_card (path : List Update) :
    (nonemptyPrefixes path).card = path.length := by
  rw [nonemptyPrefixes, List.toFinset_card_of_nodup (inits_nodup path).tail]
  simp [List.length_inits]

theorem nonemptyPrefixes_subset_frontierPrefixes
    {path : List Update} {frontier : List (List Update)}
    (live : path ∈ frontier) :
    nonemptyPrefixes path ⊆ frontierPrefixes frontier := by
  intro nodePrefix prefixMember
  rw [nonemptyPrefixes, List.mem_toFinset] at prefixMember
  rw [frontierPrefixes, List.mem_toFinset, List.mem_flatMap]
  exact ⟨path, live, prefixMember⟩

/-- With exactly one live path, the trail and shared prefix graph have equal
unit-edge storage. -/
theorem trail_optimal_for_single_live_path (path : List Update) :
    frontierPrefixCost [path] = trailPrefixCost path := by
  rw [frontierPrefixCost, trailPrefixCost]
  simp only [frontierPrefixes, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  exact nonemptyPrefixes_card path

/-- Every prefix graph that retains the current path pays at least the
trail's unit-edge cost.  This is the precise conditional optimality theorem. -/
theorem trail_cost_le_frontier_cost_of_live
    {path : List Update} {frontier : List (List Update)}
    (live : path ∈ frontier) :
    trailPrefixCost path ≤ frontierPrefixCost frontier := by
  rw [trailPrefixCost, ← nonemptyPrefixes_card path, frontierPrefixCost]
  exact Finset.card_le_card (nonemptyPrefixes_subset_frontierPrefixes live)

/-- Retaining any prefix outside the current trail makes the shared frontier
strictly more expensive in the same cost model. -/
theorem trail_cost_lt_frontier_cost_of_new_prefix
    {path : List Update} {frontier : List (List Update)}
    (live : path ∈ frontier) (nodePrefix : List Update)
    (inFrontier : nodePrefix ∈ frontierPrefixes frontier)
    (notCurrent : nodePrefix ∉ nonemptyPrefixes path) :
    trailPrefixCost path < frontierPrefixCost frontier := by
  rw [trailPrefixCost, ← nonemptyPrefixes_card path, frontierPrefixCost]
  have subset := nonemptyPrefixes_subset_frontierPrefixes live
  exact Finset.card_lt_card
    ((Finset.ssubset_iff_of_subset subset).2
      ⟨nodePrefix, inFrontier, notCurrent⟩)

end PrefixCost

/-! ## Capture-capacity bridge -/

open BranchCaptureAlgebra

/-- A single rollback history realizes exclusive one-shot choice. -/
theorem linear_history_admits_exclusive_oneShot :
    BranchCaptureAlgebra.Admitted .oneShot .exclusiveOneShot := by
  decide

/-- The same single current history cannot be advertised as an owned
multi-shot frontier. -/
theorem linear_history_rejects_owned_multiShot :
    ¬ BranchCaptureAlgebra.Admitted .oneShot .ownedMultiShot := by
  decide

/-- Independently owned branch images have the capacity required by a direct
multi-shot frontier. -/
theorem owned_images_admit_owned_multiShot :
    BranchCaptureAlgebra.Admitted .multiShot .ownedMultiShot := by
  decide

/-! ## Positive and negative controls -/

namespace Canaries

def base : History Nat := ⟨[10]⟩

/-- A simple exact observer.  Production dereference may update its physical
state through path compression; this reference observer has nothing to cache. -/
def historyLengthObservation :
    BindingObservation
      (History.store (Update := Nat)).toBindingStore Unit Nat where
  observeLogical (logical : List Nat) _ := logical.length
  observe (physical : History Nat) _ := (physical.updates.length, physical)
  result_exact _ _ := rfl
  state_preserved _ _ := rfl

/-- Positive: arbitrary finite extension rolls back exactly. -/
example :
    History.store.denote
        (History.store.rollback
          (History.store.toBindingStore.writeMany base [20, 30])
          (History.store.save base)) = [10] := by
  exact History.store.rollback_after_writeMany_exact base [20, 30]

/-- Positive: one live path pays exactly its depth in the prefix model. -/
example : frontierPrefixCost [[1, 2, 3]] = 3 := by decide

/-- Positive: observer forcing after writes agrees with the logical history. -/
example :
    (historyLengthObservation.observe
      (History.store.toBindingStore.writeMany base [20, 30]) ()).1 = 3 := by
  rfl

/-- Negative: the constant-zero result cannot implement length observation
for every physical history. -/
example : ¬ ∀ history : History Nat, 0 = history.updates.length := by
  intro claimed
  simpa using claimed ⟨[1]⟩

/-- Positive: a checkpoint plus a path reconstructs its logical endpoint
without requiring an independently live sibling image. -/
example :
    History.store.denote
        (History.store.replay
          { checkpoint := base, updates := [20, 30] }) = [10, 20, 30] := by
  rfl

/-- Negative control: a sibling with a genuinely new prefix increases the
direct-frontier footprint. -/
example : trailPrefixCost [1, 2] < frontierPrefixCost [[1, 2], [1, 3]] := by
  decide

/-- Negative control: current-path denotation cannot reconstruct both a
singleton frontier and one retaining a sibling. -/
example :
    ¬ ∃ decode : List Nat → List (List Nat),
        ∀ frontier current,
          current ∈ frontier → decode current = frontier :=
  no_frontier_observation_factors_through_current 1

/-- Positive: an inert auxiliary component needs no additional checkpoint
information and remains physically unchanged through writes and rollback. -/
example :
    let extended := History.store.withInertPhysical Nat
    let checkpoint := extended.save (base, 7)
    let evolved := extended.toBindingStore.writeMany (base, 7) [20, 30]
    extended.rollback evolved checkpoint = (base, 7) := by
  decide

/-- A deliberately non-inert auxiliary write. -/
def writeChangingAuxiliary
    (physical : History Nat × Nat) (update : Nat) : History Nat × Nat :=
  (History.store.write physical.1 update, physical.2 + 1)

/-- Roll back only the binding component while retaining the current
auxiliary component. -/
def rollbackBindingOnly
    (physical : History Nat × Nat) (mark : History.Mark) :
    History Nat × Nat :=
  (History.store.rollback physical.1 mark, physical.2)

/-- Negative: once the auxiliary component changes, a binding-only mark does
not restore the original physical product.  Inertness is therefore a real
admission premise, not an implementation convenience. -/
example :
    rollbackBindingOnly
        (writeChangingAuxiliary (base, 0) 20)
        (History.store.save base) ≠ (base, 0) := by
  decide

end Canaries

#print axioms BindingStore.writeMany_exact
#print axioms BindingStore.replay_exact
#print axioms BindingObservation.observe_writeMany_result_exact
#print axioms BindingObservation.observe_writeMany_state_preserved
#print axioms LinearRollbackStore.rollback_after_writeMany_exact
#print axioms BindingStore.withInertPhysical_writeMany_snd
#print axioms LinearRollbackStore.withInertPhysical_rollback_writeMany_snd
#print axioms LinearRollbackStore.withInertPhysical_rollback_after_writeMany_exact
#print axioms DelayedObservation.observeDirect_exact
#print axioms no_frontier_observation_factors_through_current
#print axioms nonemptyPrefixes_card
#print axioms trail_optimal_for_single_live_path
#print axioms trail_cost_le_frontier_cost_of_live
#print axioms trail_cost_lt_frontier_cost_of_new_prefix
#print axioms linear_history_rejects_owned_multiShot

end Mettapedia.GSLT.Core.BindingStoreCapabilityAlgebra
