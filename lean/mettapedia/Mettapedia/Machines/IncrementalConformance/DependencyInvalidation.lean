import Mettapedia.Machines.ConjunctionPlanning

/-!
# Dependency-directed candidate reuse

An executable cache for the admitted flat-pattern candidate prefilter in
`ConjunctionPlanning`. A patch lists changed binding cells and replaced spaces.
Only probes reading one of those locations are recomputed. The independent
reference materializes every pattern and collects its candidates afresh.

The theorem preserves the complete ordered sequence of occurrence identifiers,
including distinct occurrences with equal values. It is stronger than equality
of ranking scores. Unbound repeated variables remain candidate wildcards;
subsequent exact unification must check their correlation.

This fragment has direct binding-cell reads and immutable probe descriptors.
Aliases require transitive dependency support; dynamic dispatch, predicates with
effects, changes to the probe itself, and unreported writes are outside it.
The work counters count candidate recomputations and row-predicate calls, not
dependency lookup, map lookup, cache allocation, instructions, or elapsed time.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.IncrementalConformance.DependencyInvalidation

open ConjunctionPlanning.FlatPattern

structure World where
  bindings : Environment
  spaces : Nat → List Occurrence

structure Probe where
  space : Nat
  pattern : Pattern
  deriving DecidableEq, Repr

/-- Simultaneous writes: the first entry for a key wins. No state outside the
listed keys changes. The values may replace a binding with `none`. -/
def writeKeys {α : Type} (writes : List (Nat × α)) : List Nat := writes.map Prod.fst

def writeAll {α : Type} (base : Nat → α) : List (Nat × α) → Nat → α
  | [], key => base key
  | (key', value) :: rest, key =>
      if key = key' then value else writeAll base rest key

theorem writeAll_unchanged {α : Type} (base : Nat → α)
    (writes : List (Nat × α)) (key : Nat) (outside : key ∉ writeKeys writes) :
    writeAll base writes key = base key := by
  induction writes with
  | nil => rfl
  | cons pair rest ih =>
      simp only [writeKeys, List.map_cons, List.mem_cons, not_or] at outside
      simp only [writeAll, outside.1, ↓reduceIte]
      exact ih outside.2

structure Patch where
  bindings : List (Nat × Option Nat)
  spaces : List (Nat × List Occurrence)
  deriving DecidableEq, Repr

def Patch.apply (patch : Patch) (world : World) : World :=
  ⟨writeAll world.bindings patch.bindings, writeAll world.spaces patch.spaces⟩

/-- Syntactic dependency extraction is executable and proved sufficient below. -/
def touches (keys : List Nat) : Pattern → Bool
  | [] => false
  | .value _ :: rest => touches keys rest
  | .var key :: rest => keys.contains key || touches keys rest

def dirty (patch : Patch) (probe : Probe) : Bool :=
  (writeKeys patch.spaces).contains probe.space ||
    touches (writeKeys patch.bindings) probe.pattern

theorem testView_unchanged (env : Environment) (writes : List (Nat × Option Nat))
    (pattern : Pattern) (row : Row)
    (clean : touches (writeKeys writes) pattern = false) :
    testView (writeAll env writes) pattern row = testView env pattern row := by
  induction pattern generalizing row with
  | nil => cases row <;> rfl
  | cons cell rest ih =>
      cases row with
      | nil => rfl
      | cons value tail =>
          cases cell with
          | value constant =>
              exact congrArg (fun b => (constant == value) && b) (ih tail clean)
          | var key =>
              have clean' : key ∉ writeKeys writes ∧
                  touches (writeKeys writes) rest = false := by
                simpa [touches] using clean
              simp only [testView, testCell, writeAll_unchanged env writes key clean'.1]
              rw [ih tail clean'.2]

/-- Fresh recomputation follows the materialization-and-collection reference. -/
def reference (world : World) (probe : Probe) : List Nat :=
  (collectCandidates
    (testView emptyEnvironment (materialize world.bindings probe.pattern).1)
    (world.spaces probe.space)).1

/-- The incremental path reads bindings directly, without materialization. -/
def computeScan (world : World) (probe : Probe) : List Nat × CandidateWork :=
  collectCandidates (testView world.bindings probe.pattern) (world.spaces probe.space)

def compute (world : World) (probe : Probe) : List Nat := (computeScan world probe).1

/-- This is the counter returned by the executed row-scanning algorithm. -/
theorem computeScan_tests (world : World) (probe : Probe) :
    (computeScan world probe).2.tests = (world.spaces probe.space).length :=
  collectCandidates_tests _ _

theorem compute_eq_reference (world : World) (probe : Probe) :
    compute world probe = reference world probe := by
  have same := funext (materialize_test world.bindings probe.pattern)
  simp only [compute, computeScan, reference, same]

/-- The support theorem is proved for the concrete pattern evaluator; no
dependency-soundness assumption is supplied by the caller. -/
theorem clean_reference_unchanged (world : World) (patch : Patch) (probe : Probe)
    (clean : dirty patch probe = false) :
    reference (patch.apply world) probe = reference world probe := by
  have clean' : probe.space ∉ writeKeys patch.spaces ∧
      touches (writeKeys patch.bindings) probe.pattern = false := by
    simpa [dirty] using clean
  rw [← compute_eq_reference, ← compute_eq_reference]
  have tests : testView (writeAll world.bindings patch.bindings) probe.pattern =
      testView world.bindings probe.pattern :=
    funext fun row => testView_unchanged _ _ _ row clean'.2
  simp only [compute, computeScan, Patch.apply, tests,
    writeAll_unchanged world.spaces patch.spaces probe.space clean'.1]

structure Entry where
  probe : Probe
  candidates : List Nat
  deriving DecidableEq, Repr

def freshCache (world : World) (probes : List Probe) : List Entry :=
  probes.map fun probe => ⟨probe, reference world probe⟩

def Valid (world : World) (cache : List Entry) : Prop :=
  ∀ entry ∈ cache, entry.candidates = reference world entry.probe

theorem freshCache_valid (world : World) (probes : List Probe) :
    Valid world (freshCache world probes) := by
  intro entry present
  obtain ⟨probe, _, rfl⟩ := List.mem_map.mp present
  rfl

structure RefreshResult where
  cache : List Entry
  recomputations : Nat
  rowTests : Nat
  deriving DecidableEq, Repr

/-- Charge a recomputation only in the branch that calls `compute`, and its
actual scan length. Retained entries incur neither counted operation. -/
def refresh (world : World) (patch : Patch) : List Entry → RefreshResult
  | [] => ⟨[], 0, 0⟩
  | entry :: rest =>
      let tail := refresh world patch rest
      if dirty patch entry.probe then
        let here := computeScan (patch.apply world) entry.probe
        ⟨⟨entry.probe, here.1⟩ :: tail.cache,
          tail.recomputations + 1,
          tail.rowTests + here.2.tests⟩
      else
        ⟨entry :: tail.cache, tail.recomputations, tail.rowTests⟩

/-- The maintained cache equals independent fresh recomputation entry by entry,
not merely as a set of distinct values or as a total candidate count. -/
theorem refresh_eq_fresh (world : World) (patch : Patch) (cache : List Entry)
    (valid : Valid world cache) :
    (refresh world patch cache).cache =
      freshCache (patch.apply world) (cache.map Entry.probe) := by
  induction cache with
  | nil => rfl
  | cons entry rest ih =>
      have here := valid entry (by simp)
      have tail : Valid world rest := fun e he => valid e (by simp [he])
      simp only [refresh]
      split <;> simp only [freshCache, List.map_cons]
      · rw [ih tail, ← compute, compute_eq_reference]
        rfl
      · rename_i clean
        have clean' : dirty patch entry.probe = false := by simpa using clean
        rw [ih tail]
        have equality : entry =
            Entry.mk entry.probe (reference (patch.apply world) entry.probe) := by
          cases entry
          simp only [Entry.mk.injEq, true_and] at *
          exact here.trans (clean_reference_unchanged _ _ _ clean').symm
        rw [equality]
        rfl

theorem refresh_valid (world : World) (patch : Patch) (cache : List Entry)
    (valid : Valid world cache) :
    Valid (patch.apply world) (refresh world patch cache).cache := by
  rw [refresh_eq_fresh _ _ _ valid]
  exact freshCache_valid _ _

/-- Refreshes compose, so preservation is not restricted to one update. -/
theorem refresh_twice_eq_fresh (world : World) (first second : Patch)
    (cache : List Entry) (valid : Valid world cache) :
    (refresh (first.apply world) second (refresh world first cache).cache).cache =
      freshCache (second.apply (first.apply world)) (cache.map Entry.probe) := by
  rw [refresh_eq_fresh _ _ _ (refresh_valid _ _ _ valid)]
  rw [refresh_eq_fresh _ _ _ valid]
  simp only [freshCache, List.map_map, Function.comp_def]

theorem refresh_recomputations (world : World) (patch : Patch) (cache : List Entry) :
    (refresh world patch cache).recomputations =
      (cache.filter fun entry => dirty patch entry.probe).length := by
  induction cache with
  | nil => rfl
  | cons entry rest ih =>
      simp only [refresh]
      split <;> simp_all

theorem refresh_rowTests (world : World) (patch : Patch) (cache : List Entry) :
    (refresh world patch cache).rowTests =
      ((cache.filter fun entry => dirty patch entry.probe).map
        fun entry => ((patch.apply world).spaces entry.probe.space).length).sum := by
  induction cache with
  | nil => rfl
  | cons entry rest ih =>
      simp only [refresh]
      split <;> simp_all [computeScan_tests, Nat.add_comm]

theorem refresh_recomputations_le (world : World) (patch : Patch) (cache : List Entry) :
    (refresh world patch cache).recomputations ≤ cache.length := by
  rw [refresh_recomputations]
  exact List.length_filter_le _ _

/-- A full fresh scan executes all these row tests. Dependency maintenance does
not increase that counted work, although checking dependencies has its own cost. -/
theorem refresh_rowTests_le_fresh (world : World) (patch : Patch) (cache : List Entry) :
    (refresh world patch cache).rowTests ≤
      (cache.map fun e => ((patch.apply world).spaces e.probe.space).length).sum := by
  induction cache with
  | nil => simp [refresh]
  | cons entry rest ih =>
      simp only [refresh, List.map_cons, List.sum_cons]
      split <;> simp only [computeScan_tests] <;> omega

/-- Disjoint changes execute no candidate recomputations or row tests and
retain the actual entries, rather than rebuilding equal candidate arrays. -/
theorem refresh_disjoint (world : World) (patch : Patch) (cache : List Entry)
    (disjoint : ∀ entry ∈ cache, dirty patch entry.probe = false) :
    refresh world patch cache = ⟨cache, 0, 0⟩ := by
  induction cache with
  | nil => rfl
  | cons entry rest ih =>
      have head := disjoint entry (by simp)
      have tail := ih (fun e he => disjoint e (by simp [he]))
      simp [refresh, head, tail]

/-- Every occurrence count is preserved; duplicated values at separate stored
occurrences cannot silently disappear through cache maintenance. -/
theorem refresh_occurrence_counts (world : World) (patch : Patch) (cache : List Entry)
    (valid : Valid world cache) (id : Nat) :
    ((refresh world patch cache).cache.map fun e => e.candidates.count id) =
      (cache.map fun e => (reference (patch.apply world) e.probe).count id) := by
  rw [refresh_eq_fresh _ _ _ valid]
  simp [freshCache, List.map_map, Function.comp_def]

/-! ## Immutable space revisions

A revisioned backend can use the same cache without comparing old and new row
lists. Selecting a new revision creates a space patch even when the old query
returned no candidates. The table is immutable: reusing a revision name for
different contents would break this interface's premise.
-/

abbrev RevisionTable := Nat → Nat → List Occurrence

def revisionWorld (bindings : Environment) (revisions : Nat → Nat)
    (table : RevisionTable) : World :=
  ⟨bindings, fun space => table space (revisions space)⟩

def revisionPatch (bindings : List (Nat × Option Nat))
    (revisions : List (Nat × Nat)) (table : RevisionTable) : Patch :=
  ⟨bindings, revisions.map fun item => (item.1, table item.1 item.2)⟩

theorem writeAll_revision_rows (revisions : Nat → Nat) (writes : List (Nat × Nat))
    (table : RevisionTable) (space : Nat) :
    writeAll (fun s => table s (revisions s))
        (writes.map fun item => (item.1, table item.1 item.2)) space =
      table space (writeAll revisions writes space) := by
  induction writes with
  | nil => rfl
  | cons item rest ih =>
      simp only [List.map_cons, writeAll]
      split
      · rename_i equal
        subst space
        rfl
      · exact ih

/-- The revision adapter implements the independently stated snapshot world. -/
theorem revisionPatch_apply (bindings : Environment) (revisions : Nat → Nat)
    (bindingWrites : List (Nat × Option Nat)) (revisionWrites : List (Nat × Nat))
    (table : RevisionTable) :
    (revisionPatch bindingWrites revisionWrites table).apply
        (revisionWorld bindings revisions table) =
      revisionWorld (writeAll bindings bindingWrites)
        (writeAll revisions revisionWrites) table := by
  have same := funext fun space =>
    writeAll_revision_rows revisions revisionWrites table space
  exact congrArg (World.mk (writeAll bindings bindingWrites)) same

/-- An announced revision change invalidates every probe on that space,
including probes whose cached candidate list was empty. -/
theorem revision_write_is_dirty (bindingWrites : List (Nat × Option Nat))
    (revisionWrites : List (Nat × Nat)) (table : RevisionTable) (probe : Probe)
    (changed : probe.space ∈ writeKeys revisionWrites) :
    dirty (revisionPatch bindingWrites revisionWrites table) probe = true := by
  simp [dirty, revisionPatch, writeKeys, List.map_map, Function.comp_def] at *
  exact Or.inl changed

theorem refresh_revision_eq_fresh (bindings : Environment) (revisions : Nat → Nat)
    (bindingWrites : List (Nat × Option Nat)) (revisionWrites : List (Nat × Nat))
    (table : RevisionTable) (cache : List Entry)
    (valid : Valid (revisionWorld bindings revisions table) cache) :
    (refresh (revisionWorld bindings revisions table)
        (revisionPatch bindingWrites revisionWrites table) cache).cache =
      freshCache (revisionWorld (writeAll bindings bindingWrites)
        (writeAll revisions revisionWrites) table) (cache.map Entry.probe) := by
  rw [refresh_eq_fresh _ _ _ valid, revisionPatch_apply]

/-! ## Fixed binding aliases

The direct-cell theorem cannot be applied to native variable names whose lookup
silently follows an alias. For a fixed map to physical representatives, first
translate the pattern's variable cells; the same dependency algorithm is then
sound. A mutable alias graph additionally requires invalidation on changes to
its traversed links. No theorem here computes transitive alias support.
-/

def physicalPattern (representative : Nat → Nat) : Pattern → Pattern
  | [] => []
  | .value n :: rest => .value n :: physicalPattern representative rest
  | .var v :: rest => .var (representative v) :: physicalPattern representative rest

theorem physicalPattern_test (representative : Nat → Nat) (env : Environment)
    (pattern : Pattern) (row : Row) :
    testView env (physicalPattern representative pattern) row =
      testView (fun v => env (representative v)) pattern row := by
  induction pattern generalizing row with
  | nil => cases row <;> rfl
  | cons cell rest ih =>
      cases row with
      | nil => cases cell <;> rfl
      | cons n ns =>
          cases cell <;> simp only [physicalPattern, testView, testCell, ih]

/-- The dependency check must mention the physical cells actually read. -/
theorem physicalPattern_unchanged (representative : Nat → Nat) (env : Environment)
    (writes : List (Nat × Option Nat)) (pattern : Pattern) (row : Row)
    (clean : touches (writeKeys writes) (physicalPattern representative pattern) = false) :
    testView (fun v => writeAll env writes (representative v)) pattern row =
      testView (fun v => env (representative v)) pattern row := by
  calc
    _ = testView (writeAll env writes) (physicalPattern representative pattern) row :=
      (physicalPattern_test representative (writeAll env writes) pattern row).symm
    _ = testView env (physicalPattern representative pattern) row :=
      testView_unchanged _ _ _ _ clean
    _ = _ := physicalPattern_test representative env pattern row

namespace Controls

def world : World :=
  ⟨emptyEnvironment, fun space => if space = 0 then
    [⟨10, [7]⟩, ⟨11, [7]⟩, ⟨12, [8]⟩] else [⟨20, [9]⟩]⟩

def probe : Probe := ⟨0, [.var 0]⟩
def unrelated : Patch := ⟨[(5, some 4)], [(3, [])]⟩
def bindSeven : Patch := ⟨[(0, some 7)], []⟩
def replaceRows : Patch := ⟨[], [(0, [⟨13, [7]⟩])]⟩

theorem disjoint_change_no_candidate_work :
    refresh world unrelated (freshCache world [probe]) =
      ⟨[⟨probe, [10, 11, 12]⟩], 0, 0⟩ := by decide

theorem binding_change_recomputes_preserving_duplicates :
    refresh world bindSeven (freshCache world [probe]) =
      ⟨[⟨probe, [10, 11]⟩], 1, 3⟩ := by decide

theorem space_change_recomputes :
    refresh world replaceRows (freshCache world [probe]) =
      ⟨[⟨probe, [13]⟩], 1, 1⟩ := by decide

/-- Reusing an entry solely because the space did not change is unsound. -/
theorem stale_binding_cache_is_wrong :
    ¬ Valid (bindSeven.apply world) (freshCache world [probe]) := by
  intro valid
  have bad := valid ⟨probe, [10, 11, 12]⟩ (by decide)
  have impossible : ([10, 11, 12] : List Nat) = [10, 11] := bad
  contradiction

/-- Reusing an entry solely because the bindings did not change is unsound. -/
theorem stale_space_cache_is_wrong :
    ¬ Valid (replaceRows.apply world) (freshCache world [probe]) := by
  intro valid
  have bad := valid ⟨probe, [10, 11, 12]⟩ (by decide)
  have impossible : ([10, 11, 12] : List Nat) = [13] := bad
  contradiction

theorem unaffected_leg_does_not_rescan :
    refresh world bindSeven
      (freshCache world [probe, ⟨1, [.var 5]⟩]) =
      ⟨[⟨probe, [10, 11]⟩, ⟨⟨1, [.var 5]⟩, [20]⟩], 1, 3⟩ := by decide

def revisions : Nat → Nat := fun _ => 0
def revisionRows : RevisionTable :=
  fun space revision => if space = 0 ∧ revision = 1 then [⟨31, [7]⟩] else []

/-- Watching only rows returned previously misses insertions into an empty
result. A query depends on its space even when it has no occurrence witnesses. -/
theorem empty_result_invalidated_on_revision :
    refresh (revisionWorld emptyEnvironment revisions revisionRows)
      (revisionPatch [] [(0, 1)] revisionRows)
      (freshCache (revisionWorld emptyEnvironment revisions revisionRows) [probe]) =
      ⟨[⟨probe, [31]⟩], 1, 1⟩ := by decide

theorem stale_empty_result_is_wrong :
    ¬ Valid (revisionWorld emptyEnvironment (writeAll revisions [(0, 1)]) revisionRows)
      (freshCache (revisionWorld emptyEnvironment revisions revisionRows) [probe]) := by
  intro valid
  have bad := valid ⟨probe, []⟩ (by decide)
  have impossible : ([] : List Nat) = [31] := bad
  contradiction

def aliasTarget : Nat → Nat := fun v => if v = 0 then 1 else v
def aliasWrite : List (Nat × Option Nat) := [(1, some 7)]

/-- A syntactic dependency on variable 0 misses the physical read of cell 1. -/
theorem syntactic_alias_dependency_is_unsound :
    touches (writeKeys aliasWrite) [.var 0] = false ∧
    testView (fun v => emptyEnvironment (aliasTarget v)) [.var 0] [8] = true ∧
    testView (fun v => writeAll emptyEnvironment aliasWrite (aliasTarget v))
      [.var 0] [8] = false := by decide

theorem representative_dependency_detects_alias_write :
    touches (writeKeys aliasWrite) (physicalPattern aliasTarget [.var 0]) = true := by
  decide

end Controls
end Mettapedia.Machines.IncrementalConformance.DependencyInvalidation
