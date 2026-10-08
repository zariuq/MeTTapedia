import Mettapedia.Machines.ConstructorSummary

/-!
# Demand-computed summaries of immutable constructor DAGs

Nodes have finite lists of lower-ranked children. The rank is a termination
witness, not a fixed bound on language terms or an allocation discipline.
The executable evaluator consults a cache, recursively demands children on a
miss, and installs the newly combined summary. The algebra may depend on a
node's allocation label; in particular it need not be an unlocated bit fold.

Cached metadata and physical edges are separate. An absent summary is not
evidence of absent variables, references, effects, or collector roots.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.DemandSummary

universe u v w

structure Graph (Label : Type u) where
  label : Nat → Label
  children : (i : Nat) → List (Fin i)

abbrev Cache (Summary : Type v) := Nat → Option Summary

structure Result (Value : Type w) (Summary : Type v) where
  value : Value
  cache : Cache Summary
  computed : List Nat

variable {Label : Type u} {Summary : Type v} {Value : Type w}

def eager (g : Graph Label) (combine : Label → List Summary → Summary)
    (i : Nat) : Summary :=
  combine (g.label i) ((g.children i).map fun child => eager g combine child.val)
termination_by i

def sequence {A : Type w} (xs : List A)
    (step : A → Cache Summary → Result Summary Summary)
    (cache : Cache Summary) : Result (List Summary) Summary :=
  match xs with
  | [] => ⟨[], cache, []⟩
  | x :: xs =>
      let first := step x cache
      let rest := sequence xs step first.cache
      ⟨first.value :: rest.value, rest.cache, first.computed ++ rest.computed⟩

def demand (g : Graph Label) (combine : Label → List Summary → Summary)
    (i : Nat) (cache : Cache Summary) : Result Summary Summary :=
  match cache i with
  | some value => ⟨value, cache, []⟩
  | none =>
      let children := sequence (g.children i)
        (fun child c => demand g combine child.val c) cache
      let value := combine (g.label i) children.value
      ⟨value, Function.update children.cache i (some value), children.computed ++ [i]⟩
termination_by i

def Sound (g : Graph Label) (combine : Label → List Summary → Summary)
    (cache : Cache Summary) : Prop :=
  ∀ i value, cache i = some value → value = eager g combine i

def Extends (before after : Cache Summary) : Prop :=
  ∀ i value, before i = some value → after i = some value

theorem Extends.refl (cache : Cache Summary) : Extends cache cache := by
  intro i value h
  exact h

theorem Extends.trans {a b c : Cache Summary}
    (ab : Extends a b) (bc : Extends b c) : Extends a c := by
  intro i value h
  exact bc i value (ab i value h)

theorem Extends.none_of_none {a b : Cache Summary} (ab : Extends a b)
    {i : Nat} (absent : b i = none) : a i = none := by
  cases h : a i with
  | none => rfl
  | some value => simpa [absent] using ab i value h

theorem Extends.some_of_some {a b : Cache Summary} (ab : Extends a b)
    {i : Nat} (present : (a i).isSome = true) : (b i).isSome = true := by
  cases h : a i with
  | none => simp [h] at present
  | some value => simp [ab i value h]

/-- Construction accounting. Request/edge accounting is supplied separately by
`demandRequests_eq` and `demandRequests_le_uncached_edges`. -/
structure Valid (g : Graph Label) (combine : Label → List Summary → Summary)
    (before : Cache Summary) (result : Result Value Summary)
    (expected : Value) (bound : Nat) : Prop where
  value_eq : result.value = expected
  sound : Sound g combine result.cache
  preserves : Extends before result.cache
  fresh : ∀ i ∈ result.computed, before i = none
  stored : ∀ i ∈ result.computed, (result.cache i).isSome = true
  nodup : result.computed.Nodup
  bounded : ∀ i ∈ result.computed, i < bound

theorem sequence_valid {A : Type w} (g : Graph Label)
    (combine : Label → List Summary → Summary) (expected : A → Summary)
    (step : A → Cache Summary → Result Summary Summary) (bound : Nat)
    (xs : List A)
    (each : ∀ x ∈ xs, ∀ cache, Sound g combine cache →
      Valid g combine cache (step x cache) (expected x) bound)
    (cache : Cache Summary) (sound : Sound g combine cache) :
    Valid g combine cache (sequence xs step cache) (xs.map expected) bound := by
  induction xs generalizing cache with
  | nil =>
      exact ⟨rfl, sound, Extends.refl _, by simp [sequence],
        by simp [sequence], by simp [sequence], by simp [sequence]⟩
  | cons x xs ih =>
      have first := each x (by simp) cache sound
      have rest := ih (fun y hy => each y (by simp [hy])) _ first.sound
      refine ⟨?_, rest.sound, first.preserves.trans rest.preserves, ?_, ?_, ?_, ?_⟩
      · simp only [sequence, List.map_cons]
        rw [first.value_eq, rest.value_eq]
      · intro i hi
        rcases List.mem_append.mp hi with hi | hi
        · exact first.fresh i hi
        · exact first.preserves.none_of_none (rest.fresh i hi)
      · intro i hi
        rcases List.mem_append.mp hi with hi | hi
        · exact rest.preserves.some_of_some (first.stored i hi)
        · exact rest.stored i hi
      · apply List.nodup_append.mpr
        refine ⟨first.nodup, rest.nodup, ?_⟩
        intro i hi j hj same
        subst j
        have present := first.stored i hi
        simp [rest.fresh i hj] at present
      · intro i hi
        rcases List.mem_append.mp hi with hi | hi
        · exact first.bounded i hi
        · exact rest.bounded i hi

theorem demand_valid (g : Graph Label) (combine : Label → List Summary → Summary)
    (i : Nat) (cache : Cache Summary) (sound : Sound g combine cache) :
    Valid g combine cache (demand g combine i cache) (eager g combine i) (i + 1) := by
  induction i using Nat.strong_induction_on generalizing cache with
  | h i ih =>
      rw [demand]
      cases present : cache i with
      | some value =>
          simp only
          exact ⟨sound i value present, sound, Extends.refl _,
            by simp, by simp, by simp, by simp⟩
      | none =>
          simp only
          have children := sequence_valid g combine
            (fun child : Fin i => eager g combine child.val)
            (fun child : Fin i => fun c => demand g combine child.val c) i
            (g.children i) (by
              intro child _ c hs
              have h := ih child.val child.isLt c hs
              refine { h with bounded := ?_ }
              intro j hj
              have hj' := h.bounded j hj
              omega) cache sound
          have value_eq : combine (g.label i) (sequence (g.children i)
              (fun child c => demand g combine child.val c) cache).value =
              eager g combine i := by
            rw [children.value_eq, eager]
          refine ⟨value_eq, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro j value hj
            by_cases hji : j = i
            · subst j
              simp only [Function.update_self, Option.some.injEq] at hj
              exact hj.symm.trans value_eq
            · have h := children.sound j value
              apply h
              simpa [Function.update, hji] using hj
          · intro j value hj
            have hji : j ≠ i := by intro h; subst j; simp [present] at hj
            simpa [Function.update, hji] using children.preserves j value hj
          · intro j hj
            rcases List.mem_append.mp hj with hj | hj
            · exact children.fresh j hj
            · have : j = i := by simpa using hj
              subst j
              exact present
          · intro j hj
            rcases List.mem_append.mp hj with hj | hj
            · have hji : j ≠ i := by have := children.bounded j hj; omega
              simpa [Function.update, hji] using children.stored j hj
            · have : j = i := by simpa using hj
              subst j
              simp
          · apply List.nodup_append.mpr
            refine ⟨children.nodup, by simp, ?_⟩
            intro j hj k hk heq
            have hj' := children.bounded j hj
            simp only [List.mem_singleton] at hk
            omega
          · intro j hj
            rcases List.mem_append.mp hj with hj | hj
            · have := children.bounded j hj
              omega
            · simp only [List.mem_singleton] at hj
              omega

theorem demand_exact (g : Graph Label) (combine : Label → List Summary → Summary)
    (i : Nat) (cache : Cache Summary) (sound : Sound g combine cache) :
    (demand g combine i cache).value = eager g combine i :=
  (demand_valid g combine i cache sound).value_eq

theorem empty_sound (g : Graph Label) (combine : Label → List Summary → Summary) :
    Sound g combine (fun _ => none) := by
  intro i value h
  cases h

theorem demand_stores (g : Graph Label) (combine : Label → List Summary → Summary)
    (i : Nat) (cache : Cache Summary) :
    (demand g combine i cache).cache i = some (demand g combine i cache).value := by
  rw [demand]
  cases present : cache i <;> simp [present]

/-- A second query of the same node neither recombines a summary nor changes
the cache. The theorem is about combinations, not constant-time C lookup. -/
theorem demand_again (g : Graph Label) (combine : Label → List Summary → Summary)
    (i : Nat) (cache : Cache Summary) :
    demand g combine i (demand g combine i cache).cache =
      ⟨(demand g combine i cache).value, (demand g combine i cache).cache, []⟩ := by
  conv_lhs => rw [demand, demand_stores]

def reachable (g : Graph Label) (i : Nat) : Finset Nat :=
  insert i ((g.children i).toFinset.biUnion fun child => reachable g child.val)
termination_by i

theorem sequence_computed_source {A : Type w} (xs : List A)
    (step : A → Cache Summary → Result Summary Summary) (cache : Cache Summary)
    (i : Nat) (hi : i ∈ (sequence xs step cache).computed) :
    ∃ x ∈ xs, ∃ intermediate, i ∈ (step x intermediate).computed := by
  induction xs generalizing cache with
  | nil => simp [sequence] at hi
  | cons x xs ih =>
      rcases List.mem_append.mp hi with hfirst | hrest
      · exact ⟨x, by simp, cache, hfirst⟩
      · obtain ⟨y, hy, c, hc⟩ := ih (step x cache).cache hrest
        exact ⟨y, by simp [hy], c, hc⟩

theorem demand_computed_reachable (g : Graph Label)
    (combine : Label → List Summary → Summary) (i : Nat) (cache : Cache Summary)
    (j : Nat) (computed : j ∈ (demand g combine i cache).computed) :
    j ∈ reachable g i := by
  induction i using Nat.strong_induction_on generalizing cache with
  | h i ih =>
      rw [demand] at computed
      cases present : cache i with
      | some value => simp [present] at computed
      | none =>
          simp only [present] at computed
          rcases List.mem_append.mp computed with hc | hc
          · obtain ⟨child, hchild, c, hcomputed⟩ :=
              sequence_computed_source _ _ _ j hc
            rw [reachable]
            apply Finset.mem_insert_of_mem
            apply Finset.mem_biUnion.mpr
            exact ⟨child, by simpa using hchild, ih child.val child.isLt c hcomputed⟩
          · have : j = i := by simpa using hc
            subst j
            rw [reachable]
            exact Finset.mem_insert_self _ _

/-- The number of combinations is bounded by distinct reachable nodes whose
summaries were absent initially. Sharing is counted once. An already cached
ancestor can make the inequality strict by avoiding all of its descendants. -/
theorem demand_combinations_le_uncached_reachable (g : Graph Label)
    (combine : Label → List Summary → Summary) (i : Nat) (cache : Cache Summary)
    (sound : Sound g combine cache) :
    (demand g combine i cache).computed.length ≤
      ((reachable g i).filter fun j => (cache j).isNone).card := by
  have valid := demand_valid g combine i cache sound
  rw [← List.toFinset_card_of_nodup valid.nodup]
  apply Finset.card_le_card
  intro j hj
  have member : j ∈ (demand g combine i cache).computed := by simpa using hj
  exact Finset.mem_filter.mpr
    ⟨demand_computed_reachable g combine i cache j member,
      by simp [valid.fresh j member]⟩

/-- Number of cache requests made by a sequence, threading the actual
post-request cache from the existing evaluator. -/
def sequenceRequests {A : Type w} (xs : List A)
    (step : A → Cache Summary → Result Summary Summary)
    (requests : A → Cache Summary → Nat) (cache : Cache Summary) : Nat :=
  match xs with
  | [] => 0
  | x :: rest => requests x cache +
      sequenceRequests rest step requests (step x cache).cache

/-- One lookup on entry; a miss requests each physical outgoing edge in
order. Cache hits issue no descendant requests. -/
def demandRequests (graph : Graph Label) (combine : Label → List Summary → Summary)
    (root : Nat) (cache : Cache Summary) : Nat :=
  match cache root with
  | some _ => 1
  | none => 1 + sequenceRequests (graph.children root)
      (fun child current => demand graph combine child.val current)
      (fun child current => demandRequests graph combine child.val current) cache
termination_by root

/-- Ordered duplicate edges count separately even when their target is shared. -/
def edgeCount (graph : Graph Label) (nodes : List Nat) : Nat :=
  (nodes.map fun node => (graph.children node).length).sum

@[simp] theorem edgeCount_append (graph : Graph Label) (first second : List Nat) :
    edgeCount graph (first ++ second) = edgeCount graph first + edgeCount graph second := by
  simp [edgeCount, List.map_append, List.sum_append]

theorem sequenceRequests_eq {A : Type w} (graph : Graph Label)
    (xs : List A) (step : A → Cache Summary → Result Summary Summary)
    (requests : A → Cache Summary → Nat)
    (each : ∀ item ∈ xs, ∀ cache, requests item cache =
      1 + edgeCount graph (step item cache).computed) (cache : Cache Summary) :
    sequenceRequests xs step requests cache =
      xs.length + edgeCount graph (sequence xs step cache).computed := by
  induction xs generalizing cache with
  | nil => simp [sequenceRequests, sequence, edgeCount]
  | cons first rest ih =>
      simp only [sequenceRequests, sequence, List.length_cons, edgeCount_append]
      rw [each first (by simp), ih (fun item member => each item (by simp [member]))]
      omega

/-- The operational request count equals one root lookup plus exactly one
lookup for each outgoing edge of a newly computed node. -/
theorem demandRequests_eq (graph : Graph Label)
    (combine : Label → List Summary → Summary) (root : Nat) (cache : Cache Summary) :
    demandRequests graph combine root cache =
      1 + edgeCount graph (demand graph combine root cache).computed := by
  induction root using Nat.strong_induction_on generalizing cache with
  | h root ih =>
      rw [demandRequests, demand]
      cases present : cache root with
      | some value => simp [edgeCount]
      | none =>
          simp only
          rw [sequenceRequests_eq graph _ _ _ (fun child _ current =>
            ih child.val child.isLt current), edgeCount_append]
          simp [edgeCount, Nat.add_comm]

/-- Distinct computed nodes contribute all their physical child slots once.
Cache-table operations themselves are not charged as constant-time here. -/
theorem demandRequests_le_uncached_edges (graph : Graph Label)
    (combine : Label → List Summary → Summary) (root : Nat) (cache : Cache Summary)
    (sound : Sound graph combine cache) :
    demandRequests graph combine root cache ≤
      1 + ∑ node ∈ (reachable graph root).filter (fun node => (cache node).isNone),
        (graph.children node).length := by
  rw [demandRequests_eq]
  apply Nat.add_le_add_left
  unfold edgeCount
  have valid := demand_valid graph combine root cache sound
  rw [← List.sum_toFinset _ valid.nodup]
  apply Finset.sum_le_sum_of_subset
  intro node member
  have computed : node ∈ (demand graph combine root cache).computed := by
    simpa using member
  exact Finset.mem_filter.mpr
    ⟨demand_computed_reachable graph combine root cache node computed,
      by simp [valid.fresh node computed]⟩

/-- Ordered roots share one fixed interpretation and cache. -/
theorem sequence_demand_valid (graph : Graph Label)
    (combine : Label → List Summary → Summary) (roots : List Nat) (cache : Cache Summary)
    (sound : Sound graph combine cache) :
    Valid graph combine cache (sequence roots (demand graph combine) cache)
      (roots.map (eager graph combine)) (roots.sum + 1) := by
  apply sequence_valid
  · intro root member current valid
    have one := demand_valid graph combine root current valid
    refine { one with bounded := ?_ }
    intro node computed
    exact (one.bounded node computed).trans_le
      (Nat.add_le_add_right (List.le_sum_of_mem member) 1)
  · exact sound

/-- Multiple roots pay for their output occurrences and the edges of distinct
reachable nodes. Payload construction and memo-table cost remain separate. -/
theorem sequenceRequests_le_reachable_edges (graph : Graph Label)
    (combine : Label → List Summary → Summary) (roots : List Nat) (cache : Cache Summary)
    (sound : Sound graph combine cache) :
    sequenceRequests roots (demand graph combine) (demandRequests graph combine) cache ≤
      roots.length + ∑ node ∈ roots.toFinset.biUnion (reachable graph),
        (graph.children node).length := by
  rw [sequenceRequests_eq graph _ _ _
    (fun root _ current => demandRequests_eq graph combine root current)]
  apply Nat.add_le_add_left
  unfold edgeCount
  rw [← List.sum_toFinset _ (sequence_demand_valid graph combine roots cache sound).nodup]
  apply Finset.sum_le_sum_of_subset
  intro node member
  have computed : node ∈ (sequence roots (demand graph combine) cache).computed := by
    simpa using member
  obtain ⟨root, root_mem, current, reached⟩ :=
    sequence_computed_source _ _ _ node computed
  exact Finset.mem_biUnion.mpr ⟨root, by simpa using root_mem,
    demand_computed_reachable graph combine root current node reached⟩

/-- Dependency testing uses actual edges even when all caches are empty. -/
def affected (g : Graph Label) (changed : Nat → Bool) (i : Nat) : Bool :=
  changed i || (g.children i).any fun child => affected g changed child.val
termination_by i

def invalidate (g : Graph Label) (changed : Nat → Bool) (cache : Cache Summary) :
    Cache Summary :=
  fun i => if affected g changed i then none else cache i

/-- A revision marks every changed local label and child list. Labels include
all algebra inputs, such as allocation arena, older generation, head adjustment,
or a mutable leaf's revision-dependent summary. -/
structure Revision (before after : Graph Label) (changed : Nat → Bool) : Prop where
  labels : ∀ i, changed i = false → before.label i = after.label i
  edges : ∀ i, changed i = false → before.children i = after.children i

theorem unaffected_eager (before after : Graph Label)
    (combine : Label → List Summary → Summary) (changed : Nat → Bool)
    (revision : Revision before after changed) (i : Nat)
    (unaffected : affected before changed i = false) :
    eager before combine i = eager after combine i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      rw [affected] at unaffected
      have unchanged : changed i = false := (Bool.or_eq_false_iff.mp unaffected).1
      have children : ∀ child ∈ before.children i,
          affected before changed child.val = false := by
        have := (Bool.or_eq_false_iff.mp unaffected).2
        simpa using this
      rw [eager, eager, ← revision.labels i unchanged, ← revision.edges i unchanged]
      congr 1
      apply List.map_congr_left
      intro child hchild
      exact ih child.val child.isLt (children child hchild)

/-- Invalidation derived from the old dependency graph makes every retained
cache entry sound in the new graph. Edges added by the revision are safe:
their changed parent is itself invalidated, as are its old dependents. -/
theorem invalidate_sound (before after : Graph Label)
    (combine : Label → List Summary → Summary) (changed : Nat → Bool)
    (revision : Revision before after changed) (cache : Cache Summary)
    (sound : Sound before combine cache) :
    Sound after combine (invalidate before changed cache) := by
  intro i value present
  unfold invalidate at present
  split at present
  · cases present
  · rename_i unaffected
    have unaffected' : affected before changed i = false := by simpa using unaffected
    exact (sound i value present).trans
      (unaffected_eager before after combine changed revision i unaffected')

theorem unaffected_cache_retained (g : Graph Label) (changed : Nat → Bool)
    (cache : Cache Summary) (i : Nat) (unaffected : affected g changed i = false) :
    invalidate g changed cache i = cache i := by simp [invalidate, unaffected]

theorem changed_cache_removed (g : Graph Label) (changed : Nat → Bool)
    (cache : Cache Summary) (i : Nat) (changedHere : changed i = true) :
    invalidate g changed cache i = none := by
  have hit : affected g changed i = true := by
    rw [affected, changedHere]
    rfl
  simp [invalidate, hit]

theorem observed_demand_exact {Observation : Type w} (g : Graph Label)
    (combine : Label → List Summary → Summary) (observe : Summary → Observation)
    (i : Nat) (cache : Cache Summary) (sound : Sound g combine cache) :
    observe (demand g combine i cache).value = observe (eager g combine i) := by
  rw [demand_exact g combine i cache sound]

/-- A conservative presence test. Unknown is not a negative answer. -/
def mayHave (property : Summary → Bool) : Option Summary → Bool
  | none => true
  | some summary => property summary

/-- A conservative permission test. Unknown does not grant an optimization
such as retaining a graph without copying or sharing across threads. -/
def certified (property : Summary → Bool) : Option Summary → Bool
  | none => false
  | some summary => property summary

theorem mayHave_false_sound (g : Graph Label)
    (combine : Label → List Summary → Summary) (cache : Cache Summary)
    (sound : Sound g combine cache) (property : Summary → Bool) (i : Nat)
    (absent : mayHave property (cache i) = false) :
    property (eager g combine i) = false := by
  cases present : cache i with
  | none => simp [present, mayHave] at absent
  | some value =>
      have value_eq := sound i value present
      simpa [present, mayHave, value_eq] using absent

theorem certified_true_sound (g : Graph Label)
    (combine : Label → List Summary → Summary) (cache : Cache Summary)
    (sound : Sound g combine cache) (property : Summary → Bool) (i : Nat)
    (permission : certified property (cache i) = true) :
    property (eager g combine i) = true := by
  cases present : cache i with
  | none => simp [present, certified] at permission
  | some value =>
      have value_eq := sound i value present
      simpa [present, certified, value_eq] using permission

theorem demand_after_revision_exact (before after : Graph Label)
    (combine : Label → List Summary → Summary) (changed : Nat → Bool)
    (revision : Revision before after changed) (cache : Cache Summary)
    (sound : Sound before combine cache) (i : Nat) :
    (demand after combine i (invalidate before changed cache)).value =
      eager after combine i :=
  demand_exact after combine i _
    (invalidate_sound before after combine changed revision cache sound)

namespace Located

open ConstructorSummary Cursor.TailSummary

variable {Bit : Type u}

/-- Completed resident leaves carry their own located summaries. Constructor
labels contain the parent's arena, older generation, and head adjustments. -/
inductive Descriptor (Bit : Type u)
  | resident (summary : ConstructorSummary.Summary Bit)
  | constructor (label : ConstructorSummary.Label Bit)

def combine : Descriptor Bit → List (ConstructorSummary.Summary Bit) →
    ConstructorSummary.Summary Bit
  | .resident summary, _ => summary
  | .constructor label, children => ConstructorSummary.combine label children

/-- The generic memoization proof applies to the allocation-sensitive algebra
without treating arena closure as a disjunction of unlocated child bits. -/
theorem demand_exact (g : Graph (Descriptor Bit)) (i : Nat)
    (cache : Cache (ConstructorSummary.Summary Bit)) (sound : Sound g combine cache) :
    (demand g combine i cache).value = eager g combine i :=
  DemandSummary.demand_exact g combine i cache sound

/-- A plain child's complete aggregate is neutral only when its allocation
also satisfies the parent-relative closure and generation tests. -/
def NeutralChild (label : ConstructorSummary.Label Bit)
    (child : ConstructorSummary.Summary Bit) : Prop :=
  { child.aggregate with generation := true } = Aggregate.unit ∧
    sameArena label.arena child.home = true ∧
    generationAdmits label child = true

theorem contribution_neutral {label : ConstructorSummary.Label Bit}
    {child : ConstructorSummary.Summary Bit} (neutral : NeutralChild label child) :
    contribution label child = Aggregate.unit := by
  rcases neutral with ⟨aggregate, closed, generation⟩
  have childClosed : child.aggregate.closed = true := congrArg Aggregate.closed aggregate
  calc
    contribution label child = { child.aggregate with generation := true } := by
      ext <;> simp [contribution, childClosed, closed, generation]
    _ = Aggregate.unit := aggregate

/-- If every child is independently certified neutral, construction uses the
precomputed empty aggregate. Syntactic constructor shape alone is insufficient. -/
theorem neutral_children_fast_path (label : ConstructorSummary.Label Bit)
    (children : List (ConstructorSummary.Summary Bit))
    (neutral : ∀ child ∈ children, NeutralChild label child) :
    ConstructorSummary.combine label children = finish label Aggregate.unit := by
  unfold ConstructorSummary.combine
  congr 1
  induction children with
  | nil => rfl
  | cons child children ih =>
      simp only [List.map_cons, Aggregate.fold, List.foldr_cons]
      rw [contribution_neutral (neutral child (by simp)), Aggregate.unit_merge]
      exact ih (fun other hother => neutral other (by simp [hother]))

end Located

namespace Controls

/-- Two parents share the same leaf twice. The result is a DAG, not a tree. -/
def diamond : Graph Nat where
  label := fun _ => 1
  children
    | 0 => []
    | 1 => [⟨0, by omega⟩, ⟨0, by omega⟩]
    | 2 => [⟨0, by omega⟩, ⟨0, by omega⟩]
    | n + 3 => [⟨1, by omega⟩, ⟨2, by omega⟩]

def addSummary (label : Nat) (children : List Nat) : Nat := label + children.sum

theorem shared_leaf_computed_once :
    (demand diamond addSummary 3 (fun _ => none)).computed = [0, 1, 2, 3] ∧
    (demand diamond addSummary 3 (fun _ => none)).value = 7 := by decide +kernel

theorem cached_ancestor_avoids_descendants :
    let cache : Cache Nat := fun i => if i = 3 then some 7 else none
    (demand diamond addSummary 3 cache).computed = [] ∧
    (demand diamond addSummary 3 cache).cache 0 = none := by decide +kernel

def changedLeaf : Graph Nat :=
  { diamond with label := fun i => if i = 0 then 2 else 1 }

theorem stale_cache_changes_answer :
    let cache := (demand diamond addSummary 3 (fun _ => none)).cache
    (demand changedLeaf addSummary 3 cache).value = 7 ∧
    eager changedLeaf addSummary 3 = 11 := by decide +kernel

theorem invalidating_leaf_repairs_dependents :
    let cache := (demand diamond addSummary 3 (fun _ => none)).cache
    let repaired := invalidate diamond (fun i => i == 0) cache
    (demand changedLeaf addSummary 3 repaired).value = 11 ∧
    (demand changedLeaf addSummary 3 repaired).computed = [0, 1, 2, 3] := by decide +kernel

theorem irrelevant_revision_retains_cached_root :
    let cache := (demand diamond addSummary 3 (fun _ => none)).cache
    let retained := invalidate diamond (fun i => i == 20) cache
    (demand diamond addSummary 3 retained).computed = [] := by decide +kernel

open ConstructorSummary Cursor.TailSummary

def locatedPair (parentArena childArena : Nat) : Graph (Located.Descriptor Unit) where
  label i := if i = 0 then
    .resident (ConstructorSummary.Controls.leaf childArena)
    else .constructor (ConstructorSummary.Controls.plain parentArena)
  children
    | 0 => []
    | _ + 1 => [⟨0, by omega⟩]

theorem moving_parent_invalidates_closure :
    let old := locatedPair 1 1
    let moved := locatedPair 2 1
    let cache := (demand old Located.combine 1 (fun _ => none)).cache
    (demand moved Located.combine 1 cache).value.aggregate.closed = true ∧
    (eager moved Located.combine 1).aggregate.closed = false ∧
    (demand moved Located.combine 1
      (invalidate old (fun i => i == 1) cache)).value.aggregate.closed = false := by decide +kernel

theorem moving_child_invalidates_parent :
    let old := locatedPair 1 1
    let moved := locatedPair 1 2
    let cache := (demand old Located.combine 1 (fun _ => none)).cache
    (demand moved Located.combine 1 cache).value.aggregate.closed = true ∧
    (demand moved Located.combine 1
      (invalidate old (fun i => i == 0) cache)).value.aggregate.closed = false := by decide +kernel

/-- A data-shaped constructor may still contain a registry reference or other
inherited escape property. The head being ordinary does not certify the child. -/
theorem plain_constructor_can_contain_escape :
    let escaping : ConstructorSummary.Summary Unit := ⟨.arena 1,
      { Aggregate.unit with inherited := fun _ => true }⟩
    (ConstructorSummary.combine (ConstructorSummary.Controls.plain 1)
      [escaping]).aggregate.inherited () = true := by decide

/-- An ordinary scalar's stored generation bit is false; same-arena closure
still makes its parent-relative contribution neutral. -/
theorem closed_scalar_is_neutral :
    let scalar : ConstructorSummary.Summary Unit := ⟨.arena 1,
      { Aggregate.unit with generation := false }⟩
    Located.NeutralChild (ConstructorSummary.Controls.plain 1) scalar := by
  simp [Located.NeutralChild, ConstructorSummary.Controls.plain, sameArena,
    generationAdmits, Aggregate.unit]

/-- A zeroed pending summary would hide a real variable. An exact absence
query must demand the metadata or conservatively report possible presence. -/
theorem absent_cache_does_not_mean_absent_variable :
    let vSummary : ConstructorSummary.Summary Unit := ⟨.arena 1,
      { Aggregate.unit with vars := .one 7 }⟩
    let node : Graph (Located.Descriptor Unit) :=
      { label := fun _ => .resident vSummary, children := fun _ => [] }
    (none : Option (ConstructorSummary.Summary Unit)).isNone = true ∧
    (demand node Located.combine 0 (fun _ => none)).value.aggregate.vars = .one 7 := by decide +kernel

/-- Collector reachability includes children of uncached nodes. Cache absence
cannot justify treating a constructor as a leaf during tracing. -/
theorem uncached_node_has_live_edges :
    (none : Option Nat).isNone = true ∧ 0 ∈ reachable diamond 3 := by decide +kernel

/-- Sharing avoids duplicate construction, but each duplicate edge still
issues a request. A count of four nodes alone would omit three lookups. -/
theorem shared_leaf_requests_include_duplicate_edges :
    demandRequests Controls.diamond Controls.addSummary 3 (fun _ => none) = 7 ∧
    (demand Controls.diamond Controls.addSummary 3 (fun _ => none)).computed.length = 4 := by
  decide +kernel

theorem cached_root_one_request :
    demandRequests Controls.diamond Controls.addSummary 3
      (demand Controls.diamond Controls.addSummary 3 (fun _ => none)).cache = 1 := by
  rw [demandRequests, demand_stores]

end Controls

end Mettapedia.Machines.DemandSummary
