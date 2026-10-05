import Mettapedia.Machines.ReadOnlyQuery
import Mettapedia.Machines.OrderedDependencyIds
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic

/-!
# Finite ordered dependency stores

Each member owns an ordered occurrence list. Its query reads that list followed
by the own lists of its dependency identities, not those dependencies' views.
An explicit reverse index supports notifications. Content updates notify the
owner and its direct readers; dependency-list updates affect only that member's
view. These operations are executable and maintain the reverse-index invariant.

This is a generic store algorithm, independent of any concrete evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedDependencyStore

universe u

structure Member (Entry : Type u) (size : Nat) where
  own : List Entry
  deps : List (Fin size)
  generation : Nat := 0
  revision : Nat := 0
  prefixEpoch : Nat := 0

structure Store (Entry : Type u) (size : Nat) where
  identity : Nat
  members : Fin size → Member Entry size
  observers : Fin size → Finset (Fin size)
  epoch : Nat := 0

variable {Entry : Type u} {size : Nat}

def ObserverInvariant (s : Store Entry size) : Prop :=
  ∀ source reader, reader ∈ s.observers source ↔
    source ∈ (s.members reader).deps

def DistinctDependencies (s : Store Entry size) : Prop :=
  ∀ reader, (s.members reader).deps.Nodup

def initial (identity : Nat) (own : Fin size → List Entry) : Store Entry size :=
  ⟨identity, fun source => ⟨own source, [], 0, 0, 0⟩, fun _ => ∅, 0⟩

theorem initial_observers (identity : Nat) (own : Fin size → List Entry) :
    ObserverInvariant (initial identity own) := by
  simp [ObserverInvariant, initial]

theorem initial_distinct (identity : Nat) (own : Fin size → List Entry) :
    DistinctDependencies (initial identity own) := by
  simp [DistinctDependencies, initial]

/-- Independent declarative ordered observation. -/
def view (s : Store Entry size) (reader : Fin size) : List Entry :=
  (s.members reader).own ++
    (s.members reader).deps.flatMap fun source => (s.members source).own

/-- Query loop accumulating one source segment at a time. -/
def collect (s : Store Entry size) : List (Fin size) → List Entry → List Entry
  | [], accumulated => accumulated
  | source :: rest, accumulated =>
      collect s rest (accumulated ++ (s.members source).own)

theorem collect_eq (s : Store Entry size) (sources : List (Fin size))
    (accumulated : List Entry) :
    collect s sources accumulated =
      accumulated ++ sources.flatMap (fun source => (s.members source).own) := by
  induction sources generalizing accumulated with
  | nil => simp [collect]
  | cons source rest ih => simp [collect, ih, List.append_assoc]

def query (s : Store Entry size) (reader : Fin size) : List Entry :=
  collect s (s.members reader).deps (s.members reader).own

theorem query_eq_view (s : Store Entry size) (reader : Fin size) :
    query s reader = view s reader :=
  collect_eq s _ _

def contentUpdate (s : Store Entry size) (source : Fin size)
    (contents : List Entry) (rewrites : Bool) : Store Entry size :=
  { s with
    members := fun reader =>
      let old := s.members reader
      { old with
        own := if reader = source then contents else old.own
        revision := if reader = source ∨ reader ∈ s.observers source
          then old.revision + 1 else old.revision
        prefixEpoch := if reader = source ∧ rewrites = true
          then old.prefixEpoch + 1 else old.prefixEpoch }
    epoch := s.epoch + 1 }

def appendOwn (s : Store Entry size) (source : Fin size)
    (suffix : List Entry) : Store Entry size :=
  contentUpdate s source ((s.members source).own ++ suffix) false

def replaceOwn (s : Store Entry size) (source : Fin size)
    (contents : List Entry) : Store Entry size :=
  contentUpdate s source contents true

theorem contentUpdate_observers (s : Store Entry size)
    (h : ObserverInvariant s) (source : Fin size)
    (contents : List Entry) (rewrites : Bool) :
    ObserverInvariant (contentUpdate s source contents rewrites) := by
  simpa [ObserverInvariant, contentUpdate] using h

theorem contentUpdate_distinct (s : Store Entry size)
    (h : DistinctDependencies s) (source : Fin size)
    (contents : List Entry) (rewrites : Bool) :
    DistinctDependencies (contentUpdate s source contents rewrites) := by
  simpa [DistinctDependencies, contentUpdate] using h

@[simp] theorem contentUpdate_own (s : Store Entry size) (source : Fin size)
    (contents : List Entry) (rewrites : Bool) :
    ((contentUpdate s source contents rewrites).members source).own = contents := by
  simp [contentUpdate]

theorem contentUpdate_own_other (s : Store Entry size) {source reader : Fin size}
    (different : reader ≠ source) (contents : List Entry) (rewrites : Bool) :
    ((contentUpdate s source contents rewrites).members reader).own =
      (s.members reader).own := by
  simp [contentUpdate, different]

theorem contentUpdate_notifies (s : Store Entry size) (h : ObserverInvariant s)
    {source reader : Fin size} (reads : source ∈ (s.members reader).deps)
    (contents : List Entry) (rewrites : Bool) :
    ((contentUpdate s source contents rewrites).members reader).revision =
      (s.members reader).revision + 1 := by
  simp [contentUpdate, (h source reader).mpr reads]

theorem contentUpdate_unrelated (s : Store Entry size)
    {source reader : Fin size} (different : reader ≠ source)
    (unread : source ∉ (s.members reader).deps)
    (contents : List Entry) (rewrites : Bool) :
    view (contentUpdate s source contents rewrites) reader = view s reader := by
  have own := contentUpdate_own_other s different contents rewrites
  simp only [view, contentUpdate] at own ⊢
  rw [own]
  congr 1
  apply List.flatMap_congr
  intro member included
  have notSource : member ≠ source := by
    intro equality
    subst member
    exact unread included
  simp [notSource]

/-- Update one member's topology and the reverse index together. Imported
members' own dependency changes do not alter older importers' flattened lists. -/
def setDependencies (s : Store Entry size) (reader : Fin size)
    (deps : List (Fin size)) : Store Entry size :=
  if deps = (s.members reader).deps then s else
  { s with
    members := Function.update s.members reader
      { s.members reader with deps := deps, revision := (s.members reader).revision + 1 }
    observers := fun source => if source ∈ deps
      then insert reader (s.observers source)
      else (s.observers source).erase reader
    epoch := s.epoch + 1 }

theorem setDependencies_observers (s : Store Entry size)
    (h : ObserverInvariant s) (reader : Fin size) (deps : List (Fin size)) :
    ObserverInvariant (setDependencies s reader deps) := by
  unfold setDependencies
  split
  · exact h
  · intro source observer
    by_cases same : observer = reader
    · subst observer
      by_cases present : source ∈ deps <;> simp [present]
    · by_cases present : source ∈ deps <;>
        simpa [present, same, Function.update_of_ne] using h source observer

theorem setDependencies_distinct (s : Store Entry size)
    (h : DistinctDependencies s) (reader : Fin size)
    (deps : List (Fin size)) (distinct : deps.Nodup) :
    DistinctDependencies (setDependencies s reader deps) := by
  unfold setDependencies
  split
  · exact h
  · intro member
    by_cases same : member = reader
    · subst member
      simpa using distinct
    · simpa [Function.update_of_ne same] using h member

def link (s : Store Entry size) (reader source : Fin size) : Store Entry size :=
  if source ∈ (s.members reader).deps then s else
    setDependencies s reader ((s.members reader).deps ++ [source])

theorem link_observers (s : Store Entry size) (h : ObserverInvariant s)
    (reader source : Fin size) : ObserverInvariant (link s reader source) := by
  unfold link
  split
  · exact h
  · exact setDependencies_observers s h reader _

theorem link_distinct (s : Store Entry size) (h : DistinctDependencies s)
    (reader source : Fin size) : DistinctDependencies (link s reader source) := by
  unfold link
  split
  · exact h
  · rename_i absent
    apply setDependencies_distinct s h reader
    simp only [List.nodup_append, h reader, List.nodup_cons, List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, and_self, true_and, List.mem_singleton]
    intro member included other equality same
    subst other
    subst member
    exact absent included

@[simp] theorem setDependencies_deps (s : Store Entry size) (reader : Fin size)
    (deps : List (Fin size)) :
    ((setDependencies s reader deps).members reader).deps = deps := by
  unfold setDependencies
  split
  · rename_i same
    exact same.symm
  · simp

theorem link_idempotent (s : Store Entry size) (reader source : Fin size) :
    link (link s reader source) reader source = link s reader source := by
  by_cases present : source ∈ (s.members reader).deps
  · simp [link, present]
  · have included : source ∈ ((link s reader source).members reader).deps := by
      simp [link, present, setDependencies_deps]
    rw [link, if_pos included]

def unlink (s : Store Entry size) (reader source : Fin size) : Store Entry size :=
  setDependencies s reader ((s.members reader).deps.filter fun member => member ≠ source)

theorem unlink_observers (s : Store Entry size) (h : ObserverInvariant s)
    (reader source : Fin size) : ObserverInvariant (unlink s reader source) :=
  setDependencies_observers s h reader _

theorem unlink_distinct (s : Store Entry size) (h : DistinctDependencies s)
    (reader source : Fin size) : DistinctDependencies (unlink s reader source) :=
  setDependencies_distinct s h reader _ ((h reader).filter _)

/-- Capture a source's dependency identities only on its first import. Later
imports of that same source do not refresh this flattened identity list. A
reader is never added as its own imported dependency. -/
def moduleDependencies (s : Store Entry size) (reader source : Fin size) : List (Fin size) :=
  if reader = source ∨ source ∈ (s.members reader).deps then (s.members reader).deps else
    OrderedDependencyIds.insertDeps (s.members reader).deps
      ((source :: (s.members source).deps).filter fun member => member ≠ reader)

def importModule (s : Store Entry size) (reader source : Fin size) : Store Entry size :=
  setDependencies s reader (moduleDependencies s reader source)

theorem moduleDependencies_distinct (s : Store Entry size) (h : DistinctDependencies s)
    (reader source : Fin size) : (moduleDependencies s reader source).Nodup := by
  unfold moduleDependencies
  split
  · exact h reader
  · exact OrderedDependencyIds.nodup_insertDeps _ (h reader)

theorem moduleDependencies_prefix (s : Store Entry size) (reader source : Fin size) :
    (s.members reader).deps <+: moduleDependencies s reader source := by
  unfold moduleDependencies
  split
  · exact List.prefix_refl _
  · exact OrderedDependencyIds.prefix_insertDeps _ _

theorem importModule_observers (s : Store Entry size) (h : ObserverInvariant s)
    (reader source : Fin size) : ObserverInvariant (importModule s reader source) :=
  setDependencies_observers s h reader _

theorem importModule_distinct (s : Store Entry size) (h : DistinctDependencies s)
    (reader source : Fin size) : DistinctDependencies (importModule s reader source) :=
  setDependencies_distinct s h reader _ (moduleDependencies_distinct s h reader source)

theorem importModule_of_mem (s : Store Entry size) (reader source : Fin size)
    (present : source ∈ (s.members reader).deps) : importModule s reader source = s := by
  simp [importModule, moduleDependencies, present, setDependencies]

@[simp] theorem importModule_self (s : Store Entry size) (reader : Fin size) :
    importModule s reader reader = s := by
  simp [importModule, moduleDependencies, setDependencies]

theorem importModule_source_present (s : Store Entry size) {reader source : Fin size}
    (different : reader ≠ source) :
    source ∈ ((importModule s reader source).members reader).deps := by
  simp only [importModule, setDependencies_deps, moduleDependencies]
  split
  · rename_i already
    exact already.resolve_left different
  · apply OrderedDependencyIds.mem_insertDeps.mpr
    right
    simp [Ne.symm different]

theorem importModule_idempotent (s : Store Entry size) (reader source : Fin size) :
    importModule (importModule s reader source) reader source = importModule s reader source := by
  by_cases same : reader = source
  · subst source
    simp
  · exact importModule_of_mem _ _ _ (importModule_source_present s same)

theorem setDependencies_unrelated (s : Store Entry size)
    {changed reader : Fin size} (different : reader ≠ changed)
    (deps : List (Fin size)) :
    view (setDependencies s changed deps) reader = view s reader := by
  unfold setDependencies
  split
  · rfl
  · simp only [view, Function.update_of_ne different]
    congr 1
    apply List.flatMap_congr
    intro member included
    by_cases same : member = changed
    · subst member
      simp
    · simp [Function.update_of_ne same]

theorem contentUpdate_revision_mono (s : Store Entry size)
    (source reader : Fin size) (contents : List Entry) (rewrites : Bool) :
    (s.members reader).revision ≤
      ((contentUpdate s source contents rewrites).members reader).revision := by
  simp only [contentUpdate]
  split <;> omega

theorem contentUpdate_view_of_revision_eq (s : Store Entry size)
    (h : ObserverInvariant s) (source reader : Fin size)
    (contents : List Entry) (rewrites : Bool)
    (same : ((contentUpdate s source contents rewrites).members reader).revision =
      (s.members reader).revision) :
    view (contentUpdate s source contents rewrites) reader = view s reader := by
  have different : reader ≠ source := by
    intro equality
    simp [contentUpdate, equality] at same
  have unread : source ∉ (s.members reader).deps := by
    intro reads
    have notified := contentUpdate_notifies s h reads contents rewrites
    omega
  exact contentUpdate_unrelated s different unread contents rewrites

theorem setDependencies_revision_mono (s : Store Entry size)
    (changed reader : Fin size) (deps : List (Fin size)) :
    (s.members reader).revision ≤
      ((setDependencies s changed deps).members reader).revision := by
  unfold setDependencies
  split
  · exact Nat.le_refl _
  · by_cases same : reader = changed
    · subst reader
      simp
    · simp [Function.update_of_ne same]

theorem setDependencies_view_of_revision_eq (s : Store Entry size)
    (changed reader : Fin size) (deps : List (Fin size))
    (same : ((setDependencies s changed deps).members reader).revision =
      (s.members reader).revision) :
    view (setDependencies s changed deps) reader = view s reader := by
  by_cases unchanged : deps = (s.members changed).deps
  · simp [setDependencies, unchanged]
  · have different : reader ≠ changed := by
      intro equality
      subst reader
      simp [setDependencies, unchanged] at same
    exact setDependencies_unrelated s different deps

/-- End a member lifetime, unlink both directions, and advance its generation.
A later occupant of the same finite slot cannot revive the old certificates. -/
def retire (s : Store Entry size) (source : Fin size) : Store Entry size :=
  { s with
    members := fun reader =>
      let old := s.members reader
      { old with
        own := if reader = source then [] else old.own
        deps := if reader = source then [] else old.deps.filter fun member => member ≠ source
        generation := if reader = source then old.generation + 1 else old.generation
        revision := if reader = source ∨ reader ∈ s.observers source
          then old.revision + 1 else old.revision
        prefixEpoch := if reader = source then old.prefixEpoch + 1 else old.prefixEpoch }
    observers := fun member => if member = source then ∅ else (s.observers member).erase source
    epoch := s.epoch + 1 }

theorem retire_observers (s : Store Entry size) (h : ObserverInvariant s)
    (source : Fin size) : ObserverInvariant (retire s source) := by
  intro member reader
  by_cases sameMember : member = source
  · subst member
    by_cases sameReader : reader = source <;> simp [retire, sameReader]
  · by_cases sameReader : reader = source
    · subst reader
      simp [retire, sameMember]
    · simpa [retire, sameMember, sameReader] using h member reader

theorem retire_distinct (s : Store Entry size) (h : DistinctDependencies s)
    (source : Fin size) : DistinctDependencies (retire s source) := by
  intro reader
  by_cases same : reader = source
  · simp [retire, same]
  · simpa [retire, same] using (h reader).filter (fun member => member ≠ source)

theorem retire_unrelated (s : Store Entry size) {source reader : Fin size}
    (different : reader ≠ source) (unread : source ∉ (s.members reader).deps) :
    view (retire s source) reader = view s reader := by
  have dependencies : ((s.members reader).deps.filter fun member => member ≠ source) =
      (s.members reader).deps := by
    apply List.filter_eq_self.mpr
    intro member included
    have distinct : member ≠ source := by
      intro same
      subst member
      exact unread included
    simp [distinct]
  simp only [view, retire, different, ↓reduceIte, dependencies]
  congr 1
  apply List.flatMap_congr
  intro member included
  have distinct : member ≠ source := by
    intro same
    subst member
    exact unread included
  simp [distinct]

theorem retire_revision_mono (s : Store Entry size) (source reader : Fin size) :
    (s.members reader).revision ≤ ((retire s source).members reader).revision := by
  simp only [retire]
  split <;> omega

theorem retire_view_of_revision_eq (s : Store Entry size) (h : ObserverInvariant s)
    (source reader : Fin size)
    (same : ((retire s source).members reader).revision = (s.members reader).revision) :
    view (retire s source) reader = view s reader := by
  have different : reader ≠ source := by
    intro equality
    simp [retire, equality] at same
  have unread : source ∉ (s.members reader).deps := by
    intro reads
    have observer := (h source reader).mpr reads
    simp [retire, observer] at same
  exact retire_unrelated s different unread

/-- Source segments remain distinguished before any concatenation or overlay
masking. Equal flattened answers alone would not establish this observation. -/
def segments (s : Store Entry size) (reader : Fin size) :
    List Entry × List (Fin size × List Entry) :=
  ((s.members reader).own,
    (s.members reader).deps.map fun source => (source, (s.members source).own))

theorem contentUpdate_segments_unrelated (s : Store Entry size)
    {writer reader : Fin size} (different : reader ≠ writer)
    (unread : writer ∉ (s.members reader).deps) (contents : List Entry) (rewrites : Bool) :
    segments (contentUpdate s writer contents rewrites) reader = segments s reader := by
  simp only [segments, contentUpdate, different, ↓reduceIte]
  congr 1
  apply List.map_congr_left
  intro source included
  have notWriter : source ≠ writer := by
    intro equal
    subst source
    exact unread included
  simp [notWriter]

theorem setDependencies_segments_unrelated (s : Store Entry size)
    {changed reader : Fin size} (different : reader ≠ changed) (deps : List (Fin size)) :
    segments (setDependencies s changed deps) reader = segments s reader := by
  unfold setDependencies
  split
  · rfl
  · simp only [segments, Function.update_of_ne different]
    congr 1
    apply List.map_congr_left
    intro source included
    by_cases same : source = changed
    · subst source
      simp
    · simp [Function.update_of_ne same]

theorem retire_segments_unrelated (s : Store Entry size)
    {source reader : Fin size} (different : reader ≠ source)
    (unread : source ∉ (s.members reader).deps) :
    segments (retire s source) reader = segments s reader := by
  have dependencies : ((s.members reader).deps.filter fun member => member ≠ source) =
      (s.members reader).deps := by
    apply List.filter_eq_self.mpr
    intro member included
    have distinct : member ≠ source := by
      intro same
      subst member
      exact unread included
    simp [distinct]
  simp only [segments, retire, different, ↓reduceIte, dependencies]
  congr 1
  apply List.map_congr_left
  intro member included
  have distinct : member ≠ source := by
    intro same
    subst member
    exact unread included
  simp [distinct]

inductive Action (Entry : Type u) (size : Nat) where
  | append (source : Fin size) (suffix : List Entry)
  | replace (source : Fin size) (contents : List Entry)
  | link (reader source : Fin size)
  | unlink (reader source : Fin size)
  | retire (source : Fin size)
  | importModule (reader source : Fin size)

def step (s : Store Entry size) : Action Entry size → Store Entry size
  | .append source suffix => appendOwn s source suffix
  | .replace source contents => replaceOwn s source contents
  | .link reader source => link s reader source
  | .unlink reader source => unlink s reader source
  | .retire source => retire s source
  | .importModule reader source => importModule s reader source

theorem step_observers (s : Store Entry size) (h : ObserverInvariant s)
    (action : Action Entry size) : ObserverInvariant (step s action) := by
  cases action with
  | append source suffix => exact contentUpdate_observers s h source _ false
  | replace source contents => exact contentUpdate_observers s h source contents true
  | link reader source => exact link_observers s h reader source
  | unlink reader source => exact unlink_observers s h reader source
  | retire source => exact retire_observers s h source
  | importModule reader source => exact importModule_observers s h reader source

theorem step_distinct (s : Store Entry size) (h : DistinctDependencies s)
    (action : Action Entry size) : DistinctDependencies (step s action) := by
  cases action with
  | append source suffix => exact contentUpdate_distinct s h source _ false
  | replace source contents => exact contentUpdate_distinct s h source contents true
  | link reader source => exact link_distinct s h reader source
  | unlink reader source => exact unlink_distinct s h reader source
  | retire source => exact retire_distinct s h source
  | importModule reader source => exact importModule_distinct s h reader source

theorem step_revision_mono (s : Store Entry size) (action : Action Entry size)
    (reader : Fin size) :
    (s.members reader).revision ≤ ((step s action).members reader).revision := by
  cases action with
  | append source suffix => exact contentUpdate_revision_mono s source reader _ false
  | replace source contents => exact contentUpdate_revision_mono s source reader contents true
  | link importer source =>
      simp only [step, link]
      split
      · exact Nat.le_refl _
      · exact setDependencies_revision_mono s importer reader _
  | unlink importer source => exact setDependencies_revision_mono s importer reader _
  | retire source => exact retire_revision_mono s source reader
  | importModule importer source => exact setDependencies_revision_mono s importer reader _

theorem step_view_of_revision_eq (s : Store Entry size) (h : ObserverInvariant s)
    (action : Action Entry size) (reader : Fin size)
    (same : ((step s action).members reader).revision = (s.members reader).revision) :
    view (step s action) reader = view s reader := by
  cases action with
  | append source suffix => exact contentUpdate_view_of_revision_eq s h source reader _ false same
  | replace source contents => exact contentUpdate_view_of_revision_eq s h source reader contents true same
  | link importer source =>
      simp only [step, link] at same ⊢
      split at same
      · simp_all
      · rename_i absent
        simp only [absent, ↓reduceIte]
        exact setDependencies_view_of_revision_eq s importer reader _ same
  | unlink importer source => exact setDependencies_view_of_revision_eq s importer reader _ same
  | retire source => exact retire_view_of_revision_eq s h source reader same
  | importModule importer source => exact setDependencies_view_of_revision_eq s importer reader _ same

theorem step_segments_of_revision_eq (s : Store Entry size) (h : ObserverInvariant s)
    (action : Action Entry size) (reader : Fin size)
    (same : ((step s action).members reader).revision = (s.members reader).revision) :
    segments (step s action) reader = segments s reader := by
  have content (writer : Fin size) (contents : List Entry) (rewrites : Bool)
      (equal : ((contentUpdate s writer contents rewrites).members reader).revision =
        (s.members reader).revision) :
      segments (contentUpdate s writer contents rewrites) reader = segments s reader := by
    have different : reader ≠ writer := by
      intro identity
      simp [contentUpdate, identity] at equal
    have unread : writer ∉ (s.members reader).deps := by
      intro included
      have observer := (h writer reader).mpr included
      simp [contentUpdate, observer] at equal
    exact contentUpdate_segments_unrelated s different unread contents rewrites
  have topology (changed : Fin size) (deps : List (Fin size))
      (equal : ((setDependencies s changed deps).members reader).revision =
        (s.members reader).revision) :
      segments (setDependencies s changed deps) reader = segments s reader := by
    by_cases unchanged : deps = (s.members changed).deps
    · simp [setDependencies, unchanged]
    · have different : reader ≠ changed := by
        intro identity
        subst reader
        simp [setDependencies, unchanged] at equal
      exact setDependencies_segments_unrelated s different deps
  cases action with
  | append writer suffix => exact content writer _ false same
  | replace writer contents => exact content writer contents true same
  | link changed source =>
      simp only [step, link] at same ⊢
      split at same
      · simp_all
      · rename_i absent
        simp only [absent, ↓reduceIte]
        exact topology changed _ same
  | unlink changed source => exact topology changed _ same
  | importModule changed source => exact topology changed _ same
  | retire source =>
      have different : reader ≠ source := by
        intro identity
        simp [step, retire, identity] at same
      have unread : source ∉ (s.members reader).deps := by
        intro included
        have observer := (h source reader).mpr included
        simp [step, retire, observer] at same
      exact retire_segments_unrelated s different unread

def execute (s : Store Entry size) : List (Action Entry size) → Store Entry size
  | [] => s
  | action :: rest => execute (step s action) rest

theorem execute_observers (s : Store Entry size) (h : ObserverInvariant s)
    (actions : List (Action Entry size)) : ObserverInvariant (execute s actions) := by
  induction actions generalizing s with
  | nil => exact h
  | cons action rest ih => exact ih (step s action) (step_observers s h action)

theorem execute_revision_mono (s : Store Entry size)
    (actions : List (Action Entry size)) (reader : Fin size) :
    (s.members reader).revision ≤ ((execute s actions).members reader).revision := by
  induction actions generalizing s with
  | nil => exact Nat.le_refl _
  | cons action rest ih =>
      exact (step_revision_mono s action reader).trans (ih (step s action))

theorem execute_view_of_revision_eq (s : Store Entry size) (h : ObserverInvariant s)
    (actions : List (Action Entry size)) (reader : Fin size)
    (same : ((execute s actions).members reader).revision = (s.members reader).revision) :
    view (execute s actions) reader = view s reader := by
  induction actions generalizing s with
  | nil => rfl
  | cons action rest ih =>
      have first := step_revision_mono s action reader
      have later := execute_revision_mono (step s action) rest reader
      have unchanged : ((step s action).members reader).revision =
          (s.members reader).revision := by
        simp only [execute] at same
        omega
      have tail : ((execute (step s action) rest).members reader).revision =
          ((step s action).members reader).revision := by
        simpa [execute, unchanged] using same
      exact (ih (step s action) (step_observers s h action) tail).trans
        (step_view_of_revision_eq s h action reader unchanged)

theorem execute_segments_of_revision_eq (s : Store Entry size) (h : ObserverInvariant s)
    (actions : List (Action Entry size)) (reader : Fin size)
    (same : ((execute s actions).members reader).revision = (s.members reader).revision) :
    segments (execute s actions) reader = segments s reader := by
  induction actions generalizing s with
  | nil => rfl
  | cons action rest ih =>
      have first := step_revision_mono s action reader
      have later := execute_revision_mono (step s action) rest reader
      have unchanged : ((step s action).members reader).revision =
          (s.members reader).revision := by
        simp only [execute] at same
        omega
      have tail : ((execute (step s action) rest).members reader).revision =
          ((step s action).members reader).revision := by
        simpa [execute, unchanged] using same
      exact (ih (step s action) (step_observers s h action) tail).trans
        (step_segments_of_revision_eq s h action reader unchanged)

structure ReadStamp (size : Nat) where
  identity : Nat
  reader : Fin size
  generation : Nat
  revision : Nat
  deriving DecidableEq

def readStamp (s : Store Entry size) (reader : Fin size) : ReadStamp size :=
  ⟨s.identity, reader, (s.members reader).generation, (s.members reader).revision⟩

def checkRead (s : Store Entry size) (stamp : ReadStamp size) : Bool :=
  decide (stamp = readStamp s stamp.reader)

/-- Stamp validation is sound along the actual update algorithm, not between
arbitrary stores with coincidentally equal counters. Empty observations are
included because the certified value is the entire ordered list. -/
theorem validated_query (s : Store Entry size) (h : ObserverInvariant s)
    (actions : List (Action Entry size)) (reader : Fin size)
    (valid : checkRead (execute s actions) (readStamp s reader) = true) :
    query (execute s actions) reader = query s reader := by
  have stampEq : readStamp s reader = readStamp (execute s actions) reader :=
    of_decide_eq_true valid
  have revisionEq := congrArg ReadStamp.revision stampEq
  simp only [readStamp] at revisionEq
  simpa only [query_eq_view] using
    execute_view_of_revision_eq s h actions reader revisionEq.symm

structure PrefixStamp (size : Nat) where
  identity : Nat
  source : Fin size
  generation : Nat
  prefixEpoch : Nat
  ceiling : Nat
  deriving DecidableEq

def prefixStamp (s : Store Entry size) (source : Fin size) : PrefixStamp size :=
  ⟨s.identity, source, (s.members source).generation,
    (s.members source).prefixEpoch, (s.members source).own.length⟩

def checkPrefix (s : Store Entry size) (stamp : PrefixStamp size) : Bool :=
  decide (stamp.identity = s.identity ∧
    stamp.generation = (s.members stamp.source).generation ∧
    stamp.prefixEpoch = (s.members stamp.source).prefixEpoch ∧
    stamp.ceiling ≤ (s.members stamp.source).own.length)

/-- A source-local index is resolved at its source, under its own prefix
certificate. It is not an offset into the composed reader's storage. -/
def resolvePrefix (s : Store Entry size) (stamp : PrefixStamp size)
    (index : Nat) : Option Entry :=
  if checkPrefix s stamp && decide (index < stamp.ceiling)
    then (s.members stamp.source).own[index]? else none

theorem appendOwn_prefix_accepts (s : Store Entry size) (source : Fin size)
    (suffix : List Entry) :
    checkPrefix (appendOwn s source suffix) (prefixStamp s source) = true := by
  simp [checkPrefix, prefixStamp, appendOwn, contentUpdate]

theorem appendOwn_prefix_resolves (s : Store Entry size) (source : Fin size)
    (suffix : List Entry) (index : Nat)
    (bound : index < (s.members source).own.length) :
    resolvePrefix (appendOwn s source suffix) (prefixStamp s source) index =
      (s.members source).own[index]? := by
  simp [resolvePrefix, checkPrefix, prefixStamp, appendOwn, contentUpdate,
    bound, List.getElem?_append_left bound]

theorem replaceOwn_prefix_rejects (s : Store Entry size) (source : Fin size)
    (contents : List Entry) :
    checkPrefix (replaceOwn s source contents) (prefixStamp s source) = false := by
  simp [checkPrefix, prefixStamp, replaceOwn, contentUpdate]

theorem retire_prefix_rejects (s : Store Entry size) (source : Fin size) :
    checkPrefix (retire s source) (prefixStamp s source) = false := by
  simp [checkPrefix, prefixStamp, retire]

theorem retire_read_rejects (s : Store Entry size) (source : Fin size) :
    checkRead (retire s source) (readStamp s source) = false := by
  simp [checkRead, readStamp, retire, ReadStamp.mk.injEq]

theorem setDependencies_own (s : Store Entry size) (changed reader : Fin size)
    (deps : List (Fin size)) :
    ((setDependencies s changed deps).members reader).own = (s.members reader).own := by
  unfold setDependencies
  split
  · rfl
  · by_cases same : reader = changed
    · subst reader
      simp
    · simp [Function.update_of_ne same]

theorem setDependencies_prefixEpoch (s : Store Entry size) (changed reader : Fin size)
    (deps : List (Fin size)) :
    ((setDependencies s changed deps).members reader).prefixEpoch =
      (s.members reader).prefixEpoch := by
  unfold setDependencies
  split
  · rfl
  · by_cases same : reader = changed
    · subst reader
      simp
    · simp [Function.update_of_ne same]

theorem step_prefixEpoch_mono (s : Store Entry size) (action : Action Entry size)
    (source : Fin size) :
    (s.members source).prefixEpoch ≤ ((step s action).members source).prefixEpoch := by
  cases action with
  | append writer suffix => simp [step, appendOwn, contentUpdate]
  | replace writer contents => simp only [step, replaceOwn, contentUpdate]; split <;> omega
  | link reader dependency =>
      simp only [step, link]
      split
      · exact Nat.le_refl _
      · rw [setDependencies_prefixEpoch]
  | unlink reader dependency => simp [step, unlink, setDependencies_prefixEpoch]
  | retire retired => simp only [step, retire]; split <;> omega
  | importModule reader dependency => simp [step, importModule, setDependencies_prefixEpoch]

theorem step_own_prefix_of_epoch_eq (s : Store Entry size)
    (action : Action Entry size) (source : Fin size)
    (same : ((step s action).members source).prefixEpoch = (s.members source).prefixEpoch) :
    (s.members source).own <+: ((step s action).members source).own := by
  cases action with
  | append writer suffix =>
      by_cases writes : source = writer
      · subst source
        simp [step, appendOwn, contentUpdate, List.prefix_append]
      · simp [step, appendOwn, contentUpdate, writes]
  | replace writer contents =>
      have different : source ≠ writer := by
        intro equality
        subst source
        simp [step, replaceOwn, contentUpdate] at same
      simp [step, replaceOwn, contentUpdate, different]
  | link reader dependency =>
      simp only [step, link]
      split
      · exact List.prefix_refl _
      · rw [setDependencies_own]
  | unlink reader dependency => simp [step, unlink, setDependencies_own]
  | retire retired =>
      have different : source ≠ retired := by
        intro equality
        subst source
        simp [step, retire] at same
      simp [step, retire, different]
  | importModule reader dependency => simp [step, importModule, setDependencies_own]

theorem execute_prefixEpoch_mono (s : Store Entry size)
    (actions : List (Action Entry size)) (source : Fin size) :
    (s.members source).prefixEpoch ≤ ((execute s actions).members source).prefixEpoch := by
  induction actions generalizing s with
  | nil => exact Nat.le_refl _
  | cons action rest ih =>
      exact (step_prefixEpoch_mono s action source).trans (ih (step s action))

theorem execute_own_prefix_of_epoch_eq (s : Store Entry size)
    (actions : List (Action Entry size)) (source : Fin size)
    (same : ((execute s actions).members source).prefixEpoch =
      (s.members source).prefixEpoch) :
    (s.members source).own <+: ((execute s actions).members source).own := by
  induction actions generalizing s with
  | nil => exact List.prefix_refl _
  | cons action rest ih =>
      have first := step_prefixEpoch_mono s action source
      have later := execute_prefixEpoch_mono (step s action) rest source
      have unchanged : ((step s action).members source).prefixEpoch =
          (s.members source).prefixEpoch := by
        simp only [execute] at same
        omega
      have tail : ((execute (step s action) rest).members source).prefixEpoch =
          ((step s action).members source).prefixEpoch := by
        simpa [execute, unchanged] using same
      exact (step_own_prefix_of_epoch_eq s action source unchanged).trans
        (ih (step s action) tail)

/-- Prefix validation licenses old source occurrences, not an unchanged full
query or a stable offset in another reader's composed view. -/
theorem validated_prefix_occurrence (s : Store Entry size)
    (actions : List (Action Entry size)) (source : Fin size) (index : Nat)
    (valid : checkPrefix (execute s actions) (prefixStamp s source) = true)
    (bound : index < (s.members source).own.length) :
    resolvePrefix (execute s actions) (prefixStamp s source) index =
      (s.members source).own[index]? := by
  have checked := of_decide_eq_true valid
  have same : ((execute s actions).members source).prefixEpoch =
      (s.members source).prefixEpoch := checked.2.2.1.symm
  obtain ⟨suffix, unchanged⟩ := execute_own_prefix_of_epoch_eq s actions source same
  unfold resolvePrefix
  rw [valid]
  simp only [Bool.true_and, prefixStamp, bound, decide_true, if_true]
  rw [← unchanged, List.getElem?_append_left bound]

namespace Controls

def threeMembers : Store Nat 3 :=
  initial 900 fun source =>
    if source = 0 then [42] else if source = 2 then [7, 7] else []

def imported : Store Nat 3 := link threeMembers 0 2

theorem imported_observers : ObserverInvariant imported :=
  link_observers threeMembers (initial_observers _ _) 0 2

theorem imported_distinct : DistinctDependencies imported :=
  link_distinct threeMembers (initial_distinct _ _) 0 2

theorem ordered_duplicate_answers : query imported 0 = [42, 7, 7] := by
  decide

theorem append_updates_reader :
    query (appendOwn imported 2 [8]) 0 = [42, 7, 7, 8] ∧
    checkRead (appendOwn imported 2 [8]) (readStamp imported 0) = false := by
  decide

theorem unrelated_update_preserves_reader :
    checkRead (appendOwn imported 1 [8]) (readStamp imported 0) = true ∧
    query (appendOwn imported 1 [8]) 0 = [42, 7, 7] := by
  decide

theorem negative_query_insertion_expires :
    query imported 1 = [] ∧
    query (appendOwn imported 1 [8]) 1 = [8] ∧
    checkRead (appendOwn imported 1 [8]) (readStamp imported 1) = false := by
  decide

theorem prefix_is_not_a_full_snapshot :
    checkPrefix (appendOwn imported 2 [8]) (prefixStamp imported 2) = true ∧
    resolvePrefix (appendOwn imported 2 [8]) (prefixStamp imported 2) 0 = some 7 ∧
    checkRead (appendOwn imported 2 [8]) (readStamp imported 2) = false := by
  decide

theorem local_topology_not_transitively_acquired :
    ((link imported 2 1).members 0).deps = [2] := by
  decide

theorem dependency_topology_leaves_older_query_current :
    query (link imported 2 1) 0 = [42, 7, 7] ∧
    checkRead (link imported 2 1) (readStamp imported 0) = true := by
  decide

theorem own_topology_change_expires :
    query (unlink imported 0 2) 0 = [42] ∧
    checkRead (unlink imported 0 2) (readStamp imported 0) = false := by
  decide

theorem source_identity_not_composed_offset :
    resolvePrefix imported (prefixStamp imported 2) 0 = some 7 ∧
    (imported.members 0).own[0]? = some 42 := by
  decide

theorem earlier_segment_append_moves_composed_offset :
    (query imported 0)[1]? = some 7 ∧
    (query (appendOwn imported 0 [99]) 0)[1]? = some 99 ∧
    resolvePrefix (appendOwn imported 0 [99]) (prefixStamp imported 2) 0 = some 7 := by
  decide

/-- The deliberate broken version updates only the writer's revision. Its
reverse index remains structurally correct, but its reader cache is unsound. -/
def omittedNotification : Store Nat 3 :=
  { imported with
    members := Function.update imported.members 2
      { imported.members 2 with
        own := [7, 7, 8]
        revision := (imported.members 2).revision + 1 } }

theorem omitted_notification_accepts_changed_answer :
    checkRead omittedNotification (readStamp imported 0) = true ∧
    query omittedNotification 0 ≠ query imported 0 := by
  decide

theorem retirement_unlinks_and_notifies :
    ObserverInvariant (retire imported 2) ∧
    query (retire imported 2) 0 = [42] ∧
    ((retire imported 2).members 0).deps = [] ∧
    checkRead (retire imported 2) (readStamp imported 0) = false ∧
    checkPrefix (retire imported 2) (prefixStamp imported 2) = false := by
  exact ⟨retire_observers imported imported_observers 2, by decide⟩

def reusedSlot : Store Nat 3 := link (replaceOwn (retire imported 2) 2 [7, 7]) 0 2

theorem equal_answers_do_not_revive_retired_certificates :
    query reusedSlot 0 = query imported 0 ∧
    checkRead reusedSlot (readStamp imported 0) = false ∧
    checkPrefix reusedSlot (prefixStamp imported 2) = false := by
  decide

def diamond : Store Nat 4 :=
  let own := initial 902 fun source =>
    if source = 0 then [42] else if source = 1 then [7, 7]
    else if source = 2 then [8] else [9, 9]
  let branches := importModule (importModule own 1 3) 2 3
  importModule (importModule branches 0 1) 0 2

theorem diamond_retains_ordered_duplicate_occurrences :
    (diamond.members 0).deps = [1, 3, 2] ∧
    query diamond 0 = [42, 7, 7, 9, 9, 8] := by
  decide

theorem reimport_does_not_acquire_new_dependencies :
    let newer := importModule imported 2 1
    importModule newer 0 2 = newer ∧
    query (importModule newer 0 2) 0 = [42, 7, 7] := by
  dsimp only
  rw [importModule_of_mem _ 0 2 (by decide)]
  exact ⟨rfl, by decide⟩

theorem transitive_content_notification_is_direct :
    checkRead (appendOwn diamond 3 [10]) (readStamp diamond 0) = false ∧
    query (appendOwn diamond 3 [10]) 0 = [42, 7, 7, 9, 9, 10, 8] := by
  decide

def refreshOnReimport : Store Nat 3 :=
  let newer := importModule imported 2 1
  setDependencies newer 0 (OrderedDependencyIds.insertDeps (newer.members 0).deps
    (2 :: (newer.members 2).deps))

theorem refreshing_reimport_is_not_the_module_protocol :
    (refreshOnReimport.members 0).deps = [2, 1] ∧
    ((importModule (importModule imported 2 1) 0 2).members 0).deps = [2] := by
  decide

end Controls

end Mettapedia.Machines.OrderedDependencyStore
