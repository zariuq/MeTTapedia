import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourceOccupation
import Mettapedia.Cybernetics.ObservedVariety

/-!
# Retaining a resource footprint preserves its supported future observations

Intersection computes a smaller occurrence world. Every occupation program
whose tested and written identities lie in the retained footprint commutes
with this restriction, including the `none` outcome for a refused operation.
The same law holds for any finite continuation of such commits.

The existing Observer interface records these future observations. Their
kernel is exactly equality of the retained worlds: the empty continuation
observes all retained membership, and supported continuations can distinguish
nothing further. This permits an exact finite observation factorization.

The footprint limits all future tests and writes. It does not classify native
pointers as dead, supply a C ownership invariant, identify execution histories,
or permit an arbitrary future program to observe a discarded occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourceObservations

open ResourceOccupation
open Mettapedia.Cybernetics
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {O : Type*} [DecidableEq O]

/-- The retained world consists of the actual identities in the footprint. -/
def project (footprint world : Finset O) : Finset O := world ∩ footprint

@[simp] theorem mem_project {footprint world : Finset O} {identity : O} :
    identity ∈ project footprint world ↔ identity ∈ world ∧ identity ∈ footprint :=
  Finset.mem_inter

theorem project_subset (footprint world : Finset O) : project footprint world ⊆ footprint :=
  Finset.inter_subset_right

@[simp] theorem project_project (footprint world : Finset O) :
    project footprint (project footprint world) = project footprint world := by
  ext identity
  simp

theorem project_of_subset {footprint world : Finset O} (included : world ⊆ footprint) :
    project footprint world = world := Finset.inter_eq_left.mpr included

theorem project_insert (footprint world : Finset O) {identity : O}
    (included : identity ∈ footprint) :
    project footprint (insert identity world) = insert identity (project footprint world) := by
  ext other
  simp only [mem_project, Finset.mem_insert]
  constructor
  · rintro ⟨rfl | present, kept⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨present, kept⟩
  · rintro (rfl | ⟨present, kept⟩)
    · exact ⟨Or.inl rfl, included⟩
    · exact ⟨Or.inr present, kept⟩

theorem project_erase (footprint world : Finset O) (identity : O) :
    project footprint (world.erase identity) = (project footprint world).erase identity := by
  ext other
  simp only [mem_project, Finset.mem_erase]
  tauto

/-- The entire partial result commutes with the concrete restriction. -/
def Preserves (footprint : Finset O) (operation : Op O) : Prop :=
  ∀ world, (operation world).map (project footprint) = operation (project footprint world)

theorem preserves_one (footprint : Finset O) : Preserves footprint (one (O := O)) := by
  intro world
  rfl

theorem preserves_andThen {footprint : Finset O} {first second : Op O}
    (left : Preserves footprint first) (right : Preserves footprint second) :
    Preserves footprint (andThen first second) := by
  intro world
  have carried := left world
  cases result : first world with
  | none =>
      have restricted : first (project footprint world) = none := by
        simpa only [result, Option.map_none] using carried.symm
      simp only [andThen, result, restricted, Option.bind_none, Option.map_none]
  | some middle =>
      have restricted : first (project footprint world) = some (project footprint middle) := by
        simpa only [result, Option.map_some] using carried.symm
      simp only [andThen, result, restricted, Option.bind_some]
      exact right middle

theorem preserves_take {footprint : Finset O} {identity : O} (included : identity ∈ footprint) :
    Preserves footprint (annihilate identity) := by
  intro world
  by_cases present : identity ∈ world
  · simp only [annihilate, present, mem_project, included, and_self, if_true, Option.map_some]
    exact congrArg some (project_erase footprint world identity)
  · simp [annihilate, present]

theorem preserves_read {footprint : Finset O} {identity : O} (included : identity ∈ footprint) :
    Preserves footprint (point identity) := by
  intro world
  by_cases present : identity ∈ world <;> simp [point, present, included]

theorem preserves_make {footprint : Finset O} {identity : O} (included : identity ∈ footprint) :
    Preserves footprint (create identity) := by
  intro world
  by_cases present : identity ∈ world
  · simp [create, present, included]
  · simp only [create, present, mem_project, false_and, if_false, Option.map_some]
    exact congrArg some (project_insert footprint world included)

theorem preserves_absence {footprint : Finset O} {identity : O} (included : identity ∈ footprint) :
    Preserves footprint (vacant identity) := by
  intro world
  by_cases present : identity ∈ world <;> simp [vacant, present, included]

theorem preserves_absentOn {footprint region : Finset O} (included : region ⊆ footprint) :
    Preserves footprint (absentOn region) := by
  intro world
  have disjoint : Disjoint region (project footprint world) ↔ Disjoint region world := by
    constructor
    · intro apart
      apply Finset.disjoint_left.mpr
      intro identity member present
      exact Finset.disjoint_left.mp apart member (mem_project.mpr ⟨present, included member⟩)
    · intro apart
      apply Finset.disjoint_left.mpr
      intro identity member present
      exact Finset.disjoint_left.mp apart member (mem_project.mp present).1
  by_cases absent : Disjoint region world <;> simp [absentOn, disjoint, absent]

theorem preserves_runList (footprint : Finset O) (operation : O → Op O) (identities : List O)
    (supported : ∀ identity ∈ identities, Preserves footprint (operation identity)) :
    Preserves footprint (runList operation identities) := by
  induction identities with
  | nil => exact preserves_one footprint
  | cons identity rest earlier =>
      exact preserves_andThen (supported identity (List.mem_cons_self))
        (earlier fun other member => supported other (List.mem_cons_of_mem identity member))

/-- Every take/read/make identity is within the retained footprint. -/
def SupportedCommit (footprint : Finset O) (event : List O × List O × List O) : Prop :=
  ∀ identity ∈ event.1 ++ event.2.1 ++ event.2.2, identity ∈ footprint

theorem preserves_commit {footprint : Finset O} {taken read made : List O}
    (supported : SupportedCommit footprint (taken, read, made)) :
    Preserves footprint (commit taken read made) := by
  apply preserves_andThen
  · apply preserves_andThen
    · apply preserves_runList
      intro identity member
      exact preserves_take (supported identity (by simp only [List.mem_append]; exact Or.inl (Or.inl member)))
    · apply preserves_runList
      intro identity member
      exact preserves_read (supported identity (by simp only [List.mem_append]; exact Or.inl (Or.inr member)))
  · apply preserves_runList
    intro identity member
    exact preserves_make (supported identity (List.mem_append_right _ member))

def Supported (footprint : Finset O) (events : List (List O × List O × List O)) : Prop :=
  ∀ event ∈ events, SupportedCommit footprint event

theorem preserves_runs {footprint : Finset O} {events : List (List O × List O × List O)}
    (supported : Supported footprint events) : Preserves footprint (runs events) := by
  induction events with
  | nil => exact preserves_one footprint
  | cons event rest earlier =>
      obtain ⟨taken, read, made⟩ := event
      exact preserves_andThen (preserves_commit (supported _ (List.mem_cons_self)))
        (earlier fun next member => supported next (List.mem_cons_of_mem _ member))

/-- Retention preserves refusal in both directions, not just successful results. -/
theorem refusal_iff {footprint : Finset O} {operation : Op O}
    (preserved : Preserves footprint operation) (world : Finset O) :
    operation (project footprint world) = none ↔ operation world = none := by
  rw [← preserved world]
  simp only [Option.map_eq_none_iff]

theorem runs_refusal_iff {footprint : Finset O} {events : List (List O × List O × List O)}
    (supported : Supported footprint events) (world : Finset O) :
    runs events (project footprint world) = none ↔ runs events world = none :=
  refusal_iff (preserves_runs supported) world

omit [DecidableEq O] in
theorem supported_take {footprint : Finset O} {events : List (List O × List O × List O)}
    (supported : Supported footprint events) (length : Nat) :
    Supported footprint (events.take length) := by
  intro event member
  exact supported event (List.mem_of_mem_take member)

/-- The preservation law holds at every prefix, so a refused prefix is not
hidden by comparison of only the final successful endpoint. -/
theorem every_prefix_preserved {footprint : Finset O} {events : List (List O × List O × List O)}
    (supported : Supported footprint events) (world : Finset O) (length : Nat) :
    (runs (events.take length) world).map (project footprint) =
      runs (events.take length) (project footprint world) :=
  preserves_runs (supported_take supported length) world

theorem selection_enabled_iff {R : Type*} (label : O → R) (selection : Selection O)
    {footprint : Finset O} (supported : SupportedCommit footprint
      (selection.taken, selection.read, selection.made)) (world : Finset O) :
    (selection.taken.Nodup ∧ selection.made.Nodup ∧ Enabled label world selection.commit) ↔
      selection.taken.Nodup ∧ selection.made.Nodup ∧
        Enabled label (project footprint world) selection.commit := by
  rw [enabled_iff_nonzero_and_fresh, enabled_iff_nonzero_and_fresh]
  apply and_congr_left
  intro _fresh
  have refused := refusal_iff (preserves_commit supported) world
  cases before : commit selection.taken selection.read selection.made world <;>
    cases after : commit selection.taken selection.read selection.made (project footprint world) <;>
    simp_all

/-- Reuse the common Observer interface; each view includes the partial outcome
of every supported finite continuation. -/
def futureObserver (footprint : Finset O) :
    Observer (Finset O)
      ({events : List (List O × List O × List O) // Supported footprint events} → Option (Finset O)) where
  observe world events := (runs events.1 world).map (project footprint)

theorem future_observation_iff (footprint left right : Finset O) :
    (futureObserver footprint).observe left = (futureObserver footprint).observe right ↔
      project footprint left = project footprint right := by
  constructor
  · intro same
    have empty := congrFun same ⟨[], by intro event member; cases member⟩
    simpa only [futureObserver, runs, one, Option.map_some, Option.some.injEq] using empty
  · intro same
    funext events
    change (runs events.1 left).map (project footprint) =
      (runs events.1 right).map (project footprint)
    rw [preserves_runs events.2 left, preserves_runs events.2 right, same]

theorem retention_preserves_all_supported_futures (footprint world : Finset O) :
    (futureObserver footprint).observe (project footprint world) =
      (futureObserver footprint).observe world :=
  (future_observation_iff footprint _ _).mpr (project_project footprint world)

abbrev Retained (footprint : Finset O) := {world : Finset O // world ⊆ footprint}

def retain (footprint world : Finset O) : Retained footprint :=
  ⟨project footprint world, project_subset footprint world⟩

@[simp] theorem retain_included (footprint : Finset O) (world : Retained footprint) :
    retain footprint world.val = world := by
  apply Subtype.ext
  exact project_of_subset world.property

/-- Any observation insensitive to these future-observation fibres factors
through the computed retained world, without choosing representatives. -/
theorem observation_factors_iff {View : Type*} (footprint : Finset O)
    (observe : Finset O → View) :
    (∀ left right, (futureObserver footprint).observe left =
      (futureObserver footprint).observe right → observe left = observe right) ↔
    ∃ readout : Retained footprint → View, ∀ world, readout (retain footprint world) = observe world := by
  constructor
  · intro invariant
    refine ⟨fun kept => observe kept.val, ?_⟩
    intro world
    exact invariant _ _ (retention_preserves_all_supported_futures footprint world)
  · rintro ⟨readout, realizes⟩ left right same
    have retained : retain footprint left = retain footprint right :=
      Subtype.ext ((future_observation_iff footprint left right).mp same)
    rw [← realizes left, ← realizes right, retained]

def membershipObserver : Observer (Finset O) (O → Bool) where
  observe world identity := decide (identity ∈ world)

theorem all_membership_observers_separate :
    Function.Injective (membershipObserver (O := O)).observe := by
  intro left right same
  ext identity
  have equal := congrFun same identity
  simpa only [membershipObserver, decide_eq_decide] using equal

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourceObservations
