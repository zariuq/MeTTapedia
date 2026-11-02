import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardCutSequentialization

/-!
# Actual guarded executions extract one member of the cut family

The converse records every earlier indexed event at a guarded event. Its
graph is independently acyclic and its checks remain universal asks at that
cut. The result does not identify the family with one partial order.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardCutCompleteness

open Mettapedia.Algorithms.WellFoundedServices
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open LinearConnectionLayout ConditionalComposite GuardFreeProcessOrders

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {n : Nat}

def extractedCuts (events : Fin n → Event T O) (order : List (Fin n)) (current : Fin n) : Finset (Fin n) :=
  if (events current).1.checks = [] then ∅ else (order.take (order.idxOf current)).toFinset

omit [DecidableEq O] in
theorem extracts_prefix (events : Fin n → Event T O) (order : List (Fin n)) (distinct : order.Nodup)
    (earlier : List (Fin n)) (current : Fin n) (later : List (Fin n))
    (decomposition : order = earlier ++ current :: later) (guarded : (events current).1.checks ≠ []) :
    extractedCuts events order current = earlier.toFinset := by
  have notEarlier : current ∉ earlier := fun member =>
    (List.nodup_append.mp (decomposition ▸ distinct)).2.2 current member current List.mem_cons_self rfl
  simp [extractedCuts, guarded, decomposition, List.idxOf_append_of_notMem notEarlier]

omit [DecidableEq O] in
theorem extracted_realizes (events : Fin n → Event T O) (order : List (Fin n))
    (distinct : order.Nodup) : GuardCutOrders.RealizesCuts events (extractedCuts events order) order := by
  intro earlier current later decomposition guarded
  exact (extracts_prefix events order distinct earlier current later decomposition guarded).symm

omit [DecidableEq O] in
theorem extracted_guard_precedes (events : Fin n → Event T O) (order : List (Fin n))
    (covers : ∀ event, event ∈ order) {first second : Fin n}
    (edge : GuardCutOrders.GuardEdge events (extractedCuts events order) first second) :
    order.idxOf first < order.idxOf second := by
  rcases edge with ⟨guarded, inCut⟩ | ⟨guarded, different, notCut⟩
  · have inPrefix : first ∈ order.take (order.idxOf second) := by
      simpa only [extractedCuts, if_neg guarded, List.mem_toFinset] using inCut
    exact (List.mem_take_iff_idxOf_lt (covers first)).mp inPrefix
  · have notLess : ¬ order.idxOf second < order.idxOf first := by
      intro less
      apply notCut
      simpa only [extractedCuts, if_neg guarded, List.mem_toFinset] using
        (List.mem_take_iff_idxOf_lt (covers second)).mpr less
    have notSame : order.idxOf second ≠ order.idxOf first := fun same =>
      different ((List.idxOf_inj (covers second)).mp same)
    omega

theorem indices_of_pairwise (order : List (Fin n)) (_distinct : order.Nodup)
    (covers : ∀ event, event ∈ order) (relation : Fin n → Fin n → Prop)
    (irreflexive : ∀ event, ¬ relation event event)
    (ordered : order.Pairwise fun first second => ¬ relation second first)
    {first second : Fin n} (edge : relation first second) : order.idxOf first < order.idxOf second := by
  have firstBound := List.idxOf_lt_length_of_mem (covers first)
  have secondBound := List.idxOf_lt_length_of_mem (covers second)
  rcases lt_trichotomy (order.idxOf first) (order.idxOf second) with less | same | greater
  · exact less
  · have equal : first = second := (List.idxOf_inj (covers first)).mp same
    subst second
    exact False.elim (irreflexive first edge)
  · have blocked := List.pairwise_iff_getElem.mp ordered (order.idxOf second) (order.idxOf first)
      secondBound firstBound greater
    simp only [List.getElem_idxOf] at blocked
    exact False.elim (blocked edge)

theorem respects_of_indices (events : Fin n → Event T O) (cuts : Fin n → Finset (Fin n))
    (order : List (Fin n)) (distinct : order.Nodup)
    (increasing : ∀ first second, GuardCutOrders.Edge events cuts first second →
      order.idxOf first < order.idxOf second) : (GuardCutOrders.catalogue events cuts).Respects order := by
  refine ⟨distinct, ?_, ?_⟩
  · apply List.pairwise_iff_getElem.mpr
    intro i j hi hj less dependency
    have reverse := increasing order[j] order[i] ((GuardCutOrders.mem_deps ..).mp dependency)
    have backwards : j < i := by simpa only [distinct.idxOf_getElem] using reverse
    exact Nat.not_lt_of_ge (Nat.le_of_lt less) backwards
  · intro current _ dependency
    exact Nat.lt_irrefl _ (increasing current current ((GuardCutOrders.mem_deps ..).mp dependency))

theorem resource_self_false (A : SubstitutionAction T S) (label : O → T)
    (events : Fin n → Event T O) (order : List (Fin n)) (before : Configuration T O)
    (covers : ∀ event, event ∈ order)
    (executes : ConditionalSchedule.Executable A label before (order.map events)) (current : Fin n) :
    ¬ GuardCutOrders.ResourceEdge events current current := by
  obtain ⟨earlier, later, decomposition⟩ := List.mem_iff_append.mp (covers current)
  have rawSplit : order.map events = earlier.map events ++ events current :: later.map events := by
    simp [decomposition]
  have valid := valid_after_earlier A label (earlier.map events) (events current) (later.map events)
    before (rawSplit ▸ executes)
  rintro (⟨o, produced, used⟩ | ⟨different, _⟩)
  · have present : o ∈ (ConditionalSchedule.follow label before (earlier.map events)).present := by
      rcases used with taken | read
      · exact valid.occurrences.taken_subset (by simpa [Selection.commit] using taken)
      · exact valid.occurrences.kept_subset (by simpa [Selection.commit] using read)
    exact Finset.disjoint_left.mp valid.occurrences.fresh (by simpa [Selection.commit] using produced) present
  · exact different rfl

theorem respects_extracted (A : SubstitutionAction T S) (label : O → T)
    (events : Fin n → Event T O) (order : List (Fin n)) (before : Configuration T O)
    (distinct : order.Nodup) (covers : ∀ event, event ∈ order)
    (executes : ConditionalSchedule.Executable A label before (order.map events))
    (fresh : FreshFrom before (order.map events)) (unique : UniqueMakers (order.map events)) :
    (GuardCutOrders.catalogue events (extractedCuts events order)).Respects order := by
  have process := runs_respect_order A label (order.map events) before executes fresh unique
  have ordered : order.Pairwise fun first second => ¬ GuardCutOrders.ResourceEdge events second first := by
    apply (List.pairwise_map.mp process).imp
    intro first second independent edge
    rcases edge with ⟨o, produced, taken | read⟩ | ⟨_, o, read, taken⟩
    · exact (independent.1 o produced).1 taken
    · exact (independent.1 o produced).2 read
    · exact independent.2 o read taken
  apply respects_of_indices events (extractedCuts events order) order distinct
  intro first second edge
  rcases edge with resource | guard
  · exact indices_of_pairwise order distinct covers (GuardCutOrders.ResourceEdge events)
      (resource_self_false A label events order before covers executes) ordered resource
  · exact extracted_guard_precedes events order covers guard

theorem conditions_of_execution (A : SubstitutionAction T S) (assignment : S) (label : O → T)
    (before : Configuration T O) (events : Fin n → Event T O) (order : List (Fin n))
    (perm : order.Perm (List.finRange n))
    (executes : ConditionalSchedule.Executable A label before (order.map events))
    (fresh : FreshFrom before (order.map events)) (unique : UniqueMakers (order.map events))
    (solved : A.Models assignment (ConditionalSchedule.follow label before (order.map events)).equations) :
    GuardCutSequentialization.Conditions A assignment label before events := by
  have covers : ∀ event, event ∈ order := fun event => perm.mem_iff.mpr (List.mem_finRange _)
  have rawPerm : (order.map events).Perm (UnorderedOccurrenceConnections.roster events) := perm.map events
  have member : ∀ event, events event ∈ order.map events := fun event =>
    List.mem_map.mpr ⟨event, covers event, rfl⟩
  have models := (models_follow_iff A assignment label (order.map events) before).mp solved
  refine ⟨fun event => shapes_of_executable A label (order.map events) before executes _ (member event),
    (rawPerm.flatMap_right (fun event => event.2.made)).nodup_iff.mp
      (produced_distinct_of_executable A label (order.map events) before executes unique),
    (rawPerm.flatMap_right (fun event => event.2.taken)).nodup_iff.mp
      (consumed_distinct_of_executable A label (order.map events) before executes fresh unique), ?_, ?_, ?_,
    models.1, fun event => models.2 _ (member event)⟩
  · rw [← UnorderedOccurrenceConnections.made_eq_of_perm rawPerm]
    exact fresh_boundary_of_fresh_from (order.map events) before fresh
  · intro event occurrence port
    obtain ⟨earlier, later, decomposition⟩ := List.mem_iff_append.mp (covers event)
    have rawSplit : order.map events = earlier.map events ++ events event :: later.map events := by
      simp [decomposition]
    have valid := valid_after_earlier A label (earlier.map events) (events event) (later.map events)
      before (rawSplit ▸ executes)
    have present : occurrence ∈ (ConditionalSchedule.follow label before (earlier.map events)).present := by
      rcases port with taken | read
      · exact valid.occurrences.taken_subset (by simpa [Selection.commit] using taken)
      · exact valid.occurrences.kept_subset (by simpa [Selection.commit] using read)
    rcases Finset.mem_union.mp (present_follow_subset label (earlier.map events) before present) with initial | made
    · exact Or.inl initial
    · obtain ⟨producer, producerMember, produced⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp made)
      obtain ⟨index, _, rfl⟩ := List.mem_map.mp producerMember
      exact Or.inr ⟨index, produced⟩
  · intro event
    obtain ⟨earlier, later, decomposition⟩ := List.mem_iff_append.mp (covers event)
    have rawSplit : order.map events = earlier.map events ++ events event :: later.map events := by
      simp [decomposition]
    exact (valid_after_earlier A label (earlier.map events) (events event) (later.map events)
      before (rawSplit ▸ executes)).occurrences.apart

theorem execution_extracts_cuts (A : SubstitutionAction T S) (assignment : S) (label : O → T)
    (before : Configuration T O) (events : Fin n → Event T O) (order : List (Fin n))
    (perm : order.Perm (List.finRange n))
    (executes : ConditionalSchedule.Executable A label before (order.map events))
    (fresh : FreshFrom before (order.map events)) (unique : UniqueMakers (order.map events))
    (solved : A.Models assignment (ConditionalSchedule.follow label before (order.map events)).equations) :
    GuardCutSequentialization.Conditions A assignment label before events ∧
      GuardCutOrders.Acyclic events (extractedCuts events order) ∧
      GuardedCutSemantics.Asks A label before events (extractedCuts events order) := by
  have conditions := conditions_of_execution A assignment label before events order perm executes fresh unique solved
  have distinct := perm.nodup_iff.mpr (List.nodup_finRange n)
  have covers : ∀ event, event ∈ order := fun event => perm.mem_iff.mpr (List.mem_finRange _)
  have respects := respects_extracted A label events order before distinct covers executes fresh unique
  refine ⟨conditions, ?_, GuardedCutSemantics.asks_of_executes A assignment label before events
    (extractedCuts events order) order distinct covers (conditions.layout_of_enumeration _ respects covers)
      (extracted_realizes events order distinct) executes⟩
  have uses : (GuardCutOrders.catalogue events (extractedCuts events order)).Uses =
      Function.swap (GuardCutOrders.Edge events (extractedCuts events order)) := by
    funext second first
    exact propext (by simp [Catalogue.Uses, GuardCutOrders.catalogue])
  have acyclic := respects.acyclic (fun event _ => covers event)
  simpa only [GuardCutOrders.Acyclic, uses, Relation.transGen_swap] using acyclic

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardCutCompleteness
