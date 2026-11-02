import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnorderedSequentialization

/-!
# Independent graph acyclicity characterizes pure selected executions

Actual executions of fresh, uniquely produced occurrences respect the
producer/use graph. Conversely, the unordered port conditions and graph
acyclicity make the existing Kahn service construct an actual selected
execution. The graph vertices remain occurrence indices throughout, even
when different indices contain equal rules or equal whole event values.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnorderedOccurrenceConnections

open Mettapedia.Algorithms.WellFoundedServices
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open LinearConnectionLayout
open GuardFreeProcessOrders

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {n : Nat}

theorem covers_of_perm {order : List (Fin n)} (perm : order.Perm (List.finRange n)) :
    ∀ event, event ∈ order := fun event => perm.mem_iff.mpr (List.mem_finRange event)

theorem respects_of_layout {A : SubstitutionAction T S} {program : Set (RuleInstance T)} {assignment : S}
    {label : O → T} {before : Configuration T O} (events : Fin n → Event T O) (order : List (Fin n))
    (perm : order.Perm (List.finRange n))
    (layout : LinearConnectionLayout.Certificate A program assignment label before (order.map events)) :
    (catalogue events).Respects order := by
  have covers := covers_of_perm perm
  have pairwise : order.Pairwise fun first second => LaterIndependent (events first) (events second) :=
    List.pairwise_map.mp layout.respects_causality
  refine ⟨perm.nodup_iff.mpr (List.nodup_finRange n), ?_, ?_⟩
  · apply pairwise.imp
    intro first second independent dependency
    have edge : Edge events second first := by simpa [catalogue] using dependency
    obtain ⟨occurrence, produced, consumed⟩ := edge
    exact (independent.1 occurrence produced).1 consumed
  · intro event member dependency
    have edge : Edge events event event := by simpa [catalogue] using dependency
    obtain ⟨occurrence, produced, consumed⟩ := edge
    obtain ⟨earlier, later, decomposition⟩ := List.mem_iff_append.mp member
    have split : order.map events = earlier.map events ++ events event :: later.map events := by
      rw [decomposition, List.map_append, List.map_cons]
    have valid := valid_after_earlier A label (earlier.map events) (events event) (later.map events) before
      (split ▸ layout.executes.1)
    have present := valid.occurrences.taken_subset (List.mem_toFinset.mpr consumed)
    exact Finset.disjoint_left.mp valid.occurrences.fresh (List.mem_toFinset.mpr produced) present

theorem conditions_of_layout {A : SubstitutionAction T S} {program : Set (RuleInstance T)} {assignment : S}
    {label : O → T} {before : Configuration T O} (events : Fin n → Event T O) (order : List (Fin n))
    (perm : order.Perm (List.finRange n))
    (layout : LinearConnectionLayout.Certificate A program assignment label before (order.map events)) :
    Conditions A program assignment label before events := by
  have covers := covers_of_perm perm
  have rawPerm : (order.map events).Perm (roster events) := perm.map events
  have member : ∀ event, events event ∈ order.map events := fun event => List.mem_map.mpr ⟨event, covers event, rfl⟩
  refine ⟨fun event => layout.shapes _ (member event), fun event => layout.pure _ (member event),
    fun event => layout.declared _ (member event),
    (rawPerm.flatMap_right (fun event => event.2.made)).nodup_iff.mp layout.produced_distinct,
    (rawPerm.flatMap_right (fun event => event.2.taken)).nodup_iff.mp layout.consumed_distinct, ?_, ?_,
    layout.incoming, fun event => layout.connections _ (member event)⟩
  · rw [← made_eq_of_perm rawPerm]
    exact layout.fresh_boundary
  · intro event occurrence consumed
    obtain ⟨earlier, later, decomposition⟩ := List.mem_iff_append.mp (covers event)
    have split : order.map events = earlier.map events ++ events event :: later.map events := by
      rw [decomposition, List.map_append, List.map_cons]
    have supplied := layout.supplied (earlier.map events) (events event) (later.map events) split
      (List.mem_toFinset.mpr consumed)
    rcases Finset.mem_union.mp supplied with initial | produced
    · exact Or.inl initial
    · have inList : occurrence ∈ (earlier.map events).flatMap (fun selected => selected.2.made) :=
        List.mem_toFinset.mp produced
      obtain ⟨producer, member, made⟩ := List.mem_flatMap.mp inList
      obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
      exact Or.inr ⟨index, made⟩

/-- The source-to-graph direction retains the actual selected event
occurrences and their global equation model. -/
theorem certificate_of_execution {A : SubstitutionAction T S} {program : Set (RuleInstance T)} {assignment : S}
    {label : O → T} {before : Configuration T O} (events : Fin n → Event T O) (order : List (Fin n))
    (perm : order.Perm (List.finRange n))
    (executes : ConditionalSchedule.Executable A label before (order.map events))
    (fresh : FreshFrom before (order.map events)) (unique : UniqueMakers (order.map events))
    (pure : LinearHornAdequacy.Pure (order.map events))
    (declared : LinearHornAdequacy.Declared program (order.map events))
    (solved : A.Models assignment (ConditionalSchedule.follow label before (order.map events)).equations) :
    Certificate A program assignment label before events := by
  have layout := LinearConnectionLayout.certificate_of_executable A label (order.map events) before
    executes fresh unique pure declared solved
  exact ⟨conditions_of_layout events order perm layout,
    acyclic_of_enumeration events (respects_of_layout events order perm layout) (covers_of_perm perm)⟩

namespace Conditions

variable {A : SubstitutionAction T S} {program : Set (RuleInstance T)} {assignment : S}
  {label : O → T} {before : Configuration T O} {events : Fin n → Event T O}

theorem fresh_from_order (conditions : Conditions A program assignment label before events) (order : List (Fin n)) :
    FreshFrom before (order.map events) := by
  intro selected member occurrence produced initial
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  have inList : occurrence ∈ (roster events).flatMap (fun event => event.2.made) :=
    List.mem_flatMap.mpr ⟨events index, List.mem_map.mpr ⟨index, List.mem_finRange _, rfl⟩, produced⟩
  exact Finset.disjoint_left.mp conditions.fresh_boundary (List.mem_toFinset.mpr inList) initial

theorem unique_makers_order (conditions : Conditions A program assignment label before events)
    (order : List (Fin n)) (perm : order.Perm (List.finRange n)) : UniqueMakers (order.map events) := by
  have rawPerm : (order.map events).Perm (roster events) := perm.map events
  have distinct := (rawPerm.flatMap_right (fun event => event.2.made)).nodup_iff.mpr conditions.produced_distinct
  have separated := (List.nodup_flatMap.mp distinct).2
  exact separated.imp (fun {first second} disjoint occurrence inFirst inSecond =>
    List.disjoint_left.mp disjoint inFirst inSecond)

theorem pure_order (conditions : Conditions A program assignment label before events) (order : List (Fin n)) :
    LinearHornAdequacy.Pure (order.map events) := by
  intro selected member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact conditions.pure index

theorem declared_order (conditions : Conditions A program assignment label before events) (order : List (Fin n)) :
    LinearHornAdequacy.Declared program (order.map events) := by
  intro selected member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact conditions.declared index

theorem model_after_order (conditions : Conditions A program assignment label before events) (order : List (Fin n)) :
    A.Models assignment (ConditionalSchedule.follow label before (order.map events)).equations := by
  apply (models_follow_iff A assignment label _ _).mpr
  refine ⟨conditions.incoming, ?_⟩
  intro selected member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact conditions.connections index

/-- Acyclicity is independent graph data, yet it is equivalent to existence
of an actual selected execution of all indexed occurrences exactly once. -/
theorem acyclic_iff_executable_enumeration (conditions : Conditions A program assignment label before events) :
    Acyclic events ↔ ∃ order : List (Fin n), order.Perm (List.finRange n) ∧
      ConditionalSchedule.Executable A label before (order.map events) := by
  constructor
  · intro acyclic
    obtain ⟨order, computed, executes, _, _⟩ := conditions.sequentialize acyclic
    exact ⟨order, order?_perm events computed, executes⟩
  · rintro ⟨order, perm, executes⟩
    exact (certificate_of_execution events order perm executes (conditions.fresh_from_order order)
      (conditions.unique_makers_order order perm) (conditions.pure_order order) (conditions.declared_order order)
      (conditions.model_after_order order)).acyclic

/-- Topological tie-breaking does not change the complete physical result
or the solution set of the final equation store. This is a comparison of
fixed selected occurrences, not of arbitrary program traces or probabilities. -/
theorem enumerations_same_final (conditions : Conditions A program assignment label before events)
    (first second : List (Fin n))
    (firstRespects : (catalogue events).Respects first) (firstCovers : ∀ event, event ∈ first)
    (secondRespects : (catalogue events).Respects second) (secondCovers : ∀ event, event ∈ second) :
    SameUpTo A (ConditionalSchedule.follow label before (first.map events))
      (ConditionalSchedule.follow label before (second.map events)) := by
  have firstLayout := conditions.layout_of_enumeration firstRespects firstCovers
  have secondRuns := (conditions.executes_enumeration secondRespects secondCovers).1
  have perm : first.Perm second :=
    (enumeration_perm events firstRespects firstCovers).trans (enumeration_perm events secondRespects secondCovers).symm
  exact (firstLayout.reorderings (second.map events) (perm.map events)).2 secondRuns

end Conditions

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnorderedOccurrenceConnections
