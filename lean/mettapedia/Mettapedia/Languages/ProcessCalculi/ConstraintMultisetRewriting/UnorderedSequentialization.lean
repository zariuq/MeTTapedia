import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnorderedOccurrenceConnections

/-!
# Unordered physical connections construct actual CMR schedules

Static conditions record the declared pure event occurrences, their physical
linearity, boundary-or-producer suppliers and one joint equation model. They
do not supply an execution order. Independent graph acyclicity makes the
existing Kahn service compute an order, whose actual selected CMR schedule
is then proved executable. Every residual physical occurrence is retained.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnorderedOccurrenceConnections

open Mettapedia.Algorithms.WellFoundedServices
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open LinearConnectionLayout
open ConditionalComposite

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {n : Nat}

/-- Unordered port conditions. The roster is used only to aggregate finite
physical occurrences; its index order is not required to execute. -/
structure Conditions (A : SubstitutionAction T S) (program : Set (RuleInstance T))
    (assignment : S) (label : O → T) (before : Configuration T O) (events : Fin n → Event T O) : Prop where
  shapes : ∀ event, (ShapeTest.ofSelection (events event).1 (events event).2).Holds label
  pure : ∀ event, (events event).1.read = [] ∧ (events event).1.checks = []
  declared : ∀ event, (events event).1 ∈ program
  produced_distinct : ((roster events).flatMap fun event => event.2.made).Nodup
  consumed_distinct : ((roster events).flatMap fun event => event.2.taken).Nodup
  fresh_boundary : Disjoint (made (roster events)) before.present
  funded : ∀ event occurrence, occurrence ∈ (events event).2.taken →
    occurrence ∈ before.present ∨ ∃ producer, occurrence ∈ (events producer).2.made
  incoming : A.Models assignment before.equations
  connections : ∀ event, A.Models assignment (addedEquations label (events event).1 (events event).2)

structure Certificate (A : SubstitutionAction T S) (program : Set (RuleInstance T))
    (assignment : S) (label : O → T) (before : Configuration T O) (events : Fin n → Event T O) : Prop where
  conditions : Conditions A program assignment label before events
  acyclic : Acyclic events

theorem made_eq_of_perm {first second : List (Event T O)} (perm : first.Perm second) : made first = made second := by
  ext occurrence
  simpa only [made, List.mem_toFinset] using
    ((perm.flatMap_right (fun event : Event T O => event.2.made)).mem_iff (a := occurrence))

theorem taken_eq_of_perm {first second : List (Event T O)} (perm : first.Perm second) : taken first = taken second := by
  ext occurrence
  simpa only [taken, List.mem_toFinset] using
    ((perm.flatMap_right (fun event : Event T O => event.2.taken)).mem_iff (a := occurrence))

theorem residual_eq_of_perm (initial : Finset O) {first second : List (Event T O)} (perm : first.Perm second) :
    LinearConnectionLayout.residual initial first = LinearConnectionLayout.residual initial second := by
  rw [LinearConnectionLayout.residual, LinearConnectionLayout.residual, made_eq_of_perm perm, taken_eq_of_perm perm]

/-- Every supplier connected to the selected consumer occurs strictly in
its prefix. This uses graph order evidence, not source executability. -/
theorem supplier_in_prefix (events : Fin n → Event T O) {order earlier : List (Fin n)}
    {consumer producer : Fin n} {later : List (Fin n)}
    (respects : (catalogue events).Respects order) (covers : ∀ event, event ∈ order)
    (decomposition : order = earlier ++ consumer :: later) (edge : Edge events producer consumer) :
    producer ∈ earlier := by
  have dependency : producer ∈ (catalogue events).deps consumer := by simpa [catalogue] using edge
  have member := covers producer
  rw [decomposition, List.mem_append, List.mem_cons] at member
  rcases member with inEarlier | same | inLater
  · exact inEarlier
  · subst producer
    exact False.elim (respects.irrefl consumer (covers consumer) dependency)
  · have pairwise := respects.pairwise
    rw [decomposition] at pairwise
    have suffix := (List.pairwise_append.mp pairwise).2.1
    exact False.elim ((List.pairwise_cons.mp suffix).1 producer inLater dependency)

namespace Conditions

variable {A : SubstitutionAction T S} {program : Set (RuleInstance T)} {assignment : S}
  {label : O → T} {before : Configuration T O} {events : Fin n → Event T O}

theorem supplied_by_enumeration (conditions : Conditions A program assignment label before events)
    {order : List (Fin n)} (respects : (catalogue events).Respects order) (covers : ∀ event, event ∈ order) :
    LinearConnectionLayout.Supplied before.present (order.map events) := by
  intro earlier event later decomposition occurrence consumed
  obtain ⟨earlierIndices, remainingIndices, split, earlierMap, remainingMap⟩ :=
    List.map_eq_append_iff.mp decomposition
  obtain ⟨consumer, laterIndices, remainingSplit, eventEq, _⟩ := List.map_eq_cons_iff.mp remainingMap
  subst remainingIndices
  have taken : occurrence ∈ (events consumer).2.taken := by
    rw [eventEq]
    exact List.mem_toFinset.mp consumed
  rcases conditions.funded consumer occurrence taken with initial | ⟨producer, produced⟩
  · exact Finset.mem_union_left _ initial
  · have beforeConsumer := supplier_in_prefix events respects covers split ⟨occurrence, produced, taken⟩
    apply Finset.mem_union_right
    rw [← earlierMap]
    apply List.mem_toFinset.mpr
    exact List.mem_flatMap.mpr ⟨events producer, List.mem_map.mpr ⟨producer, beforeConsumer, rfl⟩, produced⟩

/-- Any topological enumeration gives the previously qualified static layout
and hence the actual selected source schedule. Equal event values need not
have unique preimages; all reasoning retains their occurrence indices. -/
theorem layout_of_enumeration (conditions : Conditions A program assignment label before events)
    {order : List (Fin n)} (respects : (catalogue events).Respects order) (covers : ∀ event, event ∈ order) :
    LinearConnectionLayout.Certificate A program assignment label before (order.map events) := by
  have perm : (order.map events).Perm (roster events) := (enumeration_perm events respects covers).map events
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, conditions.supplied_by_enumeration respects covers, conditions.incoming, ?_⟩
  · intro selected member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact conditions.shapes index
  · intro selected member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact conditions.pure index
  · intro selected member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact conditions.declared index
  · exact (perm.flatMap_right (fun event => event.2.made)).nodup_iff.mpr conditions.produced_distinct
  · exact (perm.flatMap_right (fun event => event.2.taken)).nodup_iff.mpr conditions.consumed_distinct
  · rw [made_eq_of_perm perm]
    exact conditions.fresh_boundary
  · intro selected member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact conditions.connections index

theorem executes_enumeration (conditions : Conditions A program assignment label before events)
    {order : List (Fin n)} (respects : (catalogue events).Respects order) (covers : ∀ event, event ∈ order) :
    ConditionalSchedule.Executable A label before (order.map events) ∧
      A.Models assignment (ConditionalSchedule.follow label before (order.map events)).equations ∧
      (ConditionalSchedule.follow label before (order.map events)).present = LinearConnectionLayout.residual before.present (roster events) := by
  have layout := conditions.layout_of_enumeration respects covers
  have perm : (order.map events).Perm (roster events) := (enumeration_perm events respects covers).map events
  exact ⟨layout.executes.1, layout.executes.2, layout.final_rows.trans (residual_eq_of_perm _ perm)⟩

theorem sequentialize (conditions : Conditions A program assignment label before events) (acyclic : Acyclic events) :
    ∃ order : List (Fin n), order? events = some order ∧
      ConditionalSchedule.Executable A label before (order.map events) ∧
      A.Models assignment (ConditionalSchedule.follow label before (order.map events)).equations ∧
      (ConditionalSchedule.follow label before (order.map events)).present = LinearConnectionLayout.residual before.present (roster events) := by
  obtain ⟨order, computed⟩ := exists_computed_order events acyclic
  have spec := order?_spec events computed
  exact ⟨order, computed, conditions.executes_enumeration spec.1 spec.2⟩

end Conditions

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnorderedOccurrenceConnections
