import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardedCutSemantics

/-!
# Guard-cut acyclicity constructs original selected executions

The unordered port conditions contain no source acceptance predicate. The
existing measured Kahn service computes an enumeration; retained read aliases,
exclusive consumption and the full physical residual boundary are preserved.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardCutSequentialization

open Mettapedia.Algorithms.WellFoundedServices
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open LinearConnectionLayout ConditionalComposite

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {n : Nat}

structure Conditions (A : SubstitutionAction T S) (assignment : S) (label : O → T)
    (before : Configuration T O) (events : Fin n → Event T O) : Prop where
  shapes : ∀ event, (ShapeTest.ofSelection (events event).1 (events event).2).Holds label
  produced_distinct : ((UnorderedOccurrenceConnections.roster events).flatMap fun event => event.2.made).Nodup
  consumed_distinct : ((UnorderedOccurrenceConnections.roster events).flatMap fun event => event.2.taken).Nodup
  fresh_boundary : Disjoint (made (UnorderedOccurrenceConnections.roster events)) before.present
  funded : ∀ event occurrence, occurrence ∈ (events event).2.taken ∨ occurrence ∈ (events event).2.read →
    occurrence ∈ before.present ∨ ∃ producer, occurrence ∈ (events producer).2.made
  take_read_apart : ∀ event, Disjoint (events event).2.taken.toFinset (events event).2.read.toFinset
  incoming : A.Models assignment before.equations
  connections : ∀ event, A.Models assignment (addedEquations label (events event).1 (events event).2)

namespace Conditions

variable {A : SubstitutionAction T S} {assignment : S} {label : O → T}
  {before : Configuration T O} {events : Fin n → Event T O}

theorem supplied_by_enumeration (conditions : Conditions A assignment label before events)
    (cuts : Fin n → Finset (Fin n)) {order : List (Fin n)}
    (respects : (GuardCutOrders.catalogue events cuts).Respects order) (covers : ∀ event, event ∈ order) :
    SharedReadProcessLayouts.Supplied before.present (order.map events) := by
  intro earlier event later decomposition occurrence port
  obtain ⟨earlierIndices, remainingIndices, split, earlierMap, remainingMap⟩ :=
    List.map_eq_append_iff.mp decomposition
  obtain ⟨consumer, laterIndices, remainingSplit, eventEq, _⟩ := List.map_eq_cons_iff.mp remainingMap
  subst remainingIndices
  have used : occurrence ∈ (events consumer).2.taken ∨ occurrence ∈ (events consumer).2.read := by
    rw [eventEq]
    simpa only [Finset.mem_union, List.mem_toFinset] using port
  rcases conditions.funded consumer occurrence used with initial | ⟨producer, produced⟩
  · exact Finset.mem_union_left _ initial
  · have beforeConsumer := GuardCutOrders.supplier_in_prefix events cuts respects covers split
      (Or.inl (Or.inl ⟨occurrence, produced, used⟩))
    apply Finset.mem_union_right
    rw [← earlierMap]
    apply List.mem_toFinset.mpr
    exact List.mem_flatMap.mpr ⟨events producer, List.mem_map.mpr ⟨producer, beforeConsumer, rfl⟩, produced⟩

theorem layout_of_enumeration (conditions : Conditions A assignment label before events)
    (cuts : Fin n → Finset (Fin n)) {order : List (Fin n)}
    (respects : (GuardCutOrders.catalogue events cuts).Respects order) (covers : ∀ event, event ∈ order) :
    SharedReadProcessLayouts.Layout A assignment label before (order.map events) := by
  have perm : (order.map events).Perm (UnorderedOccurrenceConnections.roster events) :=
    (GuardCutOrders.enumeration_perm events cuts respects covers).map events
  refine ⟨?_, ?_, ?_, ?_, conditions.supplied_by_enumeration cuts respects covers, ?_, ?_,
    conditions.incoming, ?_⟩
  · intro selected member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact conditions.shapes index
  · exact (perm.flatMap_right (fun event => event.2.made)).nodup_iff.mpr conditions.produced_distinct
  · exact (perm.flatMap_right (fun event => event.2.taken)).nodup_iff.mpr conditions.consumed_distinct
  · rw [UnorderedOccurrenceConnections.made_eq_of_perm perm]
    exact conditions.fresh_boundary
  · intro selected member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact conditions.take_read_apart index
  · apply List.pairwise_map.mpr
    have paired : order.Pairwise fun first second =>
        first ≠ second ∧ second ∉ (GuardCutOrders.catalogue events cuts).deps first :=
      List.pairwise_and_iff.mpr ⟨respects.nodup, respects.pairwise⟩
    apply paired.imp
    intro first second separated occurrence read taken
    exact separated.2 ((GuardCutOrders.mem_deps ..).mpr
      (Or.inl (Or.inr ⟨Ne.symm separated.1, occurrence, read, taken⟩)))
  · intro selected member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact conditions.connections index

theorem executes_enumeration (conditions : Conditions A assignment label before events)
    (cuts : Fin n → Finset (Fin n)) {order : List (Fin n)}
    (respects : (GuardCutOrders.catalogue events cuts).Respects order) (covers : ∀ event, event ∈ order)
    (asks : GuardedCutSemantics.Asks A label before events cuts) :
    ConditionalSchedule.Executable A label before (order.map events) ∧
      A.Models assignment (ConditionalSchedule.follow label before (order.map events)).equations ∧
      (ConditionalSchedule.follow label before (order.map events)).present =
        LinearConnectionLayout.residual before.present (UnorderedOccurrenceConnections.roster events) := by
  have layout := conditions.layout_of_enumeration cuts respects covers
  have executes := GuardedCutSemantics.executes_of_asks A assignment label before events cuts order
    respects.nodup layout (GuardCutOrders.realizes_cuts events cuts respects covers) asks
  exact ⟨executes, layout.final_model, layout.final_rows.trans
    (UnorderedOccurrenceConnections.residual_eq_of_perm before.present
      ((GuardCutOrders.enumeration_perm events cuts respects covers).map events))⟩

theorem computed_order_executes (conditions : Conditions A assignment label before events)
    (cuts : Fin n → Finset (Fin n)) {order : List (Fin n)}
    (computed : GuardCutOrders.order? events cuts = some order)
    (asks : GuardedCutSemantics.Asks A label before events cuts) :
    ConditionalSchedule.Executable A label before (order.map events) ∧
      A.Models assignment (ConditionalSchedule.follow label before (order.map events)).equations ∧
      (ConditionalSchedule.follow label before (order.map events)).present =
        LinearConnectionLayout.residual before.present (UnorderedOccurrenceConnections.roster events) :=
  conditions.executes_enumeration cuts (GuardCutOrders.order?_spec events cuts computed).1
    (GuardCutOrders.order?_spec events cuts computed).2 asks

theorem sequentialize (conditions : Conditions A assignment label before events)
    (cuts : Fin n → Finset (Fin n)) (acyclic : GuardCutOrders.Acyclic events cuts)
    (asks : GuardedCutSemantics.Asks A label before events cuts) :
    ∃ order, GuardCutOrders.order? events cuts = some order ∧
      ConditionalSchedule.Executable A label before (order.map events) ∧
      A.Models assignment (ConditionalSchedule.follow label before (order.map events)).equations ∧
      (ConditionalSchedule.follow label before (order.map events)).present =
        LinearConnectionLayout.residual before.present (UnorderedOccurrenceConnections.roster events) := by
  obtain ⟨order, computed⟩ := Option.isSome_iff_exists.mp ((GuardCutOrders.order?_isSome_iff events cuts).mpr acyclic)
  exact ⟨order, computed, conditions.computed_order_executes cuts computed asks⟩

end Conditions

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardCutSequentialization
