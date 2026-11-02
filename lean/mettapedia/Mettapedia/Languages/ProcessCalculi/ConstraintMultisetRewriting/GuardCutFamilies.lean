import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardCutCompleteness

/-!
# Guarded process executions are a family of cut-selected graph orders

Each family member fixes the predecessor subset of every guarded event.
Within that member, the existing Kahn service computes an actual original
execution. The union is exact for fresh, uniquely produced physical identities.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardCutFamilies

open LinearConnectionLayout GuardFreeProcessOrders GuardCutCompleteness

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {n : Nat}

theorem execution_iff_cut_order (A : SubstitutionAction T S) (assignment : S) (label : O → T)
    (before : Configuration T O) (events : Fin n → Event T O) (order : List (Fin n))
    (perm : order.Perm (List.finRange n))
    (fresh : FreshFrom before (UnorderedOccurrenceConnections.roster events))
    (unique : UniqueMakers (UnorderedOccurrenceConnections.roster events)) :
    (ConditionalSchedule.Executable A label before (order.map events) ∧
      A.Models assignment (ConditionalSchedule.follow label before (order.map events)).equations) ↔
      GuardCutSequentialization.Conditions A assignment label before events ∧
        ∃ cuts, (GuardCutOrders.catalogue events cuts).Respects order ∧
          GuardedCutSemantics.Asks A label before events cuts := by
  have rawPerm : (UnorderedOccurrenceConnections.roster events).Perm (order.map events) := perm.symm.map events
  have freshOrder : FreshFrom before (order.map events) := fun event member =>
    fresh event (rawPerm.mem_iff.mpr member)
  have symmetric : ∀ first second : Event T O,
      (∀ o ∈ first.2.made, o ∉ second.2.made) → ∀ o ∈ second.2.made, o ∉ first.2.made :=
    fun first second apart o inSecond inFirst => apart o inFirst inSecond
  have uniqueOrder : UniqueMakers (order.map events) :=
    (List.Perm.pairwise_iff (fun {first} {second} => symmetric first second) rawPerm).mp unique
  have covers : ∀ event, event ∈ order := fun event => perm.mem_iff.mpr (List.mem_finRange _)
  have distinct := perm.nodup_iff.mpr (List.nodup_finRange n)
  constructor
  · rintro ⟨executes, solved⟩
    have extracted := execution_extracts_cuts A assignment label before events order perm
      executes freshOrder uniqueOrder solved
    exact ⟨extracted.1, extractedCuts events order,
      respects_extracted A label events order before distinct covers executes freshOrder uniqueOrder,
      extracted.2.2⟩
  · rintro ⟨conditions, cuts, respects, asks⟩
    have result := conditions.executes_enumeration cuts respects covers asks
    exact ⟨result.1, result.2.1⟩

theorem some_execution_iff_cut_family (A : SubstitutionAction T S) (assignment : S) (label : O → T)
    (before : Configuration T O) (events : Fin n → Event T O)
    (fresh : FreshFrom before (UnorderedOccurrenceConnections.roster events))
    (unique : UniqueMakers (UnorderedOccurrenceConnections.roster events)) :
    (∃ order : List (Fin n), order.Perm (List.finRange n) ∧
      ConditionalSchedule.Executable A label before (order.map events) ∧
      A.Models assignment (ConditionalSchedule.follow label before (order.map events)).equations) ↔
      GuardCutSequentialization.Conditions A assignment label before events ∧
        ∃ cuts, GuardCutOrders.Acyclic events cuts ∧ GuardedCutSemantics.Asks A label before events cuts := by
  constructor
  · rintro ⟨order, perm, executes, solved⟩
    have characterized := (execution_iff_cut_order A assignment label before events order perm fresh unique).mp
      ⟨executes, solved⟩
    obtain ⟨cuts, respects, asks⟩ := characterized.2
    have uses : (GuardCutOrders.catalogue events cuts).Uses =
        Function.swap (GuardCutOrders.Edge events cuts) := by
      funext second first
      exact propext (by simp [Mettapedia.Algorithms.WellFoundedServices.Catalogue.Uses,
        GuardCutOrders.catalogue])
    have acyclic := respects.acyclic (fun event _ => perm.mem_iff.mpr (List.mem_finRange event))
    exact ⟨characterized.1, cuts, by
      simpa only [GuardCutOrders.Acyclic, uses, Relation.transGen_swap] using acyclic, asks⟩
  · rintro ⟨conditions, cuts, acyclic, asks⟩
    obtain ⟨order, computed, executes, solved, _⟩ := conditions.sequentialize cuts acyclic asks
    have spec := GuardCutOrders.order?_spec events cuts computed
    exact ⟨order, GuardCutOrders.enumeration_perm events cuts spec.1 spec.2, executes, solved⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardCutFamilies
