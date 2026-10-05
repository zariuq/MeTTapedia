import Mettapedia.GSLT.Logic.ObservedDepthBudgetSpan

/-!
# Material descent at a constructed stabilization boundary

A positive discount and an actual finite-depth stabilization proof identify
the exact readout kernel with graded behavioural bisimilarity. The original
authored occurrences form a fixed-depth reduction span. Outgoing endpoint
lifting and arbitrary successor-modal preservation are derived from that
proof. Incoming and exact-occurrence lifting keep their separate contracts.

This route uses a stabilization proof; it does not infer such a proof from
finite branching, or reflect all finite approximants constructively in every
system. The depth-budget span remains available without stabilization.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ObservedStabilizedFamilyDescent

open Distinction.Constructive ObservedMaterialization ObservationSpans
open Mettapedia.TypeTheory.MaterialSets
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open PowerClassFamilyDescent
open Mettapedia.OSLF.Framework.DerivedModalities

universe u v
variable {V : Type v} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V]
variable {S : GSLT.{u}} {K : Scale V}
variable (system : PresentedSystem.{u, u, u, u} S K)
variable (vocabulary : system.Vocabulary)
variable (stage : Nat)
variable (positive : K.Positive) (stable : system.Stabilizes vocabulary stage)

include vocabulary positive stable in
theorem readout_eq_iff_gradedBisimilar (left right : S.Term) :
    ObservedGradedFamilyDescent.readout system stage left =
        ObservedGradedFamilyDescent.readout system stage right ↔
      system.GradedBisimilar left right :=
  (ObservedGradedFamilyDescent.readout_eq_iff system vocabulary stage left right).trans
    (system.gradedBisimilar_iff_of_stabilizes vocabulary positive stable left right).2.symm

include vocabulary positive stable in
theorem family_descends_iff (graphs : S.Term → AccessiblePointedGraph.{u}) :
    FamilyInvariant (ObservedGradedFamilyDescent.readout system stage) graphs ↔
      ∀ ⦃left right⦄, system.GradedBisimilar left right →
        HSet.mk (graphs left) = HSet.mk (graphs right) := by
  constructor
  · intro invariant left right related
    exact invariant ((readout_eq_iff_gradedBisimilar system vocabulary stage positive stable left right).mpr related)
  · intro invariant left right same
    exact invariant ((readout_eq_iff_gradedBisimilar system vocabulary stage positive stable left right).mp same)

include vocabulary positive stable in
theorem selected_result_descends_iff (graphs : S.Term → AccessiblePointedGraph.{u})
    (term : SourceSection graphs) :
    TermCompatible (ObservedGradedFamilyDescent.readout system stage) graphs term ↔
      ∀ ⦃left right⦄, system.GradedBisimilar left right → (term left).1 = (term right).1 := by
  constructor
  · intro compatible left right related
    exact compatible ((readout_eq_iff_gradedBisimilar system vocabulary stage positive stable left right).mpr related)
  · intro compatible left right same
    exact compatible ((readout_eq_iff_gradedBisimilar system vocabulary stage positive stable left right).mp same)

variable (occurrences : ActionOccurrences system.dynamics)

abbrev Class := ObservationClass (ObservedGradedFamilyDescent.readout system stage)

def rawSpan : ReductionSpan S.Term := ActionOccurrences.sourceSpan occurrences

def observedSpan : ReductionSpan (Class system stage) where
  Edge := ActionOccurrences.Event occurrences
  source event := classOf (ObservedGradedFamilyDescent.readout system stage) event.source
  target event := classOf (ObservedGradedFamilyDescent.readout system stage) event.target

def observation : SpanMap (rawSpan system occurrences) (observedSpan system stage occurrences) where
  states := classOf (ObservedGradedFamilyDescent.readout system stage)
  events := id
  source_comm _ := rfl
  target_comm _ := rfl

include vocabulary positive stable in
theorem source_lifting_retains_label (state : S.Term) (event : ActionOccurrences.Event occurrences)
    (same : (observedSpan system stage occurrences).source event =
      (observation system stage occurrences).states state) :
    ∃ lifted : ActionOccurrences.Event occurrences,
      (rawSpan system occurrences).source lifted = state ∧
      (observation system stage occurrences).states ((rawSpan system occurrences).target lifted) =
        (observedSpan system stage occurrences).target event ∧
      lifted.label = event.label := by
  have reading := (classOf_eq_iff _ _ _).mp same
  have zero := (ObservedGradedFamilyDescent.readout_eq_iff system vocabulary stage _ _).mp reading
  have bisimulation := system.isGradedBisimulation_of_stabilizes vocabulary positive stable
  have action := (occurrences.erases _ _ _).mp ⟨event.occurrence⟩
  obtain ⟨target, step, matched⟩ := bisimulation.1 zero event.label action
  obtain ⟨occurrence⟩ := (occurrences.erases event.label state target).mpr step
  refine ⟨⟨event.label, state, target, occurrence⟩, rfl, ?_, rfl⟩
  exact (classOf_eq_iff _ _ _).mpr
    ((ObservedGradedFamilyDescent.readout_eq_iff system vocabulary stage _ _).mpr matched).symm

include vocabulary positive stable in
theorem sourceLifts : (observation system stage occurrences).SourceLifts := by
  intro state event same
  obtain ⟨lifted, source, target, _⟩ :=
    source_lifting_retains_label system vocabulary stage positive stable occurrences state event same
  exact ⟨lifted, source, target⟩

include vocabulary positive stable in
theorem diamond_pullback (predicate : Class system stage → Prop) (state : S.Term) :
    derivedDiamond (observedSpan system stage occurrences) predicate
        ((observation system stage occurrences).states state) ↔
      derivedDiamond (rawSpan system occurrences)
        (predicate ∘ (observation system stage occurrences).states) state :=
  (observation system stage occurrences).diamond_pullback
    (sourceLifts system vocabulary stage positive stable occurrences) predicate state

theorem predecessor_box_iff_targetLifts :
    (observation system stage occurrences).TargetLifts ↔
      ∀ (predicate : Class system stage → Prop) (state : S.Term),
        derivedBox (observedSpan system stage occurrences) predicate
            ((observation system stage occurrences).states state) ↔
          derivedBox (rawSpan system occurrences)
            (predicate ∘ (observation system stage occurrences).states) state :=
  (observation system stage occurrences).targetLifts_iff_box

end Mettapedia.GSLT.ObservedStabilizedFamilyDescent
