import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Progress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.TransitionMaps

/-!
# Existing strong transition comparisons as operational correspondences

These adapters retain the supplied relation and actual endpoint laws. They
add no admission rule. Strong step comparisons earn positive implementation
blocks and target administrative progress, but do not earn event bijections.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Transitions

open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational Mettapedia.GSLT.Ultrainfinite
open FragmentsOfTheStep.TransitionMaps

universe u v

variable {A : Type u} {B : Type v} {stepA : A → A → Prop} {stepB : B → B → Prop}
  {related : A → B → Prop}

def correspondence (comparison : IsBisimulation stepA stepB related) :
    OperationalCorrespondence (theoryOf A stepA) (theoryOf B stepB) where
  related := related
  readStep same step := .inr (comparison.2 same step)
  forward same step := by
    obtain ⟨next, taken, there⟩ := comparison.1 same step
    exact ⟨next, ⟨.cons ⟨taken⟩ (.refl next)⟩, there⟩

def progress (comparison : IsBisimulation stepA stepB related) :
    Progress.Certificate (correspondence comparison).toOperationalReadback :=
  Progress.Certificate.ofReflection comparison.2

theorem positive_forward (comparison : IsBisimulation stepA stepB related)
    {origin after : A} {current : B} (same : related origin current) (step : stepA origin after) :
    ∃ next, ∃ path : ExecutionPath (theoryOf B stepB) current next,
      path.length = 1 ∧ related after next := by
  obtain ⟨next, taken, there⟩ := comparison.1 same step
  exact ⟨next, .cons ⟨taken⟩ (.refl next), rfl, there⟩

theorem normalization_iff (comparison : IsBisimulation stepA stepB related)
    {origin : A} {current : B} (same : related origin current) :
    Acc (fun after before => stepA before after) origin ↔
      Acc (fun next state => stepB state next) current := by
  apply Progress.normalization_iff (correspondence comparison) (progress comparison)
    (related := same)
  intro origin after current atOrigin stepped
  obtain ⟨next, path, length, there⟩ := positive_forward comparison atOrigin stepped
  exact ⟨next, path, by rw [length]; decide, there⟩

def functionalCorrespondence {map : A → B}
    (comparison : FunctionalBisimulation stepA stepB map) :
    OperationalCorrespondence (theoryOf A stepA) (theoryOf B stepB) :=
  correspondence (graph_isBisimulation_iff.mpr comparison)

def translation {map : A → B} (comparison : FunctionalBisimulation stepA stepB map) :
    OperationalTranslation (theoryOf A stepA) (theoryOf B stepB) where
  mapTerm := map
  mapEquiv := fun same => congrArg map same
  mapStep := comparison.zig

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Transitions

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Transitions.correspondence
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Transitions.normalization_iff
