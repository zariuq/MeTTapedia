import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationRunAnswers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.ObserverConcepts

/-!
# Typed and observational classes through complete computational runs

Every execution has a result at its original declared type. Observers that
respect the frame's typed equality give the same readout on the input and
result. The distinction calculus's actual saturated concepts therefore
transport along the execution. This is an observation license, not a claim
that every predicate of raw code or occurrence positions is invariant.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open AlgebraicParallel NativeTypesOnTheStep.Computing ConversionCoherence
open LogicOverTheStep.Distinctions
open Mettapedia.Cybernetics.DistinctionCalculus.Exclusion

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
  {qualified : Qualified S} {presentation : SchemaPresentation S.R}

def Execution.output {configuration : Configuration (S := S)}
    (execution : Execution qualified presentation configuration) : TotalTerm configuration.state.frame :=
  ⟨(configuration.state.label configuration.active).1, ⟨execution.term, execution.typed.1⟩⟩

theorem Execution.output_equivalent {configuration : Configuration (S := S)}
    (execution : Execution qualified presentation configuration) :
    (frames S.levels).E (configuration.state.label configuration.active) execution.output := by
  have original := ((frames S.levels).equivalence configuration.state.frame).refl
    (configuration.state.label configuration.active)
  exact ⟨original.1, execution.typed.2⟩

def Respects {frame : Context S.R} {Value : Type} (observe : TotalTerm frame → Value) : Prop :=
  ∀ first second, (frames S.levels).E first second → observe first = observe second

theorem Execution.observation {configuration : Configuration (S := S)}
    (execution : Execution qualified presentation configuration) {Value : Type}
    (observe : TotalTerm configuration.state.frame → Value) (respects : Respects observe) :
    observe (configuration.state.label configuration.active) = observe execution.output :=
  respects _ _ execution.output_equivalent

theorem Execution.concept {configuration : Configuration (S := S)}
    (execution : Execution qualified presentation configuration) {Index Value : Type}
    (read : Index → TotalTerm configuration.state.frame → Value) (respects : ∀ index, Respects (read index))
    {concept : Set (TotalTerm configuration.state.frame)}
    (saturated : IsConcept (ObserverConcepts.Apart read) concept) :
    configuration.state.label configuration.active ∈ concept ↔ execution.output ∈ concept := by
  have same : ObserverConcepts.Indist read (configuration.state.label configuration.active) execution.output :=
    fun index => execution.observation (read index) (respects index)
  have closed := (ObserverConcepts.isConcept_iff_saturated (read := read) concept).mp saturated
  exact ⟨fun member => closed _ member _ same,
    fun member => closed _ member _ (fun index => (same index).symm)⟩

theorem quotient_respects (frame : Context S.R) :
    Respects (fun term : TotalTerm frame => QTerm.mk S.levels term.2) :=
  fun _ _ same => (equivalent_iff_classes S.levels _ _).mp same

theorem Execution.quotient {configuration : Configuration (S := S)}
    (execution : Execution qualified presentation configuration) :
    QTerm.mk S.levels (configuration.state.label configuration.active).2 =
      QTerm.mk S.levels execution.output.2 :=
  execution.observation _ (quotient_respects _)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.Execution.concept
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.Execution.quotient
