import Mettapedia.GSLT.Core.IndexedOperational
import Mettapedia.Languages.MeTTa.Prime.Language

/-!
# A two-dimensional coherence witness for Prime evaluation

Prime exposes two routes from an evaluation request to the same occurrence:

* the one-step extensional route supplied by the query-derived evaluator;
* the three-step lazy route that enters a revision-keyed Need cell and returns.

`Prime.Language` proves both paths in the interacting semantic GSLT.  This
module retains the corresponding steps as type-valued route data and supplies
one authored 2-generator comparing them.  Its free closure under vertical
composition and whiskering is the existing `GeneratedTwoCell` construction.

This is deliberately a finite two-dimensional nucleus.  It is not a claim
that all bicategorical coherence laws, much less an `(infinity,2)`-completion,
have already been constructed.
-/

namespace Mettapedia.Languages.MeTTa.Prime.EvaluationCoherence

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.ClosureCriteria
open Mettapedia.GSLT.Dynamics.OccurrenceSemantics
open Mettapedia.GSLT.Dynamics.ProofRelevantNeed
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.Languages.MeTTa.Prime.Language
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## The selected base is a faithful component, not all of Prime -/

/-- The selected base host embeds into the assembled Prime kernel, but that
embedding does not locally cover Prime transitions.  Entering the Need
component is an outgoing step from an embedded occurrence request whose
target has no base-host preimage.

The explicit `space` argument is essential: a model with no spaces has no
evaluation request at which to observe the separating transition. -/
def baseEmbedding_needStepEscapes (model : Model)
    (space : model.Space) (subject : Pattern) :
    ImageEscapingStep
      model.base.host (kernelGSLT model) (baseEmbedding model).toFun where
  sourceTerm := model.base.occurrenceEmbedding.toFun (.request space subject)
  targetTerm := (needEmbedding model).toFun (.request space subject)
  step := evaluation_enters_need model space subject
  target_not_in_image := by
    intro sourceTarget image_eq
    cases image_eq

/-- The explicit escaping-step witness refutes exact local coverage without
weakening the existing faithful and observation-preserving base embedding. -/
theorem baseEmbedding_not_locally_covered (model : Model)
    (space : model.Space) (subject : Pattern) :
    ¬ Nonempty
      (StepCover model.base.host (kernelGSLT model)
        (baseEmbedding model).toFun) :=
  (baseEmbedding_needStepEscapes model space subject).not_stepCover

/-! ## Current execution-shape witnesses -/

/-- One admitted result occurrence gives the selected Need route two
composable steps: enter the Need component, then select that occurrence. -/
def needRouteComposableStep (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (model.base.source.occurrences space subject)) :
    ComposableStepWitness (kernelGSLT model) where
  source := (evaluationKernelEmbedding model).toFun
    (.request space subject)
  middle := (needEmbedding model).toFun (.request space subject)
  target := (needEmbedding model).toFun
    (.answer space subject (needKey model space subject) occurrence result)
  first := evaluation_enters_need model space subject
  second := ((needEmbedding model).step_iff _ _).2
    (RevisionedOccurrenceStep.found copy)

/-- Need-based execution has internal re-entry whenever the selected
occurrence source has an admitted result occurrence. -/
theorem needRoute_has_composable_steps_of_occurrence (model : Model)
    (space : model.Space) (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (model.base.source.occurrences space subject)) :
    HasComposableSteps (kernelGSLT model) :=
  ⟨needRouteComposableStep model space subject result occurrence copy⟩

/-- The generated occurrence theory and its hosted Need route occupy different
points of the generic composability capability: the former is one-step
terminal, while the latter re-enters for every admitted occurrence. -/
theorem occurrenceTheory_and_needRoute_are_composability_separated
    (model : Model) (space : model.Space) (subject result : Pattern)
    (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (model.base.source.occurrences space subject)) :
    (¬ HasComposableSteps (occurrenceGSLT model.base.source)) ∧
      HasComposableSteps (kernelGSLT model) :=
  ⟨occurrenceGSLT_not_hasComposableSteps model.base.source,
    needRoute_has_composable_steps_of_occurrence model space subject result
      occurrence copy⟩

/-- In the reverse direction, no forward operational translation can erase
the selected Need route into its one-step-terminal occurrence source while
preserving both selected steps. -/
theorem no_needRoute_translation_to_occurrenceTheory (model : Model)
    (space : model.Space) (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (model.base.source.occurrences space subject)) :
    ¬ Nonempty
      (OperationalTranslation (kernelGSLT model)
        (occurrenceGSLT model.base.source)) :=
  OperationalTranslation.no_translation_to_oneStepTerminal
    (needRoute_has_composable_steps_of_occurrence model space subject result
      occurrence copy)
    (occurrenceOneStepTerminal model.base.source)

/-- Prime steps retained as data rather than propositionally truncated. -/
abbrev CarriedStep (model : Model) (source target : (kernelGSLT model).Term) :=
  PLift ((kernelGSLT model).Step source target)

/-- The direct extensional route for one result occurrence. -/
def directRoute (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (model.base.source.occurrences space subject)) :
    Route (CarriedStep model)
      ((evaluationKernelEmbedding model).toFun (.request space subject))
      ((evaluationKernelEmbedding model).toFun
        (.answer space subject occurrence result)) :=
  .cons ⟨((evaluationKernelEmbedding model).step_iff _ _).2
    (OccurrenceStep.found copy)⟩ (.refl _)

/-- The lazy route through Need for the same result occurrence. -/
def lazyRoute (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (model.base.source.occurrences space subject)) :
    Route (CarriedStep model)
      ((evaluationKernelEmbedding model).toFun (.request space subject))
      ((evaluationKernelEmbedding model).toFun
        (.answer space subject occurrence result)) :=
  .cons ⟨evaluation_enters_need model space subject⟩
    (.cons ⟨((needEmbedding model).step_iff _ _).2
      (RevisionedOccurrenceStep.found copy)⟩
      (.cons ⟨need_returns_evaluation model space subject occurrence result⟩
        (.refl _)))

/-- Every proof-relevant Prime route conserves the common occurrence-bag
interpretation.  The theorem is route-generic: direct interpretation, lazy
Need execution, and later certified routes all use the same step law. -/
theorem route_preserves_meaning (model : Model)
    {source target : (kernelGSLT model).Term}
    (route : Route (CarriedStep model) source target) :
    (kernelElaboration model).elaborate source =
      (kernelElaboration model).elaborate target :=
  Route.observe_eq_of_route (kernelElaboration model).elaborate
    (fun step => kernel_step_preserves_meaning model step.down) route

/-- The one-step extensional route preserves the complete answer bag. -/
theorem directRoute_preserves_meaning (model : Model)
    (space : model.Space) (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (model.base.source.occurrences space subject)) :
    (kernelElaboration model).elaborate
        ((evaluationKernelEmbedding model).toFun (.request space subject)) =
      (kernelElaboration model).elaborate
        ((evaluationKernelEmbedding model).toFun
          (.answer space subject occurrence result)) :=
  route_preserves_meaning model
    (directRoute model space subject result occurrence copy)

/-- The three-step lazy route preserves exactly the same complete answer bag,
including across both component boundaries. -/
theorem lazyRoute_preserves_meaning (model : Model)
    (space : model.Space) (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (model.base.source.occurrences space subject)) :
    (kernelElaboration model).elaborate
        ((evaluationKernelEmbedding model).toFun (.request space subject)) =
      (kernelElaboration model).elaborate
        ((evaluationKernelEmbedding model).toFun
          (.answer space subject occurrence result)) :=
  route_preserves_meaning model
    (lazyRoute model space subject result occurrence copy)

@[simp] theorem directRoute_length (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (model.base.source.occurrences space subject)) :
    (directRoute model space subject result occurrence copy).length = 1 :=
  rfl

@[simp] theorem lazyRoute_length (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (model.base.source.occurrences space subject)) :
    (lazyRoute model space subject result occurrence copy).length = 3 :=
  rfl

/-- The comparison is non-vacuous: its two routes are not definitionally or
propositionally equal, since their retained lengths differ. -/
theorem directRoute_ne_lazyRoute (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (model.base.source.occurrences space subject)) :
    directRoute model space subject result occurrence copy ≠
      lazyRoute model space subject result occurrence copy := by
  intro equal
  have lengths := congrArg Route.length equal
  simp at lengths

/-- The authored 2-generator says that direct interpretation and lazy
realization implement the same admitted occurrence.  The shared `copy`
evidence is load-bearing: unrelated routes receive no constructor. -/
inductive EvaluationCell (model : Model) :
    {source target : (kernelGSLT model).Term} →
      Route (CarriedStep model) source target →
      Route (CarriedStep model) source target → Type where
  | directLazy (space : model.Space) (subject result : Pattern)
      (occurrence : Nat)
      (copy : occurrence < Multiset.count result
        (model.base.source.occurrences space subject)) :
      EvaluationCell model
        (directRoute model space subject result occurrence copy)
        (lazyRoute model space subject result occurrence copy)

/-- The generated 2-cell comparing the direct and lazy routes. -/
def directLazyTwoCell (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (model.base.source.occurrences space subject)) :
    GeneratedTwoCell (EvaluationCell model)
      (directRoute model space subject result occurrence copy)
      (lazyRoute model space subject result occurrence copy) :=
  .generator (.directLazy space subject result occurrence copy)

/-- The direct/lazy comparison as a filled globular diamond.  Both branches
already reach the common answer, so their closing routes are identities. -/
def evaluationDiamond (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (model.base.source.occurrences space subject)) :
    FilledDiamond (CarriedStep model)
      (GeneratedTwoCell (EvaluationCell model))
      ((evaluationKernelEmbedding model).toFun (.request space subject))
      ((evaluationKernelEmbedding model).toFun
        (.answer space subject occurrence result))
      ((evaluationKernelEmbedding model).toFun
        (.answer space subject occurrence result)) where
  leftBranch := directRoute model space subject result occurrence copy
  rightBranch := lazyRoute model space subject result occurrence copy
  join := (evaluationKernelEmbedding model).toFun
    (.answer space subject occurrence result)
  closeLeft := .refl _
  closeRight := .refl _
  filler := by
    simpa using directLazyTwoCell model space subject result occurrence copy

end Mettapedia.Languages.MeTTa.Prime.EvaluationCoherence
