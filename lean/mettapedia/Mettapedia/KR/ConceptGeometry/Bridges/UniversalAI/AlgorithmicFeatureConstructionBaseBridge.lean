import Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidenceIndexedOSLFBridge
import Mettapedia.KR.ConceptOntology.ConstructionBase

/-!
# Algorithmic-feature construction bases

A finite algorithmic-feature experiment has a canonical construction-base
presentation:

* phenomena are indexed source observations;
* abstract contents are indexed feature programs;
* indexicality is the currently visible set of source indices; and
* incidence is checked strict-feature realization.

This is an exact repackaging of existing semantics.  Singleton construction-
base closure is precisely stage-local feature implication, while the full
closure ranges over the experiment's declared source-index carrier.  The
construction-base frontier therefore consists exactly of implications that
hold at the current observation stage but fail over that full carrier.

The full carrier of a finite experiment is not identified with all binary
sources.  A separate negative control shows that closure-completeness for the
declared carrier does not promote a sampled implication to global strict
algorithmic implication.
-/

namespace Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidence

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.KR.ConceptOntology
open Mettapedia.Logic.WorldModel.Algorithmic

universe u v

namespace FiniteFeatureExperiment

variable {SourceIndex : Type u} {FeatureIndex : Type v}
variable [Fintype SourceIndex] [Fintype FeatureIndex]

/-- A finite feature experiment viewed through the construction-base API. -/
def toConstructionBase
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex) : ConstructionBase where
  Phenomena := SourceIndex
  Abstract := FeatureIndex
  Indexicality := Set SourceIndex
  incidence := E.Relation
  visibleAt := id

@[simp]
theorem toConstructionBase_visibleAt
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (observed : Set SourceIndex) :
    E.toConstructionBase.visibleAt observed = observed :=
  rfl

@[simp]
theorem toConstructionBase_refines_iff
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (earlier later : Set SourceIndex) :
    E.toConstructionBase.Refines earlier later ↔ earlier ⊆ later :=
  Iff.rfl

/-- Singleton closure at one observation stage is exactly stage-local feature
implication. -/
theorem mem_toConstructionBase_closureAt_singleton_iff_implicationAt
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (observed : Set SourceIndex) (premise consequent : FeatureIndex) :
    consequent ∈ E.toConstructionBase.closureAt observed ({premise} : Set FeatureIndex) ↔
      E.ImplicationAt observed premise consequent := by
  change consequent ∈ sampledAttributeClosure observed E.Relation ({premise} : Set FeatureIndex) ↔ _
  rw [mem_sampledAttributeClosure_iff]
  constructor
  · intro closure source premiseAtSource
    exact ⟨premiseAtSource.1,
      closure source premiseAtSource.1 (by
        intro feature featureMem
        have featureEq : feature = premise := by simpa using featureMem
        subst feature
        exact premiseAtSource.2)⟩
  · intro implication source sourceObserved carriesPremise
    exact (implication source ⟨sourceObserved, carriesPremise premise (by simp)⟩).2

/-- The complete singleton closure ranges over every source index declared by
the experiment. -/
theorem mem_toConstructionBase_fullClosure_singleton_iff_implication
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (premise consequent : FeatureIndex) :
    consequent ∈ E.toConstructionBase.fullClosure ({premise} : Set FeatureIndex) ↔
      E.Implication premise consequent := by
  change consequent ∈ fullAttributeClosure E.Relation ({premise} : Set FeatureIndex) ↔ _
  rw [mem_fullAttributeClosure_iff]
  constructor
  · intro closure source carriesPremise
    exact closure source (by
      intro feature featureMem
      have featureEq : feature = premise := by simpa using featureMem
      subst feature
      exact carriesPremise)
  · intro implication source carriesPremise
    exact implication source (carriesPremise premise (by simp))

/-- Set-level form of the singleton closure correspondence. -/
theorem toConstructionBase_closureAt_singleton_eq_intent
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (observed : Set SourceIndex) (premise : FeatureIndex) :
    E.toConstructionBase.closureAt observed ({premise} : Set FeatureIndex) =
      (E.conceptAt observed premise).intent := by
  ext consequent
  exact E.mem_toConstructionBase_closureAt_singleton_iff_implicationAt
    observed premise consequent

/-- A frontier member is exactly a provisional implication: valid at the
current visible stage, invalid over the experiment's full source carrier. -/
theorem mem_toConstructionBase_frontierAt_singleton_iff
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (observed : Set SourceIndex) (premise consequent : FeatureIndex) :
    consequent ∈ E.toConstructionBase.frontierAt observed ({premise} : Set FeatureIndex) ↔
      E.ImplicationAt observed premise consequent ∧
        ¬ E.Implication premise consequent := by
  constructor
  · intro frontier
    exact ⟨
      (E.mem_toConstructionBase_closureAt_singleton_iff_implicationAt
        observed premise consequent).1 frontier.1,
      fun implication => frontier.2
        ((E.mem_toConstructionBase_fullClosure_singleton_iff_implication
          premise consequent).2 implication)⟩
  · rintro ⟨localImplication, notFullImplication⟩
    exact ⟨
      (E.mem_toConstructionBase_closureAt_singleton_iff_implicationAt
        observed premise consequent).2 localImplication,
      fun fullMember => notFullImplication
        ((E.mem_toConstructionBase_fullClosure_singleton_iff_implication
          premise consequent).1 fullMember)⟩

/-- Open-world status for a singleton premise is witnessed precisely by some
provisional implication in the current stage. -/
theorem toConstructionBase_openWorldAt_singleton_iff_exists
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (observed : Set SourceIndex) (premise : FeatureIndex) :
    E.toConstructionBase.openWorldAt observed ({premise} : Set FeatureIndex) ↔
      ∃ consequent,
        E.ImplicationAt observed premise consequent ∧
          ¬ E.Implication premise consequent := by
  constructor
  · intro openWorld
    have frontierNonempty :
        (E.toConstructionBase.frontierAt observed
          ({premise} : Set FeatureIndex)).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr openWorld
    obtain ⟨consequent, frontier⟩ := frontierNonempty
    exact ⟨consequent,
      (E.mem_toConstructionBase_frontierAt_singleton_iff
        observed premise consequent).1 frontier⟩
  · rintro ⟨consequent, provisional⟩
    exact Set.nonempty_iff_ne_empty.mp
      ⟨consequent,
        (E.mem_toConstructionBase_frontierAt_singleton_iff
          observed premise consequent).2 provisional⟩

/-- At the full declared source stage, local and experiment-wide implication
coincide. -/
theorem implicationAt_univ_iff_implication
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (premise consequent : FeatureIndex) :
    E.ImplicationAt Set.univ premise consequent ↔
      E.Implication premise consequent := by
  constructor
  · intro implication source premiseAtSource
    exact (implication source ⟨Set.mem_univ source, premiseAtSource⟩).2
  · intro implication source premiseAtSource
    exact ⟨Set.mem_univ source, implication source premiseAtSource.2⟩

/-- The full declared source stage is closure-complete relative to that
experiment. -/
theorem toConstructionBase_thatsAllAt_univ
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (premise : Set FeatureIndex) :
    E.toConstructionBase.thatsAllAt Set.univ premise := by
  rfl

/-- A globally certified strict feature implication belongs to the full
closure of every finite experiment representing its two feature programs. -/
theorem mem_toConstructionBase_fullClosure_of_strictFeatureImplication
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    {premise consequent : FeatureIndex}
    (implication : StrictFeatureImplication E.algorithm
      (E.feature premise) (E.feature consequent)) :
    consequent ∈ E.toConstructionBase.fullClosure ({premise} : Set FeatureIndex) := by
  exact (E.mem_toConstructionBase_fullClosure_singleton_iff_implication
    premise consequent).2 (E.implication_of_global implication)

/-- The construction-base closure law is the same one-sided restriction used
by the indexed OSLF growth translation. -/
theorem implicationGSLTAt_step_iff_mem_toConstructionBase_closureAt
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (observed : Set SourceIndex) (premise consequent : FeatureIndex) :
    (E.implicationGSLTAt observed).Step premise consequent ↔
      consequent ∈ E.toConstructionBase.closureAt observed
        ({premise} : Set FeatureIndex) := by
  exact (E.implicationGSLTAt_step_iff observed premise consequent).trans
    (E.mem_toConstructionBase_closureAt_singleton_iff_implicationAt
      observed premise consequent).symm

/-- Observation refinement simultaneously induces construction-base
refinement and the contravariant operational translation used by indexed
OSLF. -/
theorem constructionBase_refinement_and_implication_translation
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    {earlier later : Set SourceIndex} (growth : earlier ⊆ later) :
    E.toConstructionBase.Refines earlier later ∧
      Nonempty (OperationalTranslation
        (E.implicationGSLTAt later) (E.implicationGSLTAt earlier)) := by
  exact ⟨growth, ⟨E.implicationGrowthTranslation growth⟩⟩

end FiniteFeatureExperiment

end Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidence

namespace Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureConstructionBase

open Mettapedia.KR.ConceptOntology
open Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidence
open Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidenceGrowth
open Mettapedia.Logic.WorldModel.Algorithmic

/-! ## Nonvacuous frontier controls -/

/-- The early evidence stage is genuinely open-world: `true` is provisionally
implied by `false`, but the experiment's second source refutes it. -/
theorem growthCanary_early_openWorld :
    growthCanaryExperiment.toConstructionBase.openWorldAt
      earlyObserved ({false} : Set Bool) := by
  refine (growthCanaryExperiment.toConstructionBase_openWorldAt_singleton_iff_exists
    earlyObserved false).2 ⟨true, growthCanary_early_false_implies_true, ?_⟩
  intro fullImplication
  exact growthCanary_later_not_false_implies_true
    ((growthCanaryExperiment.implicationAt_univ_iff_implication false true).2
      fullImplication)

/-- The later stage sees the full declared source carrier and is therefore
closure-complete relative to this finite experiment. -/
theorem growthCanary_later_thatsAll :
    growthCanaryExperiment.toConstructionBase.thatsAllAt
      laterObserved ({false} : Set Bool) := by
  simpa [laterObserved] using
    growthCanaryExperiment.toConstructionBase_thatsAllAt_univ
      ({false} : Set Bool)

/-- The witnessed frontier member is discharged when the counterexample
becomes visible. -/
theorem growthCanary_frontier_member_discharged :
    true ∈ growthCanaryExperiment.toConstructionBase.frontierAt
        earlyObserved ({false} : Set Bool) ∧
      true ∉ growthCanaryExperiment.toConstructionBase.frontierAt
        laterObserved ({false} : Set Bool) := by
  constructor
  · exact (growthCanaryExperiment.mem_toConstructionBase_frontierAt_singleton_iff
      earlyObserved false true).2 ⟨growthCanary_early_false_implies_true, by
        intro fullImplication
        exact growthCanary_later_not_false_implies_true
          ((growthCanaryExperiment.implicationAt_univ_iff_implication false true).2
            fullImplication)⟩
  · intro laterFrontier
    exact growthCanary_later_not_false_implies_true
      ((growthCanaryExperiment.mem_toConstructionBase_frontierAt_singleton_iff
        laterObserved false true).1 laterFrontier).1

/-- Closure-completeness for a finite declared phenomenon carrier is not a
global totality claim over all binary sources. -/
theorem finite_fullClosure_does_not_promote_to_global_strict_implication :
    true ∈ canaryExperiment.toConstructionBase.fullClosure ({false} : Set Bool) ∧
      ¬ StrictFeatureImplication canaryExperiment.algorithm
        (canaryExperiment.feature false) (canaryExperiment.feature true) := by
  exact ⟨
    (canaryExperiment.mem_toConstructionBase_fullClosure_singleton_iff_implication
      false true).2 canary_sample_false_implies_true,
    canary_not_global_false_implies_true⟩

section AxiomAudit

#print axioms FiniteFeatureExperiment.toConstructionBase
#print axioms FiniteFeatureExperiment.mem_toConstructionBase_closureAt_singleton_iff_implicationAt
#print axioms FiniteFeatureExperiment.mem_toConstructionBase_frontierAt_singleton_iff
#print axioms FiniteFeatureExperiment.toConstructionBase_openWorldAt_singleton_iff_exists
#print axioms FiniteFeatureExperiment.implicationGSLTAt_step_iff_mem_toConstructionBase_closureAt
#print axioms FiniteFeatureExperiment.constructionBase_refinement_and_implication_translation
#print axioms growthCanary_early_openWorld
#print axioms growthCanary_later_thatsAll
#print axioms growthCanary_frontier_member_discharged
#print axioms finite_fullClosure_does_not_promote_to_global_strict_implication

end AxiomAudit

end Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureConstructionBase
