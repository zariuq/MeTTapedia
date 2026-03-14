import Mettapedia.Logic.HOL.Probabilistic.Semantics
import Mettapedia.ProbabilityTheory.HigherOrderProbability.Basic

/-!
# Hierarchical States for Probabilistic HOL

This module introduces the canonical semantic object for hierarchical and
infinite-order uncertainty over closed HOL formulas.

The design follows the higher-order probability/Kyburg line already formalized
in `Mettapedia/ProbabilityTheory/HigherOrderProbability/`, together with the
broader higher-order and infinite-order probability perspective of:

- Haim Gaifman, *A Theory of Higher Order Probabilities* (1986)
- David Atkinson and Jeanne Peijnenburg,
  *A Consistent Set of Infinite-Order Probabilities* (2013)

The key choice is to represent higher-order uncertainty as a probability
distribution over probability measures on a fixed indexed model space, rather
than as an explicit tower of nested probability syntax.
-/

namespace Mettapedia.Logic.HOL.Probabilistic

open Mettapedia.Logic.HOL
open scoped ENNReal

universe u v w x

abbrev ParametrizedDistribution :=
  Mettapedia.ProbabilityTheory.HigherOrderProbability.ParametrizedDistribution

variable {Base : Type u} {Const : Ty Base → Type v}

/-- A hierarchical probabilistic HOL state consists of a base indexed model
space together with a higher-order probability over measures on that space. -/
structure HierarchicalState (Base : Type u) (Const : Ty Base → Type v) where
  Θ : Type x
  instMeasurableSpace : MeasurableSpace Θ
  baseSpace : ModelSpace Base Const
  pd : ParametrizedDistribution Θ baseSpace.Idx

attribute [instance] HierarchicalState.instMeasurableSpace

namespace HierarchicalState

/-- The flattened predictive measure on the base model index space. -/
noncomputable def flattenedModelMeasure
    (H : HierarchicalState Base Const) :
    MeasureTheory.Measure H.baseSpace.Idx :=
  Mettapedia.ProbabilityTheory.HigherOrderProbability.ParametrizedDistribution.flatten H.pd

/-- Sentence probability inside one latent component of a hierarchical state. -/
noncomputable def componentSentenceProb
    (H : HierarchicalState Base Const)
    (θ : H.Θ)
    (φ : ClosedFormula Const) : ℝ≥0∞ :=
  sentenceProb H.baseSpace (H.pd.kernel θ) φ

/-- Hierarchy built from a deterministic selector into a base model space. -/
noncomputable def ofDeterministic
    {Θ : Type x} [MeasurableSpace Θ]
    (S : ModelSpace Base Const)
    (f : Θ → S.Idx)
    (hf : Measurable f)
    (μ : MeasureTheory.Measure Θ)
    [MeasureTheory.IsProbabilityMeasure μ] :
    HierarchicalState Base Const where
  Θ := Θ
  instMeasurableSpace := inferInstance
  baseSpace := S
  pd := {
    kernel := ProbabilityTheory.Kernel.deterministic f hf
    kernel_isMarkov := by infer_instance
    mixingMeasure := μ
    mixing_isProbability := inferInstance
  }

/-- Hierarchy with a single latent parameter and a constant predictive measure. -/
noncomputable def ofConstantMeasure
    (S : ModelSpace Base Const)
    (μIdx : MeasureTheory.Measure S.Idx)
    [MeasureTheory.IsProbabilityMeasure μIdx] :
    HierarchicalState Base Const where
  Θ := Unit
  instMeasurableSpace := inferInstance
  baseSpace := S
  pd := {
    kernel := ProbabilityTheory.Kernel.const Unit μIdx
    kernel_isMarkov := by infer_instance
    mixingMeasure := MeasureTheory.Measure.dirac ()
    mixing_isProbability := by infer_instance
  }

end HierarchicalState

end Mettapedia.Logic.HOL.Probabilistic
