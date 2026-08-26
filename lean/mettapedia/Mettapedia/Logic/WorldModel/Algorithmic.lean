import Mettapedia.Computability.KolmogorovComplexity.CompressiveFeature
import Mettapedia.Logic.WorldModel.Generative

/-!
# Algorithmic generative world models

This file specializes relational generative world models to executable
feature/residual decompositions.  A model is a feature program, residual data
also carries the program that extracts it from a world, and realization checks
both extraction and reconstruction.

Strict compression and additive-slack compression remain separate semantics.
This prevents a logarithmic-overhead containment result from being used as an
exact feature implication without an independently proved margin.
-/

namespace Mettapedia.Logic.WorldModel.Algorithmic

open KolmogorovComplexity
open Mettapedia.Logic.WorldModel.Generative

/-- Proof-relevant residual data: the residual itself and an executable program
that extracts it from the candidate world. -/
structure ResidualCertificate where
  descriptiveProgram : BinString
  residual : BinString
deriving DecidableEq

/-- Strict feature realization.  The feature program reconstructs the world
from the residual, the descriptive program extracts that same residual, and
the feature plus residual is strictly shorter than the world. -/
def strictFeatureSemantics (U : ConditionalAlgorithm) :
    Semantics BinString ResidualCertificate BinString where
  admissible := fun feature certificate =>
    ∃ source,
      certificate.residual ∈ U certificate.descriptiveProgram source ∧
      source ∈ U feature certificate.residual ∧
      feature.length + certificate.residual.length < source.length
  realizes := fun feature certificate source =>
    certificate.residual ∈ U certificate.descriptiveProgram source ∧
    source ∈ U feature certificate.residual ∧
    feature.length + certificate.residual.length < source.length
  realizes_admissible := by
    intro feature certificate source realizesSource
    exact ⟨source, realizesSource⟩

/-- Slack-indexed feature realization.  The slack is part of the semantics,
not erased evidence. -/
def slackFeatureSemantics (U : ConditionalAlgorithm) (slack : Nat) :
    Semantics BinString ResidualCertificate BinString where
  admissible := fun feature certificate =>
    ∃ source,
      certificate.residual ∈ U certificate.descriptiveProgram source ∧
      source ∈ U feature certificate.residual ∧
      feature.length + certificate.residual.length < source.length + slack
  realizes := fun feature certificate source =>
    certificate.residual ∈ U certificate.descriptiveProgram source ∧
    source ∈ U feature certificate.residual ∧
    feature.length + certificate.residual.length < source.length + slack
  realizes_admissible := by
    intro feature certificate source realizesSource
    exact ⟨source, realizesSource⟩

/-- A strict compression step is exactly a realization in the strict
algorithmic world-model semantics. -/
theorem compressionStep_realizes_strictFeatureSemantics
    {U : ConditionalAlgorithm} {source : BinString}
    (step : CompressionStep U source) :
    (strictFeatureSemantics U).realizes step.featureProgram
      { descriptiveProgram := step.descriptiveProgram, residual := step.residual }
      source := by
  exact ⟨step.extracts, step.reconstructs, step.compresses⟩

/-- A slack compression step is exactly a realization in the semantics at its
declared slack. -/
theorem slackCompressionStep_realizes_slackFeatureSemantics
    {U : ConditionalAlgorithm} {source : BinString} {slack : Nat}
    (step : SlackCompressionStep U source slack) :
    (slackFeatureSemantics U slack).realizes step.featureProgram
      { descriptiveProgram := step.descriptiveProgram, residual := step.residual }
      source := by
  exact ⟨step.extracts, step.reconstructs, step.compressesWithSlack⟩

/-- Exact compression is zero-slack compression at the same proof-relevant
residual certificate. -/
theorem strictRealization_to_zeroSlack
    {U : ConditionalAlgorithm} {feature source : BinString}
    {certificate : ResidualCertificate}
    (realizesSource :
      (strictFeatureSemantics U).realizes feature certificate source) :
    (slackFeatureSemantics U 0).realizes feature certificate source := by
  simpa [strictFeatureSemantics, slackFeatureSemantics] using realizesSource

/-- Increasing a slack budget cannot destroy a realization. -/
theorem slackRealization_mono
    {U : ConditionalAlgorithm} {feature source : BinString}
    {certificate : ResidualCertificate} {small large : Nat}
    (hslack : small ≤ large)
    (realizesSource :
      (slackFeatureSemantics U small).realizes feature certificate source) :
    (slackFeatureSemantics U large).realizes feature certificate source := by
  rcases realizesSource with ⟨extracts, reconstructs, compresses⟩
  exact ⟨extracts, reconstructs, by omega⟩

/-- `source` has `feature` as a strict executable feature. -/
def StrictFeatureOf (U : ConditionalAlgorithm)
    (feature source : BinString) : Prop :=
  ∃ certificate, (strictFeatureSemantics U).realizes feature certificate source

/-- `source` has `feature` with the declared additive slack. -/
def SlackFeatureOf (U : ConditionalAlgorithm) (slack : Nat)
    (feature source : BinString) : Prop :=
  ∃ certificate,
    (slackFeatureSemantics U slack).realizes feature certificate source

theorem strictFeatureOf_to_zeroSlack
    {U : ConditionalAlgorithm} {feature source : BinString}
    (h : StrictFeatureOf U feature source) :
    SlackFeatureOf U 0 feature source := by
  obtain ⟨certificate, realizesSource⟩ := h
  exact ⟨certificate, strictRealization_to_zeroSlack realizesSource⟩

theorem slackFeatureOf_mono
    {U : ConditionalAlgorithm} {feature source : BinString}
    {small large : Nat} (hslack : small ≤ large)
    (h : SlackFeatureOf U small feature source) :
    SlackFeatureOf U large feature source := by
  obtain ⟨certificate, realizesSource⟩ := h
  exact ⟨certificate, slackRealization_mono hslack realizesSource⟩

/-- Exact algorithmic feature implication: every world strictly generated by
the premise feature also has the consequent as a strict feature. -/
def StrictFeatureImplication (U : ConditionalAlgorithm)
    (premise consequent : BinString) : Prop :=
  Entails (strictFeatureSemantics U) premise (StrictFeatureOf U consequent)

theorem strictFeatureImplication_refl
    (U : ConditionalAlgorithm) (feature : BinString) :
    StrictFeatureImplication U feature feature := by
  intro certificate source realizesSource
  exact ⟨certificate, realizesSource⟩

theorem strictFeatureImplication_trans
    {U : ConditionalAlgorithm} {first second third : BinString}
    (h₁₂ : StrictFeatureImplication U first second)
    (h₂₃ : StrictFeatureImplication U second third) :
    StrictFeatureImplication U first third := by
  intro firstCertificate source realizesFirst
  obtain ⟨secondCertificate, realizesSecond⟩ :=
    h₁₂ firstCertificate source realizesFirst
  exact h₂₃ secondCertificate source realizesSecond

/-! ## Positive and negative controls -/

theorem finiteCompressionStep_strictFeature :
    StrictFeatureOf finiteCompressionAlgorithm
      finiteCompressionStep.featureProgram fourTrue := by
  exact ⟨
    { descriptiveProgram := finiteCompressionStep.descriptiveProgram,
      residual := finiteCompressionStep.residual },
    compressionStep_realizes_strictFeatureSemantics finiteCompressionStep⟩

theorem literalSlackStep_is_slackFeature :
    SlackFeatureOf literalResidualAlgorithm 1
      literalSlackStep.featureProgram fourTrue := by
  exact ⟨
    { descriptiveProgram := literalSlackStep.descriptiveProgram,
      residual := literalSlackStep.residual },
    slackCompressionStep_realizes_slackFeatureSemantics literalSlackStep⟩

/-- The literal boundary example is not rescued by choosing a different
descriptive program or residual: its reconstruction forces the empty residual,
so the feature is exactly as long as the source. -/
theorem literalSlackFeature_not_strict :
    ¬ StrictFeatureOf literalResidualAlgorithm
      literalSlackStep.featureProgram fourTrue := by
  rintro ⟨certificate, extracts, _reconstructs, compresses⟩
  have residualEmpty : certificate.residual = [] := by
    by_cases hprogram : certificate.descriptiveProgram = []
    · simp [literalResidualAlgorithm, hprogram] at extracts
      exact extracts
    · simp [literalResidualAlgorithm, hprogram, fourTrue] at extracts
  rw [residualEmpty] at compresses
  simp [literalSlackStep, fourTrue] at compresses

/-- Slack featurehood cannot in general be collapsed into strict
featurehood. -/
theorem slackFeature_does_not_imply_strict :
    SlackFeatureOf literalResidualAlgorithm 1
      literalSlackStep.featureProgram fourTrue ∧
    ¬ StrictFeatureOf literalResidualAlgorithm
      literalSlackStep.featureProgram fourTrue :=
  ⟨literalSlackStep_is_slackFeature, literalSlackFeature_not_strict⟩

#print axioms strictFeatureImplication_trans
#print axioms finiteCompressionStep_strictFeature
#print axioms slackFeature_does_not_imply_strict

end Mettapedia.Logic.WorldModel.Algorithmic
