import Mettapedia.Logic.WorldModel.Algorithmic

/-!
# Compression-preserving feature containment

Bare inclusion between the images of two generator programs does not preserve
featurehood: the second generator may be too long to compress the objects it
generates.  This file therefore states family-level implication with an
explicit, object-indexed slack budget.

The budgeted conclusion is the appropriate target for results whose overhead
is logarithmic in a witness length.  It remains a different type from strict
feature implication, and no asymptotic statement is silently promoted to exact
compression.
-/

namespace Mettapedia.Logic.WorldModel.FeatureContainment

open KolmogorovComplexity
open Mettapedia.Logic.WorldModel.Algorithmic
open Mettapedia.Logic.WorldModel.Generative

/-- Membership in the raw image of a generator program, without an extractor
or compression requirement. -/
def GeneratedBy (U : ConditionalAlgorithm)
    (feature source : BinString) : Prop :=
  ∃ residual, source ∈ U feature residual

/-- Bare image inclusion between two generator programs. -/
def ImageIncluded (U : ConditionalAlgorithm)
    (premise consequent : BinString) : Prop :=
  ∀ source, GeneratedBy U premise source → GeneratedBy U consequent source

/-- Every strict instance of `premise` has `consequent` as an executable
feature at the slack budget declared for that source. -/
def FeatureImplicationWithBudget (U : ConditionalAlgorithm)
    (budget : BinString → Nat) (premise consequent : BinString) : Prop :=
  ∀ certificate source,
    (strictFeatureSemantics U).realizes premise certificate source →
    SlackFeatureOf U (budget source) consequent source

/-- A nonvacuous implication packages the witness that the premise really is a
feature of at least one source. -/
def WitnessedFeatureImplicationWithBudget (U : ConditionalAlgorithm)
    (budget : BinString → Nat) (premise consequent witness : BinString) : Prop :=
  StrictFeatureOf U premise witness ∧
    FeatureImplicationWithBudget U budget premise consequent

theorem strictFeatureImplication_to_zeroBudget
    {U : ConditionalAlgorithm} {premise consequent : BinString}
    (implication : StrictFeatureImplication U premise consequent) :
    FeatureImplicationWithBudget U (fun _ => 0) premise consequent := by
  intro certificate source realizesPremise
  exact strictFeatureOf_to_zeroSlack
    (implication certificate source realizesPremise)

theorem featureImplicationWithBudget_mono
    {U : ConditionalAlgorithm} {small large : BinString → Nat}
    {premise consequent : BinString}
    (hle : ∀ source, small source ≤ large source)
    (implication : FeatureImplicationWithBudget U small premise consequent) :
    FeatureImplicationWithBudget U large premise consequent := by
  intro certificate source realizesPremise
  exact slackFeatureOf_mono (hle source)
    (implication certificate source realizesPremise)

theorem strictFeatureOf_generatedBy
    {U : ConditionalAlgorithm} {feature source : BinString}
    (featureOf : StrictFeatureOf U feature source) :
    GeneratedBy U feature source := by
  obtain ⟨certificate, _extracts, reconstructs, _compresses⟩ := featureOf
  exact ⟨certificate.residual, reconstructs⟩

/-! ## Image inclusion does not preserve compression -/

/-- A finite table with a short and a long generator for the same source. -/
def imageCompressionAlgorithm : ConditionalAlgorithm :=
  fun program condition =>
    if program = [false] ∧ condition = [] then Part.some fourTrue
    else if program = fourTrue ∧ condition = [] then Part.some fourTrue
    else if program = [true] ∧ condition = fourTrue then Part.some []
    else Part.none

def shortImageCompressionStep :
    CompressionStep imageCompressionAlgorithm fourTrue where
  featureProgram := [false]
  descriptiveProgram := [true]
  residual := []
  extracts := by simp [imageCompressionAlgorithm, fourTrue]
  reconstructs := by simp [imageCompressionAlgorithm, fourTrue]
  compresses := by simp [fourTrue]

theorem shortGenerator_strictFeature :
    StrictFeatureOf imageCompressionAlgorithm [false] fourTrue := by
  exact ⟨
    { descriptiveProgram := [true], residual := [] },
    compressionStep_realizes_strictFeatureSemantics shortImageCompressionStep⟩

theorem shortImage_included_in_longImage :
    ImageIncluded imageCompressionAlgorithm [false] fourTrue := by
  intro source
  rintro ⟨residual, generated⟩
  by_cases residualEmpty : residual = []
  · subst residual
    have sourceEq : source = fourTrue := by
      simpa [imageCompressionAlgorithm, fourTrue] using generated
    subst source
    exact ⟨[], by simp [imageCompressionAlgorithm, fourTrue]⟩
  · simp [imageCompressionAlgorithm, residualEmpty, fourTrue] at generated

theorem longGenerator_slackFeature :
    SlackFeatureOf imageCompressionAlgorithm 1 fourTrue fourTrue := by
  refine ⟨{ descriptiveProgram := [true], residual := [] }, ?_⟩
  exact ⟨by simp [imageCompressionAlgorithm, fourTrue],
    by simp [imageCompressionAlgorithm, fourTrue], by simp [fourTrue]⟩

theorem longGenerator_not_strictFeature :
    ¬ StrictFeatureOf imageCompressionAlgorithm fourTrue fourTrue := by
  rintro ⟨certificate, _extracts, reconstructs, compresses⟩
  by_cases residualEmpty : certificate.residual = []
  · rw [residualEmpty] at compresses
    simp [fourTrue] at compresses
  · simp [imageCompressionAlgorithm, residualEmpty, fourTrue] at reconstructs

theorem shortImpliesLong_with_oneBitBudget :
    WitnessedFeatureImplicationWithBudget imageCompressionAlgorithm
      (fun _ => 1) [false] fourTrue fourTrue := by
  refine ⟨shortGenerator_strictFeature, ?_⟩
  intro certificate source realizesPremise
  rcases realizesPremise with ⟨_extracts, reconstructs, _compresses⟩
  by_cases residualEmpty : certificate.residual = []
  · rw [residualEmpty] at reconstructs
    have sourceEq : source = fourTrue := by
      simpa [imageCompressionAlgorithm, fourTrue] using reconstructs
    subst source
    exact longGenerator_slackFeature
  · simp [imageCompressionAlgorithm, residualEmpty, fourTrue] at reconstructs

/-- Even nonvacuous image inclusion does not imply strict feature implication:
the longer generator reaches the same source but fails the compression
condition. -/
theorem imageInclusion_does_not_imply_strictFeatureImplication :
    ImageIncluded imageCompressionAlgorithm [false] fourTrue ∧
    StrictFeatureOf imageCompressionAlgorithm [false] fourTrue ∧
    ¬ StrictFeatureImplication imageCompressionAlgorithm [false] fourTrue := by
  refine ⟨shortImage_included_in_longImage, shortGenerator_strictFeature, ?_⟩
  intro implication
  exact longGenerator_not_strictFeature
    (implication
      { descriptiveProgram := [true], residual := [] }
      fourTrue
      (compressionStep_realizes_strictFeatureSemantics
        shortImageCompressionStep))

/-- One-bit slack is genuinely weaker than strict family implication, even
when the premise has a witnessed strict instance. -/
theorem budgetedImplication_does_not_imply_strictFeatureImplication :
    WitnessedFeatureImplicationWithBudget imageCompressionAlgorithm
      (fun _ => 1) [false] fourTrue fourTrue ∧
    ¬ StrictFeatureImplication imageCompressionAlgorithm [false] fourTrue := by
  exact ⟨shortImpliesLong_with_oneBitBudget,
    imageInclusion_does_not_imply_strictFeatureImplication.2.2⟩

/-- There is no uniform rule promoting nonvacuous image inclusion to strict
feature implication.  The obstruction is quantitative, not vacuity: the
premise has a witnessed strict instance, while the longer consequent reaches
the same image without compressing it. -/
theorem no_uniform_imageInclusion_to_strictFeatureImplication :
    ¬ (∀ (U : ConditionalAlgorithm) (premise consequent : BinString),
      ImageIncluded U premise consequent →
      (∃ witness, StrictFeatureOf U premise witness) →
      StrictFeatureImplication U premise consequent) := by
  intro upgrade
  have promoted := upgrade imageCompressionAlgorithm [false] fourTrue
    shortImage_included_in_longImage ⟨fourTrue, shortGenerator_strictFeature⟩
  exact imageInclusion_does_not_imply_strictFeatureImplication.2.2 promoted

/-- Even a witnessed one-bit budgeted implication has no uniform promotion to
strict implication.  Consequently an additive coding-overhead theorem must
retain its slack unless a separate compression-margin premise is supplied. -/
theorem no_uniform_oneBitBudget_to_strictFeatureImplication :
    ¬ (∀ (U : ConditionalAlgorithm) (premise consequent witness : BinString),
      WitnessedFeatureImplicationWithBudget U (fun _ => 1)
        premise consequent witness →
      StrictFeatureImplication U premise consequent) := by
  intro upgrade
  have promoted := upgrade imageCompressionAlgorithm [false] fourTrue fourTrue
    shortImpliesLong_with_oneBitBudget
  exact imageInclusion_does_not_imply_strictFeatureImplication.2.2 promoted

#print axioms strictFeatureImplication_to_zeroBudget
#print axioms shortImpliesLong_with_oneBitBudget
#print axioms imageInclusion_does_not_imply_strictFeatureImplication
#print axioms budgetedImplication_does_not_imply_strictFeatureImplication
#print axioms no_uniform_imageInclusion_to_strictFeatureImplication
#print axioms no_uniform_oneBitBudget_to_strictFeatureImplication

end Mettapedia.Logic.WorldModel.FeatureContainment
