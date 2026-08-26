import Mettapedia.Logic.WorldModel.Algorithmic
import Mettapedia.Logic.WorldModel.OpenEnded

/-!
# Uniform algorithmic features of open-ended worlds

This file lifts executable compression from one finite string to one coherent
family of finite observations of a primary world.  The feature and extractor
programs are fixed across stages.  Sources and residuals may grow, but both
must form prefix-coherent families.

This is stronger than asserting an unrelated compression witness at every
stage.  It also exposes an unavoidable resource law: unbounded residual
descriptions force unbounded source observations under strict compression.
-/

namespace Mettapedia.Logic.WorldModel.OpenEndedAlgorithmic

open KolmogorovComplexity
open Mettapedia.Computability
open Mettapedia.Logic.WorldModel.Algorithmic

universe uWorld

/-- One fixed executable feature decomposition, valid at every finite stage of
one primary open-ended world. -/
structure UniformCompressionFamily
    (U : ConditionalAlgorithm) (World : Type uWorld) where
  world : World
  sourceAt : Nat → World → BinString
  featureProgram : BinString
  descriptiveProgram : BinString
  residualAt : Nat → BinString
  sourceCoherent : ∀ stage,
    sourceAt stage world <+: sourceAt (stage + 1) world
  residualCoherent : ∀ stage,
    residualAt stage <+: residualAt (stage + 1)
  extracts : ∀ stage,
    residualAt stage ∈ U descriptiveProgram (sourceAt stage world)
  reconstructs : ∀ stage,
    sourceAt stage world ∈ U featureProgram (residualAt stage)
  compresses : ∀ stage,
    featureProgram.length + (residualAt stage).length <
      (sourceAt stage world).length

namespace UniformCompressionFamily

/-- Every stage is an ordinary strict compression step with the same feature
and extractor programs. -/
def compressionStep
    {U : ConditionalAlgorithm} {World : Type uWorld}
    (family : UniformCompressionFamily U World) (stage : Nat) :
    CompressionStep U (family.sourceAt stage family.world) where
  featureProgram := family.featureProgram
  descriptiveProgram := family.descriptiveProgram
  residual := family.residualAt stage
  extracts := family.extracts stage
  reconstructs := family.reconstructs stage
  compresses := family.compresses stage

theorem strictFeatureAt
    {U : ConditionalAlgorithm} {World : Type uWorld}
    (family : UniformCompressionFamily U World) (stage : Nat) :
    StrictFeatureOf U family.featureProgram
      (family.sourceAt stage family.world) := by
  let step := family.compressionStep stage
  exact ⟨
    { descriptiveProgram := step.descriptiveProgram,
      residual := step.residual },
    compressionStep_realizes_strictFeatureSemantics step⟩

/-- An unbounded residual family forces unbounded observed source lengths. -/
theorem sourceLengths_unbounded_of_residualLengths_unbounded
    {U : ConditionalAlgorithm} {World : Type uWorld}
    (family : UniformCompressionFamily U World)
    (unboundedResidual : ∀ bound, ∃ stage,
      bound < (family.residualAt stage).length) :
    ∀ bound, ∃ stage,
      bound < (family.sourceAt stage family.world).length := by
  intro bound
  obtain ⟨stage, residualLarge⟩ := unboundedResidual bound
  exact ⟨stage, residualLarge.trans
    (by have := family.compresses stage; omega)⟩

/-- Bounded source observations and unbounded residual descriptions cannot
coexist in a strict uniform compression family. -/
theorem not_boundedSource_of_unboundedResidual
    {U : ConditionalAlgorithm} {World : Type uWorld}
    (family : UniformCompressionFamily U World)
    (unboundedResidual : ∀ bound, ∃ stage,
      bound < (family.residualAt stage).length) :
    ¬ ∃ bound, ∀ stage,
      (family.sourceAt stage family.world).length ≤ bound := by
  rintro ⟨bound, boundedSource⟩
  obtain ⟨stage, sourceLarge⟩ :=
    family.sourceLengths_unbounded_of_residualLengths_unbounded
      unboundedResidual bound
  exact (Nat.not_lt_of_ge (boundedSource stage)) sourceLarge

end UniformCompressionFamily

/-! ## A nondegenerate open-ended compression family -/

/-- Observe the first `2 * stage + 4` bits of a primary Cantor-space world. -/
def expandingSourceAt (stage : Nat) (world : CantorSpace) : BinString :=
  List.ofFn (fun coordinate : Fin (2 * stage + 4) => world coordinate)

/-- A fixed generator/extractor pair for the repetitive-world control.

The generator expands a unary residual of length `n` into `2n+4` true bits.
The extractor recovers a unary residual from the source length. -/
def repetitiveCompressionAlgorithm : ConditionalAlgorithm :=
  fun program condition =>
    if program = [false] then
      Part.some (List.replicate (2 * condition.length + 4) true)
    else if program = [true] then
      Part.some (List.replicate ((condition.length - 4) / 2) true)
    else Part.none

/-- The primary infinite world in the positive control. -/
def constantTrueWorld : CantorSpace := fun _ => true

private theorem expandingSourceAt_constantTrue (stage : Nat) :
    expandingSourceAt stage constantTrueWorld =
      List.replicate (2 * stage + 4) true := by
  unfold expandingSourceAt constantTrueWorld
  exact List.ofFn_const _ _

/-- One fixed feature and extractor strictly compress every declared finite
observation of the constant-true primary world. -/
def repetitiveUniformCompression :
    UniformCompressionFamily repetitiveCompressionAlgorithm CantorSpace where
  world := constantTrueWorld
  sourceAt := expandingSourceAt
  featureProgram := [false]
  descriptiveProgram := [true]
  residualAt := fun stage => List.replicate stage true
  sourceCoherent := by
    intro stage
    rw [expandingSourceAt_constantTrue, expandingSourceAt_constantTrue]
    refine ⟨List.replicate 2 true, ?_⟩
    rw [← List.replicate_add]
    congr 1
  residualCoherent := by
    intro stage
    refine ⟨List.replicate 1 true, ?_⟩
    rw [← List.replicate_add]
  extracts := by
    intro stage
    simp [repetitiveCompressionAlgorithm, expandingSourceAt_constantTrue]
  reconstructs := by
    intro stage
    simp [repetitiveCompressionAlgorithm, expandingSourceAt_constantTrue]
  compresses := by
    intro stage
    rw [expandingSourceAt_constantTrue]
    simp
    omega

theorem repetitiveUniformCompression_strictFeatureAt (stage : Nat) :
    StrictFeatureOf repetitiveCompressionAlgorithm [false]
      (expandingSourceAt stage constantTrueWorld) :=
  repetitiveUniformCompression.strictFeatureAt stage

theorem repetitiveUniformCompression_residualLengths_unbounded :
    ∀ bound, ∃ stage,
      bound < (repetitiveUniformCompression.residualAt stage).length := by
  intro bound
  exact ⟨bound + 1, by simp [repetitiveUniformCompression]⟩

theorem repetitiveUniformCompression_sourceLengths_unbounded :
    ∀ bound, ∃ stage,
      bound < (repetitiveUniformCompression.sourceAt stage
        repetitiveUniformCompression.world).length :=
  repetitiveUniformCompression.sourceLengths_unbounded_of_residualLengths_unbounded
    repetitiveUniformCompression_residualLengths_unbounded

/-! ## Incoherent finite-stage control -/

/-- Alternating four-bit snapshots.  Each is a finite string, but the sequence
does not form prefixes of one another. -/
def alternatingSnapshots (stage : Nat) : BinString :=
  if stage % 2 = 0 then
    [true, true, true, true]
  else
    [false, false, false, false]

/-- Merely presenting one finite object at every stage does not produce an
open-ended prefix family. -/
theorem alternatingSnapshots_not_coherent :
    ¬ ∀ stage, alternatingSnapshots stage <+:
      alternatingSnapshots (stage + 1) := by
  intro coherent
  have h := coherent 0
  simp [alternatingSnapshots] at h

#print axioms repetitiveUniformCompression_strictFeatureAt
#print axioms repetitiveUniformCompression_sourceLengths_unbounded
#print axioms alternatingSnapshots_not_coherent

end Mettapedia.Logic.WorldModel.OpenEndedAlgorithmic
