import Mettapedia.Computability.KolmogorovComplexity.CompressiveFeature
import Mettapedia.Computability.KolmogorovComplexity.ConditionalPrefixBridge

/-!
# Incremental compression and conditional algorithmic probability

Solomonoff induction and incremental compression use program length for
different mathematical roles.  A Solomonoff prior assigns mass to every
program that produces an output.  A compressive feature additionally requires
an executable residual extractor and a strict two-part description bound.

This file proves their exact overlap.  A compressive feature implemented by a
conditional prefix machine gives both

* a conditional shortest-program bound, and
* an explicit contribution to conditional algorithmic probability.

The converse does not hold: a program can contribute algorithmic probability
without being a strict compressive feature.  The finite controls below expose
that separation.

References:

* Ray Solomonoff, "A Formal Theory of Inductive Inference" (1964).
* Arthur Franz, Anton Antonenko, and Anton Soletskyi, "A Theory of
  Incremental Compression" (2021).
-/

namespace Mettapedia.UniversalAI.IncrementalCompressionBridge

open KolmogorovComplexity

/-- Interpret the deterministic output of a conditional prefix machine as a
single-valued conditional algorithm. -/
def prefixMachineAlgorithm (U : ConditionalPrefixFreeMachine) :
    ConditionalAlgorithm :=
  fun program condition => Part.ofOption (U.compute program condition)

/-- A reconstructing feature program is a conditional description of its
source, so conditional prefix complexity is no greater than its length. -/
theorem compressionStep_conditionalComplexity_le_featureProgram
    {U : ConditionalPrefixFreeMachine} {source : BinString}
    (step : CompressionStep (prefixMachineAlgorithm U) source) :
    Kc[U](source | step.residual) <= step.featureProgram.length := by
  apply conditionalComplexity_le_program_length U step.residual source
    step.featureProgram
  simpa [IsProgram, prefixMachineAlgorithm] using step.reconstructs

/-- Strict incremental compression therefore gives a strict two-part bound
using conditional prefix complexity itself, not only the exhibited program. -/
theorem compressionStep_conditionalTwoPartCode_lt_source
    {U : ConditionalPrefixFreeMachine} {source : BinString}
    (step : CompressionStep (prefixMachineAlgorithm U) source) :
    Kc[U](source | step.residual) + step.residual.length < source.length := by
  exact lt_of_le_of_lt
    (Nat.add_le_add_right
      (compressionStep_conditionalComplexity_le_featureProgram step)
      step.residual.length)
    step.compresses

/-- A single witnessed program contributes exactly its dyadic weight to the
finite algorithmic probability formed from that singleton program set. -/
theorem singletonAlgorithmicProbability_eq_programWeight
    (U : ConditionalPrefixFreeMachine) (condition program source : BinString)
    (computes : (conditionalSlice U condition).compute program = some source) :
    Mettapedia.UniversalAI.SolomonoffPrior.algorithmicProbability
        (conditionalSlice U condition) {program} source =
      (2 : Real) ^ (-(program.length : Int)) := by
  have added :=
    Mettapedia.UniversalAI.SolomonoffPrior.algorithmicProbability_add_program
      (conditionalSlice U condition) ({} : Finset BinString) program source
      (by simp) computes
  simpa [Mettapedia.UniversalAI.SolomonoffPrior.algorithmicProbability] using added

/-- The feature program contributes its dyadic weight to the finite
conditional algorithmic probability of the source. -/
theorem compressionStep_singletonAlgorithmicProbability_eq_featureWeight
    {U : ConditionalPrefixFreeMachine} {source : BinString}
    (step : CompressionStep (prefixMachineAlgorithm U) source) :
    Mettapedia.UniversalAI.SolomonoffPrior.algorithmicProbability
        (conditionalSlice U step.residual) {step.featureProgram} source =
      (2 : Real) ^ (-(step.featureProgram.length : Int)) := by
  apply singletonAlgorithmicProbability_eq_programWeight
  simpa [conditionalSlice, prefixMachineAlgorithm] using step.reconstructs

/-! ## Finite positive and negative controls -/

/-- A one-program conditional prefix machine.  The program `[false]`
reconstructs `source` from the empty residual and extracts that residual from
`source`. -/
def singletonFeatureMachine (source : BinString) :
    ConditionalPrefixFreeMachine where
  compute := fun program condition =>
    if program = [false] then
      if condition = [] then some source
      else if condition = source then some []
      else none
    else none
  prefix_free := by
    intro condition program extension _prefix distinct halts
    by_cases hp : program = [false]
    · have hq : extension ≠ [false] := by
        intro h
        exact distinct (hp.trans h.symm)
      simp [hq]
    · simp [hp] at halts

/-- A genuine strict prefix-machine feature: one program bit and an empty
residual reconstruct four source bits. -/
def strictPrefixCompressionStep :
    CompressionStep
      (prefixMachineAlgorithm (singletonFeatureMachine fourTrue)) fourTrue where
  featureProgram := [false]
  descriptiveProgram := [false]
  residual := []
  extracts := by
    simp [prefixMachineAlgorithm, singletonFeatureMachine, fourTrue]
  reconstructs := by
    simp [prefixMachineAlgorithm, singletonFeatureMachine, fourTrue]
  compresses := by simp [fourTrue]

/-- The positive control simultaneously has a strict conditional two-part
code and the dyadic mass contributed by its feature program. -/
theorem strictPrefixCompression_has_complexityAndMass :
    Kc[singletonFeatureMachine fourTrue](fourTrue | []) < fourTrue.length ∧
    Mettapedia.UniversalAI.SolomonoffPrior.algorithmicProbability
        (conditionalSlice (singletonFeatureMachine fourTrue) []) {[false]} fourTrue =
          (2 : Real) ^ (-1 : Int) := by
  constructor
  · simpa [strictPrefixCompressionStep] using
      compressionStep_conditionalTwoPartCode_lt_source strictPrefixCompressionStep
  · simpa [strictPrefixCompressionStep] using
      compressionStep_singletonAlgorithmicProbability_eq_featureWeight
        strictPrefixCompressionStep

/-- One bit used by the non-compression control. -/
def oneTrue : BinString := [true]

/-- The same one-bit generator is only a one-bit-slack description of a
one-bit source; it is not a strict compression step. -/
def boundaryPrefixSlackStep :
    SlackCompressionStep
      (prefixMachineAlgorithm (singletonFeatureMachine oneTrue)) oneTrue 1 where
  featureProgram := [false]
  descriptiveProgram := [false]
  residual := []
  extracts := by
    simp [prefixMachineAlgorithm, singletonFeatureMachine, oneTrue]
  reconstructs := by
    simp [prefixMachineAlgorithm, singletonFeatureMachine, oneTrue]
  compressesWithSlack := by simp [oneTrue]

/-- Negative control: the boundary program contributes positive dyadic mass,
but the exhibited description is not a strict compressive feature. -/
theorem programMass_does_not_imply_strictCompression :
    Mettapedia.UniversalAI.SolomonoffPrior.algorithmicProbability
        (conditionalSlice (singletonFeatureMachine oneTrue) []) {[false]} oneTrue =
        (2 : Real) ^ (-1 : Int) ∧
      ¬ (boundaryPrefixSlackStep.featureProgram.length +
        boundaryPrefixSlackStep.residual.length < oneTrue.length) := by
  constructor
  · apply singletonAlgorithmicProbability_eq_programWeight
    simp [conditionalSlice, singletonFeatureMachine, oneTrue]
  · simp [boundaryPrefixSlackStep, oneTrue]

#print axioms compressionStep_conditionalComplexity_le_featureProgram
#print axioms compressionStep_conditionalTwoPartCode_lt_source
#print axioms compressionStep_singletonAlgorithmicProbability_eq_featureWeight
#print axioms strictPrefixCompression_has_complexityAndMass
#print axioms programMass_does_not_imply_strictCompression

end Mettapedia.UniversalAI.IncrementalCompressionBridge
