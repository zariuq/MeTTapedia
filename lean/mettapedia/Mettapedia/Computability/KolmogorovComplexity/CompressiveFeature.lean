import Mettapedia.Computability.KolmogorovComplexity.ConditionalPlainComplexity

/-!
# Compressive features and residual decompositions

A compressive feature is an executable two-way decomposition, not merely a
function whose image contains an object.  A feature program reconstructs the
source from a residual; a descriptive-map program extracts that residual from
the source; and their combined description is strictly shorter than the source.

The strict definition follows the feature/descriptive-map condition in the
incremental-compression literature.  Logarithmic-slack results use a separate
structure so that an approximate implication cannot silently inhabit the exact
feature interface.
-/

namespace KolmogorovComplexity

open scoped Classical

/-- A strict executable compression step for `source` relative to `U`.

Both directions are proof-relevant: `extracts` rules out an arbitrary residual
chosen only because reconstruction happens to work. -/
structure CompressionStep (U : ConditionalAlgorithm) (source : BinString) where
  featureProgram : BinString
  descriptiveProgram : BinString
  residual : BinString
  extracts : residual ∈ U descriptiveProgram source
  reconstructs : source ∈ U featureProgram residual
  compresses : featureProgram.length + residual.length < source.length

/-- A compression step whose description may exceed the source by at most the
declared additive slack.  This is intentionally not a `CompressionStep`. -/
structure SlackCompressionStep
    (U : ConditionalAlgorithm) (source : BinString) (slack : Nat) where
  featureProgram : BinString
  descriptiveProgram : BinString
  residual : BinString
  extracts : residual ∈ U descriptiveProgram source
  reconstructs : source ∈ U featureProgram residual
  compressesWithSlack :
    featureProgram.length + residual.length < source.length + slack

namespace CompressionStep

theorem feature_length_lt
    {U : ConditionalAlgorithm} {source : BinString}
    (step : CompressionStep U source) :
    step.featureProgram.length < source.length := by
  have h := step.compresses
  omega

theorem residual_length_lt
    {U : ConditionalAlgorithm} {source : BinString}
    (step : CompressionStep U source) :
    step.residual.length < source.length := by
  have h := step.compresses
  omega

/-- Every strict step is a zero-slack step. -/
def toSlack
    {U : ConditionalAlgorithm} {source : BinString}
    (step : CompressionStep U source) :
    SlackCompressionStep U source 0 where
  featureProgram := step.featureProgram
  descriptiveProgram := step.descriptiveProgram
  residual := step.residual
  extracts := step.extracts
  reconstructs := step.reconstructs
  compressesWithSlack := by simpa using step.compresses

end CompressionStep

namespace SlackCompressionStep

/-- Slack budgets are monotone. -/
def weaken
    {U : ConditionalAlgorithm} {source : BinString} {small large : Nat}
    (step : SlackCompressionStep U source small) (h : small ≤ large) :
    SlackCompressionStep U source large where
  featureProgram := step.featureProgram
  descriptiveProgram := step.descriptiveProgram
  residual := step.residual
  extracts := step.extracts
  reconstructs := step.reconstructs
  compressesWithSlack := by
    have hstep := step.compressesWithSlack
    omega

/-- A witnessed margin dominating the allowed slack recovers a genuinely strict
feature.  The margin is additional information; it is not derivable from a slack
bound alone. -/
def toStrictOfMargin
    {U : ConditionalAlgorithm} {source : BinString} {slack : Nat}
    (step : SlackCompressionStep U source slack)
    (margin : step.featureProgram.length + step.residual.length + slack < source.length) :
    CompressionStep U source where
  featureProgram := step.featureProgram
  descriptiveProgram := step.descriptiveProgram
  residual := step.residual
  extracts := step.extracts
  reconstructs := step.reconstructs
  compresses := by omega

end SlackCompressionStep

/-! ## Concrete positive and negative controls -/

/-- Four bits used by the controls below. -/
def fourTrue : BinString := [true, true, true, true]

/-- A finite executable table containing a real compression/decompression pair.
The feature `[false]` reconstructs `fourTrue` from the empty residual, while the
descriptive program `[true]` extracts that residual. -/
def finiteCompressionAlgorithm : ConditionalAlgorithm :=
  fun program condition =>
    if program = [false] ∧ condition = [] then Part.some fourTrue
    else if program = [true] ∧ condition = fourTrue then Part.some []
    else Part.none

/-- The table exhibits a nondegenerate strict feature: one feature bit replaces
four source bits and both executable directions are present. -/
def finiteCompressionStep : CompressionStep finiteCompressionAlgorithm fourTrue where
  featureProgram := [false]
  descriptiveProgram := [true]
  residual := []
  extracts := by simp [finiteCompressionAlgorithm, fourTrue]
  reconstructs := by simp [finiteCompressionAlgorithm, fourTrue]
  compresses := by simp [fourTrue]

theorem finiteCompressionStep_is_strict :
    finiteCompressionStep.featureProgram.length +
      finiteCompressionStep.residual.length < fourTrue.length :=
  finiteCompressionStep.compresses

/-- A literal constructor with an empty descriptive program.  It provides the
boundary case where slack admits a description exactly as long as the source. -/
def literalResidualAlgorithm : ConditionalAlgorithm :=
  fun program condition =>
    if program = [] then Part.some []
    else if condition = [] then Part.some program
    else Part.none

def literalSlackStep : SlackCompressionStep literalResidualAlgorithm fourTrue 1 where
  featureProgram := fourTrue
  descriptiveProgram := []
  residual := []
  extracts := by simp [literalResidualAlgorithm]
  reconstructs := by simp [literalResidualAlgorithm, fourTrue]
  compressesWithSlack := by simp [fourTrue]

/-- Additive slack does not imply strict compression.  This is the typing canary
for containment-to-implication results with logarithmic overhead. -/
theorem literalSlackStep_not_strict :
    ¬ (literalSlackStep.featureProgram.length +
        literalSlackStep.residual.length < fourTrue.length) := by
  simp [literalSlackStep, fourTrue]

/-- The identity decomposition cannot raise itself to a strict feature, even
though reconstruction is exact. -/
theorem identity_reconstruction_not_compression (source : BinString) :
    ¬ ([] : BinString).length + source.length < source.length := by
  simp

#print axioms finiteCompressionStep_is_strict
#print axioms literalSlackStep_not_strict
#print axioms identity_reconstruction_not_compression

end KolmogorovComplexity
