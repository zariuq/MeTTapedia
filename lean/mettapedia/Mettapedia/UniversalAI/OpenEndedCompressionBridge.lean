import Mettapedia.Logic.WorldModel.OpenEndedAlgorithmic
import Mettapedia.UniversalAI.IncrementalCompressionBridge
import Mettapedia.UniversalAI.OptimalityBoundary

/-!
# Open-ended compression as stagewise Solomonoff evidence

An open-ended compression family uses one feature program and one extractor
program at every finite observation stage.  When its underlying algorithm is
implemented by a conditional prefix machine, each stage has two consequences:

* a strict conditional prefix-complexity bound, and
* an exact singleton contribution to conditional algorithmic probability.

Because the feature program is fixed, its dyadic contribution is independent
of the stage even though the source and residual conditions may grow.

The converses are intentionally separated.  Positive program mass does not by
itself provide an extractor or a strict description-length improvement.  Nor
does stagewise predictive evidence select a unique optimal policy: the finite
optimality boundary remains in force.
-/

namespace Mettapedia.UniversalAI.OpenEndedCompressionBridge

open KolmogorovComplexity
open Mettapedia.Logic.WorldModel.OpenEndedAlgorithmic
open Mettapedia.UniversalAI.IncrementalCompressionBridge

universe uWorld

/-- One coherent open-ended compression family has conditional complexity and
singleton program-mass evidence at every finite stage. -/
def HasStagewisePrefixEvidence
    (U : ConditionalPrefixFreeMachine) (World : Type uWorld)
    (family : UniformCompressionFamily (prefixMachineAlgorithm U) World) : Prop :=
  ∀ stage,
    Kc[U](family.sourceAt stage family.world | family.residualAt stage) +
          (family.residualAt stage).length <
        (family.sourceAt stage family.world).length ∧
      Mettapedia.UniversalAI.SolomonoffPrior.algorithmicProbability
          (conditionalSlice U (family.residualAt stage))
          {family.featureProgram} (family.sourceAt stage family.world) =
        (2 : Real) ^ (-(family.featureProgram.length : Int))

namespace UniformCompressionFamily

/-- The exhibited feature program bounds conditional prefix complexity at
every stage of a prefix-machine compression family. -/
theorem conditionalTwoPartCodeAt
    {U : ConditionalPrefixFreeMachine} {World : Type uWorld}
    (family : UniformCompressionFamily (prefixMachineAlgorithm U) World)
    (stage : Nat) :
    Kc[U](family.sourceAt stage family.world | family.residualAt stage) +
          (family.residualAt stage).length <
        (family.sourceAt stage family.world).length := by
  exact compressionStep_conditionalTwoPartCode_lt_source
    (family.compressionStep stage)

/-- The fixed feature program contributes its exact dyadic weight at every
stage, under that stage's residual condition. -/
theorem singletonAlgorithmicProbabilityAt
    {U : ConditionalPrefixFreeMachine} {World : Type uWorld}
    (family : UniformCompressionFamily (prefixMachineAlgorithm U) World)
    (stage : Nat) :
    Mettapedia.UniversalAI.SolomonoffPrior.algorithmicProbability
        (conditionalSlice U (family.residualAt stage))
        {family.featureProgram} (family.sourceAt stage family.world) =
      (2 : Real) ^ (-(family.featureProgram.length : Int)) := by
  exact compressionStep_singletonAlgorithmicProbability_eq_featureWeight
    (family.compressionStep stage)

/-- The finite-stage complexity and probability consequences hold uniformly
over the coherent family. -/
theorem hasStagewisePrefixEvidence
    {U : ConditionalPrefixFreeMachine} {World : Type uWorld}
    (family : UniformCompressionFamily (prefixMachineAlgorithm U) World) :
    HasStagewisePrefixEvidence U World family := by
  intro stage
  exact ⟨conditionalTwoPartCodeAt family stage,
    singletonAlgorithmicProbabilityAt family stage⟩

/-- Although residual conditions and reconstructed sources may change, the
singleton contribution of the shared feature program is stage-invariant. -/
theorem singletonFeatureWeight_stageInvariant
    {U : ConditionalPrefixFreeMachine} {World : Type uWorld}
    (family : UniformCompressionFamily (prefixMachineAlgorithm U) World)
    (first second : Nat) :
    Mettapedia.UniversalAI.SolomonoffPrior.algorithmicProbability
        (conditionalSlice U (family.residualAt first))
        {family.featureProgram} (family.sourceAt first family.world) =
      Mettapedia.UniversalAI.SolomonoffPrior.algorithmicProbability
        (conditionalSlice U (family.residualAt second))
        {family.featureProgram} (family.sourceAt second family.world) := by
  rw [singletonAlgorithmicProbabilityAt family first,
    singletonAlgorithmicProbabilityAt family second]

end UniformCompressionFamily

/-! ## A concrete prefix-free open-ended family -/

/-- Prefix-machine realization of the repetitive open-ended control.  The two
one-bit programs are prefix-incomparable. -/
def repetitivePrefixMachine : ConditionalPrefixFreeMachine where
  compute := fun program condition =>
    if program = [false] then
      some (List.replicate (2 * condition.length + 4) true)
    else if program = [true] then
      some (List.replicate ((condition.length - 4) / 2) true)
    else none
  prefix_free := by
    intro condition program extension hprefix hdistinct hhalts
    obtain ⟨suffix, rfl⟩ := hprefix
    cases suffix with
    | nil => exact (hdistinct (by simp)).elim
    | cons bit tail =>
        by_cases feature : program = [false]
        · subst program
          simp
        · by_cases extractor : program = [true]
          · subst program
            simp
          · simp [feature, extractor] at hhalts

/-- The prefix-machine interpretation is extensionally the open-ended
repetitive algorithm. -/
theorem repetitivePrefixMachine_algorithm_eq :
    prefixMachineAlgorithm repetitivePrefixMachine =
      repetitiveCompressionAlgorithm := by
  funext program condition
  by_cases feature : program = [false]
  · simp [prefixMachineAlgorithm, repetitivePrefixMachine,
      repetitiveCompressionAlgorithm, feature, Part.ofOption]
  · by_cases extractor : program = [true]
    · simp [prefixMachineAlgorithm, repetitivePrefixMachine,
        repetitiveCompressionAlgorithm, extractor, Part.ofOption]
    · simp [prefixMachineAlgorithm, repetitivePrefixMachine,
        repetitiveCompressionAlgorithm, feature, extractor, Part.ofOption]

/-- The existing coherent repetitive family, now carried by an explicit
conditional prefix machine. -/
def repetitivePrefixUniformCompression :
    UniformCompressionFamily
      (prefixMachineAlgorithm repetitivePrefixMachine)
      Mettapedia.Computability.CantorSpace := by
  rw [repetitivePrefixMachine_algorithm_eq]
  exact repetitiveUniformCompression

/-- Positive open-ended control: the fixed one-bit feature supplies a strict
conditional code and exact half-unit singleton mass at every finite stage. -/
theorem repetitivePrefixUniformCompression_hasStagewiseEvidence :
    HasStagewisePrefixEvidence repetitivePrefixMachine
      Mettapedia.Computability.CantorSpace
      repetitivePrefixUniformCompression :=
  UniformCompressionFamily.hasStagewisePrefixEvidence
    repetitivePrefixUniformCompression

/-- The shared feature's singleton contribution is equal at any two stages of
the growing repetitive world. -/
theorem repetitivePrefixUniformCompression_mass_stageInvariant
    (first second : Nat) :
    Mettapedia.UniversalAI.SolomonoffPrior.algorithmicProbability
        (conditionalSlice repetitivePrefixMachine
          (repetitivePrefixUniformCompression.residualAt first))
        {repetitivePrefixUniformCompression.featureProgram}
        (repetitivePrefixUniformCompression.sourceAt first
          repetitivePrefixUniformCompression.world) =
      Mettapedia.UniversalAI.SolomonoffPrior.algorithmicProbability
        (conditionalSlice repetitivePrefixMachine
          (repetitivePrefixUniformCompression.residualAt second))
        {repetitivePrefixUniformCompression.featureProgram}
        (repetitivePrefixUniformCompression.sourceAt second
          repetitivePrefixUniformCompression.world) :=
  UniformCompressionFamily.singletonFeatureWeight_stageInvariant
    repetitivePrefixUniformCompression first second

/-! ## Converse and policy-selection boundaries -/

/-- Positive singleton program mass is not sufficient for strict incremental
compression.  The witness has one bit of program mass but no strict length
improvement. -/
theorem exists_programMass_without_strictCompression :
    ∃ (U : ConditionalPrefixFreeMachine)
      (condition program source : BinString),
      Mettapedia.UniversalAI.SolomonoffPrior.algorithmicProbability
          (conditionalSlice U condition) {program} source =
          (2 : Real) ^ (-(program.length : Int)) ∧
        ¬ (program.length + condition.length < source.length) := by
  refine ⟨singletonFeatureMachine oneTrue, [], [false], oneTrue, ?_⟩
  simpa [boundaryPrefixSlackStep] using
    programMass_does_not_imply_strictCompression

/-- Stagewise compression evidence coexists with the finite witness that broad
Pareto undominatedness does not select a unique policy and does not imply
pointwise optimality.  Thus the evidence theorem is not an agent-optimality
theorem. -/
theorem stagewiseEvidence_with_paretoNonselection
    (gamma : Mettapedia.UniversalAI.BayesianAgents.DiscountFactor) :
    HasStagewisePrefixEvidence repetitivePrefixMachine
        Mettapedia.Computability.CantorSpace
        repetitivePrefixUniformCompression ∧
      Mettapedia.UniversalAI.OptimalityBoundary.alwaysLeft ≠
        Mettapedia.UniversalAI.OptimalityBoundary.alwaysRight ∧
      Mettapedia.UniversalAI.BadUniversalPriors.ParetoOptimal
        Mettapedia.UniversalAI.OptimalityBoundary.alwaysLeft Set.univ gamma 2 ∧
      Mettapedia.UniversalAI.BadUniversalPriors.ParetoOptimal
        Mettapedia.UniversalAI.OptimalityBoundary.alwaysRight Set.univ gamma 2 ∧
      Mettapedia.UniversalAI.BayesianAgents.value
          (Mettapedia.UniversalAI.BadUniversalPriors.buddyEnvironmentNow
            Mettapedia.UniversalAI.BayesianAgents.Action.left)
          Mettapedia.UniversalAI.OptimalityBoundary.alwaysRight gamma [] 2 <
        Mettapedia.UniversalAI.BayesianAgents.value
          (Mettapedia.UniversalAI.BadUniversalPriors.buddyEnvironmentNow
            Mettapedia.UniversalAI.BayesianAgents.Action.left)
          Mettapedia.UniversalAI.OptimalityBoundary.alwaysLeft gamma [] 2 := by
  exact ⟨repetitivePrefixUniformCompression_hasStagewiseEvidence,
    Mettapedia.UniversalAI.OptimalityBoundary.pareto_nonselective_witness gamma⟩

#print axioms UniformCompressionFamily.conditionalTwoPartCodeAt
#print axioms UniformCompressionFamily.singletonAlgorithmicProbabilityAt
#print axioms UniformCompressionFamily.hasStagewisePrefixEvidence
#print axioms UniformCompressionFamily.singletonFeatureWeight_stageInvariant
#print axioms repetitivePrefixMachine_algorithm_eq
#print axioms repetitivePrefixUniformCompression_hasStagewiseEvidence
#print axioms exists_programMass_without_strictCompression
#print axioms stagewiseEvidence_with_paretoNonselection

end Mettapedia.UniversalAI.OpenEndedCompressionBridge
