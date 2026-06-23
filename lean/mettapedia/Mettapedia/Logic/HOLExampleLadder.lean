import Mettapedia.Logic.HOL.Soundness
import Mettapedia.Logic.HOL.TermModel.HenkinCompleteness
import Mettapedia.Logic.HOL.WitnessedWorld
import Mettapedia.Logic.HOL.WitnessedSaturation
import Mettapedia.Logic.HOL.Embedding.FirstOrder
import Mettapedia.Logic.HOL.WorldModel
import Mettapedia.Logic.HOL.WorldModelCompleteness
import Mettapedia.Logic.HOL.Probabilistic.BenchmarkBeliefBridge
import Mettapedia.Logic.PLNProbHOLPlannerBridge

/-!
# HOL Example Ladder

This module curates theorem-level examples showing how the current higher-order
logic stack can already be instantiated across several layers:

- HOL soundness for closed theorems,
- classical Henkin satisfiability/model existence,
- the witnessed prime-extension and witness-axiom machinery,
- first-order embedding into real HOL,
- HOL-to-world-model consequence transfer,
- higher-order probabilistic belief tracking,
- and planner-facing higher-order PLN shadow theorems.

Positive examples:

- `closedTheoremSoundnessExample`
- `henkinSatisfiabilityExample`
- `henkinClassicalModelExistenceExample`
- `witnessedPrimeExtensionExample`
- `witnessAxiomExistsExample`
- `firstOrderEmbeddingSentenceExample`
- `singletonWorldModelAdequacyExample`
- `worldModelSingletonConsequenceExample`
- `benchmarkHierarchicalProbStrengthExample`
- `benchmarkBeliefTracksHierarchicalProbExample`
- `higherOrderSemanticContractionCarriesBeliefPriceExample`
- `plannerShadowTracksHierarchicalProbExample`

Negative examples:

- `singletonWorldModelCounterevidenceExample`
- `benchmarkBeliefNotGlobalOracleExample`
- `plannerShadowNotGlobalOracleExample`

This is intentionally an example ladder, not the final end-to-end theorem. In
particular, the final witnessed original-signature HOL completeness theorem is
still in progress, so the current probabilistic/planner-facing examples are
theorem-backed uses of the HOL semantic layers rather than consequences of that
final missing completeness bridge.
-/

namespace Mettapedia.Logic.HOLExampleLadder

/-- Positive example: closed HOL theorems are sound in every Heyting-Henkin
model of the corrected intuitionistic-extensional core. -/
abbrev closedTheoremSoundnessExample :=
  @Mettapedia.Logic.HOL.Soundness.theorem_sound

/-- Positive example: the witnessed + excluded-middle Henkin extension has a
general Henkin model whenever that extended theory is consistent. -/
abbrev henkinSatisfiabilityExample :=
  @Mettapedia.Logic.HOL.ClosedTheorySet.henkin_satisfiable

/-- Positive example: in the honest classical/Henkin regime, consistency of the
original parameter-free theory yields a Henkin model of that theory. -/
abbrev henkinClassicalModelExistenceExample :=
  @Mettapedia.Logic.HOL.ClosedTheorySet.henkin_model_exists_of_consistent_classical

/-- Positive example: consistent parameter-free theories extend to witnessed,
prime, deductively closed Henkin worlds. -/
abbrev witnessedPrimeExtensionExample :=
  @Mettapedia.Logic.HOL.exists_witnessed_prime_extension

/-- Positive example: the Henkin saturation contains an explicit witness axiom
for every enumerated existential body. -/
abbrev witnessAxiomExistsExample :=
  @Mettapedia.Logic.HOL.exists_witnessAxiom

/-- Positive example: first-order sentence truth is preserved by the standard
embedding into real Church-style HOL. -/
abbrev firstOrderEmbeddingSentenceExample :=
  @Mettapedia.Logic.HOL.Embedding.FirstOrder.denote_embedSentence_iff

/-- Positive example: truth of a closed HOL formula is equivalent to singleton
world-model strength `1` in the pointed-Henkin world-model bridge. -/
abbrev singletonWorldModelAdequacyExample :=
  @Mettapedia.Logic.HOL.WorldModel.singleton_adequacy_strength_one

/-- Negative example: falsity of a closed HOL formula yields singleton
counterevidence in the world-model bridge. -/
abbrev singletonWorldModelCounterevidenceExample :=
  @Mettapedia.Logic.HOL.WorldModel.holEvidence_singleton_of_not_satisfies

/-- Positive example: pointwise HOL implication is exactly singleton
world-model consequence on pointed Henkin states. -/
abbrev worldModelSingletonConsequenceExample :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.pointwiseImplies_iff_singletonConsequence

/-- Positive example: the benchmark hierarchical query strength coincides with
the higher-order semantic value in the probabilistic HOL bridge. -/
abbrev benchmarkHierarchicalProbStrengthExample :=
  @Mettapedia.Logic.HOL.Probabilistic.benchmarkHierarchicalProbQueryStrength_eq_higherOrderSemanticValue

/-- Positive example: the belief-day benchmark shadow tracks hierarchical
probability on the canonical sample. -/
abbrev benchmarkBeliefTracksHierarchicalProbExample :=
  @Mettapedia.Logic.HOL.Probabilistic.benchmarkBeliefDay_tracks_benchmarkHierarchicalProbOn

/-- Positive example: the higher-order semantic contraction already carries the
same value as the benchmark belief price consumed by the PLN-facing layer. -/
abbrev higherOrderSemanticContractionCarriesBeliefPriceExample :=
  @Mettapedia.Logic.HOL.Probabilistic.higherOrderSemanticContraction_value_eq_benchmarkBeliefPrice

/-- Negative example: the benchmark belief adapter remains query-focused rather
than becoming a global oracle on the expanded sample. -/
abbrev benchmarkBeliefNotGlobalOracleExample :=
  @Mettapedia.Logic.HOL.Probabilistic.benchmarkBeliefDay_not_tracks_benchmarkHierarchicalProbOn_with_top

/-- Positive example: the planner-facing shadow tracks the higher-order
hierarchical probability semantics on the benchmark sample. -/
abbrev plannerShadowTracksHierarchicalProbExample :=
  @Mettapedia.Logic.benchmarkPlannerShadow_day_tracks_hierarchicalProbOn

/-- Negative example: the planner-facing shadow is not a global oracle for the
expanded benchmark sample. -/
abbrev plannerShadowNotGlobalOracleExample :=
  @Mettapedia.Logic.benchmarkPlannerShadow_day_not_tracks_expandedSample

end Mettapedia.Logic.HOLExampleLadder
