import Mettapedia.Logic.HOLExampleLadder

/-!
# HOL -> WM -> Probabilistic -> Planner Demo

This module packages the current closest thing to an end-to-end higher-order
demo chain in the repository.

The chain is:

1. a real HOL metatheoretic rung,
2. a HOL-to-world-model consequence rung,
3. a probabilistic higher-order belief-tracking rung,
4. a planner-facing carried-value / shadow rung.

Positive examples:

- `holSoundnessRung`
- `holInternalCompletenessRung`
- `wmConsequenceSchemaRung`
- `probabilisticBeliefRung`
- `plannerCarriedValueRung`
- `plannerTrackingRung`

Negative examples:

- `holOriginalReflectionObstructionRung`
- `probabilisticNotGlobalOracleRung`
- `plannerNotGlobalOracleRung`

This is still not the final witnessed-source original-signature completeness
theorem. The demo is therefore an honest theorem ladder through the currently
build-green layers, not a claim that the final completeness bridge is already
finished.
-/

namespace Mettapedia.Logic.HOLProbPLNExampleDemo

/-- Positive example: closed HOL theorems are sound in every Heyting-Henkin
model of the corrected core. -/
abbrev holSoundnessRung :=
  @Mettapedia.Logic.HOL.IntuitionisticSoundness.theorem_sound

/-- Positive example: internal cumulative-Henkin canonical validity is already
equivalent to finite-context provability. -/
abbrev holInternalCompletenessRung :=
  @Mettapedia.Logic.HOL.HenkinConstInfinity.canonicalHenkinValidFrom_iff_provable

/-- Negative example: naive original reflection is formally obstructed. -/
abbrev holOriginalReflectionObstructionRung :=
  @Mettapedia.Logic.HOL.HenkinConstInfinity.emptySignature_originalLiftProvable_existsTop

/-- Positive example: any external implication relation that is sound and
complete for pointwise HOL implication coincides with singleton WM
consequence. -/
abbrev wmConsequenceSchemaRung :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.externalImplication_iff_singletonConsequence_of_sound_complete

/-- Positive example: benchmark belief-day behavior tracks the hierarchical
probabilistic HOL semantics on the canonical benchmark sample. -/
abbrev probabilisticBeliefRung :=
  @Mettapedia.Logic.HOL.Probabilistic.benchmarkBeliefDay_tracks_benchmarkHierarchicalProbOn

/-- Negative example: the benchmark belief adapter is not a global oracle on
the expanded sample. -/
abbrev probabilisticNotGlobalOracleRung :=
  @Mettapedia.Logic.HOL.Probabilistic.benchmarkBeliefDay_not_tracks_benchmarkHierarchicalProbOn_with_top

/-- Positive example: the planner-facing carried value agrees with the semantic
benchmark belief price. -/
abbrev plannerCarriedValueRung :=
  @Mettapedia.Logic.benchmarkPlannerShadow_carried_value_eq_benchmarkBeliefPrice

/-- Positive example: the planner-facing shadow tracks the hierarchical
probabilistic HOL semantics on the benchmark sample. -/
abbrev plannerTrackingRung :=
  @Mettapedia.Logic.benchmarkPlannerShadow_day_tracks_hierarchicalProbOn

/-- Negative example: the planner-facing shadow remains query-focused and is
not a global oracle on the expanded sample. -/
abbrev plannerNotGlobalOracleRung :=
  @Mettapedia.Logic.benchmarkPlannerShadow_day_not_tracks_expandedSample

end Mettapedia.Logic.HOLProbPLNExampleDemo
