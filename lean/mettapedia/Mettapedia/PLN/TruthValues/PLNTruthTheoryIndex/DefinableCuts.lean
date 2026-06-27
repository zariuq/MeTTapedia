import Mettapedia.PLN.TruthValues.PLNTruthTower
import Mettapedia.PLN.TruthValues.PLNConfidenceWeightRevision
import Mettapedia.PLN.TruthValues.PLNInformationGeometry
import Mettapedia.PLN.TruthValues.PLNAmplitudePhase
import Mettapedia.PLN.TruthValues.PLNDidacticWitnesses
import Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions
import Mettapedia.PLN.WorldModel.PLNWorldModelITV
import Mettapedia.KR.ConceptOntology.ConstructionBasePredictiveITV
import Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyMultinomialIDMExamples
import Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal
import Mettapedia.Logic.MarkovLogicInfiniteCredalBridge
import Mettapedia.Logic.MarkovLogicPLNTruthBridge
import Mettapedia.Logic.MarkovLogicInfiniteUniqueness
import Mettapedia.Logic.MarkovLogicInfinitePLNCrown
import Mettapedia.Logic.MarkovLogicInfiniteSymmetricGridExample
import Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge
import Mettapedia.PLN.TruthValues.PLNDistinctionCredalBridge
import Mettapedia.PLN.Bridges.Languages.PLNDistinctionCredalOSLFBridge
import Mettapedia.PLN.Bridges.ProbabilityTheory.PLNSubjectiveLogicBridge
import Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo
import Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLEmpiricalAssocPatBridge
import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLDefinableCuts


namespace Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex

open Mettapedia.PLN.WorldModel

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.WithParams
open Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLDefinableCuts
open Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLQuantifierBridge
open Mettapedia.PLN.TruthValues.PLNConfidenceWeight
open Mettapedia.PLN.TruthValues.PLNConfidenceWeight.EvidenceWeightCoordinate
open Mettapedia.PLN.TruthValues.PLNIndefiniteTruth
open Mettapedia.PLN.TruthValues.PLNInformationGeometry
open Mettapedia.PLN.TruthValues.PLNAmplitudePhase
open Mettapedia.PLN.TruthValues.PLNTruthTower
open Mettapedia.Algebra.TwoDimClassification
open scoped ENNReal

universe u v


/-! ## Definable-cut tightness spine -/

/-- Public theorem-index name for arbitrary finite witness-set thresholds of
HOL predicate extensions.  This is the generic semantic spine behind the
constructed `∃`, `at least two`, and `at least three` counting sentences. -/
abbrev hol_predicate_extension_ncard_ge_iff_exists_witness_set
    {Base : Type u} {Const : Ty Base → Type v} :=
  predicateExtension_ncard_ge_iff_exists_witnessSet
    (Base := Base) (Const := Const)

/-- Public theorem-index name for arbitrary finite non-witness-set thresholds
of the complement of a HOL predicate extension. -/
abbrev hol_predicate_extension_compl_ncard_ge_iff_exists_nonwitness_set
    {Base : Type u} {Const : Ty Base → Type v} :=
  predicateExtension_compl_ncard_ge_iff_exists_nonwitnessSet
    (Base := Base) (Const := Const)

/-- Public theorem-index constructor for the uniform closed HOL sentence
asserting at least `k` distinct base objects satisfy a unary predicate.
Semantic cardinality certification remains a separate theorem layer. -/
abbrev hol_predicate_at_least_n_base_formula
    {Base : Type u} {Const : Ty Base → Type v} :=
  predicateAtLeastNBaseFormula
    (Base := Base) (Const := Const)

/-- Public theorem-index name for param-freeness of the uniform
`at least k base witnesses` HOL sentence. -/
abbrev hol_no_const_occurrence_predicate_at_least_n_base_formula
    {Base : Type u} {Const : Ty Base → Type v}
    {τ : Ty Base} {c : Const τ} :=
  noConstOccurrence_predicateAtLeastNBaseFormula
    (Base := Base) (Const := Const) (τ := τ) (c := c)

/-- Public theorem-index name for the semantic readout of the generated
witness-conjunction subformula: every tuple entry satisfies the HOL predicate. -/
abbrev hol_denote_predicate_witness_conjunction_base_formula_iff_forall
    {Base : Type u} {Const : Ty Base → Type v} :=
  denote_predicateWitnessConjunctionBaseFormula_iff_forall
    (Base := Base) (Const := Const)

/-- Public theorem-index name for definable-cut endpoint tightness: lower
endpoint `1` is exactly provability of the representing HOL threshold formula.
The certificate's `represents_ge` field remains the required no-laundering
bridge from a numeric score to a formula. -/
abbrev definable_cut_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  ExtensionalDefinableCut.lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for definable-cut width collapse: a certified
numeric threshold interval has width zero exactly when the underlying theory
decides the representing HOL threshold formula. -/
abbrev definable_cut_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  ExtensionalDefinableCut.width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for positive affine calibration of already
certified numeric cuts. This is unit/scale transport for a discharged cut, not
an existence theorem for arbitrary numeric observables. -/
abbrev definable_cut_pos_affine_rescale_interval_eq
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  ExtensionalDefinableCut.posAffineRescale_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for Boolean-valued endpoint cuts at
arbitrary positive thresholds at most `1`. Concrete consumers must still prove
that their score is literally `0` or `1` in every canonical model. -/
abbrev definable_cut_boolean_positive_threshold
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  ExtensionalDefinableCut.booleanPositiveThreshold
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for Boolean-valued positive-threshold transport:
the formula-level credal interval is unchanged because the representing HOL
formula is unchanged. -/
abbrev definable_cut_boolean_positive_threshold_interval_eq
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  ExtensionalDefinableCut.booleanPositiveThreshold_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for the nonpositive-threshold boundary of
Boolean-valued certified scores. If `τ ≤ 0`, the represented threshold event is
tautological, so the formula is `φ ∨ ¬φ`. -/
noncomputable abbrev definable_cut_boolean_nonpositive_threshold_tautology
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  ExtensionalDefinableCut.booleanNonpositiveThresholdTautology
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for Boolean indicator cuts at arbitrary
positive thresholds at most `1`. This is a concrete non-`1`
`represents_ge` certificate for the original indicator score, not merely a
rescaling of the score. -/
noncomputable abbrev definable_cut_formula_indicator_positive_threshold
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  formulaIndicatorPositiveThresholdCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the positive-threshold Boolean indicator
cut's interval readout: its credal interval is the same formula-level interval
as the endpoint-`1` indicator cut, because the representing HOL formula is
unchanged. -/
abbrev definable_cut_formula_indicator_positive_threshold_interval_eq_ge_one
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  formulaIndicatorPositiveThresholdCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for positive-threshold Boolean indicator lower
endpoint tightness. -/
abbrev definable_cut_formula_indicator_positive_threshold_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  formulaIndicatorPositiveThresholdCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for positive-threshold Boolean indicator upper
endpoint tightness. -/
abbrev definable_cut_formula_indicator_positive_threshold_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  formulaIndicatorPositiveThresholdCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for positive-threshold Boolean indicator
width-zero tightness. -/
abbrev definable_cut_formula_indicator_positive_threshold_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  formulaIndicatorPositiveThresholdCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for the nonpositive-threshold boundary of
Boolean indicator cuts. At `τ ≤ 0`, the threshold event for the indicator score
is represented by the tautology `φ ∨ ¬φ`, not by `φ`. -/
noncomputable abbrev definable_cut_formula_indicator_nonpositive_threshold_tautology
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  formulaIndicatorNonpositiveThresholdTautologyCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for strict finite-QFM `ForAll`
acceptance at arbitrary positive thresholds at most `1`. This is valid because
the endpoint acceptance score is Boolean-valued; it is not a theorem about
fractional near-one mass thresholds. -/
noncomputable abbrev definable_cut_qfm_forall_acceptance_positive_threshold
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCrispEndpointPositiveThresholdCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the strict finite-QFM `ForAll`
positive-threshold acceptance readout: its formula-level credal interval is
the same as the endpoint-`1` acceptance cut. -/
abbrev definable_cut_qfm_forall_acceptance_positive_threshold_interval_eq_ge_one
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCrispEndpointPositiveThresholdCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for positive-threshold strict finite-QFM
`ForAll` acceptance lower endpoint tightness. -/
abbrev definable_cut_qfm_forall_acceptance_positive_threshold_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCrispEndpointPositiveThresholdCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for positive-threshold strict finite-QFM
`ForAll` acceptance upper endpoint tightness. -/
abbrev definable_cut_qfm_forall_acceptance_positive_threshold_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCrispEndpointPositiveThresholdCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for positive-threshold strict finite-QFM
`ForAll` acceptance width-zero tightness. -/
abbrev definable_cut_qfm_forall_acceptance_positive_threshold_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCrispEndpointPositiveThresholdCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for strict finite-QFM `ThereExists`
acceptance at arbitrary positive thresholds at most `1`. At this endpoint the
acceptance score is Boolean-valued; richer fractional QFM thresholds still need
their own definable-cut certificates. -/
noncomputable abbrev definable_cut_qfm_there_exists_acceptance_positive_threshold
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCrispEndpointPositiveThresholdCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the strict finite-QFM `ThereExists`
positive-threshold acceptance readout.  The readout is still the endpoint-`1`
HOL universal-predicate interval, not an arbitrary fractional-QFM claim. -/
abbrev definable_cut_qfm_there_exists_acceptance_positive_threshold_interval_eq_ge_one
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCrispEndpointPositiveThresholdCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for positive-threshold strict finite-QFM
`ThereExists` acceptance lower endpoint tightness. -/
abbrev definable_cut_qfm_there_exists_acceptance_positive_threshold_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCrispEndpointPositiveThresholdCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for positive-threshold strict finite-QFM
`ThereExists` acceptance upper endpoint tightness. -/
abbrev definable_cut_qfm_there_exists_acceptance_positive_threshold_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCrispEndpointPositiveThresholdCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for positive-threshold strict finite-QFM
`ThereExists` acceptance width-zero tightness. -/
abbrev definable_cut_qfm_there_exists_acceptance_positive_threshold_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCrispEndpointPositiveThresholdCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for the nonpositive-threshold tautology
boundary of strict finite-QFM `ForAll` acceptance. -/
noncomputable abbrev definable_cut_qfm_forall_acceptance_nonpositive_threshold_tautology
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCrispEndpointNonpositiveThresholdTautologyCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for the nonpositive-threshold tautology
boundary of strict finite-QFM `ThereExists` acceptance. -/
noncomputable abbrev definable_cut_qfm_there_exists_acceptance_nonpositive_threshold_tautology
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCrispEndpointNonpositiveThresholdTautologyCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for exact-denominator finite-QFM
`ForAll` cardinality thresholds under normalized counting capacity.  This is a
genuine fractional `represents_ge` certificate, guarded by `ε = 0`,
`PCL = k / N`, an exact carrier-size equation, and a supplied HOL formula
representing `k ≤ ncard (ext p)`. -/
noncomputable abbrev definable_cut_qfm_forall_counting_cardinality_threshold
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingCardinalityThresholdCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ForAll`
counting-threshold interval readout.  The certified numeric interval is the
existing HOL interval for the supplied cardinality-threshold formula. -/
abbrev definable_cut_qfm_forall_counting_cardinality_threshold_interval_eq
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingCardinalityThresholdCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ForAll`
counting-threshold lower endpoint tightness. -/
abbrev definable_cut_qfm_forall_counting_cardinality_threshold_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingCardinalityThresholdCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ForAll`
counting-threshold upper endpoint tightness. -/
abbrev definable_cut_qfm_forall_counting_cardinality_threshold_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingCardinalityThresholdCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ForAll`
counting-threshold open lower endpoint tightness. -/
abbrev definable_cut_qfm_forall_counting_cardinality_threshold_lower_eq_zero_iff_not_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingCardinalityThresholdCut_lower_eq_zero_iff_not_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ForAll`
counting-threshold open upper endpoint tightness. -/
abbrev definable_cut_qfm_forall_counting_cardinality_threshold_upper_eq_one_iff_not_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingCardinalityThresholdCut_upper_eq_one_iff_not_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ForAll`
counting-threshold width-zero tightness. -/
abbrev definable_cut_qfm_forall_counting_cardinality_threshold_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingCardinalityThresholdCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for exact-denominator finite-QFM
`ThereExists` cardinality thresholds under normalized counting capacity.  This
is the QFM mass threshold `PCL ≤ 1 - nearZeroFraction`, not ordinary HOL
existential quantification, and is guarded by `ε = 0`, `PCL = k / N`, an exact
carrier-size equation, and a supplied HOL formula representing
`k ≤ ncard (ext p)`. -/
noncomputable abbrev definable_cut_qfm_there_exists_counting_cardinality_threshold
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingCardinalityThresholdCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ThereExists`
counting-threshold interval readout.  The certified numeric interval is the
existing HOL interval for the supplied cardinality-threshold formula. -/
abbrev definable_cut_qfm_there_exists_counting_cardinality_threshold_interval_eq
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingCardinalityThresholdCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ThereExists`
counting-threshold lower endpoint tightness. -/
abbrev definable_cut_qfm_there_exists_counting_cardinality_threshold_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingCardinalityThresholdCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ThereExists`
counting-threshold upper endpoint tightness. -/
abbrev definable_cut_qfm_there_exists_counting_cardinality_threshold_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingCardinalityThresholdCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ThereExists`
counting-threshold open lower endpoint tightness. -/
abbrev definable_cut_qfm_there_exists_counting_cardinality_threshold_lower_eq_zero_iff_not_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingCardinalityThresholdCut_lower_eq_zero_iff_not_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ThereExists`
counting-threshold open upper endpoint tightness. -/
abbrev definable_cut_qfm_there_exists_counting_cardinality_threshold_upper_eq_one_iff_not_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingCardinalityThresholdCut_upper_eq_one_iff_not_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ThereExists`
counting-threshold width-zero tightness. -/
abbrev definable_cut_qfm_there_exists_counting_cardinality_threshold_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingCardinalityThresholdCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for exact-denominator finite-QFM `ForAll`
counting thresholds at the HOL existential boundary (`k = 1`).  This packages
the existing HOL existence formula as the certified cut for
`1 / N ≤ QFM_ForAll(counting, p)`. -/
noncomputable abbrev definable_cut_qfm_forall_counting_exists_exact_threshold
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingExistsExactThresholdCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the exact-denominator finite-QFM `ForAll`
existential-threshold interval readout. -/
abbrev definable_cut_qfm_forall_counting_exists_exact_threshold_interval_eq
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingExistsExactThresholdCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ForAll`
existential-threshold lower endpoint tightness. -/
abbrev definable_cut_qfm_forall_counting_exists_exact_threshold_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingExistsExactThresholdCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ForAll`
existential-threshold upper endpoint tightness. -/
abbrev definable_cut_qfm_forall_counting_exists_exact_threshold_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingExistsExactThresholdCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ForAll`
existential-threshold open lower endpoint tightness. -/
abbrev definable_cut_qfm_forall_counting_exists_exact_threshold_lower_eq_zero_iff_not_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingExistsExactThresholdCut_lower_eq_zero_iff_not_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ForAll`
existential-threshold open upper endpoint tightness. -/
abbrev definable_cut_qfm_forall_counting_exists_exact_threshold_upper_eq_one_iff_not_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingExistsExactThresholdCut_upper_eq_one_iff_not_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ForAll`
existential-threshold width-zero tightness. -/
abbrev definable_cut_qfm_forall_counting_exists_exact_threshold_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingExistsExactThresholdCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for exact-denominator finite-QFM
`ThereExists` counting thresholds at the HOL existential boundary (`k = 1`).
This packages the existing HOL existence formula as the certified cut for
`1 / N ≤ QFM_ThereExists(counting, p)`. -/
noncomputable abbrev definable_cut_qfm_there_exists_counting_exists_exact_threshold
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingExistsExactThresholdCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the exact-denominator finite-QFM
`ThereExists` existential-threshold interval readout. -/
abbrev definable_cut_qfm_there_exists_counting_exists_exact_threshold_interval_eq
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingExistsExactThresholdCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ThereExists`
existential-threshold lower endpoint tightness. -/
abbrev definable_cut_qfm_there_exists_counting_exists_exact_threshold_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingExistsExactThresholdCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ThereExists`
existential-threshold upper endpoint tightness. -/
abbrev definable_cut_qfm_there_exists_counting_exists_exact_threshold_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingExistsExactThresholdCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ThereExists`
existential-threshold open lower endpoint tightness. -/
abbrev definable_cut_qfm_there_exists_counting_exists_exact_threshold_lower_eq_zero_iff_not_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingExistsExactThresholdCut_lower_eq_zero_iff_not_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ThereExists`
existential-threshold open upper endpoint tightness. -/
abbrev definable_cut_qfm_there_exists_counting_exists_exact_threshold_upper_eq_one_iff_not_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingExistsExactThresholdCut_upper_eq_one_iff_not_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ThereExists`
existential-threshold width-zero tightness. -/
abbrev definable_cut_qfm_there_exists_counting_exists_exact_threshold_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingExistsExactThresholdCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for exact-denominator finite-QFM `ForAll`
counting thresholds at the HOL universal boundary (`k = N`). This packages
the existing HOL universal formula as the certified cut for
`N / N ≤ QFM_ForAll(counting, p)`. -/
noncomputable abbrev definable_cut_qfm_forall_counting_universal_exact_threshold
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingUniversalExactThresholdCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the exact-denominator finite-QFM `ForAll`
universal-threshold interval readout. -/
abbrev definable_cut_qfm_forall_counting_universal_exact_threshold_interval_eq
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingUniversalExactThresholdCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ForAll`
universal-threshold lower endpoint tightness. -/
abbrev definable_cut_qfm_forall_counting_universal_exact_threshold_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingUniversalExactThresholdCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ForAll`
universal-threshold upper endpoint tightness. -/
abbrev definable_cut_qfm_forall_counting_universal_exact_threshold_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingUniversalExactThresholdCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ForAll`
universal-threshold open lower endpoint tightness. -/
abbrev definable_cut_qfm_forall_counting_universal_exact_threshold_lower_eq_zero_iff_not_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingUniversalExactThresholdCut_lower_eq_zero_iff_not_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ForAll`
universal-threshold open upper endpoint tightness. -/
abbrev definable_cut_qfm_forall_counting_universal_exact_threshold_upper_eq_one_iff_not_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingUniversalExactThresholdCut_upper_eq_one_iff_not_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ForAll`
universal-threshold width-zero tightness. -/
abbrev definable_cut_qfm_forall_counting_universal_exact_threshold_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingUniversalExactThresholdCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for exact-denominator finite-QFM
`ThereExists` counting thresholds at the HOL universal boundary (`k = N`).
This packages the existing HOL universal formula as the certified cut for
`N / N ≤ QFM_ThereExists(counting, p)`. -/
noncomputable abbrev definable_cut_qfm_there_exists_counting_universal_exact_threshold
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingUniversalExactThresholdCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the exact-denominator finite-QFM
`ThereExists` universal-threshold interval readout. -/
abbrev definable_cut_qfm_there_exists_counting_universal_exact_threshold_interval_eq
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingUniversalExactThresholdCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ThereExists`
universal-threshold lower endpoint tightness. -/
abbrev definable_cut_qfm_there_exists_counting_universal_exact_threshold_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingUniversalExactThresholdCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ThereExists`
universal-threshold upper endpoint tightness. -/
abbrev definable_cut_qfm_there_exists_counting_universal_exact_threshold_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingUniversalExactThresholdCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ThereExists`
universal-threshold open lower endpoint tightness. -/
abbrev definable_cut_qfm_there_exists_counting_universal_exact_threshold_lower_eq_zero_iff_not_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingUniversalExactThresholdCut_lower_eq_zero_iff_not_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ThereExists`
universal-threshold open upper endpoint tightness. -/
abbrev definable_cut_qfm_there_exists_counting_universal_exact_threshold_upper_eq_one_iff_not_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingUniversalExactThresholdCut_upper_eq_one_iff_not_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator finite-QFM `ThereExists`
universal-threshold width-zero tightness. -/
abbrev definable_cut_qfm_there_exists_counting_universal_exact_threshold_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingUniversalExactThresholdCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for the concrete base-type finite-QFM
`ForAll` counting cut whose representing HOL formula says that at least two
distinct base objects satisfy the predicate. -/
noncomputable abbrev definable_cut_qfm_forall_counting_at_least_two_base
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingAtLeastTwoBaseCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type finite-QFM `ForAll`
"at least two" interval readout. -/
abbrev definable_cut_qfm_forall_counting_at_least_two_base_interval_eq
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingAtLeastTwoBaseCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type finite-QFM `ForAll`
"at least two" lower-endpoint tightness. -/
abbrev definable_cut_qfm_forall_counting_at_least_two_base_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingAtLeastTwoBaseCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type finite-QFM `ForAll`
"at least two" upper-endpoint refutation tightness. -/
abbrev definable_cut_qfm_forall_counting_at_least_two_base_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingAtLeastTwoBaseCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type finite-QFM `ForAll`
"at least two" open lower-endpoint tightness. -/
abbrev definable_cut_qfm_forall_counting_at_least_two_base_lower_eq_zero_iff_not_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingAtLeastTwoBaseCut_lower_eq_zero_iff_not_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type finite-QFM `ForAll`
"at least two" open upper-endpoint tightness. -/
abbrev definable_cut_qfm_forall_counting_at_least_two_base_upper_eq_one_iff_not_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingAtLeastTwoBaseCut_upper_eq_one_iff_not_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type finite-QFM `ForAll`
"at least two" width collapse. -/
abbrev definable_cut_qfm_forall_counting_at_least_two_base_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingAtLeastTwoBaseCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for the concrete base-type finite-QFM
`ThereExists` counting cut whose representing HOL formula says that at least
two distinct base objects satisfy the predicate. -/
noncomputable abbrev definable_cut_qfm_there_exists_counting_at_least_two_base
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingAtLeastTwoBaseCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type finite-QFM
`ThereExists` "at least two" interval readout. -/
abbrev definable_cut_qfm_there_exists_counting_at_least_two_base_interval_eq
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingAtLeastTwoBaseCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type finite-QFM
`ThereExists` "at least two" lower-endpoint tightness. -/
abbrev definable_cut_qfm_there_exists_counting_at_least_two_base_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingAtLeastTwoBaseCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type finite-QFM
`ThereExists` "at least two" upper-endpoint refutation tightness. -/
abbrev definable_cut_qfm_there_exists_counting_at_least_two_base_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingAtLeastTwoBaseCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type finite-QFM
`ThereExists` "at least two" open lower-endpoint tightness. -/
abbrev definable_cut_qfm_there_exists_counting_at_least_two_base_lower_eq_zero_iff_not_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingAtLeastTwoBaseCut_lower_eq_zero_iff_not_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type finite-QFM
`ThereExists` "at least two" open upper-endpoint tightness. -/
abbrev definable_cut_qfm_there_exists_counting_at_least_two_base_upper_eq_one_iff_not_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingAtLeastTwoBaseCut_upper_eq_one_iff_not_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type finite-QFM
`ThereExists` "at least two" width collapse. -/
abbrev definable_cut_qfm_there_exists_counting_at_least_two_base_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingAtLeastTwoBaseCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for the concrete base-type finite-QFM
`ForAll` counting cut whose representing HOL formula says that at least three
distinct base objects satisfy the predicate. -/
noncomputable abbrev definable_cut_qfm_forall_counting_at_least_three_base
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingAtLeastThreeBaseCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type finite-QFM `ForAll`
"at least three" interval readout. -/
abbrev definable_cut_qfm_forall_counting_at_least_three_base_interval_eq
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingAtLeastThreeBaseCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type finite-QFM `ForAll`
"at least three" lower-endpoint tightness. -/
abbrev definable_cut_qfm_forall_counting_at_least_three_base_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingAtLeastThreeBaseCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type finite-QFM `ForAll`
"at least three" upper-endpoint refutation tightness. -/
abbrev definable_cut_qfm_forall_counting_at_least_three_base_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingAtLeastThreeBaseCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type finite-QFM `ForAll`
"at least three" open lower-endpoint tightness. -/
abbrev definable_cut_qfm_forall_counting_at_least_three_base_lower_eq_zero_iff_not_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingAtLeastThreeBaseCut_lower_eq_zero_iff_not_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type finite-QFM `ForAll`
"at least three" open upper-endpoint tightness. -/
abbrev definable_cut_qfm_forall_counting_at_least_three_base_upper_eq_one_iff_not_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingAtLeastThreeBaseCut_upper_eq_one_iff_not_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type finite-QFM `ForAll`
"at least three" width collapse. -/
abbrev definable_cut_qfm_forall_counting_at_least_three_base_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyForAllCountingAtLeastThreeBaseCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for the concrete base-type finite-QFM
`ThereExists` counting cut whose representing HOL formula says that at least
three distinct base objects satisfy the predicate. -/
noncomputable abbrev definable_cut_qfm_there_exists_counting_at_least_three_base
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingAtLeastThreeBaseCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type finite-QFM
`ThereExists` "at least three" interval readout. -/
abbrev definable_cut_qfm_there_exists_counting_at_least_three_base_interval_eq
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingAtLeastThreeBaseCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type finite-QFM
`ThereExists` "at least three" lower-endpoint tightness. -/
abbrev definable_cut_qfm_there_exists_counting_at_least_three_base_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingAtLeastThreeBaseCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type finite-QFM
`ThereExists` "at least three" upper-endpoint refutation tightness. -/
abbrev definable_cut_qfm_there_exists_counting_at_least_three_base_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingAtLeastThreeBaseCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type finite-QFM
`ThereExists` "at least three" open lower-endpoint tightness. -/
abbrev definable_cut_qfm_there_exists_counting_at_least_three_base_lower_eq_zero_iff_not_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingAtLeastThreeBaseCut_lower_eq_zero_iff_not_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type finite-QFM
`ThereExists` "at least three" open upper-endpoint tightness. -/
abbrev definable_cut_qfm_there_exists_counting_at_least_three_base_upper_eq_one_iff_not_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingAtLeastThreeBaseCut_upper_eq_one_iff_not_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type finite-QFM
`ThereExists` "at least three" width collapse. -/
abbrev definable_cut_qfm_there_exists_counting_at_least_three_base_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateFuzzyThereExistsCountingAtLeastThreeBaseCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for the first guarded fractional
counting-capacity cut.  HOL existence represents the positive threshold
`θ ≤ countingCapacity(ext p)` only under an explicit finite-carrier bound
`card ≤ N` with `0 < θ ≤ 1/N`; without that guard, the fractional claim is
not valid uniformly across arbitrary finite completions. -/
noncomputable abbrev definable_cut_counting_capacity_exists_positive_threshold
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsPositiveThresholdCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the guarded fractional counting cut's
formula-level interval readout.  The numeric score is counting-capacity based,
but its certified credal interval is the existing HOL interval for the
representing existential formula. -/
abbrev definable_cut_counting_capacity_exists_positive_threshold_interval_eq
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsPositiveThresholdCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the guarded fractional counting-existence
cut's lower-endpoint tightness. The finite-carrier guard remains part of the
underlying cut certificate. -/
abbrev definable_cut_counting_capacity_exists_positive_threshold_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsPositiveThresholdCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the guarded fractional counting-existence
cut's upper-endpoint refutation tightness. -/
abbrev definable_cut_counting_capacity_exists_positive_threshold_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsPositiveThresholdCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the guarded fractional counting-existence
cut's open lower endpoint. -/
abbrev definable_cut_counting_capacity_exists_positive_threshold_lower_eq_zero_iff_not_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsPositiveThresholdCut_lower_eq_zero_iff_not_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the guarded fractional counting-existence
cut's open upper endpoint. -/
abbrev definable_cut_counting_capacity_exists_positive_threshold_upper_eq_one_iff_not_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsPositiveThresholdCut_upper_eq_one_iff_not_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the guarded fractional counting-existence
cut's width collapse: the interval collapses exactly when the theory decides
the representing HOL existence formula. -/
abbrev definable_cut_counting_capacity_exists_positive_threshold_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsPositiveThresholdCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for the exact-denominator counting cut
whose representing HOL formula says that some admissible object satisfies the
predicate. Under an exact carrier-size guard `N`, it certifies
`1 / N ≤ countingCapacity(ext p)`. -/
noncomputable abbrev definable_cut_counting_capacity_exists_exact_threshold
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsExactThresholdCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the exact-denominator existential counting
cut's interval readout. -/
abbrev definable_cut_counting_capacity_exists_exact_threshold_interval_eq
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsExactThresholdCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the exact-denominator existential counting
cut's lower-endpoint tightness. -/
abbrev definable_cut_counting_capacity_exists_exact_threshold_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsExactThresholdCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the exact-denominator existential counting
cut's upper-endpoint refutation tightness. -/
abbrev definable_cut_counting_capacity_exists_exact_threshold_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsExactThresholdCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the exact-denominator existential counting
cut's open lower endpoint. -/
abbrev definable_cut_counting_capacity_exists_exact_threshold_lower_eq_zero_iff_not_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsExactThresholdCut_lower_eq_zero_iff_not_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the exact-denominator existential counting
cut's open upper endpoint. -/
abbrev definable_cut_counting_capacity_exists_exact_threshold_upper_eq_one_iff_not_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsExactThresholdCut_upper_eq_one_iff_not_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the exact-denominator existential counting
cut's width collapse. -/
abbrev definable_cut_counting_capacity_exists_exact_threshold_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsExactThresholdCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for exact-denominator counting-capacity
cardinality thresholds.  A param-free HOL formula `χ` must represent
`k ≤ ncard (ext p)`, and every completion's predicate-object carrier must have
exact cardinality `N`; with those guards, `χ` represents the rational threshold
`k / N ≤ countingCapacity (ext p)`. -/
noncomputable abbrev definable_cut_counting_capacity_cardinality_threshold
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityCardinalityThresholdCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the exact-denominator counting-capacity
cardinality-threshold interval readout.  The certified numeric interval is the
existing HOL interval for the formula representing the finite-cardinality
threshold. -/
abbrev definable_cut_counting_capacity_cardinality_threshold_interval_eq
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityCardinalityThresholdCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator lower-cardinality
threshold lower-endpoint tightness. -/
abbrev definable_cut_counting_capacity_cardinality_threshold_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityCardinalityThresholdCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator lower-cardinality
threshold upper-endpoint refutation tightness. -/
abbrev definable_cut_counting_capacity_cardinality_threshold_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityCardinalityThresholdCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator lower-cardinality
threshold open lower-endpoint tightness. -/
abbrev definable_cut_counting_capacity_cardinality_threshold_lower_eq_zero_iff_not_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityCardinalityThresholdCut_lower_eq_zero_iff_not_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator lower-cardinality
threshold open upper-endpoint tightness. -/
abbrev definable_cut_counting_capacity_cardinality_threshold_upper_eq_one_iff_not_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityCardinalityThresholdCut_upper_eq_one_iff_not_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator lower-cardinality
threshold width collapse. -/
abbrev definable_cut_counting_capacity_cardinality_threshold_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityCardinalityThresholdCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for the concrete base-type counting cut
whose representing HOL formula says that at least two distinct base objects
satisfy the predicate.  This specializes the exact-denominator cardinality
threshold machinery at `k = 2` with a constructed formula and a proven
`represents_ge` bridge. -/
noncomputable abbrev definable_cut_counting_capacity_at_least_two_base
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityAtLeastTwoBaseCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type "at least two"
counting cut's interval readout. -/
abbrev definable_cut_counting_capacity_at_least_two_base_interval_eq
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityAtLeastTwoBaseCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type "at least two"
counting cut's lower-endpoint tightness. -/
abbrev definable_cut_counting_capacity_at_least_two_base_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityAtLeastTwoBaseCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type "at least two"
counting cut's upper-endpoint refutation tightness. -/
abbrev definable_cut_counting_capacity_at_least_two_base_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityAtLeastTwoBaseCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type "at least two"
counting cut's open lower endpoint. -/
abbrev definable_cut_counting_capacity_at_least_two_base_lower_eq_zero_iff_not_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityAtLeastTwoBaseCut_lower_eq_zero_iff_not_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type "at least two"
counting cut's open upper endpoint. -/
abbrev definable_cut_counting_capacity_at_least_two_base_upper_eq_one_iff_not_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityAtLeastTwoBaseCut_upper_eq_one_iff_not_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type "at least two"
counting cut's width collapse. -/
abbrev definable_cut_counting_capacity_at_least_two_base_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityAtLeastTwoBaseCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for the concrete base-type counting cut
whose representing HOL formula says that at least three distinct base objects
satisfy the predicate. This specializes the exact-denominator cardinality
threshold machinery at `k = 3` with a constructed formula and a proven
`represents_ge` bridge. -/
noncomputable abbrev definable_cut_counting_capacity_at_least_three_base
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityAtLeastThreeBaseCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type "at least three"
counting cut's interval readout. -/
abbrev definable_cut_counting_capacity_at_least_three_base_interval_eq
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityAtLeastThreeBaseCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type "at least three"
counting cut's lower-endpoint tightness. -/
abbrev definable_cut_counting_capacity_at_least_three_base_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityAtLeastThreeBaseCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type "at least three"
counting cut's upper-endpoint refutation tightness. -/
abbrev definable_cut_counting_capacity_at_least_three_base_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityAtLeastThreeBaseCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type "at least three"
counting cut's open lower endpoint. -/
abbrev definable_cut_counting_capacity_at_least_three_base_lower_eq_zero_iff_not_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityAtLeastThreeBaseCut_lower_eq_zero_iff_not_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type "at least three"
counting cut's open upper endpoint. -/
abbrev definable_cut_counting_capacity_at_least_three_base_upper_eq_one_iff_not_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityAtLeastThreeBaseCut_upper_eq_one_iff_not_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type "at least three"
counting cut's width collapse. -/
abbrev definable_cut_counting_capacity_at_least_three_base_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityAtLeastThreeBaseCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for exact-denominator complement
counting-capacity cardinality thresholds.  A param-free HOL formula `χ` must
represent `ncard (ext p) + k ≤ N`, and every completion's predicate-object
carrier must have exact cardinality `N`; with those guards, `χ` represents
`k / N ≤ 1 - countingCapacity (ext p)`. -/
noncomputable abbrev definable_cut_counting_capacity_complement_cardinality_threshold
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityComplementCardinalityThresholdCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the exact-denominator complement
counting-capacity cardinality-threshold interval readout.  The certified
numeric interval is the existing HOL interval for the formula representing the
finite upper-cardinality threshold. -/
abbrev definable_cut_counting_capacity_complement_cardinality_threshold_interval_eq
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityComplementCardinalityThresholdCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator complement-cardinality
threshold lower-endpoint tightness. -/
abbrev definable_cut_counting_capacity_complement_cardinality_threshold_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityComplementCardinalityThresholdCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator complement-cardinality
threshold upper-endpoint refutation tightness. -/
abbrev definable_cut_counting_capacity_complement_cardinality_threshold_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityComplementCardinalityThresholdCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator complement-cardinality
threshold open lower-endpoint tightness. -/
abbrev definable_cut_counting_capacity_complement_cardinality_threshold_lower_eq_zero_iff_not_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityComplementCardinalityThresholdCut_lower_eq_zero_iff_not_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator complement-cardinality
threshold open upper-endpoint tightness. -/
abbrev definable_cut_counting_capacity_complement_cardinality_threshold_upper_eq_one_iff_not_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityComplementCardinalityThresholdCut_upper_eq_one_iff_not_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator complement-cardinality
threshold width collapse. -/
abbrev definable_cut_counting_capacity_complement_cardinality_threshold_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityComplementCardinalityThresholdCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for the concrete complement counting cut
whose representing HOL formula says that some admissible object does not
satisfy the predicate.  Under an exact carrier-size guard `N`, it certifies the
threshold `1 / N ≤ 1 - countingCapacity (ext p)`. -/
noncomputable abbrev definable_cut_counting_capacity_exists_not_complement
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsNotComplementCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete non-witness complement
counting cut's interval readout. -/
abbrev definable_cut_counting_capacity_exists_not_complement_interval_eq
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsNotComplementCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete non-witness complement
counting cut's lower-endpoint tightness. -/
abbrev definable_cut_counting_capacity_exists_not_complement_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsNotComplementCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete non-witness complement
counting cut's upper-endpoint refutation tightness. -/
abbrev definable_cut_counting_capacity_exists_not_complement_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsNotComplementCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete non-witness complement
counting cut's open lower endpoint. -/
abbrev definable_cut_counting_capacity_exists_not_complement_lower_eq_zero_iff_not_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsNotComplementCut_lower_eq_zero_iff_not_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete non-witness complement
counting cut's open upper endpoint. -/
abbrev definable_cut_counting_capacity_exists_not_complement_upper_eq_one_iff_not_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsNotComplementCut_upper_eq_one_iff_not_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete non-witness complement
counting cut's width collapse. -/
abbrev definable_cut_counting_capacity_exists_not_complement_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsNotComplementCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for exact-denominator finite-frequency
bands.  It composes the lower cardinality threshold and complement
upper-cardinality threshold through `andCut`, so both sides must enter through
their own supplied HOL representation formulae. -/
noncomputable abbrev definable_cut_counting_capacity_cardinality_band
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityCardinalityBandCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the model-level event readout of exact
finite-frequency bands: the certified band event is exactly the conjunction of
the lower-cardinality and upper-cardinality side conditions. -/
abbrev definable_cut_counting_capacity_cardinality_band_event_iff
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityCardinalityBandCut_ge_iff
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact finite-frequency band interval readout:
the certified numeric band interval is the existing HOL interval for the
conjunction of the supplied lower and upper formulas. -/
abbrev definable_cut_counting_capacity_cardinality_band_interval_eq
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityCardinalityBandCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact finite-frequency band lower-endpoint
tightness: lower endpoint `1` is exactly provability of the supplied
lower/upper cardinality conjunction. -/
abbrev definable_cut_counting_capacity_cardinality_band_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityCardinalityBandCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact finite-frequency band upper-endpoint
tightness: upper endpoint `0` is exactly provability of the negation of the
supplied lower/upper cardinality conjunction. -/
abbrev definable_cut_counting_capacity_cardinality_band_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityCardinalityBandCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact finite-frequency band open lower
endpoint tightness. -/
abbrev definable_cut_counting_capacity_cardinality_band_lower_eq_zero_iff_not_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityCardinalityBandCut_lower_eq_zero_iff_not_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact finite-frequency band open upper
endpoint tightness. -/
abbrev definable_cut_counting_capacity_cardinality_band_upper_eq_one_iff_not_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityCardinalityBandCut_upper_eq_one_iff_not_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact finite-frequency band width collapse:
the certified band interval has width zero exactly when the theory decides the
supplied lower/upper cardinality conjunction. -/
abbrev definable_cut_counting_capacity_cardinality_band_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityCardinalityBandCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for the all-HOL proper finite-frequency
band. It certifies the exact event
`1 / N ≤ countingCapacity(ext p)` and
`1 / N ≤ 1 - countingCapacity(ext p)` through the constructed HOL formulas
`∃ x, p x` and `∃ x, ¬ p x`. -/
noncomputable abbrev definable_cut_counting_capacity_exists_and_exists_not_band
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsAndExistsNotBandCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the model-level event readout of the
all-HOL proper finite-frequency band. -/
abbrev definable_cut_counting_capacity_exists_and_exists_not_band_event_iff
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsAndExistsNotBandCut_ge_iff
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the numeric readout of the all-HOL proper
finite-frequency band: the certified event is exactly
`0 < countingCapacity(ext p) < 1` under the exact finite-carrier guard. -/
abbrev definable_cut_counting_capacity_exists_and_exists_not_band_strict_capacity_event_iff
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsAndExistsNotBandCut_ge_iff_countingCapacity_pos_and_lt_one
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the all-HOL proper finite-frequency band's
interval readout. -/
abbrev definable_cut_counting_capacity_exists_and_exists_not_band_interval_eq
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsAndExistsNotBandCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the all-HOL proper finite-frequency band's
lower-endpoint tightness. -/
abbrev definable_cut_counting_capacity_exists_and_exists_not_band_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsAndExistsNotBandCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the all-HOL proper finite-frequency band's
upper-endpoint refutation tightness. -/
abbrev definable_cut_counting_capacity_exists_and_exists_not_band_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsAndExistsNotBandCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the all-HOL proper finite-frequency band's
open lower endpoint. -/
abbrev definable_cut_counting_capacity_exists_and_exists_not_band_lower_eq_zero_iff_not_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsAndExistsNotBandCut_lower_eq_zero_iff_not_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the all-HOL proper finite-frequency band's
open upper endpoint. -/
abbrev definable_cut_counting_capacity_exists_and_exists_not_band_upper_eq_one_iff_not_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsAndExistsNotBandCut_upper_eq_one_iff_not_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the all-HOL proper finite-frequency band's
width collapse. -/
abbrev definable_cut_counting_capacity_exists_and_exists_not_band_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityExistsAndExistsNotBandCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for the concrete base-type
two-to-all-but-one finite-frequency band. It certifies the exact event
`2 / N ≤ countingCapacity(ext p)` and
`1 / N ≤ 1 - countingCapacity(ext p)` through constructed HOL formulas. -/
noncomputable abbrev definable_cut_counting_capacity_two_to_all_but_one_base_band
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityTwoToAllButOneBaseBandCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the model-level event readout of the
concrete base-type two-to-all-but-one finite-frequency band. -/
abbrev definable_cut_counting_capacity_two_to_all_but_one_base_band_event_iff
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityTwoToAllButOneBaseBandCut_ge_iff
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type two-to-all-but-one
finite-frequency band's interval readout. -/
abbrev definable_cut_counting_capacity_two_to_all_but_one_base_band_interval_eq
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityTwoToAllButOneBaseBandCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type two-to-all-but-one
finite-frequency band's lower-endpoint tightness. -/
abbrev definable_cut_counting_capacity_two_to_all_but_one_base_band_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityTwoToAllButOneBaseBandCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type two-to-all-but-one
finite-frequency band's upper-endpoint refutation tightness. -/
abbrev definable_cut_counting_capacity_two_to_all_but_one_base_band_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityTwoToAllButOneBaseBandCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type two-to-all-but-one
finite-frequency band's open lower endpoint. -/
abbrev definable_cut_counting_capacity_two_to_all_but_one_base_band_lower_eq_zero_iff_not_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityTwoToAllButOneBaseBandCut_lower_eq_zero_iff_not_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type two-to-all-but-one
finite-frequency band's open upper endpoint. -/
abbrev definable_cut_counting_capacity_two_to_all_but_one_base_band_upper_eq_one_iff_not_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityTwoToAllButOneBaseBandCut_upper_eq_one_iff_not_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type two-to-all-but-one
finite-frequency band's width collapse. -/
abbrev definable_cut_counting_capacity_two_to_all_but_one_base_band_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateCountingCapacityTwoToAllButOneBaseBandCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for calibrated Sugeno endpoint cuts. An
arbitrary capacity family reaches the proof-theoretic layer only through an
explicit calibration certificate equating Sugeno score `1` with the HOL
universal-predicate event. -/
noncomputable abbrev definable_cut_sugeno_calibrated_forall_endpoint
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCalibratedCrispEndpointGeOneCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the calibrated Sugeno endpoint interval
readout. The certified numeric interval is the existing HOL interval for the
representing universal-predicate formula. -/
abbrev definable_cut_sugeno_calibrated_forall_endpoint_interval_eq
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCalibratedCrispEndpointGeOneCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for calibrated Sugeno endpoint lower endpoint
tightness. -/
abbrev definable_cut_sugeno_calibrated_forall_endpoint_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCalibratedCrispEndpointGeOneCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for calibrated Sugeno endpoint upper endpoint
tightness. -/
abbrev definable_cut_sugeno_calibrated_forall_endpoint_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCalibratedCrispEndpointGeOneCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for calibrated Sugeno endpoint width-zero
tightness. -/
abbrev definable_cut_sugeno_calibrated_forall_endpoint_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCalibratedCrispEndpointGeOneCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for the concrete counting-capacity Sugeno
endpoint cut. This is an endpoint-`1` cut, not a soft fractional Sugeno
threshold theorem. -/
noncomputable abbrev definable_cut_sugeno_counting_forall_endpoint
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingCrispEndpointGeOneCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the counting-capacity Sugeno endpoint
interval readout. The score is Sugeno/counting based, but the certified
interval is the existing HOL interval for the representing universal formula. -/
abbrev definable_cut_sugeno_counting_forall_endpoint_interval_eq
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingCrispEndpointGeOneCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for counting-capacity Sugeno endpoint lower
endpoint tightness. -/
abbrev definable_cut_sugeno_counting_forall_endpoint_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingCrispEndpointGeOneCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for counting-capacity Sugeno endpoint upper
endpoint tightness. -/
abbrev definable_cut_sugeno_counting_forall_endpoint_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingCrispEndpointGeOneCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for counting-capacity Sugeno endpoint width-zero
tightness. -/
abbrev definable_cut_sugeno_counting_forall_endpoint_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingCrispEndpointGeOneCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for exact-denominator normalized-counting
Sugeno cardinality thresholds.  For HOL-induced crisp profiles,
Sugeno/counting reduces to counting capacity of the predicate extension, so a
supplied HOL formula representing `k ≤ ncard (ext p)` certifies the fractional
event `k / N ≤ Sugeno(counting, p)` under exact carrier size `N`. -/
noncomputable abbrev definable_cut_sugeno_counting_cardinality_threshold
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingCardinalityThresholdCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the exact-denominator normalized-counting
Sugeno interval readout.  The certified numeric interval is the existing HOL
interval for the supplied cardinality-threshold formula. -/
abbrev definable_cut_sugeno_counting_cardinality_threshold_interval_eq
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingCardinalityThresholdCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator normalized-counting Sugeno
lower endpoint tightness. -/
abbrev definable_cut_sugeno_counting_cardinality_threshold_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingCardinalityThresholdCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator normalized-counting Sugeno
upper endpoint tightness. -/
abbrev definable_cut_sugeno_counting_cardinality_threshold_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingCardinalityThresholdCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator normalized-counting Sugeno
open lower endpoint tightness. -/
abbrev definable_cut_sugeno_counting_cardinality_threshold_lower_eq_zero_iff_not_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingCardinalityThresholdCut_lower_eq_zero_iff_not_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator normalized-counting Sugeno
open upper endpoint tightness. -/
abbrev definable_cut_sugeno_counting_cardinality_threshold_upper_eq_one_iff_not_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingCardinalityThresholdCut_upper_eq_one_iff_not_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator normalized-counting Sugeno
width-zero tightness. -/
abbrev definable_cut_sugeno_counting_cardinality_threshold_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingCardinalityThresholdCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for the exact-denominator
normalized-counting Sugeno threshold at the HOL existential boundary (`k = 1`).
This packages the existing HOL existence formula as the certified cut for
`1 / N ≤ Sugeno(counting, p)`. -/
noncomputable abbrev definable_cut_sugeno_counting_exists_exact_threshold
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingExistsExactThresholdCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the exact-denominator normalized-counting
Sugeno existential-threshold interval readout. -/
abbrev definable_cut_sugeno_counting_exists_exact_threshold_interval_eq
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingExistsExactThresholdCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator normalized-counting Sugeno
existential-threshold lower endpoint tightness. -/
abbrev definable_cut_sugeno_counting_exists_exact_threshold_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingExistsExactThresholdCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator normalized-counting Sugeno
existential-threshold upper endpoint tightness. -/
abbrev definable_cut_sugeno_counting_exists_exact_threshold_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingExistsExactThresholdCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator normalized-counting Sugeno
existential-threshold open lower endpoint tightness. -/
abbrev definable_cut_sugeno_counting_exists_exact_threshold_lower_eq_zero_iff_not_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingExistsExactThresholdCut_lower_eq_zero_iff_not_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator normalized-counting Sugeno
existential-threshold open upper endpoint tightness. -/
abbrev definable_cut_sugeno_counting_exists_exact_threshold_upper_eq_one_iff_not_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingExistsExactThresholdCut_upper_eq_one_iff_not_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator normalized-counting Sugeno
existential-threshold width-zero tightness. -/
abbrev definable_cut_sugeno_counting_exists_exact_threshold_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingExistsExactThresholdCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for the exact-denominator
normalized-counting Sugeno threshold at the HOL universal boundary (`k = N`).
This packages the existing HOL universal formula as the certified cut for
`N / N ≤ Sugeno(counting, p)`. -/
noncomputable abbrev definable_cut_sugeno_counting_universal_exact_threshold
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingUniversalExactThresholdCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the exact-denominator normalized-counting
Sugeno universal-threshold interval readout. -/
abbrev definable_cut_sugeno_counting_universal_exact_threshold_interval_eq
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingUniversalExactThresholdCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator normalized-counting Sugeno
universal-threshold lower endpoint tightness. -/
abbrev definable_cut_sugeno_counting_universal_exact_threshold_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingUniversalExactThresholdCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator normalized-counting Sugeno
universal-threshold upper endpoint tightness. -/
abbrev definable_cut_sugeno_counting_universal_exact_threshold_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingUniversalExactThresholdCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator normalized-counting Sugeno
universal-threshold open lower endpoint tightness. -/
abbrev definable_cut_sugeno_counting_universal_exact_threshold_lower_eq_zero_iff_not_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingUniversalExactThresholdCut_lower_eq_zero_iff_not_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator normalized-counting Sugeno
universal-threshold open upper endpoint tightness. -/
abbrev definable_cut_sugeno_counting_universal_exact_threshold_upper_eq_one_iff_not_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingUniversalExactThresholdCut_upper_eq_one_iff_not_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for exact-denominator normalized-counting Sugeno
universal-threshold width-zero tightness. -/
abbrev definable_cut_sugeno_counting_universal_exact_threshold_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingUniversalExactThresholdCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for the concrete base-type
normalized-counting Sugeno cut whose representing HOL formula says that at
least two distinct base objects satisfy the predicate. -/
noncomputable abbrev definable_cut_sugeno_counting_at_least_two_base
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingAtLeastTwoBaseCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type normalized-counting
Sugeno "at least two" interval readout. -/
abbrev definable_cut_sugeno_counting_at_least_two_base_interval_eq
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingAtLeastTwoBaseCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type normalized-counting
Sugeno "at least two" lower-endpoint tightness. -/
abbrev definable_cut_sugeno_counting_at_least_two_base_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingAtLeastTwoBaseCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type normalized-counting
Sugeno "at least two" upper-endpoint refutation tightness. -/
abbrev definable_cut_sugeno_counting_at_least_two_base_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingAtLeastTwoBaseCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type normalized-counting
Sugeno "at least two" open lower-endpoint tightness. -/
abbrev definable_cut_sugeno_counting_at_least_two_base_lower_eq_zero_iff_not_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingAtLeastTwoBaseCut_lower_eq_zero_iff_not_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type normalized-counting
Sugeno "at least two" open upper-endpoint tightness. -/
abbrev definable_cut_sugeno_counting_at_least_two_base_upper_eq_one_iff_not_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingAtLeastTwoBaseCut_upper_eq_one_iff_not_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type normalized-counting
Sugeno "at least two" width collapse. -/
abbrev definable_cut_sugeno_counting_at_least_two_base_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingAtLeastTwoBaseCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index constructor for the concrete base-type
normalized-counting Sugeno cut whose representing HOL formula says that at
least three distinct base objects satisfy the predicate. -/
noncomputable abbrev definable_cut_sugeno_counting_at_least_three_base
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingAtLeastThreeBaseCut
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type normalized-counting
Sugeno "at least three" interval readout. -/
abbrev definable_cut_sugeno_counting_at_least_three_base_interval_eq
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingAtLeastThreeBaseCut_intervalOfConsistent
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type normalized-counting
Sugeno "at least three" lower-endpoint tightness. -/
abbrev definable_cut_sugeno_counting_at_least_three_base_lower_eq_one_iff_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingAtLeastThreeBaseCut_lower_eq_one_iff_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type normalized-counting
Sugeno "at least three" upper-endpoint refutation tightness. -/
abbrev definable_cut_sugeno_counting_at_least_three_base_upper_eq_zero_iff_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingAtLeastThreeBaseCut_upper_eq_zero_iff_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type normalized-counting
Sugeno "at least three" open lower-endpoint tightness. -/
abbrev definable_cut_sugeno_counting_at_least_three_base_lower_eq_zero_iff_not_provable
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingAtLeastThreeBaseCut_lower_eq_zero_iff_not_provable
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type normalized-counting
Sugeno "at least three" open upper-endpoint tightness. -/
abbrev definable_cut_sugeno_counting_at_least_three_base_upper_eq_one_iff_not_provable_not
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingAtLeastThreeBaseCut_upper_eq_one_iff_not_provable_not
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for the concrete base-type normalized-counting
Sugeno "at least three" width collapse. -/
abbrev definable_cut_sugeno_counting_at_least_three_base_width_eq_zero_iff_decides
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  predicateSugenoCountingAtLeastThreeBaseCut_width_eq_zero_iff_decides
    (Base := Base) (Const := Const) (T := T)

/-! ### Certified Boolean closure for already-discharged definable cuts

These aliases expose the safe closure layer: once each premise has a real
`represents_ge` certificate, the certified events can be composed by HOL
connectives. They are not existence theorems for arbitrary new numeric scores.
-/

/-- Public theorem-index name for conjunctive certified cuts: certainty of the
joint cut is exactly universal satisfaction of both original threshold events. -/
abbrev definable_cut_and_lower_eq_one_iff_forall_both_ge
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  ExtensionalDefinableCut.andCut_lower_eq_one_iff_forall_both_ge
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for disjunctive certified cuts: certainty of the
alternative cut is exactly universal satisfaction of either threshold event. -/
abbrev definable_cut_or_lower_eq_one_iff_forall_either_ge
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  ExtensionalDefinableCut.orCut_lower_eq_one_iff_forall_either_ge
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for complement certified cuts: certainty of the
complement is universal failure of the original threshold event. -/
abbrev definable_cut_complement_lower_eq_one_iff_forall_not_ge
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  ExtensionalDefinableCut.notCut_lower_eq_one_iff_forall_not_ge
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for implication certified cuts: certainty of the
rule cut is universal preservation from premise threshold to conclusion
threshold. -/
abbrev definable_cut_implication_lower_eq_one_iff_forall_imp_ge
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  ExtensionalDefinableCut.impCut_lower_eq_one_iff_forall_imp_ge
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for refuting conjunctive certified cuts:
refutation of the joint cut is universal failure of simultaneous threshold
satisfaction. -/
abbrev definable_cut_and_upper_eq_zero_iff_forall_not_both_ge
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  ExtensionalDefinableCut.andCut_upper_eq_zero_iff_forall_not_both_ge
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for refuting disjunctive certified cuts:
refutation of the alternative cut is universal failure of both threshold
events. -/
abbrev definable_cut_or_upper_eq_zero_iff_forall_not_either_ge
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  ExtensionalDefinableCut.orCut_upper_eq_zero_iff_forall_not_either_ge
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for refuting complement certified cuts:
refutation of the complement is universal satisfaction of the original
threshold event. -/
abbrev definable_cut_complement_upper_eq_zero_iff_forall_ge
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  ExtensionalDefinableCut.notCut_upper_eq_zero_iff_forall_ge
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for refuting implication certified cuts:
refutation of the rule cut is universal counterexample behavior. -/
abbrev definable_cut_implication_upper_eq_zero_iff_forall_counterexample_ge
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  ExtensionalDefinableCut.impCut_upper_eq_zero_iff_forall_counterexample_ge
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for nonempty finite conjunctions of certified
cuts: certainty of the folded rule gate is universal satisfaction of the head
cut and every tail cut. Every member still enters only through its own
`represents_ge` certificate. -/
abbrev definable_cut_all_lower_eq_one_iff_forall_all_ge
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  ExtensionalDefinableCut.allCut_lower_eq_one_iff_forall_all_ge
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for refuting a nonempty finite conjunction of
certified cuts: every canonical model fails at least one certified threshold
event in the folded gate. -/
abbrev definable_cut_all_upper_eq_zero_iff_forall_not_all_ge
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  ExtensionalDefinableCut.allCut_upper_eq_zero_iff_forall_not_all_ge
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for finite certified rule gates: certainty of
the implication from the folded premise gate to the conclusion cut is universal
threshold preservation from all premises to the conclusion. -/
abbrev definable_cut_all_implication_lower_eq_one_iff_forall_all_imp_ge
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  ExtensionalDefinableCut.allCut_impCut_lower_eq_one_iff_forall_all_imp_ge
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for refuting finite certified rule gates:
refutation of the implication from the folded premise gate to the conclusion
cut is universal finite-premise counterexample behavior. -/
abbrev definable_cut_all_implication_upper_eq_zero_iff_forall_all_counterexample_ge
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  ExtensionalDefinableCut.allCut_impCut_upper_eq_zero_iff_forall_all_counterexample_ge
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for certified-cut modus ponens. Concrete PLN rule
families must still prove their implication cut before using this consumer. -/
abbrev definable_cut_modus_ponens
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  ExtensionalDefinableCut.lower_eq_one_of_impCut_lower_eq_one_of_lower_eq_one
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for multi-premise certified-cut modus ponens.
Concrete PLN rule families must still prove the finite-gate implication cut
before using this consumer. -/
abbrev definable_cut_all_modus_ponens
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  ExtensionalDefinableCut.lower_eq_one_of_allCut_impCut_lower_eq_one_of_allCut_lower_eq_one
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for certified-cut modus tollens over the same
generic implication-cut surface. -/
abbrev definable_cut_modus_tollens
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  ExtensionalDefinableCut.notCut_lower_eq_one_of_impCut_lower_eq_one_of_notCut_lower_eq_one
    (Base := Base) (Const := Const) (T := T)

/-- Public theorem-index name for refuting an implication cut from a certain
premise cut and a refuted conclusion cut. -/
abbrev definable_cut_implication_refuted_of_premise_certain_of_conclusion_refuted
    {Base : Type u} {Const : Ty Base → Type v}
    {T : ClosedTheorySet (WithParams Const)} :=
  ExtensionalDefinableCut.impCut_upper_eq_zero_of_lower_eq_one_of_upper_eq_zero
    (Base := Base) (Const := Const) (T := T)


end Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex
