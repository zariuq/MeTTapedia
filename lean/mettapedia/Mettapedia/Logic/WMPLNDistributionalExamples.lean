import Mettapedia.Logic.MarkovTransitionXiExamples
import Mettapedia.Logic.WMPLNDistributionalTruthFunctions

noncomputable section

namespace Mettapedia.Logic.WMPLNDistributionalExamples

open Mettapedia.Logic
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNJointEvidence
open Mettapedia.Logic.WMMarkovCanonical
open Mettapedia.Logic.WMPLNDistributionalTruthFunctions
open Mettapedia.Logic.MarkovPredictiveChaining
open Mettapedia.Logic.UniversalPrediction
open scoped ENNReal

-- `MarkovTransitionXiExamples` provides the concrete transition-state
-- constructors used by the small predictive example below.

/-!
# WM-PLN Distributional Worked Examples

This file consolidates a few small, textbook-style examples for the main
distribution-backed WM-PLN truth-view regimes.

The goal is not to replace the larger theory files, but to provide one easy
entry point where readers can see:

* a Dirichlet-over-worlds proposition example,
* a binary Markov transition / predictive example,
* a finite-population hypergeometric interval example.

For larger demonstrations and surrounding discussion, see:

* `Mettapedia.Logic.WMPLNDistributionalTruthFunctions`
* `Mettapedia.Logic.PLNMapleCourtDemo`
* `Mettapedia.Logic.MarkovPredictiveChaining`
* `Mettapedia.Logic.PLNConjunction`
* `../../../../papers/wm-pln-book_v3.tex`, especially the worked Dirichlet-over-worlds
  section.

Every theorem below is either:

* an exact rational equality, intended as the strongest showcase result, or
* an interval-containment / unit-interval sanity fact, marked with names like
  `_bounds`, `_in_unit`, or `_width_nonneg`.

Historical note: the older `Mettapedia.Logic.PLNMettaTruthFunctions` surface
has been retired. The classical mirrored/theorem-backed split now lives in
`PeTTaLibPLNTruthFunctions`, `WMPLNJustifiedTruthFunctions`, and the
distributional file imported here.
-/

/-! ## Dirichlet-over-worlds: one binary proposition -/

abbrev coinAtom : Fin 1 := ⟨0, by decide⟩
abbrev coinWorld0 : Fin (2 ^ 1) := ⟨0, by decide⟩
abbrev coinWorld1 : Fin (2 ^ 1) := ⟨1, by decide⟩

/-- A one-atom joint-evidence example with 7 world-counts for `false` and
3 world-counts for `true`. This is the smallest Dirichlet-over-worlds carrier
that already exposes proposition STV/WTV/ITV views. -/
def binaryCoinJointEvidence : Mettapedia.Logic.PLNJointEvidence.JointEvidence 1 :=
  fun w => if w = coinWorld0 then 7 else 3

theorem binaryCoin_propEvidence :
    JointEvidence.propEvidence (n := 1) (E := binaryCoinJointEvidence) coinAtom = ⟨3, 7⟩ := by
  ext <;>
    simp [JointEvidence.propEvidence, JointEvidence.countWorld,
      Mettapedia.Logic.CompletePLN.worldToAssignment,
      binaryCoinJointEvidence, coinWorld0,
      Fin.sum_univ_two]

theorem binaryCoin_propSTV_strength :
    (truthDirichletOverWorldsPropSTV 2 binaryCoinJointEvidence coinAtom).strength = 3 / 10 := by
  have hE : binaryCoinJointEvidence.propEvidence 0 = ⟨3, 7⟩ := by
    simpa [coinAtom] using binaryCoin_propEvidence
  simp [truthDirichletOverWorldsPropSTV,
    Mettapedia.Logic.EvidenceSTVBridge.evidenceToDeductionSTV]
  rw [hE]
  norm_num [Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.toStrength,
    Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.total,
    Mettapedia.Logic.PLNDeduction.clamp01]

theorem binaryCoin_propSTV_confidence :
    (truthDirichletOverWorldsPropSTV 2 binaryCoinJointEvidence coinAtom).confidence = 5 / 6 := by
  have hE : binaryCoinJointEvidence.propEvidence 0 = ⟨3, 7⟩ := by
    simpa [coinAtom] using binaryCoin_propEvidence
  simp [truthDirichletOverWorldsPropSTV,
    Mettapedia.Logic.EvidenceSTVBridge.evidenceToDeductionSTV]
  rw [hE]
  norm_num [Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.toConfidence,
    Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.total,
    Mettapedia.Logic.PLNDeduction.clamp01]

theorem binaryCoin_propITVBayesExact95_bounds :
    let itv := truthDirichletOverWorldsPropITVBayesExact95
      Mettapedia.Logic.EvidenceClass.BinaryContext.jeffreys
      binaryCoinJointEvidence coinAtom
    itv.lower ∈ Set.Icc 0 1 ∧
      itv.upper ∈ Set.Icc 0 1 ∧
      itv.credibility ∈ Set.Icc 0 1 := by
  intro itv
  exact ⟨itv.lower_in_unit, itv.upper_in_unit, itv.credibility_in_unit⟩

/-! ## Markov-Dirichlet: one observed binary transition -/

abbrev bit0 : Fin 2 := Mettapedia.Logic.MarkovPredictiveChaining.bit0
abbrev bit1 : Fin 2 := Mettapedia.Logic.MarkovPredictiveChaining.bit1

/-- Smallest nontrivial Markov WM state: one observed transition `0 → 1`. -/
def oneStep01State : MarkovTransitionWMState 2 :=
  markov_transitionMultiset (k := 2) [bit0, bit1]

abbrev oneStep01Counts : TransCounts 2 :=
  TransCounts.bump (0 : TransCounts 2) bit0 bit1

theorem oneStep01_summary :
    TransCounts.summary (k := 2) [bit0, bit1] =
      some (oneStep01Counts, bit1) := by
  rfl

theorem oneStep01_transitionEvidence :
    BinaryWorldModel.evidence
        (State := MarkovTransitionWMState 2)
        (Query := MarkovTransitionQuery 2)
        oneStep01State (.link bit0 bit1) = ⟨1, 0⟩ := by
  have h :=
    markov_linkEvidence_transitionMultiset_eq_of_summary
      (k := 2) (xs := [bit0, bit1]) (c := oneStep01Counts)
      (last := bit1) oneStep01_summary bit0 bit1
  simpa [oneStep01State, markov_binaryEvidenceOfRowEvidence, markov_rowEvidence,
    rowEvidence, oneStep01Counts, Fin.sum_univ_two]
    using h

theorem oneStep01_walley_lower :
    (truthMarkovDirichletTransitionITVWalley
      Mettapedia.Logic.PLNWorldModel.IDMPredictiveContext.default
      oneStep01State (.link bit0 bit1)).lower = 1 / 3 := by
  unfold truthMarkovDirichletTransitionITVWalley
  unfold Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryITV
  unfold Mettapedia.Logic.PLNWorldModel.ITVSemantics.walleyIDMPredictive
  rw [oneStep01_transitionEvidence]
  norm_num [Mettapedia.Logic.PLNWorldModel.IDMPredictiveContext.default,
    Mettapedia.Logic.PLNIndefiniteTruth.ITV.fromWalleyIDMPredictive]

theorem oneStep01_walley_upper :
    (truthMarkovDirichletTransitionITVWalley
      Mettapedia.Logic.PLNWorldModel.IDMPredictiveContext.default
      oneStep01State (.link bit0 bit1)).upper = 1 := by
  unfold truthMarkovDirichletTransitionITVWalley
  unfold Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryITV
  unfold Mettapedia.Logic.PLNWorldModel.ITVSemantics.walleyIDMPredictive
  rw [oneStep01_transitionEvidence]
  norm_num [Mettapedia.Logic.PLNWorldModel.IDMPredictiveContext.default,
    Mettapedia.Logic.PLNIndefiniteTruth.ITV.fromWalleyIDMPredictive]

theorem oneStep01_walley_credibility :
    (truthMarkovDirichletTransitionITVWalley
      Mettapedia.Logic.PLNWorldModel.IDMPredictiveContext.default
      oneStep01State (.link bit0 bit1)).credibility = 1 / 3 := by
  unfold truthMarkovDirichletTransitionITVWalley
  unfold Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryITV
  unfold Mettapedia.Logic.PLNWorldModel.ITVSemantics.walleyIDMPredictive
  rw [oneStep01_transitionEvidence]
  norm_num [Mettapedia.Logic.PLNWorldModel.IDMPredictiveContext.default,
    Mettapedia.Logic.PLNIndefiniteTruth.ITV.fromWalleyIDMPredictive]

theorem binary_markovTwoStepArrivalMass_example
    (prior : Fin 2 → Mettapedia.Logic.EvidenceDirichlet.DirichletParams 2)
    (prev dst : Fin 2) (c : TransCounts 2) :
    truthMarkovDirichletPredictiveChainMass (by decide) prior prev c [bit0, dst] +
      truthMarkovDirichletPredictiveChainMass (by decide) prior prev c [bit1, dst] =
      Mettapedia.Logic.MarkovPredictiveChaining.markovTwoStepArrivalMass
        (k := 2) (by decide) prior prev c dst := by
  symm
  simpa [truthMarkovDirichletPredictiveChainMass] using
    Mettapedia.Logic.MarkovPredictiveChaining.binary_markovTwoStepArrivalMass_expand
      (hk := by decide) (prior := prior) (prev := prev) (dst := dst) (c := c)

/-! ## Hypergeometric finite-population conjunction -/

/-- In the example below, `n = 10` is the population size, `a = 8` is the
number of successes in the population, and `b = 7` is the draw count. -/

theorem hypergeometric_10_8_7_modal_strength :
    (truthConjunctionHypergeometricModal 10 8 7).s = 3 / 5 := by
  norm_num [truthConjunctionHypergeometricModal,
    Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthConjunctionHypergeometric,
    Mettapedia.Logic.PLNConjunction.hypergeometricMode]

theorem hypergeometric_10_8_7_interval_lower :
    (truthConjunctionHypergeometricInterval 10 8 7).lower = 1 / 2 := by
  norm_num [truthConjunctionHypergeometricInterval,
    hypergeometricSupportLowerCount, hypergeometricSupportUpperCount,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

theorem hypergeometric_10_8_7_interval_upper :
    (truthConjunctionHypergeometricInterval 10 8 7).upper = 7 / 10 := by
  norm_num [truthConjunctionHypergeometricInterval,
    hypergeometricSupportLowerCount, hypergeometricSupportUpperCount,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

theorem hypergeometric_10_8_7_interval_width :
    (truthConjunctionHypergeometricInterval 10 8 7).width = 1 / 5 := by
  unfold Mettapedia.Logic.PLNIndefiniteTruth.ITV.width
  rw [hypergeometric_10_8_7_interval_lower, hypergeometric_10_8_7_interval_upper]
  norm_num

theorem hypergeometric_10_8_7_interval_credibility_in_unit :
    (truthConjunctionHypergeometricInterval 10 8 7).credibility ∈ Set.Icc 0 1 :=
  truthConjunctionHypergeometricInterval_credibility_in_unit 10 8 7

/-- Equal-tailed 95% CDF example with `n = 20`, `a = 10`, `b = 10`.

This showcases the new quantile/CDF surface at a clean symmetric point. The
current example package records the nominal 95% credibility and the fact that
the resulting ITV stays inside `[0,1]`; a fully exact endpoint calculation can
be added later as a dedicated arithmetic refinement.
-/

theorem hypergeometric_20_10_10_cdf95_credibility :
    (truthConjunctionHypergeometricCDFInterval95 20 10 10).credibility = 19 / 20 := by
  simpa using truthConjunctionHypergeometricCDFInterval95_credibility_eq 20 10 10

theorem hypergeometric_20_10_10_cdf95_width_nonneg :
    0 ≤ (truthConjunctionHypergeometricCDFInterval95 20 10 10).width :=
  truthConjunctionHypergeometricCDFInterval95_width_nonneg 20 10 10

theorem hypergeometric_20_10_10_cdf95_bounds_in_unit :
    let itv := truthConjunctionHypergeometricCDFInterval95 20 10 10
    itv.lower ∈ Set.Icc 0 1 ∧ itv.upper ∈ Set.Icc 0 1 := by
  intro itv
  exact ⟨itv.lower_in_unit, itv.upper_in_unit⟩

end Mettapedia.Logic.WMPLNDistributionalExamples
