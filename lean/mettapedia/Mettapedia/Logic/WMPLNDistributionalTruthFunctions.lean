import Mettapedia.Logic.EvidenceSTVBridge
import Mettapedia.Logic.MarkovPredictiveChaining
import Mettapedia.Logic.PLNIndefiniteTruthBridge
import Mettapedia.Logic.PLNJointEvidence
import Mettapedia.Logic.WMMarkovCanonical
import Mettapedia.Logic.WMPLNJustifiedTruthFunctions
import Mettapedia.Logic.WorldModelITV
import Mathlib.Data.Finset.Interval

noncomputable section

namespace Mettapedia.Logic.WMPLNDistributionalTruthFunctions

open Mettapedia.Logic
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNJointEvidence
open Mettapedia.Logic.WMMarkovCanonical
open Mettapedia.Logic.MarkovPredictiveChaining
open scoped ENNReal

/-!
# WM-PLN Distributional Truth Functions

This file gathers the main distribution-backed truth-view families that sit
above the evidence carriers already formalized in the WM-PLN development.

The design follows the `BinaryWorldModel` principle: truth values are **views**
of evidence, not the primary semantic objects. The point of this file is to
publish those views in one discoverable place without collapsing distinct
regimes into a single overloaded `truthConjunction`-style API.

Current public regimes:

* Dirichlet-over-worlds joint-evidence views
  - proposition/link STV views
  - proposition/link WTV views
  - proposition/link ITV views (exact-invCDF Bayesian 95%)
* Markov-Dirichlet transition-query views
  - STV / WTV query views
  - Walley-IDM interval view
  - predictive chain mass (process-level rather than additive TV)
* Hypergeometric finite-population conjunction views
  - modal TV point view (re-exported from `WMPLNJustifiedTruthFunctions`)
  - support ITV, exposing the exact finite-population support interval
  - equal-tailed 95% CDF ITV, normalized over the clipped finite count window

The interval surface for hypergeometric conjunction is intentionally packaged as
an **honest support interval**. The current tree has PMF/CDF machinery, but not
yet a theorem-backed central-quantile selector for the raw support law itself.
This file now adds a second, explicit equal-tailed 95% CDF interval view by
normalizing the PMF over the clipped finite count window. This keeps the public
surface truthful for both regimes:

* `truthConjunctionHypergeometricInterval`
  - exact support interval
* `truthConjunctionHypergeometricCDFInterval95`
  - genuine equal-tailed CDF interval on the normalized clipped count window

The CDF interval is intentionally named with its confidence level and should
not be mistaken for the support ITV above.

Worked examples for these public surfaces live in
`Mettapedia.Logic.WMPLNDistributionalExamples`.

Historical note: the older `Mettapedia.Logic.PLNMettaTruthFunctions` surface
has been retired. The classical mirrored/theorem-backed split now lives in
`PeTTaLibPLNTruthFunctions`, `WMPLNJustifiedTruthFunctions`, and this
distributional sibling.
-/

abbrev STV := Mettapedia.Logic.EvidenceSTVBridge.DeductionSTV
abbrev WTV := Mettapedia.Logic.PLNWeightTV.WTV
abbrev ITV := Mettapedia.Logic.PLNIndefiniteTruth.ITV
abbrev TV := Mettapedia.Logic.WMPLNJustifiedTruthFunctions.TV
abbrev BinaryContext := Mettapedia.Logic.EvidenceClass.BinaryContext
abbrev IDMPredictiveContext := Mettapedia.Logic.PLNWorldModel.IDMPredictiveContext

abbrev JointEvidence (n : ℕ) := Mettapedia.Logic.PLNJointEvidence.JointEvidence n

/-! ## Dirichlet-over-worlds joint-evidence views -/

/-- STV proposition view extracted from the Dirichlet-over-worlds carrier. -/
noncomputable def truthDirichletOverWorldsPropSTV
    (κ : ℝ≥0∞) {n : ℕ} (E : JointEvidence n) (A : Fin n) : STV :=
  Mettapedia.Logic.EvidenceSTVBridge.evidenceToDeductionSTV κ
    (Mettapedia.Logic.PLNJointEvidence.JointEvidence.propEvidence (n := n) (E := E) A)

/-- STV link view extracted from the Dirichlet-over-worlds carrier. -/
noncomputable def truthDirichletOverWorldsLinkSTV
    (κ : ℝ≥0∞) {n : ℕ} (E : JointEvidence n) (A B : Fin n) : STV :=
  Mettapedia.Logic.EvidenceSTVBridge.evidenceToDeductionSTV κ
    (Mettapedia.Logic.PLNJointEvidence.JointEvidence.linkEvidence (n := n) (E := E) A B)

/-- WTV proposition view extracted from the Dirichlet-over-worlds carrier. -/
noncomputable def truthDirichletOverWorldsPropWTV
    (κ : ℝ≥0∞) {n : ℕ} (E : JointEvidence n) (A : Fin n) : WTV :=
  Mettapedia.Logic.PLNJointEvidence.JointEvidence.propWTV κ E A

/-- WTV link view extracted from the Dirichlet-over-worlds carrier. -/
noncomputable def truthDirichletOverWorldsLinkWTV
    (κ : ℝ≥0∞) {n : ℕ} (E : JointEvidence n) (A B : Fin n) : WTV :=
  Mettapedia.Logic.PLNJointEvidence.JointEvidence.linkWTV κ E A B

/-- Exact-invCDF 95% Bayesian ITV proposition view extracted from the
Dirichlet-over-worlds carrier. -/
noncomputable def truthDirichletOverWorldsPropITVBayesExact95
    {n : ℕ} (ctx : BinaryContext) (E : JointEvidence n) (A : Fin n) : ITV :=
  Mettapedia.Logic.PLNIndefiniteTruth.ITV.fromBayesCredible95ExactInvCDF
    (Mettapedia.Logic.PLNJointEvidence.JointEvidence.propEvidence (n := n) (E := E) A) ctx

/-- Exact-invCDF 95% Bayesian ITV link view extracted from the
Dirichlet-over-worlds carrier. -/
noncomputable def truthDirichletOverWorldsLinkITVBayesExact95
    {n : ℕ} (ctx : BinaryContext) (E : JointEvidence n) (A B : Fin n) : ITV :=
  Mettapedia.Logic.PLNIndefiniteTruth.ITV.fromBayesCredible95ExactInvCDF
    (Mettapedia.Logic.PLNJointEvidence.JointEvidence.linkEvidence (n := n) (E := E) A B) ctx

@[simp] theorem truthDirichletOverWorldsPropWTV_eq_propWTV
    (κ : ℝ≥0∞) {n : ℕ} (E : JointEvidence n) (A : Fin n) :
    truthDirichletOverWorldsPropWTV κ E A =
      Mettapedia.Logic.PLNJointEvidence.JointEvidence.propWTV κ E A := rfl

@[simp] theorem truthDirichletOverWorldsLinkWTV_eq_linkWTV
    (κ : ℝ≥0∞) {n : ℕ} (E : JointEvidence n) (A B : Fin n) :
    truthDirichletOverWorldsLinkWTV κ E A B =
      Mettapedia.Logic.PLNJointEvidence.JointEvidence.linkWTV κ E A B := rfl

@[simp] theorem truthDirichletOverWorldsPropITVBayesExact95_eq
    {n : ℕ} (ctx : BinaryContext) (E : JointEvidence n) (A : Fin n) :
    truthDirichletOverWorldsPropITVBayesExact95 ctx E A =
      Mettapedia.Logic.PLNIndefiniteTruth.ITV.fromBayesCredible95ExactInvCDF
        (Mettapedia.Logic.PLNJointEvidence.JointEvidence.propEvidence (n := n) (E := E) A) ctx := rfl

@[simp] theorem truthDirichletOverWorldsLinkITVBayesExact95_eq
    {n : ℕ} (ctx : BinaryContext) (E : JointEvidence n) (A B : Fin n) :
    truthDirichletOverWorldsLinkITVBayesExact95 ctx E A B =
      Mettapedia.Logic.PLNIndefiniteTruth.ITV.fromBayesCredible95ExactInvCDF
        (Mettapedia.Logic.PLNJointEvidence.JointEvidence.linkEvidence (n := n) (E := E) A B) ctx := rfl

/-! ## Markov-Dirichlet transition-query views -/

/-- STV view of a binary transition query over the Markov Dirichlet carrier. -/
noncomputable def truthMarkovDirichletTransitionSTV
    (κ : ℝ≥0∞) {k : ℕ} (W : MarkovTransitionWMState k) (q : MarkovTransitionQuery k) : STV :=
  Mettapedia.Logic.EvidenceSTVBridge.evidenceToDeductionSTV κ
    (Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.evidence
      (State := MarkovTransitionWMState k) (Query := MarkovTransitionQuery k) W q)

/-- WTV view of a binary transition query over the Markov Dirichlet carrier. -/
noncomputable def truthMarkovDirichletTransitionWTV
    (κ : ℝ≥0∞) {k : ℕ} (W : MarkovTransitionWMState k) (q : MarkovTransitionQuery k) : WTV :=
  Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryWTV
    (State := MarkovTransitionWMState k) (Query := MarkovTransitionQuery k) κ W q

/-- Walley-IDM ITV view of a binary transition query over the Markov Dirichlet
carrier. This is the interval-facing predictive view for the transition row. -/
noncomputable abbrev truthMarkovDirichletTransitionITVWalley
    {k : ℕ} (ctx : IDMPredictiveContext) (W : MarkovTransitionWMState k)
    (q : MarkovTransitionQuery k) : ITV :=
  Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryITV
    (State := MarkovTransitionWMState k) (Query := MarkovTransitionQuery k)
    Mettapedia.Logic.PLNWorldModel.ITVSemantics.walleyIDMPredictive ctx W q

/-- Exact-invCDF 95% Bayesian ITV view of a binary transition query over the
Markov Dirichlet carrier. -/
noncomputable def truthMarkovDirichletTransitionITVBayesExact95
    {k : ℕ} (ctx : BinaryContext) (W : MarkovTransitionWMState k)
    (q : MarkovTransitionQuery k) : ITV :=
  Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryITV
    (State := MarkovTransitionWMState k) (Query := MarkovTransitionQuery k)
    Mettapedia.Logic.PLNWorldModel.ITVSemantics.bayesCredibleExact95 ctx W q

/-- Sequential predictive chain mass for Markov-Dirichlet futures.
This is intentionally not collapsed into STV/WTV because it is a path-mass
process quantity rather than a single additive query view. -/
noncomputable def truthMarkovDirichletPredictiveChainMass
    {k : ℕ} (hk : 0 < k)
    (prior : Fin k → Mettapedia.Logic.EvidenceDirichlet.DirichletParams k)
    (prev : Fin k) (c : Mettapedia.Logic.UniversalPrediction.TransCounts k)
    (ys : List (Fin k)) : ℝ≥0∞ :=
  Mettapedia.Logic.MarkovPredictiveChaining.markovWMPosteriorChain
    (k := k) hk prior prev c ys

theorem truthMarkovDirichletTransitionITVWalley_width_add_credibility
    {k : ℕ} (ctx : IDMPredictiveContext) (W : MarkovTransitionWMState k)
    (q : MarkovTransitionQuery k) :
    (truthMarkovDirichletTransitionITVWalley ctx W q).width +
      (truthMarkovDirichletTransitionITVWalley ctx W q).credibility = 1 := by
  change
    Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryITVWidth
        Mettapedia.Logic.PLNWorldModel.ITVSemantics.walleyIDMPredictive ctx W q +
      Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryITVCredibility
        Mettapedia.Logic.PLNWorldModel.ITVSemantics.walleyIDMPredictive ctx W q = 1
  exact
    Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryITVWidth_add_queryITVCredibility_walley
      (State := MarkovTransitionWMState k) (Query := MarkovTransitionQuery k) ctx W q

theorem truthMarkovDirichletPredictiveChainMass_le_one
    {k : ℕ} (hk : 0 < k) (prior : Fin k → Mettapedia.Logic.EvidenceDirichlet.DirichletParams k)
    (prev : Fin k) (c : Mettapedia.Logic.UniversalPrediction.TransCounts k)
    (ys : List (Fin k)) :
    truthMarkovDirichletPredictiveChainMass hk prior prev c ys ≤ 1 := by
  exact Mettapedia.Logic.MarkovPredictiveChaining.markovWMPosteriorChain_le_one
    (k := k) hk prior prev c ys

/-! ## Hypergeometric finite-population conjunction views -/

/-- Modal point view for finite-population conjunction, re-exported from the
WM-justified truth-function surface. -/
abbrev truthConjunctionHypergeometricModal :=
  Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthConjunctionHypergeometric

/-- Upper support count of the hypergeometric intersection law, clipped to the
ambient population size for totalized inputs. -/
def hypergeometricSupportUpperCount (n a b : ℕ) : ℕ :=
  min n (min a b)

/-- Lower support count of the hypergeometric intersection law, clipped into the
valid support interval for totalized inputs. -/
def hypergeometricSupportLowerCount (n a b : ℕ) : ℕ :=
  min (hypergeometricSupportUpperCount n a b) (a + b - n)

/-- Interval view for finite-population conjunction.

This packages the exact support interval of the hypergeometric overlap law as
an ITV. The credibility coordinate reuses the modal PMF mass, clamped into
`[0,1]` for a stable public view.
-/
noncomputable def truthConjunctionHypergeometricInterval (n a b : ℕ) : ITV :=
  let lowerCount := hypergeometricSupportLowerCount n a b
  let upperCount := hypergeometricSupportUpperCount n a b
  let cred :=
    Mettapedia.Logic.PLNDeduction.clamp01
      ((truthConjunctionHypergeometricModal n a b).c)
  Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility
    (if _ : n = 0 then 0 else (lowerCount : ℝ) / n)
    (if _ : n = 0 then 0 else (upperCount : ℝ) / n)
    cred
    (by
      by_cases hn : n = 0
      · simp [hn]
      · have hcounts : lowerCount ≤ upperCount := Nat.min_le_left _ _
        have hcountsR : (lowerCount : ℝ) ≤ (upperCount : ℝ) := by
          exact_mod_cast hcounts
        have hnR : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
        simpa [hn] using div_le_div_of_nonneg_right hcountsR hnR)
    (by
      by_cases hn : n = 0
      · simp [hn]
      · simp [hn]
        exact div_nonneg (by positivity) (by exact_mod_cast Nat.zero_le n))
    (by
      by_cases hn : n = 0
      · simp [hn]
      · have hup : upperCount ≤ n := Nat.min_le_left _ _
        have hupR : (upperCount : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast hup
        have hnR : 0 ≤ (n : ℝ) := by positivity
        simp [hn]
        have hdiv : (upperCount : ℝ) / n ≤ (n : ℝ) / n := by
          exact div_le_div_of_nonneg_right hupR hnR
        have hnR_ne : (n : ℝ) ≠ 0 := by
          exact_mod_cast Nat.ne_of_gt (Nat.pos_of_ne_zero hn)
        simpa [hnR_ne] using hdiv)
    (by
      constructor
      · exact Mettapedia.Logic.PLNDeduction.clamp01_nonneg _
      · exact Mettapedia.Logic.PLNDeduction.clamp01_le_one _)

theorem truthConjunctionHypergeometricInterval_width_nonneg (n a b : ℕ) :
    0 ≤ (truthConjunctionHypergeometricInterval n a b).width :=
  (truthConjunctionHypergeometricInterval n a b).width_nonneg

theorem truthConjunctionHypergeometricInterval_credibility_in_unit (n a b : ℕ) :
    (truthConjunctionHypergeometricInterval n a b).credibility ∈ Set.Icc 0 1 :=
  (truthConjunctionHypergeometricInterval n a b).credibility_in_unit

/-! ### Hypergeometric equal-tailed 95% CDF interval -/

/-- Finite clipped count window used by the public hypergeometric CDF surface.

This keeps the CDF-based interval in the same ambient count range as the
support ITV while still allowing the PMF to contribute zero mass on impossible
counts inside the window. -/
def hypergeometricClippedCountWindow (n a b : ℕ) : Finset ℕ :=
  Finset.Icc (hypergeometricSupportLowerCount n a b) (hypergeometricSupportUpperCount n a b)

/-- Total mass of the hypergeometric PMF over the clipped public count window. -/
noncomputable def hypergeometricClippedCountMass (n a b : ℕ) : ℝ≥0∞ :=
  (hypergeometricClippedCountWindow n a b).sum (fun k => Mettapedia.Logic.PLNConjunction.hypergeometricPMF n a b k)

/-- Cumulative mass of the hypergeometric PMF on the clipped count window,
truncated at count `k`. -/
noncomputable def hypergeometricClippedCountCDFMass (n a b k : ℕ) : ℝ≥0∞ :=
  ((hypergeometricClippedCountWindow n a b).filter (fun i => i ≤ k)).sum
    (fun i => Mettapedia.Logic.PLNConjunction.hypergeometricPMF n a b i)

/-- Normalized hypergeometric CDF on the clipped public count window. -/
noncomputable def hypergeometricClippedCountCDF (n a b k : ℕ) : ℝ≥0∞ :=
  let mass := hypergeometricClippedCountMass n a b
  if _ : mass = 0 then 0 else hypergeometricClippedCountCDFMass n a b k / mass

/-- Lower equal-tail threshold for the public 95% hypergeometric CDF interval. -/
noncomputable def hypergeometricCDF95LowerThreshold : ℝ≥0∞ := (1 : ℝ≥0∞) / 40

/-- Upper equal-tail threshold for the public 95% hypergeometric CDF interval. -/
noncomputable def hypergeometricCDF95UpperThreshold : ℝ≥0∞ := (39 : ℝ≥0∞) / 40

/-- Candidate lower counts for the equal-tailed 95% hypergeometric CDF interval. -/
noncomputable def hypergeometricCDF95LowerCandidates (n a b : ℕ) : Finset ℕ :=
  (hypergeometricClippedCountWindow n a b).filter
    (fun k => hypergeometricCDF95LowerThreshold ≤ hypergeometricClippedCountCDF n a b k)

/-- Candidate upper counts for the equal-tailed 95% hypergeometric CDF interval. -/
noncomputable def hypergeometricCDF95UpperCandidates (n a b : ℕ) : Finset ℕ :=
  (hypergeometricClippedCountWindow n a b).filter
    (fun k => hypergeometricCDF95UpperThreshold ≤ hypergeometricClippedCountCDF n a b k)

/-- Lower count of the equal-tailed 95% hypergeometric CDF interval. -/
noncomputable def hypergeometricCDF95LowerCount (n a b : ℕ) : ℕ :=
  if h : (hypergeometricCDF95LowerCandidates n a b).Nonempty
  then (hypergeometricCDF95LowerCandidates n a b).min' h
  else hypergeometricSupportLowerCount n a b

/-- Upper count of the equal-tailed 95% hypergeometric CDF interval. -/
noncomputable def hypergeometricCDF95UpperCount (n a b : ℕ) : ℕ :=
  if h : (hypergeometricCDF95UpperCandidates n a b).Nonempty
  then (hypergeometricCDF95UpperCandidates n a b).min' h
  else hypergeometricSupportUpperCount n a b

theorem hypergeometricSupportLowerCount_le_upperCount (n a b : ℕ) :
    hypergeometricSupportLowerCount n a b ≤ hypergeometricSupportUpperCount n a b :=
  Nat.min_le_left _ _

theorem hypergeometricPMF_ne_top (n a b k : ℕ) :
    Mettapedia.Logic.PLNConjunction.hypergeometricPMF n a b k ≠ ⊤ := by
  unfold Mettapedia.Logic.PLNConjunction.hypergeometricPMF
  split_ifs with hvalid
  · have hden_ne_zero : ((Nat.choose n b : ℕ) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hvalid.2.2.2).ne'
    have hnum_ne_top :
        (((Nat.choose a k * Nat.choose (n - a) (b - k) : ℕ) : ℝ≥0∞)) ≠ ⊤ := by
      exact ENNReal.natCast_ne_top _
    exact ENNReal.div_ne_top hnum_ne_top hden_ne_zero
  · simp

theorem hypergeometricClippedCountMass_ne_top (n a b : ℕ) :
    hypergeometricClippedCountMass n a b ≠ ⊤ := by
  unfold hypergeometricClippedCountMass
  exact (ENNReal.sum_ne_top).2 (by
    intro k hk
    exact hypergeometricPMF_ne_top n a b k)

theorem hypergeometricClippedCountCDF_at_upper
    (n a b : ℕ) (h0 : hypergeometricClippedCountMass n a b ≠ 0) :
    hypergeometricClippedCountCDF n a b (hypergeometricSupportUpperCount n a b) = 1 := by
  have hfilter :
      (hypergeometricClippedCountWindow n a b).filter
          (fun i => i ≤ hypergeometricSupportUpperCount n a b) =
        hypergeometricClippedCountWindow n a b := by
    apply Finset.filter_true_of_mem
    intro i hi
    simp [hypergeometricClippedCountWindow] at hi
    exact hi.2
  have htop : hypergeometricClippedCountMass n a b ≠ ⊤ :=
    hypergeometricClippedCountMass_ne_top n a b
  unfold hypergeometricClippedCountCDF
  rw [dif_neg h0]
  unfold hypergeometricClippedCountCDFMass
  rw [hfilter]
  simpa [hypergeometricClippedCountMass] using (ENNReal.div_self h0 htop)

theorem hypergeometricCDF95LowerCount_le_supportUpper (n a b : ℕ) :
    hypergeometricCDF95LowerCount n a b ≤ hypergeometricSupportUpperCount n a b := by
  by_cases hS : (hypergeometricCDF95LowerCandidates n a b).Nonempty
  · have hmem : (hypergeometricCDF95LowerCandidates n a b).min' hS ∈
        hypergeometricCDF95LowerCandidates n a b := Finset.min'_mem _ _
    simp [hypergeometricCDF95LowerCandidates, hypergeometricClippedCountWindow] at hmem
    rw [hypergeometricCDF95LowerCount, dif_pos hS]
    exact hmem.1.2
  · simpa [hypergeometricCDF95LowerCount, hS] using
      hypergeometricSupportLowerCount_le_upperCount n a b

theorem hypergeometricSupportLowerCount_le_CDF95UpperCount (n a b : ℕ) :
    hypergeometricSupportLowerCount n a b ≤ hypergeometricCDF95UpperCount n a b := by
  by_cases hS : (hypergeometricCDF95UpperCandidates n a b).Nonempty
  · have hmem_upper :
        (hypergeometricCDF95UpperCandidates n a b).min' hS ∈
          hypergeometricCDF95UpperCandidates n a b := Finset.min'_mem _ _
    have hmem_window :
        hypergeometricSupportLowerCount n a b ≤
          (hypergeometricCDF95UpperCandidates n a b).min' hS ∧
        (hypergeometricCDF95UpperCandidates n a b).min' hS ≤
          hypergeometricSupportUpperCount n a b := by
      simpa [hypergeometricClippedCountWindow, Finset.mem_Icc] using
        ((Finset.mem_filter.mp hmem_upper).1)
    have hlow :
        hypergeometricSupportLowerCount n a b ≤
          (hypergeometricCDF95UpperCandidates n a b).min' hS := hmem_window.1
    simpa [hypergeometricCDF95UpperCount, hS] using hlow
  · simpa [hypergeometricCDF95UpperCount, hS] using
      hypergeometricSupportLowerCount_le_upperCount n a b

theorem hypergeometricCDF95UpperCount_le_supportUpper (n a b : ℕ) :
    hypergeometricCDF95UpperCount n a b ≤ hypergeometricSupportUpperCount n a b := by
  by_cases hS : (hypergeometricCDF95UpperCandidates n a b).Nonempty
  · have hmem_upper :
        (hypergeometricCDF95UpperCandidates n a b).min' hS ∈
          hypergeometricCDF95UpperCandidates n a b := Finset.min'_mem _ _
    have hmem_window :
        hypergeometricSupportLowerCount n a b ≤
          (hypergeometricCDF95UpperCandidates n a b).min' hS ∧
        (hypergeometricCDF95UpperCandidates n a b).min' hS ≤
          hypergeometricSupportUpperCount n a b := by
      simpa [hypergeometricClippedCountWindow, Finset.mem_Icc] using
        ((Finset.mem_filter.mp hmem_upper).1)
    simpa [hypergeometricCDF95UpperCount, hS] using hmem_window.2
  · simp [hypergeometricCDF95UpperCount, hS]

theorem hypergeometricCDF95LowerCount_le_upperCount (n a b : ℕ) :
    hypergeometricCDF95LowerCount n a b ≤ hypergeometricCDF95UpperCount n a b := by
  by_cases hHi : (hypergeometricCDF95UpperCandidates n a b).Nonempty
  · by_cases hLo : (hypergeometricCDF95LowerCandidates n a b).Nonempty
    ·
      have hhi_mem :
          (hypergeometricCDF95UpperCandidates n a b).min' hHi ∈
            hypergeometricCDF95UpperCandidates n a b := Finset.min'_mem _ _
      have hhi_mem_lo :
          (hypergeometricCDF95UpperCandidates n a b).min' hHi ∈
            hypergeometricCDF95LowerCandidates n a b := by
        refine Finset.mem_filter.mpr ?_
        constructor
        · exact (Finset.mem_filter.mp hhi_mem).1
        · have hhi_thresh :
              hypergeometricCDF95UpperThreshold ≤
                hypergeometricClippedCountCDF n a b
                  ((hypergeometricCDF95UpperCandidates n a b).min' hHi) :=
            (Finset.mem_filter.mp hhi_mem).2
          have hthreshold :
              hypergeometricCDF95LowerThreshold ≤ hypergeometricCDF95UpperThreshold := by
            have hone_le : (1 : ℝ≥0∞) ≤ 39 := by norm_num
            simpa [hypergeometricCDF95LowerThreshold, hypergeometricCDF95UpperThreshold] using
              (ENNReal.div_le_div_right hone_le (40 : ℝ≥0∞))
          exact le_trans hthreshold hhi_thresh
      simpa [hypergeometricCDF95LowerCount, hypergeometricCDF95UpperCount, hLo, hHi] using
        (Finset.min'_le _ _ hhi_mem_lo)
    · simpa [hypergeometricCDF95LowerCount, hypergeometricCDF95UpperCount, hLo, hHi] using
        hypergeometricSupportLowerCount_le_CDF95UpperCount n a b
  · calc
      hypergeometricCDF95LowerCount n a b ≤ hypergeometricSupportUpperCount n a b := by
        exact hypergeometricCDF95LowerCount_le_supportUpper n a b
      _ = hypergeometricCDF95UpperCount n a b := by
        simp [hypergeometricCDF95UpperCount, hHi]

/-- Equal-tailed 95% CDF interval view for finite-population conjunction.

Unlike `truthConjunctionHypergeometricInterval`, which returns the exact support
interval, this surface selects its lower and upper endpoints from the
normalized finite-support CDF on the clipped count window. The credibility
coordinate records the nominal 95% level used to choose the equal tails. -/
noncomputable def truthConjunctionHypergeometricCDFInterval95 (n a b : ℕ) : ITV :=
  let lowerCount := hypergeometricCDF95LowerCount n a b
  let upperCount := hypergeometricCDF95UpperCount n a b
  Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility
    (if h : n = 0 then 0 else (lowerCount : ℝ) / n)
    (if h : n = 0 then 0 else (upperCount : ℝ) / n)
    (19 / 20 : ℝ)
    (by
      by_cases hn : n = 0
      · simp [hn]
      · have hcounts : lowerCount ≤ upperCount := hypergeometricCDF95LowerCount_le_upperCount n a b
        have hcountsR : (lowerCount : ℝ) ≤ (upperCount : ℝ) := by
          exact_mod_cast hcounts
        have hnR : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
        simpa [hn] using div_le_div_of_nonneg_right hcountsR hnR)
    (by
      by_cases hn : n = 0
      · simp [hn]
      · simp [hn]
        exact div_nonneg (by positivity) (by exact_mod_cast Nat.zero_le n))
    (by
      by_cases hn : n = 0
      · simp [hn]
      · have hup : upperCount ≤ n := by
          calc
            upperCount ≤ hypergeometricSupportUpperCount n a b := by
              exact hypergeometricCDF95UpperCount_le_supportUpper n a b
            _ ≤ n := Nat.min_le_left _ _
        have hupR : (upperCount : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast hup
        have hnR : 0 ≤ (n : ℝ) := by positivity
        simp [hn]
        have hdiv : (upperCount : ℝ) / n ≤ (n : ℝ) / n := by
          exact div_le_div_of_nonneg_right hupR hnR
        have hnR_ne : (n : ℝ) ≠ 0 := by
          exact_mod_cast Nat.ne_of_gt (Nat.pos_of_ne_zero hn)
        simpa [hnR_ne] using hdiv)
    (by
      norm_num)

theorem truthConjunctionHypergeometricCDFInterval95_width_nonneg (n a b : ℕ) :
    0 ≤ (truthConjunctionHypergeometricCDFInterval95 n a b).width :=
  (truthConjunctionHypergeometricCDFInterval95 n a b).width_nonneg

theorem truthConjunctionHypergeometricCDFInterval95_credibility_eq (n a b : ℕ) :
    (truthConjunctionHypergeometricCDFInterval95 n a b).credibility = 19 / 20 := by
  simp [truthConjunctionHypergeometricCDFInterval95,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

end Mettapedia.Logic.WMPLNDistributionalTruthFunctions
