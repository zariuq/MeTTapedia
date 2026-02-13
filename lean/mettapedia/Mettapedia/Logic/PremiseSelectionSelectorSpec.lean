import Mettapedia.Logic.PremiseSelectionPriorNB
import Mettapedia.Logic.PremiseSelectionFusion
import Mettapedia.Logic.EvidenceQuantale

/-!
# Selector-Spec Theorems for Normalization and Gating Defaults

This module ties practical selector defaults to the explicit proof-side checklist:
- normalization totals for prior/likelihood
- gating range constraints
- top-k finite-pool budget constraints

It is intentionally lightweight and theorem-facing, so implementation code can
reference a precise, stable contract.
-/

namespace Mettapedia.Logic.PremiseSelection

open scoped ENNReal
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PremiseSelectionOptimality

/-- Proof-facing default parameter bundle for a premise selector. -/
structure SelectorDefaults (Goal Fact : Type*) where
  tPrior : ℝ≥0∞
  tLik : ℝ≥0∞
  gate : Goal → Fact → ℝ
  tPrior_ne_zero : tPrior ≠ 0
  tLik_ne_zero : tLik ≠ 0
  tPrior_ne_top : tPrior ≠ ⊤
  tLik_ne_top : tLik ≠ ⊤
  gate_lower : ∀ g f, 0 ≤ gate g f
  gate_upper : ∀ g f, gate g f ≤ 1

/-- Canonical defaults used in the proof-driven selector spec:
`1`/`1` normalization totals and a neutral `1/2` gate. -/
noncomputable def selectorDefaults_halfGate (Goal Fact : Type*) : SelectorDefaults Goal Fact :=
  { tPrior := 1
    tLik := 1
    gate := fun _ _ => (1 / 2 : ℝ)
    tPrior_ne_zero := by simp
    tLik_ne_zero := by simp
    tPrior_ne_top := by simp
    tLik_ne_top := by simp
    gate_lower := by intro _ _; norm_num
    gate_upper := by intro _ _; norm_num }

/-- Checklist linkage: default selector settings satisfy the finite budget and gate-range
requirements under the explicit Prior-NB checklist assumptions. -/
theorem selectorSpec_defaults_match_checklist
    {Goal Fact Bin : Type*} [Fintype Fact]
    (A : PriorNBAssumptionChecklist Goal Fact Bin) :
    A.topK ≤ Fintype.card Fact
    ∧ (∀ g f,
        0 ≤ (selectorDefaults_halfGate Goal Fact).gate g f
        ∧ (selectorDefaults_halfGate Goal Fact).gate g f ≤ 1) := by
  refine ⟨A.topK_le_pool, ?_⟩
  intro g f
  exact ⟨(selectorDefaults_halfGate Goal Fact).gate_lower g f,
    (selectorDefaults_halfGate Goal Fact).gate_upper g f⟩

/-- Equal normalization defaults induce equal mixing weights in the normalized
fusion formula (real-valued form). -/
theorem selectorSpec_default_equalMix_toReal
    {Goal Fact : Type*} (s₁ s₂ : Scorer Goal Fact) (g : Goal) (f : Fact) :
    (Evidence.toStrength
        ((fuse (normalizeScorer (selectorDefaults_halfGate Goal Fact).tPrior s₁)
               (normalizeScorer (selectorDefaults_halfGate Goal Fact).tLik s₂)).score g f)).toReal
      =
      ((1:ℝ≥0∞) / (1 + 1)).toReal
          * (Evidence.toStrength
              ((normalizeScorer (selectorDefaults_halfGate Goal Fact).tPrior s₁).score g f)).toReal
      + ((1:ℝ≥0∞) / (1 + 1)).toReal
          * (Evidence.toStrength
              ((normalizeScorer (selectorDefaults_halfGate Goal Fact).tLik s₂).score g f)).toReal := by
  simpa [selectorDefaults_halfGate] using
    (fuse_toStrength_normalized_const_toReal_one (s₁ := s₁) (s₂ := s₂) (g := g) (f := f))

/-- Selector-spec theorem: checklist assumptions + default normalization/gating imply
Prior-NB ranking transfer is available at the default normalization point. -/
theorem selectorSpec_default_priorNB_ranking_transfer
    {Goal Fact Bin : Type*} [Fintype Fact]
    (A : PriorNBAssumptionChecklist Goal Fact Bin)
    (η : Fact -> ℝ)
    (globalPrior localPrior likelihood : Scorer Goal Fact)
    (g : Goal)
    (hLocal : A.localExchangeabilityInBin) :
    A.topK ≤ Fintype.card Fact
    ∧ (∀ g' f',
        0 ≤ (selectorDefaults_halfGate Goal Fact).gate g' f'
        ∧ (selectorDefaults_halfGate Goal Fact).gate g' f' ≤ 1)
    ∧
    (BayesOptimalRanking η
      (fun x =>
        (Evidence.toStrength
          ((normalizeScorer (selectorDefaults_halfGate Goal Fact).tPrior
            (priorNBPosterior globalPrior localPrior likelihood)).score g x)).toReal)
      ↔
    BayesOptimalRanking η
      (fun x =>
        (Evidence.toStrength
          ((normalizeScorer (selectorDefaults_halfGate Goal Fact).tPrior
            (priorNBPosteriorTwoStage globalPrior localPrior likelihood)).score g x)).toReal)) := by
  have hdefaults := selectorSpec_defaults_match_checklist (A := A)
  have hrank :=
    priorNB_assumptionChecklist_ranking_transfer
      (A := A) (η := η)
      (globalPrior := globalPrior) (localPrior := localPrior) (likelihood := likelihood)
      (g := g) (t := (selectorDefaults_halfGate Goal Fact).tPrior) hLocal
  exact ⟨hdefaults.1, hdefaults.2, by simpa [selectorDefaults_halfGate] using hrank⟩

/-- Selector-spec fallback theorem: if local gate mass is zero, the gated role-correct
posterior collapses to the global-prior update path. -/
theorem selectorSpec_zeroLocalGate_fallback
    {Goal Fact : Type*}
    {TS : OperatorRoleTheoryScaled Goal Fact}
    (cfg : RoleDisciplinedSelector TS.toOperatorRoleTheory) :
    gatedPosterior cfg 0 = update cfg.globalPrior cfg.likelihood := by
  simpa using gatedPosterior_zero_local (cfg := cfg)

end Mettapedia.Logic.PremiseSelection
