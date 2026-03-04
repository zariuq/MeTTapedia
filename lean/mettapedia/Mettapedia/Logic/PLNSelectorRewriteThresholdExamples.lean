import Mettapedia.Logic.PLNCanonicalAPI
import Mettapedia.Logic.PLNInferenceControlExamples
import Mettapedia.Logic.PLNXiDerivedBNRules

/-!
# Selector→Rewrite→Threshold Worked Examples

Concrete worked fixtures for the composed selector/rewrite/threshold API path.
-/

namespace Mettapedia.Logic.PLNSelectorRewriteThresholdExamples

open Mettapedia.Logic
open Mettapedia.Logic.PLNCanonical
open Mettapedia.Logic.PLNInferenceControlExamples

noncomputable section

/-- Concrete selector fixture (`Bool`, `topK = 1`) composed with the generic
rewrite→OSLF→threshold endpoint in one theorem.

The selector side is fully concrete (Chapter-13 worked fixture); the rewrite/OSLF
side remains generic so this theorem can be instantiated in any WM/OSLF setting. -/
theorem bool_selector_rewrite_threshold_end_to_end_fixture
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : CtxOfInterval i)
    {r : WMRewriteRuleSigma State Srt Query} {W₁ W₂ : State}
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau :
      tau ≤ coord ((semanticsOfInterval i).eval ctx (r.derive W₁)))
    (hEq : WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query)
      r.conclusion (queryOfAtom₁ a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p')
    (selectorWitness : Finset Bool → Finset (Unit × Unit)) :
    let G := PLNInferenceControlAlgorithms.greedySelect
      ch13_dependencyBool ch13_checklistBool.topK
    (ch13_checklistBool.topK ≤ Fintype.card Bool
      ∧ (∀ g' f',
          0 ≤ (Mettapedia.Logic.PremiseSelection.selectorDefaults_halfGate Bool Bool).gate g' f'
            ∧ (Mettapedia.Logic.PremiseSelection.selectorDefaults_halfGate Bool Bool).gate g' f' ≤ 1)
      ∧ Mettapedia.Logic.PremiseSelectionOptimality.BayesOptimalRanking ch13_etaBool
          (Mettapedia.Logic.PremiseSelectionOptimality.perturbedScore
            (ch13ScorePooled ch13_globalPriorBool ch13_localPriorBool ch13_likelihoodBool true)
            ch13_deltaZero)
      ∧ (1 - Real.exp (-1)) * (Nat.min ch13_checklistBool.topK ch13_dependencyBool.card : ℝ) ≤
          Mettapedia.Logic.PremiseSelection.dependencyCoverage ch13_dependencyBool G)
      ∧ ch8ThresholdAccepted
          (State := State) (Srt := Srt) (Query := Query)
          (i := i) (R := R) (m := m) (ctx := ctx)
          W₂ queryOfAtom₂ a0 p coord tau := by
  simpa [ch13_deltaZero] using
    (ch9_selector_rewrite_threshold_end_to_end_of_interval
      (A := ch13_checklistBool)
      (η := ch13_etaBool)
      (globalPrior := ch13_globalPriorBool)
      (localPrior := ch13_localPriorBool)
      (likelihood := ch13_likelihoodBool)
      (g := true)
      ch13_localExchangeabilityBool
      (δ := ch13_deltaZero) (ε := 0)
      ch13_twoStageRankingBool
      (hbound := by intro x; simp [ch13_deltaZero])
      (hmargin := ch13_marginBool)
      (htie := by intro x y hxy; simp [ch13_deltaZero])
      (D := ch13_dependencyBool)
      (i := i) (R := R) (m := m) (ctx := ctx)
      (r := r) (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (p := p) (coord := coord) (tau := tau)
      hSide hW hTau hEq hVal selectorWitness)

/-- Concrete Chapter-8 acceptance fixture:
instantiate the selector-witness channel with a fixed finite witness and project
the threshold-acceptance component from the composed selector/rewrite theorem. -/
theorem ch8_thresholdAccepted_bool_selector_fixture
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : CtxOfInterval i)
    {r : WMRewriteRuleSigma State Srt Query} {W₁ W₂ : State}
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau :
      tau ≤ coord ((semanticsOfInterval i).eval ctx (r.derive W₁)))
    (hEq : WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query)
      r.conclusion (queryOfAtom₁ a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p') :
    ch8ThresholdAccepted
      (State := State) (Srt := Srt) (Query := Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      W₂ queryOfAtom₂ a0 p coord tau := by
  exact
    (bool_selector_rewrite_threshold_end_to_end_fixture
      (State := State) (Srt := Srt) (Query := Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      (r := r) (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (p := p) (coord := coord) (tau := tau)
      hSide hW hTau hEq hVal
      (selectorWitness := fun _ => ({((), ())} : Finset (Unit × Unit)))).2

end

end Mettapedia.Logic.PLNSelectorRewriteThresholdExamples
