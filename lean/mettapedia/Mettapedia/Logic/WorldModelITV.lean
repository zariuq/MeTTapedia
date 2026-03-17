import Mettapedia.Logic.PLNWorldModel
import Mettapedia.Logic.PLNWorldModelCalculus
-- PLNWorldModelCalculusTyped merged into PLNWorldModelCalculus
import Mettapedia.Logic.PLNIndefiniteTruth

/-!
# PLN World-Model ITV Semantics

This module adds an explicit semantics layer for ITV-valued query views:

- **Bayesian credible-interval semantics** (Beta normal approximation or exact invCDF)
- **Walley IDM predictive-interval semantics**

The WM state remains evidence-valued; ITV is a derived query view chosen by an
explicit semantics object.
-/

namespace Mettapedia.Logic.PLNWorldModel

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNIndefiniteTruth

/-- Context-indexed ITV semantics: how to map extracted evidence to an ITV. -/
structure ITVSemantics (Ctx : Type*) where
  eval : Ctx → BinaryEvidence → PLNIndefiniteTruth.ITV

/-- Context for Walley IDM predictive intervals (`s > 0` is IDM prior strength). -/
structure IDMPredictiveContext where
  s : ℝ
  s_pos : 0 < s

namespace IDMPredictiveContext

/-- Common default in IDM examples (`s = 2`). -/
def default : IDMPredictiveContext := ⟨2, by norm_num⟩

end IDMPredictiveContext

namespace ITVSemantics

/-- Bayesian ITV semantics using Beta credible intervals via normal approximation. -/
noncomputable def bayesCredibleNormalApprox (level : ℝ) (hlevel : 0 < level ∧ level < 1) :
    ITVSemantics BinaryContext where
  eval := fun ctx e => PLNIndefiniteTruth.ITV.fromBayesCredibleNormalApprox e ctx level hlevel

/-- Bayesian ITV semantics using Beta credible intervals via exact-invCDF backend. -/
noncomputable def bayesCredibleExactInvCDF (level : ℝ) (hlevel : 0 < level ∧ level < 1) :
    ITVSemantics BinaryContext where
  eval := fun ctx e => PLNIndefiniteTruth.ITV.fromBayesCredibleExactInvCDF e ctx level hlevel

/-- Bayesian ITV semantics at 95% credible level. -/
noncomputable def bayesCredible95 : ITVSemantics BinaryContext :=
  bayesCredibleNormalApprox 0.95 ⟨by norm_num, by norm_num⟩

/-- Bayesian ITV semantics at 90% credible level. -/
noncomputable def bayesCredible90 : ITVSemantics BinaryContext :=
  bayesCredibleNormalApprox 0.90 ⟨by norm_num, by norm_num⟩

/-- Bayesian ITV semantics at 95% credible level using exact-invCDF backend. -/
noncomputable def bayesCredibleExact95 : ITVSemantics BinaryContext :=
  bayesCredibleExactInvCDF 0.95 ⟨by norm_num, by norm_num⟩

/-- Bayesian ITV semantics at 90% credible level using exact-invCDF backend. -/
noncomputable def bayesCredibleExact90 : ITVSemantics BinaryContext :=
  bayesCredibleExactInvCDF 0.90 ⟨by norm_num, by norm_num⟩

/-- Walley IDM predictive-interval semantics. -/
noncomputable def walleyIDMPredictive : ITVSemantics IDMPredictiveContext where
  eval := fun ctx e => PLNIndefiniteTruth.ITV.fromWalleyIDMPredictive e ctx.s ctx.s_pos

end ITVSemantics

namespace BinaryWorldModel

variable {State Query Ctx : Type*} [EvidenceType State] [BinaryWorldModel State Query]

/-- ITV query view from an explicit semantics choice. -/
noncomputable def queryITV (sem : ITVSemantics Ctx) (ctx : Ctx) (W : State) (q : Query) :
    PLNIndefiniteTruth.ITV :=
  sem.eval ctx (BinaryWorldModel.evidence (State := State) (Query := Query) W q)

/-- Lower bound from `queryITV`. -/
noncomputable def queryITVLower (sem : ITVSemantics Ctx) (ctx : Ctx) (W : State) (q : Query) :
    ℝ :=
  (queryITV (State := State) (Query := Query) sem ctx W q).lower

/-- Upper bound from `queryITV`. -/
noncomputable def queryITVUpper (sem : ITVSemantics Ctx) (ctx : Ctx) (W : State) (q : Query) :
    ℝ :=
  (queryITV (State := State) (Query := Query) sem ctx W q).upper

/-- Credibility component from `queryITV`. -/
noncomputable def queryITVCredibility
    (sem : ITVSemantics Ctx) (ctx : Ctx) (W : State) (q : Query) : ℝ :=
  (queryITV (State := State) (Query := Query) sem ctx W q).credibility

/-- Midpoint strength view from `queryITV`. -/
noncomputable def queryITVStrength
    (sem : ITVSemantics Ctx) (ctx : Ctx) (W : State) (q : Query) : ℝ :=
  (queryITV (State := State) (Query := Query) sem ctx W q).strength

/-- Width view from `queryITV`. -/
noncomputable def queryITVWidth (sem : ITVSemantics Ctx) (ctx : Ctx) (W : State) (q : Query) :
    ℝ :=
  (queryITV (State := State) (Query := Query) sem ctx W q).width

/-- Under Walley IDM predictive semantics, query width and credibility sum to 1. -/
theorem queryITVWidth_add_queryITVCredibility_walley
    (ctx : IDMPredictiveContext) (W : State) (q : Query) :
    queryITVWidth (State := State) (Query := Query)
      ITVSemantics.walleyIDMPredictive ctx W q +
      queryITVCredibility (State := State) (Query := Query)
        ITVSemantics.walleyIDMPredictive ctx W q = 1 := by
  unfold queryITVWidth queryITVCredibility queryITV
  simpa using
    (PLNIndefiniteTruth.ITV.fromWalleyIDMPredictive_width_add_credibility
      (e := BinaryWorldModel.evidence (State := State) (Query := Query) W q)
      (s := ctx.s) (hs := ctx.s_pos))

/-- Equivalent Walley IDM identity written as `width = 1 - credibility`. -/
theorem queryITVWidth_eq_one_sub_queryITVCredibility_walley
    (ctx : IDMPredictiveContext) (W : State) (q : Query) :
    queryITVWidth (State := State) (Query := Query)
      ITVSemantics.walleyIDMPredictive ctx W q =
      1 - queryITVCredibility (State := State) (Query := Query)
        ITVSemantics.walleyIDMPredictive ctx W q := by
  unfold queryITVWidth queryITVCredibility queryITV
  simpa using
    (PLNIndefiniteTruth.ITV.fromWalleyIDMPredictive_width_eq_one_sub_credibility
      (e := BinaryWorldModel.evidence (State := State) (Query := Query) W q)
      (s := ctx.s) (hs := ctx.s_pos))

/-! ## ITV judgments -/

/-- ITV judgment from a derivable WM state. -/
def WMITVJudgment
    (sem : ITVSemantics Ctx) (ctx : Ctx)
    (W : State) (q : Query) (itv : PLNIndefiniteTruth.ITV) : Prop :=
  WMJudgment W ∧ itv = queryITV (State := State) (Query := Query) sem ctx W q

/-- ITV judgment under a context-indexed WM derivation. -/
def WMITVJudgmentCtx
    (sem : ITVSemantics Ctx) (ctx : Ctx)
    (Γ : Set State) (W : State) (q : Query) (itv : PLNIndefiniteTruth.ITV) : Prop :=
  WMJudgmentCtx Γ W ∧ itv = queryITV (State := State) (Query := Query) sem ctx W q

/-- BinaryEvidence-level rewrite soundness lifted to ITV semantics. -/
theorem WMRewriteRule.itv_eval_eq_queryITV
    (sem : ITVSemantics Ctx) (ctx : Ctx)
    {r : WMRewriteRule State Query} (hSide : r.side) (W : State) :
    sem.eval ctx (r.derive W) =
      queryITV (State := State) (Query := Query) sem ctx W r.conclusion := by
  simp [queryITV, r.sound hSide W]

/-- Apply an evidence-level rewrite rule to produce an ITV judgment. -/
theorem WMRewriteRule.applyITV
    (sem : ITVSemantics Ctx) (ctx : Ctx)
    {r : WMRewriteRule State Query} {W : State}
    (hSide : r.side) (hW : WMJudgment W) :
    WMITVJudgment (State := State) (Query := Query) sem ctx
      W r.conclusion (sem.eval ctx (r.derive W)) := by
  exact ⟨hW, WMRewriteRule.itv_eval_eq_queryITV (State := State) (Query := Query) sem ctx hSide W⟩

/-- Context-indexed ITV judgment from an evidence-level rewrite rule. -/
theorem WMRewriteRule.applyITVCtx
    (sem : ITVSemantics Ctx) (ctx : Ctx)
    {r : WMRewriteRule State Query} {Γ : Set State} {W : State}
    (hSide : r.side) (hW : WMJudgmentCtx Γ W) :
    WMITVJudgmentCtx (State := State) (Query := Query) sem ctx
      Γ W r.conclusion (sem.eval ctx (r.derive W)) := by
  exact ⟨hW, WMRewriteRule.itv_eval_eq_queryITV (State := State) (Query := Query) sem ctx hSide W⟩

end BinaryWorldModel

namespace WorldModelSigma

variable {State Srt Ctx : Type*} {Query : Srt → Type*}
variable [EvidenceType State] [WorldModelSigma State Srt Query]

/-- ITV query view from an explicit semantics choice over typed (sort-indexed) queries. -/
noncomputable def queryITV (sem : ITVSemantics Ctx) (ctx : Ctx) (W : State)
    (q : Sigma Query) : PLNIndefiniteTruth.ITV :=
  sem.eval ctx (WorldModelSigma.evidence (State := State) (Srt := Srt) (Query := Query) W q)

/-- ITV query view for an explicitly sorted query. -/
noncomputable def queryITVAt (sem : ITVSemantics Ctx) (ctx : Ctx) (W : State)
    {s : Srt} (q : Query s) : PLNIndefiniteTruth.ITV :=
  queryITV (State := State) (Srt := Srt) (Query := Query) sem ctx W ⟨s, q⟩

/-- Lower bound from typed `queryITV`. -/
noncomputable def queryITVLower (sem : ITVSemantics Ctx) (ctx : Ctx) (W : State)
    (q : Sigma Query) : ℝ :=
  (queryITV (State := State) (Srt := Srt) (Query := Query) sem ctx W q).lower

/-- Upper bound from typed `queryITV`. -/
noncomputable def queryITVUpper (sem : ITVSemantics Ctx) (ctx : Ctx) (W : State)
    (q : Sigma Query) : ℝ :=
  (queryITV (State := State) (Srt := Srt) (Query := Query) sem ctx W q).upper

/-- Credibility component from typed `queryITV`. -/
noncomputable def queryITVCredibility (sem : ITVSemantics Ctx) (ctx : Ctx) (W : State)
    (q : Sigma Query) : ℝ :=
  (queryITV (State := State) (Srt := Srt) (Query := Query) sem ctx W q).credibility

/-- Midpoint strength view from typed `queryITV`. -/
noncomputable def queryITVStrength (sem : ITVSemantics Ctx) (ctx : Ctx) (W : State)
    (q : Sigma Query) : ℝ :=
  (queryITV (State := State) (Srt := Srt) (Query := Query) sem ctx W q).strength

/-- Width view from typed `queryITV`. -/
noncomputable def queryITVWidth (sem : ITVSemantics Ctx) (ctx : Ctx) (W : State)
    (q : Sigma Query) : ℝ :=
  (queryITV (State := State) (Srt := Srt) (Query := Query) sem ctx W q).width

/-- Typed Walley IDM identity: `width + credibility = 1`. -/
theorem queryITVWidth_add_queryITVCredibility_walley
    (ctx : IDMPredictiveContext) (W : State) (q : Sigma Query) :
    queryITVWidth (State := State) (Srt := Srt) (Query := Query)
      ITVSemantics.walleyIDMPredictive ctx W q +
      queryITVCredibility (State := State) (Srt := Srt) (Query := Query)
        ITVSemantics.walleyIDMPredictive ctx W q = 1 := by
  unfold queryITVWidth queryITVCredibility queryITV
  simpa using
    (PLNIndefiniteTruth.ITV.fromWalleyIDMPredictive_width_add_credibility
      (e := WorldModelSigma.evidence (State := State) (Srt := Srt) (Query := Query) W q)
      (s := ctx.s) (hs := ctx.s_pos))

/-- Typed Walley IDM identity: `width = 1 - credibility`. -/
theorem queryITVWidth_eq_one_sub_queryITVCredibility_walley
    (ctx : IDMPredictiveContext) (W : State) (q : Sigma Query) :
    queryITVWidth (State := State) (Srt := Srt) (Query := Query)
      ITVSemantics.walleyIDMPredictive ctx W q =
      1 - queryITVCredibility (State := State) (Srt := Srt) (Query := Query)
        ITVSemantics.walleyIDMPredictive ctx W q := by
  unfold queryITVWidth queryITVCredibility queryITV
  simpa using
    (PLNIndefiniteTruth.ITV.fromWalleyIDMPredictive_width_eq_one_sub_credibility
      (e := WorldModelSigma.evidence (State := State) (Srt := Srt) (Query := Query) W q)
      (s := ctx.s) (hs := ctx.s_pos))

/-! ## Typed ITV judgments -/

/-- Typed ITV judgment from a derivable WM state. -/
def WMITVJudgmentSigma
    (sem : ITVSemantics Ctx) (ctx : Ctx)
    (W : State) (q : Sigma Query) (itv : PLNIndefiniteTruth.ITV) : Prop :=
  WMJudgment W ∧ itv = queryITV (State := State) (Srt := Srt) (Query := Query) sem ctx W q

/-- Typed ITV judgment under a context-indexed WM derivation. -/
def WMITVJudgmentCtxSigma
    (sem : ITVSemantics Ctx) (ctx : Ctx)
    (Γ : Set State) (W : State) (q : Sigma Query) (itv : PLNIndefiniteTruth.ITV) : Prop :=
  WMJudgmentCtx Γ W ∧ itv = queryITV (State := State) (Srt := Srt) (Query := Query) sem ctx W q

/-- Typed ITV threshold judgment for an ITV coordinate. -/
def WMITVThresholdJudgmentSigma
    (sem : ITVSemantics Ctx) (ctx : Ctx)
    (W : State) (q : Sigma Query)
    (coord : PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ) : Prop :=
  WMJudgment W ∧ tau ≤ coord (queryITV (State := State) (Srt := Srt) (Query := Query) sem ctx W q)

/-- Context-indexed typed ITV threshold judgment for an ITV coordinate. -/
def WMITVThresholdJudgmentCtxSigma
    (sem : ITVSemantics Ctx) (ctx : Ctx)
    (Γ : Set State) (W : State) (q : Sigma Query)
    (coord : PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ) : Prop :=
  WMJudgmentCtx Γ W ∧
    tau ≤ coord (queryITV (State := State) (Srt := Srt) (Query := Query) sem ctx W q)

/-- Typed query equivalence preserves ITV views under any semantics. -/
theorem WMQueryEqSigma.to_queryITV
    {q₁ q₂ : Sigma Query}
    (hEq : WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q₁ q₂)
    (sem : ITVSemantics Ctx) (ctx : Ctx) (W : State) :
    queryITV (State := State) (Srt := Srt) (Query := Query) sem ctx W q₁ =
      queryITV (State := State) (Srt := Srt) (Query := Query) sem ctx W q₂ := by
  simp [queryITV, hEq W]

/-- Typed query equivalence preserves every ITV coordinate view. -/
theorem WMQueryEqSigma.to_queryITV_coord
    {q₁ q₂ : Sigma Query}
    (hEq : WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q₁ q₂)
    (sem : ITVSemantics Ctx) (ctx : Ctx) (W : State)
    (coord : PLNIndefiniteTruth.ITV → ℝ) :
    coord (queryITV (State := State) (Srt := Srt) (Query := Query) sem ctx W q₁) =
      coord (queryITV (State := State) (Srt := Srt) (Query := Query) sem ctx W q₂) := by
  simpa using congrArg coord
    (WMQueryEqSigma.to_queryITV
      (State := State) (Srt := Srt) (Query := Query) hEq sem ctx W)

/-- Typed query equivalence transports ITV threshold judgments. -/
theorem WMQueryEqSigma.to_queryITV_threshold
    {q₁ q₂ : Sigma Query}
    (hEq : WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q₁ q₂)
    (sem : ITVSemantics Ctx) (ctx : Ctx) (W : State)
    (coord : PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hTau : tau ≤ coord (queryITV (State := State) (Srt := Srt) (Query := Query) sem ctx W q₁)) :
    tau ≤ coord (queryITV (State := State) (Srt := Srt) (Query := Query) sem ctx W q₂) := by
  have hcoord := WMQueryEqSigma.to_queryITV_coord
    (State := State) (Srt := Srt) (Query := Query) hEq sem ctx W coord
  simpa [hcoord] using hTau

/-- Typed evidence-level rewrite soundness lifted to ITV semantics. -/
theorem WMRewriteRuleSigma.itv_eval_eq_queryITV
    (sem : ITVSemantics Ctx) (ctx : Ctx)
    {r : WMRewriteRuleSigma State Srt Query} (hSide : r.side) (W : State) :
    sem.eval ctx (r.derive W) =
      queryITV (State := State) (Srt := Srt) (Query := Query) sem ctx W r.conclusion := by
  simp [queryITV, r.sound hSide W]

/-- Apply a typed evidence-level rewrite rule to produce an ITV judgment. -/
theorem WMRewriteRuleSigma.applyITV
    (sem : ITVSemantics Ctx) (ctx : Ctx)
    {r : WMRewriteRuleSigma State Srt Query} {W : State}
    (hSide : r.side) (hW : WMJudgment W) :
    WMITVJudgmentSigma (State := State) (Srt := Srt) (Query := Query) sem ctx
      W r.conclusion (sem.eval ctx (r.derive W)) := by
  exact ⟨hW, WMRewriteRuleSigma.itv_eval_eq_queryITV
    (State := State) (Srt := Srt) (Query := Query) sem ctx hSide W⟩

/-- Context-indexed typed ITV judgment from an evidence-level rewrite rule. -/
theorem WMRewriteRuleSigma.applyITVCtx
    (sem : ITVSemantics Ctx) (ctx : Ctx)
    {r : WMRewriteRuleSigma State Srt Query} {Γ : Set State} {W : State}
    (hSide : r.side) (hW : WMJudgmentCtx Γ W) :
    WMITVJudgmentCtxSigma (State := State) (Srt := Srt) (Query := Query) sem ctx
      Γ W r.conclusion (sem.eval ctx (r.derive W)) := by
  exact ⟨hW, WMRewriteRuleSigma.itv_eval_eq_queryITV
    (State := State) (Srt := Srt) (Query := Query) sem ctx hSide W⟩

/-- Typed ITV threshold judgment preserved by a rewrite rule. -/
theorem WMRewriteRuleSigma.applyITVThreshold
    (sem : ITVSemantics Ctx) (ctx : Ctx)
    {r : WMRewriteRuleSigma State Srt Query} {W : State}
    (coord : PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : WMJudgment W)
    (hTau : tau ≤ coord (sem.eval ctx (r.derive W))) :
    WMITVThresholdJudgmentSigma (State := State) (Srt := Srt) (Query := Query) sem ctx
      W r.conclusion coord tau := by
  refine ⟨hW, ?_⟩
  have hEq := WMRewriteRuleSigma.itv_eval_eq_queryITV
    (State := State) (Srt := Srt) (Query := Query) sem ctx hSide W
  simpa [hEq] using hTau

/-- Context-indexed typed ITV threshold judgment preserved by a rewrite rule. -/
theorem WMRewriteRuleSigma.applyITVThresholdCtx
    (sem : ITVSemantics Ctx) (ctx : Ctx)
    {r : WMRewriteRuleSigma State Srt Query} {Γ : Set State} {W : State}
    (coord : PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : WMJudgmentCtx Γ W)
    (hTau : tau ≤ coord (sem.eval ctx (r.derive W))) :
    WMITVThresholdJudgmentCtxSigma (State := State) (Srt := Srt) (Query := Query) sem ctx
      Γ W r.conclusion coord tau := by
  refine ⟨hW, ?_⟩
  have hEq := WMRewriteRuleSigma.itv_eval_eq_queryITV
    (State := State) (Srt := Srt) (Query := Query) sem ctx hSide W
  simpa [hEq] using hTau

/-- Typed ITV rewrite-preservation under Bayes 95% normal-approx semantics. -/
theorem WMRewriteRuleSigma.applyITV_bayes95
    {r : WMRewriteRuleSigma State Srt Query} {W : State}
    (ctx : BinaryContext) (hSide : r.side) (hW : WMJudgment W) :
    WMITVJudgmentSigma (State := State) (Srt := Srt) (Query := Query)
      ITVSemantics.bayesCredible95 ctx
      W r.conclusion
      (ITVSemantics.bayesCredible95.eval ctx (r.derive W)) :=
  WMRewriteRuleSigma.applyITV
    (State := State) (Srt := Srt) (Query := Query)
    ITVSemantics.bayesCredible95 ctx hSide hW

/-- Typed ITV rewrite-preservation under Bayes 95% exact-invCDF semantics. -/
theorem WMRewriteRuleSigma.applyITV_bayesExact95
    {r : WMRewriteRuleSigma State Srt Query} {W : State}
    (ctx : BinaryContext) (hSide : r.side) (hW : WMJudgment W) :
    WMITVJudgmentSigma (State := State) (Srt := Srt) (Query := Query)
      ITVSemantics.bayesCredibleExact95 ctx
      W r.conclusion
      (ITVSemantics.bayesCredibleExact95.eval ctx (r.derive W)) :=
  WMRewriteRuleSigma.applyITV
    (State := State) (Srt := Srt) (Query := Query)
    ITVSemantics.bayesCredibleExact95 ctx hSide hW

/-- Typed ITV rewrite-preservation under Walley IDM predictive semantics. -/
theorem WMRewriteRuleSigma.applyITV_walleyIDM
    {r : WMRewriteRuleSigma State Srt Query} {W : State}
    (ctx : IDMPredictiveContext) (hSide : r.side) (hW : WMJudgment W) :
    WMITVJudgmentSigma (State := State) (Srt := Srt) (Query := Query)
      ITVSemantics.walleyIDMPredictive ctx
      W r.conclusion
      (ITVSemantics.walleyIDMPredictive.eval ctx (r.derive W)) :=
  WMRewriteRuleSigma.applyITV
    (State := State) (Srt := Srt) (Query := Query)
    ITVSemantics.walleyIDMPredictive ctx hSide hW

/-- Typed ITV threshold preservation under Bayes 95% normal-approx semantics. -/
theorem WMRewriteRuleSigma.applyITVThreshold_bayes95
    {r : WMRewriteRuleSigma State Srt Query} {W : State}
    (ctx : BinaryContext) (coord : PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : WMJudgment W)
    (hTau : tau ≤ coord (ITVSemantics.bayesCredible95.eval ctx (r.derive W))) :
    WMITVThresholdJudgmentSigma (State := State) (Srt := Srt) (Query := Query)
      ITVSemantics.bayesCredible95 ctx W r.conclusion coord tau :=
  WMRewriteRuleSigma.applyITVThreshold
    (State := State) (Srt := Srt) (Query := Query)
    ITVSemantics.bayesCredible95 ctx coord tau hSide hW hTau

/-- Typed ITV threshold preservation under Bayes 95% exact-invCDF semantics. -/
theorem WMRewriteRuleSigma.applyITVThreshold_bayesExact95
    {r : WMRewriteRuleSigma State Srt Query} {W : State}
    (ctx : BinaryContext) (coord : PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : WMJudgment W)
    (hTau : tau ≤ coord (ITVSemantics.bayesCredibleExact95.eval ctx (r.derive W))) :
    WMITVThresholdJudgmentSigma (State := State) (Srt := Srt) (Query := Query)
      ITVSemantics.bayesCredibleExact95 ctx W r.conclusion coord tau :=
  WMRewriteRuleSigma.applyITVThreshold
    (State := State) (Srt := Srt) (Query := Query)
    ITVSemantics.bayesCredibleExact95 ctx coord tau hSide hW hTau

/-- Typed ITV threshold preservation under Walley IDM predictive semantics. -/
theorem WMRewriteRuleSigma.applyITVThreshold_walleyIDM
    {r : WMRewriteRuleSigma State Srt Query} {W : State}
    (ctx : IDMPredictiveContext) (coord : PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : WMJudgment W)
    (hTau : tau ≤ coord (ITVSemantics.walleyIDMPredictive.eval ctx (r.derive W))) :
    WMITVThresholdJudgmentSigma (State := State) (Srt := Srt) (Query := Query)
      ITVSemantics.walleyIDMPredictive ctx W r.conclusion coord tau :=
  WMRewriteRuleSigma.applyITVThreshold
    (State := State) (Srt := Srt) (Query := Query)
    ITVSemantics.walleyIDMPredictive ctx coord tau hSide hW hTau

end WorldModelSigma

end Mettapedia.Logic.PLNWorldModel
