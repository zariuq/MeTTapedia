import Mettapedia.Logic.PLNWorldModelITV
import Mettapedia.OSLF.Framework.PLNWMHypercubeBasis

/-!
# Hypercube-Indexed ITV Semantics (Typed WM Layer)

Connects the interval-semantics axis from `PLNWMHypercubeBasis` to explicit
ITV semantics and typed WM query views.
-/

namespace Mettapedia.Logic.PLNWorldModelITVHypercube

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.OSLF.Framework.PLNWMHypercubeBasis

/-- Context family selected by the interval semantics axis. -/
def CtxOfInterval : WMIntervalSemantics → Type
  | .bayesNormal => BinaryContext
  | .bayesExact => BinaryContext
  | .walleyIDM => IDMPredictiveContext

/-- ITV semantics selected by the interval semantics axis. -/
noncomputable def semanticsOfInterval :
    (i : WMIntervalSemantics) → ITVSemantics (CtxOfInterval i)
  | .bayesNormal => ITVSemantics.bayesCredible95
  | .bayesExact => ITVSemantics.bayesCredibleExact95
  | .walleyIDM => ITVSemantics.walleyIDMPredictive

@[simp] theorem semanticsOfInterval_bayesNormal :
    semanticsOfInterval .bayesNormal = ITVSemantics.bayesCredible95 := rfl

@[simp] theorem semanticsOfInterval_bayesExact :
    semanticsOfInterval .bayesExact = ITVSemantics.bayesCredibleExact95 := rfl

@[simp] theorem semanticsOfInterval_walleyIDM :
    semanticsOfInterval .walleyIDM = ITVSemantics.walleyIDMPredictive := rfl

/-- Context family selected by the interval axis at a WM hypercube vertex. -/
def CtxOfVertex (v : WMVertex) : Type := CtxOfInterval (v .interval)

section Untyped

variable {State Query : Type*}
variable [EvidenceType State] [BinaryWorldModel State Query]

/-- Hypercube-interval-indexed ITV query view (untyped queries). -/
noncomputable def queryITVOfInterval
    (i : WMIntervalSemantics) (ctx : CtxOfInterval i)
    (W : State) (q : Query) : PLNIndefiniteTruth.ITV :=
  BinaryWorldModel.queryITV (State := State) (Query := Query) (Ctx := CtxOfInterval i)
    (semanticsOfInterval i) ctx W q

/-- Hypercube-interval-indexed ITV query lower bound. -/
noncomputable def queryITVLowerOfInterval
    (i : WMIntervalSemantics) (ctx : CtxOfInterval i)
    (W : State) (q : Query) : ℝ :=
  (queryITVOfInterval (State := State) (Query := Query) i ctx W q).lower

/-- Hypercube-interval-indexed ITV query upper bound. -/
noncomputable def queryITVUpperOfInterval
    (i : WMIntervalSemantics) (ctx : CtxOfInterval i)
    (W : State) (q : Query) : ℝ :=
  (queryITVOfInterval (State := State) (Query := Query) i ctx W q).upper

/-- Hypercube-interval-indexed ITV query credibility. -/
noncomputable def queryITVCredibilityOfInterval
    (i : WMIntervalSemantics) (ctx : CtxOfInterval i)
    (W : State) (q : Query) : ℝ :=
  (queryITVOfInterval (State := State) (Query := Query) i ctx W q).credibility

/-- Hypercube-interval-indexed ITV query midpoint strength. -/
noncomputable def queryITVStrengthOfInterval
    (i : WMIntervalSemantics) (ctx : CtxOfInterval i)
    (W : State) (q : Query) : ℝ :=
  (queryITVOfInterval (State := State) (Query := Query) i ctx W q).strength

/-- Hypercube-interval-indexed ITV query width. -/
noncomputable def queryITVWidthOfInterval
    (i : WMIntervalSemantics) (ctx : CtxOfInterval i)
    (W : State) (q : Query) : ℝ :=
  (queryITVOfInterval (State := State) (Query := Query) i ctx W q).width

end Untyped

section Typed

variable {State Srt : Type*} {Query : Srt → Type*}
variable [EvidenceType State] [WorldModelSigma State Srt Query]

/-- Hypercube-interval-indexed ITV query view (typed/sort-indexed queries). -/
noncomputable def queryITVSigmaOfInterval
    (i : WMIntervalSemantics) (ctx : CtxOfInterval i)
    (W : State) (q : Sigma Query) : PLNIndefiniteTruth.ITV :=
  WorldModelSigma.queryITV
    (State := State) (Srt := Srt) (Query := Query) (Ctx := CtxOfInterval i)
    (semanticsOfInterval i) ctx W q

/-- Hypercube-interval-indexed ITV query lower bound (typed). -/
noncomputable def queryITVSigmaLowerOfInterval
    (i : WMIntervalSemantics) (ctx : CtxOfInterval i)
    (W : State) (q : Sigma Query) : ℝ :=
  (queryITVSigmaOfInterval (State := State) (Srt := Srt) (Query := Query) i ctx W q).lower

/-- Hypercube-interval-indexed ITV query upper bound (typed). -/
noncomputable def queryITVSigmaUpperOfInterval
    (i : WMIntervalSemantics) (ctx : CtxOfInterval i)
    (W : State) (q : Sigma Query) : ℝ :=
  (queryITVSigmaOfInterval (State := State) (Srt := Srt) (Query := Query) i ctx W q).upper

/-- Hypercube-interval-indexed ITV query credibility (typed). -/
noncomputable def queryITVSigmaCredibilityOfInterval
    (i : WMIntervalSemantics) (ctx : CtxOfInterval i)
    (W : State) (q : Sigma Query) : ℝ :=
  (queryITVSigmaOfInterval (State := State) (Srt := Srt) (Query := Query) i ctx W q).credibility

/-- Hypercube-interval-indexed ITV query midpoint strength (typed). -/
noncomputable def queryITVSigmaStrengthOfInterval
    (i : WMIntervalSemantics) (ctx : CtxOfInterval i)
    (W : State) (q : Sigma Query) : ℝ :=
  (queryITVSigmaOfInterval (State := State) (Srt := Srt) (Query := Query) i ctx W q).strength

/-- Hypercube-interval-indexed ITV query width (typed). -/
noncomputable def queryITVSigmaWidthOfInterval
    (i : WMIntervalSemantics) (ctx : CtxOfInterval i)
    (W : State) (q : Sigma Query) : ℝ :=
  (queryITVSigmaOfInterval (State := State) (Srt := Srt) (Query := Query) i ctx W q).width

/-- Hypercube-vertex-indexed ITV query view (typed). -/
noncomputable def queryITVAtVertex
    (v : WMVertex) (ctx : CtxOfVertex v)
    (W : State) (q : Sigma Query) : PLNIndefiniteTruth.ITV :=
  queryITVSigmaOfInterval
    (State := State) (Srt := Srt) (Query := Query) (v .interval) ctx W q

/-- Hypercube-vertex-indexed ITV query view at an explicit sort. -/
noncomputable def queryITVAtVertexAt
    (v : WMVertex) (ctx : CtxOfVertex v)
    (W : State) {s : Srt} (q : Query s) : PLNIndefiniteTruth.ITV :=
  queryITVAtVertex (State := State) (Srt := Srt) (Query := Query) v ctx W ⟨s, q⟩

/-- Hypercube-vertex-indexed ITV query lower bound (typed). -/
noncomputable def queryITVAtVertexLower
    (v : WMVertex) (ctx : CtxOfVertex v)
    (W : State) (q : Sigma Query) : ℝ :=
  (queryITVAtVertex (State := State) (Srt := Srt) (Query := Query) v ctx W q).lower

/-- Hypercube-vertex-indexed ITV query upper bound (typed). -/
noncomputable def queryITVAtVertexUpper
    (v : WMVertex) (ctx : CtxOfVertex v)
    (W : State) (q : Sigma Query) : ℝ :=
  (queryITVAtVertex (State := State) (Srt := Srt) (Query := Query) v ctx W q).upper

/-- Hypercube-vertex-indexed ITV query credibility (typed). -/
noncomputable def queryITVAtVertexCredibility
    (v : WMVertex) (ctx : CtxOfVertex v)
    (W : State) (q : Sigma Query) : ℝ :=
  (queryITVAtVertex (State := State) (Srt := Srt) (Query := Query) v ctx W q).credibility

/-- Hypercube-vertex-indexed ITV query midpoint strength (typed). -/
noncomputable def queryITVAtVertexStrength
    (v : WMVertex) (ctx : CtxOfVertex v)
    (W : State) (q : Sigma Query) : ℝ :=
  (queryITVAtVertex (State := State) (Srt := Srt) (Query := Query) v ctx W q).strength

/-- Hypercube-vertex-indexed ITV query width (typed). -/
noncomputable def queryITVAtVertexWidth
    (v : WMVertex) (ctx : CtxOfVertex v)
    (W : State) (q : Sigma Query) : ℝ :=
  (queryITVAtVertex (State := State) (Srt := Srt) (Query := Query) v ctx W q).width

/-- Walley interval identity at the interval-axis level (typed): `width + credibility = 1`. -/
theorem queryITVSigma_width_add_credibility_walley
    (ctx : CtxOfInterval .walleyIDM) (W : State) (q : Sigma Query) :
    queryITVSigmaWidthOfInterval
      (State := State) (Srt := Srt) (Query := Query) .walleyIDM ctx W q +
      queryITVSigmaCredibilityOfInterval
        (State := State) (Srt := Srt) (Query := Query) .walleyIDM ctx W q = 1 := by
  simpa [queryITVSigmaWidthOfInterval, queryITVSigmaCredibilityOfInterval,
    queryITVSigmaOfInterval, semanticsOfInterval] using
    (WorldModelSigma.queryITVWidth_add_queryITVCredibility_walley
      (State := State) (Srt := Srt) (Query := Query) ctx W q)

/-- Walley interval identity at the interval-axis level (typed): `width = 1 - credibility`. -/
theorem queryITVSigma_width_eq_one_sub_credibility_walley
    (ctx : CtxOfInterval .walleyIDM) (W : State) (q : Sigma Query) :
    queryITVSigmaWidthOfInterval
      (State := State) (Srt := Srt) (Query := Query) .walleyIDM ctx W q =
      1 - queryITVSigmaCredibilityOfInterval
        (State := State) (Srt := Srt) (Query := Query) .walleyIDM ctx W q := by
  simpa [queryITVSigmaWidthOfInterval, queryITVSigmaCredibilityOfInterval,
    queryITVSigmaOfInterval, semanticsOfInterval] using
    (WorldModelSigma.queryITVWidth_eq_one_sub_queryITVCredibility_walley
      (State := State) (Srt := Srt) (Query := Query) ctx W q)

/-- Interval-selector transport of typed query-equivalence into ITV views. -/
theorem WMQueryEqSigma.to_queryITVSigmaOfInterval
    {q₁ q₂ : Sigma Query}
    (hEq : WorldModelSigma.WMQueryEqSigma
      (State := State) (Srt := Srt) (Query := Query) q₁ q₂)
    (i : WMIntervalSemantics) (ctx : CtxOfInterval i) (W : State) :
    queryITVSigmaOfInterval
      (State := State) (Srt := Srt) (Query := Query) i ctx W q₁ =
      queryITVSigmaOfInterval
        (State := State) (Srt := Srt) (Query := Query) i ctx W q₂ := by
  unfold queryITVSigmaOfInterval
  simpa using
    (WorldModelSigma.WMQueryEqSigma.to_queryITV
      (State := State) (Srt := Srt) (Query := Query)
      hEq (semanticsOfInterval i) ctx W)

/-- Vertex-selector transport of typed query-equivalence into ITV views. -/
theorem WMQueryEqSigma.to_queryITVAtVertex
    {q₁ q₂ : Sigma Query}
    (hEq : WorldModelSigma.WMQueryEqSigma
      (State := State) (Srt := Srt) (Query := Query) q₁ q₂)
    (v : WMVertex) (ctx : CtxOfVertex v) (W : State) :
    queryITVAtVertex
      (State := State) (Srt := Srt) (Query := Query) v ctx W q₁ =
      queryITVAtVertex
        (State := State) (Srt := Srt) (Query := Query) v ctx W q₂ := by
  simpa [queryITVAtVertex] using
    (WMQueryEqSigma.to_queryITVSigmaOfInterval
      (State := State) (Srt := Srt) (Query := Query)
      hEq (v .interval) ctx W)

/-- Bayes-exact selector transport of typed query-equivalence into ITV views. -/
theorem WMQueryEqSigma.to_queryITVSigma_bayesExact
    {q₁ q₂ : Sigma Query}
    (hEq : WorldModelSigma.WMQueryEqSigma
      (State := State) (Srt := Srt) (Query := Query) q₁ q₂)
    (ctx : CtxOfInterval .bayesExact) (W : State) :
    queryITVSigmaOfInterval
      (State := State) (Srt := Srt) (Query := Query) .bayesExact ctx W q₁ =
      queryITVSigmaOfInterval
        (State := State) (Srt := Srt) (Query := Query) .bayesExact ctx W q₂ :=
  WMQueryEqSigma.to_queryITVSigmaOfInterval
    (State := State) (Srt := Srt) (Query := Query) hEq .bayesExact ctx W

/-- Walley selector transport of typed query-equivalence into ITV views. -/
theorem WMQueryEqSigma.to_queryITVSigma_walley
    {q₁ q₂ : Sigma Query}
    (hEq : WorldModelSigma.WMQueryEqSigma
      (State := State) (Srt := Srt) (Query := Query) q₁ q₂)
    (ctx : CtxOfInterval .walleyIDM) (W : State) :
    queryITVSigmaOfInterval
      (State := State) (Srt := Srt) (Query := Query) .walleyIDM ctx W q₁ =
      queryITVSigmaOfInterval
        (State := State) (Srt := Srt) (Query := Query) .walleyIDM ctx W q₂ :=
  WMQueryEqSigma.to_queryITVSigmaOfInterval
    (State := State) (Srt := Srt) (Query := Query) hEq .walleyIDM ctx W

/-- Interval-selector transport of typed ITV judgments along query equivalence. -/
theorem WMQueryEqSigma.to_WMITVJudgmentSigmaOfInterval
    {q₁ q₂ : Sigma Query}
    (hEq : WorldModelSigma.WMQueryEqSigma
      (State := State) (Srt := Srt) (Query := Query) q₁ q₂)
    (i : WMIntervalSemantics) (ctx : CtxOfInterval i)
    {W : State} {itv : PLNIndefiniteTruth.ITV}
    (hJudg : WorldModelSigma.WMITVJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query)
      (semanticsOfInterval i) ctx W q₁ itv) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query)
      (semanticsOfInterval i) ctx W q₂ itv := by
  rcases hJudg with ⟨hW, hItv⟩
  refine ⟨hW, ?_⟩
  calc
    itv = queryITVSigmaOfInterval
      (State := State) (Srt := Srt) (Query := Query) i ctx W q₁ := by
        simpa [queryITVSigmaOfInterval] using hItv
    _ = queryITVSigmaOfInterval
      (State := State) (Srt := Srt) (Query := Query) i ctx W q₂ :=
        WMQueryEqSigma.to_queryITVSigmaOfInterval
          (State := State) (Srt := Srt) (Query := Query) hEq i ctx W

/-- Bayes-exact selector transport of typed ITV judgments along query equivalence. -/
theorem WMQueryEqSigma.to_WMITVJudgmentSigma_bayesExact
    {q₁ q₂ : Sigma Query}
    (hEq : WorldModelSigma.WMQueryEqSigma
      (State := State) (Srt := Srt) (Query := Query) q₁ q₂)
    (ctx : CtxOfInterval .bayesExact)
    {W : State} {itv : PLNIndefiniteTruth.ITV}
    (hJudg : WorldModelSigma.WMITVJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query)
      (semanticsOfInterval .bayesExact) ctx W q₁ itv) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query)
      (semanticsOfInterval .bayesExact) ctx W q₂ itv :=
  WMQueryEqSigma.to_WMITVJudgmentSigmaOfInterval
    (State := State) (Srt := Srt) (Query := Query) hEq .bayesExact ctx hJudg

/-- Walley selector transport of typed ITV judgments along query equivalence. -/
theorem WMQueryEqSigma.to_WMITVJudgmentSigma_walley
    {q₁ q₂ : Sigma Query}
    (hEq : WorldModelSigma.WMQueryEqSigma
      (State := State) (Srt := Srt) (Query := Query) q₁ q₂)
    (ctx : CtxOfInterval .walleyIDM)
    {W : State} {itv : PLNIndefiniteTruth.ITV}
    (hJudg : WorldModelSigma.WMITVJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query)
      (semanticsOfInterval .walleyIDM) ctx W q₁ itv) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query)
      (semanticsOfInterval .walleyIDM) ctx W q₂ itv :=
  WMQueryEqSigma.to_WMITVJudgmentSigmaOfInterval
    (State := State) (Srt := Srt) (Query := Query) hEq .walleyIDM ctx hJudg

/-- Interval-selector transport of typed ITV-threshold judgments along query equivalence. -/
theorem WMQueryEqSigma.to_WMITVThresholdJudgmentSigmaOfInterval
    {q₁ q₂ : Sigma Query}
    (hEq : WorldModelSigma.WMQueryEqSigma
      (State := State) (Srt := Srt) (Query := Query) q₁ q₂)
    (i : WMIntervalSemantics) (ctx : CtxOfInterval i)
    {W : State}
    (coord : PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hJudg : WorldModelSigma.WMITVThresholdJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query)
      (semanticsOfInterval i) ctx W q₁ coord tau) :
    WorldModelSigma.WMITVThresholdJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query)
      (semanticsOfInterval i) ctx W q₂ coord tau := by
  rcases hJudg with ⟨hW, hTau⟩
  refine ⟨hW, ?_⟩
  have hTau' :
      tau ≤ coord
        (WorldModelSigma.queryITV
          (State := State) (Srt := Srt) (Query := Query) (Ctx := CtxOfInterval i)
          (semanticsOfInterval i) ctx W q₁) := by
    simpa [queryITVSigmaOfInterval] using hTau
  have hTau'' := WorldModelSigma.WMQueryEqSigma.to_queryITV_threshold
    (State := State) (Srt := Srt) (Query := Query)
    hEq (semanticsOfInterval i) ctx W coord tau hTau'
  simpa [queryITVSigmaOfInterval] using hTau''

/-- Bayes-exact selector transport of typed ITV-threshold judgments along query equivalence. -/
theorem WMQueryEqSigma.to_WMITVThresholdJudgmentSigma_bayesExact
    {q₁ q₂ : Sigma Query}
    (hEq : WorldModelSigma.WMQueryEqSigma
      (State := State) (Srt := Srt) (Query := Query) q₁ q₂)
    (ctx : CtxOfInterval .bayesExact)
    {W : State}
    (coord : PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hJudg : WorldModelSigma.WMITVThresholdJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query)
      (semanticsOfInterval .bayesExact) ctx W q₁ coord tau) :
    WorldModelSigma.WMITVThresholdJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query)
      (semanticsOfInterval .bayesExact) ctx W q₂ coord tau :=
  WMQueryEqSigma.to_WMITVThresholdJudgmentSigmaOfInterval
    (State := State) (Srt := Srt) (Query := Query)
    hEq .bayesExact ctx coord tau hJudg

/-- Walley selector transport of typed ITV-threshold judgments along query equivalence. -/
theorem WMQueryEqSigma.to_WMITVThresholdJudgmentSigma_walley
    {q₁ q₂ : Sigma Query}
    (hEq : WorldModelSigma.WMQueryEqSigma
      (State := State) (Srt := Srt) (Query := Query) q₁ q₂)
    (ctx : CtxOfInterval .walleyIDM)
    {W : State}
    (coord : PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hJudg : WorldModelSigma.WMITVThresholdJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query)
      (semanticsOfInterval .walleyIDM) ctx W q₁ coord tau) :
    WorldModelSigma.WMITVThresholdJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query)
      (semanticsOfInterval .walleyIDM) ctx W q₂ coord tau :=
  WMQueryEqSigma.to_WMITVThresholdJudgmentSigmaOfInterval
    (State := State) (Srt := Srt) (Query := Query)
    hEq .walleyIDM ctx coord tau hJudg

/-- Interval-selector rewrite-preservation for typed ITV judgments. -/
theorem WMRewriteRuleSigma.applyITV_ofInterval
    {r : WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W : State}
    (i : WMIntervalSemantics) (ctx : CtxOfInterval i)
    (hSide : r.side) (hW : WMJudgment W) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query)
      (semanticsOfInterval i) ctx
      W r.conclusion ((semanticsOfInterval i).eval ctx (r.derive W)) :=
  WorldModelSigma.WMRewriteRuleSigma.applyITV
    (State := State) (Srt := Srt) (Query := Query)
    (semanticsOfInterval i) ctx hSide hW

/-- Interval-selector rewrite-preservation for typed ITV threshold judgments. -/
theorem WMRewriteRuleSigma.applyITVThreshold_ofInterval
    {r : WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W : State}
    (i : WMIntervalSemantics) (ctx : CtxOfInterval i)
    (coord : PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : WMJudgment W)
    (hTau : tau ≤ coord ((semanticsOfInterval i).eval ctx (r.derive W))) :
    WorldModelSigma.WMITVThresholdJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query)
      (semanticsOfInterval i) ctx
      W r.conclusion coord tau :=
  WorldModelSigma.WMRewriteRuleSigma.applyITVThreshold
    (State := State) (Srt := Srt) (Query := Query)
    (semanticsOfInterval i) ctx coord tau hSide hW hTau

/-- Bayes-normal selector rewrite-preservation for typed ITV judgments. -/
theorem WMRewriteRuleSigma.applyITV_bayesNormal_selector
    {r : WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W : State}
    (ctx : CtxOfInterval .bayesNormal) (hSide : r.side) (hW : WMJudgment W) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query)
      (semanticsOfInterval .bayesNormal) ctx
      W r.conclusion ((semanticsOfInterval .bayesNormal).eval ctx (r.derive W)) := by
  simpa [semanticsOfInterval] using
    (WMRewriteRuleSigma.applyITV_ofInterval
      (State := State) (Srt := Srt) (Query := Query)
      (r := r) .bayesNormal ctx hSide hW)

/-- Bayes-exact selector rewrite-preservation for typed ITV judgments. -/
theorem WMRewriteRuleSigma.applyITV_bayesExact_selector
    {r : WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W : State}
    (ctx : CtxOfInterval .bayesExact) (hSide : r.side) (hW : WMJudgment W) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query)
      (semanticsOfInterval .bayesExact) ctx
      W r.conclusion ((semanticsOfInterval .bayesExact).eval ctx (r.derive W)) := by
  simpa [semanticsOfInterval] using
    (WMRewriteRuleSigma.applyITV_ofInterval
      (State := State) (Srt := Srt) (Query := Query)
      (r := r) .bayesExact ctx hSide hW)

/-- Walley selector rewrite-preservation for typed ITV judgments. -/
theorem WMRewriteRuleSigma.applyITV_walley_selector
    {r : WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W : State}
    (ctx : CtxOfInterval .walleyIDM) (hSide : r.side) (hW : WMJudgment W) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query)
      (semanticsOfInterval .walleyIDM) ctx
      W r.conclusion ((semanticsOfInterval .walleyIDM).eval ctx (r.derive W)) := by
  simpa [semanticsOfInterval] using
    (WMRewriteRuleSigma.applyITV_ofInterval
      (State := State) (Srt := Srt) (Query := Query)
      (r := r) .walleyIDM ctx hSide hW)

/-- Bayes-exact selector rewrite-preservation for typed ITV threshold judgments. -/
theorem WMRewriteRuleSigma.applyITVThreshold_bayesExact_selector
    {r : WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W : State}
    (ctx : CtxOfInterval .bayesExact)
    (coord : PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : WMJudgment W)
    (hTau : tau ≤ coord ((semanticsOfInterval .bayesExact).eval ctx (r.derive W))) :
    WorldModelSigma.WMITVThresholdJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query)
      (semanticsOfInterval .bayesExact) ctx
      W r.conclusion coord tau := by
  simpa [semanticsOfInterval] using
    (WMRewriteRuleSigma.applyITVThreshold_ofInterval
      (State := State) (Srt := Srt) (Query := Query)
      (r := r) .bayesExact ctx coord tau hSide hW hTau)

/-- Walley selector rewrite-preservation for typed ITV threshold judgments. -/
theorem WMRewriteRuleSigma.applyITVThreshold_walley_selector
    {r : WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W : State}
    (ctx : CtxOfInterval .walleyIDM)
    (coord : PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : WMJudgment W)
    (hTau : tau ≤ coord ((semanticsOfInterval .walleyIDM).eval ctx (r.derive W))) :
    WorldModelSigma.WMITVThresholdJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query)
      (semanticsOfInterval .walleyIDM) ctx
      W r.conclusion coord tau := by
  simpa [semanticsOfInterval] using
    (WMRewriteRuleSigma.applyITVThreshold_ofInterval
      (State := State) (Srt := Srt) (Query := Query)
      (r := r) .walleyIDM ctx coord tau hSide hW hTau)

/-- Bayes-exact selector, lower-coordinate threshold rewrite preservation. -/
theorem WMRewriteRuleSigma.applyITVThreshold_bayesExact_lower_selector
    {r : WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W : State}
    (ctx : CtxOfInterval .bayesExact) (tau : ℝ)
    (hSide : r.side) (hW : WMJudgment W)
    (hTau : tau ≤ ((semanticsOfInterval .bayesExact).eval ctx (r.derive W)).lower) :
    WorldModelSigma.WMITVThresholdJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query)
      (semanticsOfInterval .bayesExact) ctx
      W r.conclusion (fun itv => itv.lower) tau :=
  WMRewriteRuleSigma.applyITVThreshold_bayesExact_selector
    (State := State) (Srt := Srt) (Query := Query)
    (r := r) ctx (fun itv => itv.lower) tau hSide hW hTau

/-- Bayes-exact selector, upper-coordinate threshold rewrite preservation. -/
theorem WMRewriteRuleSigma.applyITVThreshold_bayesExact_upper_selector
    {r : WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W : State}
    (ctx : CtxOfInterval .bayesExact) (tau : ℝ)
    (hSide : r.side) (hW : WMJudgment W)
    (hTau : tau ≤ ((semanticsOfInterval .bayesExact).eval ctx (r.derive W)).upper) :
    WorldModelSigma.WMITVThresholdJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query)
      (semanticsOfInterval .bayesExact) ctx
      W r.conclusion (fun itv => itv.upper) tau :=
  WMRewriteRuleSigma.applyITVThreshold_bayesExact_selector
    (State := State) (Srt := Srt) (Query := Query)
    (r := r) ctx (fun itv => itv.upper) tau hSide hW hTau

/-- Bayes-exact selector, credibility-coordinate threshold rewrite preservation. -/
theorem WMRewriteRuleSigma.applyITVThreshold_bayesExact_credibility_selector
    {r : WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W : State}
    (ctx : CtxOfInterval .bayesExact) (tau : ℝ)
    (hSide : r.side) (hW : WMJudgment W)
    (hTau : tau ≤ ((semanticsOfInterval .bayesExact).eval ctx (r.derive W)).credibility) :
    WorldModelSigma.WMITVThresholdJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query)
      (semanticsOfInterval .bayesExact) ctx
      W r.conclusion (fun itv => itv.credibility) tau :=
  WMRewriteRuleSigma.applyITVThreshold_bayesExact_selector
    (State := State) (Srt := Srt) (Query := Query)
    (r := r) ctx (fun itv => itv.credibility) tau hSide hW hTau

/-- Bayes-exact selector, width-coordinate threshold rewrite preservation. -/
theorem WMRewriteRuleSigma.applyITVThreshold_bayesExact_width_selector
    {r : WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W : State}
    (ctx : CtxOfInterval .bayesExact) (tau : ℝ)
    (hSide : r.side) (hW : WMJudgment W)
    (hTau : tau ≤ ((semanticsOfInterval .bayesExact).eval ctx (r.derive W)).width) :
    WorldModelSigma.WMITVThresholdJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query)
      (semanticsOfInterval .bayesExact) ctx
      W r.conclusion (fun itv => itv.width) tau :=
  WMRewriteRuleSigma.applyITVThreshold_bayesExact_selector
    (State := State) (Srt := Srt) (Query := Query)
    (r := r) ctx (fun itv => itv.width) tau hSide hW hTau

/-- Bayes-exact selector, strength-coordinate threshold rewrite preservation. -/
theorem WMRewriteRuleSigma.applyITVThreshold_bayesExact_strength_selector
    {r : WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W : State}
    (ctx : CtxOfInterval .bayesExact) (tau : ℝ)
    (hSide : r.side) (hW : WMJudgment W)
    (hTau : tau ≤ ((semanticsOfInterval .bayesExact).eval ctx (r.derive W)).strength) :
    WorldModelSigma.WMITVThresholdJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query)
      (semanticsOfInterval .bayesExact) ctx
      W r.conclusion (fun itv => itv.strength) tau :=
  WMRewriteRuleSigma.applyITVThreshold_bayesExact_selector
    (State := State) (Srt := Srt) (Query := Query)
    (r := r) ctx (fun itv => itv.strength) tau hSide hW hTau

/-- Walley selector, lower-coordinate threshold rewrite preservation. -/
theorem WMRewriteRuleSigma.applyITVThreshold_walley_lower_selector
    {r : WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W : State}
    (ctx : CtxOfInterval .walleyIDM) (tau : ℝ)
    (hSide : r.side) (hW : WMJudgment W)
    (hTau : tau ≤ ((semanticsOfInterval .walleyIDM).eval ctx (r.derive W)).lower) :
    WorldModelSigma.WMITVThresholdJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query)
      (semanticsOfInterval .walleyIDM) ctx
      W r.conclusion (fun itv => itv.lower) tau :=
  WMRewriteRuleSigma.applyITVThreshold_walley_selector
    (State := State) (Srt := Srt) (Query := Query)
    (r := r) ctx (fun itv => itv.lower) tau hSide hW hTau

/-- Walley selector, upper-coordinate threshold rewrite preservation. -/
theorem WMRewriteRuleSigma.applyITVThreshold_walley_upper_selector
    {r : WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W : State}
    (ctx : CtxOfInterval .walleyIDM) (tau : ℝ)
    (hSide : r.side) (hW : WMJudgment W)
    (hTau : tau ≤ ((semanticsOfInterval .walleyIDM).eval ctx (r.derive W)).upper) :
    WorldModelSigma.WMITVThresholdJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query)
      (semanticsOfInterval .walleyIDM) ctx
      W r.conclusion (fun itv => itv.upper) tau :=
  WMRewriteRuleSigma.applyITVThreshold_walley_selector
    (State := State) (Srt := Srt) (Query := Query)
    (r := r) ctx (fun itv => itv.upper) tau hSide hW hTau

/-- Walley selector, credibility-coordinate threshold rewrite preservation. -/
theorem WMRewriteRuleSigma.applyITVThreshold_walley_credibility_selector
    {r : WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W : State}
    (ctx : CtxOfInterval .walleyIDM) (tau : ℝ)
    (hSide : r.side) (hW : WMJudgment W)
    (hTau : tau ≤ ((semanticsOfInterval .walleyIDM).eval ctx (r.derive W)).credibility) :
    WorldModelSigma.WMITVThresholdJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query)
      (semanticsOfInterval .walleyIDM) ctx
      W r.conclusion (fun itv => itv.credibility) tau :=
  WMRewriteRuleSigma.applyITVThreshold_walley_selector
    (State := State) (Srt := Srt) (Query := Query)
    (r := r) ctx (fun itv => itv.credibility) tau hSide hW hTau

/-- Walley selector, width-coordinate threshold rewrite preservation. -/
theorem WMRewriteRuleSigma.applyITVThreshold_walley_width_selector
    {r : WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W : State}
    (ctx : CtxOfInterval .walleyIDM) (tau : ℝ)
    (hSide : r.side) (hW : WMJudgment W)
    (hTau : tau ≤ ((semanticsOfInterval .walleyIDM).eval ctx (r.derive W)).width) :
    WorldModelSigma.WMITVThresholdJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query)
      (semanticsOfInterval .walleyIDM) ctx
      W r.conclusion (fun itv => itv.width) tau :=
  WMRewriteRuleSigma.applyITVThreshold_walley_selector
    (State := State) (Srt := Srt) (Query := Query)
    (r := r) ctx (fun itv => itv.width) tau hSide hW hTau

/-- Walley selector, strength-coordinate threshold rewrite preservation. -/
theorem WMRewriteRuleSigma.applyITVThreshold_walley_strength_selector
    {r : WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W : State}
    (ctx : CtxOfInterval .walleyIDM) (tau : ℝ)
    (hSide : r.side) (hW : WMJudgment W)
    (hTau : tau ≤ ((semanticsOfInterval .walleyIDM).eval ctx (r.derive W)).strength) :
    WorldModelSigma.WMITVThresholdJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query)
      (semanticsOfInterval .walleyIDM) ctx
      W r.conclusion (fun itv => itv.strength) tau :=
  WMRewriteRuleSigma.applyITVThreshold_walley_selector
    (State := State) (Srt := Srt) (Query := Query)
    (r := r) ctx (fun itv => itv.strength) tau hSide hW hTau

end Typed

end Mettapedia.Logic.PLNWorldModelITVHypercube
