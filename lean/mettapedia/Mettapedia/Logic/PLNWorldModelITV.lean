import Mettapedia.Logic.PLNWorldModel
import Mettapedia.Logic.PLNWorldModelTyped
import Mettapedia.Logic.PLNIndefiniteTruth

/-!
# PLN World-Model ITV Semantics

This module adds an explicit semantics layer for ITV-valued query views:

- **Bayesian credible-interval semantics** (Beta normal approximation)
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
  eval : Ctx → Evidence → PLNIndefiniteTruth.ITV

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

/-- Bayesian ITV semantics at 95% credible level. -/
noncomputable def bayesCredible95 : ITVSemantics BinaryContext :=
  bayesCredibleNormalApprox 0.95 ⟨by norm_num, by norm_num⟩

/-- Bayesian ITV semantics at 90% credible level. -/
noncomputable def bayesCredible90 : ITVSemantics BinaryContext :=
  bayesCredibleNormalApprox 0.90 ⟨by norm_num, by norm_num⟩

/-- Walley IDM predictive-interval semantics. -/
noncomputable def walleyIDMPredictive : ITVSemantics IDMPredictiveContext where
  eval := fun ctx e => PLNIndefiniteTruth.ITV.fromWalleyIDMPredictive e ctx.s ctx.s_pos

end ITVSemantics

namespace WorldModel

variable {State Query Ctx : Type*} [EvidenceType State] [WorldModel State Query]

/-- ITV query view from an explicit semantics choice. -/
noncomputable def queryITV (sem : ITVSemantics Ctx) (ctx : Ctx) (W : State) (q : Query) :
    PLNIndefiniteTruth.ITV :=
  sem.eval ctx (WorldModel.evidence (State := State) (Query := Query) W q)

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

end WorldModel

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

end WorldModelSigma

end Mettapedia.Logic.PLNWorldModel
