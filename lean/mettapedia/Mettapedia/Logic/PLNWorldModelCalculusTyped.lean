import Mettapedia.Logic.PLNWorldModelTyped

/-!
# PLN World-Model Calculus (Typed Query Rewrite Layer)

Typed companion to `PLNWorldModelCalculus`, using sort-indexed queries
`Query : Srt → Type` packaged as `Sigma Query`.
-/

namespace Mettapedia.Logic.PLNWorldModel

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open scoped ENNReal

namespace WorldModelSigma

variable {State Srt : Type*} {Query : Srt → Type*}
variable [EvidenceType State] [WorldModelSigma State Srt Query]

/-! ## Typed query equivalence -/

/-- Two typed queries are equivalent if they extract identical evidence
from every WM state. -/
def WMQueryEqSigma (q₁ q₂ : Sigma Query) : Prop :=
  ∀ W : State, WorldModelSigma.evidence W q₁ = WorldModelSigma.evidence W q₂

theorem WMQueryEqSigma.refl (q : Sigma Query) :
    WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q q := by
  intro W
  rfl

theorem WMQueryEqSigma.symm {q₁ q₂ : Sigma Query} :
    WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q₁ q₂ →
      WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q₂ q₁ := by
  intro h W
  simpa using (h W).symm

theorem WMQueryEqSigma.trans {q₁ q₂ q₃ : Sigma Query} :
    WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q₁ q₂ →
    WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q₂ q₃ →
      WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q₁ q₃ := by
  intro h12 h23 W
  simpa [h12 W] using h23 W

theorem WMQueryEqSigma.to_queryStrength {q₁ q₂ : Sigma Query} :
    WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q₁ q₂ →
      ∀ W : State, queryStrength W q₁ = queryStrength W q₂ := by
  intro h W
  simpa [queryStrength] using congrArg Evidence.toStrength (h W)

/-! ## Typed rewrite templates -/

/-- If side conditions prove typed query equivalence, rewrite `q₂` using `q₁`. -/
def rewrite_of_WMQueryEqSigma
    (Side : Prop) (q₁ q₂ : Sigma Query)
    (h : Side →
      WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q₁ q₂) :
    WMRewriteRuleSigma State Srt Query :=
  { side := Side
    conclusion := q₂
    derive := fun W => WorldModelSigma.evidence W q₁
    sound := by
      intro hSide W
      exact (h hSide W) }

/-- Strength-level rewrite induced by typed query equivalence. -/
noncomputable def strengthRewrite_of_WMQueryEqSigma
    (Side : Prop) (q₁ q₂ : Sigma Query)
    (h : Side →
      WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q₁ q₂) :
    WMStrengthRuleSigma State Srt Query :=
  { side := Side
    conclusion := q₂
    derive := fun W => queryStrength W q₁
    sound := by
      intro hSide W
      exact (WMQueryEqSigma.to_queryStrength (State := State) (Srt := Srt) (Query := Query)
        (h hSide) W) }

end WorldModelSigma

end Mettapedia.Logic.PLNWorldModel
