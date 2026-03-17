import Mettapedia.Logic.PLNHigherOrderHOLConsequence
import Mettapedia.Logic.PLNLinkCalculus

namespace Mettapedia.Logic.PLNHigherOrderHOLLinkBridge

universe u v w

open Mettapedia.Logic.HOL
open Mettapedia.Logic.PLNWorldModel
open scoped ENNReal

variable {Base : Type u} {Const : Ty Base → Type v}

abbrev HOLQuery (Const : Ty Base → Type v) :=
  Mettapedia.Logic.PLNHigherOrderHOLCore.HOLQuery (Base := Base) Const

abbrev HOLState (Base : Type u) (Const : Ty Base → Type v) :=
  Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState Base Const

abbrev HOLProvImp (φ ψ : HOLQuery Const) : Prop :=
  Mettapedia.Logic.PLNHigherOrderHOLCore.HOLProvImp (Const := Const) φ ψ

abbrev HOLProvIff (φ ψ : HOLQuery Const) : Prop :=
  Mettapedia.Logic.PLNHigherOrderHOLRules.HOLProvIff (Base := Base) (Const := Const) φ ψ

abbrev HOLLinkJudgment :=
  Mettapedia.Logic.PLNLinkCalculus.Judgment (HOLQuery (Base := Base) Const)

/-- A term judgment holds at strength `s` exactly when the HOL WM state extracts that strength. -/
def holdsTermWM (W : HOLState Base Const) (φ : HOLQuery Const) (s : ℝ≥0∞) : Prop :=
  BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const) W φ = s

/-- A higher-order link holds in a WM state when the source query is no stronger than the target. -/
def holdsLinkWM (W : HOLState Base Const) (φ ψ : HOLQuery Const) : Prop :=
  BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const) W φ ≤
    BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const) W ψ

/-- Any proved HOL implication yields a valid higher-order link at every WM state. -/
theorem holdsLinkWM_mono_of_holProvImp {φ ψ : HOLQuery Const}
    (h : HOLProvImp (Const := Const) φ ψ) (W : HOLState Base Const) :
    holdsLinkWM (Base := Base) (Const := Const) W φ ψ :=
  by
    exact Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvImp_implies_multisetConsequence
      (Base := Base) (Const := Const) h W

/-- Provable HOL equivalence transports a WM term judgment unchanged. -/
theorem holdsTermWM_transport_of_holProvIff {φ ψ : HOLQuery Const}
    (h : HOLProvIff (Const := Const) φ ψ)
    (W : HOLState Base Const) (s : ℝ≥0∞) :
    holdsTermWM (Base := Base) (Const := Const) W φ s →
      holdsTermWM (Base := Base) (Const := Const) W ψ s := by
  intro hφ
  have hEq :=
    Mettapedia.Logic.PLNHigherOrderHOLConsequence.holProvIff_to_WMStrengthEq
      (Base := Base) (Const := Const) h W
  dsimp [holdsTermWM] at hφ ⊢
  calc
    BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const) W ψ
        =
      BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const) W φ :=
        hEq.symm
    _ = s := hφ

/-- Provable HOL equivalence yields a valid higher-order link in the forward direction. -/
theorem holdsLinkWM_of_holProvIff_left {φ ψ : HOLQuery Const}
    (h : HOLProvIff (Const := Const) φ ψ) (W : HOLState Base Const) :
    holdsLinkWM (Base := Base) (Const := Const) W φ ψ := by
  have hEq :=
    Mettapedia.Logic.PLNHigherOrderHOLConsequence.holProvIff_to_WMStrengthEq
      (Base := Base) (Const := Const) h W
  simp [holdsLinkWM, hEq]

/-- Provable HOL equivalence yields a valid higher-order link in the reverse direction. -/
theorem holdsLinkWM_of_holProvIff_right {φ ψ : HOLQuery Const}
    (h : HOLProvIff (Const := Const) φ ψ) (W : HOLState Base Const) :
    holdsLinkWM (Base := Base) (Const := Const) W ψ φ := by
  have hEq :=
    Mettapedia.Logic.PLNHigherOrderHOLConsequence.holProvIff_to_WMStrengthEq
      (Base := Base) (Const := Const) h W
  simp [holdsLinkWM, hEq]

end Mettapedia.Logic.PLNHigherOrderHOLLinkBridge
