import Mettapedia.Logic.PLNHigherOrderHOLSoundness
import Mettapedia.Logic.PLNWorldModelCalculus

namespace Mettapedia.Logic.PLNHigherOrderHOLConsequence

universe u v w

open Mettapedia.Logic.HOL
open Mettapedia.Logic.PLNWorldModel

variable {Base : Type u} {Const : Ty Base → Type v}

abbrev HOLQuery (Const : Ty Base → Type v) :=
  Mettapedia.Logic.PLNHigherOrderHOLCore.HOLQuery (Base := Base) Const

abbrev HOLState (Base : Type u) (Const : Ty Base → Type v) :=
  Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState Base Const

abbrev HOLProvImp (φ ψ : HOLQuery Const) : Prop :=
  Mettapedia.Logic.PLNHigherOrderHOLCore.HOLProvImp (Const := Const) φ ψ

abbrev HOLProvIff (φ ψ : HOLQuery Const) : Prop :=
  Mettapedia.Logic.PLNHigherOrderHOLRules.HOLProvIff (Base := Base) (Const := Const) φ ψ

abbrev HOLWMQueryEq (φ ψ : HOLQuery Const) : Prop :=
  WMQueryEq
    (State := Multiset (HenkinModel.{u, v, w} Base Const))
    (Query := HOLQuery Const) φ ψ

abbrev HOLWMStrengthEq (φ ψ : HOLQuery Const) : Prop :=
  ∀ W : Multiset (HenkinModel.{u, v, w} Base Const),
    BinaryWorldModel.queryStrength
        (State := Multiset (HenkinModel.{u, v, w} Base Const))
        (Query := HOLQuery Const) W φ =
      BinaryWorldModel.queryStrength
        (State := Multiset (HenkinModel.{u, v, w} Base Const))
        (Query := HOLQuery Const) W ψ

/-- Proof-backed WM strength transport for higher-order HOL queries. -/
theorem holProvImp_to_WMStrengthLE {φ ψ : HOLQuery Const}
    (h : HOLProvImp (Const := Const) φ ψ) :
    WMStrengthLE (State := HOLState Base Const) (Query := HOLQuery Const) φ ψ :=
  Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvImp_implies_multisetConsequence
    (Base := Base) (Const := Const) h

/-- Proof-backed WM query equivalence for higher-order HOL queries. -/
theorem holProvIff_to_WMQueryEq {φ ψ : HOLQuery Const}
    (h : HOLProvIff (Const := Const) φ ψ) :
    HOLWMQueryEq (Base := Base) (Const := Const) φ ψ :=
  Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvIff_implies_queryEq
    (Base := Base) (Const := Const) h

/-- Proof-backed WM strength equality for higher-order HOL queries. -/
theorem holProvIff_to_WMStrengthEq {φ ψ : HOLQuery Const}
    (h : HOLProvIff (Const := Const) φ ψ) :
    HOLWMStrengthEq (Base := Base) (Const := Const) φ ψ :=
  Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvIff_implies_strengthEq
    (Base := Base) (Const := Const) h

/-- A proved HOL implication packages as a global WM consequence rule. -/
noncomputable def wmConsequenceRule_of_holProvImp {φ ψ : HOLQuery Const}
    (h : HOLProvImp (Const := Const) φ ψ) :
    WMConsequenceRule (HOLState Base Const) (HOLQuery Const) where
  side := True
  premise := φ
  conclusion := ψ
  sound := by
    intro _ W
    exact Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvImp_implies_multisetConsequence
      (Base := Base) (Const := Const) h W

/-- A proved HOL implication packages as a state-indexed WM consequence rule. -/
noncomputable def wmConsequenceRuleOn_of_holProvImp {φ ψ : HOLQuery Const}
    (h : HOLProvImp (Const := Const) φ ψ) :
    WMConsequenceRuleOn (HOLState Base Const) (HOLQuery Const) :=
  WMConsequenceRuleOn.ofGlobal
    (wmConsequenceRule_of_holProvImp (Base := Base) (Const := Const) h)

/-- Apply the proof-backed WM consequence rule directly at a world-model state. -/
theorem holProvImp_to_WMConsequenceRuleOn_apply {φ ψ : HOLQuery Const}
    (h : HOLProvImp (Const := Const) φ ψ) (W : HOLState Base Const) :
    BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const) W φ ≤
      BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const) W ψ :=
  Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvImp_implies_multisetConsequence
    (Base := Base) (Const := Const) h W

/-- A proved HOL equivalence packages as a sound WM query rewrite. -/
noncomputable def wmRewriteRule_of_holProvIff {φ ψ : HOLQuery Const}
    (h : HOLProvIff (Const := Const) φ ψ) :
    WMRewriteRule (HOLState Base Const) (HOLQuery Const) where
  side := True
  conclusion := ψ
  derive := fun W => BinaryWorldModel.evidence (State := HOLState Base Const) (Query := HOLQuery Const) W φ
  sound := by
    intro _ W
    exact holProvIff_to_WMQueryEq (Base := Base) (Const := Const) h W

end Mettapedia.Logic.PLNHigherOrderHOLConsequence
