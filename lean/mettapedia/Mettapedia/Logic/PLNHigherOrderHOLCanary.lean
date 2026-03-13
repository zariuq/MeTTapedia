import Mettapedia.Logic.PLNHigherOrderHOLLinkBridge

namespace Mettapedia.Logic.PLNHigherOrderHOLCanary

open Mettapedia.Logic.HOL
open Mettapedia.Logic.PLNWorldModel
open scoped ENNReal

abbrev FixtureBase := PUnit

abbrev FixtureConst : Ty FixtureBase → Type := fun _ => PEmpty

abbrev FixtureObjTy : Ty FixtureBase := .base PUnit.unit

abbrev FixtureEndTy : Ty FixtureBase := FixtureObjTy ⇒ FixtureObjTy

def fixtureId : Term FixtureConst [] FixtureEndTy :=
  .lam (.var .vz)

def fixtureHigherOrderRefl : ClosedFormula FixtureConst :=
  .all (σ := FixtureEndTy) (.eq (.var .vz) (.var .vz))

def fixtureModel : HenkinModel FixtureBase FixtureConst :=
  HenkinModel.standard
    (Carrier := fun _ => PUnit)
    (constDen := by
      intro τ c
      nomatch c)

theorem canary_hol_higherOrderRefl_provable :
    Mettapedia.Logic.PLNHigherOrderHOLCore.HOLProvable
      (Const := FixtureConst) fixtureHigherOrderRefl :=
  .allI (.eqRefl (.var .vz))

theorem canary_hol_higherOrderRefl_singleton_strength_one :
    WorldModel.queryStrength
        (State := Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState FixtureBase FixtureConst)
        (Query := Mettapedia.Logic.PLNHigherOrderHOLCore.HOLQuery
          (Base := FixtureBase) FixtureConst)
        ({fixtureModel} :
          Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState FixtureBase FixtureConst)
        fixtureHigherOrderRefl = 1 := by
  have hsatisfies :
      HenkinModel.models fixtureModel fixtureHigherOrderRefl :=
    Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvable_models
      (Const := FixtureConst) canary_hol_higherOrderRefl_provable fixtureModel
  exact
    Mettapedia.Logic.PLNWorldModelHOL.queryStrength_singleton_of_satisfies
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureModel fixtureHigherOrderRefl hsatisfies

theorem canary_hol_id_eta_eq :
    Mettapedia.Logic.PLNHigherOrderHOLRules.HOLProvEq
      (Base := FixtureBase) (Const := FixtureConst)
      (.lam (.app (weaken (Base := FixtureBase) (σ := FixtureObjTy) fixtureId) (.var .vz)))
      fixtureId :=
  Mettapedia.Logic.PLNHigherOrderHOLRules.holProvEq_eta
    (Base := FixtureBase) (Const := FixtureConst) fixtureId

theorem canary_hol_top_imp_top_link
    (W : Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState FixtureBase FixtureConst) :
    Mettapedia.Logic.PLNHigherOrderHOLLinkBridge.holdsLinkWM
      (Base := FixtureBase) (Const := FixtureConst) W (.top : ClosedFormula FixtureConst) .top :=
  Mettapedia.Logic.PLNHigherOrderHOLLinkBridge.holdsLinkWM_mono_of_holProvImp
    (Base := FixtureBase) (Const := FixtureConst)
    (φ := (.top : ClosedFormula FixtureConst))
    (ψ := (.top : ClosedFormula FixtureConst))
    (Mettapedia.Logic.PLNHigherOrderHOLCore.holProvImp_refl (.top : ClosedFormula FixtureConst))
    W

theorem canary_hol_top_iff_top_queryEq :
    Mettapedia.Logic.PLNHigherOrderHOLConsequence.HOLWMQueryEq
      (Base := FixtureBase) (Const := FixtureConst)
      (.top : ClosedFormula FixtureConst) .top :=
  Mettapedia.Logic.PLNHigherOrderHOLConsequence.holProvIff_to_WMQueryEq
    (Base := FixtureBase) (Const := FixtureConst)
    (Mettapedia.Logic.PLNHigherOrderHOLRules.holProvIff_refl
      (Base := FixtureBase) (Const := FixtureConst)
      (.top : ClosedFormula FixtureConst))

theorem canary_hol_and_comm_queryEq :
    Mettapedia.Logic.PLNHigherOrderHOLConsequence.HOLWMQueryEq
      (Base := FixtureBase) (Const := FixtureConst)
      (.and (.top : ClosedFormula FixtureConst) .bot)
      (.and (.bot : ClosedFormula FixtureConst) .top) :=
  Mettapedia.Logic.PLNHigherOrderHOLConsequence.holProvIff_to_WMQueryEq
    (Base := FixtureBase) (Const := FixtureConst)
    (Mettapedia.Logic.PLNHigherOrderHOLRules.holProvIff_and_comm
      (Base := FixtureBase) (Const := FixtureConst)
      (.top : ClosedFormula FixtureConst) .bot)

theorem canary_hol_or_comm_queryEq :
    Mettapedia.Logic.PLNHigherOrderHOLConsequence.HOLWMQueryEq
      (Base := FixtureBase) (Const := FixtureConst)
      (.or (.top : ClosedFormula FixtureConst) .bot)
      (.or (.bot : ClosedFormula FixtureConst) .top) :=
  Mettapedia.Logic.PLNHigherOrderHOLConsequence.holProvIff_to_WMQueryEq
    (Base := FixtureBase) (Const := FixtureConst)
    (Mettapedia.Logic.PLNHigherOrderHOLRules.holProvIff_or_comm
      (Base := FixtureBase) (Const := FixtureConst)
      (.top : ClosedFormula FixtureConst) .bot)

theorem canary_hol_imp_mono_link
    (W : Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState FixtureBase FixtureConst) :
    Mettapedia.Logic.PLNHigherOrderHOLLinkBridge.holdsLinkWM
      (Base := FixtureBase) (Const := FixtureConst) W
      (.imp (.top : ClosedFormula FixtureConst) .top)
      (.imp (.bot : ClosedFormula FixtureConst) .top) :=
  Mettapedia.Logic.PLNHigherOrderHOLLinkBridge.holdsLinkWM_mono_of_holProvImp
    (Base := FixtureBase) (Const := FixtureConst)
    (φ := .imp (.top : ClosedFormula FixtureConst) .top)
    (ψ := .imp (.bot : ClosedFormula FixtureConst) .top)
    (Mettapedia.Logic.PLNHigherOrderHOLRules.holProvImp_imp_mono
      (Base := FixtureBase) (Const := FixtureConst)
      (φ := (.top : ClosedFormula FixtureConst))
      (ψ := (.bot : ClosedFormula FixtureConst))
      (χ := (.top : ClosedFormula FixtureConst))
      (δ := (.top : ClosedFormula FixtureConst))
      (Mettapedia.Logic.PLNHigherOrderHOLCore.holProvImp_top
        (.bot : ClosedFormula FixtureConst))
      (Mettapedia.Logic.PLNHigherOrderHOLCore.holProvImp_refl
        (.top : ClosedFormula FixtureConst)))
    W

theorem canary_hol_not_queryEq_top_bot :
    ¬ Mettapedia.Logic.PLNHigherOrderHOLConsequence.HOLWMQueryEq
      (Base := FixtureBase) (Const := FixtureConst)
      (.top : ClosedFormula FixtureConst) (.bot : ClosedFormula FixtureConst) := by
  intro hEq
  have hStrength :=
    WMQueryEq.to_queryStrength
      (State := Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState FixtureBase FixtureConst)
      (Query := Mettapedia.Logic.PLNHigherOrderHOLCore.HOLQuery
        (Base := FixtureBase) FixtureConst)
      hEq ({fixtureModel} :
        Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState FixtureBase FixtureConst)
  have htop :
      WorldModel.queryStrength
          (State := Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState FixtureBase FixtureConst)
          (Query := Mettapedia.Logic.PLNHigherOrderHOLCore.HOLQuery
            (Base := FixtureBase) FixtureConst)
          ({fixtureModel} :
            Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState FixtureBase FixtureConst)
          (.top : ClosedFormula FixtureConst) = 1 :=
    Mettapedia.Logic.PLNWorldModelHOL.queryStrength_singleton_of_satisfies
      (Base := FixtureBase) (Const := FixtureConst) fixtureModel .top
      (HenkinModel.models_top fixtureModel)
  have hbot :
      WorldModel.queryStrength
          (State := Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState FixtureBase FixtureConst)
          (Query := Mettapedia.Logic.PLNHigherOrderHOLCore.HOLQuery
            (Base := FixtureBase) FixtureConst)
          ({fixtureModel} :
            Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState FixtureBase FixtureConst)
          (.bot : ClosedFormula FixtureConst) = 0 :=
    Mettapedia.Logic.PLNWorldModelHOL.queryStrength_singleton_of_not_satisfies
      (Base := FixtureBase) (Const := FixtureConst) fixtureModel .bot
      (HenkinModel.models_bot fixtureModel)
  rw [htop, hbot] at hStrength
  exact zero_ne_one hStrength.symm

theorem canary_hol_not_queryEq_and_top_bot_top :
    ¬ Mettapedia.Logic.PLNHigherOrderHOLConsequence.HOLWMQueryEq
      (Base := FixtureBase) (Const := FixtureConst)
      (.and (.top : ClosedFormula FixtureConst) .bot)
      (.top : ClosedFormula FixtureConst) := by
  intro hEq
  have hStrength :=
    WMQueryEq.to_queryStrength
      (State := Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState FixtureBase FixtureConst)
      (Query := Mettapedia.Logic.PLNHigherOrderHOLCore.HOLQuery
        (Base := FixtureBase) FixtureConst)
      hEq ({fixtureModel} :
        Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState FixtureBase FixtureConst)
  have hAndNot :
      ¬ HenkinModel.models fixtureModel
        (.and (.top : ClosedFormula FixtureConst) .bot) := by
    intro hAnd
    have hpairs := (HenkinModel.models_and fixtureModel).mp hAnd
    exact HenkinModel.models_bot fixtureModel hpairs.2
  have hand :
      WorldModel.queryStrength
          (State := Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState FixtureBase FixtureConst)
          (Query := Mettapedia.Logic.PLNHigherOrderHOLCore.HOLQuery
            (Base := FixtureBase) FixtureConst)
          ({fixtureModel} :
            Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState FixtureBase FixtureConst)
          (.and (.top : ClosedFormula FixtureConst) .bot) = 0 :=
    Mettapedia.Logic.PLNWorldModelHOL.queryStrength_singleton_of_not_satisfies
      (Base := FixtureBase) (Const := FixtureConst) fixtureModel
      (.and (.top : ClosedFormula FixtureConst) .bot) hAndNot
  have htop :
      WorldModel.queryStrength
          (State := Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState FixtureBase FixtureConst)
          (Query := Mettapedia.Logic.PLNHigherOrderHOLCore.HOLQuery
            (Base := FixtureBase) FixtureConst)
          ({fixtureModel} :
            Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState FixtureBase FixtureConst)
          (.top : ClosedFormula FixtureConst) = 1 :=
    Mettapedia.Logic.PLNWorldModelHOL.queryStrength_singleton_of_satisfies
      (Base := FixtureBase) (Const := FixtureConst) fixtureModel .top
      (HenkinModel.models_top fixtureModel)
  rw [hand, htop] at hStrength
  exact zero_ne_one hStrength

theorem canary_hol_not_singletonConsequence_top_bot :
    ¬ ∀ M : HenkinModel FixtureBase FixtureConst,
      WorldModel.queryStrength
          (State := Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState FixtureBase FixtureConst)
          (Query := Mettapedia.Logic.PLNHigherOrderHOLCore.HOLQuery
            (Base := FixtureBase) FixtureConst)
          ({M} : Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState FixtureBase FixtureConst)
          (.top : ClosedFormula FixtureConst) ≤
        WorldModel.queryStrength
          (State := Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState FixtureBase FixtureConst)
          (Query := Mettapedia.Logic.PLNHigherOrderHOLCore.HOLQuery
            (Base := FixtureBase) FixtureConst)
          ({M} : Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState FixtureBase FixtureConst)
          (.bot : ClosedFormula FixtureConst) := by
  intro h
  have htop :
      WorldModel.queryStrength
          (State := Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState FixtureBase FixtureConst)
          (Query := Mettapedia.Logic.PLNHigherOrderHOLCore.HOLQuery
            (Base := FixtureBase) FixtureConst)
          ({fixtureModel} :
            Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState FixtureBase FixtureConst)
          (.top : ClosedFormula FixtureConst) = 1 :=
    Mettapedia.Logic.PLNWorldModelHOL.queryStrength_singleton_of_satisfies
      (Base := FixtureBase) (Const := FixtureConst) fixtureModel .top
      (HenkinModel.models_top fixtureModel)
  have hbot :
      WorldModel.queryStrength
          (State := Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState FixtureBase FixtureConst)
          (Query := Mettapedia.Logic.PLNHigherOrderHOLCore.HOLQuery
            (Base := FixtureBase) FixtureConst)
          ({fixtureModel} :
            Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState FixtureBase FixtureConst)
          (.bot : ClosedFormula FixtureConst) = 0 :=
    Mettapedia.Logic.PLNWorldModelHOL.queryStrength_singleton_of_not_satisfies
      (Base := FixtureBase) (Const := FixtureConst) fixtureModel .bot
      (HenkinModel.models_bot fixtureModel)
  have hcontra := h fixtureModel
  rw [htop, hbot] at hcontra
  exact not_le_of_gt (by simp : (0 : ℝ≥0∞) < 1) hcontra

end Mettapedia.Logic.PLNHigherOrderHOLCanary
