import Mathlib.Probability.UniformOn
import Mettapedia.Logic.PLNHigherOrderHOLLinkBridge
import Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge
import Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge
import Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge
import Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge
import Mettapedia.Logic.PLNHigherOrderHOLProbabilisticBridge
import Mettapedia.Logic.PLNHigherOrderHOLCredalBridge
import Mettapedia.Logic.PLNHigherOrderHOLDeductionBridge

namespace Mettapedia.Logic.PLNHigherOrderHOLCanary

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Probabilistic
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

def fixtureEmptyModel : HenkinModel FixtureBase FixtureConst :=
  HenkinModel.standard
    (Carrier := fun _ => PEmpty)
    (constDen := by
      intro τ c
      nomatch c)

/-- The concrete nonempty fixture model has exactly one admissible object at
the object type. This explicit equivalence lets finite-vocabulary HO-PLN
canaries use the full extensional/intensional inheritance strength layer
without pretending the global HOL predicate syntax is finite. -/
def fixturePredicateObjectEquivPUnit :
    Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.PredicateObject
      (Base := FixtureBase) (Const := FixtureConst) fixtureModel FixtureObjTy ≃
        PUnit where
  toFun x := x.1
  invFun x := ⟨x, trivial⟩
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl

noncomputable instance fixturePredicateObjectFintype :
    Fintype
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.PredicateObject
        (Base := FixtureBase) (Const := FixtureConst) fixtureModel FixtureObjTy) :=
  Fintype.ofEquiv PUnit fixturePredicateObjectEquivPUnit.symm

theorem canary_hol_higherOrderRefl_provable :
    Mettapedia.Logic.PLNHigherOrderHOLCore.HOLProvable
      (Const := FixtureConst) fixtureHigherOrderRefl :=
  .allI (.eqRefl (.var .vz))

theorem canary_hol_higherOrderRefl_singleton_strength_one :
    BinaryWorldModel.queryStrength
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
      BinaryWorldModel.queryStrength
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
      BinaryWorldModel.queryStrength
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
      BinaryWorldModel.queryStrength
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
      BinaryWorldModel.queryStrength
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
      BinaryWorldModel.queryStrength
          (State := Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState FixtureBase FixtureConst)
          (Query := Mettapedia.Logic.PLNHigherOrderHOLCore.HOLQuery
            (Base := FixtureBase) FixtureConst)
          ({M} : Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState FixtureBase FixtureConst)
          (.top : ClosedFormula FixtureConst) ≤
        BinaryWorldModel.queryStrength
          (State := Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState FixtureBase FixtureConst)
          (Query := Mettapedia.Logic.PLNHigherOrderHOLCore.HOLQuery
            (Base := FixtureBase) FixtureConst)
          ({M} : Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState FixtureBase FixtureConst)
          (.bot : ClosedFormula FixtureConst) := by
  intro h
  have htop :
      BinaryWorldModel.queryStrength
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
      BinaryWorldModel.queryStrength
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

abbrev FixturePredTy : Ty FixtureBase := FixtureObjTy ⇒ propTy

def fixturePredTop : ClosedTerm FixtureConst FixturePredTy :=
  .lam .top

def fixturePredBot : ClosedTerm FixtureConst FixturePredTy :=
  .lam .bot

def fixturePredTopBotIff : ClosedFormula FixtureConst :=
  Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateIffFormula
    (Base := FixtureBase) (Const := FixtureConst)
    FixtureObjTy fixturePredTop fixturePredBot

def fixturePredTopBotImp : ClosedFormula FixtureConst :=
  Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateImpFormula
    (Base := FixtureBase) (Const := FixtureConst)
    FixtureObjTy fixturePredTop fixturePredBot

def fixturePredBotTopImp : ClosedFormula FixtureConst :=
  Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateImpFormula
    (Base := FixtureBase) (Const := FixtureConst)
    FixtureObjTy fixturePredBot fixturePredTop

theorem canary_hol_predicateTop_inherits_predicateTop :
    (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateInterpretation
      (Base := FixtureBase) (Const := FixtureConst) fixtureModel FixtureObjTy).Inherits
        fixturePredTop fixturePredTop := by
  exact
    Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.holProvable_predicateImpFormula_implies_inherits
      (Base := FixtureBase) (Const := FixtureConst)
      FixtureObjTy fixturePredTop fixturePredTop
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.holProvable_predicateImpFormula_refl
        (Base := FixtureBase) (Const := FixtureConst) FixtureObjTy fixturePredTop)
      fixtureModel

theorem canary_hol_not_predicateTop_inherits_predicateBot :
    ¬ (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateInterpretation
      (Base := FixtureBase) (Const := FixtureConst) fixtureModel FixtureObjTy).Inherits
        fixturePredTop fixturePredBot := by
  intro hInh
  have hModel :
      HenkinModel.models fixtureModel
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateImpFormula
          (Base := FixtureBase) (Const := FixtureConst)
          FixtureObjTy fixturePredTop fixturePredBot) :=
    (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateInterpretation_inherits_iff_models_predicateImpFormula
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureModel FixtureObjTy fixturePredTop fixturePredBot).1 hInh
  have hPointwise :=
    (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.models_predicateImpFormula_iff
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureModel FixtureObjTy fixturePredTop fixturePredBot).1 hModel
  have htop :
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateHoldsAt
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureModel FixtureObjTy fixturePredTop ⟨PUnit.unit, trivial⟩ := by
    change True
    simp
  have hbot :
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateHoldsAt
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureModel FixtureObjTy fixturePredBot ⟨PUnit.unit, trivial⟩ :=
    hPointwise ⟨PUnit.unit, trivial⟩ htop
  change False at hbot
  exact hbot

theorem canary_hol_predicateTop_mutualInherits_predicateTop :
    Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateMutualInheritsAt
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureModel FixtureObjTy fixturePredTop fixturePredTop := by
  exact
    ⟨canary_hol_predicateTop_inherits_predicateTop,
     canary_hol_predicateTop_inherits_predicateTop⟩

theorem canary_hol_not_predicateTop_mutualInherits_predicateBot :
    ¬ Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateMutualInheritsAt
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureModel FixtureObjTy fixturePredTop fixturePredBot := by
  intro hMutual
  exact canary_hol_not_predicateTop_inherits_predicateBot hMutual.1

theorem canary_hol_empty_predicateTop_mutualInherits_predicateBot :
    Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateMutualInheritsAt
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureEmptyModel FixtureObjTy fixturePredTop fixturePredBot := by
  rw [Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateMutualInheritsAt_iff_models_predicateIffFormula]
  apply (HenkinModel.models_and fixtureEmptyModel).2
  constructor
  · apply
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.models_predicateImpFormula_iff
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureEmptyModel FixtureObjTy fixturePredTop fixturePredBot).2
    intro x _hxTop
    cases x.1
  · apply
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.models_predicateImpFormula_iff
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureEmptyModel FixtureObjTy fixturePredBot fixturePredTop).2
    intro x _hxBot
    cases x.1

theorem canary_hol_predicateForAllTop_models :
    HenkinModel.models fixtureModel
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateForAllFormula
        (Base := FixtureBase) (Const := FixtureConst)
        FixtureObjTy fixturePredTop) := by
  exact
    (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.models_predicateForAllFormula_iff
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureModel FixtureObjTy fixturePredTop).2 <|
      by
        intro x
        change True
        simp

theorem canary_hol_not_predicateForAllBot_models :
    ¬ HenkinModel.models fixtureModel
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateForAllFormula
        (Base := FixtureBase) (Const := FixtureConst)
        FixtureObjTy fixturePredBot) := by
  intro hAll
  have hPoint :=
    (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.models_predicateForAllFormula_iff
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureModel FixtureObjTy fixturePredBot).1 hAll ⟨PUnit.unit, trivial⟩
  change False at hPoint
  exact hPoint

theorem canary_hol_predicateExistsTop_models :
    HenkinModel.models fixtureModel
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateExistsFormula
        (Base := FixtureBase) (Const := FixtureConst)
        FixtureObjTy fixturePredTop) := by
  exact
    (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.models_predicateExistsFormula_iff
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureModel FixtureObjTy fixturePredTop).2
      ⟨⟨PUnit.unit, trivial⟩, by
        change True
        simp⟩

theorem canary_hol_not_predicateExistsBot_models :
    ¬ HenkinModel.models fixtureModel
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateExistsFormula
        (Base := FixtureBase) (Const := FixtureConst)
        FixtureObjTy fixturePredBot) := by
  intro hExists
  rcases
    (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.models_predicateExistsFormula_iff
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureModel FixtureObjTy fixturePredBot).1 hExists with
    ⟨x, hx⟩
  change False at hx
  exact hx

theorem canary_hol_predicateSimilarityTopTop_strength_one :
    Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateSimilarityStrength
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureModel FixtureObjTy fixturePredTop fixturePredTop = 1 :=
  Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateSimilarityStrength_eq_one_of_mutualInherits
    (Base := FixtureBase) (Const := FixtureConst)
    fixtureModel FixtureObjTy fixturePredTop fixturePredTop
    canary_hol_predicateTop_mutualInherits_predicateTop

theorem canary_hol_predicateSimilarityTopBot_strength_zero :
    Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateSimilarityStrength
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureModel FixtureObjTy fixturePredTop fixturePredBot = 0 :=
  Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateSimilarityStrength_eq_zero_of_not_inherits_left
    (Base := FixtureBase) (Const := FixtureConst)
    fixtureModel FixtureObjTy fixturePredTop fixturePredBot
    canary_hol_not_predicateTop_inherits_predicateBot

/-! ## Non-counting fuzzy-capacity canaries -/

abbrev FixtureSingletonPredObj :=
  Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.PredicateObject
    (Base := FixtureBase) (Const := FixtureConst) fixtureModel FixtureObjTy

def fixtureSingletonObj : FixtureSingletonPredObj :=
  ⟨PUnit.unit, trivial⟩

noncomputable instance fixtureSingletonPredicateObjectMeasurableSpace :
    MeasurableSpace FixtureSingletonPredObj :=
  ⊤

noncomputable def fixtureSharpFourFifthsParams :
    Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierParams where
  ε := 0
  LPC := 0
  UPC := 1
  PCL := 4 / 5
  hε := by norm_num
  hLPC := by norm_num
  hUPC := by norm_num
  hPCL := by norm_num
  hLPC_le_UPC := by norm_num

noncomputable def fixtureSingletonFourFifthsCapacity :
    Mettapedia.Logic.PLNFirstOrder.FuzzyCapacity FixtureSingletonPredObj where
  cap := by
    classical
    intro A
    exact if fixtureSingletonObj ∈ A then ⟨(4 / 5 : ℝ), by norm_num⟩ else 0
  cap_empty := by
    classical
    simp [fixtureSingletonObj]
  mono := by
    classical
    intro A B hAB
    by_cases hA : fixtureSingletonObj ∈ A
    · have hB : fixtureSingletonObj ∈ B := hAB hA
      simp [hA, hB]
    · by_cases hB : fixtureSingletonObj ∈ B
      · simp [hA, hB]
      · simp [hA, hB]

theorem canary_hol_singleton_nearOneCut_top_eq_univ :
    Mettapedia.Logic.PLNFirstOrder.nearOneCutInf
        fixtureSharpFourFifthsParams.toInf
        (Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfileInf
          (Base := FixtureBase) (Const := FixtureConst)
          fixtureModel FixtureObjTy fixturePredTop) =
      Set.univ := by
  ext x
  have hxTop :
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateHoldsAt
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureModel FixtureObjTy fixturePredTop x := by
    change True
    simp
  have hxTop' :
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateHoldsAt
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureModel FixtureObjTy (.lam .top : ClosedTerm FixtureConst FixturePredTy) x := by
    simpa [fixturePredTop] using hxTop
  simp [Mettapedia.Logic.PLNFirstOrder.nearOneCutInf,
    Mettapedia.Logic.PLNFirstOrder.nearOneInf,
    fixtureSharpFourFifthsParams,
    Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfileInf,
    Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfile,
    hxTop',
    fixturePredTop]
  norm_num [fixtureSharpFourFifthsParams,
    Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierParams.toInf]

theorem canary_hol_singleton_nearOneCut_bot_eq_empty :
    Mettapedia.Logic.PLNFirstOrder.nearOneCutInf
        fixtureSharpFourFifthsParams.toInf
        (Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfileInf
          (Base := FixtureBase) (Const := FixtureConst)
          fixtureModel FixtureObjTy fixturePredBot) =
      ∅ := by
  ext x
  have hxBot :
      ¬ Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateHoldsAt
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureModel FixtureObjTy fixturePredBot x := by
    change ¬ False
    simp
  have hxBot' :
      ¬ Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateHoldsAt
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureModel FixtureObjTy (.lam .bot : ClosedTerm FixtureConst FixturePredTy) x := by
    simpa [fixturePredBot] using hxBot
  simp [Mettapedia.Logic.PLNFirstOrder.nearOneCutInf,
    Mettapedia.Logic.PLNFirstOrder.nearOneInf,
    fixtureSharpFourFifthsParams,
    Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfileInf,
    Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfile,
    hxBot',
    fixturePredBot]
  norm_num [fixtureSharpFourFifthsParams,
    Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierParams.toInf]

theorem canary_hol_singleton_weightedNearOne_top_eq_four_fifths :
    ((Mettapedia.Logic.PLNFirstOrder.nearOneMassInf
        fixtureSharpFourFifthsParams.toInf
        fixtureSingletonFourFifthsCapacity
        (Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfileInf
          (Base := FixtureBase) (Const := FixtureConst)
          fixtureModel FixtureObjTy fixturePredTop)) : ℝ) = 4 / 5 := by
  unfold Mettapedia.Logic.PLNFirstOrder.nearOneMassInf
  rw [canary_hol_singleton_nearOneCut_top_eq_univ]
  simp [fixtureSingletonFourFifthsCapacity, fixtureSingletonObj]

theorem canary_hol_singleton_weightedNearOne_bot_eq_zero :
    ((Mettapedia.Logic.PLNFirstOrder.nearOneMassInf
        fixtureSharpFourFifthsParams.toInf
        fixtureSingletonFourFifthsCapacity
        (Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfileInf
          (Base := FixtureBase) (Const := FixtureConst)
          fixtureModel FixtureObjTy fixturePredBot)) : ℝ) = 0 := by
  unfold Mettapedia.Logic.PLNFirstOrder.nearOneMassInf
  rw [canary_hol_singleton_nearOneCut_bot_eq_empty]
  simp [fixtureSingletonFourFifthsCapacity, fixtureSingletonObj]

theorem canary_hol_singleton_weightedQFMForAll_top :
    Mettapedia.Logic.PLNFirstOrder.fuzzyForAllHoldsInf
        fixtureSharpFourFifthsParams.toInf
        fixtureSingletonFourFifthsCapacity
        (Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfileInf
          (Base := FixtureBase) (Const := FixtureConst)
          fixtureModel FixtureObjTy fixturePredTop) := by
  unfold Mettapedia.Logic.PLNFirstOrder.fuzzyForAllHoldsInf
  rw [canary_hol_singleton_weightedNearOne_top_eq_four_fifths]
  norm_num [fixtureSharpFourFifthsParams,
    Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierParams.toInf]

theorem canary_hol_singleton_not_weightedQFMForAll_bot :
    ¬ Mettapedia.Logic.PLNFirstOrder.fuzzyForAllHoldsInf
        fixtureSharpFourFifthsParams.toInf
        fixtureSingletonFourFifthsCapacity
        (Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfileInf
          (Base := FixtureBase) (Const := FixtureConst)
          fixtureModel FixtureObjTy fixturePredBot) := by
  intro hBot
  unfold Mettapedia.Logic.PLNFirstOrder.fuzzyForAllHoldsInf at hBot
  rw [canary_hol_singleton_weightedNearOne_bot_eq_zero] at hBot
  norm_num [fixtureSharpFourFifthsParams,
    Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierParams.toInf] at hBot

/-! ## Two-object weighted-capacity canaries -/

inductive FixtureTwoConst : Ty FixtureBase → Type
  | leftObj : FixtureTwoConst FixtureObjTy
  | rightObj : FixtureTwoConst FixtureObjTy

def fixtureTwoConstDen :
    {τ : Ty FixtureBase} → FixtureTwoConst τ →
      Ty.denote (fun _ : FixtureBase => ULift Bool) τ
  | _, .leftObj => ULift.up false
  | _, .rightObj => ULift.up true

def fixtureTwoModel : HenkinModel FixtureBase FixtureTwoConst :=
  HenkinModel.standard
    (Carrier := fun _ => ULift Bool)
    (constDen := fixtureTwoConstDen)

@[simp] theorem fixtureTwoModel_constDen_left :
    fixtureTwoModel.constDen FixtureTwoConst.leftObj = ULift.up false := rfl

@[simp] theorem fixtureTwoModel_constDen_right :
    fixtureTwoModel.constDen FixtureTwoConst.rightObj = ULift.up true := rfl

def fixtureTwoPredLeft : ClosedTerm FixtureTwoConst FixturePredTy :=
  .lam (.eq (.var .vz) (.const FixtureTwoConst.leftObj))

def fixtureTwoPredRight : ClosedTerm FixtureTwoConst FixturePredTy :=
  .lam (.eq (.var .vz) (.const FixtureTwoConst.rightObj))

def fixtureTwoPredTop : ClosedTerm FixtureTwoConst FixturePredTy :=
  .lam .top

def fixtureTwoPredBot : ClosedTerm FixtureTwoConst FixturePredTy :=
  .lam .bot

abbrev FixtureTwoPredObj :=
  Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.PredicateObject
    (Base := FixtureBase) (Const := FixtureTwoConst) fixtureTwoModel FixtureObjTy

def fixtureTwoLeftObj : FixtureTwoPredObj :=
  ⟨ULift.up false, trivial⟩

def fixtureTwoRightObj : FixtureTwoPredObj :=
  ⟨ULift.up true, trivial⟩

theorem fixtureTwoLeftObj_ne_rightObj :
    fixtureTwoLeftObj ≠ fixtureTwoRightObj := by
  intro h
  have hdown := congrArg (fun x : FixtureTwoPredObj => x.1.down) h
  simp [fixtureTwoLeftObj, fixtureTwoRightObj] at hdown

def fixtureTwoPredicateObjectEquivBool : FixtureTwoPredObj ≃ Bool where
  toFun x := x.1.down
  invFun x := ⟨ULift.up x, trivial⟩
  left_inv := by
    intro x
    cases x with
    | mk x hx =>
        cases x
        rfl
  right_inv := by
    intro x
    rfl

noncomputable instance fixtureTwoPredicateObjectFintype :
    Fintype FixtureTwoPredObj :=
  Fintype.ofEquiv Bool fixtureTwoPredicateObjectEquivBool.symm

noncomputable instance fixtureTwoPredicateObjectMeasurableSpace :
    MeasurableSpace FixtureTwoPredObj :=
  ⊤

noncomputable def fixtureTwoWeightedQFMParams :
    Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierParams where
  ε := 0
  LPC := 0
  UPC := 1
  PCL := 3 / 4
  hε := by norm_num
  hLPC := by norm_num
  hUPC := by norm_num
  hPCL := by norm_num
  hLPC_le_UPC := by norm_num

noncomputable def fixtureTwoWeightedCapacity :
    Mettapedia.Logic.PLNFirstOrder.FuzzyCapacity FixtureTwoPredObj where
  cap := by
    classical
    intro A
    exact
      if fixtureTwoLeftObj ∈ A ∧ fixtureTwoRightObj ∈ A then
        1
      else if fixtureTwoLeftObj ∈ A then
        ⟨(4 / 5 : ℝ), by norm_num⟩
      else if fixtureTwoRightObj ∈ A then
        ⟨(1 / 5 : ℝ), by norm_num⟩
      else
        0
  cap_empty := by
    classical
    simp [fixtureTwoLeftObj, fixtureTwoRightObj]
  mono := by
    classical
    intro A B hAB
    by_cases hAl : fixtureTwoLeftObj ∈ A
    · have hBl : fixtureTwoLeftObj ∈ B := hAB hAl
      by_cases hAr : fixtureTwoRightObj ∈ A
      · have hBr : fixtureTwoRightObj ∈ B := hAB hAr
        simp [hAl, hAr, hBl, hBr]
      · by_cases hBr : fixtureTwoRightObj ∈ B
        · simp [hAl, hAr, hBl, hBr]
          exact (show (4 / 5 : ℝ) ≤ 1 by norm_num)
        · simp [hAl, hAr, hBl, hBr]
    · by_cases hAr : fixtureTwoRightObj ∈ A
      · have hBr : fixtureTwoRightObj ∈ B := hAB hAr
        by_cases hBl : fixtureTwoLeftObj ∈ B
        · simp [hAl, hAr, hBl, hBr]
          apply Subtype.mk_le_mk.mpr
          norm_num
        · simp [hAl, hAr, hBl, hBr]
      · by_cases hBl : fixtureTwoLeftObj ∈ B
        · by_cases hBr : fixtureTwoRightObj ∈ B
          · simp [hAl, hAr, hBl, hBr]
          · simp [hAl, hAr, hBl, hBr]
        · by_cases hBr : fixtureTwoRightObj ∈ B
          · simp [hAl, hAr, hBl, hBr]
          · simp [hAl, hAr, hBl, hBr]

theorem canary_hol_two_weightedCapacity_normalized :
    Mettapedia.Logic.PLNFirstOrder.FuzzyCapacity.IsNormalized
      fixtureTwoWeightedCapacity := by
  classical
  unfold Mettapedia.Logic.PLNFirstOrder.FuzzyCapacity.IsNormalized
  simp [fixtureTwoWeightedCapacity, fixtureTwoLeftObj, fixtureTwoRightObj]

theorem canary_hol_two_predLeft_holds_iff (x : FixtureTwoPredObj) :
    Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateHoldsAt
      (Base := FixtureBase) (Const := FixtureTwoConst)
      fixtureTwoModel FixtureObjTy fixtureTwoPredLeft x ↔
        x = fixtureTwoLeftObj := by
  cases x with
  | mk x hx =>
      cases x with
      | up b =>
          cases b <;>
            simp [Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateHoldsAt,
              Mettapedia.Logic.HOL.weaken, Mettapedia.Logic.HOL.rename,
              Mettapedia.Logic.HOL.Rename.lift,
              Mettapedia.Logic.HOL.PreModel.denote,
              Mettapedia.Logic.HOL.PreModel.extend,
              Mettapedia.Logic.HOL.PreModel.Eqv,
              fixtureTwoModel_constDen_left,
              fixtureTwoPredLeft, fixtureTwoLeftObj]

theorem canary_hol_two_predRight_holds_iff (x : FixtureTwoPredObj) :
    Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateHoldsAt
      (Base := FixtureBase) (Const := FixtureTwoConst)
      fixtureTwoModel FixtureObjTy fixtureTwoPredRight x ↔
        x = fixtureTwoRightObj := by
  cases x with
  | mk x hx =>
      cases x with
      | up b =>
          cases b <;>
            simp [Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateHoldsAt,
              Mettapedia.Logic.HOL.weaken, Mettapedia.Logic.HOL.rename,
              Mettapedia.Logic.HOL.Rename.lift,
              Mettapedia.Logic.HOL.PreModel.denote,
              Mettapedia.Logic.HOL.PreModel.extend,
              Mettapedia.Logic.HOL.PreModel.Eqv,
              fixtureTwoModel_constDen_right,
              fixtureTwoPredRight, fixtureTwoRightObj]

theorem canary_hol_two_predTop_holds (x : FixtureTwoPredObj) :
    Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateHoldsAt
      (Base := FixtureBase) (Const := FixtureTwoConst)
      fixtureTwoModel FixtureObjTy fixtureTwoPredTop x := by
  cases x with
  | mk x hx =>
      cases x with
      | up b =>
          cases b <;>
            simp [Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateHoldsAt,
              Mettapedia.Logic.HOL.weaken, Mettapedia.Logic.HOL.rename,
              Mettapedia.Logic.HOL.PreModel.denote,
              fixtureTwoModel, fixtureTwoPredTop]

theorem canary_hol_two_nearOneCut_left_eq_singleton :
    Mettapedia.Logic.PLNFirstOrder.nearOneCutInf
        fixtureTwoWeightedQFMParams.toInf
        (Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfileInf
          (Base := FixtureBase) (Const := FixtureTwoConst)
          fixtureTwoModel FixtureObjTy fixtureTwoPredLeft) =
      {fixtureTwoLeftObj} := by
  ext x
  by_cases hx : x = fixtureTwoLeftObj
  · subst x
    have hholds :
        Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateHoldsAt
          (Base := FixtureBase) (Const := FixtureTwoConst)
          fixtureTwoModel FixtureObjTy fixtureTwoPredLeft fixtureTwoLeftObj :=
        (canary_hol_two_predLeft_holds_iff fixtureTwoLeftObj).2 rfl
    simp [Mettapedia.Logic.PLNFirstOrder.nearOneCutInf,
      Mettapedia.Logic.PLNFirstOrder.nearOneInf,
      fixtureTwoWeightedQFMParams,
      Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfileInf,
      Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfile]
    rw [if_pos hholds]
    norm_num [fixtureTwoWeightedQFMParams,
      Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierParams.toInf]
  · have hholds :
        ¬ Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateHoldsAt
          (Base := FixtureBase) (Const := FixtureTwoConst)
          fixtureTwoModel FixtureObjTy fixtureTwoPredLeft x := by
        intro h
        exact hx ((canary_hol_two_predLeft_holds_iff x).1 h)
    simp [Mettapedia.Logic.PLNFirstOrder.nearOneCutInf,
      Mettapedia.Logic.PLNFirstOrder.nearOneInf,
      fixtureTwoWeightedQFMParams,
      Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfileInf,
      Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfile,
      hholds, hx]
    norm_num [fixtureTwoWeightedQFMParams,
      Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierParams.toInf]

theorem canary_hol_two_nearOneCut_right_eq_singleton :
    Mettapedia.Logic.PLNFirstOrder.nearOneCutInf
        fixtureTwoWeightedQFMParams.toInf
        (Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfileInf
          (Base := FixtureBase) (Const := FixtureTwoConst)
          fixtureTwoModel FixtureObjTy fixtureTwoPredRight) =
      {fixtureTwoRightObj} := by
  ext x
  by_cases hx : x = fixtureTwoRightObj
  · subst x
    have hholds :
        Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateHoldsAt
          (Base := FixtureBase) (Const := FixtureTwoConst)
          fixtureTwoModel FixtureObjTy fixtureTwoPredRight fixtureTwoRightObj :=
        (canary_hol_two_predRight_holds_iff fixtureTwoRightObj).2 rfl
    simp [Mettapedia.Logic.PLNFirstOrder.nearOneCutInf,
      Mettapedia.Logic.PLNFirstOrder.nearOneInf,
      fixtureTwoWeightedQFMParams,
      Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfileInf,
      Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfile]
    rw [if_pos hholds]
    norm_num [fixtureTwoWeightedQFMParams,
      Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierParams.toInf]
  · have hholds :
        ¬ Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateHoldsAt
          (Base := FixtureBase) (Const := FixtureTwoConst)
          fixtureTwoModel FixtureObjTy fixtureTwoPredRight x := by
        intro h
        exact hx ((canary_hol_two_predRight_holds_iff x).1 h)
    simp [Mettapedia.Logic.PLNFirstOrder.nearOneCutInf,
      Mettapedia.Logic.PLNFirstOrder.nearOneInf,
      fixtureTwoWeightedQFMParams,
      Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfileInf,
      Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfile,
      hholds, hx]
    norm_num [fixtureTwoWeightedQFMParams,
      Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierParams.toInf]

theorem canary_hol_two_nearOneCut_top_eq_univ :
    Mettapedia.Logic.PLNFirstOrder.nearOneCutInf
        fixtureTwoWeightedQFMParams.toInf
        (Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfileInf
          (Base := FixtureBase) (Const := FixtureTwoConst)
          fixtureTwoModel FixtureObjTy fixtureTwoPredTop) =
      Set.univ := by
  ext x
  have hholds :
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateHoldsAt
        (Base := FixtureBase) (Const := FixtureTwoConst)
        fixtureTwoModel FixtureObjTy fixtureTwoPredTop x :=
    canary_hol_two_predTop_holds x
  simp [Mettapedia.Logic.PLNFirstOrder.nearOneCutInf,
    Mettapedia.Logic.PLNFirstOrder.nearOneInf,
    fixtureTwoWeightedQFMParams,
    Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfileInf,
    Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfile,
    hholds]
  norm_num [fixtureTwoWeightedQFMParams,
    Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierParams.toInf]

theorem canary_hol_two_nearOneMass_left_eq_four_fifths :
    ((Mettapedia.Logic.PLNFirstOrder.nearOneMassInf
        fixtureTwoWeightedQFMParams.toInf
        fixtureTwoWeightedCapacity
        (Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfileInf
          (Base := FixtureBase) (Const := FixtureTwoConst)
          fixtureTwoModel FixtureObjTy fixtureTwoPredLeft)) : ℝ) = 4 / 5 := by
  unfold Mettapedia.Logic.PLNFirstOrder.nearOneMassInf
  rw [canary_hol_two_nearOneCut_left_eq_singleton]
  have hRightNotLeft :
      fixtureTwoRightObj ∉ ({fixtureTwoLeftObj} : Set FixtureTwoPredObj) := by
    intro h
    exact fixtureTwoLeftObj_ne_rightObj (by simpa using h.symm)
  have hNotBoth :
      ¬ (fixtureTwoLeftObj ∈ ({fixtureTwoLeftObj} : Set FixtureTwoPredObj) ∧
        fixtureTwoRightObj ∈ ({fixtureTwoLeftObj} : Set FixtureTwoPredObj)) := by
    intro h
    exact hRightNotLeft h.2
  simp [fixtureTwoWeightedCapacity]
  rw [if_neg hNotBoth]

theorem canary_hol_two_nearOneMass_right_eq_one_fifth :
    ((Mettapedia.Logic.PLNFirstOrder.nearOneMassInf
        fixtureTwoWeightedQFMParams.toInf
        fixtureTwoWeightedCapacity
        (Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfileInf
          (Base := FixtureBase) (Const := FixtureTwoConst)
          fixtureTwoModel FixtureObjTy fixtureTwoPredRight)) : ℝ) = 1 / 5 := by
  unfold Mettapedia.Logic.PLNFirstOrder.nearOneMassInf
  rw [canary_hol_two_nearOneCut_right_eq_singleton]
  have hLeftNotRight :
      fixtureTwoLeftObj ∉ ({fixtureTwoRightObj} : Set FixtureTwoPredObj) := by
    intro h
    exact fixtureTwoLeftObj_ne_rightObj (by simpa using h)
  have hNotBoth :
      ¬ (fixtureTwoLeftObj ∈ ({fixtureTwoRightObj} : Set FixtureTwoPredObj) ∧
        fixtureTwoRightObj ∈ ({fixtureTwoRightObj} : Set FixtureTwoPredObj)) := by
    intro h
    exact hLeftNotRight h.1
  simp [fixtureTwoWeightedCapacity]
  rw [if_neg hNotBoth, if_neg hLeftNotRight]

theorem canary_hol_two_nearOneMass_top_eq_one :
    ((Mettapedia.Logic.PLNFirstOrder.nearOneMassInf
        fixtureTwoWeightedQFMParams.toInf
        fixtureTwoWeightedCapacity
        (Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfileInf
          (Base := FixtureBase) (Const := FixtureTwoConst)
          fixtureTwoModel FixtureObjTy fixtureTwoPredTop)) : ℝ) = 1 := by
  unfold Mettapedia.Logic.PLNFirstOrder.nearOneMassInf
  rw [canary_hol_two_nearOneCut_top_eq_univ]
  simp [fixtureTwoWeightedCapacity, fixtureTwoLeftObj, fixtureTwoRightObj]

theorem canary_hol_two_weightedQFMForAll_left :
    Mettapedia.Logic.PLNFirstOrder.fuzzyForAllHoldsInf
        fixtureTwoWeightedQFMParams.toInf
        fixtureTwoWeightedCapacity
        (Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfileInf
          (Base := FixtureBase) (Const := FixtureTwoConst)
          fixtureTwoModel FixtureObjTy fixtureTwoPredLeft) := by
  unfold Mettapedia.Logic.PLNFirstOrder.fuzzyForAllHoldsInf
  rw [canary_hol_two_nearOneMass_left_eq_four_fifths]
  norm_num [fixtureTwoWeightedQFMParams,
    Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierParams.toInf]

theorem canary_hol_two_not_weightedQFMForAll_right :
    ¬ Mettapedia.Logic.PLNFirstOrder.fuzzyForAllHoldsInf
        fixtureTwoWeightedQFMParams.toInf
        fixtureTwoWeightedCapacity
        (Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfileInf
          (Base := FixtureBase) (Const := FixtureTwoConst)
          fixtureTwoModel FixtureObjTy fixtureTwoPredRight) := by
  intro hRight
  unfold Mettapedia.Logic.PLNFirstOrder.fuzzyForAllHoldsInf at hRight
  rw [canary_hol_two_nearOneMass_right_eq_one_fifth] at hRight
  norm_num [fixtureTwoWeightedQFMParams,
    Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierParams.toInf] at hRight

theorem canary_hol_two_weightedQFM_distinguishes_singleton_extensions :
    ((Mettapedia.Logic.PLNFirstOrder.nearOneMassInf
        fixtureTwoWeightedQFMParams.toInf
        fixtureTwoWeightedCapacity
        (Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfileInf
          (Base := FixtureBase) (Const := FixtureTwoConst)
          fixtureTwoModel FixtureObjTy fixtureTwoPredLeft)) : ℝ) ≠
      ((Mettapedia.Logic.PLNFirstOrder.nearOneMassInf
        fixtureTwoWeightedQFMParams.toInf
        fixtureTwoWeightedCapacity
        (Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge.predicateCrispProfileInf
          (Base := FixtureBase) (Const := FixtureTwoConst)
          fixtureTwoModel FixtureObjTy fixtureTwoPredRight)) : ℝ) := by
  rw [canary_hol_two_nearOneMass_left_eq_four_fifths,
    canary_hol_two_nearOneMass_right_eq_one_fifth]
  norm_num

theorem canary_hol_two_weightedQFMTwoInh2Sim_value :
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalQFMCapacityFiniteRuleValue
      (endpoint :=
        fun _ : Unit => fun j : Fin 2 =>
          if j = 0 then (4 / 5 : ℝ) else 1 / 5)
      (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.binaryRuleAsFinite2
        Mettapedia.Logic.PLNInferenceRules.twoInh2Sim)
      () = 4 / 21 := by
  norm_num [
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalQFMCapacityFiniteRuleValue,
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.binaryRuleAsFinite2,
    Mettapedia.Logic.PLNInferenceRules.twoInh2Sim]

theorem canary_hol_two_weightedQFMModusPonens_value :
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalQFMCapacityFiniteRuleValue
      (endpoint :=
        fun _ : Unit => fun j : Fin 2 =>
          if j = 0 then (4 / 5 : ℝ) else 1 / 5)
      (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.modusPonensAsFinite2
        (1 / 10 : ℝ))
      () = 6 / 25 := by
  norm_num [
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalQFMCapacityFiniteRuleValue,
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.modusPonensAsFinite2,
    Mettapedia.Logic.PLNInferenceRules.modusPonens]

theorem canary_hol_two_weightedQFMSymmetricModusPonens_value :
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalQFMCapacityFiniteRuleValue
      (endpoint :=
        fun _ : Unit => fun j : Fin 2 =>
          if j = 0 then (4 / 5 : ℝ) else 1 / 5)
      (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.symmetricModusPonensAsFinite2
        (1 / 10 : ℝ))
      () = 38 / 125 := by
  norm_num [
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalQFMCapacityFiniteRuleValue,
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.symmetricModusPonensAsFinite2,
    Mettapedia.Logic.PLNInferenceRules.symmetricModusPonens]

theorem canary_hol_two_weightedQFMSim2Inh_value :
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalQFMCapacityFiniteRuleValue
      (endpoint :=
        fun _ : Unit => fun j : Fin 3 =>
          if j = 0 then (4 / 5 : ℝ) else
            if j = 1 then 4 / 5 else 1 / 5)
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.sim2inhAsFinite3
      () = 5 / 9 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  norm_num [
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalQFMCapacityFiniteRuleValue,
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.sim2inhAsFinite3,
    Mettapedia.Logic.PLNInferenceRules.sim2inh, h20, h21]

theorem canary_hol_two_weightedQFMSim2Inh_mixed_endpoint_order :
    Mettapedia.Logic.PLNInferenceRules.sim2inh
        (2 / 5 : ℝ) (4 / 5 : ℝ) (1 / 5 : ℝ) ≤
      Mettapedia.Logic.PLNInferenceRules.sim2inh
        (4 / 5 : ℝ) (3 / 5 : ℝ) (2 / 5 : ℝ) := by
  norm_num [Mettapedia.Logic.PLNInferenceRules.sim2inh]

theorem canary_hol_two_weightedQFMFiniteRule_singleton_multiJoin_width_zero :
    let I :=
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalQFMCapacityFiniteRuleInterval
        (endpoint :=
          fun _ : Unit => fun j : Fin 2 =>
            if j = 0 then (4 / 5 : ℝ) else 1 / 5)
        (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.binaryRuleAsFinite2
          Mettapedia.Logic.PLNInferenceRules.twoInh2Sim)
        (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.binaryRuleAsFinite2_monotone_on_unit
          Mettapedia.Logic.PLNInferenceRules.twoInh2Sim
          Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.twoInh2Sim_binaryRuleMonotoneOnUnit)
        (by
          intro k j
          fin_cases j <;> norm_num)
        (by
          intro k j
          fin_cases j <;> norm_num)
    I.width = 0 := by
  dsimp
  rw [
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalQFMCapacityFiniteRuleInterval_eq_const_of_subsingleton
      (endpoint :=
        fun _ : Unit => fun j : Fin 2 =>
          if j = 0 then (4 / 5 : ℝ) else 1 / 5)
      ()
      (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.binaryRuleAsFinite2
        Mettapedia.Logic.PLNInferenceRules.twoInh2Sim)
      (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.binaryRuleAsFinite2_monotone_on_unit
        Mettapedia.Logic.PLNInferenceRules.twoInh2Sim
        Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.twoInh2Sim_binaryRuleMonotoneOnUnit)
      (by
        intro k j
        fin_cases j <;> norm_num)
      (by
        intro k j
        fin_cases j <;> norm_num)]
  simp [
    Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.Interval.width,
    Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.constInterval]

theorem canary_hol_two_weightedQFMProductMultiJoin_singleton_width_zero :
    let I :=
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalQFMCapacityProductMultiJoinInterval
        (endpoint :=
          fun _ : Unit => fun j : Fin 2 =>
            if j = 0 then (4 / 5 : ℝ) else 1 / 5)
        (by
          intro k j
          fin_cases j <;> norm_num)
        (by
          intro k j
          fin_cases j <;> norm_num)
    I.width = 0 := by
  dsimp [
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalQFMCapacityProductMultiJoinInterval]
  rw [
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalQFMCapacityFiniteRuleInterval_eq_const_of_subsingleton
      (endpoint :=
        fun _ : Unit => fun j : Fin 2 =>
          if j = 0 then (4 / 5 : ℝ) else 1 / 5)
      ()
      (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.productMultiJoin)
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.productMultiJoin_monotone_on_unit
      (by
        intro k j
        fin_cases j <;> norm_num)
      (by
        intro k j
        fin_cases j <;> norm_num)]
  simp [
    Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.Interval.width,
    Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.constInterval]

theorem canary_hol_two_weightedQFMNoisyOrMultiJoin_value :
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalQFMCapacityFiniteRuleValue
      (endpoint :=
        fun _ : Unit => fun j : Fin 2 =>
          if j = 0 then (4 / 5 : ℝ) else 1 / 5)
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.noisyOrMultiJoin
      () = 21 / 25 := by
  norm_num [
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalQFMCapacityFiniteRuleValue,
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.noisyOrMultiJoin]

theorem canary_hol_two_weightedQFMNoisyOrMultiJoin_singleton_width_zero :
    let I :=
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalQFMCapacityNoisyOrMultiJoinInterval
        (endpoint :=
          fun _ : Unit => fun j : Fin 2 =>
            if j = 0 then (4 / 5 : ℝ) else 1 / 5)
        (by
          intro k j
          fin_cases j <;> norm_num)
        (by
          intro k j
          fin_cases j <;> norm_num)
    I.width = 0 := by
  dsimp [
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalQFMCapacityNoisyOrMultiJoinInterval]
  rw [
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalQFMCapacityFiniteRuleInterval_eq_const_of_subsingleton
      (endpoint :=
        fun _ : Unit => fun j : Fin 2 =>
          if j = 0 then (4 / 5 : ℝ) else 1 / 5)
      ()
      (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.noisyOrMultiJoin)
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.noisyOrMultiJoin_monotone_on_unit
      (by
        intro k j
        fin_cases j <;> norm_num)
      (by
        intro k j
        fin_cases j <;> norm_num)]
  simp [
    Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.Interval.width,
    Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.constInterval]

theorem canary_hol_two_weightedQFMNoisyOr_complement_product_sum_one :
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.productMultiJoin
        (fun j : Fin 2 =>
          1 - (if j = 0 then (4 / 5 : ℝ) else 1 / 5)) +
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.noisyOrMultiJoin
        (fun j : Fin 2 => if j = 0 then (4 / 5 : ℝ) else 1 / 5) =
        1 := by
  simpa using
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.productMultiJoin_compl_add_noisyOrMultiJoin
      (fun j : Fin 2 => if j = 0 then (4 / 5 : ℝ) else 1 / 5)

theorem canary_hol_two_weightedQFMNoisyOr_complement_dual :
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.noisyOrMultiJoin
        (fun j : Fin 2 =>
          1 - (if j = 0 then (4 / 5 : ℝ) else 1 / 5)) =
      1 -
        Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.productMultiJoin
          (fun j : Fin 2 => if j = 0 then (4 / 5 : ℝ) else 1 / 5) := by
  simpa using
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.noisyOrMultiJoin_compl_eq_one_sub_productMultiJoin
      (fun j : Fin 2 => if j = 0 then (4 / 5 : ℝ) else 1 / 5)

theorem canary_hol_two_weightedQFMNoisyOr_capacity_value_dual :
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalQFMCapacityFiniteRuleValue
      (endpoint :=
        fun _ : Unit => fun j : Fin 2 =>
          if j = 0 then (4 / 5 : ℝ) else 1 / 5)
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.noisyOrMultiJoin
      () =
      1 -
        Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.productMultiJoin
          (fun j : Fin 2 =>
            1 - (if j = 0 then (4 / 5 : ℝ) else 1 / 5)) := by
  simpa using
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalQFMCapacityFiniteRuleValue_noisyOr_eq_one_sub_productMultiJoin_compl
      (endpoint :=
        fun _ : Unit => fun j : Fin 2 =>
          if j = 0 then (4 / 5 : ℝ) else 1 / 5)
      ()

theorem canary_hol_two_weightedQFMNoisyOr_hull_containment :
    (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalQFMCapacityNoisyOrMultiJoinInterval
      (endpoint :=
        fun _ : Unit => fun j : Fin 2 =>
          if j = 0 then (4 / 5 : ℝ) else 1 / 5)
      (by
        intro k j
        fin_cases j <;> norm_num)
      (by
        intro k j
        fin_cases j <;> norm_num)).containedIn
      (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalQFMCapacityNoisyOrMultiJoinHull
        (endpoint :=
          fun _ : Unit => fun j : Fin 2 =>
            if j = 0 then (4 / 5 : ℝ) else 1 / 5)
        (by
          intro k j
          fin_cases j <;> norm_num)
        (by
          intro k j
          fin_cases j <;> norm_num)) := by
  exact
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalQFMCapacityNoisyOrMultiJoinInterval_containedIn_hull
      (endpoint :=
        fun _ : Unit => fun j : Fin 2 =>
          if j = 0 then (4 / 5 : ℝ) else 1 / 5)
      (by
        intro k j
        fin_cases j <;> norm_num)
      (by
        intro k j
        fin_cases j <;> norm_num)

theorem canary_hol_two_weightedQFMNoisyOr_hull_dual_lower :
    (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalQFMCapacityNoisyOrMultiJoinHull
      (endpoint :=
        fun _ : Unit => fun j : Fin 2 =>
          if j = 0 then (4 / 5 : ℝ) else 1 / 5)
      (by
        intro k j
        fin_cases j <;> norm_num)
      (by
        intro k j
        fin_cases j <;> norm_num)).lower =
      1 -
        Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.productMultiJoin
          (fun j =>
            1 -
              (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalQFMCapacityEndpointInterval
                (endpoint :=
                  fun _ : Unit => fun j : Fin 2 =>
                    if j = 0 then (4 / 5 : ℝ) else 1 / 5)
                (by
                  intro k j
                  fin_cases j <;> norm_num)
                (by
                  intro k j
                  fin_cases j <;> norm_num)
                j).lower) := by
  exact
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalQFMCapacityNoisyOrMultiJoinHull_lower_eq_one_sub_product_compl
      (endpoint :=
        fun _ : Unit => fun j : Fin 2 =>
          if j = 0 then (4 / 5 : ℝ) else 1 / 5)
      (by
        intro k j
        fin_cases j <;> norm_num)
      (by
        intro k j
        fin_cases j <;> norm_num)

def fixtureSingletonModelSpace (M : HenkinModel FixtureBase FixtureConst) :
    ModelSpace FixtureBase FixtureConst where
  Idx := Unit
  instMeasurableSpace := inferInstance
  model := fun _ => M
  measurable_sentence_event := by
    intro φ
    classical
    have hEvent :
        {i : Unit | Mettapedia.Logic.HOL.WorldModel.holSatisfies M φ} =
          if Mettapedia.Logic.HOL.WorldModel.holSatisfies M φ then Set.univ else ∅ := by
      by_cases h : Mettapedia.Logic.HOL.WorldModel.holSatisfies M φ
      · rw [if_pos h]
        ext i
        constructor
        · intro _hp
          trivial
        · intro _hUnit
          exact h
      · rw [if_neg h]
        ext i
        constructor
        · intro hp
          exact h hp
        · intro hEmpty
          exact False.elim hEmpty
    rw [hEvent]
    split <;> simp

def fixtureModelSpace : ModelSpace FixtureBase FixtureConst :=
  fixtureSingletonModelSpace fixtureModel

def fixtureEmptyModelSpace : ModelSpace FixtureBase FixtureConst :=
  fixtureSingletonModelSpace fixtureEmptyModel

noncomputable def fixtureHierarchicalState : HierarchicalState FixtureBase FixtureConst :=
  HierarchicalState.ofConstantMeasure fixtureModelSpace (MeasureTheory.Measure.dirac ())

noncomputable def fixtureEmptyHierarchicalState :
    HierarchicalState FixtureBase FixtureConst :=
  HierarchicalState.ofConstantMeasure fixtureEmptyModelSpace (MeasureTheory.Measure.dirac ())

theorem canary_hol_hierarchicalPredicateSimilarityTopTop_strength_one :
    Mettapedia.Logic.PLNHigherOrderHOLProbabilisticBridge.hierarchicalPredicateSimilarityStrength
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureHierarchicalState FixtureObjTy fixturePredTop fixturePredTop = 1 :=
  Mettapedia.Logic.PLNHigherOrderHOLProbabilisticBridge.hierarchicalPredicateSimilarityStrength_eq_one_of_pointwiseMutualInherits
    (Base := FixtureBase) (Const := FixtureConst)
    fixtureHierarchicalState FixtureObjTy fixturePredTop fixturePredTop
    (by
      intro i
      cases i
      exact canary_hol_predicateTop_mutualInherits_predicateTop)

theorem canary_hol_hierarchicalPredicateSimilarityTopBot_strength_zero :
    Mettapedia.Logic.PLNHigherOrderHOLProbabilisticBridge.hierarchicalPredicateSimilarityStrength
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureHierarchicalState FixtureObjTy fixturePredTop fixturePredBot = 0 :=
  Mettapedia.Logic.PLNHigherOrderHOLProbabilisticBridge.hierarchicalPredicateSimilarityStrength_eq_zero_of_pointwiseNotMutualInherits
    (Base := FixtureBase) (Const := FixtureConst)
    fixtureHierarchicalState FixtureObjTy fixturePredTop fixturePredBot
    (by
      intro i
      cases i
      exact canary_hol_not_predicateTop_mutualInherits_predicateBot)

theorem canary_hol_empty_hierarchicalPredicateSimilarityTopBot_strength_one :
    Mettapedia.Logic.PLNHigherOrderHOLProbabilisticBridge.hierarchicalPredicateSimilarityStrength
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureEmptyHierarchicalState FixtureObjTy fixturePredTop fixturePredBot = 1 :=
  Mettapedia.Logic.PLNHigherOrderHOLProbabilisticBridge.hierarchicalPredicateSimilarityStrength_eq_one_of_pointwiseMutualInherits
    (Base := FixtureBase) (Const := FixtureConst)
    fixtureEmptyHierarchicalState FixtureObjTy fixturePredTop fixturePredBot
    (by
      intro i
      cases i
      exact canary_hol_empty_predicateTop_mutualInherits_predicateBot)

noncomputable def fixtureCredalFamily (_ : Unit) : HierarchicalState FixtureBase FixtureConst :=
  fixtureHierarchicalState

noncomputable def fixtureTwoCompletionCredalFamily :
    Bool → HierarchicalState FixtureBase FixtureConst
  | false => fixtureHierarchicalState
  | true => fixtureEmptyHierarchicalState

/-- Two-point model space mixing the nonempty fixture model with the empty
fixture model.  It is the smallest semantic witness where the same predicate
equivalence has probability `1/2` rather than collapsing to a crisp `0` or `1`.
-/
noncomputable def fixtureTwoModelSpace : ModelSpace FixtureBase FixtureConst where
  Idx := Bool
  instMeasurableSpace := inferInstance
  model := fun b => if b then fixtureEmptyModel else fixtureModel
  measurable_sentence_event := by
    intro _φ
    exact Set.Finite.measurableSet (Set.toFinite _)

noncomputable abbrev fixtureBoolUniformMeasure : MeasureTheory.Measure Bool :=
  ProbabilityTheory.uniformOn (Set.univ : Set Bool)

/-- Uniform half/half hierarchical state over the two fixture completions. -/
noncomputable def fixtureTwoModelUniformState :
    HierarchicalState FixtureBase FixtureConst := by
  have hμ : MeasureTheory.IsProbabilityMeasure fixtureBoolUniformMeasure := by
    simpa [fixtureBoolUniformMeasure] using
      (inferInstance :
        MeasureTheory.IsProbabilityMeasure
          (ProbabilityTheory.uniformOn (Set.univ : Set Bool)))
  exact
    @HierarchicalState.ofConstantMeasure
      FixtureBase FixtureConst fixtureTwoModelSpace fixtureBoolUniformMeasure hμ

theorem canary_hol_twoModelSpace_topBotIff_event :
    fixtureTwoModelSpace.sentenceEvent fixturePredTopBotIff = ({true} : Set Bool) := by
  ext b
  cases b
  · constructor
    · intro h
      simp [ModelSpace.sentenceEvent, fixtureTwoModelSpace] at h
      have hMutual :=
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateMutualInheritsAt_iff_models_predicateIffFormula
          (Base := FixtureBase) (Const := FixtureConst)
          fixtureModel FixtureObjTy fixturePredTop fixturePredBot).2 h
      exact False.elim (canary_hol_not_predicateTop_mutualInherits_predicateBot hMutual)
    · intro h
      exact False.elim (Bool.false_ne_true (Set.mem_singleton_iff.mp h))
  · constructor
    · intro _h
      exact Set.mem_singleton true
    · intro _h
      simp [ModelSpace.sentenceEvent, fixtureTwoModelSpace]
      exact
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateMutualInheritsAt_iff_models_predicateIffFormula
            (Base := FixtureBase) (Const := FixtureConst)
            fixtureEmptyModel FixtureObjTy fixturePredTop fixturePredBot).1
          canary_hol_empty_predicateTop_mutualInherits_predicateBot

theorem canary_hol_twoModelSpace_topBotIff_sentenceProb_half :
    sentenceProb fixtureTwoModelSpace fixtureBoolUniformMeasure fixturePredTopBotIff =
      (1 / 2 : ℝ≥0∞) := by
  rw [sentenceProb, canary_hol_twoModelSpace_topBotIff_event]
  have h :=
    ProbabilityTheory.uniformOn_univ (Ω := Bool) (s := ({true} : Set Bool))
  change ProbabilityTheory.uniformOn (Set.univ : Set Bool) ({true} : Set Bool) =
    (1 / 2 : ℝ≥0∞)
  simpa using h

theorem canary_hol_twoModelUniform_topBotIff_value_half :
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
      fixtureTwoModelUniformState fixturePredTopBotIff = (1 / 2 : ℝ) := by
  unfold Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
  rw [hierarchicalProbQueryStrength_eq_sentenceProb]
  unfold fixtureTwoModelUniformState
  rw [hierarchicalSentenceProb_ofConstantMeasure_eq_sentenceProb]
  rw [canary_hol_twoModelSpace_topBotIff_sentenceProb_half]
  norm_num

theorem canary_hol_credalPredicateSimilarityTopTop_interval_one :
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateSimilarityInterval
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureCredalFamily FixtureObjTy fixturePredTop fixturePredTop =
        Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.constInterval 1 := by
  rw [Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateSimilarityInterval_eq_const_of_subsingleton
    (Base := FixtureBase) (Const := FixtureConst)
    fixtureCredalFamily () FixtureObjTy fixturePredTop fixturePredTop]
  change
    Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.constInterval
      (Mettapedia.Logic.PLNHigherOrderHOLProbabilisticBridge.hierarchicalPredicateSimilarityStrength
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureHierarchicalState FixtureObjTy fixturePredTop fixturePredTop).toReal =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.constInterval 1
  rw [canary_hol_hierarchicalPredicateSimilarityTopTop_strength_one]
  simp

theorem canary_hol_credalPredicateSimilarityTopBot_interval_zero :
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateSimilarityInterval
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureCredalFamily FixtureObjTy fixturePredTop fixturePredBot =
        Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.constInterval 0 := by
  rw [Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateSimilarityInterval_eq_const_of_subsingleton
    (Base := FixtureBase) (Const := FixtureConst)
    fixtureCredalFamily () FixtureObjTy fixturePredTop fixturePredBot]
  change
    Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.constInterval
      (Mettapedia.Logic.PLNHigherOrderHOLProbabilisticBridge.hierarchicalPredicateSimilarityStrength
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureHierarchicalState FixtureObjTy fixturePredTop fixturePredBot).toReal =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.constInterval 0
  rw [canary_hol_hierarchicalPredicateSimilarityTopBot_strength_zero]
  simp

theorem canary_hol_credalPredicateSimilarityTopBot_two_completion_bounds :
    let I :=
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateSimilarityInterval
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureTwoCompletionCredalFamily FixtureObjTy fixturePredTop fixturePredBot
    I.lower = 0 ∧ I.upper = 1 := by
  let φ :=
    Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateIffFormula
      (Base := FixtureBase) (Const := FixtureConst)
      FixtureObjTy fixturePredTop fixturePredBot
  have hFalse :
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
        (fixtureTwoCompletionCredalFamily false) φ = 0 := by
    change
      (Mettapedia.Logic.PLNHigherOrderHOLProbabilisticBridge.hierarchicalPredicateSimilarityStrength
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureHierarchicalState FixtureObjTy fixturePredTop fixturePredBot).toReal = 0
    rw [canary_hol_hierarchicalPredicateSimilarityTopBot_strength_zero]
    simp
  have hTrue :
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
        (fixtureTwoCompletionCredalFamily true) φ = 1 := by
    change
      (Mettapedia.Logic.PLNHigherOrderHOLProbabilisticBridge.hierarchicalPredicateSimilarityStrength
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureEmptyHierarchicalState FixtureObjTy fixturePredTop fixturePredBot).toReal = 1
    rw [canary_hol_empty_hierarchicalPredicateSimilarityTopBot_strength_one]
    simp
  have hRange :
      Set.range
          (fun i =>
            Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
              (fixtureTwoCompletionCredalFamily i) φ) =
        ({0, 1} : Set ℝ) := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩
      cases i
      · exact Or.inl hFalse
      · exact Or.inr hTrue
    · intro hr
      simp at hr
      rcases hr with h0 | h1
      · exact ⟨false, by
          change
            Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
              (fixtureTwoCompletionCredalFamily false) φ = r
          rw [hFalse, ← h0]⟩
      · exact ⟨true, by
          change
            Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
              (fixtureTwoCompletionCredalFamily true) φ = r
          rw [hTrue, ← h1]⟩
  constructor
  · unfold Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateSimilarityInterval
    change
      (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaInterval
        fixtureTwoCompletionCredalFamily φ).lower = 0
    unfold Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaInterval
    dsimp [Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.IntervalAddSemantics.intervalOf]
    rw [hRange]
    simp
  · unfold Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateSimilarityInterval
    change
      (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaInterval
        fixtureTwoCompletionCredalFamily φ).upper = 1
    unfold Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaInterval
    dsimp [Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.IntervalAddSemantics.intervalOf]
    rw [hRange]
    simp

theorem fixtureHalfCredibility : (1 / 2 : ℝ) ∈ Set.Icc 0 1 := by
  norm_num

theorem canary_hol_credalPredicateSimilarityTopBot_two_completion_ITV :
    let tv :=
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateSimilarityITV
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureTwoCompletionCredalFamily FixtureObjTy fixturePredTop fixturePredBot
        (1 / 2 : ℝ) fixtureHalfCredibility
    tv.lower = 0 ∧ tv.upper = 1 ∧ tv.credibility = 1 / 2 ∧ tv.width = 1 := by
  have hBounds :=
    canary_hol_credalPredicateSimilarityTopBot_two_completion_bounds
  dsimp
  constructor
  · simpa [
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateSimilarityITV,
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateSimilarityInterval]
      using hBounds.1
  constructor
  · simpa [
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateSimilarityITV,
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateSimilarityInterval]
      using hBounds.2
  constructor
  · simp [
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateSimilarityITV]
  · let φ :=
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateIffFormula
        (Base := FixtureBase) (Const := FixtureConst)
        FixtureObjTy fixturePredTop fixturePredBot
    have hLower :
        (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaInterval
          fixtureTwoCompletionCredalFamily φ).lower = 0 := by
      simpa [
        Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateSimilarityInterval]
        using hBounds.1
    have hUpper :
        (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaInterval
          fixtureTwoCompletionCredalFamily φ).upper = 1 := by
      simpa [
        Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateSimilarityInterval]
        using hBounds.2
    change
      (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaInterval
        fixtureTwoCompletionCredalFamily φ).upper -
        (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaInterval
          fixtureTwoCompletionCredalFamily φ).lower = 1
    rw [hUpper, hLower]
    norm_num

theorem canary_hol_credalPredicateSimilarityTopTop_ITV :
    let tv :=
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateSimilarityITV
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureCredalFamily FixtureObjTy fixturePredTop fixturePredTop
        (1 / 2 : ℝ) fixtureHalfCredibility
    tv.lower = 1 ∧ tv.upper = 1 ∧ tv.credibility = 1 / 2 ∧ tv.width = 0 := by
  have hInterval := canary_hol_credalPredicateSimilarityTopTop_interval_one
  dsimp
  constructor
  · simpa [
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateSimilarityITV,
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateSimilarityInterval,
      Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.constInterval] using congrArg
        Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.Interval.lower
        hInterval
  constructor
  · simpa [
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateSimilarityITV,
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateSimilarityInterval,
      Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.constInterval] using congrArg
        Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.Interval.upper
        hInterval
  constructor
  · simp [
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateSimilarityITV]
  · have hL :
        (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateSimilarityInterval
          (Base := FixtureBase) (Const := FixtureConst)
          fixtureCredalFamily FixtureObjTy fixturePredTop fixturePredTop).lower = 1 := by
      simpa [
        Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.constInterval] using congrArg
          Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.Interval.lower
          hInterval
    have hU :
        (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateSimilarityInterval
          (Base := FixtureBase) (Const := FixtureConst)
          fixtureCredalFamily FixtureObjTy fixturePredTop fixturePredTop).upper = 1 := by
      simpa [
        Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.constInterval] using congrArg
          Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.Interval.upper
          hInterval
    change
      (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateSimilarityInterval
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureCredalFamily FixtureObjTy fixturePredTop fixturePredTop).upper -
      (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateSimilarityInterval
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureCredalFamily FixtureObjTy fixturePredTop fixturePredTop).lower = 0
    rw [hU, hL]
    norm_num

/-- Flagship HO-PLN predicate-similarity canary: a decided predicate
relationship collapses to width `0`, while the same top/bot query over a
two-completion family keeps the full width `1`.

This is the small executable theorem-shape behind the MeTTa
`canonical-decided-query-width` / `canonical-open-query-width` witness: width is
logical/model-class indeterminacy, not an arbitrary confidence penalty. -/
theorem canary_hol_flagship_predicateSimilarity_decided_vs_open_widths :
    let decided :=
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateSimilarityITV
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureCredalFamily FixtureObjTy fixturePredTop fixturePredTop
        (1 / 2 : ℝ) fixtureHalfCredibility
    let openCase :=
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateSimilarityITV
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureTwoCompletionCredalFamily FixtureObjTy fixturePredTop fixturePredBot
        (1 / 2 : ℝ) fixtureHalfCredibility
    decided.width = 0 ∧ openCase.width = 1 ∧
      decided.lower = 1 ∧ openCase.lower = 0 ∧ openCase.upper = 1 := by
  have hDecided := canary_hol_credalPredicateSimilarityTopTop_ITV
  have hOpen := canary_hol_credalPredicateSimilarityTopBot_two_completion_ITV
  dsimp at hDecided hOpen ⊢
  exact ⟨hDecided.2.2.2, hOpen.2.2.2, hDecided.1, hOpen.1, hOpen.2.1⟩

/-- Five genuine HOL predicate-similarity links whose flattened strengths are
used as the five coordinates of the PLN deduction rule.  Each coordinate is the
same `top ↔ bot` predicate-equivalence query in the uniform two-completion
state, so each evaluates to `1/2`. -/
def fixtureTopBotSimilarityDeductionLinks :
    Fin 5 → ClosedTerm FixtureConst FixturePredTy × ClosedTerm FixtureConst FixturePredTy :=
  fun _ => (fixturePredTop, fixturePredBot)

theorem canary_hol_topBotSimilarityDeductionCoordinates_eq_open :
    Mettapedia.Logic.PLNHigherOrderHOLDeductionBridge.hierarchicalPredicateSimilarityDeductionCoordinates
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureTwoModelUniformState FixtureObjTy fixtureTopBotSimilarityDeductionLinks =
        Mettapedia.Logic.PLNHigherOrderHOLDeductionBridge.openDeductionCanaryCoordinates := by
  funext j
  fin_cases j <;>
    simp [
      fixtureTopBotSimilarityDeductionLinks,
      Mettapedia.Logic.PLNHigherOrderHOLDeductionBridge.hierarchicalPredicateSimilarityDeductionCoordinates,
      Mettapedia.Logic.PLNHigherOrderHOLDeductionBridge.openDeductionCanaryCoordinates]
  all_goals
    simpa [fixturePredTopBotIff] using
      canary_hol_twoModelUniform_topBotIff_value_half

theorem canary_hol_topBotSimilarityDeduction_admissible :
    Mettapedia.Logic.PLNHigherOrderHOLDeductionBridge.DeductionCoordinateAdmissibility
      (Mettapedia.Logic.PLNHigherOrderHOLDeductionBridge.hierarchicalPredicateSimilarityDeductionCoordinates
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureTwoModelUniformState FixtureObjTy fixtureTopBotSimilarityDeductionLinks) := by
  rw [canary_hol_topBotSimilarityDeductionCoordinates_eq_open]
  refine ⟨?_, ?_,
    Mettapedia.Logic.PLNHigherOrderHOLDeductionBridge.openDeductionCanary_feasible,
    ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [
      Mettapedia.Logic.PLNHigherOrderHOLDeductionBridge.openDeductionCanaryCoordinates,
      Mettapedia.Logic.PLNDeduction.conditionalProbabilityConsistency,
      Mettapedia.Logic.PLNDeduction.deductionBBranchLower,
      Mettapedia.Logic.PLNDeduction.deductionBBranchUpper,
      Mettapedia.Logic.PLNDeduction.deductionNotBBranchLower,
      Mettapedia.Logic.PLNDeduction.deductionNotBBranchUpper,
      Mettapedia.Logic.PLNDeduction.deductionJointAB,
      Mettapedia.Logic.PLNDeduction.deductionJointBC,
      Mettapedia.Logic.PLNDeduction.smallestIntersectionProbability,
      Mettapedia.Logic.PLNDeduction.largestIntersectionProbability,
      Mettapedia.Logic.PLNDeduction.complementConditionalFromMarginal]

theorem canary_hol_topBotSimilarityDeductionPointValue_open :
    Mettapedia.Logic.PLNHigherOrderHOLDeductionBridge.hierarchicalPredicateSimilarityDeductionPointValue
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureTwoModelUniformState FixtureObjTy fixtureTopBotSimilarityDeductionLinks =
        1 / 2 := by
  change
    Mettapedia.Logic.PLNHigherOrderHOLDeductionBridge.deductionAsFinite5
      (Mettapedia.Logic.PLNHigherOrderHOLDeductionBridge.hierarchicalPredicateSimilarityDeductionCoordinates
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureTwoModelUniformState FixtureObjTy fixtureTopBotSimilarityDeductionLinks) =
      1 / 2
  rw [canary_hol_topBotSimilarityDeductionCoordinates_eq_open]
  exact Mettapedia.Logic.PLNHigherOrderHOLDeductionBridge.openDeductionCanary_pointValue

theorem canary_hol_topBotSimilarityDeductionPointValue_mem_openITV :
    Mettapedia.Logic.PLNHigherOrderHOLDeductionBridge.openDeductionCanaryITV.lower ≤
        Mettapedia.Logic.PLNHigherOrderHOLDeductionBridge.hierarchicalPredicateSimilarityDeductionPointValue
          (Base := FixtureBase) (Const := FixtureConst)
          fixtureTwoModelUniformState FixtureObjTy fixtureTopBotSimilarityDeductionLinks ∧
      Mettapedia.Logic.PLNHigherOrderHOLDeductionBridge.hierarchicalPredicateSimilarityDeductionPointValue
          (Base := FixtureBase) (Const := FixtureConst)
          fixtureTwoModelUniformState FixtureObjTy fixtureTopBotSimilarityDeductionLinks ≤
        Mettapedia.Logic.PLNHigherOrderHOLDeductionBridge.openDeductionCanaryITV.upper := by
  constructor
  · rw [
      Mettapedia.Logic.PLNHigherOrderHOLDeductionBridge.openDeductionCanaryITV_lower,
      canary_hol_topBotSimilarityDeductionPointValue_open]
    norm_num
  · rw [
      Mettapedia.Logic.PLNHigherOrderHOLDeductionBridge.openDeductionCanaryITV_upper,
      canary_hol_topBotSimilarityDeductionPointValue_open]
    norm_num

theorem canary_hol_impTopBot_nonempty_value_zero :
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
      fixtureHierarchicalState fixturePredTopBotImp = 0 := by
  have hBotIff :
      fixtureHierarchicalState.baseSpace.PointwiseIff
        fixturePredTopBotImp (.bot : ClosedFormula FixtureConst) := by
    intro i
    cases i
    constructor
    · intro hφ
      have hInh :=
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateInterpretation_inherits_iff_models_predicateImpFormula
          (Base := FixtureBase) (Const := FixtureConst)
          fixtureModel FixtureObjTy fixturePredTop fixturePredBot).2 hφ
      exact False.elim (canary_hol_not_predicateTop_inherits_predicateBot hInh)
    · intro hbot
      exact False.elim (HenkinModel.models_bot fixtureModel hbot)
  unfold Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
  change (hierarchicalProbQueryStrength fixtureHierarchicalState fixturePredTopBotImp).toReal = 0
  rw [hierarchicalProbQueryStrength_eq_of_pointwiseIff (H := fixtureHierarchicalState) hBotIff]
  rw [hierarchicalProbQueryStrength_eq_sentenceProb]
  rw [hierarchicalSentenceProb_bot_eq_zero]
  simp

theorem canary_hol_impBotTop_nonempty_value_one :
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
      fixtureHierarchicalState fixturePredBotTopImp = 1 := by
  have hTopIff :
      fixtureHierarchicalState.baseSpace.PointwiseIff
        fixturePredBotTopImp (.top : ClosedFormula FixtureConst) := by
    intro i
    cases i
    constructor
    · intro _hφ
      exact HenkinModel.models_top fixtureModel
    · intro _htop
      apply
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.models_predicateImpFormula_iff
          (Base := FixtureBase) (Const := FixtureConst)
          fixtureModel FixtureObjTy fixturePredBot fixturePredTop).2
      intro _x _hxBot
      change True
      simp
  unfold Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
  change (hierarchicalProbQueryStrength fixtureHierarchicalState fixturePredBotTopImp).toReal = 1
  rw [hierarchicalProbQueryStrength_eq_of_pointwiseIff (H := fixtureHierarchicalState) hTopIff]
  rw [hierarchicalProbQueryStrength_eq_sentenceProb]
  rw [hierarchicalSentenceProb_top_eq_one]
  simp

theorem canary_hol_impTopBot_empty_value_one :
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
      fixtureEmptyHierarchicalState fixturePredTopBotImp = 1 := by
  have hTopIff :
      fixtureEmptyHierarchicalState.baseSpace.PointwiseIff
        fixturePredTopBotImp (.top : ClosedFormula FixtureConst) := by
    intro i
    cases i
    constructor
    · intro _hφ
      exact HenkinModel.models_top fixtureEmptyModel
    · intro _htop
      apply
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.models_predicateImpFormula_iff
          (Base := FixtureBase) (Const := FixtureConst)
          fixtureEmptyModel FixtureObjTy fixturePredTop fixturePredBot).2
      intro x _hxTop
      cases x.1
  unfold Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
  change (hierarchicalProbQueryStrength fixtureEmptyHierarchicalState fixturePredTopBotImp).toReal = 1
  rw [hierarchicalProbQueryStrength_eq_of_pointwiseIff (H := fixtureEmptyHierarchicalState) hTopIff]
  rw [hierarchicalProbQueryStrength_eq_sentenceProb]
  rw [hierarchicalSentenceProb_top_eq_one]
  simp

theorem canary_hol_impBotTop_empty_value_one :
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
      fixtureEmptyHierarchicalState fixturePredBotTopImp = 1 := by
  have hTopIff :
      fixtureEmptyHierarchicalState.baseSpace.PointwiseIff
        fixturePredBotTopImp (.top : ClosedFormula FixtureConst) := by
    intro i
    cases i
    constructor
    · intro _hφ
      exact HenkinModel.models_top fixtureEmptyModel
    · intro _htop
      apply
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.models_predicateImpFormula_iff
          (Base := FixtureBase) (Const := FixtureConst)
          fixtureEmptyModel FixtureObjTy fixturePredBot fixturePredTop).2
      intro x _hxBot
      cases x.1
  unfold Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
  change (hierarchicalProbQueryStrength fixtureEmptyHierarchicalState fixturePredBotTopImp).toReal = 1
  rw [hierarchicalProbQueryStrength_eq_of_pointwiseIff (H := fixtureEmptyHierarchicalState) hTopIff]
  rw [hierarchicalProbQueryStrength_eq_sentenceProb]
  rw [hierarchicalSentenceProb_top_eq_one]
  simp

theorem canary_hol_twoInh2SimPredicateSimilarityTopBot_two_completion_bounds :
    let I :=
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateTwoInh2SimInterval
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureTwoCompletionCredalFamily FixtureObjTy fixturePredTop fixturePredBot
    I.lower = 0 ∧ I.upper = 1 := by
  have hRuleFalse :
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaBinaryRuleValue
        (fixtureTwoCompletionCredalFamily false)
        fixturePredTopBotImp fixturePredBotTopImp
        Mettapedia.Logic.PLNInferenceRules.twoInh2Sim = 0 := by
    unfold Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaBinaryRuleValue
    change
      Mettapedia.Logic.PLNInferenceRules.twoInh2Sim
        (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
          fixtureHierarchicalState fixturePredTopBotImp)
        (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
          fixtureHierarchicalState fixturePredBotTopImp) = 0
    rw [canary_hol_impTopBot_nonempty_value_zero,
      canary_hol_impBotTop_nonempty_value_one]
    norm_num [Mettapedia.Logic.PLNInferenceRules.twoInh2Sim]
  have hRuleTrue :
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaBinaryRuleValue
        (fixtureTwoCompletionCredalFamily true)
        fixturePredTopBotImp fixturePredBotTopImp
        Mettapedia.Logic.PLNInferenceRules.twoInh2Sim = 1 := by
    unfold Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaBinaryRuleValue
    change
      Mettapedia.Logic.PLNInferenceRules.twoInh2Sim
        (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
          fixtureEmptyHierarchicalState fixturePredTopBotImp)
        (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
          fixtureEmptyHierarchicalState fixturePredBotTopImp) = 1
    rw [canary_hol_impTopBot_empty_value_one,
      canary_hol_impBotTop_empty_value_one]
    norm_num [Mettapedia.Logic.PLNInferenceRules.twoInh2Sim]
  have hRange :
      Set.range
          (fun i =>
            Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaBinaryRuleValue
              (fixtureTwoCompletionCredalFamily i)
              fixturePredTopBotImp fixturePredBotTopImp
              Mettapedia.Logic.PLNInferenceRules.twoInh2Sim) =
        ({0, 1} : Set ℝ) := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩
      cases i
      · exact Or.inl hRuleFalse
      · exact Or.inr hRuleTrue
    · intro hr
      simp at hr
      rcases hr with h0 | h1
      · exact ⟨false, by
          change
            Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaBinaryRuleValue
              (fixtureTwoCompletionCredalFamily false)
              fixturePredTopBotImp fixturePredBotTopImp
              Mettapedia.Logic.PLNInferenceRules.twoInh2Sim = r
          rw [hRuleFalse, ← h0]⟩
      · exact ⟨true, by
          change
            Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaBinaryRuleValue
              (fixtureTwoCompletionCredalFamily true)
              fixturePredTopBotImp fixturePredBotTopImp
              Mettapedia.Logic.PLNInferenceRules.twoInh2Sim = r
          rw [hRuleTrue, ← h1]⟩
  constructor
  · unfold Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateTwoInh2SimInterval
    unfold Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaBinaryRuleInterval
    dsimp [Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.IntervalAddSemantics.intervalOf]
    change
      sInf
          (Set.range fun i =>
            Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaBinaryRuleValue
              (fixtureTwoCompletionCredalFamily i)
              fixturePredTopBotImp fixturePredBotTopImp
              Mettapedia.Logic.PLNInferenceRules.twoInh2Sim) =
        0
    rw [hRange]
    simp
  · unfold Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateTwoInh2SimInterval
    unfold Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaBinaryRuleInterval
    dsimp [Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.IntervalAddSemantics.intervalOf]
    change
      sSup
          (Set.range fun i =>
            Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaBinaryRuleValue
              (fixtureTwoCompletionCredalFamily i)
              fixturePredTopBotImp fixturePredBotTopImp
              Mettapedia.Logic.PLNInferenceRules.twoInh2Sim) =
        1
    rw [hRange]
    simp

theorem canary_hol_twoInh2SimPredicateSimilarityTopBot_two_completion_ITV :
    let tv :=
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateTwoInh2SimITV
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureTwoCompletionCredalFamily FixtureObjTy fixturePredTop fixturePredBot
        (1 / 2 : ℝ) fixtureHalfCredibility
    tv.lower = 0 ∧ tv.upper = 1 ∧ tv.credibility = 1 / 2 := by
  have hBounds :=
    canary_hol_twoInh2SimPredicateSimilarityTopBot_two_completion_bounds
  dsimp
  constructor
  · simpa using hBounds.1
  constructor
  · simpa using hBounds.2
  · simp [
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateTwoInh2SimITV]

/-- A one-symbol active predicate vocabulary used to canary the deployable
finite-vocabulary bridge. -/
abbrev FixtureOnePredVocab := Unit

def fixtureOnePredDecode (_ : FixtureOnePredVocab) :
    Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
      (Base := FixtureBase) (Const := FixtureConst) FixtureObjTy :=
  fixturePredTop

theorem canary_hol_predicateVocabularyTop_extent_nonzero :
    ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureModel FixtureObjTy fixtureOnePredDecode).meaning ()).extent.ncard ≠ 0 := by
  apply ne_of_gt
  rw [Set.ncard_pos]
  refine ⟨⟨PUnit.unit, trivial⟩, ?_⟩
  have hholds :
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateHoldsAt
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureModel FixtureObjTy (fixtureOnePredDecode ()) ⟨PUnit.unit, trivial⟩ := by
    change True
    trivial
  have haccept :
      Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport.accept
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyEvidence
          (Base := FixtureBase) (Const := FixtureConst)
          fixtureModel FixtureObjTy fixtureOnePredDecode ⟨PUnit.unit, trivial⟩ ()) :=
    (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.positiveSupport_accept_predicateVocabularyEvidence_iff
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureModel FixtureObjTy fixtureOnePredDecode ⟨PUnit.unit, trivial⟩ ()).2
      hholds
  simpa [
    Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation,
    Mettapedia.Logic.AbstractInheritance.crispInterpretation,
    Mettapedia.Logic.AbstractInheritance.ofCrispBaseConcept,
    Mettapedia.Logic.AbstractInheritance.crispBaseConcept,
    Mettapedia.Logic.ConceptOntology.mem_crispExtent_iff] using haccept

theorem canary_hol_predicateVocabularyTop_intent_nonzero :
    ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureModel FixtureObjTy fixtureOnePredDecode).meaning ()).intent.ncard ≠ 0 := by
  apply ne_of_gt
  rw [Set.ncard_pos]
  refine ⟨(), ?_⟩
  change () ∈
    (Mettapedia.Logic.AbstractInheritance.ofCrispBaseConcept
      Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyEvidence
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureModel FixtureObjTy fixtureOnePredDecode) ()).intent
  exact
    Mettapedia.Logic.AbstractInheritance.self_mem_intent_ofCrispBaseConcept
      Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyEvidence
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureModel FixtureObjTy fixtureOnePredDecode) ()

theorem canary_hol_predicateVocabularyTop_sameIntent_self :
    Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureModel FixtureObjTy fixtureOnePredDecode () () := by
  rfl

theorem canary_hol_predicateVocabularyIntensionalPairSubsetRel_self :
    Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel
      (State := Unit) (Base := FixtureBase) (Const := FixtureConst)
      fixtureModel FixtureObjTy fixtureOnePredDecode () () () () () := by
  exact
    Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel_of_sameIntent
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureModel FixtureObjTy fixtureOnePredDecode ()
      canary_hol_predicateVocabularyTop_sameIntent_self
      canary_hol_predicateVocabularyTop_sameIntent_self

theorem canary_hol_predicateVocabularyFullInheritanceTopTop_strength_one :
    Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureModel FixtureObjTy fixtureOnePredDecode () () = 1 := by
  apply
    (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength_eq_one_iff_models_predicateImpFormula
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureModel FixtureObjTy fixtureOnePredDecode () ()
      canary_hol_predicateVocabularyTop_extent_nonzero
      canary_hol_predicateVocabularyTop_intent_nonzero).2
  apply
    (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.models_predicateImpFormula_iff
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureModel FixtureObjTy fixturePredTop fixturePredTop).2
  intro _x hx
  exact hx

theorem canary_hol_predicateVocabularyFullInheritanceTopTop_chain_strength_one :
    Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureModel FixtureObjTy fixtureOnePredDecode () () = 1 :=
  Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength_eq_one_of_chain
    (Base := FixtureBase) (Const := FixtureConst)
    fixtureModel FixtureObjTy fixtureOnePredDecode () () ()
    canary_hol_predicateVocabularyTop_extent_nonzero
    canary_hol_predicateVocabularyTop_intent_nonzero
    canary_hol_predicateVocabularyTop_extent_nonzero
    canary_hol_predicateVocabularyTop_intent_nonzero
    canary_hol_predicateVocabularyFullInheritanceTopTop_strength_one
    canary_hol_predicateVocabularyFullInheritanceTopTop_strength_one

theorem canary_hol_predicateVocabularySimilarityTopTop_strength_one :
    Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySimilarityStrength
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureModel FixtureObjTy fixtureOnePredDecode () () = 1 := by
  apply
    Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySimilarityStrength_eq_one_of_models_predicateIffFormula
  · exact canary_hol_predicateVocabularyTop_extent_nonzero
  · exact canary_hol_predicateVocabularyTop_intent_nonzero
  · exact canary_hol_predicateVocabularyTop_extent_nonzero
  · exact canary_hol_predicateVocabularyTop_intent_nonzero
  · apply (HenkinModel.models_and fixtureModel).2
    constructor
    · apply
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.models_predicateImpFormula_iff
            (Base := FixtureBase) (Const := FixtureConst)
            fixtureModel FixtureObjTy fixturePredTop fixturePredTop).2
      intro _x hx
      exact hx
    · apply
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.models_predicateImpFormula_iff
            (Base := FixtureBase) (Const := FixtureConst)
            fixtureModel FixtureObjTy fixturePredTop fixturePredTop).2
      intro _x hx
      exact hx

theorem canary_hol_predicateVocabularySourceSimilarityTransfer_strength_one :
    Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureModel FixtureObjTy fixtureOnePredDecode () () = 1 :=
  Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularyFullInheritanceStrength_eq_one_of_source_similarity
    (Base := FixtureBase) (Const := FixtureConst)
    fixtureModel FixtureObjTy fixtureOnePredDecode () () ()
    canary_hol_predicateVocabularyTop_extent_nonzero
    canary_hol_predicateVocabularyTop_intent_nonzero
    canary_hol_predicateVocabularyTop_extent_nonzero
    canary_hol_predicateVocabularyTop_intent_nonzero
    canary_hol_predicateVocabularyTop_intent_nonzero
    canary_hol_predicateVocabularySimilarityTopTop_strength_one
    canary_hol_predicateVocabularyFullInheritanceTopTop_strength_one

theorem canary_hol_predicateVocabularyTargetSimilarityTransfer_strength_one :
    Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyFullInheritanceStrength
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureModel FixtureObjTy fixtureOnePredDecode () () = 1 :=
  Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularyFullInheritanceStrength_eq_one_of_target_similarity
    (Base := FixtureBase) (Const := FixtureConst)
    fixtureModel FixtureObjTy fixtureOnePredDecode () () ()
    canary_hol_predicateVocabularyTop_extent_nonzero
    canary_hol_predicateVocabularyTop_intent_nonzero
    canary_hol_predicateVocabularyTop_extent_nonzero
    canary_hol_predicateVocabularyTop_extent_nonzero
    canary_hol_predicateVocabularyTop_intent_nonzero
    canary_hol_predicateVocabularyFullInheritanceTopTop_strength_one
    canary_hol_predicateVocabularySimilarityTopTop_strength_one

theorem canary_hol_predicateVocabularyPureExtensionalSimilarityTopTop_strength_one :
    Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularyPureExtensionalSimilarityStrength
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureModel FixtureObjTy fixtureOnePredDecode () () = 1 := by
  apply
    Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularyPureExtensionalSimilarityStrength_eq_one_of_mutualExtensional
  · exact canary_hol_predicateVocabularyTop_extent_nonzero
  · exact canary_hol_predicateVocabularyTop_extent_nonzero
  · intro _obj hobj
    exact hobj
  · intro _obj hobj
    exact hobj

theorem canary_hol_predicateVocabularyPureIntensionalSimilarityTopTop_strength_one :
    Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularyPureIntensionalSimilarityStrength
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureModel FixtureObjTy fixtureOnePredDecode () () = 1 := by
  apply
    Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularyPureIntensionalSimilarityStrength_eq_one_of_mutualIntensional
  · exact canary_hol_predicateVocabularyTop_intent_nonzero
  · exact canary_hol_predicateVocabularyTop_intent_nonzero
  · intro _attr hattr
    exact hattr
  · intro _attr hattr
    exact hattr

theorem canary_hol_predicateVocabularyPureIntensionalSimilarityTopTop_strength_one_of_sameIntent :
    Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularyPureIntensionalSimilarityStrength
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureModel FixtureObjTy fixtureOnePredDecode () () = 1 := by
  exact
    Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularyPureIntensionalSimilarityStrength_eq_one_of_sameIntent
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureModel FixtureObjTy fixtureOnePredDecode () ()
      canary_hol_predicateVocabularyTop_intent_nonzero
      canary_hol_predicateVocabularyTop_intent_nonzero
      canary_hol_predicateVocabularyTop_sameIntent_self

noncomputable def fixtureVocabularyModelFamily (_ : Unit) :
    HenkinModel FixtureBase FixtureConst :=
  fixtureModel

noncomputable def fixtureVocabularyObjectFintype
    (_ : Unit) :
    Fintype
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.PredicateObject
        (Base := FixtureBase) (Const := FixtureConst) fixtureModel FixtureObjTy) :=
  inferInstance

theorem canary_hol_credalPredicateVocabularySimilarityTopTop_interval_one :
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateVocabularySimilarityInterval
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureVocabularyModelFamily FixtureObjTy fixtureOnePredDecode
        fixtureVocabularyObjectFintype () () =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.constInterval 1 := by
  apply
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateVocabularySimilarityInterval_eq_const_one_of_pointwise_models
  · intro i
    cases i
    exact canary_hol_predicateVocabularyTop_extent_nonzero
  · intro i
    cases i
    exact canary_hol_predicateVocabularyTop_intent_nonzero
  · intro i
    cases i
    exact canary_hol_predicateVocabularyTop_extent_nonzero
  · intro i
    cases i
    exact canary_hol_predicateVocabularyTop_intent_nonzero
  · intro i
    cases i
    apply (HenkinModel.models_and fixtureModel).2
    constructor
    · apply
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.models_predicateImpFormula_iff
            (Base := FixtureBase) (Const := FixtureConst)
            fixtureModel FixtureObjTy fixturePredTop fixturePredTop).2
      intro _x hx
      exact hx
    · apply
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.models_predicateImpFormula_iff
            (Base := FixtureBase) (Const := FixtureConst)
            fixtureModel FixtureObjTy fixturePredTop fixturePredTop).2
      intro _x hx
      exact hx

theorem canary_hol_credalPredicateVocabularySimilarityTopTop_ITV :
    let tv :=
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateVocabularySimilarityITV
          (Base := FixtureBase) (Const := FixtureConst)
          fixtureVocabularyModelFamily FixtureObjTy fixtureOnePredDecode
          fixtureVocabularyObjectFintype () ()
          (1 / 2 : ℝ) fixtureHalfCredibility
    tv.lower = 1 ∧ tv.upper = 1 ∧ tv.credibility = 1 / 2 := by
  have hInterval :=
    canary_hol_credalPredicateVocabularySimilarityTopTop_interval_one
  dsimp
  constructor
  · rw [Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateVocabularySimilarityITV_lower]
    simpa [Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.constInterval] using congrArg
      Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.Interval.lower
      hInterval
  constructor
  · rw [Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateVocabularySimilarityITV_upper]
    simpa [Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.constInterval] using congrArg
      Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.Interval.upper
      hInterval
  · simp [
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateVocabularySimilarityITV,
      Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

theorem canary_hol_credalPredicateVocabularyPureExtensionalSimilarityTopTop_interval_one :
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateVocabularyPureExtensionalSimilarityInterval
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureVocabularyModelFamily FixtureObjTy fixtureOnePredDecode
        fixtureVocabularyObjectFintype () () =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.constInterval 1 := by
  apply
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateVocabularyPureExtensionalSimilarityInterval_eq_const_of_pointwise_value_eq
  intro i
  cases i
  exact canary_hol_predicateVocabularyPureExtensionalSimilarityTopTop_strength_one

theorem canary_hol_credalPredicateVocabularyPureIntensionalSimilarityTopTop_interval_one :
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateVocabularyPureIntensionalSimilarityInterval
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureVocabularyModelFamily FixtureObjTy fixtureOnePredDecode () () =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.constInterval 1 := by
  apply
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateVocabularyPureIntensionalSimilarityInterval_eq_const_of_pointwise_value_eq
  intro i
  cases i
  exact canary_hol_predicateVocabularyPureIntensionalSimilarityTopTop_strength_one

theorem canary_hol_credalPredicateVocabularyPureExtensionalSimilarityTopTop_interval_one_of_mutual :
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateVocabularyPureExtensionalSimilarityInterval
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureVocabularyModelFamily FixtureObjTy fixtureOnePredDecode
        fixtureVocabularyObjectFintype () () =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.constInterval 1 := by
  apply
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateVocabularyPureExtensionalSimilarityInterval_eq_const_one_of_pointwise_mutualExtensional
  · intro i
    cases i
    exact canary_hol_predicateVocabularyTop_extent_nonzero
  · intro i
    cases i
    exact canary_hol_predicateVocabularyTop_extent_nonzero
  · intro i
    cases i
    constructor
    · intro _obj hobj
      exact hobj
    · intro _obj hobj
      exact hobj

theorem canary_hol_credalPredicateVocabularyPureIntensionalSimilarityTopTop_interval_one_of_mutual :
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateVocabularyPureIntensionalSimilarityInterval
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureVocabularyModelFamily FixtureObjTy fixtureOnePredDecode () () =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.constInterval 1 := by
  apply
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateVocabularyPureIntensionalSimilarityInterval_eq_const_one_of_pointwise_mutualIntensional
  · intro i
    cases i
    exact canary_hol_predicateVocabularyTop_intent_nonzero
  · intro i
    cases i
    exact canary_hol_predicateVocabularyTop_intent_nonzero
  · intro i
    cases i
    constructor
    · intro _attr hattr
      exact hattr
    · intro _attr hattr
      exact hattr

theorem canary_hol_credalPredicateVocabularyPureIntensionalSimilarityTopTop_interval_one_of_sameIntent :
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateVocabularyPureIntensionalSimilarityInterval
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureVocabularyModelFamily FixtureObjTy fixtureOnePredDecode () () =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.constInterval 1 := by
  apply
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateVocabularyPureIntensionalSimilarityInterval_eq_const_one_of_pointwise_sameIntent
  · intro i
    cases i
    exact canary_hol_predicateVocabularyTop_intent_nonzero
  · intro i
    cases i
    exact canary_hol_predicateVocabularyTop_intent_nonzero
  · intro i
    cases i
    exact canary_hol_predicateVocabularyTop_sameIntent_self

theorem canary_hol_credalPredicateVocabularyPureExtensionalSimilarityTopTop_ITV :
    let tv :=
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateVocabularyPureExtensionalSimilarityITV
          (Base := FixtureBase) (Const := FixtureConst)
          fixtureVocabularyModelFamily FixtureObjTy fixtureOnePredDecode
          fixtureVocabularyObjectFintype () ()
          (1 / 2 : ℝ) fixtureHalfCredibility
    tv.lower = 1 ∧ tv.upper = 1 ∧ tv.credibility = 1 / 2 := by
  have hInterval :=
    canary_hol_credalPredicateVocabularyPureExtensionalSimilarityTopTop_interval_one
  dsimp
  constructor
  · rw [Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateVocabularyPureExtensionalSimilarityITV_lower]
    simpa [Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.constInterval] using congrArg
      Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.Interval.lower
      hInterval
  constructor
  · rw [Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateVocabularyPureExtensionalSimilarityITV_upper]
    simpa [Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.constInterval] using congrArg
      Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.Interval.upper
      hInterval
  · simp [
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateVocabularyPureExtensionalSimilarityITV,
      Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

theorem canary_hol_credalPredicateVocabularyPureIntensionalSimilarityTopTop_ITV :
    let tv :=
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateVocabularyPureIntensionalSimilarityITV
          (Base := FixtureBase) (Const := FixtureConst)
          fixtureVocabularyModelFamily FixtureObjTy fixtureOnePredDecode () ()
          (1 / 2 : ℝ) fixtureHalfCredibility
    tv.lower = 1 ∧ tv.upper = 1 ∧ tv.credibility = 1 / 2 := by
  have hInterval :=
    canary_hol_credalPredicateVocabularyPureIntensionalSimilarityTopTop_interval_one
  dsimp
  constructor
  · rw [Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateVocabularyPureIntensionalSimilarityITV_lower]
    simpa [Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.constInterval] using congrArg
      Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.Interval.lower
      hInterval
  constructor
  · rw [Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateVocabularyPureIntensionalSimilarityITV_upper]
    simpa [Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.constInterval] using congrArg
      Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.Interval.upper
      hInterval
  · simp [
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalPredicateVocabularyPureIntensionalSimilarityITV,
      Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

noncomputable def fixtureProductRule (a b : ℝ) : ℝ :=
  a * b

theorem fixtureProductRule_monotone_on_unit :
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.BinaryRuleMonotoneOnUnit
      fixtureProductRule := by
  intro a₁ a₂ b₁ b₂ ha₁_nonneg _ha₂_le_one hb₁_nonneg _hb₂_le_one ha hb
  unfold fixtureProductRule
  have ha₂_nonneg : 0 ≤ a₂ := le_trans ha₁_nonneg ha
  calc
    a₁ * b₁ ≤ a₂ * b₁ := mul_le_mul_of_nonneg_right ha hb₁_nonneg
    _ ≤ a₂ * b₂ := mul_le_mul_of_nonneg_left hb ha₂_nonneg

theorem canary_hol_binaryRuleProduct_predicateSimilarityTopBot_two_completion_bounds :
    let I :=
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaBinaryRuleInterval
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureTwoCompletionCredalFamily fixturePredTopBotIff fixturePredTopBotIff fixtureProductRule
        fixtureProductRule_monotone_on_unit
    I.lower = 0 ∧ I.upper = 1 := by
  have hFalse :
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
        (fixtureTwoCompletionCredalFamily false) fixturePredTopBotIff = 0 := by
    change
      (Mettapedia.Logic.PLNHigherOrderHOLProbabilisticBridge.hierarchicalPredicateSimilarityStrength
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureHierarchicalState FixtureObjTy fixturePredTop fixturePredBot).toReal = 0
    rw [canary_hol_hierarchicalPredicateSimilarityTopBot_strength_zero]
    simp
  have hTrue :
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
        (fixtureTwoCompletionCredalFamily true) fixturePredTopBotIff = 1 := by
    change
      (Mettapedia.Logic.PLNHigherOrderHOLProbabilisticBridge.hierarchicalPredicateSimilarityStrength
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureEmptyHierarchicalState FixtureObjTy fixturePredTop fixturePredBot).toReal = 1
    rw [canary_hol_empty_hierarchicalPredicateSimilarityTopBot_strength_one]
    simp
  have hRuleFalse :
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaBinaryRuleValue
        (fixtureTwoCompletionCredalFamily false) fixturePredTopBotIff fixturePredTopBotIff
          fixtureProductRule = 0 := by
    unfold Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaBinaryRuleValue
      fixtureProductRule
    rw [hFalse]
    norm_num
  have hRuleTrue :
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaBinaryRuleValue
        (fixtureTwoCompletionCredalFamily true) fixturePredTopBotIff fixturePredTopBotIff
          fixtureProductRule = 1 := by
    unfold Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaBinaryRuleValue
      fixtureProductRule
    rw [hTrue]
    norm_num
  have hRange :
      Set.range
          (fun i =>
            Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaBinaryRuleValue
              (fixtureTwoCompletionCredalFamily i) fixturePredTopBotIff
              fixturePredTopBotIff fixtureProductRule) =
        ({0, 1} : Set ℝ) := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩
      cases i
      · exact Or.inl hRuleFalse
      · exact Or.inr hRuleTrue
    · intro hr
      simp at hr
      rcases hr with h0 | h1
      · exact ⟨false, by
          change
            Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaBinaryRuleValue
              (fixtureTwoCompletionCredalFamily false) fixturePredTopBotIff
              fixturePredTopBotIff fixtureProductRule = r
          rw [hRuleFalse, ← h0]⟩
      · exact ⟨true, by
          change
            Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaBinaryRuleValue
              (fixtureTwoCompletionCredalFamily true) fixturePredTopBotIff
              fixturePredTopBotIff fixtureProductRule = r
          rw [hRuleTrue, ← h1]⟩
  constructor
  · unfold Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaBinaryRuleInterval
    dsimp [Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.IntervalAddSemantics.intervalOf]
    rw [hRange]
    simp
  · unfold Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaBinaryRuleInterval
    dsimp [Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.IntervalAddSemantics.intervalOf]
    rw [hRange]
    simp

theorem canary_hol_binaryRuleProduct_predicateSimilarityTopBot_two_completion_ITV :
    let tv :=
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaBinaryRuleITV
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureTwoCompletionCredalFamily fixturePredTopBotIff fixturePredTopBotIff
        fixtureProductRule
        fixtureProductRule_monotone_on_unit
        (by simp [fixtureProductRule]) (by simp [fixtureProductRule])
        (1 / 2 : ℝ) fixtureHalfCredibility
    tv.lower = 0 ∧ tv.upper = 1 ∧ tv.credibility = 1 / 2 := by
  have hBounds :=
    canary_hol_binaryRuleProduct_predicateSimilarityTopBot_two_completion_bounds
  dsimp
  constructor
  · simpa using hBounds.1
  constructor
  · simpa using hBounds.2
  · simp [
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaBinaryRuleITV,
      Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

theorem canary_hol_finiteRuleProduct_singleton_multiJoin_width_zero :
    let I :=
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaFiniteRuleInterval
        (Base := FixtureBase) (Const := FixtureConst)
        (fun _ : Unit => fixtureHierarchicalState)
        (fun _ : Fin 2 => fixturePredTopBotIff)
        (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.binaryRuleAsFinite2
          fixtureProductRule)
        (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.binaryRuleAsFinite2_monotone_on_unit
          fixtureProductRule fixtureProductRule_monotone_on_unit)
    I.width = 0 := by
  dsimp
  rw [
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaFiniteRuleInterval_eq_const_of_subsingleton
      (Base := FixtureBase) (Const := FixtureConst)
      (fun _ : Unit => fixtureHierarchicalState)
      ()
      (fun _ : Fin 2 => fixturePredTopBotIff)
      (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.binaryRuleAsFinite2
        fixtureProductRule)
      (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.binaryRuleAsFinite2_monotone_on_unit
        fixtureProductRule fixtureProductRule_monotone_on_unit)]
  simp [
    Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.Interval.width,
    Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.constInterval]

theorem canary_hol_productMultiJoin_singleton_width_zero :
    let I :=
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaProductMultiJoinInterval
        (Base := FixtureBase) (Const := FixtureConst)
        (fun _ : Unit => fixtureHierarchicalState)
        (fun _ : Fin 2 => fixturePredTopBotIff)
    I.width = 0 := by
  dsimp [
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaProductMultiJoinInterval]
  rw [
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaFiniteRuleInterval_eq_const_of_subsingleton
      (Base := FixtureBase) (Const := FixtureConst)
      (fun _ : Unit => fixtureHierarchicalState)
      ()
      (fun _ : Fin 2 => fixturePredTopBotIff)
      (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.productMultiJoin)
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.productMultiJoin_monotone_on_unit]
  simp [
    Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.Interval.width,
    Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.constInterval]

theorem canary_hol_noisyOrMultiJoin_singleton_width_zero :
    let I :=
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaNoisyOrMultiJoinInterval
        (Base := FixtureBase) (Const := FixtureConst)
        (fun _ : Unit => fixtureHierarchicalState)
        (fun _ : Fin 2 => fixturePredTopBotIff)
    I.width = 0 := by
  dsimp [
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaNoisyOrMultiJoinInterval]
  rw [
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaFiniteRuleInterval_eq_const_of_subsingleton
      (Base := FixtureBase) (Const := FixtureConst)
      (fun _ : Unit => fixtureHierarchicalState)
      ()
      (fun _ : Fin 2 => fixturePredTopBotIff)
      (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.noisyOrMultiJoin)
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.noisyOrMultiJoin_monotone_on_unit]
  simp [
    Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.Interval.width,
    Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.constInterval]

theorem canary_hol_noisyOrMultiJoin_kyburg_join_value_zero :
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaFiniteRuleValue
      fixtureHierarchicalState
      (fun _ : Fin 2 => fixturePredTopBotIff)
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.noisyOrMultiJoin = 0 := by
  have hValue :
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
        fixtureHierarchicalState fixturePredTopBotIff = 0 := by
    change
      (Mettapedia.Logic.PLNHigherOrderHOLProbabilisticBridge.hierarchicalPredicateSimilarityStrength
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureHierarchicalState FixtureObjTy fixturePredTop fixturePredBot).toReal = 0
    rw [canary_hol_hierarchicalPredicateSimilarityTopBot_strength_zero]
    simp
  have hJoin :
      (sentenceProb fixtureHierarchicalState.baseSpace
        (MeasureTheory.Measure.join
          (fixtureHierarchicalState.pd.mixingMeasure.map
            fixtureHierarchicalState.pd.kernel))
        fixturePredTopBotIff).toReal = 0 := by
    simpa [
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue_eq_toReal_sentenceProb_kyburg_join]
      using hValue
  rw [
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaFiniteRuleValue_eq_rule_on_kyburg_join]
  simp [Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.noisyOrMultiJoin]
  rw [hJoin]
  norm_num

theorem canary_hol_credalHOLFormulaValue_not_topBotIff_eq_one :
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
      fixtureHierarchicalState (.not fixturePredTopBotIff) = 1 := by
  rw [
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue_not_eq_one_sub]
  have hValue :
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
        fixtureHierarchicalState fixturePredTopBotIff = 0 := by
    change
      (Mettapedia.Logic.PLNHigherOrderHOLProbabilisticBridge.hierarchicalPredicateSimilarityStrength
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureHierarchicalState FixtureObjTy fixturePredTop fixturePredBot).toReal = 0
    rw [canary_hol_hierarchicalPredicateSimilarityTopBot_strength_zero]
    simp
  rw [hValue]
  norm_num

theorem canary_hol_noisyOrMultiJoin_formula_not_dual_value :
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaFiniteRuleValue.{0,0,0,0}
      fixtureHierarchicalState
      (fun _ : Fin 2 => fixturePredTopBotIff)
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.noisyOrMultiJoin =
        1 -
          Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaFiniteRuleValue.{0,0,0,0}
            fixtureHierarchicalState
            (fun k : Fin 2 =>
              (.not ((fun _ : Fin 2 => fixturePredTopBotIff) k) : ClosedFormula FixtureConst))
            Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.productMultiJoin := by
  exact
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaFiniteRuleValue_noisyOr_eq_one_sub_productMultiJoin_not.{0,0,0,0}
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureHierarchicalState (fun _ : Fin 2 => fixturePredTopBotIff)

theorem canary_hol_credalHOLFormulaInterval_not_endpoint_dual_lower :
    (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaInterval.{0,0,0,0,0}
      fixtureTwoCompletionCredalFamily (.not fixturePredTopBotIff)).lower =
        1 -
          (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaInterval.{0,0,0,0,0}
            fixtureTwoCompletionCredalFamily fixturePredTopBotIff).upper := by
  exact
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaInterval_not_lower_eq_one_sub_upper.{0,0,0,0,0}
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureTwoCompletionCredalFamily fixturePredTopBotIff

theorem canary_hol_credalHOLFormulaInterval_not_endpoint_dual_upper :
    (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaInterval.{0,0,0,0,0}
      fixtureTwoCompletionCredalFamily (.not fixturePredTopBotIff)).upper =
        1 -
          (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaInterval.{0,0,0,0,0}
            fixtureTwoCompletionCredalFamily fixturePredTopBotIff).lower := by
  exact
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaInterval_not_upper_eq_one_sub_lower.{0,0,0,0,0}
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureTwoCompletionCredalFamily fixturePredTopBotIff

theorem canary_hol_noisyOrMultiJoin_hull_formula_not_dual_lower :
    (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaNoisyOrMultiJoinHull.{0,0,0,0,0}
      fixtureTwoCompletionCredalFamily
      (fun _ : Fin 2 => fixturePredTopBotIff)).lower =
        1 -
          (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaProductMultiJoinHull.{0,0,0,0,0}
            fixtureTwoCompletionCredalFamily
            (fun k : Fin 2 =>
              (.not ((fun _ : Fin 2 => fixturePredTopBotIff) k) : ClosedFormula FixtureConst))).upper := by
  exact
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaNoisyOrMultiJoinHull_lower_eq_one_sub_product_not_upper.{0,0,0,0,0}
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureTwoCompletionCredalFamily (fun _ : Fin 2 => fixturePredTopBotIff)

theorem canary_hol_noisyOrMultiJoin_hull_formula_not_dual_upper :
    (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaNoisyOrMultiJoinHull.{0,0,0,0,0}
      fixtureTwoCompletionCredalFamily
      (fun _ : Fin 2 => fixturePredTopBotIff)).upper =
        1 -
          (Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaProductMultiJoinHull.{0,0,0,0,0}
            fixtureTwoCompletionCredalFamily
            (fun k : Fin 2 =>
              (.not ((fun _ : Fin 2 => fixturePredTopBotIff) k) : ClosedFormula FixtureConst))).lower := by
  exact
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaNoisyOrMultiJoinHull_upper_eq_one_sub_product_not_lower.{0,0,0,0,0}
      (Base := FixtureBase) (Const := FixtureConst)
      fixtureTwoCompletionCredalFamily (fun _ : Fin 2 => fixturePredTopBotIff)

noncomputable def fixtureTriProductRule (xs : Fin 3 → ℝ) : ℝ :=
  xs 0 * xs 1 * xs 2

theorem fixtureTriProductRule_monotone_on_unit :
    Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.FiniteRuleMonotoneOnUnit
      fixtureTriProductRule := by
  intro a b ha_nonneg _hb_le_one hle
  unfold fixtureTriProductRule
  have hb0_nonneg : 0 ≤ b 0 := le_trans (ha_nonneg 0) (hle 0)
  have hb1_nonneg : 0 ≤ b 1 := le_trans (ha_nonneg 1) (hle 1)
  have hab01 : a 0 * a 1 ≤ b 0 * b 1 := by
    exact mul_le_mul (hle 0) (hle 1) (ha_nonneg 1) hb0_nonneg
  have hb01_nonneg : 0 ≤ b 0 * b 1 :=
    mul_nonneg hb0_nonneg hb1_nonneg
  exact mul_le_mul hab01 (hle 2) (ha_nonneg 2) hb01_nonneg

theorem canary_hol_finiteRuleTriProduct_predicateSimilarityTopBot_two_completion_bounds :
    let I :=
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaFiniteRuleInterval
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureTwoCompletionCredalFamily
        (fun _ : Fin 3 => fixturePredTopBotIff)
        fixtureTriProductRule
        fixtureTriProductRule_monotone_on_unit
    I.lower = 0 ∧ I.upper = 1 := by
  have hFalse :
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
        (fixtureTwoCompletionCredalFamily false) fixturePredTopBotIff = 0 := by
    change
      (Mettapedia.Logic.PLNHigherOrderHOLProbabilisticBridge.hierarchicalPredicateSimilarityStrength
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureHierarchicalState FixtureObjTy fixturePredTop fixturePredBot).toReal = 0
    rw [canary_hol_hierarchicalPredicateSimilarityTopBot_strength_zero]
    simp
  have hTrue :
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
        (fixtureTwoCompletionCredalFamily true) fixturePredTopBotIff = 1 := by
    change
      (Mettapedia.Logic.PLNHigherOrderHOLProbabilisticBridge.hierarchicalPredicateSimilarityStrength
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureEmptyHierarchicalState FixtureObjTy fixturePredTop fixturePredBot).toReal = 1
    rw [canary_hol_empty_hierarchicalPredicateSimilarityTopBot_strength_one]
    simp
  have hRuleFalse :
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaFiniteRuleValue
        (fixtureTwoCompletionCredalFamily false)
        (fun _ : Fin 3 => fixturePredTopBotIff)
        fixtureTriProductRule = 0 := by
    unfold Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaFiniteRuleValue
      fixtureTriProductRule
    change
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
        (fixtureTwoCompletionCredalFamily false) fixturePredTopBotIff *
        Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
          (fixtureTwoCompletionCredalFamily false) fixturePredTopBotIff *
          Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
            (fixtureTwoCompletionCredalFamily false) fixturePredTopBotIff = 0
    rw [hFalse]
    norm_num
  have hRuleTrue :
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaFiniteRuleValue
        (fixtureTwoCompletionCredalFamily true)
        (fun _ : Fin 3 => fixturePredTopBotIff)
        fixtureTriProductRule = 1 := by
    unfold Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaFiniteRuleValue
      fixtureTriProductRule
    change
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
        (fixtureTwoCompletionCredalFamily true) fixturePredTopBotIff *
        Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
          (fixtureTwoCompletionCredalFamily true) fixturePredTopBotIff *
          Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaValue
            (fixtureTwoCompletionCredalFamily true) fixturePredTopBotIff = 1
    rw [hTrue]
    norm_num
  have hRange :
      Set.range
          (fun i =>
            Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaFiniteRuleValue
              (fixtureTwoCompletionCredalFamily i)
              (fun _ : Fin 3 => fixturePredTopBotIff)
              fixtureTriProductRule) =
        ({0, 1} : Set ℝ) := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩
      cases i
      · exact Or.inl hRuleFalse
      · exact Or.inr hRuleTrue
    · intro hr
      simp at hr
      rcases hr with h0 | h1
      · exact ⟨false, by
          change
            Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaFiniteRuleValue
              (fixtureTwoCompletionCredalFamily false)
              (fun _ : Fin 3 => fixturePredTopBotIff)
              fixtureTriProductRule = r
          rw [hRuleFalse, ← h0]⟩
      · exact ⟨true, by
          change
            Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaFiniteRuleValue
              (fixtureTwoCompletionCredalFamily true)
              (fun _ : Fin 3 => fixturePredTopBotIff)
              fixtureTriProductRule = r
          rw [hRuleTrue, ← h1]⟩
  constructor
  · unfold Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaFiniteRuleInterval
    dsimp [Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.IntervalAddSemantics.intervalOf]
    rw [hRange]
    simp
  · unfold Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaFiniteRuleInterval
    dsimp [Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets.IntervalAddSemantics.intervalOf]
    rw [hRange]
    simp

theorem canary_hol_finiteRuleTriProduct_predicateSimilarityTopBot_two_completion_ITV :
    let tv :=
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaFiniteRuleITV
        (Base := FixtureBase) (Const := FixtureConst)
        fixtureTwoCompletionCredalFamily
        (fun _ : Fin 3 => fixturePredTopBotIff)
        fixtureTriProductRule
        fixtureTriProductRule_monotone_on_unit
        (by simp [fixtureTriProductRule]) (by simp [fixtureTriProductRule])
        (1 / 2 : ℝ) fixtureHalfCredibility
    tv.lower = 0 ∧ tv.upper = 1 ∧ tv.credibility = 1 / 2 := by
  have hBounds :=
    canary_hol_finiteRuleTriProduct_predicateSimilarityTopBot_two_completion_bounds
  dsimp
  constructor
  · simpa using hBounds.1
  constructor
  · simpa using hBounds.2
  · simp [
      Mettapedia.Logic.PLNHigherOrderHOLCredalBridge.credalHOLFormulaFiniteRuleITV,
      Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

end Mettapedia.Logic.PLNHigherOrderHOLCanary
