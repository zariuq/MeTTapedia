import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ClosedTermPreModelBridge

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ClosedTermPreModelBridgeRegression

open Mettapedia.Logic.HOL
open Mettapedia.PLN.WorldModel.PLNWorldModel
open ClosedTermCanonicalWorldModel
open scoped ENNReal

inductive TestBase where
  | atom
deriving DecidableEq, Repr

inductive TestConst : Ty TestBase → Type where
  | a : TestConst (.base .atom)
  | f : TestConst (.base .atom ⇒ .base .atom)

abbrev TestTheory : ClosedTheorySet TestConst := ∅

theorem realizedArrowAdmissible_eqvArgumentCongruent_canary
    (M : HenkinModel TestBase TestConst)
    (hReal : RealizedArrowAdmissible M) :
    EqvArgumentCongruent M :=
  realizedArrowAdmissible_eqvArgumentCongruent hReal

theorem realizedArrowAdmissible_iff_eqvArgumentCongruent_canary
    (M : HenkinModel TestBase TestConst) :
    RealizedArrowAdmissible M ↔ EqvArgumentCongruent M :=
  realizedArrowAdmissible_iff_eqvArgumentCongruent

theorem representsClosedTerm_denote_canary
    (M : HenkinModel TestBase TestConst)
    {τ : Ty TestBase} (t : ClosedTerm TestConst τ) :
    ClosedTermPreModelBridge.RepresentsClosedTerm M t
      (HenkinModel.denote M t (ClosedTermPreModelBridge.emptyValuation M)) :=
  ClosedTermPreModelBridge.representsClosedTerm_denote M t

theorem representedValue_denote_canary
    (M : HenkinModel TestBase TestConst)
    {τ : Ty TestBase} (t : ClosedTerm TestConst τ) :
    ClosedTermPreModelBridge.RepresentedValue M
      (HenkinModel.denote M t (ClosedTermPreModelBridge.emptyValuation M)) :=
  ClosedTermPreModelBridge.representedValue_denote M t

theorem representsClosedTerm_admissible_canary
    (M : HenkinModel TestBase TestConst)
    {τ : Ty TestBase} {t : ClosedTerm TestConst τ}
    {x : Ty.denote M.Carrier τ}
    (hx : ClosedTermPreModelBridge.RepresentsClosedTerm M t x) :
    M.adm τ x :=
  ClosedTermPreModelBridge.representsClosedTerm_admissible (M := M) hx

theorem representedValue_admissible_canary
    (M : HenkinModel TestBase TestConst)
    {τ : Ty TestBase} {x : Ty.denote M.Carrier τ}
    (hx : ClosedTermPreModelBridge.RepresentedValue M x) :
    M.adm τ x :=
  ClosedTermPreModelBridge.representedValue_admissible (M := M) hx

theorem representsClosedTerm_app_canary
    (M : HenkinModel TestBase TestConst)
    {σ τ : Ty TestBase}
    {F : ClosedTerm TestConst (σ ⇒ τ)}
    {t : ClosedTerm TestConst σ}
    {f : Ty.denote M.Carrier (σ ⇒ τ)}
    {x : Ty.denote M.Carrier σ}
    (hF : ClosedTermPreModelBridge.RepresentsClosedTerm M F f)
    (hx : ClosedTermPreModelBridge.RepresentsClosedTerm M t x) :
    ClosedTermPreModelBridge.RepresentsClosedTerm M (.app F t) (f x) :=
  ClosedTermPreModelBridge.representsClosedTerm_app (M := M) hF hx

theorem quotientRealization_representedValue_canary
    (M : HenkinModel TestBase TestConst)
    {T : ClosedTheorySet TestConst}
    (R : ClosedTermPreModelBridge.QuotientRealization M T)
    {τ : Ty TestBase} {x : Ty.denote M.Carrier τ}
    (hx : M.adm τ x) :
    ClosedTermPreModelBridge.RepresentedValue M x :=
  ClosedTermPreModelBridge.quotientRealization_representedValue
    (M := M) R hx

theorem quotientRealization_reflects_closedTermEq_canary
    (M : HenkinModel TestBase TestConst)
    {T : ClosedTheorySet TestConst}
    (R : ClosedTermPreModelBridge.QuotientRealization M T)
    {τ : Ty TestBase}
    {t u : ClosedTerm TestConst τ}
    {x y : Ty.denote M.Carrier τ}
    (hx : ClosedTermPreModelBridge.RepresentsClosedTerm M t x)
    (hy : ClosedTermPreModelBridge.RepresentsClosedTerm M u y)
    (hxy : PreModel.Eqv M.toPreModel τ x y) :
    ClosedTermEq T t u :=
  ClosedTermPreModelBridge.quotientRealization_reflects_closedTermEq
    (M := M) R hx hy hxy

theorem quotientRealization_closedTermEq_sound_canary
    (M : HenkinModel TestBase TestConst)
    {T : ClosedTheorySet TestConst}
    (R : ClosedTermPreModelBridge.QuotientRealization M T)
    {τ : Ty TestBase}
    {t u : ClosedTerm TestConst τ}
    {x y : Ty.denote M.Carrier τ}
    (hx : ClosedTermPreModelBridge.RepresentsClosedTerm M t x)
    (hy : ClosedTermPreModelBridge.RepresentsClosedTerm M u y)
    (htu : ClosedTermEq T t u) :
    PreModel.Eqv M.toPreModel τ x y :=
  ClosedTermPreModelBridge.quotientRealization_closedTermEq_sound
    (M := M) R hx hy htu

theorem quotientRealization_propTruth_to_represented_down_canary
    (M : HenkinModel TestBase TestConst)
    {T : ClosedTheorySet TestConst}
    (R : ClosedTermPreModelBridge.QuotientRealization M T)
    {p : ClosedFormula TestConst}
    {x : Ty.denote M.Carrier propTy}
    (hx : ClosedTermPreModelBridge.RepresentsClosedTerm M p x)
    (hp : ClosedTermEq.propTruth (T := T) (ClosedTermEq.classOf p)) :
    x.down :=
  ClosedTermPreModelBridge.quotientRealization_propTruth_to_represented_down
    (M := M) R hx hp

theorem quotientRealization_represented_down_to_propTruth_canary
    (M : HenkinModel TestBase TestConst)
    {T : ClosedTheorySet TestConst}
    (R : ClosedTermPreModelBridge.QuotientRealization M T)
    {p : ClosedFormula TestConst}
    {x : Ty.denote M.Carrier propTy}
    (hx : ClosedTermPreModelBridge.RepresentsClosedTerm M p x)
    (hpx : x.down) :
    ClosedTermEq.propTruth (T := T) (ClosedTermEq.classOf p) :=
  ClosedTermPreModelBridge.quotientRealization_represented_down_to_propTruth
    (M := M) R hx hpx

theorem quotientRealization_propTruth_iff_represented_down_canary
    (M : HenkinModel TestBase TestConst)
    {T : ClosedTheorySet TestConst}
    (R : ClosedTermPreModelBridge.QuotientRealization M T)
    {p : ClosedFormula TestConst}
    {x : Ty.denote M.Carrier propTy}
    (hx : ClosedTermPreModelBridge.RepresentsClosedTerm M p x) :
    ClosedTermEq.propTruth (T := T) (ClosedTermEq.classOf p) ↔ x.down :=
  ClosedTermPreModelBridge.quotientRealization_propTruth_iff_represented_down
    (M := M) R hx

theorem quotientRealization_models_iff_propTruth_canary
    (M : HenkinModel TestBase TestConst)
    {T : ClosedTheorySet TestConst}
    (R : ClosedTermPreModelBridge.QuotientRealization M T)
    (p : ClosedFormula TestConst) :
    HenkinModel.models M p ↔
      ClosedTermEq.propTruth (T := T) (ClosedTermEq.classOf p) :=
  ClosedTermPreModelBridge.quotientRealization_models_iff_propTruth
    (M := M) R p

theorem quotientRealization_models_iff_world_mem_canary
    (M : HenkinModel TestBase TestConst)
    (W : ClosedTheorySet.World TestConst)
    (R : ClosedTermPreModelBridge.QuotientRealization M W.carrier)
    (p : ClosedFormula TestConst) :
    HenkinModel.models M p ↔ p ∈ W.carrier :=
  ClosedTermPreModelBridge.quotientRealization_models_iff_world_mem
    (M := M) W R p

theorem quotientRealization_modelsClosedTheorySet_world_canary
    (M : HenkinModel TestBase TestConst)
    (W : ClosedTheorySet.World TestConst)
    (R : ClosedTermPreModelBridge.QuotientRealization M W.carrier) :
    ModelsClosedTheorySet M W.carrier :=
  ClosedTermPreModelBridge.quotientRealization_modelsClosedTheorySet_world
    (M := M) W R

theorem quotientRealization_not_models_of_world_not_mem_canary
    (M : HenkinModel TestBase TestConst)
    (W : ClosedTheorySet.World TestConst)
    (R : ClosedTermPreModelBridge.QuotientRealization M W.carrier)
    {p : ClosedFormula TestConst}
    (hp : p ∉ W.carrier) :
    ¬ HenkinModel.models M p :=
  ClosedTermPreModelBridge.quotientRealization_not_models_of_world_not_mem
    (M := M) W R hp

theorem quotientRealization_models_iff_singleton_strength_one_canary
    (M : HenkinModel TestBase TestConst)
    (W : ClosedTheorySet.World TestConst)
    (R : ClosedTermPreModelBridge.QuotientRealization M W.carrier)
    (p : ClosedFormula TestConst) :
    HenkinModel.models M p ↔
      BinaryWorldModel.queryStrength
          (State := Multiset (ClosedTheorySet.World TestConst))
          (Query := CanonicalQuery TestConst)
          ({W} : Multiset (ClosedTheorySet.World TestConst)) p = 1 :=
  ClosedTermPreModelBridge.quotientRealization_models_iff_singleton_strength_one
    (M := M) W R p

theorem quotientRealization_not_models_iff_singleton_strength_zero_canary
    (M : HenkinModel TestBase TestConst)
    (W : ClosedTheorySet.World TestConst)
    (R : ClosedTermPreModelBridge.QuotientRealization M W.carrier)
    (p : ClosedFormula TestConst) :
    ¬ HenkinModel.models M p ↔
      BinaryWorldModel.queryStrength
          (State := Multiset (ClosedTheorySet.World TestConst))
          (Query := CanonicalQuery TestConst)
          ({W} : Multiset (ClosedTheorySet.World TestConst)) p = 0 :=
  ClosedTermPreModelBridge.quotientRealization_not_models_iff_singleton_strength_zero
    (M := M) W R p

theorem quotientRealization_representedCarrierLaws_canary
    (M : HenkinModel TestBase TestConst)
    {T : ClosedTheorySet TestConst}
    (R : ClosedTermPreModelBridge.QuotientRealization M T) :
    ClosedTermPreModelBridge.RepresentedCarrierLaws M T :=
  ClosedTermPreModelBridge.quotientRealization_representedCarrierLaws
    (M := M) R

theorem quotientRealization_realizedArrowAdmissible_canary
    (M : HenkinModel TestBase TestConst)
    {T : ClosedTheorySet TestConst}
    (R : ClosedTermPreModelBridge.QuotientRealization M T) :
    RealizedArrowAdmissible M :=
  ClosedTermPreModelBridge.quotientRealization_realizedArrowAdmissible
    (M := M) R

theorem quotientRealization_eqvArgumentCongruent_canary
    (M : HenkinModel TestBase TestConst)
    {T : ClosedTheorySet TestConst}
    (R : ClosedTermPreModelBridge.QuotientRealization M T) :
    EqvArgumentCongruent M :=
  ClosedTermPreModelBridge.quotientRealization_eqvArgumentCongruent
    (M := M) R

theorem extDerivation_sound_of_quotientRealization_canary
    (M : HenkinModel TestBase TestConst)
    {T : ClosedTheorySet TestConst}
    (R : ClosedTermPreModelBridge.QuotientRealization M T)
    {Γ : Ctx TestBase} {Δ : List (Formula TestConst Γ)}
    {φ : Formula TestConst Γ}
    (d : ExtDerivation TestConst Δ φ) :
    ∀ {ρ : HenkinModel.Valuation M Γ},
      HenkinModel.ValuationAdmissible M ρ →
      Soundness.SatisfiesHyps M ρ Δ →
      (HenkinModel.denote M φ ρ).down :=
  ClosedTermPreModelBridge.extDerivation_sound_of_quotientRealization
    (M := M) R d

theorem closedTheorySet_provable_sound_of_quotientRealization_canary
    (M : HenkinModel TestBase TestConst)
    {T : ClosedTheorySet TestConst}
    (R : ClosedTermPreModelBridge.QuotientRealization M T)
    (hT : ModelsClosedTheorySet M T)
    {φ : ClosedFormula TestConst}
    (hφ : ClosedTheorySet.Provable T φ) :
    HenkinModel.models M φ :=
  ClosedTermPreModelBridge.closedTheorySet_provable_sound_of_quotientRealization
    (M := M) R hT hφ

theorem closedTheorySet_provable_eq_to_preModel_eqv_of_quotientRealization_canary
    (M : HenkinModel TestBase TestConst)
    {T : ClosedTheorySet TestConst}
    (R : ClosedTermPreModelBridge.QuotientRealization M T)
    (hT : ModelsClosedTheorySet M T)
    {τ : Ty TestBase}
    {t u : ClosedTerm TestConst τ}
    (hEq : ClosedTheorySet.Provable (Const := TestConst) T (.eq t u)) :
    PreModel.Eqv M.toPreModel τ
      (HenkinModel.denote M t (ClosedTermPreModelBridge.emptyValuation M))
      (HenkinModel.denote M u (ClosedTermPreModelBridge.emptyValuation M)) :=
  ClosedTermPreModelBridge.closedTheorySet_provable_eq_to_preModel_eqv_of_quotientRealization
    (M := M) R hT hEq

theorem closedTermEq_to_preModel_eqv_of_quotientRealization_canary
    (M : HenkinModel TestBase TestConst)
    {T : ClosedTheorySet TestConst}
    (R : ClosedTermPreModelBridge.QuotientRealization M T)
    (hT : ModelsClosedTheorySet M T)
    {τ : Ty TestBase}
    {t u : ClosedTerm TestConst τ}
    (hEq : ClosedTermEq T t u) :
    PreModel.Eqv M.toPreModel τ
      (HenkinModel.denote M t (ClosedTermPreModelBridge.emptyValuation M))
      (HenkinModel.denote M u (ClosedTermPreModelBridge.emptyValuation M)) :=
  ClosedTermPreModelBridge.closedTermEq_to_preModel_eqv_of_quotientRealization
    (M := M) R hT hEq

theorem represented_closedTermEq_to_preModel_eqv_of_quotientRealization_canary
    (M : HenkinModel TestBase TestConst)
    {T : ClosedTheorySet TestConst}
    (R : ClosedTermPreModelBridge.QuotientRealization M T)
    (hT : ModelsClosedTheorySet M T)
    {τ : Ty TestBase}
    {t u : ClosedTerm TestConst τ}
    {x y : Ty.denote M.Carrier τ}
    (hx : ClosedTermPreModelBridge.RepresentsClosedTerm M t x)
    (hy : ClosedTermPreModelBridge.RepresentsClosedTerm M u y)
    (hEq : ClosedTermEq T t u) :
    PreModel.Eqv M.toPreModel τ x y :=
  ClosedTermPreModelBridge.represented_closedTermEq_to_preModel_eqv_of_quotientRealization
    (M := M) R hT hx hy hEq

theorem representedCarrierLaws_realizedArrowAdmissible_canary
    (M : HenkinModel TestBase TestConst)
    {T : ClosedTheorySet TestConst}
    (h : ClosedTermPreModelBridge.RepresentedCarrierLaws M T) :
    RealizedArrowAdmissible M :=
  ClosedTermPreModelBridge.representedCarrierLaws_realizedArrowAdmissible
    (M := M) h

theorem representedCarrierLaws_eqvArgumentCongruent_canary
    (M : HenkinModel TestBase TestConst)
    {T : ClosedTheorySet TestConst}
    (h : ClosedTermPreModelBridge.RepresentedCarrierLaws M T) :
    EqvArgumentCongruent M :=
  ClosedTermPreModelBridge.representedCarrierLaws_eqvArgumentCongruent
    (M := M) h

theorem extDerivation_sound_of_representedCarrierLaws_canary
    (M : HenkinModel TestBase TestConst)
    {T : ClosedTheorySet TestConst}
    (h : ClosedTermPreModelBridge.RepresentedCarrierLaws M T)
    {Γ : Ctx TestBase} {Δ : List (Formula TestConst Γ)}
    {φ : Formula TestConst Γ}
    (d : ExtDerivation TestConst Δ φ) :
    ∀ {ρ : HenkinModel.Valuation M Γ},
      HenkinModel.ValuationAdmissible M ρ →
      Soundness.SatisfiesHyps M ρ Δ →
      (HenkinModel.denote M φ ρ).down :=
  ClosedTermPreModelBridge.extDerivation_sound_of_representedCarrierLaws
    (M := M) h d

theorem closedTheorySet_provable_eq_to_preModel_eqv_shape_canary
    (M : HenkinModel TestBase TestConst)
    (hArg : EqvArgumentCongruent M)
    (hT : ModelsClosedTheorySet M TestTheory)
    {τ : Ty TestBase}
    {t u : ClosedTerm TestConst τ}
    (hEq : ClosedTheorySet.Provable (Const := TestConst) TestTheory (.eq t u)) :
    PreModel.Eqv M.toPreModel τ
      (HenkinModel.denote M t (ClosedTermPreModelBridge.emptyValuation M))
      (HenkinModel.denote M u (ClosedTermPreModelBridge.emptyValuation M)) :=
  ClosedTermPreModelBridge.closedTheorySet_provable_eq_to_preModel_eqv
    (M := M) hArg hT hEq

theorem closedTermEq_to_preModel_eqv_shape_canary
    (M : HenkinModel TestBase TestConst)
    (hArg : EqvArgumentCongruent M)
    (hT : ModelsClosedTheorySet M TestTheory)
    {τ : Ty TestBase}
    {t u : ClosedTerm TestConst τ}
    (hEq : ClosedTermEq TestTheory t u) :
    PreModel.Eqv M.toPreModel τ
      (HenkinModel.denote M t (ClosedTermPreModelBridge.emptyValuation M))
      (HenkinModel.denote M u (ClosedTermPreModelBridge.emptyValuation M)) :=
  ClosedTermPreModelBridge.closedTermEq_to_preModel_eqv
    (M := M) hArg hT hEq

theorem closedTermEq_to_preModel_eqv_of_representedCarrierLaws_canary
    (M : HenkinModel TestBase TestConst)
    {T : ClosedTheorySet TestConst}
    (hLaws : ClosedTermPreModelBridge.RepresentedCarrierLaws M T)
    (hT : ModelsClosedTheorySet M T)
    {τ : Ty TestBase}
    {t u : ClosedTerm TestConst τ}
    (hEq : ClosedTermEq T t u) :
    PreModel.Eqv M.toPreModel τ
      (HenkinModel.denote M t (ClosedTermPreModelBridge.emptyValuation M))
      (HenkinModel.denote M u (ClosedTermPreModelBridge.emptyValuation M)) :=
  ClosedTermPreModelBridge.closedTermEq_to_preModel_eqv_of_representedCarrierLaws
    (M := M) hLaws hT hEq

theorem represented_closedTermEq_to_preModel_eqv_canary
    (M : HenkinModel TestBase TestConst)
    (hArg : EqvArgumentCongruent M)
    (hT : ModelsClosedTheorySet M TestTheory)
    {τ : Ty TestBase}
    {t u : ClosedTerm TestConst τ}
    {x y : Ty.denote M.Carrier τ}
    (hx : ClosedTermPreModelBridge.RepresentsClosedTerm M t x)
    (hy : ClosedTermPreModelBridge.RepresentsClosedTerm M u y)
    (hEq : ClosedTermEq TestTheory t u) :
    PreModel.Eqv M.toPreModel τ x y :=
  ClosedTermPreModelBridge.represented_closedTermEq_to_preModel_eqv
    (M := M) hArg hT hx hy hEq

theorem represented_closedTermEq_to_preModel_eqv_of_representedCarrierLaws_canary
    (M : HenkinModel TestBase TestConst)
    {T : ClosedTheorySet TestConst}
    (hLaws : ClosedTermPreModelBridge.RepresentedCarrierLaws M T)
    (hT : ModelsClosedTheorySet M T)
    {τ : Ty TestBase}
    {t u : ClosedTerm TestConst τ}
    {x y : Ty.denote M.Carrier τ}
    (hx : ClosedTermPreModelBridge.RepresentsClosedTerm M t x)
    (hy : ClosedTermPreModelBridge.RepresentsClosedTerm M u y)
    (hEq : ClosedTermEq T t u) :
    PreModel.Eqv M.toPreModel τ x y :=
  ClosedTermPreModelBridge.represented_closedTermEq_to_preModel_eqv_of_representedCarrierLaws
    (M := M) hLaws hT hx hy hEq

theorem closedTermEq_to_preModel_eqv_of_realizedArrow_canary
    (M : HenkinModel TestBase TestConst)
    (hReal : RealizedArrowAdmissible M)
    (hT : ModelsClosedTheorySet M TestTheory)
    {τ : Ty TestBase}
    {t u : ClosedTerm TestConst τ}
    (hEq : ClosedTermEq TestTheory t u) :
    PreModel.Eqv M.toPreModel τ
      (HenkinModel.denote M t (ClosedTermPreModelBridge.emptyValuation M))
      (HenkinModel.denote M u (ClosedTermPreModelBridge.emptyValuation M)) :=
  ClosedTermPreModelBridge.closedTermEq_to_preModel_eqv_of_realizedArrowAdmissible
    (M := M) hReal hT hEq

theorem represented_closedTermEq_to_preModel_eqv_of_realizedArrow_canary
    (M : HenkinModel TestBase TestConst)
    (hReal : RealizedArrowAdmissible M)
    (hT : ModelsClosedTheorySet M TestTheory)
    {τ : Ty TestBase}
    {t u : ClosedTerm TestConst τ}
    {x y : Ty.denote M.Carrier τ}
    (hx : ClosedTermPreModelBridge.RepresentsClosedTerm M t x)
    (hy : ClosedTermPreModelBridge.RepresentsClosedTerm M u y)
    (hEq : ClosedTermEq TestTheory t u) :
    PreModel.Eqv M.toPreModel τ x y :=
  ClosedTermPreModelBridge.represented_closedTermEq_to_preModel_eqv_of_realizedArrowAdmissible
    (M := M) hReal hT hx hy hEq

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ClosedTermPreModelBridgeRegression
