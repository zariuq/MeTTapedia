import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ClosedTermQuotient

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ClosedTermQuotientRegression

open Mettapedia.Logic.HOL

inductive TestBase where
  | atom
deriving DecidableEq, Repr

inductive TestConst : Ty TestBase → Type where
  | a : TestConst (.base .atom)
  | f : TestConst (.base .atom ⇒ .base .atom)

abbrev TestTheory : ClosedTheorySet TestConst := ∅

theorem closedTermEq_refl_canary :
    ClosedTermEq TestTheory (.const TestConst.a) (.const TestConst.a) :=
  ClosedTermEq.refl TestTheory (.const TestConst.a)

theorem closedTermEq_app_congr_canary :
    ClosedTermEq TestTheory
      (.app (.const TestConst.f) (.const TestConst.a))
      (.app (.const TestConst.f) (.const TestConst.a)) := by
  exact ClosedTermEq.app_congr
    (ClosedTermEq.refl TestTheory (.const TestConst.f))
    (ClosedTermEq.refl TestTheory (.const TestConst.a))

theorem closedTermQuot_appClass_canary :
    ClosedTermEq.appClass (T := TestTheory)
      (ClosedTermEq.classOf (.const TestConst.f))
      (ClosedTermEq.classOf (.const TestConst.a)) =
        ClosedTermEq.classOf
          (T := TestTheory)
          (.app (.const TestConst.f) (.const TestConst.a)) :=
  rfl

theorem closedTermQuot_appClass_beta_canary
    {T : ClosedTheorySet TestConst}
    (body : Term TestConst [(.base .atom)] (.base .atom))
    (t : ClosedTerm TestConst (.base .atom)) :
    ClosedTermEq.appClass (T := T)
        (ClosedTermEq.classOf (.lam body))
        (ClosedTermEq.classOf t) =
      ClosedTermEq.classOf (T := T)
        (instantiate (Base := TestBase) t body) :=
  ClosedTermEq.appClass_beta_classOf body t

theorem closedTermQuot_appClass_eta_canary
    {T : ClosedTheorySet TestConst}
    (f : ClosedTerm TestConst (.base .atom ⇒ .base .atom)) :
    ClosedTermEq.classOf (T := T)
        (.lam
          (.app
            (weaken (Base := TestBase) (σ := .base .atom) f)
            (.var .vz))) =
      ClosedTermEq.classOf (T := T) f :=
  ClosedTermEq.appClass_eta_classOf f

theorem closedTermQuot_respects_representatives_canary
    {T : ClosedTheorySet TestConst}
    {g : ClosedTerm TestConst (.base .atom ⇒ .base .atom)}
    {x : ClosedTerm TestConst (.base .atom)}
    (hg : ClosedTermEq T (.const TestConst.f) g)
    (hx : ClosedTermEq T (.const TestConst.a) x) :
    ClosedTermEq.appClass (T := T)
      (ClosedTermEq.classOf (.const TestConst.f))
      (ClosedTermEq.classOf (.const TestConst.a)) =
        ClosedTermEq.appClass (T := T)
          (ClosedTermEq.classOf g)
          (ClosedTermEq.classOf x) := by
  exact ClosedTermEq.appClass_respects_representatives hg hx

theorem closedTermQuot_appClass_arg_respects_closedTermEq_canary
    {T : ClosedTheorySet TestConst}
    {x y : ClosedTerm TestConst (.base .atom)}
    (hxy : ClosedTermEq T x y) :
    ClosedTermEq.appClass (T := T)
        (ClosedTermEq.classOf (.const TestConst.f))
        (ClosedTermEq.classOf x) =
      ClosedTermEq.appClass (T := T)
        (ClosedTermEq.classOf (.const TestConst.f))
        (ClosedTermEq.classOf y) :=
  ClosedTermEq.appClass_arg_respects_closedTermEq (.const TestConst.f) hxy

theorem closedTermCarrier_eqvArgumentCongruent_canary
    {T : ClosedTheorySet TestConst}
    (f : ClosedTermEq.Quot T (.base .atom ⇒ .base .atom))
    {x y : ClosedTermEq.Quot T (.base .atom)}
    (hxy : x = y) :
    ClosedTermEq.appClass (T := T) f x =
      ClosedTermEq.appClass (T := T) f y :=
  ClosedTermEq.closedTermCarrier_eqvArgumentCongruent f hxy

theorem closedTermQuot_represents_classOf_canary
    {T : ClosedTheorySet TestConst}
    {τ : Ty TestBase}
    (t : ClosedTerm TestConst τ) :
    ClosedTermEq.QuotRepresentsClosedTerm
      (T := T) t (ClosedTermEq.classOf t) :=
  ClosedTermEq.quotRepresentsClosedTerm_classOf (T := T) t

theorem closedTermQuot_represented_value_canary
    {T : ClosedTheorySet TestConst}
    {τ : Ty TestBase}
    (x : ClosedTermEq.Quot T τ) :
    ClosedTermEq.QuotRepresentedValue (T := T) x :=
  ClosedTermEq.quotRepresentedValue x

theorem closedTermQuot_represents_app_canary
    {T : ClosedTheorySet TestConst}
    {σ τ : Ty TestBase}
    {F : ClosedTerm TestConst (σ ⇒ τ)}
    {t : ClosedTerm TestConst σ}
    {f : ClosedTermEq.Quot T (σ ⇒ τ)}
    {x : ClosedTermEq.Quot T σ}
    (hF : ClosedTermEq.QuotRepresentsClosedTerm (T := T) F f)
    (hx : ClosedTermEq.QuotRepresentsClosedTerm (T := T) t x) :
    ClosedTermEq.QuotRepresentsClosedTerm
      (T := T) (.app F t) (ClosedTermEq.appClass f x) :=
  ClosedTermEq.quotRepresentsClosedTerm_app hF hx

theorem closedTermQuot_represented_carrier_laws_canary
    (T : ClosedTheorySet TestConst) :
    ClosedTermEq.QuotRepresentedCarrierLaws T :=
  ClosedTermEq.quotRepresentedCarrierLaws T

theorem closedTermQuot_laws_reflect_eq_canary
    {T : ClosedTheorySet TestConst}
    {τ : Ty TestBase}
    {t u : ClosedTerm TestConst τ}
    {x y : ClosedTermEq.Quot T τ}
    (hx : ClosedTermEq.QuotRepresentsClosedTerm (T := T) t x)
    (hy : ClosedTermEq.QuotRepresentsClosedTerm (T := T) u y)
    (hxy : x = y) :
    ClosedTermEq T t u :=
  (ClosedTermEq.quotRepresentedCarrierLaws T).eq_reflects_closedTermEq
    hx hy hxy

theorem closedTermQuot_laws_sound_eq_canary
    {T : ClosedTheorySet TestConst}
    {τ : Ty TestBase}
    {t u : ClosedTerm TestConst τ}
    {x y : ClosedTermEq.Quot T τ}
    (hx : ClosedTermEq.QuotRepresentsClosedTerm (T := T) t x)
    (hy : ClosedTermEq.QuotRepresentsClosedTerm (T := T) u y)
    (htu : ClosedTermEq T t u) :
    x = y :=
  (ClosedTermEq.quotRepresentedCarrierLaws T).closedTermEq_sound
    hx hy htu

theorem closedTermQuot_laws_realized_arrow_canary
    {T : ClosedTheorySet TestConst} :
    ClosedTermEq.QuotRealizedArrowAdmissible T :=
  ClosedTermEq.quotRepresentedCarrierLaws_realizedArrowAdmissible
    (ClosedTermEq.quotRepresentedCarrierLaws T)

theorem closedTermQuot_realized_arrow_canary
    {T : ClosedTheorySet TestConst}
    (f : ClosedTermEq.Quot T (.base .atom ⇒ .base .atom))
    {x y : ClosedTermEq.Quot T (.base .atom)}
    (hxy : x = y) :
    ClosedTermEq.appClass (T := T) f x =
      ClosedTermEq.appClass (T := T) f y :=
  ClosedTermEq.quotRealizedArrowAdmissible T f hxy

theorem closedTermCarrier_eqvArgumentCongruent_from_laws_canary
    {T : ClosedTheorySet TestConst}
    (f : ClosedTermEq.Quot T (.base .atom ⇒ .base .atom))
    {x y : ClosedTermEq.Quot T (.base .atom)}
    (hxy : x = y) :
    ClosedTermEq.appClass (T := T) f x =
      ClosedTermEq.appClass (T := T) f y :=
  ClosedTermEq.closedTermCarrier_eqvArgumentCongruent_from_laws f hxy

theorem closedTermEq_prop_provable_reflection_canary
    {T : ClosedTheorySet TestConst}
    {p q : ClosedFormula TestConst}
    (hpq : ClosedTermEq T p q) :
    ClosedTheorySet.Provable T p ↔ ClosedTheorySet.Provable T q :=
  ClosedTermEq.prop_provable_iff hpq

theorem closedTermQuot_propTruth_top_canary :
    ClosedTermEq.propTruth
      (T := TestTheory)
      (ClosedTermEq.classOf (.top : ClosedFormula TestConst)) :=
  ClosedTheorySet.Provable.top TestTheory

theorem closedTermQuot_propTruth_respects_representatives_canary
    {T : ClosedTheorySet TestConst}
    {p q : ClosedFormula TestConst}
    (hpq : ClosedTermEq T p q) :
    ClosedTermEq.propTruth (T := T) (ClosedTermEq.classOf p) ↔
      ClosedTermEq.propTruth (T := T) (ClosedTermEq.classOf q) := by
  exact ClosedTermEq.propTruth_respects_representatives hpq

theorem closedTermQuot_propTruth_eq_classOf_canary
    {T : ClosedTheorySet TestConst}
    {τ : Ty TestBase}
    {t u : ClosedTerm TestConst τ} :
    ClosedTermEq.propTruth (T := T)
        (ClosedTermEq.classOf (.eq t u : ClosedFormula TestConst)) ↔
      ClosedTermEq T t u :=
  ClosedTermEq.propTruth_eq_classOf

theorem closedTermQuot_propTruth_eq_iff_classOf_eq_canary
    {T : ClosedTheorySet TestConst}
    {τ : Ty TestBase}
    {t u : ClosedTerm TestConst τ} :
    ClosedTermEq.propTruth (T := T)
        (ClosedTermEq.classOf (.eq t u : ClosedFormula TestConst)) ↔
      ClosedTermEq.classOf (T := T) t = ClosedTermEq.classOf u :=
  ClosedTermEq.propTruth_eq_iff_classOf_eq

theorem closedTermEq_prop_eq_top_iff_canary
    {T : ClosedTheorySet TestConst}
    {p : ClosedFormula TestConst} :
    ClosedTermEq T p (.top : ClosedFormula TestConst) ↔
      ClosedTheorySet.Provable T p :=
  ClosedTermEq.prop_eq_top_iff

theorem closedTermQuot_propTruth_iff_eq_top_canary
    {T : ClosedTheorySet TestConst}
    (a : ClosedTermEq.Quot T propTy) :
    ClosedTermEq.propTruth (T := T) a ↔
      a = ClosedTermEq.classOf (T := T) (.top : ClosedFormula TestConst) :=
  ClosedTermEq.propTruth_iff_eq_top a

theorem closedTermQuot_propTruth_and_canary
    {T : ClosedTheorySet TestConst}
    {p q : ClosedFormula TestConst} :
    ClosedTermEq.propTruth
        (T := T)
        (ClosedTermEq.classOf (.and p q : ClosedFormula TestConst)) ↔
      ClosedTermEq.propTruth (T := T) (ClosedTermEq.classOf p) ∧
        ClosedTermEq.propTruth (T := T) (ClosedTermEq.classOf q) :=
  ClosedTermEq.propTruth_and_classOf

theorem closedTermQuot_propTruth_imp_elim_canary
    {T : ClosedTheorySet TestConst}
    {p q : ClosedFormula TestConst}
    (hpq : ClosedTermEq.propTruth
      (T := T) (ClosedTermEq.classOf (.imp p q : ClosedFormula TestConst)))
    (hp : ClosedTermEq.propTruth (T := T) (ClosedTermEq.classOf p)) :
    ClosedTermEq.propTruth (T := T) (ClosedTermEq.classOf q) :=
  ClosedTermEq.propTruth_imp_elim_classOf hpq hp

theorem closedTermQuot_propTruth_or_left_canary
    {T : ClosedTheorySet TestConst}
    {p q : ClosedFormula TestConst}
    (hp : ClosedTermEq.propTruth (T := T) (ClosedTermEq.classOf p)) :
    ClosedTermEq.propTruth
      (T := T)
      (ClosedTermEq.classOf (.or p q : ClosedFormula TestConst)) :=
  ClosedTermEq.propTruth_or_intro_left_classOf hp

theorem closedTermQuot_propTruth_or_right_canary
    {T : ClosedTheorySet TestConst}
    {p q : ClosedFormula TestConst}
    (hq : ClosedTermEq.propTruth (T := T) (ClosedTermEq.classOf q)) :
    ClosedTermEq.propTruth
      (T := T)
      (ClosedTermEq.classOf (.or p q : ClosedFormula TestConst)) :=
  ClosedTermEq.propTruth_or_intro_right_classOf hq

theorem closedTermQuot_propTruth_not_elim_canary
    {T : ClosedTheorySet TestConst}
    {p : ClosedFormula TestConst}
    (hnot : ClosedTermEq.propTruth
      (T := T) (ClosedTermEq.classOf (.not p : ClosedFormula TestConst)))
    (hp : ClosedTermEq.propTruth (T := T) (ClosedTermEq.classOf p)) :
    ClosedTermEq.propTruth
      (T := T)
      (ClosedTermEq.classOf (.bot : ClosedFormula TestConst)) :=
  ClosedTermEq.propTruth_not_elim_classOf hnot hp

theorem closedTermQuot_propTruth_not_of_bot_canary
    {T : ClosedTheorySet TestConst}
    {p : ClosedFormula TestConst}
    (hbot : ClosedTermEq.propTruth
      (T := T) (ClosedTermEq.classOf (.bot : ClosedFormula TestConst))) :
    ClosedTermEq.propTruth
      (T := T)
      (ClosedTermEq.classOf (.not p : ClosedFormula TestConst)) :=
  ClosedTermEq.propTruth_not_of_bot_classOf hbot

theorem closedTermQuot_world_truth_iff_mem_canary
    (W : ClosedTheorySet.World TestConst)
    (p : ClosedFormula TestConst) :
    ClosedTermEq.propTruth (T := W.carrier) (ClosedTermEq.classOf p) ↔
      p ∈ W.carrier :=
  ClosedTermEq.propTruth_world_iff_mem W p

theorem closedTermQuot_world_top_truth_canary
    (W : ClosedTheorySet.World TestConst) :
    ClosedTermEq.propTruth
      (T := W.carrier)
      (ClosedTermEq.classOf (.top : ClosedFormula TestConst)) :=
  ClosedTermEq.propTruth_top_world_classOf W

theorem closedTermQuot_world_top_mem_canary
    (W : ClosedTheorySet.World TestConst) :
    (.top : ClosedFormula TestConst) ∈ W.carrier :=
  ClosedTermEq.top_mem_world W

theorem closedTermQuot_world_bottom_not_truth_canary
    (W : ClosedTheorySet.World TestConst) :
    ¬ ClosedTermEq.propTruth
      (T := W.carrier)
      (ClosedTermEq.classOf (.bot : ClosedFormula TestConst)) :=
  ClosedTermEq.propTruth_bot_not_world W

theorem closedTermQuot_world_bottom_truth_false_canary
    (W : ClosedTheorySet.World TestConst) :
    ClosedTermEq.propTruth
        (T := W.carrier)
        (ClosedTermEq.classOf (.bot : ClosedFormula TestConst)) ↔
      False :=
  ClosedTermEq.propTruth_bot_world_iff_false W

theorem closedTermQuot_world_bottom_mem_false_canary
    (W : ClosedTheorySet.World TestConst) :
    (.bot : ClosedFormula TestConst) ∈ W.carrier ↔ False :=
  ClosedTermEq.bot_mem_world_iff_false W

theorem closedTermQuot_world_and_truth_canary
    (W : ClosedTheorySet.World TestConst)
    {p q : ClosedFormula TestConst} :
    ClosedTermEq.propTruth
        (T := W.carrier)
        (ClosedTermEq.classOf (.and p q : ClosedFormula TestConst)) ↔
      ClosedTermEq.propTruth (T := W.carrier) (ClosedTermEq.classOf p) ∧
        ClosedTermEq.propTruth (T := W.carrier) (ClosedTermEq.classOf q) :=
  ClosedTermEq.propTruth_and_world_classOf W

theorem closedTermQuot_world_and_mem_canary
    (W : ClosedTheorySet.World TestConst)
    {p q : ClosedFormula TestConst} :
    (.and p q : ClosedFormula TestConst) ∈ W.carrier ↔
      p ∈ W.carrier ∧ q ∈ W.carrier :=
  ClosedTermEq.and_mem_world_iff W

theorem closedTermQuot_world_imp_truth_elim_canary
    (W : ClosedTheorySet.World TestConst)
    {p q : ClosedFormula TestConst}
    (hpq : ClosedTermEq.propTruth
      (T := W.carrier)
      (ClosedTermEq.classOf (.imp p q : ClosedFormula TestConst)))
    (hp : ClosedTermEq.propTruth (T := W.carrier) (ClosedTermEq.classOf p)) :
    ClosedTermEq.propTruth (T := W.carrier) (ClosedTermEq.classOf q) :=
  ClosedTermEq.propTruth_imp_elim_world_classOf W hpq hp

theorem closedTermQuot_world_imp_mem_elim_canary
    (W : ClosedTheorySet.World TestConst)
    {p q : ClosedFormula TestConst}
    (hpq : (.imp p q : ClosedFormula TestConst) ∈ W.carrier)
    (hp : p ∈ W.carrier) :
    q ∈ W.carrier :=
  ClosedTermEq.imp_mem_world_elim W hpq hp

theorem closedTermQuot_world_eq_truth_canary
    (W : ClosedTheorySet.World TestConst)
    {τ : Ty TestBase}
    {t u : ClosedTerm TestConst τ} :
    ClosedTermEq.propTruth
        (T := W.carrier)
        (ClosedTermEq.classOf (.eq t u : ClosedFormula TestConst)) ↔
      ClosedTermEq W.carrier t u :=
  ClosedTermEq.propTruth_eq_world_classOf W

theorem closedTermQuot_world_eq_truth_class_canary
    (W : ClosedTheorySet.World TestConst)
    {τ : Ty TestBase}
    {t u : ClosedTerm TestConst τ} :
    ClosedTermEq.propTruth
        (T := W.carrier)
        (ClosedTermEq.classOf (.eq t u : ClosedFormula TestConst)) ↔
      ClosedTermEq.classOf (T := W.carrier) t = ClosedTermEq.classOf u :=
  ClosedTermEq.propTruth_eq_world_iff_classOf_eq W

theorem closedTermQuot_world_eq_mem_canary
    (W : ClosedTheorySet.World TestConst)
    {τ : Ty TestBase}
    {t u : ClosedTerm TestConst τ} :
    (.eq t u : ClosedFormula TestConst) ∈ W.carrier ↔
      ClosedTermEq W.carrier t u :=
  ClosedTermEq.eq_mem_world_iff_closedTermEq W

theorem closedTermQuot_world_eq_mem_class_canary
    (W : ClosedTheorySet.World TestConst)
    {τ : Ty TestBase}
    {t u : ClosedTerm TestConst τ} :
    (.eq t u : ClosedFormula TestConst) ∈ W.carrier ↔
      ClosedTermEq.classOf (T := W.carrier) t = ClosedTermEq.classOf u :=
  ClosedTermEq.eq_mem_world_iff_classOf_eq W

theorem closedTermQuot_world_or_reflection_canary
    (W : ClosedTheorySet.World TestConst)
    {p q : ClosedFormula TestConst} :
    ClosedTermEq.propTruth
        (T := W.carrier)
        (ClosedTermEq.classOf (.or p q : ClosedFormula TestConst)) ↔
        ClosedTermEq.propTruth (T := W.carrier) (ClosedTermEq.classOf p) ∨
        ClosedTermEq.propTruth (T := W.carrier) (ClosedTermEq.classOf q) :=
  ClosedTermEq.propTruth_or_world_classOf W

theorem closedTermQuot_world_or_mem_canary
    (W : ClosedTheorySet.World TestConst)
    {p q : ClosedFormula TestConst} :
    (.or p q : ClosedFormula TestConst) ∈ W.carrier ↔
      p ∈ W.carrier ∨ q ∈ W.carrier :=
  ClosedTermEq.or_mem_world_iff W

theorem closedTermQuot_propTruth_all_elim_canary
    {T : ClosedTheorySet TestConst}
    {σ : Ty TestBase}
    {body : Formula TestConst [σ]}
    (t : ClosedTerm TestConst σ)
    (hAll : ClosedTermEq.propTruth
      (T := T)
      (ClosedTermEq.classOf (.all body : ClosedFormula TestConst))) :
    ClosedTermEq.propTruth
      (T := T)
      (ClosedTermEq.classOf (instantiate (Base := TestBase) t body)) :=
  ClosedTermEq.propTruth_all_elim_classOf (T := T) (body := body) t hAll

theorem closedTermQuot_propTruth_ex_intro_canary
    {T : ClosedTheorySet TestConst}
    {σ : Ty TestBase}
    {body : Formula TestConst [σ]}
    (t : ClosedTerm TestConst σ)
    (hInst : ClosedTermEq.propTruth
      (T := T)
      (ClosedTermEq.classOf (instantiate (Base := TestBase) t body))) :
    ClosedTermEq.propTruth
      (T := T)
      (ClosedTermEq.classOf (.ex body : ClosedFormula TestConst)) :=
  ClosedTermEq.propTruth_ex_intro_classOf (T := T) (body := body) t hInst

theorem closedTermQuot_world_ex_witness_canary
    (W : ClosedTheorySet.World TestConst)
    {σ : Ty TestBase}
    {body : Formula TestConst [σ]} :
    ClosedTermEq.propTruth
        (T := W.carrier)
        (ClosedTermEq.classOf (.ex body : ClosedFormula TestConst)) ↔
      ∃ t : ClosedTerm TestConst σ,
        ClosedTermEq.propTruth
          (T := W.carrier)
          (ClosedTermEq.classOf (instantiate (Base := TestBase) t body)) :=
  ClosedTermEq.propTruth_ex_world_classOf W

theorem closedTermQuot_world_ex_mem_canary
    (W : ClosedTheorySet.World TestConst)
    {σ : Ty TestBase}
    {body : Formula TestConst [σ]} :
    (.ex body : ClosedFormula TestConst) ∈ W.carrier ↔
      ∃ t : ClosedTerm TestConst σ,
        instantiate (Base := TestBase) t body ∈ W.carrier :=
  ClosedTermEq.ex_mem_world_iff W

theorem closedTermQuot_world_all_counterexample_canary
    (W : ClosedTheorySet.World TestConst)
    {σ : Ty TestBase}
    {body : Formula TestConst [σ]} :
    ¬ ClosedTermEq.propTruth
        (T := W.carrier)
        (ClosedTermEq.classOf (.all body : ClosedFormula TestConst)) →
      ∃ t : ClosedTerm TestConst σ,
        ¬ ClosedTermEq.propTruth
          (T := W.carrier)
          (ClosedTermEq.classOf (instantiate (Base := TestBase) t body)) :=
  ClosedTermEq.propTruth_all_counterexample_world_classOf W

theorem closedTermQuot_world_all_notnot_of_forall_instances_canary
    (W : ClosedTheorySet.World TestConst)
    {σ : Ty TestBase}
    {body : Formula TestConst [σ]}
    (hInst :
      ∀ t : ClosedTerm TestConst σ,
        ClosedTermEq.propTruth
          (T := W.carrier)
          (ClosedTermEq.classOf (instantiate (Base := TestBase) t body))) :
    ¬¬ ClosedTermEq.propTruth
      (T := W.carrier)
      (ClosedTermEq.classOf (.all body : ClosedFormula TestConst)) :=
  ClosedTermEq.propTruth_all_world_notnot_of_forall_instances W hInst

theorem closedTermQuot_world_all_of_stable_forall_instances_canary
    (W : ClosedTheorySet.World TestConst)
    {σ : Ty TestBase}
    {body : Formula TestConst [σ]}
    (hStable :
      ¬¬ ClosedTermEq.propTruth
        (T := W.carrier)
        (ClosedTermEq.classOf (.all body : ClosedFormula TestConst)) →
      ClosedTermEq.propTruth
        (T := W.carrier)
        (ClosedTermEq.classOf (.all body : ClosedFormula TestConst)))
    (hInst :
      ∀ t : ClosedTerm TestConst σ,
        ClosedTermEq.propTruth
          (T := W.carrier)
          (ClosedTermEq.classOf (instantiate (Base := TestBase) t body))) :
    ClosedTermEq.propTruth
      (T := W.carrier)
      (ClosedTermEq.classOf (.all body : ClosedFormula TestConst)) :=
  ClosedTermEq.propTruth_all_world_of_stable_forall_instances W hStable hInst

theorem closedTermQuot_world_all_not_mem_counterexample_canary
    (W : ClosedTheorySet.World TestConst)
    {σ : Ty TestBase}
    {body : Formula TestConst [σ]} :
    (.all body : ClosedFormula TestConst) ∉ W.carrier ↔
      ∃ t : ClosedTerm TestConst σ,
        instantiate (Base := TestBase) t body ∉ W.carrier :=
  ClosedTermEq.all_not_mem_world_iff_exists_counterexample W

theorem closedTermQuot_world_all_mem_notnot_of_forall_instances_canary
    (W : ClosedTheorySet.World TestConst)
    {σ : Ty TestBase}
    {body : Formula TestConst [σ]}
    (hInst :
      ∀ t : ClosedTerm TestConst σ,
        instantiate (Base := TestBase) t body ∈ W.carrier) :
    ¬¬ (.all body : ClosedFormula TestConst) ∈ W.carrier :=
  ClosedTermEq.all_mem_world_notnot_of_forall_instances W hInst

theorem closedTermQuot_world_all_mem_of_stable_forall_instances_canary
    (W : ClosedTheorySet.World TestConst)
    {σ : Ty TestBase}
    {body : Formula TestConst [σ]}
    (hStable :
      ¬¬ (.all body : ClosedFormula TestConst) ∈ W.carrier →
        (.all body : ClosedFormula TestConst) ∈ W.carrier)
    (hInst :
      ∀ t : ClosedTerm TestConst σ,
        instantiate (Base := TestBase) t body ∈ W.carrier) :
    (.all body : ClosedFormula TestConst) ∈ W.carrier :=
  ClosedTermEq.all_mem_world_of_stable_forall_instances W hStable hInst

abbrev TestAtomTy : Ty TestBase := .base TestBase.atom

abbrev TestClosedEnv :
    ClosedTermEq.ClosedEnv TestConst [TestAtomTy] :=
  fun {_} v =>
    match v with
    | .vz => .const TestConst.a

theorem closedEnv_close_var_canary :
    ClosedTermEq.closeTerm TestClosedEnv
        (.var (Var.vz : Var [TestAtomTy] TestAtomTy) :
          Term TestConst [TestAtomTy] TestAtomTy) =
      (.const TestConst.a : ClosedTerm TestConst TestAtomTy) :=
  rfl

theorem closedEnv_extend_head_canary
    (t : ClosedTerm TestConst TestAtomTy) :
    ClosedTermEq.ClosedEnv.extend TestClosedEnv t
        (Var.vz :
          Var [TestAtomTy, TestAtomTy] TestAtomTy) =
      t :=
  rfl

theorem closedEnv_instantiate_lift_canary
    (body :
      Formula TestConst [TestAtomTy, TestAtomTy])
    (t : ClosedTerm TestConst TestAtomTy) :
    instantiate (Base := TestBase) t
        (subst
          (Subst.lift (Base := TestBase) (Const := TestConst) TestClosedEnv)
          body) =
      ClosedTermEq.closeTerm
        (ClosedTermEq.ClosedEnv.extend TestClosedEnv t)
        body :=
  ClosedTermEq.instantiate_closeTerm_lift TestClosedEnv t body

theorem closedEnv_satisfies_top_canary
    {T : ClosedTheorySet TestConst} :
    ClosedTermEq.envSatisfies T TestClosedEnv
      (.top : Formula TestConst [TestAtomTy]) :=
  ClosedTermEq.envSatisfies_top T TestClosedEnv

theorem closedEnv_satisfies_and_canary
    {T : ClosedTheorySet TestConst}
    {φ ψ : Formula TestConst [TestAtomTy]} :
    ClosedTermEq.envSatisfies T TestClosedEnv (.and φ ψ) ↔
      ClosedTermEq.envSatisfies T TestClosedEnv φ ∧
        ClosedTermEq.envSatisfies T TestClosedEnv ψ :=
  ClosedTermEq.envSatisfies_and

theorem closedEnv_satisfies_imp_elim_canary
    {T : ClosedTheorySet TestConst}
    {φ ψ : Formula TestConst [TestAtomTy]}
    (hImp : ClosedTermEq.envSatisfies T TestClosedEnv (.imp φ ψ))
    (hφ : ClosedTermEq.envSatisfies T TestClosedEnv φ) :
    ClosedTermEq.envSatisfies T TestClosedEnv ψ :=
  ClosedTermEq.envSatisfies_imp_elim hImp hφ

theorem closedEnv_satisfies_eq_closedTermEq_canary
    {T : ClosedTheorySet TestConst}
    {τ : Ty TestBase}
    {t u : Term TestConst [TestAtomTy] τ} :
    ClosedTermEq.envSatisfies T TestClosedEnv (.eq t u) ↔
      ClosedTermEq T
        (ClosedTermEq.closeTerm TestClosedEnv t)
        (ClosedTermEq.closeTerm TestClosedEnv u) :=
  ClosedTermEq.envSatisfies_eq_iff_closedTermEq

theorem closedEnv_satisfies_eq_class_canary
    {T : ClosedTheorySet TestConst}
    {τ : Ty TestBase}
    {t u : Term TestConst [TestAtomTy] τ} :
    ClosedTermEq.envSatisfies T TestClosedEnv (.eq t u) ↔
      ClosedTermEq.classOf (T := T)
          (ClosedTermEq.closeTerm TestClosedEnv t) =
        ClosedTermEq.classOf (T := T)
          (ClosedTermEq.closeTerm TestClosedEnv u) :=
  ClosedTermEq.envSatisfies_eq_iff_classOf_eq

theorem closedEnv_satisfies_all_elim_canary
    {T : ClosedTheorySet TestConst}
    {body : Formula TestConst [TestAtomTy, TestAtomTy]}
    (t : ClosedTerm TestConst TestAtomTy)
    (hAll : ClosedTermEq.envSatisfies T TestClosedEnv (.all body)) :
    ClosedTermEq.envSatisfies T
      (ClosedTermEq.ClosedEnv.extend TestClosedEnv t) body :=
  ClosedTermEq.envSatisfies_all_elim t hAll

theorem closedEnv_satisfies_ex_intro_canary
    {T : ClosedTheorySet TestConst}
    {body : Formula TestConst [TestAtomTy, TestAtomTy]}
    (t : ClosedTerm TestConst TestAtomTy)
    (hBody : ClosedTermEq.envSatisfies T
      (ClosedTermEq.ClosedEnv.extend TestClosedEnv t) body) :
    ClosedTermEq.envSatisfies T TestClosedEnv (.ex body) :=
  ClosedTermEq.envSatisfies_ex_intro t hBody

theorem closedEnv_world_truth_iff_mem_canary
    (W : ClosedTheorySet.World TestConst)
    (φ : Formula TestConst [TestAtomTy]) :
    ClosedTermEq.envSatisfies W.carrier TestClosedEnv φ ↔
      ClosedTermEq.closeFormula TestClosedEnv φ ∈ W.carrier :=
  ClosedTermEq.envSatisfies_world_iff_mem W TestClosedEnv φ

theorem closedEnv_world_or_canary
    (W : ClosedTheorySet.World TestConst)
    {φ ψ : Formula TestConst [TestAtomTy]} :
    ClosedTermEq.envSatisfies W.carrier TestClosedEnv (.or φ ψ) ↔
      ClosedTermEq.envSatisfies W.carrier TestClosedEnv φ ∨
        ClosedTermEq.envSatisfies W.carrier TestClosedEnv ψ :=
  ClosedTermEq.envSatisfies_or_world W

theorem closedEnv_world_ex_witness_canary
    (W : ClosedTheorySet.World TestConst)
    {body : Formula TestConst [TestAtomTy, TestAtomTy]} :
    ClosedTermEq.envSatisfies W.carrier TestClosedEnv (.ex body) ↔
      ∃ t : ClosedTerm TestConst TestAtomTy,
        ClosedTermEq.envSatisfies W.carrier
          (ClosedTermEq.ClosedEnv.extend TestClosedEnv t) body :=
  ClosedTermEq.envSatisfies_ex_world W

theorem closedEnv_world_all_counterexample_canary
    (W : ClosedTheorySet.World TestConst)
    {body : Formula TestConst [TestAtomTy, TestAtomTy]} :
    ¬ ClosedTermEq.envSatisfies W.carrier TestClosedEnv (.all body) →
      ∃ t : ClosedTerm TestConst TestAtomTy,
        ¬ ClosedTermEq.envSatisfies W.carrier
          (ClosedTermEq.ClosedEnv.extend TestClosedEnv t) body :=
  ClosedTermEq.envSatisfies_all_counterexample_world W

theorem closedEnv_world_all_notnot_of_forall_instances_canary
    (W : ClosedTheorySet.World TestConst)
    {body : Formula TestConst [TestAtomTy, TestAtomTy]}
    (hInst :
      ∀ t : ClosedTerm TestConst TestAtomTy,
        ClosedTermEq.envSatisfies W.carrier
          (ClosedTermEq.ClosedEnv.extend TestClosedEnv t) body) :
    ¬¬ ClosedTermEq.envSatisfies W.carrier TestClosedEnv (.all body) :=
  ClosedTermEq.envSatisfies_all_world_notnot_of_forall_instances W hInst

theorem closedEnv_world_all_of_stable_forall_instances_canary
    (W : ClosedTheorySet.World TestConst)
    {body : Formula TestConst [TestAtomTy, TestAtomTy]}
    (hStable :
      ¬¬ ClosedTermEq.envSatisfies W.carrier TestClosedEnv (.all body) →
        ClosedTermEq.envSatisfies W.carrier TestClosedEnv (.all body))
    (hInst :
      ∀ t : ClosedTerm TestConst TestAtomTy,
        ClosedTermEq.envSatisfies W.carrier
          (ClosedTermEq.ClosedEnv.extend TestClosedEnv t) body) :
    ClosedTermEq.envSatisfies W.carrier TestClosedEnv (.all body) :=
  ClosedTermEq.envSatisfies_all_world_of_stable_forall_instances W hStable hInst

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ClosedTermQuotientRegression
