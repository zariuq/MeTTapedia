import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLDefinableCuts
import Mettapedia.Logic.HOL.SevenVirtues.Completeness

/-!
# Controls for the counting-capacity definable cuts

The counting-capacity cuts assume, beyond the classical hypotheses of the credal
interval, that every extensional model of the theory has a finite carrier of objects at
the predicate's type, of size at most `N`. This file gives a theory over the parameter
signature that meets all of these hypotheses together.

* Signature: one base type `ι` and one predicate constant `P : ι ⇒ prop`.
* Theory `atMostOneTheory`: excluded middle and `∀ x y : ι, x = y`; every extensional
  model of it has at most one object of type `ι` (`subsingleton_of_models`).

Positive: the cut of `∃ x, P x` at threshold `1` is defined (`existsCut`) and its width
theorem applies (`existsCut_width_iff`).

Positive: the fuzzy "for all" cut at "at least one" has carriers of exact size `1` in every
extensional model (`objCard_eq_one`), and its width theorem applies
(`forAllAtLeastOne_width_iff`); the counting capacity calibrates the Sugeno endpoint of
`∀ x, P x` (`sugenoCalibration`), and the Sugeno width theorem applies (`sugeno_width_iff`);
the band "some but not all" and the fuzzy "for all" endpoint cut have their width theorems
applied too (`existsAndExistsNotBand_width_iff`, `forAllEndpoint_width_iff`).

Negative: the theory decides neither `∃ x, P x` nor its negation (standard models with one
individual and `P` false or true), so the cut does not collapse
(`existsCut_width_ne_zero`).
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLDefinableCuts.CountingControls

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.WithParams
open Mettapedia.Logic.HOL.ClosedTheorySet
open Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLCompletenessTightness
open Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge
open Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLQuantifierBridge

/-- The type of individuals. -/
abbrev ι : Ty Unit := .base ()

/-- One predicate constant on individuals. -/
inductive PredConst : Ty Unit → Type
  | pred : PredConst (ι ⇒ propTy)

deriving instance Countable for PredConst

/-- The predicate `P` over the parameter signature. -/
def predP : UnaryPredicate (Base := Unit) (Const := WithParams PredConst) ι :=
  .const (inj .pred)

/-- `∀ x y : ι, x = y`. -/
def atMostOne : ClosedFormula (WithParams PredConst) :=
  .all (σ := ι) (.all (σ := ι) (.eq (.var (.vs .vz)) (.var .vz)))

/-- Excluded middle and at most one individual. -/
def atMostOneTheory : ClosedTheorySet (WithParams PredConst) :=
  {SevenVirtues.excludedMiddle, atMostOne}

theorem atMostOneTheory_paramFree :
    ∀ ψ ∈ atMostOneTheory, ∀ (σ : Ty Unit) (k : Nat), NoConstOccurrence (param σ k) ψ := by
  intro ψ hψ σ k
  rcases hψ with rfl | hψ
  · exact .all (.or .var (.not .var))
  · rw [Set.mem_singleton_iff] at hψ
    subst hψ
    exact .all (.all (.eq .var .var))

theorem atMostOneTheory_proves_emSchema :
    ∀ ψ ∈ EMSchema PredConst,
      Provable (Const := WithParams PredConst) atMostOneTheory ψ :=
  SevenVirtues.provable_emSchema_of_mem (Set.mem_insert _ _)

/-! ## Standard models with one individual -/

/-- A value of every type over one individual. -/
def unitDefault : (τ : Ty Unit) → Ty.denote.{0, 0} (fun _ => PUnit.{2}) τ
  | .prop => ULift.up True
  | .base _ => PUnit.unit
  | .arr _ τ => fun _ => unitDefault τ

/-- `P` denotes the constant truth value `v`; parameters denote default values. -/
def predConst (v : Prop) {τ : Ty Unit} :
    WithParams PredConst τ → Ty.denote.{0, 0} (fun _ => PUnit.{2}) τ
  | Sum.inl c => match τ, c with
    | _, .pred => fun _ => ULift.up v
  | Sum.inr _ => unitDefault τ

/-- The standard model with one individual in which `P` has truth value `v`. -/
def predModel (v : Prop) : HenkinModel.{0, 0, 0} Unit (WithParams PredConst) :=
  HenkinModel.standard (fun _ => PUnit.{2}) (predConst v)

theorem predModel_extensional (v : Prop) : (predModel v).FunctionsRespectEqv :=
  (predModel v).functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _)

theorem predModel_models_theory (v : Prop) :
    ∀ ψ ∈ atMostOneTheory, (predModel v).models ψ := by
  intro ψ hψ
  rcases hψ with rfl | hψ
  · exact SevenVirtues.models_excludedMiddle _
  · rw [Set.mem_singleton_iff] at hψ
    subst hψ
    intro x _ y _
    rfl

theorem models_of_provable {φ : ClosedFormula (WithParams PredConst)}
    (h : Provable (Const := WithParams PredConst) atMostOneTheory φ) (v : Prop) :
    (predModel v).models φ :=
  SevenVirtues.soundness (T := atMostOneTheory)
    (provable_mono (Const := WithParams PredConst) (fun hψ => Set.mem_insert_of_mem _ hψ) h)
    _ (predModel_extensional v) (predModel_models_theory v)

theorem atMostOneTheory_consistent :
    Consistent (Const := WithParams PredConst) atMostOneTheory := fun hBot =>
  HenkinModel.models_bot _ (models_of_provable hBot True)

/-! ## The finite-carrier hypotheses -/

/-- Every extensional model of the theory has at most one object of type `ι`. -/
theorem subsingleton_of_models
    (M : ExtensionalTheoryModel (Base := Unit) (Const := PredConst) atMostOneTheory) :
    Subsingleton (PredicateObject (Base := Unit) (Const := WithParams PredConst) M.1 ι) := by
  constructor
  intro x y
  have h := M.2.1 atMostOne (Set.mem_insert_of_mem _ rfl)
  exact Subtype.ext (h x.1 x.2 y.1 y.2)

/-- The finite carrier of each model. -/
@[instance_reducible] noncomputable def objFintype
    (M : ExtensionalTheoryModel (Base := Unit) (Const := PredConst) atMostOneTheory) :
    Fintype (PredicateObject (Base := Unit) (Const := WithParams PredConst) M.1 ι) :=
  haveI := subsingleton_of_models M
  Fintype.ofFinite _

theorem objCard_le_one
    (M : ExtensionalTheoryModel (Base := Unit) (Const := PredConst) atMostOneTheory) :
    @Fintype.card _ (objFintype M) ≤ 1 :=
  (@Fintype.card_le_one_iff_subsingleton _ (objFintype M)).mpr (subsingleton_of_models M)

theorem existsFormula_paramFree (ρ : Ty Unit) (k : Nat) :
    NoConstOccurrence (param ρ k)
      (predicateExistsFormula (Base := Unit) (Const := WithParams PredConst) ι predP) := by
  refine .ex (.app ?_ .var)
  by_cases h : ρ = (ι ⇒ propTy)
  · subst h
    exact .const_same_ne _ (inj_ne_param _ k)
  · exact .const_diff_type h _

/-- A surjective enumeration of the one-variable bodies. -/
noncomputable def predEnum : Nat → Body PredConst :=
  Classical.choose (SevenVirtues.exists_body_enumeration (Const := PredConst))

theorem predEnum_surjective : ∀ b : Body PredConst, ∃ n, predEnum n = b :=
  Classical.choose_spec (SevenVirtues.exists_body_enumeration (Const := PredConst))

/-! ## The cut and its controls -/

/-- **Positive control.** The counting-capacity cut of `∃ x, P x` at threshold `1`. -/
noncomputable def existsCut :
    ExtensionalDefinableCut (Base := Unit) (Const := PredConst) atMostOneTheory :=
  predicateCountingCapacityExistsPositiveThresholdCut ι predP objFintype (fun _ => ⊤) 1 one_pos
    objCard_le_one 1 one_pos (by norm_num) existsFormula_paramFree

/-- **Positive control.** The width theorem of the cut applies. -/
theorem existsCut_width_iff :
    type_of% (predicateCountingCapacityExistsPositiveThresholdCut_width_eq_zero_iff_decides
      (T := atMostOneTheory) ι predP objFintype (fun _ => ⊤) 1 one_pos objCard_le_one 1 one_pos
      (by norm_num) existsFormula_paramFree predEnum predEnum_surjective
      atMostOneTheory_consistent atMostOneTheory_paramFree atMostOneTheory_proves_emSchema) :=
  predicateCountingCapacityExistsPositiveThresholdCut_width_eq_zero_iff_decides
    (T := atMostOneTheory) ι predP objFintype (fun _ => ⊤) 1 one_pos objCard_le_one 1 one_pos
    (by norm_num) existsFormula_paramFree predEnum predEnum_surjective
    atMostOneTheory_consistent atMostOneTheory_paramFree atMostOneTheory_proves_emSchema

theorem predModel_models_exists_iff (v : Prop) :
    (predModel v).models
        (predicateExistsFormula (Base := Unit) (Const := WithParams PredConst) ι predP) ↔ v := by
  rw [models_predicateExistsFormula_iff]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨⟨PUnit.unit, trivial⟩, h⟩⟩

/-- **Negative control.** The theory decides neither `∃ x, P x` nor its negation, so the
cut does not collapse. -/
theorem existsCut_width_ne_zero :
    (ExtensionalDefinableCut.intervalOfConsistent (Base := Unit) (Const := PredConst) existsCut
      predEnum predEnum_surjective atMostOneTheory_consistent atMostOneTheory_paramFree
      atMostOneTheory_proves_emSchema).width ≠ 0 := fun hWidth =>
  (existsCut_width_iff.mp hWidth).elim
    (fun h => (predModel_models_exists_iff False).mp (models_of_provable h False))
    (fun h => (HenkinModel.models_not _).mp (models_of_provable h True)
      ((predModel_models_exists_iff True).mpr trivial))

/-- Repeating the conjunction changes the HOL syntax and preserves the
threshold event and its interval. -/
theorem existsCut_conjunction_same_interval :
    (existsCut.andCut existsCut).formula ≠ existsCut.formula ∧
      (existsCut.andCut existsCut).intervalOfConsistent predEnum predEnum_surjective
        atMostOneTheory_consistent atMostOneTheory_paramFree atMostOneTheory_proves_emSchema =
      existsCut.intervalOfConsistent predEnum predEnum_surjective
        atMostOneTheory_consistent atMostOneTheory_paramFree atMostOneTheory_proves_emSchema := by
  constructor
  · change Term.and _ _ ≠ Term.ex _
    intro impossible
    cases impossible
  · apply ExtensionalDefinableCut.intervalOfConsistent_eq_of_thresholdEvent_eq
    rw [ExtensionalDefinableCut.andCut_thresholdEvent, Set.inter_self]

open Mettapedia.GSLT.Core.NonFactorization in
/-- An affine shift preserves the threshold event and changes the score in
the actual one-individual model. -/
theorem numeric_score_does_not_factor_through_threshold_event :
    ¬ Factors (ExtensionalDefinableCut.thresholdEvent (T := atMostOneTheory))
      (ExtensionalDefinableCut.score (T := atMostOneTheory)) := by
  let shifted := existsCut.posAffineRescale 1 1 one_pos
  apply NonTrivialFiber.not_factors
  refine ⟨existsCut, shifted, ?_, ?_⟩
  · apply Set.ext
    intro M
    change existsCut.threshold ≤ existsCut.score M ↔
      1 * existsCut.threshold + 1 ≤ 1 * existsCut.score M + 1
    simp
  · intro sameScore
    let M : ExtensionalTheoryModel (Base := Unit) (Const := PredConst) atMostOneTheory :=
      ⟨predModel True, predModel_models_theory True, predModel_extensional True⟩
    have atModel := congrFun sameScore M
    change existsCut.score M = 1 * existsCut.score M + 1 at atModel
    linarith

theorem parameter_constant_is_not_parameter_free :
    ¬ ParameterFree (.const (param ι 0) : Term (WithParams PredConst) [] ι) := by
  intro free
  cases free ι 0 with
  | const_diff_type different => exact different rfl
  | const_same_ne _ different => exact different rfl

/-! ## A fuzzy-quantifier cut with an exact carrier size -/

/-- Every extensional model has exactly one object of type `ι`: the parameter `param ι 0`
denotes one. -/
theorem objCard_eq_one
    (M : ExtensionalTheoryModel (Base := Unit) (Const := PredConst) atMostOneTheory) :
    @Fintype.card _ (objFintype M) = 1 :=
  (@Fintype.card_eq_one_iff _ (objFintype M)).mpr
    ⟨⟨M.1.constDen (param ι 0), M.1.const_mem _⟩,
      fun _ => (subsingleton_of_models M).elim _ _⟩

theorem predP_paramFree (ρ : Ty Unit) (k : Nat) : NoConstOccurrence (param ρ k) predP := by
  by_cases h : ρ = (ι ⇒ propTy)
  · subst h
    exact .const_same_ne _ (inj_ne_param _ k)
  · exact .const_diff_type h _

/-- Crisp parameters: `ε = 0` and proportion cutoff `1`. -/
def crispParams : Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers.FuzzyQuantifierParams where
  ε := 0
  LPC := 0
  UPC := 1
  PCL := 1
  hε := ⟨le_refl _, zero_le_one⟩
  hLPC := ⟨le_refl _, zero_le_one⟩
  hUPC := ⟨zero_le_one, le_refl _⟩
  hPCL := ⟨zero_le_one, le_refl _⟩
  hLPC_le_UPC := zero_le_one

/-- **Positive control.** The width theorem of the fuzzy "for all" cut at "at least one",
over carriers of exact size `1`. -/
theorem forAllAtLeastOne_width_iff :
    type_of% (predicateFuzzyForAllCountingAtLeastNBaseCut_width_eq_zero_iff_decides
      (T := atMostOneTheory) () crispParams predP predP_paramFree objFintype (fun _ => ⊤) rfl
      1 1 one_pos (by norm_num [crispParams]) objCard_eq_one predEnum predEnum_surjective
      atMostOneTheory_consistent atMostOneTheory_paramFree atMostOneTheory_proves_emSchema) :=
  predicateFuzzyForAllCountingAtLeastNBaseCut_width_eq_zero_iff_decides
    (T := atMostOneTheory) () crispParams predP predP_paramFree objFintype (fun _ => ⊤) rfl
    1 1 one_pos (by norm_num [crispParams]) objCard_eq_one predEnum predEnum_surjective
    atMostOneTheory_consistent atMostOneTheory_paramFree atMostOneTheory_proves_emSchema

/-! ## A Sugeno cut with the counting calibration -/

theorem objNonempty
    (M : ExtensionalTheoryModel (Base := Unit) (Const := PredConst) atMostOneTheory) :
    Nonempty (PredicateObject (Base := Unit) (Const := WithParams PredConst) M.1 ι) :=
  ⟨⟨M.1.constDen (param ι 0), M.1.const_mem _⟩⟩

theorem forAllFormula_paramFree (ρ : Ty Unit) (k : Nat) :
    NoConstOccurrence (param ρ k)
      (predicateForAllFormula (Base := Unit) (Const := WithParams PredConst) ι predP) := by
  refine .all (.app ?_ .var)
  by_cases h : ρ = (ι ⇒ propTy)
  · subst h
    exact .const_same_ne _ (inj_ne_param _ k)
  · exact .const_diff_type h _

/-- **Positive control.** The counting capacity calibrates the Sugeno endpoint of `∀ x, P x`
over this theory. -/
noncomputable def sugenoCalibration :
    PredicateSugenoOneCalibration (Base := Unit) (Const := PredConst) atMostOneTheory ι predP :=
  predicateSugenoCountingOneCalibration ι predP objFintype objNonempty (fun _ => ⊤)

/-- **Positive control.** The width theorem of the Sugeno counting cut applies. -/
theorem sugeno_width_iff :
    type_of% (predicateSugenoCountingCrispEndpointGeOneCut_width_eq_zero_iff_decides
      (T := atMostOneTheory) ι predP objFintype objNonempty (fun _ => ⊤)
      forAllFormula_paramFree predEnum predEnum_surjective atMostOneTheory_consistent
      atMostOneTheory_paramFree atMostOneTheory_proves_emSchema) :=
  predicateSugenoCountingCrispEndpointGeOneCut_width_eq_zero_iff_decides
    (T := atMostOneTheory) ι predP objFintype objNonempty (fun _ => ⊤)
    forAllFormula_paramFree predEnum predEnum_surjective atMostOneTheory_consistent
    atMostOneTheory_paramFree atMostOneTheory_proves_emSchema

/-! ## A band cut and a fuzzy-quantifier endpoint cut -/

/-- **Positive control.** The width theorem of the counting band "some but not all" applies. -/
theorem existsAndExistsNotBand_width_iff :
    type_of% (predicateCountingCapacityExistsAndExistsNotBandCut_width_eq_zero_iff_decides
      (T := atMostOneTheory) ι predP predP_paramFree objFintype (fun _ => ⊤) 1 one_pos
      objCard_eq_one predEnum predEnum_surjective atMostOneTheory_consistent
      atMostOneTheory_paramFree atMostOneTheory_proves_emSchema) :=
  predicateCountingCapacityExistsAndExistsNotBandCut_width_eq_zero_iff_decides
    (T := atMostOneTheory) ι predP predP_paramFree objFintype (fun _ => ⊤) 1 one_pos
    objCard_eq_one predEnum predEnum_surjective atMostOneTheory_consistent
    atMostOneTheory_paramFree atMostOneTheory_proves_emSchema

/-- **Positive control.** The width theorem of the fuzzy "for all" endpoint cut applies. -/
theorem forAllEndpoint_width_iff :
    type_of% (predicateFuzzyForAllCrispEndpointPositiveThresholdCut_width_eq_zero_iff_decides
      (T := atMostOneTheory) ι crispParams predP objFintype objNonempty rfl rfl
      forAllFormula_paramFree 1 one_pos le_rfl predEnum predEnum_surjective
      atMostOneTheory_consistent atMostOneTheory_paramFree atMostOneTheory_proves_emSchema) :=
  predicateFuzzyForAllCrispEndpointPositiveThresholdCut_width_eq_zero_iff_decides
    (T := atMostOneTheory) ι crispParams predP objFintype objNonempty rfl rfl
    forAllFormula_paramFree 1 one_pos le_rfl predEnum predEnum_surjective
    atMostOneTheory_consistent atMostOneTheory_paramFree atMostOneTheory_proves_emSchema

#print axioms existsCut_width_iff
#print axioms existsCut_width_ne_zero
#print axioms forAllAtLeastOne_width_iff
#print axioms sugeno_width_iff
#print axioms existsAndExistsNotBand_width_iff
#print axioms forAllEndpoint_width_iff

end Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLDefinableCuts.CountingControls
