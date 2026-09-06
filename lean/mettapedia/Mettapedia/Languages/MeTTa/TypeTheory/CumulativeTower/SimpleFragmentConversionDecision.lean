import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SimpleFragmentNormalization
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SimpleFragmentNormalForms
import Mettapedia.GSLT.LanguageDef.NIKServiceFamily

/-!
# Exact conversion comparison and native simple-fragment services

Normal forms retain their intrinsic typing information. Together with strong
normalization and tower skeleton confluence, this proves that tower conversion
between translated simple terms is exactly intrinsic beta conversion. The
forward term map is therefore injective on conversion classes, although it is
not injective on raw syntax.

Comparison of computed normal forms gives a direct decision service, and
normalization gives a native operation over the same independently declared
conversion target. Neither service consumes an external certificate.

The result concerns conversion of terms already in the simple image. It does
not establish reflection of type inhabitation or a model reduct for all tower
points. The sealed tower has no declaration-specific root computation here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace SimpleFragmentConversionDecision

open FourFaceBetaExperiment FourFaceBetaExperiment.IntrinsicSTT
open SimpleFragmentNormalization
open Mettapedia.GSLT.LanguageDef
open NIKMetalogic MaximalNativeCalculus KernelAuthority

variable {Γ Δ : List Ty} {A : Ty}

theorem normalize_normal (t : Term Γ A) : Normal (normalize t).normalForm :=
  Normal.iff_no_betaStep.mpr (normalize t).irreducible

theorem normalize_eq_of_towerConv {left right : Term Γ A}
    (h : Presentation.Conv Presentation.Tower.HeadEq
      (TowerDTT.eraseTerm left) (TowerDTT.eraseTerm right)) :
    (normalize left).normalForm = (normalize right).normalForm := by
  apply Normal.eq_of_towerConv (normalize_normal left) (normalize_normal right)
  exact .trans _ _ _ (.symm _ _ (normalize_convert left).erase)
    (.trans _ _ _ h (normalize_convert right).erase)

/-- Full sealed-tower conversion is conservative on the translated simple
term image, even when its conversion path leaves that image. -/
theorem towerConv_iff_betaConv (left right : Term Γ A) :
    Presentation.Conv Presentation.Tower.HeadEq
      (TowerDTT.eraseTerm left) (TowerDTT.eraseTerm right) ↔ BetaConv left right := by
  constructor
  · intro h
    have equal := normalize_eq_of_towerConv h
    have leftPath := normalize_convert left
    rw [equal] at leftPath
    exact .trans _ _ _ leftPath (.symm _ _ (normalize_convert right))
  · exact BetaConv.erase

theorem normalize_eq_iff_betaConv (left right : Term Γ A) :
    (normalize left).normalForm = (normalize right).normalForm ↔ BetaConv left right := by
  constructor
  · intro equal
    have leftPath := normalize_convert left
    rw [equal] at leftPath
    exact .trans _ _ _ leftPath (.symm _ _ (normalize_convert right))
  · intro h
    exact normalize_eq_of_towerConv h.erase

theorem normalize_substitute (t : Term Γ A) (σ : Substitution Γ Δ) :
    (normalize ((normalize t).normalForm.substitute σ)).normalForm =
      (normalize (t.substitute σ)).normalForm :=
  (normalize_eq_iff_betaConv _ _).2
    (BetaConv.substitute (Relation.EqvGen.symm _ _ (normalize_convert t)) σ)

/-- The obstruction at raw syntax disappears for the induced term-class map. -/
theorem betaClass_toTower_injective :
    Function.Injective (BetaClass.toTower (Γ := Γ) (A := A)) := by
  intro left right equal
  induction left using Quotient.inductionOn with
  | _ left =>
      induction right using Quotient.inductionOn with
      | _ right =>
          apply Quotient.sound
          exact (towerConv_iff_betaConv left right).1 (Quotient.exact equal)

/-- Beta classes have unique intrinsic normal-form representatives. -/
def betaClassEquivNormal : BetaClass Γ A ≃ {t : Term Γ A // Normal t} where
  toFun := Quotient.lift
    (fun t => ⟨(normalize t).normalForm, normalize_normal t⟩)
    (fun left right h => Subtype.ext ((normalize_eq_iff_betaConv left right).2 h))
  invFun := fun t => Quotient.mk (betaSetoid Γ A) t.1
  left_inv := by
    intro t
    induction t using Quotient.inductionOn with
    | _ t => exact Quotient.sound (.symm _ _ (normalize_convert t))
  right_inv := by
    intro t
    apply Subtype.ext
    exact normalize_of_irreducible t.1 t.2.no_betaStep

/-- Direct comparison of computed normal-form syntax, not proof replay. -/
def decideConversion (left right : Term Γ A) : Bool :=
  decide (TowerDTT.eraseTerm (normalize left).normalForm =
    TowerDTT.eraseTerm (normalize right).normalForm)

theorem decideConversion_correct (left right : Term Γ A) :
    decideConversion left right = true ↔ BetaConv left right := by
  simp only [decideConversion, decide_eq_true_eq]
  constructor
  · intro equal
    exact (normalize_eq_iff_betaConv left right).1
      (Normal.eq_of_erase_eq (normalize_normal left) (normalize_normal right) equal)
  · intro h
    exact congrArg TowerDTT.eraseTerm ((normalize_eq_iff_betaConv left right).2 h)

def conversionTarget (Γ : List Ty) (A : Ty) : AdmissionObject where
  Carrier := Term Γ A × Term Γ A
  Meaning pair := BetaConv pair.1 pair.2

def decisionKernel (Γ : List Ty) (A : Ty) :
    Checker.DecisionKernel (conversionTarget Γ A).Carrier (conversionTarget Γ A).Meaning where
  decide pair := decideConversion pair.1 pair.2
  correct pair := decideConversion_correct pair.1 pair.2

def decisionService (Γ : List Ty) (A : Ty) : NIK.Service.{0, 0} (conversionTarget Γ A) :=
  .directDecision (decisionKernel Γ A)

def normalizationOperation (Γ : List Ty) (A : Ty) :
    AdmissionHom (conversionTarget Γ A) (conversionTarget Γ A) where
  run pair := ((normalize pair.1).normalForm, (normalize pair.2).normalForm)
  preserves pair h := by
    change BetaConv (normalize pair.1).normalForm (normalize pair.2).normalForm
    rw [(normalize_eq_iff_betaConv pair.1 pair.2).2 h]
    exact .refl _

def normalizationService (Γ : List Ty) (A : Ty) :
    NIK.Service.{0, 0} (conversionTarget Γ A) :=
  .nativeOperation (conversionTarget Γ A) (normalizationOperation Γ A)

theorem normalizationOperation_meaning_iff (pair : (conversionTarget Γ A).Carrier) :
    (conversionTarget Γ A).Meaning ((normalizationOperation Γ A).run pair) ↔
      (conversionTarget Γ A).Meaning pair := by
  constructor
  · intro h
    exact .trans _ _ _ (normalize_convert pair.1)
      (.trans _ _ _ h (.symm _ _ (normalize_convert pair.2)))
  · exact (normalizationOperation Γ A).preserves pair

theorem native_faces :
    (decisionService Γ A).face = .directDecision ∧
    (normalizationService Γ A).face = .nativeOperation ∧
    NIK.Service.hasExternalCertificateBoundary (decisionService Γ A) = false ∧
    NIK.Service.hasExternalCertificateBoundary (normalizationService Γ A) = false :=
  ⟨rfl, rfl, rfl, rfl⟩

open SimpleFragmentErasureBoundary in
/-- The native operation performs computation: it is not the raw identity map. -/
theorem normalization_changes_raw_syntax :
    (normalizationOperation [] (.arr .atom .atom)).run
      (discardAtomicIdentity, discardFunctionIdentity) ≠
        (discardAtomicIdentity, discardFunctionIdentity) := by
  intro unchanged
  have normalized := congrArg Prod.fst unchanged
  have normal := normalize_normal discardAtomicIdentity
  rw [show (normalize discardAtomicIdentity).normalForm = discardAtomicIdentity from normalized]
    at normal
  exact discardAtomicIdentity_not_normal normal

open SimpleFragmentErasureBoundary in
theorem accepts_discarded_identities :
    decideConversion discardAtomicIdentity discardFunctionIdentity = true :=
  (decideConversion_correct _ _).2 discarded_identities_convert

theorem rejects_distinct_variables :
    decideConversion (.var .zero : Term [.atom, .atom] .atom) (.var (.succ .zero)) = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  exact distinct_variables_not_convertible ((decideConversion_correct _ _).1 accepted)

/-- Extensional eta equality remains distinct from the selected beta equality. -/
def etaVariable : Term [.arr .atom .atom] (.arr .atom .atom) := .var .zero

def etaExpansion : Term [.arr .atom .atom] (.arr .atom .atom) :=
  .lam (.app (.var (.succ .zero)) (.var .zero))

theorem eta_same_denotation {Ground : Type*}
    (environment : Environment Ground [.arr .atom .atom]) :
    etaVariable.denote environment = etaExpansion.denote environment := rfl

theorem eta_not_betaConvertible : ¬ BetaConv etaVariable etaExpansion := by
  intro h
  have equal := Normal.eq_of_towerConv (Normal.neutral (.var .zero))
    (Normal.lam (.neutral (.app (.var (.succ .zero)) (.neutral (.var .zero))))) h.erase
  cases equal

theorem rejects_eta : decideConversion etaVariable etaExpansion = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  exact eta_not_betaConvertible ((decideConversion_correct _ _).1 accepted)

#print axioms towerConv_iff_betaConv
#print axioms betaClass_toTower_injective
#print axioms betaClassEquivNormal
#print axioms decideConversion_correct
#print axioms normalizationOperation_meaning_iff
#print axioms normalization_changes_raw_syntax
#print axioms rejects_eta

end SimpleFragmentConversionDecision
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
