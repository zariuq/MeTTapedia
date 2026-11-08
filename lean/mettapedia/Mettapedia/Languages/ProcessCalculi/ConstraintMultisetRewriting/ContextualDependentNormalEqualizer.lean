import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalSupport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRenameAgreement

/-!
# Normal equality of two instances of one term forces pointwise agreement

In the rigid-constant profile, two normal renamings of one raw term can be
typed-equal only when the maps agree on every used variable. Function and
pair eta are handled by their normal observations. This is stronger than
equality of support images, which alone does not justify equalizer pruning.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentNormalEqualizer

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ContextualDependentNormalChecking ContextualDependentNormalObservations
open ContextualDependentRenameAgreement

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (rigid : ∀ name, S.roles name = .rigid)

def SameSource {n : Nat} (first second : Tm Head n) : Prop :=
  ∀ {k : Nat} (term : Tm Head k) (left right : Ren k n),
    Presentation.rename left term = first → Presentation.rename right term = second →
      Agrees left right term.support

theorem sameSource_self {n : Nat} (value : Tm Head n) : SameSource value value := by
  intro k term left right first second
  exact (rename_eq_iff_agrees term left right).mp (first.trans second.symm)

def After {n : Nat} (first second : Tm Head n) : Prop :=
  ∀ left right, WhRed S.R S.roles first left → Normal (S := S) left →
    WhRed S.R S.roles second right → Normal (S := S) right → SameSource left right

def Coincides : AlgorithmicStatement Head → Prop
  | .types _ first second | .typesW _ first second => After (S := S) first second
  | .terms _ first second _ | .termsW _ first second _ => After (S := S) first second
  | .spines _ first second _ | .spinesW _ first second _ => After (S := S) first second

include rigid in
theorem algorithmic_agreement {statement : AlgorithmicStatement Head}
    (proof : Algorithmic S.R S.roles statement) : Coincides (S := S) statement := by
  induction proof with
  | types firstRed secondRed firstForm secondForm comparison ih =>
      intro left right leftRed leftNormal rightRed rightNormal
      exact ih left right (WhRed.to_whnf S.shape leftRed (normal_whnf leftNormal) firstRed.red) leftNormal
        (WhRed.to_whnf S.shape rightRed (normal_whnf rightNormal) secondRed.red) rightNormal
  | @heads n Γ first second level same firstTyped secondTyped universeWitness =>
      intro left right leftRed leftNormal rightRed rightNormal
      have leftEq := WhRed.eq_of_whnf (S := S) (head_whnf S.shape first) leftRed
      subst left
      have rightEq := WhRed.eq_of_whnf (S := S) (head_whnf S.shape second) rightRed
      subst right
      intro k term rho sigma image _
      obtain rfl := rename_eq_head image
      exact agrees_empty rho sigma
  | @pi n Γ domain domain' body body' domainType domains bodies ihDomain ihBody =>
      intro left right leftRed leftNormal rightRed rightNormal
      have leftEq := WhRed.eq_of_whnf (S := S) (pi_whnf S.shape domain body) leftRed
      subst left
      have rightEq := WhRed.eq_of_whnf (S := S) (pi_whnf S.shape domain' body') rightRed
      subst right
      intro k term rho sigma firstImage secondImage
      obtain ⟨sourceDomain, sourceBody, rfl, domainImage, bodyImage⟩ := StrongNormalization.rename_eq_pi firstImage
      have images := Tm.pi.inj secondImage
      have domainAgreement := ihDomain domain domain' .refl (fun _ step => leftNormal _ (.congPiDom step))
        .refl (fun _ step => rightNormal _ (.congPiDom step)) sourceDomain rho sigma domainImage images.1
      have bodyAgreement := ihBody body body' .refl (fun _ step => leftNormal _ (.congPiCod step))
        .refl (fun _ step => rightNormal _ (.congPiCod step)) sourceBody (liftRen rho) (liftRen sigma) bodyImage images.2
      exact (agrees_union rho sigma _ _).mpr ⟨domainAgreement, (agrees_lift rho sigma _).mp bodyAgreement⟩
  | @sigma n Γ domain domain' body body' domainType domains bodies ihDomain ihBody =>
      intro left right leftRed leftNormal rightRed rightNormal
      have leftEq := WhRed.eq_of_whnf (S := S) (sigma_whnf S.shape domain body) leftRed
      subst left
      have rightEq := WhRed.eq_of_whnf (S := S) (sigma_whnf S.shape domain' body') rightRed
      subst right
      intro k term rho sigma firstImage secondImage
      obtain ⟨sourceDomain, sourceBody, rfl, domainImage, bodyImage⟩ := StrongNormalization.rename_eq_sigma firstImage
      have images := Tm.sigma.inj secondImage
      have domainAgreement := ihDomain domain domain' .refl (fun _ step => leftNormal _ (.congSigmaDom step))
        .refl (fun _ step => rightNormal _ (.congSigmaDom step)) sourceDomain rho sigma domainImage images.1
      have bodyAgreement := ihBody body body' .refl (fun _ step => leftNormal _ (.congSigmaCod step))
        .refl (fun _ step => rightNormal _ (.congSigmaCod step)) sourceBody (liftRen rho) (liftRen sigma) bodyImage images.2
      exact (agrees_union rho sigma _ _).mpr ⟨domainAgreement, (agrees_lift rho sigma _).mp bodyAgreement⟩
  | @id n Γ carrier carrier' first first' second second' carriers firsts seconds ihCarrier ihFirst ihSecond =>
      intro left right leftRed leftNormal rightRed rightNormal
      have leftEq := WhRed.eq_of_whnf (S := S) (id_whnf S.shape carrier first second) leftRed
      subst left
      have rightEq := WhRed.eq_of_whnf (S := S) (id_whnf S.shape carrier' first' second') rightRed
      subst right
      intro k term rho sigma firstImage secondImage
      obtain ⟨sourceCarrier, sourceFirst, sourceSecond, rfl, carrierImage, firstImage, lastImage⟩ :=
        StrongNormalization.rename_eq_id firstImage
      have images := Tm.id.inj secondImage
      have carrierAgreement := ihCarrier carrier carrier' .refl (fun _ step => leftNormal _ (.congIdTy step))
        .refl (fun _ step => rightNormal _ (.congIdTy step)) sourceCarrier rho sigma carrierImage images.1
      have firstAgreement := ihFirst first first' .refl (fun _ step => leftNormal _ (.congIdLeft step))
        .refl (fun _ step => rightNormal _ (.congIdLeft step)) sourceFirst rho sigma firstImage images.2.1
      have secondAgreement := ihSecond second second' .refl (fun _ step => leftNormal _ (.congIdRight step))
        .refl (fun _ step => rightNormal _ (.congIdRight step)) sourceSecond rho sigma lastImage images.2.2
      exact (agrees_union rho sigma _ _).mpr ⟨(agrees_union rho sigma _ _).mpr ⟨carrierAgreement, firstAgreement⟩, secondAgreement⟩
  | @inductiveType n Γ name constructors role type =>
      intro left right leftRed leftNormal rightRed rightNormal
      have neutral : Neutral S.roles (.const name : Tm Head n) := .rigid [] (rigid name)
      have leftEq := WhRed.eq_of_whnf (S := S) (neutral.whnf S.shape) leftRed
      subst left
      have rightEq := WhRed.eq_of_whnf (S := S) (neutral.whnf S.shape) rightRed
      subst right
      exact @sameSource_self Head n (.const name)
  | neutralTypes _ _ _ _ ih => exact ih
  | terms typeRed typeForm firstRed secondRed comparison ih =>
      intro left right leftRed leftNormal rightRed rightNormal
      exact ih left right (WhRed.to_whnf S.shape leftRed (normal_whnf leftNormal) firstRed.red) leftNormal
        (WhRed.to_whnf S.shape rightRed (normal_whnf rightNormal) secondRed.red) rightNormal
  | univ _ _ _ _ ih => exact ih
  | @eta n Γ first second domain codomain domainType firstTyped firstForm secondTyped secondForm comparison ih =>
      intro left right leftRed leftNormal rightRed rightNormal
      have leftEq := WhRed.eq_of_whnf (S := S) (function_whnf rigid firstForm) leftRed
      subst left
      have rightEq := WhRed.eq_of_whnf (S := S) (function_whnf rigid secondForm) rightRed
      subst right
      intro k term rho sigma firstImage secondImage
      apply agrees_of_fresh rho sigma term
      exact ih (freshValue first) (freshValue second)
        (fresh_reduces (S := S) first) (fresh_normal rigid leftNormal)
        (fresh_reduces (S := S) second) (fresh_normal rigid rightNormal)
        (freshValue term) (liftRen rho) (liftRen sigma)
        ((fresh_rename rho term).symm.trans (congrArg freshValue firstImage))
        ((fresh_rename sigma term).symm.trans (congrArg freshValue secondImage))
  | @sigmaEta n Γ first second domain codomain firstTyped firstForm secondTyped secondForm
      firstComparison secondComparison ihFirst ihSecond =>
      intro left right leftRed leftNormal rightRed rightNormal
      have leftEq := WhRed.eq_of_whnf (S := S) (pair_whnf_of_shape firstForm) leftRed
      subst left
      have rightEq := WhRed.eq_of_whnf (S := S) (pair_whnf_of_shape secondForm) rightRed
      subst right
      intro k term rho sigma firstImage secondImage
      have firstNormals := projections_normal rigid leftNormal
      have secondNormals := projections_normal rigid rightNormal
      apply agrees_of_projections rho sigma term
      · exact ihFirst (firstValue first) (firstValue second)
          (first_reduces (S := S) first) firstNormals.1 (first_reduces (S := S) second) secondNormals.1
          (firstValue term) rho sigma
          ((first_rename rho term).symm.trans (congrArg firstValue firstImage))
          ((first_rename sigma term).symm.trans (congrArg firstValue secondImage))
      · exact ihSecond (secondValue first) (secondValue second)
          (second_reduces (S := S) first) firstNormals.2 (second_reduces (S := S) second) secondNormals.2
          (secondValue term) rho sigma
          ((second_rename rho term).symm.trans (congrArg secondValue firstImage))
          ((second_rename sigma term).symm.trans (congrArg secondValue secondImage))
  | @refl n Γ first second carrier a b firstTyped secondTyped comparison ih =>
      intro left right leftRed leftNormal rightRed rightNormal
      have leftEq := WhRed.eq_of_whnf (S := S) (refl_whnf S.shape first) leftRed
      subst left
      have rightEq := WhRed.eq_of_whnf (S := S) (refl_whnf S.shape second) rightRed
      subst right
      intro k term rho sigma firstImage secondImage
      obtain ⟨source, rfl, image⟩ := StrongNormalization.rename_eq_refl firstImage
      exact ih first second .refl (fun _ step => leftNormal _ (.congRefl step))
        .refl (fun _ step => rightNormal _ (.congRefl step)) source rho sigma image (Tm.refl.inj secondImage)
  | spine _ _ _ _ _ _ ih => exact ih
  | @var n Γ index =>
      intro left right leftRed leftNormal rightRed rightNormal
      have leftEq := WhRed.eq_of_whnf (S := S) (var_whnf S.shape index) leftRed
      subst left
      have rightEq := WhRed.eq_of_whnf (S := S) (var_whnf S.shape index) rightRed
      subst right
      exact @sameSource_self Head n (.var index)
  | @const n Γ name type declared typed =>
      intro left right leftRed leftNormal rightRed rightNormal
      have neutral : Neutral S.roles (.const name : Tm Head n) := .rigid [] (rigid name)
      have leftEq := WhRed.eq_of_whnf (S := S) (neutral.whnf S.shape) leftRed
      subst left
      have rightEq := WhRed.eq_of_whnf (S := S) (neutral.whnf S.shape) rightRed
      subst right
      exact @sameSource_self Head n (.const name)
  | @app n Γ first second argument argument' domain codomain functions arguments ihFunction ihArgument =>
      intro left right leftRed leftNormal rightRed rightNormal
      have neutral := ContextualDependentNormalSupport.spine_shape rigid functions Γ first second _ (.inr rfl)
      have leftEq := WhRed.eq_of_whnf (S := S) ((Neutral.app neutral.1).whnf S.shape) leftRed
      subst left
      have rightEq := WhRed.eq_of_whnf (S := S) ((Neutral.app neutral.2).whnf S.shape) rightRed
      subst right
      intro k term rho sigma firstImage secondImage
      obtain ⟨sourceFunction, sourceArgument, rfl, functionImage, argumentImage⟩ := StrongNormalization.rename_eq_app firstImage
      have images := Tm.app.inj secondImage
      have functionAgreement := ihFunction first second .refl (fun _ step => leftNormal _ (.congAppFun step))
        .refl (fun _ step => rightNormal _ (.congAppFun step)) sourceFunction rho sigma functionImage images.1
      have argumentAgreement := ihArgument argument argument' .refl (fun _ step => leftNormal _ (.congAppArg step))
        .refl (fun _ step => rightNormal _ (.congAppArg step)) sourceArgument rho sigma argumentImage images.2
      exact (agrees_union rho sigma _ _).mpr ⟨functionAgreement, argumentAgreement⟩
  | @fst n Γ first second domain codomain pairs ih =>
      intro left right leftRed leftNormal rightRed rightNormal
      have neutral := ContextualDependentNormalSupport.spine_shape rigid pairs Γ first second _ (.inr rfl)
      have leftEq := WhRed.eq_of_whnf (S := S) ((Neutral.fst neutral.1).whnf S.shape) leftRed
      subst left
      have rightEq := WhRed.eq_of_whnf (S := S) ((Neutral.fst neutral.2).whnf S.shape) rightRed
      subst right
      intro k term rho sigma firstImage secondImage
      obtain ⟨source, rfl, image⟩ := StrongNormalization.rename_eq_fst firstImage
      exact ih first second .refl (fun _ step => leftNormal _ (.congFst step))
        .refl (fun _ step => rightNormal _ (.congFst step)) source rho sigma image (Tm.fst.inj secondImage)
  | @snd n Γ first second domain codomain pairs ih =>
      intro left right leftRed leftNormal rightRed rightNormal
      have neutral := ContextualDependentNormalSupport.spine_shape rigid pairs Γ first second _ (.inr rfl)
      have leftEq := WhRed.eq_of_whnf (S := S) ((Neutral.snd neutral.1).whnf S.shape) leftRed
      subst left
      have rightEq := WhRed.eq_of_whnf (S := S) ((Neutral.snd neutral.2).whnf S.shape) rightRed
      subst right
      intro k term rho sigma firstImage secondImage
      obtain ⟨source, rfl, image⟩ := StrongNormalization.rename_eq_snd firstImage
      exact ih first second .refl (fun _ step => leftNormal _ (.congSnd step))
        .refl (fun _ step => rightNormal _ (.congSnd step)) source rho sigma image (Tm.snd.inj secondImage)
  | spinesW _ _ _ ih => exact ih

include rigid in
theorem equal_agreement (complete : AlgorithmicComplete S.R S.roles)
    {n m : Nat} {Γ : Ctx Head m} (formed : CtxFormed S.R Γ) (term : Tm Head n) (left right : Ren n m)
    {type : Tm Head m}
    (same : Equal S.R Γ (Presentation.rename left term) (Presentation.rename right term) type)
    (normal : Normal (S := S) term) : Agrees left right term.support :=
  algorithmic_agreement rigid (complete formed same) _ _ .refl (normal_rename rigid left normal)
    .refl (normal_rename rigid right normal) term left right rfl rfl

include rigid in
theorem typeEq_agreement (complete : AlgorithmicComplete S.R S.roles)
    {n m : Nat} {Γ : Ctx Head m} (formed : CtxFormed S.R Γ) (term : Tm Head n) (left right : Ren n m)
    (same : TypeEq S.R Γ (Presentation.rename left term) (Presentation.rename right term))
    (normal : Normal (S := S) term) : Agrees left right term.support :=
  algorithmic_agreement rigid (complete.types same formed) _ _ .refl (normal_rename rigid left normal)
    .refl (normal_rename rigid right normal) term left right rfl rfl

include rigid in
theorem equal_renamings_literal (complete : AlgorithmicComplete S.R S.roles)
    {n m : Nat} {Γ : Ctx Head m} (formed : CtxFormed S.R Γ) (term : Tm Head n) (left right : Ren n m)
    {type : Tm Head m}
    (same : Equal S.R Γ (Presentation.rename left term) (Presentation.rename right term) type)
    (normal : Normal (S := S) term) : Presentation.rename left term = Presentation.rename right term :=
  (rename_eq_iff_agrees term left right).mpr (equal_agreement rigid complete formed term left right same normal)

include rigid in
theorem equal_iff_agrees (complete : AlgorithmicComplete S.R S.roles)
    {n m : Nat} {Γ : Ctx Head m} (formed : CtxFormed S.R Γ) (term : Tm Head n) (left right : Ren n m)
    {type : Tm Head m} (typed : Typed S.R Γ (Presentation.rename left term) type)
    (normal : Normal (S := S) term) :
    Equal S.R Γ (Presentation.rename left term) (Presentation.rename right term) type ↔ Agrees left right term.support := by
  constructor
  · exact fun same => equal_agreement rigid complete formed term left right same normal
  · intro agreement
    rw [← (rename_eq_iff_agrees term left right).mpr agreement]
    exact .refl typed

end ContextualDependentNormalEqualizer
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
