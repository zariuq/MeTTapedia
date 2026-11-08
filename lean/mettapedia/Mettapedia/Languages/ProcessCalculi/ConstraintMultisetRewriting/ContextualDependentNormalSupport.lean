import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalObservations

/-!
# Typed equality preserves normal support in the rigid-constant profile

The proof follows the existing algorithmic equality. Function eta is observed
at a fresh variable; pair eta is observed through both projections. Their
normal observations retain precisely the original outer support. This is a
necessary scope consequence of equality, not a converse equality test.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentNormalSupport

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ContextualDependentNormalChecking ContextualDependentNormalObservations ContextualDependentSupport

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (rigid : ∀ name, S.roles name = .rigid)

def SpineShape (statement : AlgorithmicStatement Head) : Prop :=
  ∀ {n : Nat} (Γ : Ctx Head n) (first second type : Tm Head n),
    (statement = .spines Γ first second type ∨ statement = .spinesW Γ first second type) →
      Neutral S.roles first ∧ Neutral S.roles second

include rigid in
theorem spine_shape {statement : AlgorithmicStatement Head} (proof : Algorithmic S.R S.roles statement) :
    SpineShape (S := S) statement := by
  induction proof with
  | var index =>
      intro n Γ first second type same
      rcases same with same | same <;> cases same
      exact ⟨.var index, .var index⟩
  | @const n Γ name type declared typed =>
      intro m Δ first second annotation same
      rcases same with same | same <;> cases same
      exact ⟨.rigid [] (rigid name), .rigid [] (rigid name)⟩
  | @app n Γ f g a b domain codomain functions arguments ihFunction ihArgument =>
      intro m Δ first second annotation same
      rcases same with same | same <;> cases same
      have functions := ihFunction Γ f g _ (.inr rfl)
      exact ⟨.app functions.1, .app functions.2⟩
  | @fst n Γ p q domain codomain pairs ih =>
      intro m Δ first second annotation same
      rcases same with same | same <;> cases same
      have pairs := ih Γ p q _ (.inr rfl)
      exact ⟨.fst pairs.1, .fst pairs.2⟩
  | @snd n Γ p q domain codomain pairs ih =>
      intro m Δ first second annotation same
      rcases same with same | same <;> cases same
      have pairs := ih Γ p q _ (.inr rfl)
      exact ⟨.snd pairs.1, .snd pairs.2⟩
  | @spinesW n Γ first second type normalType comparison red form ih =>
      intro m Δ left right annotation same
      rcases same with same | same <;> cases same
      exact ih Γ first second type (.inl rfl)
  | _ =>
      intro n Γ first second type same
      rcases same with same | same <;> cases same

def After {n : Nat} (first second : Tm Head n) : Prop :=
  ∀ left right, WhRed S.R S.roles first left → Normal (S := S) left →
    WhRed S.R S.roles second right → Normal (S := S) right → left.support = right.support

def Supports : AlgorithmicStatement Head → Prop
  | .types _ first second | .typesW _ first second => After (S := S) first second
  | .terms _ first second _ | .termsW _ first second _ => After (S := S) first second
  | .spines _ first second _ | .spinesW _ first second _ => After (S := S) first second

include rigid in
theorem algorithmic_support {statement : AlgorithmicStatement Head}
    (proof : Algorithmic S.R S.roles statement) : Supports (S := S) statement := by
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
      rfl
  | @pi n Γ domain domain' body body' domainType domains bodies ihDomain ihBody =>
      intro left right leftRed leftNormal rightRed rightNormal
      have leftEq := WhRed.eq_of_whnf (S := S) (pi_whnf S.shape domain body) leftRed
      subst left
      have rightEq := WhRed.eq_of_whnf (S := S) (pi_whnf S.shape domain' body') rightRed
      subst right
      have domains := ihDomain domain domain' .refl (fun _ step => leftNormal _ (.congPiDom step))
        .refl (fun _ step => rightNormal _ (.congPiDom step))
      have bodies := ihBody body body' .refl (fun _ step => leftNormal _ (.congPiCod step))
        .refl (fun _ step => rightNormal _ (.congPiCod step))
      exact congrArg₂ (fun a b => a ∪ b) domains (congrArg outerSupport bodies)
  | @sigma n Γ domain domain' body body' domainType domains bodies ihDomain ihBody =>
      intro left right leftRed leftNormal rightRed rightNormal
      have leftEq := WhRed.eq_of_whnf (S := S) (sigma_whnf S.shape domain body) leftRed
      subst left
      have rightEq := WhRed.eq_of_whnf (S := S) (sigma_whnf S.shape domain' body') rightRed
      subst right
      have domains := ihDomain domain domain' .refl (fun _ step => leftNormal _ (.congSigmaDom step))
        .refl (fun _ step => rightNormal _ (.congSigmaDom step))
      have bodies := ihBody body body' .refl (fun _ step => leftNormal _ (.congSigmaCod step))
        .refl (fun _ step => rightNormal _ (.congSigmaCod step))
      exact congrArg₂ (fun a b => a ∪ b) domains (congrArg outerSupport bodies)
  | @id n Γ carrier carrier' first first' second second' carriers firsts seconds ihCarrier ihFirst ihSecond =>
      intro left right leftRed leftNormal rightRed rightNormal
      have leftEq := WhRed.eq_of_whnf (S := S) (id_whnf S.shape carrier first second) leftRed
      subst left
      have rightEq := WhRed.eq_of_whnf (S := S) (id_whnf S.shape carrier' first' second') rightRed
      subst right
      have carriers := ihCarrier carrier carrier' .refl (fun _ step => leftNormal _ (.congIdTy step))
        .refl (fun _ step => rightNormal _ (.congIdTy step))
      have firsts := ihFirst first first' .refl (fun _ step => leftNormal _ (.congIdLeft step))
        .refl (fun _ step => rightNormal _ (.congIdLeft step))
      have seconds := ihSecond second second' .refl (fun _ step => leftNormal _ (.congIdRight step))
        .refl (fun _ step => rightNormal _ (.congIdRight step))
      exact congrArg₂ (fun a b => a ∪ b) (congrArg₂ (fun a b => a ∪ b) carriers firsts) seconds
  | @inductiveType n Γ name constructors role type =>
      intro left right leftRed leftNormal rightRed rightNormal
      have neutral : Neutral S.roles (.const name : Tm Head n) := .rigid [] (rigid name)
      have leftEq := WhRed.eq_of_whnf (S := S) (neutral.whnf S.shape) leftRed
      subst left
      have rightEq := WhRed.eq_of_whnf (S := S) (neutral.whnf S.shape) rightRed
      subst right
      rfl
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
      have observed := ih (freshValue first) (freshValue second)
        (fresh_reduces (S := S) first) (fresh_normal rigid leftNormal)
        (fresh_reduces (S := S) second) (fresh_normal rigid rightNormal)
      exact (fresh_support first).symm.trans ((congrArg outerSupport observed).trans (fresh_support second))
  | @sigmaEta n Γ first second domain codomain firstTyped firstForm secondTyped secondForm
      firstComparison secondComparison ihFirst ihSecond =>
      intro left right leftRed leftNormal rightRed rightNormal
      have leftEq := WhRed.eq_of_whnf (S := S) (pair_whnf_of_shape firstForm) leftRed
      subst left
      have rightEq := WhRed.eq_of_whnf (S := S) (pair_whnf_of_shape secondForm) rightRed
      subst right
      have firstNormals := projections_normal rigid leftNormal
      have secondNormals := projections_normal rigid rightNormal
      have firsts := ihFirst (firstValue first) (firstValue second)
        (first_reduces (S := S) first) firstNormals.1 (first_reduces (S := S) second) secondNormals.1
      have seconds := ihSecond (secondValue first) (secondValue second)
        (second_reduces (S := S) first) firstNormals.2 (second_reduces (S := S) second) secondNormals.2
      exact (projections_support first).symm.trans
        ((congrArg₂ (fun a b => a ∪ b) firsts seconds).trans (projections_support second))
  | @refl n Γ first second carrier a b firstTyped secondTyped comparison ih =>
      intro left right leftRed leftNormal rightRed rightNormal
      have leftEq := WhRed.eq_of_whnf (S := S) (refl_whnf S.shape first) leftRed
      subst left
      have rightEq := WhRed.eq_of_whnf (S := S) (refl_whnf S.shape second) rightRed
      subst right
      exact ih first second .refl (fun _ step => leftNormal _ (.congRefl step))
        .refl (fun _ step => rightNormal _ (.congRefl step))
  | spine _ _ _ _ _ _ ih => exact ih
  | @var n Γ index =>
      intro left right leftRed leftNormal rightRed rightNormal
      have leftEq := WhRed.eq_of_whnf (S := S) (var_whnf S.shape index) leftRed
      subst left
      have rightEq := WhRed.eq_of_whnf (S := S) (var_whnf S.shape index) rightRed
      subst right
      rfl
  | @const n Γ name type declared typed =>
      intro left right leftRed leftNormal rightRed rightNormal
      have neutral : Neutral S.roles (.const name : Tm Head n) := .rigid [] (rigid name)
      have leftEq := WhRed.eq_of_whnf (S := S) (neutral.whnf S.shape) leftRed
      subst left
      have rightEq := WhRed.eq_of_whnf (S := S) (neutral.whnf S.shape) rightRed
      subst right
      rfl
  | @app n Γ first second argument argument' domain codomain functions arguments ihFunction ihArgument =>
      intro left right leftRed leftNormal rightRed rightNormal
      have neutral := spine_shape rigid functions Γ first second _ (.inr rfl)
      have leftEq := WhRed.eq_of_whnf (S := S) ((Neutral.app neutral.1).whnf S.shape) leftRed
      subst left
      have rightEq := WhRed.eq_of_whnf (S := S) ((Neutral.app neutral.2).whnf S.shape) rightRed
      subst right
      have functions := ihFunction first second .refl (fun _ step => leftNormal _ (.congAppFun step))
        .refl (fun _ step => rightNormal _ (.congAppFun step))
      have arguments := ihArgument argument argument' .refl (fun _ step => leftNormal _ (.congAppArg step))
        .refl (fun _ step => rightNormal _ (.congAppArg step))
      exact congrArg₂ (fun a b => a ∪ b) functions arguments
  | @fst n Γ first second domain codomain pairs ih =>
      intro left right leftRed leftNormal rightRed rightNormal
      have neutral := spine_shape rigid pairs Γ first second _ (.inr rfl)
      have leftEq := WhRed.eq_of_whnf (S := S) ((Neutral.fst neutral.1).whnf S.shape) leftRed
      subst left
      have rightEq := WhRed.eq_of_whnf (S := S) ((Neutral.fst neutral.2).whnf S.shape) rightRed
      subst right
      exact ih first second .refl (fun _ step => leftNormal _ (.congFst step))
        .refl (fun _ step => rightNormal _ (.congFst step))
  | @snd n Γ first second domain codomain pairs ih =>
      intro left right leftRed leftNormal rightRed rightNormal
      have neutral := spine_shape rigid pairs Γ first second _ (.inr rfl)
      have leftEq := WhRed.eq_of_whnf (S := S) ((Neutral.snd neutral.1).whnf S.shape) leftRed
      subst left
      have rightEq := WhRed.eq_of_whnf (S := S) ((Neutral.snd neutral.2).whnf S.shape) rightRed
      subst right
      exact ih first second .refl (fun _ step => leftNormal _ (.congSnd step))
        .refl (fun _ step => rightNormal _ (.congSnd step))
  | spinesW _ _ _ ih => exact ih

include rigid in
theorem equal_support (complete : AlgorithmicComplete S.R S.roles)
    {n : Nat} {Γ : Ctx Head n} {first second type : Tm Head n}
    (formed : CtxFormed S.R Γ) (same : Equal S.R Γ first second type)
    (firstNormal : Normal (S := S) first) (secondNormal : Normal (S := S) second) :
    first.support = second.support :=
  algorithmic_support rigid (complete formed same) first second .refl firstNormal .refl secondNormal

include rigid in
theorem typeEq_support (complete : AlgorithmicComplete S.R S.roles)
    {n : Nat} {Γ : Ctx Head n} {first second : Tm Head n}
    (formed : CtxFormed S.R Γ) (same : TypeEq S.R Γ first second)
    (firstNormal : Normal (S := S) first) (secondNormal : Normal (S := S) second) :
    first.support = second.support :=
  algorithmic_support rigid (complete.types same formed) first second .refl firstNormal .refl secondNormal

end ContextualDependentNormalSupport
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
