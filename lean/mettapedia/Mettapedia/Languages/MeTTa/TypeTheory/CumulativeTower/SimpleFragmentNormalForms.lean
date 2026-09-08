import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SimpleFragmentConversion
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.TowerConversionSkeleton

/-!
# Intrinsic normal forms retain their typing information under erasure

In a neutral term, the head variable and its application spine determine the
types of every argument. A normal lambda's declared result type determines
its binder type. Consequently erasure is injective on beta-normal intrinsic
terms at a fixed context and result type, although it is not injective on
arbitrary intrinsic terms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace FourFaceBetaExperiment.IntrinsicSTT

open TowerDTT

mutual
  /-- A variable-headed application spine with normal arguments. -/
  inductive Neutral : {Γ : List Ty} → {A : Ty} → Term Γ A → Prop
    | var {Γ : List Ty} {A : Ty} (v : Var Γ A) : Neutral (.var v)
    | app {Γ : List Ty} {A B : Ty} {f : Term Γ (.arr A B)} {a : Term Γ A} :
        Neutral f → Normal a → Neutral (.app f a)

  /-- A beta-normal intrinsic term. -/
  inductive Normal : {Γ : List Ty} → {A : Ty} → Term Γ A → Prop
    | neutral {Γ : List Ty} {A : Ty} {t : Term Γ A} : Neutral t → Normal t
    | lam {Γ : List Ty} {A B : Ty} {body : Term (A :: Γ) B} : Normal body → Normal (.lam body)
end

variable {Γ : List Ty} {A B : Ty}

/-- A variable's de Bruijn position determines both its type and its intrinsic
variable constructor in a fixed context. -/
theorem Var.type_eq_and_heq_of_erase_eq {v : Var Γ A} {w : Var Γ B}
    (equal : eraseVar v = eraseVar w) : A = B ∧ HEq v w := by
  induction v generalizing B with
  | zero =>
      cases w with
      | zero => exact ⟨rfl, HEq.rfl⟩
      | succ w =>
          have indices := congrArg Fin.val equal
          simp [eraseVar] at indices
  | succ v ih =>
      cases w with
      | zero =>
          have indices := congrArg Fin.val equal
          simp [eraseVar] at indices
      | succ w =>
          obtain ⟨rfl, same⟩ := ih (Fin.succ_inj.mp equal)
          cases same
          exact ⟨rfl, HEq.rfl⟩

private theorem erasure_properties (left : Term Γ A) :
    (∀ (right : Term Γ A), Normal left → Normal right →
      eraseTerm left = eraseTerm right → left = right) ∧
    (∀ {B : Ty} (right : Term Γ B), Neutral left → Neutral right →
      eraseTerm left = eraseTerm right → A = B ∧ HEq left right) := by
  induction left with
  | @var Γ A v =>
      have neutralCase : ∀ {B : Ty} (right : Term Γ B), Neutral right →
          eraseTerm (.var v) = eraseTerm right → A = B ∧ HEq (Term.var v) right := by
        intro B right rightNeutral equal
        cases rightNeutral with
        | var w =>
            obtain ⟨rfl, same⟩ := Var.type_eq_and_heq_of_erase_eq
              (Presentation.Tm.var.inj equal)
            cases same
            exact ⟨rfl, HEq.rfl⟩
        | app _ _ => cases equal
      constructor
      · intro right _ rightNormal equal
        cases rightNormal with
        | neutral rightNeutral => exact eq_of_heq (neutralCase _ rightNeutral equal).2
        | lam _ => cases equal
      · intro B right _ rightNeutral equal
        exact neutralCase right rightNeutral equal
  | @lam Γ A B body ih =>
      constructor
      · intro right leftNormal rightNormal equal
        cases leftNormal with
        | neutral neutral => cases neutral
        | lam leftBody =>
            cases rightNormal with
            | neutral rightNeutral => cases rightNeutral <;> cases equal
            | lam rightBody =>
                exact congrArg Term.lam (ih.1 _ leftBody rightBody
                  (Presentation.Tm.lam.inj equal))
      · intro C right leftNeutral
        cases leftNeutral
  | @app Γ A B function argument functionIH argumentIH =>
      have neutralCase : ∀ {C : Ty} (right : Term Γ C),
          Neutral (.app function argument) → Neutral right →
          eraseTerm (.app function argument) = eraseTerm right →
          B = C ∧ HEq (Term.app function argument) right := by
        intro C right leftNeutral rightNeutral equal
        cases leftNeutral with
        | app leftFunction leftArgument =>
            cases rightNeutral with
            | var _ => cases equal
            | app rightFunction rightArgument =>
                obtain ⟨functions, arguments⟩ := Presentation.Tm.app.inj equal
                obtain ⟨types, sameFunctions⟩ :=
                  functionIH.2 _ leftFunction rightFunction functions
                obtain ⟨domain, codomain⟩ := Ty.arr.inj types
                cases domain
                cases codomain
                have sameArguments := argumentIH.1 _ leftArgument rightArgument arguments
                cases sameFunctions
                cases sameArguments
                exact ⟨rfl, HEq.rfl⟩
      constructor
      · intro right leftNormal rightNormal equal
        cases leftNormal with
        | neutral leftNeutral =>
            cases rightNormal with
            | neutral rightNeutral =>
                exact eq_of_heq (neutralCase _ leftNeutral rightNeutral equal).2
            | lam _ => cases equal
      · exact neutralCase

/-- Equal erased neutral terms synthesize the same type and retain the same
intrinsic syntax. -/
theorem Neutral.type_eq_and_heq_of_erase_eq
    {left : Term Γ A} {right : Term Γ B}
    (leftNeutral : Neutral left) (rightNeutral : Neutral right)
    (equal : eraseTerm left = eraseTerm right) : A = B ∧ HEq left right :=
  (erasure_properties left).2 right leftNeutral rightNeutral equal

/-- At a fixed context and result type, beta-normal terms are determined by
their erased raw syntax. -/
theorem Normal.eq_of_erase_eq {left right : Term Γ A}
    (leftNormal : Normal left) (rightNormal : Normal right)
    (equal : eraseTerm left = eraseTerm right) : left = right :=
  (erasure_properties left).1 right leftNormal rightNormal equal

/-- Erasure is injective on the subtype of beta-normal terms. -/
theorem eraseNormal_injective :
    Function.Injective (fun t : {t : Term Γ A // Normal t} => eraseTerm t.1) := by
  intro left right equal
  exact Subtype.ext (Normal.eq_of_erase_eq left.2 right.2 equal)

/-- Intrinsic normal forms have no one-step beta reduct. -/
theorem Normal.no_betaStep {term : Term Γ A} (normal : Normal term) :
    ∀ target, ¬ BetaStep term target := by
  induction term with
  | var v => intro target step; cases step
  | lam body ih =>
      cases normal with
      | neutral neutral => cases neutral
      | lam bodyNormal =>
          intro target step
          cases step with
          | lam inner => exact ih bodyNormal _ inner
  | app function argument functionIH argumentIH =>
      cases normal with
      | neutral neutral =>
          cases neutral with
          | app functionNeutral argumentNormal =>
              intro target step
              cases step with
              | beta body argument => cases functionNeutral
              | appLeft inner => exact functionIH (.neutral functionNeutral) _ inner
              | appRight inner => exact argumentIH argumentNormal _ inner

/-- Every intrinsically typed beta-irreducible term is a normal form. -/
theorem Normal.of_no_betaStep {term : Term Γ A}
    (irreducible : ∀ target, ¬ BetaStep term target) : Normal term := by
  induction term with
  | var v => exact .neutral (.var v)
  | lam body ih =>
      exact .lam (ih (fun target step => irreducible _ (.lam step)))
  | app function argument functionIH argumentIH =>
      have functionNormal := functionIH (fun target step => irreducible _ (.appLeft step))
      have argumentNormal := argumentIH (fun target step => irreducible _ (.appRight step))
      cases functionNormal with
      | neutral functionNeutral => exact .neutral (.app functionNeutral argumentNormal)
      | lam bodyNormal => exact False.elim (irreducible _ (.beta _ _))

/-- Normal-form syntax and beta irreducibility describe exactly the same
intrinsic terms. -/
theorem Normal.iff_no_betaStep {term : Term Γ A} :
    Normal term ↔ ∀ target, ¬ BetaStep term target :=
  ⟨Normal.no_betaStep, Normal.of_no_betaStep⟩

/-- The computational skeleton of an intrinsic normal form is normal in the
larger Pure reduction relation, which also contains dependent constructors. -/
theorem Normal.skeleton_normal {term : Term Γ A} (normal : Normal term) :
    Pure.Intrinsic.PresentationBoundary.RedNormal
      (Presentation.TowerConversionSkeleton.erase (eraseTerm term)) := by
  induction term with
  | var v => intro target step; cases step
  | lam body ih =>
      cases normal with
      | neutral neutral => cases neutral
      | lam bodyNormal =>
          intro target step
          cases step with
          | congLam inner => exact ih bodyNormal _ inner
  | app function argument functionIH argumentIH =>
      cases normal with
      | neutral neutral =>
          cases neutral with
          | app functionNeutral argumentNormal =>
              have functionNormal := Normal.neutral functionNeutral
              cases functionNeutral <;> intro target step <;> cases step with
              | congAppFun inner => exact functionIH functionNormal _ inner
              | congAppArg inner => exact argumentIH argumentNormal _ inner

/-- The Pure computational skeleton loses no further syntax on the simple
lambda fragment: its legacy embedding reconstructs the raw tower erasure. -/
theorem reconstruct_skeleton (term : Term Γ A) :
    Presentation.Legacy.embed (Presentation.Legacy.ofPure
      (Presentation.TowerConversionSkeleton.erase (eraseTerm term))) = eraseTerm term := by
  induction term with
  | var v => rfl
  | lam body ih => exact congrArg Presentation.Tm.lam ih
  | app function argument functionIH argumentIH =>
      exact congrArg₂ Presentation.Tm.app functionIH argumentIH

/-- Equal computational skeletons determine equal normal intrinsic terms at
a fixed context and result type. -/
theorem Normal.eq_of_skeleton_eq {left right : Term Γ A}
    (leftNormal : Normal left) (rightNormal : Normal right)
    (equal : Presentation.TowerConversionSkeleton.erase (eraseTerm left) =
      Presentation.TowerConversionSkeleton.erase (eraseTerm right)) : left = right := by
  apply leftNormal.eq_of_erase_eq rightNormal
  have reconstructed := congrArg
    (fun term => Presentation.Legacy.embed (Presentation.Legacy.ofPure term)) equal
  simpa only [reconstruct_skeleton] using reconstructed

/-- Tower conversion cannot identify distinct beta-normal intrinsic terms.
This statement includes conversion paths through the full tower syntax. -/
theorem Normal.eq_of_towerConv {left right : Term Γ A}
    (leftNormal : Normal left) (rightNormal : Normal right)
    (conversion : Presentation.Conv Presentation.Tower.HeadEq
      (eraseTerm left) (eraseTerm right)) : left = right :=
  leftNormal.eq_of_skeleton_eq rightNormal
    (Presentation.TowerConversionSkeleton.erase_eq_of_conv
      leftNormal.skeleton_normal rightNormal.skeleton_normal conversion)

/-- The ordinary closed identity is normal. -/
theorem identity_normal : Normal SimpleFragmentErasureBoundary.identityTerm :=
  .lam (.neutral (.var .zero))

/-- The annotation-erasure collision necessarily leaves the normal fragment. -/
theorem discardAtomicIdentity_not_normal :
    ¬ Normal SimpleFragmentErasureBoundary.discardAtomicIdentity := by
  intro normal
  cases normal with
  | neutral neutral => cases neutral
  | lam body =>
      cases body with
      | neutral neutral =>
          cases neutral with
          | app function _ => cases function

#print axioms Var.type_eq_and_heq_of_erase_eq
#print axioms Neutral.type_eq_and_heq_of_erase_eq
#print axioms Normal.eq_of_erase_eq
#print axioms eraseNormal_injective
#print axioms Normal.iff_no_betaStep
#print axioms Normal.skeleton_normal
#print axioms Normal.eq_of_towerConv
#print axioms identity_normal
#print axioms discardAtomicIdentity_not_normal

end FourFaceBetaExperiment.IntrinsicSTT
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
