import Mettapedia.OSLF.Syntax.CategoricalBindingStageCore

/-!
# Reading substitution and metavariables at stage points

The point laws and their restaging hold before choosing any equation quotient
or map between equation models.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalBindingModel

open _root_.CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.FreeBindingTerms (FamilyArgs)
open Mettapedia.OSLF.Binding.SecondOrderContext

universe u v

variable {S : Signature}

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

namespace Model

variable (M : Model S D)

/-- Two successive stage changes agree with their composite. -/
theorem restageElem_restageElem {C C' C'' : D} (f : C ⟶ C') (g : C' ⟶ C'') {Γ : Ctx S}
    {s : S.Srt} (x : M.ElemOver C'' Γ s) :
    M.restageElem f (M.restageElem g x) = M.restageElem (f ≫ g) x := by
  apply ElemOver.ext
  funext W w ρ
  exact congrArg (fun m => x.value W m ρ) (Category.assoc w f g)

/-- A metavariable applied to its own variables, read at a point, is the
point's component. -/
theorem restageElem_interp_metaVar (X : List (MetaArity S)) {Z : D} (p : Z ⟶ M.family X)
    (i : Fin X.length) :
    M.restageElem p (M.interp X (metaVar i)) = M.elemOfPoint (p ≫ M.familyProj X i) := by
  apply M.elemEquiv.injective
  refine (M.elemEquiv_restage p _).trans ?_
  refine (congrArg (p ≫ ·) (M.generic_metaVar X i)).trans ?_
  exact (M.elemEquiv.right_inv _).symm

/-- Substituted terms read at a point are substituted readings. -/
theorem restageElem_interp_bind (X : List (MetaArity S)) {Z : D} (p : Z ⟶ M.family X)
    {Γ Δ : Ctx S} {s : S.Srt} (σ : Sub (withMetas S X) Γ Δ) (t : Term (withMetas S X) Γ s) :
    M.restageElem p (M.interp X (bind σ t)) =
      (M.kripkeSubstitution Z (N' := [])).substitute
        (fun γ v => M.restageElem p (M.interp X (σ γ v))) (M.restageElem p (M.interp X t)) := by
  apply ElemOver.ext
  funext W w ρ
  exact M.interp_bind X σ t W (w ≫ p) ρ


end Model

end Mettapedia.OSLF.Binding.CategoricalBindingModel
