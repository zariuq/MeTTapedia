import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedPresheafSetting
import Mettapedia.OSLF.Syntax.SecondOrderEquationProducts
import Mettapedia.OSLF.Syntax.CategoricalBindingGroupoid

/-!
# Actual program products under the operational Yoneda embedding

The program restriction uses the authored equation quotient, the event-free
section, and lifted Yoneda. Its terminal and head/tail product cones are the
images of the existing equation-context limit cones. Selected binder powers
can then be joined to this checked product data without another product
construction.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.CategoricalBindingModel

universe w

variable {S : Signature} (R : List (LocalRule S))
variable {K : List (MetaArity S)} (equations : List (EqAxiom S K))

/-- The chosen head assignment is the first projection of the original
context product, before taking its equation class. -/
theorem firstProjection_headArrow (arity : MetaArity S) (X : Object S) :
    firstProjection S (oneObj arity.1 arity.2) X = headArrow arity X := by
  apply oneObj_hom_ext
  rfl

/-- The chosen tail assignment is the second original context projection. -/
theorem secondProjection_tailArrow (arity : MetaArity S) (X : Object S) :
    secondProjection S (oneObj arity.1 arity.2) X = tailArrow arity X := by
  funext i
  rfl

/-- The image of the empty authored context is terminal in the actual
presheaf target, exactly as required by CartesianArities. -/
def programRestriction_terminal :
    IsTerminal ((programRestriction.{w} R equations).obj ⟨[]⟩) := by
  let _ := programEmbedding_preservesLimits.{w} R equations
  exact (quotientEmptyIsTerminal (authoredEquationPresentation S equations)).isTerminalObj
    (programSection R equations ⋙ embedding.{w} R equations)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The mapped head and tail assignments form the chosen binary product
cone, exactly as required by CartesianArities. -/
def programRestriction_cons (arity : MetaArity S) (X : Object S) :
    IsLimit (BinaryFan.mk
      ((programRestriction.{w} R equations).map (headArrow arity X))
      ((programRestriction.{w} R equations).map (tailArrow arity X))) := by
  let _ := programEmbedding_preservesLimits.{w} R equations
  have rawLimit : IsLimit (BinaryFan.mk
      ((authoredEquationPresentation S equations).quotientFunctor.map (headArrow arity X))
      ((authoredEquationPresentation S equations).quotientFunctor.map (tailArrow arity X))) := by
    have given := quotientProductIsLimit (authoredEquationPresentation S equations)
      (oneObj arity.1 arity.2) X
    rw [firstProjection_headArrow, secondProjection_tailArrow] at given
    exact given
  exact mapIsLimitOfPreservesOfIsLimit
    (programSection R equations ⋙ embedding.{w} R equations) _ _ rawLimit


/-- Assemble the independently supplied selected binder powers with the
proved terminal and product cones of the actual program restriction. -/
def programRestrictionArities
    (powers : ∀ (Γ : Ctx S) (s : S.Srt),
      Exponential (contextOf (sortOf (programRestriction.{w} R equations)) Γ)
        (sortOf (programRestriction.{w} R equations) s)
        ((programRestriction.{w} R equations).obj (oneObj Γ s))) :
    CartesianArities (programRestriction.{w} R equations) where
  terminal := programRestriction_terminal R equations
  cons := programRestriction_cons R equations
  exponential := powers

variable (powers : ∀ (Γ : Ctx S) (s : S.Srt),
  Exponential (contextOf (sortOf (programRestriction.{w} R equations)) Γ)
    (sortOf (programRestriction.{w} R equations) s)
    ((programRestriction.{w} R equations).obj (oneObj Γ s)))

/-- Use the existing family-object comparison of the checked arity products.
The selected powers are an independent ingredient of this construction API. -/
abbrev programRestrictionFamilyIso (arities : List (MetaArity S)) :
    (programRestriction.{w} R equations).obj ⟨arities⟩ ≅
      familyOf (fun Γ s => (programRestriction.{w} R equations).obj (oneObj Γ s)) arities :=
  (programRestrictionArities R equations powers).famIso arities

/-- The declared operator is the image of its actual generic opTerm arrow,
read through the existing family-object comparison. -/
def programRestrictionData : PreservingData (programRestriction.{w} R equations) where
  toCartesianArities := programRestrictionArities R equations powers
  op o := (programRestrictionFamilyIso R equations powers (S.arity o)).inv ≫
    (programRestriction.{w} R equations).map (termArrow (opTerm o))

/-- Each listed family projection is the image of the actual contextual
slot assignment, at every binder arity and every position. -/
theorem programRestriction_familyProj (arities : List (MetaArity S))
    (position : Fin arities.length) :
    (programRestrictionFamilyIso R equations powers arities).hom ≫
        (programRestrictionData R equations powers).toModel.familyProj arities position =
      (programRestriction.{w} R equations).map (slot arities position) :=
  (programRestrictionData R equations powers).famIso_proj arities position

/-- The operator arrow transported through the family comparison is exactly
the image of the authored operator applied to its generic metavariables. -/
theorem programRestriction_opTerm {s : S.Srt} (op : S.Op s) :
    (programRestrictionFamilyIso R equations powers (S.arity op)).hom ≫
        (programRestrictionData R equations powers).op op =
      (programRestriction.{w} R equations).map (termArrow (opTerm op)) := by
  exact (programRestrictionFamilyIso R equations powers (S.arity op)).hom_inv_id_assoc _

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf

end
