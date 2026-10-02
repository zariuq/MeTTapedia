import Mettapedia.OSLF.Syntax.CategoricalBindingTargetPreservationElements
import Mettapedia.OSLF.Syntax.CategoricalBindingClassification

/-!
# Binding preservation under a change of categorical target

Postcomposition along a functor preserving finite products and the selected
binding function objects preserves the constructor interpretation laws.
The laws are derived from the original interpretation and the universal
property of the mapped function objects.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.CategoricalBindingModel

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.SecondOrderContext (Object)
open Mettapedia.OSLF.Binding.FreeBindingTerms (FamilyArgs)

universe u v u' v'

variable {S : Signature}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {D' : Type u'} [Category.{v'} D'] [CartesianMonoidalCategory D']
variable (H : D ⥤ D') [PreservesFiniteProducts H] [ExponentialPreservation H]

namespace CartesianArities

variable {F : Object S ⥤ D} (hF : CartesianArities F)

/-- The products and selected function objects of a postcomposed functor. -/
def postcompose : CartesianArities (F ⋙ H) where
  terminal := hF.terminal.isTerminalObj H
  cons a X := mapIsLimitOfPreservesOfIsLimit H _ _ (hF.cons a X)
  exponential Γ s := (imageExponential H (hF.exponential Γ s)).transport
    (contextComparison H (sortOf F) Γ) (Iso.refl _) (Iso.refl _)

end CartesianArities

namespace PreservingData

variable {F : Object S ⥤ D} (hF : PreservingData F)

/-- Postcomposition transports the actual operator arrows. -/
def postcompose : PreservingData (F ⋙ H) where
  toCartesianArities := hF.toCartesianArities.postcompose H
  op o := (familyComparison H (fun Γ s => F.obj (oneObj Γ s)) (S.arity o)).hom ≫ H.map (hF.op o)

/-- The reconstructed model is the model with image sorts and image powers. -/
theorem postcompose_toModel : (hF.postcompose H).toModel = mapModel H hF.toModel := rfl

/-- The canonical products of the postcomposed functor agree with the image
of the original products. -/
theorem postcompose_famIso (L : List (MetaArity S)) :
    ((hF.postcompose H).famIso L).hom ≫ (familyComparison H hF.toModel.power L).hom =
      H.map ((hF.famIso L).hom) := by
  apply (cancel_mono (familyComparison H hF.toModel.power L).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have left : ((hF.postcompose H).famIso L).hom =
      (hF.postcompose H).toModel.familyLift L (fun i => H.map (F.map (slot L i))) := by
    apply (hF.postcompose H).toModel.familyLift_unique
    intro i
    exact (hF.postcompose H).famIso_proj L i
  have right : H.map (hF.famIso L).hom ≫ (familyComparison H hF.toModel.power L).inv =
      (hF.postcompose H).toModel.familyLift L (fun i => H.map (F.map (slot L i))) := by
    apply (hF.postcompose H).toModel.familyLift_unique
    intro i
    change (H.map (hF.famIso L).hom ≫ (familyComparison H hF.toModel.power L).inv) ≫
      (mapModel H hF.toModel).familyProj L i = _
    rw [← familyComparison_proj H hF.toModel]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← H.map_comp, hF.famIso_proj]
  exact left.trans right.symm

end PreservingData

namespace Preserving

variable {F : Object S ⥤ D} (hF : Preserving F)

/-- Postcomposition carries each term arrow to the curried interpretation
in the model with actual image sorts and powers. -/
theorem postcompose_map_termArrow (X : Object S) {Γ : Ctx S} {s : S.Srt}
    (t : Term (withMetas S X.arities) Γ s) :
    (F ⋙ H).map (termArrow t) =
      ((hF.toPreservingData.postcompose H).famIso X.arities).hom ≫
        (hF.toPreservingData.postcompose H).toModel.curry
          ((hF.toPreservingData.postcompose H).toModel.generic X.arities t) := by
  change H.map (F.map (termArrow t)) = _
  rw [hF.map_termArrow X t, H.map_comp]
  change H.map ((hF.famIso X.arities).hom) ≫ H.map (hF.toModel.curry (hF.toModel.generic X.arities t)) =
    ((hF.toPreservingData.postcompose H).famIso X.arities).hom ≫
      (mapModel H hF.toModel).curry ((mapModel H hF.toModel).generic X.arities t)
  rw [mapModel_curry_generic H hF.toModel X.arities t]
  rw [← Category.assoc, hF.toPreservingData.postcompose_famIso H]

/-- Every postcomposed term meaning is the independently defined term fold.
Naturality extends the generic arrow calculation to all target stages. -/
theorem postcompose_meaning_eq_interp {X : Object S} {Γ : Ctx S} {s : S.Srt}
    (t : Term (withMetas S X.arities) Γ s) :
    (hF.toPreservingData.postcompose H).meaning t =
      (hF.toPreservingData.postcompose H).toModel.interp X.arities t := by
  let M := (hF.toPreservingData.postcompose H).toModel
  apply Model.ElemOver.ext
  funext Z m ρ
  change lift (M.tupleEnv ρ) (m ≫ ((hF.toPreservingData.postcompose H).famIso X.arities).inv ≫
    (F ⋙ H).map (termArrow t)) ≫ M.eval Γ s = (M.interp X.arities t).value Z m ρ
  rw [hF.postcompose_map_termArrow H X t, Iso.inv_hom_id_assoc]
  have split : lift (M.tupleEnv ρ) (m ≫ M.curry (M.generic X.arities t)) =
      lift (M.tupleEnv ρ) m ≫ (M.ctx Γ ◁ M.curry (M.generic X.arities t)) := by
    rw [lift_whiskerLeft]
  rw [split, Category.assoc, M.curry_eval, M.value_eq_generic]
  rfl

/-- Products, selected exponentials and every authored constructor law are
preserved by qualified postcomposition. -/
def postcompose : Preserving (F ⋙ H) where
  toPreservingData := hF.toPreservingData.postcompose H
  meaning_var := fun X Γ γ v => by
    rw [hF.postcompose_meaning_eq_interp H]
    rfl
  meaning_op := fun X Γ s o args => by
    rw [hF.postcompose_meaning_eq_interp H]
    change (hF.toPreservingData.postcompose H).toModel.opElem o
      (FreeBindingTerms.foldArgs ((hF.toPreservingData.postcompose H).toModel.kripke X.arities).toRaw args) = _
    rw [foldArgs_eq_map]
    congr 1
    exact familyArgs_map_congr (fun t => (hF.postcompose_meaning_eq_interp H t).symm) _
  meaning_meta := fun X Γ j args => by
    rw [hF.postcompose_meaning_eq_interp H]
    change (hF.toPreservingData.postcompose H).toModel.metaElem j
      (FreeBindingTerms.foldArgs ((hF.toPreservingData.postcompose H).toModel.kripke X.arities).toRaw args) = _
    rw [foldArgs_eq_map]
    congr 1
    exact familyArgs_map_congr (fun t => (hF.postcompose_meaning_eq_interp H t).symm) _

end Preserving

end Mettapedia.OSLF.Binding.CategoricalBindingModel
