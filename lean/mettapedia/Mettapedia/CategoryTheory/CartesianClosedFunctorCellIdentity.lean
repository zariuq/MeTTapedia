import Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence

/-!
# Complete product and function readings of natural cells

Projection naturality determines both components of a product cell.
Evaluation naturality and the target's actual closed adjunction determine a
function cell when its argument and result components are fixed. No identity
at the product of a function with its argument is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.CartesianClosedFunctorCellIdentity

open _root_.CategoryTheory MonoidalCategory
open _root_.CategoryTheory.Limits (PreservesFiniteLimits)
open CartesianMonoidalCategory MonoidalClosed

universe u w v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]
variable {D : Type w} [Category.{v} D] [CartesianMonoidalCategory D] [MonoidalClosed D]
variable (mapping : C ⥤ D) (cell : mapping ⟶ mapping)

omit [MonoidalClosed C] [MonoidalClosed D] in
theorem product_natural (first second : C) :
    prodComparison mapping first second ≫ (cell.app first ⊗ₘ cell.app second) =
      cell.app (first ⊗ second) ≫ prodComparison mapping first second := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, tensorHom_fst, prodComparison_fst, prodComparison_fst_assoc]
    exact cell.naturality (fst first second)
  · simp only [Category.assoc, tensorHom_snd, prodComparison_snd, prodComparison_snd_assoc]
    exact cell.naturality (snd first second)

variable [PreservesFiniteLimits mapping]

omit [MonoidalClosed C] [MonoidalClosed D] in
theorem terminal_fixed : cell.app (𝟙_ C) = 𝟙 (mapping.obj (𝟙_ C)) := by
  apply (cancel_mono (terminalComparison mapping)).mp
  exact Subsingleton.elim _ _

omit [MonoidalClosed C] [MonoidalClosed D] in
theorem product_fixed (first second : C)
    (firstFixed : cell.app first = 𝟙 (mapping.obj first))
    (secondFixed : cell.app second = 𝟙 (mapping.obj second)) :
    cell.app (first ⊗ second) = 𝟙 (mapping.obj (first ⊗ second)) := by
  apply (cancel_mono (prodComparison mapping first second)).mp
  rw [Category.id_comp, ← product_natural, firstFixed, secondFixed,
    id_tensorHom_id, Category.comp_id]

variable [MonoidalClosedFunctor mapping]

theorem exponential_fixed (argument result : C)
    (argumentFixed : cell.app argument = 𝟙 (mapping.obj argument))
    (resultFixed : cell.app result = 𝟙 (mapping.obj result)) :
    cell.app ((ihom argument).obj result) = 𝟙 (mapping.obj ((ihom argument).obj result)) := by
  let comparison := prodComparison mapping argument ((ihom argument).obj result)
  have cartesian := product_natural mapping cell argument ((ihom argument).obj result)
  rw [argumentFixed, id_tensorHom] at cartesian
  have lifted : (mapping.obj argument ◁ cell.app ((ihom argument).obj result)) ≫ inv comparison =
      inv comparison ≫ cell.app (argument ⊗ (ihom argument).obj result) := by
    have transported := congrArg (fun arrow => inv comparison ≫ arrow ≫ inv comparison) cartesian
    simpa only [comparison, Category.assoc, IsIso.inv_hom_id_assoc,
      IsIso.hom_inv_id, Category.comp_id] using transported
  have evaluated := cell.naturality ((ihom.ev argument).app result)
  change mapping.map ((ihom.ev argument).app result) ≫ cell.app result =
    cell.app (argument ⊗ (ihom argument).obj result) ≫ mapping.map ((ihom.ev argument).app result) at evaluated
  rw [resultFixed] at evaluated
  have evaluatedRead : mapping.map ((ihom.ev argument).app result) =
      cell.app (argument ⊗ (ihom argument).obj result) ≫ mapping.map ((ihom.ev argument).app result) :=
    (Category.comp_id (show mapping.obj (argument ⊗ (ihom argument).obj result) ⟶ mapping.obj result from
      mapping.map ((ihom.ev argument).app result))).symm.trans evaluated
  apply (cancel_mono ((expComparison mapping argument).natTrans.app result)).mp
  rw [Category.id_comp]
  apply MonoidalClosed.uncurry_injective
  simp only [MonoidalClosed.uncurry_natural_left, uncurry_expComparison]
  rw [← Category.assoc, lifted, Category.assoc, ← evaluatedRead]

end Mettapedia.CategoryTheory.CartesianClosedFunctorCellIdentity
