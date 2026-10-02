import Mettapedia.OSLF.Syntax.CategoricalBindingModel
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# Pointwise comparison of categorical binding models in presheaves

Natural transformations are determined by their values at all stages.
The chosen binding-model evaluator also computes uncurrying pointwise.
These comparisons apply to any presheaf target, independently of an
operational presentation or a particular chosen representable.
-/

set_option autoImplicit false
noncomputable section
namespace Mettapedia.OSLF.Binding.CategoricalBindingModel
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
universe u v w

/-- Presheaf arrows agree once their components agree at every stage. -/
theorem presheafHom_ext {C : Type u} [Category.{v} C] {Z T : Cᵒᵖ ⥤ Type w} {f g : Z ⟶ T}
    (h : ∀ (a : C) (z : Z.obj (Opposite.op a)),
      f.app (Opposite.op a) z = g.app (Opposite.op a) z) : f = g := by
  apply NatTrans.ext
  funext a
  apply ConcreteCategory.hom_ext
  intro z
  exact h a.unop z

/-- Uncurrying in a presheaf model evaluates the supplied binder tuple. -/
theorem Model.uncurry_app {C : Type u} [Category.{v} C] {S : Signature}
    (M : Model S (Cᵒᵖ ⥤ Type w)) {Γ : Ctx S} {s : S.Srt} {Z : Cᵒᵖ ⥤ Type w}
    (g : Z ⟶ M.power Γ s) (a : Cᵒᵖ) (arguments : (M.ctx Γ).obj a) (z : Z.obj a) :
    (M.uncurry g).app a (arguments, z) = (M.eval Γ s).app a (arguments, g.app a z) := rfl

end Mettapedia.OSLF.Binding.CategoricalBindingModel
end
