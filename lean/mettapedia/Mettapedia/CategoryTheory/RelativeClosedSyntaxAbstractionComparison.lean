import Mettapedia.CategoryTheory.RelativeClosedSyntaxInterpretation

/-!
# Complete arrow comparisons for right-hand abstraction

The chosen right-hand binding convention is related to the actual closed
adjunction by its product exchange. Postcomposition, injectivity and full
evaluation eta hold for arbitrary categorical arrows.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation

open _root_.CategoryTheory MonoidalCategory CartesianMonoidalCategory

universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]

theorem abstraction_postcomposition {X A E P : C}
    (body : X ⊗ A ⟶ E) (endpoint : E ⟶ P) :
    abstraction body ≫ (ihom A).map endpoint = abstraction (body ≫ endpoint) := by
  unfold abstraction
  rw [← MonoidalClosed.curry_natural_right, Category.assoc]

theorem abstraction_injective {X A P : C} :
    Function.Injective (abstraction : (X ⊗ A ⟶ P) → (X ⟶ (A ⟶[C] P))) := by
  intro first second same
  have body := MonoidalClosed.curry_injective same
  have exchanged := congrArg (fun arrow : A ⊗ X ⟶ P => exchange X A ≫ arrow) body
  simpa [exchange, ← Category.assoc] using exchanged

theorem abstraction_evaluation {X A P : C} (function : X ⟶ (A ⟶[C] P)) :
    abstraction (lift (fst X A ≫ function) (snd X A) ≫ evaluation A P) = function := by
  unfold abstraction evaluation
  apply (MonoidalClosed.curry_eq_iff _ function).2
  rw [MonoidalClosed.uncurry_eq]
  simp only [← Category.assoc]
  apply congrArg (fun paired : A ⊗ X ⟶ A ⊗ (A ⟶[C] P) => paired ≫ (ihom.ev A).app P)
  apply hom_ext <;> simp [exchange]

end Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation
