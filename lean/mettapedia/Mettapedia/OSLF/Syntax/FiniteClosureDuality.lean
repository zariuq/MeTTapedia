import Mathlib.CategoryTheory.ObjectProperty.ColimitsClosure
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape

/-!
# Duality of generated object closures

Closing objects under a family of colimit shapes and then taking opposites
agrees with closing opposite objects under the opposite limit shapes. This
comparison keeps the index categories and their variance explicit.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding

open CategoryTheory

universe u v w t u' v'

variable {C : Type u} [Category.{v} C]
variable {α : Type t} (J : α → Type u') [∀ a, Category.{v'} (J a)]

/-- Opposite converts closure under the specified colimit presentations into
closure under the corresponding limit presentations. -/
theorem op_colimitsClosure_eq_limitsClosure (P : ObjectProperty C) :
    (P.colimitsClosure J).op =
      P.op.limitsClosure (fun a => (J a)ᵒᵖ) := by
  apply le_antisymm
  · intro X hX
    let Q : ObjectProperty Cᵒᵖ := P.op.limitsClosure (fun a => (J a)ᵒᵖ)
    have h : P.colimitsClosure J ≤ Q.unop := by
      apply ObjectProperty.colimitsClosure_le
      intro Y hY
      exact ObjectProperty.le_limitsClosure _ _ _ hY
    exact h X.unop hX
  · intro X hX
    let Q : ObjectProperty C := P.colimitsClosure J
    have h : P.op.limitsClosure (fun a => (J a)ᵒᵖ) ≤ Q.op := by
      apply ObjectProperty.limitsClosure_le
      intro Y hY
      exact ObjectProperty.le_colimitsClosure _ _ _ hY
    exact h X hX

end Mettapedia.OSLF.Binding
