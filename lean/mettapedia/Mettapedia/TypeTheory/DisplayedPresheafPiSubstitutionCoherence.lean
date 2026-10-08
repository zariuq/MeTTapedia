import Mettapedia.TypeTheory.DisplayedPresheafPiSubstitution

/-!
# Coherence of native dependent function substitution

The selected right-Kan function families are substituted through their
canonical formation comparison. This file checks identity and composite
substitution on every natural function term, without replacing that
comparison by an equality of selected type objects.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafPiSubstitutionCoherence

open _root_.CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafPi DisplayedPresheafPiSubstitution

universe u
variable {C : Type u} [Category.{u} C]
variable {P Q R : Cᵒᵖ ⥤ Type u}

set_option backward.isDefEq.respectTransparency false in
theorem reindexFunction_identity (A : DisplayedFamily P)
    (B : DisplayedFamily (totalSpace A)) (function : (piDisplayed A B).sections) :
    reindexFunction (𝟙 P) A B function = function := by
  obtain ⟨body, rfl⟩ := (piSectionEquiv A B).surjective function
  exact reindexFunction_lam (𝟙 P) A B body

set_option backward.isDefEq.respectTransparency false in
/-- The complete dependent function is unchanged by replacing two native
substitution stages with their composite. -/
theorem reindexFunction_composition (f : P ⟶ Q) (g : Q ⟶ R)
    (A : DisplayedFamily R) (B : DisplayedFamily (totalSpace A))
    (function : (piDisplayed A B).sections) :
    reindexFunction (f ≫ g) A B function =
      reindexFunction f (reindexDisplayed g A)
        (reindexDisplayed (totalReindexMap g A) B) (reindexFunction g A B function) := by
  obtain ⟨body, rfl⟩ := (piSectionEquiv A B).surjective function
  exact (reindexFunction_lam (f ≫ g) A B body).trans
    ((congrArg
      (reindexFunction f (reindexDisplayed g A) (reindexDisplayed (totalReindexMap g A) B))
      (reindexFunction_lam g A B body)).trans
        (reindexFunction_lam f (reindexDisplayed g A)
          (reindexDisplayed (totalReindexMap g A) B)
          (reindexDisplayedSection (totalReindexMap g A) B body))).symm

end Mettapedia.TypeTheory.DisplayedPresheafPiSubstitutionCoherence
