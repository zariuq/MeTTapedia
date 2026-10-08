import Mettapedia.TypeTheory.NativeLocalTheoryRestriction
import Mettapedia.TypeTheory.ContextualLocalUniversesDisplay

/-!
# Native logical comparisons in the actual display categories

The dependent-family comparisons induce complete comprehension arrows
between the retained native presentations. Sum comparisons are invertible
display arrows. Product comparisons become invertible under the same future
coverage that supplies the native function inverse. The complete program
point and supplied evidence are carried by these arrows.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.NativeLocalDisplayComparisons

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafSlice
open DisplayedPresheafCwf ContextualLocalUniverses NativeLocalTypeFormers
open NativeLocalTheoryRestriction

universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {X : Dᵒᵖ ⥤ Type u}

local instance decodedCategory (P : Cᵒᵖ ⥤ Type u) :
    Category.{u} ((presheafCwf.{u, u, u} C).Ty P) :=
  inferInstanceAs (Category.{u} (DisplayedFamily.{u, u, u, u} P))

local instance (P : Cᵒᵖ ⥤ Type u) :
    Category.{u} (TypeOver (localCwf (presheafCwf.{u, u, u} C)) P) :=
  TypeOver.instCategory (C := localCwf (presheafCwf.{u, u, u} C)) (Γ := P)

def displayHom {P : Cᵒᵖ ⥤ Type u} (A B : NativeType P)
    (operation : A.decoded ⟶ B.decoded) :
    (⟨A⟩ : TypeOver (localCwf (presheafCwf.{u, u, u} C)) P) ⟶ ⟨B⟩ where
  substitution := totalHom operation
  over := totalHom_projection operation

@[simp] theorem displayHom_value {P : Cᵒᵖ ⥤ Type u} (A B : NativeType P)
    (operation : A.decoded ⟶ B.decoded) (world : Cᵒᵖ)
    (receipt : (totalSpace A.decoded).obj world) :
    (displayHom A B operation).substitution.app world receipt =
      ⟨receipt.1, operation.app ⟨world, receipt.1⟩ receipt.2⟩ := rfl

theorem displayHom_identity {P : Cᵒᵖ ⥤ Type u} (A : NativeType P) :
    displayHom A A (𝟙 A.decoded) = 𝟙 (⟨A⟩ :
      TypeOver (localCwf (presheafCwf.{u, u, u} C)) P) := by
  apply TypeOver.Hom.ext
  change totalHom (𝟙 A.decoded) = 𝟙 (totalSpace A.decoded)
  ext world receipt
  rfl

theorem displayHom_composition {P : Cᵒᵖ ⥤ Type u} (A B E : NativeType P)
    (first : A.decoded ⟶ B.decoded) (second : B.decoded ⟶ E.decoded) :
    displayHom A E (first ≫ second) = displayHom A B first ≫ displayHom B E second := by
  apply TypeOver.Hom.ext
  change totalHom (first ≫ second) = totalHom first ≫ totalHom second
  ext world receipt
  rfl

/-- Both inverse equations are earned from the whole dependent-family
isomorphism, retaining the complete comprehension substitution. -/
def displayIso {P : Cᵒᵖ ⥤ Type u} (A B : NativeType P)
    (comparison : A.decoded ≅ B.decoded) :
    (⟨A⟩ : TypeOver (localCwf (presheafCwf.{u, u, u} C)) P) ≅ ⟨B⟩ where
  hom := displayHom A B comparison.hom
  inv := displayHom B A comparison.inv
  hom_inv_id := by
    rw [← displayHom_composition, comparison.hom_inv_id]
    exact displayHom_identity A
  inv_hom_id := by
    rw [← displayHom_composition, comparison.inv_hom_id]
    exact displayHom_identity B

noncomputable def sumDisplayIso (F : C ⥤ D) (A : NativeType X)
    (B : NativeType (totalSpace A.decoded)) :
    (⟨restrict F (sigma A B)⟩ : TypeOver (localCwf (presheafCwf.{u, u, u} C))
      (F.op ⋙ X)) ≅ ⟨sigma (restrict F A) (body F A B)⟩ :=
  displayIso _ _ (sumIso F A B)

noncomputable def productDisplayMap (F : C ⥤ D) (A : NativeType X)
    (B : NativeType (totalSpace A.decoded)) :
    (⟨restrict F (pi A B)⟩ : TypeOver (localCwf (presheafCwf.{u, u, u} C))
      (F.op ⋙ X)) ⟶ ⟨pi (restrict F A) (body F A B)⟩ :=
  displayHom _ _ (productMap F A B)

noncomputable def productDisplayIso (F : C ⥤ D) (A : NativeType X)
    (B : NativeType (totalSpace A.decoded))
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp F.op X) A.decoded point).Initial] :
    (⟨restrict F (pi A B)⟩ : TypeOver (localCwf (presheafCwf.{u, u, u} C))
      (F.op ⋙ X)) ≅ ⟨pi (restrict F A) (body F A B)⟩ :=
  displayIso _ _ (productIso F A B)

theorem productDisplayIso_hom (F : C ⥤ D) (A : NativeType X)
    (B : NativeType (totalSpace A.decoded))
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp F.op X) A.decoded point).Initial] :
    (productDisplayIso F A B).hom = productDisplayMap F A B :=
  congrArg (displayHom _ _) (productIso_hom F A B)

noncomputable def productDisplayEquivalence (F : C ⥤ D) [F.IsEquivalence]
    (A : NativeType X) (B : NativeType (totalSpace A.decoded)) :
    (⟨restrict F (pi A B)⟩ : TypeOver (localCwf (presheafCwf.{u, u, u} C))
      (F.op ⋙ X)) ≅ ⟨pi (restrict F A) (body F A B)⟩ :=
  displayIso _ _ (productEquivalence F A B)

theorem productDisplayEquivalence_hom (F : C ⥤ D) [F.IsEquivalence]
    (A : NativeType X) (B : NativeType (totalSpace A.decoded)) :
    (productDisplayEquivalence F A B).hom = productDisplayMap F A B :=
  congrArg (displayHom _ _) (productEquivalence_hom F A B)

/-- The decoder retains the complete actual display arrow, rather than
only an equivalence of its fibre carriers. -/
theorem displayDecoder_square {P : Cᵒᵖ ⥤ Type u} (A B : NativeType P)
    (operation : A.decoded ⟶ B.decoded) :
    ((displayDecoder (presheafCwf.{u, u, u} C) P).map
      (displayHom A B operation)).substitution = totalHom operation := rfl

end Mettapedia.TypeTheory.NativeLocalDisplayComparisons
