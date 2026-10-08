import Mettapedia.TypeTheory.ContextualLocalUniversesDecoding
import Mettapedia.GSLT.Core.ContextualPseudoCwfMorphism
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Display maps of local family presentations

Decoding a local family forgets its external parameter presentation. It
retains each complete comprehension substitution. Consequently its action
on display arrows is a bijection for every supplied pair of local objects,
even when their decoded types agree and their presentations differ.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualLocalUniverses

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder

universe u v w'
variable (C : Cwf.{u, v, max u v, w'})

local instance (E : Cwf.{u, v, max u v, w'}) (Γ : E.Ctx) :
    Category.{v} (TypeOver E Γ) := TypeOver.instCategory (C := E) (Γ := Γ)

local instance (E : Cwf.{u, v, max u v, w'}) (Γ : E.Ctx) :
    Category.{v} (TypeOver (localCwf E) Γ) := TypeOver.instCategory (C := localCwf E) (Γ := Γ)

def displayDecoder (Γ : C.Ctx) : TypeOver (localCwf C) Γ ⥤ TypeOver C Γ where
  obj A := ⟨A.val.decoded⟩
  map arrow := ⟨arrow.substitution, arrow.over⟩
  map_id _ := TypeOver.Hom.ext rfl
  map_comp _ _ := TypeOver.Hom.ext rfl

def displayHomEquiv {Γ : C.Ctx} (A B : TypeOver (localCwf C) Γ) :
    (A ⟶ B) ≃ ((displayDecoder C Γ).obj A ⟶ (displayDecoder C Γ).obj B) where
  toFun := (displayDecoder C Γ).map
  invFun arrow := ⟨arrow.substitution, arrow.over⟩
  left_inv _ := TypeOver.Hom.ext rfl
  right_inv _ := TypeOver.Hom.ext rfl

@[simp] theorem displayDecoder_substitution {Γ : C.Ctx}
    {A B : TypeOver (localCwf C) Γ} (arrow : A ⟶ B) :
    ((displayDecoder C Γ).map arrow).substitution = arrow.substitution := rfl

@[simp] theorem displayHomEquiv_inverse_substitution {Γ : C.Ctx}
    {A B : TypeOver (localCwf C) Γ}
    (arrow : (displayDecoder C Γ).obj A ⟶ (displayDecoder C Γ).obj B) :
    ((displayHomEquiv C A B).symm arrow).substitution = arrow.substitution := rfl

def displayDecoderFullyFaithful (Γ : C.Ctx) : (displayDecoder C Γ).FullyFaithful where
  preimage := fun arrow => ⟨arrow.substitution, arrow.over⟩
  map_preimage _ := TypeOver.Hom.ext rfl
  preimage_map _ := TypeOver.Hom.ext rfl

set_option backward.isDefEq.respectTransparency false in
theorem displayDecoder_is_contextual (model : CwfWithTerminal.{u, v, max u v, w'})
    (Γ : model.toCwf.Ctx) :
    displayDecoder model.toCwf Γ = ((strictDecoder model).toPseudo.mapTypeFunctor Γ) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro A B arrow
  apply heq_of_eq
  apply TypeOver.Hom.ext
  simp only [StrictCwfMorphism.toPseudo_mapTypeArrow,
    StrictCwfMorphism.mapTypeArrow, StrictCwfMorphism.comprehensionIso,
    strictDecoder, familyDecoder, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
    Functor.id_map, Category.comp_id]
  change arrow.substitution = model.toCwf.compS arrow.substitution (model.toCwf.idS _)
  exact (model.toCwf.comp_id arrow.substitution).symm

end Mettapedia.TypeTheory.ContextualLocalUniverses
