import Mettapedia.TypeTheory.DisplayedPresheafSliceSubstitution
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.Functor.Cat

/-!
# The native family action on contexts

Substitution acts on the full categories of displayed families, including
maps of evidence. The existing category-of-elements substitution gives a
strict contravariant action and hence a pseudofunctor. Comprehension remains
related to the chosen slice pullbacks by the canonical substitution isomorphism.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafFamilyAction

open CategoryTheory Opposite
open DisplayedPresheafTransport DisplayedPresheafSliceSubstitution

universe u
variable {C : Type u} [Category.{u} C]

theorem reindex_identity (P : Cᵒᵖ ⥤ Type u) : reindexFunctor (𝟙 P) = 𝟭 (DisplayedFamily P) := by
  rfl

theorem reindex_composition {P Q R : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q) (g : Q ⟶ R) :
    reindexFunctor (f ≫ g) = reindexFunctor g ⋙ reindexFunctor f := by
  rfl

/-- The actual categories of native families and their contravariant
substitution functors. -/
def familyAction (C : Type u) [Category.{u} C] : (Cᵒᵖ ⥤ Type u)ᵒᵖ ⥤ Cat.{u, u + 1} where
  obj P := Cat.of (DisplayedFamily (unop P))
  map f := (reindexFunctor f.unop).toCatHom
  map_id _ := by
    apply Cat.ext
    exact reindex_identity _
  map_comp f g := by
    apply Cat.ext
    exact reindex_composition g.unop f.unop

/-- The same proof-valued family action in the bicategorical interface. -/
abbrev familyPseudofunctor (C : Type u) [Category.{u} C] := (familyAction C).toPseudofunctor'

end Mettapedia.TypeTheory.DisplayedPresheafFamilyAction
