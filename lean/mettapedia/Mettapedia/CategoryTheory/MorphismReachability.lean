import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Reachability through a multiplicative morphism property

A class of morphisms containing identities and closed under composition
induces a preorder on the objects of its category: `X ≤ Y` when some admitted
morphism runs from `X` to `Y`.

Keeping the morphism property as an explicit parameter prevents different
notions of simulation, embedding, interpretation, or refinement from being
silently identified.
-/

set_option autoImplicit false

namespace Mettapedia.MorphismReachability

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

/-- Reachability using only morphisms satisfying `admissible`. -/
def Reaches (admissible : MorphismProperty C) (source target : C) : Prop :=
  ∃ morphism : source ⟶ target, admissible morphism

/-- Identities give reflexive reachability. -/
theorem reaches_refl (admissible : MorphismProperty C)
    [admissible.ContainsIdentities] (object : C) :
    Reaches admissible object object :=
  ⟨𝟙 object, admissible.id_mem object⟩

/-- Composition gives transitive reachability. -/
theorem reaches_trans (admissible : MorphismProperty C)
    [admissible.IsStableUnderComposition]
    {first second third : C}
    (firstSecond : Reaches admissible first second)
    (secondThird : Reaches admissible second third) :
    Reaches admissible first third := by
  rcases firstSecond with ⟨earlier, earlierAdmissible⟩
  rcases secondThird with ⟨later, laterAdmissible⟩
  exact ⟨earlier ≫ later,
    admissible.comp_mem earlier later earlierAdmissible laterAdmissible⟩

/-- An object viewed in the reachability preorder selected by one
multiplicative morphism property. -/
@[ext] structure Order (admissible : MorphismProperty C) where
  object : C

instance (admissible : MorphismProperty C) [admissible.IsMultiplicative] :
    Preorder (Order admissible) where
  le source target := Reaches admissible source.object target.object
  le_refl object := reaches_refl admissible object.object
  le_trans _source _middle _target := reaches_trans admissible

/-- The preorder relation exposes exactly the selected reachability
predicate. -/
theorem order_le_iff (admissible : MorphismProperty C)
    [admissible.IsMultiplicative]
    (source target : Order admissible) :
    source ≤ target ↔ Reaches admissible source.object target.object :=
  Iff.rfl

end Mettapedia.MorphismReachability
