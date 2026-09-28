import Mettapedia.TypeTheory.IndexedPolynomial

/-!
# Morphisms of indexed rule algebras

Rule-algebra maps preserve every constructor action, including all of its
recursive premise positions. These maps form a category over each fixed
indexed rule polynomial.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IndexedPolynomial.Algebra

universe uBase uIndex uShape uPosition uSource uMiddle uTarget uFourth

variable {Base : Type uBase} {Index : Base → Type uIndex}
variable {polynomial : IndexedPolynomial.{uBase, uIndex, uShape, uPosition}
    Base Index}
variable {source : (base : Base) → Index base → Type uSource}
variable {middle : (base : Base) → Index base → Type uMiddle}
variable {target : (base : Base) → Index base → Type uTarget}
variable {fourth : (base : Base) → Index base → Type uFourth}

/-- Identity interpretation of a rule algebra. -/
def Hom.id (A : Algebra polynomial source) : Hom A A where
  toFun := fun _ _ value => value
  commutes := by
    intro base index layer
    simp only [IndexedPolynomial.Extension.map_id]

/-- Compose rule-algebra interpretations. The position map in the
polynomial extension guarantees that every recursive premise is respected. -/
def Hom.comp {A : Algebra polynomial source}
    {B : Algebra polynomial middle} {C : Algebra polynomial target}
    (f : Hom A B) (g : Hom B C) : Hom A C where
  toFun := fun base index value => g.toFun base index (f.toFun base index value)
  commutes := by
    intro base index layer
    rw [f.commutes, g.commutes]
    cases layer
    rfl

/-- A morphism of rule algebras is determined by its action on evidence. -/
@[ext] theorem Hom.ext {A : Algebra polynomial source}
    {B : Algebra polynomial target} (f g : Hom A B)
    (h : ∀ base index value, f.toFun base index value =
      g.toFun base index value) : f = g := by
  cases f with
  | mk f hf =>
      cases g with
      | mk g hg =>
          have equal : f = g := by
            funext base index value
            exact h base index value
          subst g
          rfl

theorem Hom.comp_id {A : Algebra polynomial source}
    {B : Algebra polynomial target} (f : Hom A B) :
    Hom.comp f (Hom.id B) = f := by
  apply Hom.ext
  intro base index value
  rfl

theorem Hom.id_comp {A : Algebra polynomial source}
    {B : Algebra polynomial target} (f : Hom A B) :
    Hom.comp (Hom.id A) f = f := by
  apply Hom.ext
  intro base index value
  rfl

theorem Hom.comp_assoc {A : Algebra polynomial source}
    {B : Algebra polynomial middle} {C : Algebra polynomial target}
    {D : Algebra polynomial fourth}
    (f : Hom A B) (g : Hom B C) (h : Hom C D) :
    Hom.comp (Hom.comp f g) h = Hom.comp f (Hom.comp g h) := by
  apply Hom.ext
  intro base index value
  rfl

end Mettapedia.TypeTheory.IndexedPolynomial.Algebra
