import Mathlib.MeasureTheory.Category.MeasCat

/-!
# Markov Category Core Interface

Minimal categorical interface for stochastic morphisms with copy/discard.
This is intentionally lightweight: it packages the operations and composition
laws needed by the current de Finetti bridge files.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory

universe u v

-- Object and morphism universes are independent, as for Category itself.
set_option linter.checkUnivs false in
/-- Core Markov-category style interface used by bridge layers.

`comp f g` is "first `f`, then `g`" (category-style order). -/
structure MarkovCategoryCore where
  Obj : Type u
  Hom : Obj → Obj → Type v
  id : ∀ X : Obj, Hom X X
  comp : ∀ {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z
  prod : Obj → Obj → Obj
  unit : Obj
  copy : ∀ X : Obj, Hom X (prod X X)
  discard : ∀ X : Obj, Hom X unit
  id_comp : ∀ {X Y : Obj} (f : Hom X Y), comp (id X) f = f
  comp_id : ∀ {X Y : Obj} (f : Hom X Y), comp f (id Y) = f
  comp_assoc : ∀ {W X Y Z : Obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    comp f (comp g h) = comp (comp f g) h

end Mettapedia.ProbabilityTheory
