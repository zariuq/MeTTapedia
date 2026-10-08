import Mettapedia.GSLT.Topos.PresheafPredicateTotalExponential
import Mettapedia.GSLT.Topos.YonedaPredicateClosedComparison
import Mathlib.CategoryTheory.Yoneda

/-!
# The Yoneda-restricted predicate theory

Restricting the presheaf predicate fibration to the representables gives a
predicate theory indexed by the base category itself: an object carries the
predicates on its representable presheaf, and a map of the base reindexes
them.

What restricts for free:

* each fibre is a frame, since it is a fibre of the unrestricted theory;
* reindexing is functorial (`yonedaReindex_id`, `yonedaReindex_comp`) and
  monotone;
* reindexing preserves implication (`yonedaReindex_himp`), because a map of
  representables is in particular a map of presheaves — which is exactly the
  setting in which that preservation holds.

Closed structure does not restrict over an arbitrary base category: the
function object of two representables need not be representable. Over a
cartesian closed base, `YonedaClosed.exponentialIso` earns its representation
using the actual canonical exponential comparison and the complete
generalized-element bijection.

The general `yonedaExpPredicate` accepts any supplied representing isomorphism.
`canonicalYonedaExpPredicate` instead uses the earned canonical isomorphism
when the base is cartesian closed. Both carry the full future-sensitive
function predicate; neither tests only present arguments.

This is the shape the source construction uses, which is why the restriction
is recorded separately from the unrestricted structure rather than folded into
it.

## References

- Williams & Stay, "Native Type Theory" (ACT 2021), §3 — the predicate theory
  is taken over the Yoneda image.
- Mac Lane–Moerdijk, "Sheaves in Geometry and Logic" (1994), Ch. I.4–I.6.
-/

open _root_.CategoryTheory MonoidalCategory CartesianMonoidalCategory

universe u

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos

variable {C : Type u} [Category.{u} C]

/-- Predicates on a representable presheaf. -/
noncomputable abbrev yonedaPredicate (X : C) : Type u :=
  Subfunctor (yoneda.obj (C := C) X)

/-- Reindexing along a map of the base. -/
noncomputable def yonedaReindex {X Y : C} (f : X ⟶ Y)
    (φ : yonedaPredicate Y) : yonedaPredicate X :=
  φ.preimage (yoneda.map f)

@[simp] theorem yonedaReindex_id (X : C) (φ : yonedaPredicate X) :
    yonedaReindex (𝟙 X) φ = φ := by
  rw [yonedaReindex, yoneda.map_id, Subfunctor.preimage_id]

theorem yonedaReindex_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (φ : yonedaPredicate Z) :
    yonedaReindex (f ≫ g) φ = yonedaReindex f (yonedaReindex g φ) := by
  rw [yonedaReindex, yonedaReindex, yonedaReindex, yoneda.map_comp,
    Subfunctor.preimage_comp]

theorem yonedaReindex_mono {X Y : C} (f : X ⟶ Y) :
    Monotone (yonedaReindex (C := C) f) := by
  intro φ ψ below U x held
  exact below U held

/-- Reindexing on representables preserves implication, since it is
reindexing along a presheaf morphism. -/
theorem yonedaReindex_himp {X Y : C} (f : X ⟶ Y)
    (φ ψ : yonedaPredicate Y) :
    yonedaReindex f (φ ⇨ ψ) = yonedaReindex f φ ⇨ yonedaReindex f ψ :=
  preimage_himp φ ψ (yoneda.map f)

/-- Where the function object of two representables is itself representable,
the exponential predicate restricts to the Yoneda image.  The representing
isomorphism is the explicit preservation witness; nothing here asserts that
one exists. -/
noncomputable def yonedaExpPredicate {X Y E : C}
    (witness : yoneda.obj E ≅
      (ihom (yoneda.obj (C := C) X)).obj (yoneda.obj (C := C) Y))
    (φ : yonedaPredicate X) (ψ : yonedaPredicate Y) : yonedaPredicate E :=
  (expPredicate (totalOfPredicate (yoneda.obj X) φ)
    (totalOfPredicate (yoneda.obj Y) ψ)).preimage witness.hom

/-- The restricted exponential predicate is monotone in the target. -/
theorem yonedaExpPredicate_mono_target {X Y E : C}
    (witness : yoneda.obj E ≅
      (ihom (yoneda.obj (C := C) X)).obj (yoneda.obj (C := C) Y))
    (φ : yonedaPredicate X) {ψ ψ' : yonedaPredicate Y} (below : ψ ≤ ψ') :
    yonedaExpPredicate witness φ ψ ≤ yonedaExpPredicate witness φ ψ' := by
  have step :
      expPredicate (totalOfPredicate (yoneda.obj X) φ)
          (totalOfPredicate (yoneda.obj Y) ψ) ≤
        expPredicate (totalOfPredicate (yoneda.obj X) φ)
          (totalOfPredicate (yoneda.obj Y) ψ') := by
    refine forallAlong_mono _ ?_
    refine himp_le_himp_left ?_
    intro V y member
    exact below V member
  intro U x held
  exact step U held

section CanonicalClosed

variable [CartesianMonoidalCategory C] [MonoidalClosed C]

/-- The actual exponential predicate on the selected base exponential,
using the canonical representation earned from base closure. -/
noncomputable def canonicalYonedaExpPredicate {X Y : C}
    (φ : yonedaPredicate X) (ψ : yonedaPredicate Y) :
    yonedaPredicate ((ihom X).obj Y) :=
  yonedaExpPredicate (YonedaClosed.exponentialIso X Y) φ ψ

theorem canonicalYonedaExpPredicate_mono_target {X Y : C}
    (φ : yonedaPredicate X) {ψ ψ' : yonedaPredicate Y} (below : ψ ≤ ψ') :
    canonicalYonedaExpPredicate φ ψ ≤ canonicalYonedaExpPredicate φ ψ' :=
  yonedaExpPredicate_mono_target (YonedaClosed.exponentialIso X Y) φ below

end CanonicalClosed
end Mettapedia.GSLT.Topos

#print axioms Mettapedia.GSLT.Topos.yonedaReindex_id
#print axioms Mettapedia.GSLT.Topos.yonedaReindex_comp
#print axioms Mettapedia.GSLT.Topos.yonedaReindex_himp
#print axioms Mettapedia.GSLT.Topos.yonedaExpPredicate_mono_target
