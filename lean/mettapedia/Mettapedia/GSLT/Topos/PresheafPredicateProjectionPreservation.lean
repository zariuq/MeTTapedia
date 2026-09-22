import Mettapedia.GSLT.Topos.PresheafFunctionPredicateTransport

/-!
# The predicate projection preserves the cartesian closed structure strictly

The total predicate category's terminal object, binary products and
exponentials were each constructed over the corresponding object of the base.
This file records that the projection sends every piece of that structure to
the base's corresponding piece **on the nose**, not merely up to isomorphism:
each identity below holds by definitional equality, except evaluation, which
reduces to the base's evaluation through the identity-uncurrying law.

`projection_preserves_cartesianClosed` bundles the six identities.

## Why this is not vacuous

Strict preservation would carry no information if the projection were an
equivalence, so both directions of its failure to be one are recorded:

* `projection_faithful` — a total morphism is determined by its base map, so
  the projection is faithful and no information is added by the fibre beyond
  the existence of an entailment;
* `projection_not_full` — over a presheaf with a section, the identity base
  map admits no total morphism from the top predicate to the bottom one, so
  some base morphisms have no lift at all.

Faithful but not full is the precise sense in which the predicate layer
**restricts** the base rather than relabelling it. Preservation says the
structure is the base's structure; non-fullness says the predicates are a real
constraint on which of the base's morphisms survive.

## References

- Jacobs, "Categorical Logic and Type Theory" (1999), Ch. 1 and Ch. 9
  (strict versus non-strict preservation by a fibration's projection).
- Williams & Stay, "Native Type Theory" (ACT 2021), §3.
-/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

universe u

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos

variable {C : Type u} [Category.{u} C]

/-! Structure maps are sent to the base's structure maps, on the nose. -/

theorem toUnitTotal_base (a : PresheafPredicateTotal C) :
    (toUnitTotal a).base = toUnit a.base := rfl

theorem prodTotalFst_base (a b : PresheafPredicateTotal C) :
    (prodTotalFst a b).base = fst a.base b.base := rfl

theorem prodTotalSnd_base (a b : PresheafPredicateTotal C) :
    (prodTotalSnd a b).base = snd a.base b.base := rfl

theorem prodTotalLift_base {c a b : PresheafPredicateTotal C}
    (f : c ⟶ a) (g : c ⟶ b) :
    (prodTotalLift f g).base = lift f.base g.base := rfl

/-! Faithful, and not full. -/

/-- The projection is faithful: a total morphism is determined by its base. -/
theorem projection_faithful {a b : PresheafPredicateTotal C} (f g : a ⟶ b)
    (base : f.base = g.base) : f = g := hom_ext f g base

/-- The projection is not full: over a presheaf with a section, the identity
base map admits no total morphism from the top predicate to the bottom one.
So the predicate layer restricts the base rather than relabelling it. -/
theorem projection_not_full {P : Cᵒᵖ ⥤ Type u} {U : Cᵒᵖ} (point : P.obj U) :
    ¬ ∃ g : totalOfPredicate P ⊤ ⟶ totalOfPredicate P ⊥, g.base = 𝟙 P :=
  no_identity_hom_top_to_bot point


/-- Strict preservation of the whole cartesian closed structure, bundled. -/
theorem projection_preserves_cartesianClosed (C : Type u) [Category.{u} C] :
    ((unitTotal C).base = 𝟙_ (Cᵒᵖ ⥤ Type u)) ∧
      (∀ a b : PresheafPredicateTotal C,
        (prodTotal a b).base = a.base ⊗ b.base) ∧
      (∀ a b : PresheafPredicateTotal C,
        (expTotal a b).base = (ihom a.base).obj b.base) ∧
      (∀ a b : PresheafPredicateTotal C,
        (prodTotalFst a b).base = fst a.base b.base) ∧
      (∀ a b : PresheafPredicateTotal C,
        (prodTotalSnd a b).base = snd a.base b.base) ∧
      (∀ a b : PresheafPredicateTotal C,
        (expEvalHom a b).base = expEval a b) :=
  ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun a b => expEvalHom_base a b⟩

end Mettapedia.GSLT.Topos

#print axioms Mettapedia.GSLT.Topos.projection_preserves_cartesianClosed
#print axioms Mettapedia.GSLT.Topos.projection_faithful
#print axioms Mettapedia.GSLT.Topos.projection_not_full
