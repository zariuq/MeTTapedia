import Mettapedia.GSLT.Topos.PresheafPredicateProjection
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory

/-!
# Finite products of the total presheaf predicate category

The total category of the presheaf predicate projection has objects a presheaf
together with a predicate on it, and morphisms a presheaf map whose action
entails the target predicate.  This file supplies that category's terminal
object and binary products, over the corresponding presheaf objects, and
records the structural fact that governs every such construction:

* `hom_ext` — a total morphism is determined by its base map.

The entailment component is a proposition-like order relation, so it carries
no data beyond its existence.  Consequently every universal property in this
category has a free uniqueness half, and all of its content lies in exhibiting
the required entailment.  The constructions below are stated so that this is
visible rather than implicit.

Two controls mark the boundary:

* `no_hom_over_of_not_entails` — a base map whose entailment fails carries no
  total morphism, so the fibre condition is a real obstruction;
* `no_identity_hom_top_to_bot` — over a presheaf with a section the identity
  base map admits no morphism from the top predicate to the bottom one, so the
  obstruction is inhabited rather than vacuous.

Reindexing lemmas absent from the ambient library are supplied here
(`preimage_inf`, `preimage_top`, `preimage_fst_lift`, `preimage_snd_lift`).

This file establishes finite products only.  Predicate exponentials and the
projection's preservation of a closed structure are not constructed here.

## References

- Williams & Stay, "Native Type Theory" (ACT 2021), §3.
- Jacobs, "Categorical Logic and Type Theory" (1999), Ch. 1 and Ch. 9
  (fibred products and the structure of total categories).
-/

open CategoryTheory CategoryTheory.Functor Opposite MonoidalCategory
open CartesianMonoidalCategory

universe u

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos

variable {C : Type u} [Category.{u} C]

/-- Fibre morphisms of the predicate pseudofunctor are proof irrelevant: the
fibres are order categories. -/
instance pseudoFiberHomSubsingleton (P : LocallyDiscrete (Cᵒᵖ ⥤ Type u)ᵒᵖ)
    (x y : (presheafPredicatePseudofunctor C).obj P) : Subsingleton (x ⟶ y) :=
  inferInstanceAs (Subsingleton
    ((show Subfunctor (unop P.as) from x) ⟶ (show Subfunctor (unop P.as) from y)))

/-! ## Objects and morphisms in usable form -/

/-- Total predicate object from a presheaf and an actual predicate on it. -/
abbrev totalOfPredicate (P : Cᵒᵖ ⥤ Type u) (φ : Subfunctor P) :
    PresheafPredicateTotal C :=
  ⟨P, φ⟩

/-- The predicate an object carries, as an actual subfunctor of its base. -/
abbrev objectPredicate (a : PresheafPredicateTotal C) : Subfunctor a.base :=
  a.fiber

theorem totalOfPredicate_objectPredicate (a : PresheafPredicateTotal C) :
    totalOfPredicate a.base (objectPredicate a) = a := rfl

/-- A total morphism is determined by its base map: the entailment component
carries no further data. -/
theorem hom_ext {a b : PresheafPredicateTotal C} (f g : a ⟶ b)
    (base : f.base = g.base) : f = g := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ base ?_
  apply Subsingleton.elim

/-- A base map entailing the target predicate is a total morphism. -/
abbrev homOfEntailment {a b : PresheafPredicateTotal C} (f : a.base ⟶ b.base)
    (entails : objectPredicate a ≤ (objectPredicate b).preimage f) : a ⟶ b :=
  (predicateTotalHomEquiv a b).symm ⟨f, entails⟩

@[simp] theorem homOfEntailment_base {a b : PresheafPredicateTotal C}
    (f : a.base ⟶ b.base)
    (entails : objectPredicate a ≤ (objectPredicate b).preimage f) :
    (homOfEntailment f entails).base = f := rfl

/-- The entailment that a total morphism carries. -/
theorem hom_entailment {a b : PresheafPredicateTotal C} (f : a ⟶ b) :
    objectPredicate a ≤ (objectPredicate b).preimage f.base :=
  ((predicateTotalHomEquiv a b) f).property

/-! ## Reindexing laws -/

@[simp] theorem preimage_inf {P Q : Cᵒᵖ ⥤ Type u} (φ ψ : Subfunctor Q)
    (f : P ⟶ Q) : (φ ⊓ ψ).preimage f = φ.preimage f ⊓ ψ.preimage f := rfl

@[simp] theorem preimage_top {P Q : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q) :
    (⊤ : Subfunctor Q).preimage f = ⊤ := rfl

/-- Reindexing a first-component predicate along a pairing is reindexing along
the first map. -/
theorem preimage_fst_lift {c a b : Cᵒᵖ ⥤ Type u} (φ : Subfunctor a)
    (f : c ⟶ a) (g : c ⟶ b) :
    (φ.preimage (fst a b)).preimage (lift f g) = φ.preimage f := by
  rw [← Subfunctor.preimage_comp, lift_fst]

/-- Reindexing a second-component predicate along a pairing is reindexing
along the second map. -/
theorem preimage_snd_lift {c a b : Cᵒᵖ ⥤ Type u} (ψ : Subfunctor b)
    (f : c ⟶ a) (g : c ⟶ b) :
    (ψ.preimage (snd a b)).preimage (lift f g) = ψ.preimage g := by
  rw [← Subfunctor.preimage_comp, lift_snd]

/-! ## Terminal object -/

/-- The unit presheaf carrying the top predicate. -/
abbrev unitTotal (C : Type u) [Category.{u} C] : PresheafPredicateTotal C :=
  totalOfPredicate (𝟙_ (Cᵒᵖ ⥤ Type u)) ⊤

/-- The unique total morphism into the unit object. -/
def toUnitTotal (a : PresheafPredicateTotal C) : a ⟶ unitTotal C :=
  homOfEntailment (toUnit a.base) (by
    show objectPredicate a ≤
      (⊤ : Subfunctor (𝟙_ (Cᵒᵖ ⥤ Type u))).preimage (toUnit a.base)
    rw [preimage_top]
    exact le_top)

theorem toUnitTotal_unique (a : PresheafPredicateTotal C)
    (f : a ⟶ unitTotal C) : f = toUnitTotal a :=
  hom_ext _ _ (toUnit_unique _ _)

/-- The unit presheaf with the top predicate is terminal in the total
category. -/
def unitTotalIsTerminal (C : Type u) [Category.{u} C] :
    Limits.IsTerminal (unitTotal C) :=
  Limits.IsTerminal.ofUniqueHom toUnitTotal (fun _ f => toUnitTotal_unique _ f)

/-! ## Binary products -/

/-- The product object: the presheaf product carrying the conjunction of the
two predicates reindexed along the projections. -/
abbrev prodTotal (a b : PresheafPredicateTotal C) : PresheafPredicateTotal C :=
  totalOfPredicate (a.base ⊗ b.base)
    ((objectPredicate a).preimage (fst a.base b.base) ⊓
      (objectPredicate b).preimage (snd a.base b.base))

def prodTotalFst (a b : PresheafPredicateTotal C) : prodTotal a b ⟶ a :=
  homOfEntailment (fst a.base b.base) inf_le_left

def prodTotalSnd (a b : PresheafPredicateTotal C) : prodTotal a b ⟶ b :=
  homOfEntailment (snd a.base b.base) inf_le_right

/-- Pairing of total morphisms: the base maps pair, and the conjunction of the
two entailments is exactly the product predicate's entailment. -/
def prodTotalLift {c a b : PresheafPredicateTotal C} (f : c ⟶ a) (g : c ⟶ b) :
    c ⟶ prodTotal a b :=
  homOfEntailment (lift f.base g.base) (by
    show objectPredicate c ≤
      ((objectPredicate a).preimage (fst a.base b.base) ⊓
        (objectPredicate b).preimage (snd a.base b.base)).preimage
          (lift f.base g.base)
    rw [preimage_inf]
    refine le_inf ?_ ?_
    · rw [preimage_fst_lift]
      exact hom_entailment f
    · rw [preimage_snd_lift]
      exact hom_entailment g)

@[simp] theorem prodTotalLift_fst {c a b : PresheafPredicateTotal C}
    (f : c ⟶ a) (g : c ⟶ b) : prodTotalLift f g ≫ prodTotalFst a b = f :=
  hom_ext _ _ (by
    show lift f.base g.base ≫ fst a.base b.base = f.base
    simp)

@[simp] theorem prodTotalLift_snd {c a b : PresheafPredicateTotal C}
    (f : c ⟶ a) (g : c ⟶ b) : prodTotalLift f g ≫ prodTotalSnd a b = g :=
  hom_ext _ _ (by
    show lift f.base g.base ≫ snd a.base b.base = g.base
    simp)

/-- The pairing is the unique total morphism with the two given components. -/
theorem prodTotalLift_unique {c a b : PresheafPredicateTotal C}
    (f : c ⟶ a) (g : c ⟶ b) (candidate : c ⟶ prodTotal a b)
    (first : candidate ≫ prodTotalFst a b = f)
    (second : candidate ≫ prodTotalSnd a b = g) :
    candidate = prodTotalLift f g := by
  refine hom_ext _ _ ?_
  have firstBase : candidate.base ≫ fst a.base b.base = f.base :=
    congrArg Pseudofunctor.CoGrothendieck.Hom.base first
  have secondBase : candidate.base ≫ snd a.base b.base = g.base :=
    congrArg Pseudofunctor.CoGrothendieck.Hom.base second
  show candidate.base = lift f.base g.base
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [lift_fst]
    exact firstBase
  · rw [lift_snd]
    exact secondBase

/-- The projection sends the constructed product to the presheaf product. -/
theorem prodTotal_base (a b : PresheafPredicateTotal C) :
    (prodTotal a b).base = a.base ⊗ b.base := rfl

/-- The projection sends the constructed terminal object to the unit
presheaf. -/
theorem unitTotal_base (C : Type u) [Category.{u} C] :
    (unitTotal C).base = 𝟙_ (Cᵒᵖ ⥤ Type u) := rfl

/-! ## Controls -/

/-- The entailment component is a real obstruction: no total morphism lies
over a base map whose predicate entailment fails. -/
theorem no_hom_over_of_not_entails {a b : PresheafPredicateTotal C}
    (f : a.base ⟶ b.base)
    (fails : ¬ objectPredicate a ≤ (objectPredicate b).preimage f) :
    ¬ ∃ g : a ⟶ b, g.base = f := by
  rintro ⟨g, rfl⟩
  exact fails (hom_entailment g)

/-- A presheaf with a section separates the top and bottom predicates. -/
theorem top_not_le_bot {P : Cᵒᵖ ⥤ Type u} {U : Cᵒᵖ} (point : P.obj U) :
    ¬ (⊤ : Subfunctor P) ≤ (⊥ : Subfunctor P) := by
  intro le
  exact (le U (by trivial) : point ∈ (⊥ : Subfunctor P).obj U)

/-- Non-vacuity of the obstruction: over a presheaf with a section, the
identity base map carries no total morphism from the top predicate to the
bottom one. -/
theorem no_identity_hom_top_to_bot {P : Cᵒᵖ ⥤ Type u} {U : Cᵒᵖ}
    (point : P.obj U) :
    ¬ ∃ g : totalOfPredicate P ⊤ ⟶ totalOfPredicate P ⊥, g.base = 𝟙 P := by
  refine no_hom_over_of_not_entails
    (a := totalOfPredicate P ⊤) (b := totalOfPredicate P ⊥) (𝟙 P) ?_
  show ¬ (⊤ : Subfunctor P) ≤ (⊥ : Subfunctor P).preimage (𝟙 P)
  rw [Subfunctor.preimage_id]
  exact top_not_le_bot point

end Mettapedia.GSLT.Topos

#print axioms Mettapedia.GSLT.Topos.hom_ext
#print axioms Mettapedia.GSLT.Topos.hom_entailment
#print axioms Mettapedia.GSLT.Topos.toUnitTotal_unique
#print axioms Mettapedia.GSLT.Topos.prodTotalLift_fst
#print axioms Mettapedia.GSLT.Topos.prodTotalLift_snd
#print axioms Mettapedia.GSLT.Topos.prodTotalLift_unique
#print axioms Mettapedia.GSLT.Topos.no_hom_over_of_not_entails
#print axioms Mettapedia.GSLT.Topos.no_identity_hom_top_to_bot
