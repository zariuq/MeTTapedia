import Mettapedia.GSLT.Topos.PresheafPredicateTotalProducts
import Mathlib.CategoryTheory.Yoneda

/-!
# The actual total category of Yoneda predicates

The restricted doctrine is the concrete presheaf predicate doctrine composed
with Yoneda. Its contravariant Grothendieck construction has actual base
objects and maps, retaining precisely the entailment along the corresponding
representable map. Its embedding in the unrestricted predicate category is
fully faithful by the Yoneda lemma, rather than by identifying the objects.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.YonedaPredicate

open _root_.CategoryTheory Opposite

universe u
variable {C : Type u} [Category.{u} C]

/-- Restrict the actual predicate doctrine along the Yoneda embedding. -/
def doctrine (C : Type u) [Category.{u} C] : Cᵒᵖ ⥤ Cat.{u,u} :=
  yoneda.op ⋙ presheafPredicateFunctor C

abbrev pseudofunctor (C : Type u) [Category.{u} C] := (doctrine C).toPseudofunctor'

/-- The genuine contravariant Grothendieck total category. -/
abbrev Total (C : Type u) [Category.{u} C] :=
  Pseudofunctor.CoGrothendieck (pseudofunctor C)

/-- Projection retains the actual base category and its maps. -/
abbrev projection (C : Type u) [Category.{u} C] :=
  Pseudofunctor.CoGrothendieck.forget (pseudofunctor C)

instance fiberHomSubsingleton (X : LocallyDiscrete Cᵒᵖ)
    (first second : (pseudofunctor C).obj X) : Subsingleton (first ⟶ second) :=
  inferInstanceAs (Subsingleton
    ((show Subfunctor (yoneda.obj X.as.unop) from first) ⟶
      (show Subfunctor (yoneda.obj X.as.unop) from second)))

/-- A supplied predicate over an actual representable. -/
abbrev ofPredicate (X : C) (predicate : Subfunctor (yoneda.obj X)) : Total C :=
  ⟨X, predicate⟩

abbrev predicate (object : Total C) : Subfunctor (yoneda.obj object.base) := object.fiber

/-- Restricted morphisms are equal when their actual base maps agree. -/
theorem hom_ext {first second : Total C} (f g : first ⟶ second)
    (same : f.base = g.base) : f = g := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ same ?_
  apply Subsingleton.elim

/-- An actual base map with the earned predicate entailment. -/
abbrev homOfEntailment {first second : Total C} (f : first.base ⟶ second.base)
    (entails : predicate first ≤ (predicate second).preimage (yoneda.map f)) :
    first ⟶ second :=
  ⟨f, by
    change predicate first ⟶ (predicate second).preimage (yoneda.map f)
    exact homOfLE entails⟩

theorem hom_entailment {first second : Total C} (f : first ⟶ second) :
    predicate first ≤ (predicate second).preimage (yoneda.map f.base) :=
  (show predicate first ⟶ (predicate second).preimage (yoneda.map f.base) from f.fiber).le

/-- The fully faithful interpretation in the existing unrestricted total category. -/
def embedding (C : Type u) [Category.{u} C] : Total C ⥤ PresheafPredicateTotal C where
  obj object := totalOfPredicate (yoneda.obj object.base) (predicate object)
  map f := Topos.homOfEntailment (yoneda.map f.base) (hom_entailment f)
  map_id object := Topos.hom_ext _ _ (yoneda.map_id object.base)
  map_comp f g := Topos.hom_ext _ _ (yoneda.map_comp f.base g.base)

/-- Yoneda fullness earns the actual inverse on restricted total morphisms. -/
def fullyFaithful (C : Type u) [Category.{u} C] : (embedding C).FullyFaithful where
  preimage {first second} f := homOfEntailment (Yoneda.fullyFaithful.preimage f.base) (by
    erw [Yoneda.fullyFaithful.map_preimage]
    exact Topos.hom_entailment f)
  map_preimage f := Topos.hom_ext _ _ (Yoneda.fullyFaithful.map_preimage f.base)
  preimage_map f := hom_ext _ _ (Yoneda.fullyFaithful.preimage_map f.base)

instance embeddingFull : (embedding C).Full := (fullyFaithful C).full
instance embeddingFaithful : (embedding C).Faithful := (fullyFaithful C).faithful

/-- The base projection is faithful, while the fibre remains a real constraint. -/
instance projectionFaithful : (projection C).Faithful where
  map_injective same := hom_ext _ _ same

theorem embedding_projection :
    embedding C ⋙ presheafPredicateProjection C = projection C ⋙ yoneda := rfl

/-- The restricted projection is genuinely a fibration. -/
theorem projection_fibered : _root_.CategoryTheory.Functor.IsFibered (projection C) := inferInstance

/-- An inhabited representable excludes an identity map from truth to falsehood. -/
theorem no_identity_top_to_bottom (X : C) :
    ¬ ∃ arrow : ofPredicate X ⊤ ⟶ ofPredicate X ⊥, arrow.base = 𝟙 X := by
  rintro ⟨arrow, _same⟩
  have impossible := hom_entailment arrow (op X)
    (show (𝟙 X) ∈ (⊤ : Subfunctor (yoneda.obj X)).obj (op X) from Set.mem_univ _)
  exact impossible

end Mettapedia.GSLT.Topos.YonedaPredicate
