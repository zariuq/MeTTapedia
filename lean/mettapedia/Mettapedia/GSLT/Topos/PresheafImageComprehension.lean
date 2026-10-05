import Mettapedia.GSLT.Topos.PresheafPredicateTotalProducts
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The image-comprehension adjunction on presheaves

Dependent types are arrows of presheaves. Predicates inhabit the existing
Grothendieck total category of subfunctors. Taking the image of an arrow is
left adjoint to turning a predicate into its inclusion arrow. The hom-set
equivalence preserves the underlying context map and is natural in both
arguments; comprehension is fully faithful.

The witness-permutation control shows that image formation forgets proof
fibres. It must not be used as an occurrence-preserving interpretation of
execution or history. This reflection is distinct from freely adjoining
logical syntax to a presented theory.

References: Williams and Stay, Native Type Theory (2021), Section 3;
Jacobs, Categorical Logic and Type Theory (1999), Chapters 9-11.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.ImageComprehension

open _root_.CategoryTheory

universe u
variable {C : Type u} [Category.{u} C]

/-- A dependent type determines the predicate that its fibre is inhabited. -/
abbrev imageObject (p : Arrow (Cᵒᵖ ⥤ Type u)) : PresheafPredicateTotal C :=
  totalOfPredicate p.right (Subfunctor.range p.hom)

/-- A commuting square maps inhabited fibres to inhabited fibres. -/
def imageMap {p q : Arrow (Cᵒᵖ ⥤ Type u)} (f : p ⟶ q) :
    imageObject p ⟶ imageObject q :=
  homOfEntailment f.right (by
    intro U y member
    obtain ⟨x, rfl⟩ := member
    refine ⟨f.left.app U x, ?_⟩
    exact congrArg (fun η => η.app U x) f.w)

/-- Image formation on dependent types and their context maps. -/
def imageFunctor : Arrow (Cᵒᵖ ⥤ Type u) ⥤ PresheafPredicateTotal C where
  obj := imageObject
  map := imageMap
  map_id _ := hom_ext _ _ rfl
  map_comp _ _ := hom_ext _ _ rfl

/-- A predicate determines its inclusion as a dependent type. -/
abbrev comprehensionObject (a : PresheafPredicateTotal C) : Arrow (Cᵒᵖ ⥤ Type u) :=
  Arrow.mk (objectPredicate a).ι

/-- A predicate-preserving context map acts on its satisfying elements. -/
def comprehensionMap {a b : PresheafPredicateTotal C} (f : a ⟶ b) :
    comprehensionObject a ⟶ comprehensionObject b :=
  Arrow.homMk
    { app := fun U => ConcreteCategory.ofHom (TypeCat.Fun.mk
        (fun x => ⟨f.base.app U x.val, hom_entailment f U x.property⟩))
      naturality := by
        intro U V i
        ext x
        apply Subtype.ext
        exact NatTrans.naturality_apply f.base i x.val }
    f.base
    (by ext U x; rfl)

/-- Comprehension into the existing arrow category of presheaves. -/
def comprehensionFunctor : PresheafPredicateTotal C ⥤ Arrow (Cᵒᵖ ⥤ Type u) where
  obj := comprehensionObject
  map := comprehensionMap
  map_id _ := by
    apply Arrow.hom_ext
    · ext U x
      rfl
    · rfl
  map_comp _ _ := by
    apply Arrow.hom_ext
    · ext U x
      rfl
    · rfl

/-- Image entailment supplies the unique factorization through comprehension. -/
def toComprehension {p : Arrow (Cᵒᵖ ⥤ Type u)} {a : PresheafPredicateTotal C}
    (f : imageObject p ⟶ a) : p ⟶ comprehensionObject a :=
  Arrow.homMk
    { app := fun U => ConcreteCategory.ofHom (TypeCat.Fun.mk (fun x =>
        ⟨f.base.app U (p.hom.app U x), hom_entailment f U ⟨x, rfl⟩⟩))
      naturality := by
        intro U V i
        ext x
        apply Subtype.ext
        exact NatTrans.naturality_apply (p.hom ≫ f.base) i x }
    f.base
    (by ext U x; rfl)

/-- A commuting square into a predicate inclusion entails that predicate. -/
def fromComprehension {p : Arrow (Cᵒᵖ ⥤ Type u)} {a : PresheafPredicateTotal C}
    (f : p ⟶ comprehensionObject a) : imageObject p ⟶ a :=
  homOfEntailment f.right (by
    intro U y member
    obtain ⟨x, rfl⟩ := member
    have same := congrArg (fun η => η.app U x) f.w
    change (f.left.app U x).val = f.right.app U (p.hom.app U x) at same
    change f.right.app U (p.hom.app U x) ∈ (objectPredicate a).obj U
    rw [← same]
    exact (f.left.app U x).property)

/-- The natural hom-set equivalence between image and comprehension. -/
def homEquiv (p : Arrow (Cᵒᵖ ⥤ Type u)) (a : PresheafPredicateTotal C) :
    (imageFunctor.obj p ⟶ a) ≃ (p ⟶ comprehensionFunctor.obj a) where
  toFun := toComprehension
  invFun := fromComprehension
  left_inv f := hom_ext _ _ rfl
  right_inv f := by
    apply Arrow.hom_ext
    · ext U x
      apply Subtype.ext
      exact (congrArg (fun η => η.app U x) f.w).symm
    · rfl

/-- Image is left adjoint to comprehension as actual categorical functors. -/
def adjunction : imageFunctor (C := C) ⊣ comprehensionFunctor :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv
      homEquiv_naturality_left_symm := by
        intro p q a f g
        exact hom_ext _ _ rfl
      homEquiv_naturality_right := by
        intro p a b f g
        apply Arrow.hom_ext
        · ext U x
          rfl
        · rfl }

/-- Comprehension retains every predicate morphism and distinguishes them. -/
def comprehensionFullyFaithful : (comprehensionFunctor (C := C)).FullyFaithful where
  preimage f := homOfEntailment f.right (by
    intro U x member
    exact hom_entailment (fromComprehension f) U ⟨⟨x, member⟩, rfl⟩)
  map_preimage f := by
    apply Arrow.hom_ext
    · ext U x
      apply Subtype.ext
      exact (congrArg (fun η => η.app U x) f.w).symm
    · rfl
  preimage_map _ := hom_ext _ _ rfl

theorem range_comprehension (a : PresheafPredicateTotal C) :
    objectPredicate (imageObject (comprehensionObject a)) = objectPredicate a :=
  Subfunctor.range_ι _

namespace Controls

/-- A dependent type with two witnesses over the same point. -/
def twoWitnesses : Arrow (Cᵒᵖ ⥤ Type u) :=
  Arrow.mk
    { app := fun _ => ConcreteCategory.ofHom
        (TypeCat.Fun.mk (fun _ : ULift.{u} Bool => PUnit.unit))
      naturality := by intros; rfl :
      (Functor.const Cᵒᵖ).obj (ULift.{u} Bool) ⟶
        (Functor.const Cᵒᵖ).obj PUnit.{u+1} }

/-- Exchange the two witnesses while keeping the context fixed. -/
def swapWitnesses : twoWitnesses (C := C) ⟶ twoWitnesses :=
  Arrow.homMk
    { app := fun _ => ConcreteCategory.ofHom
        (TypeCat.Fun.mk (fun x : ULift.{u} Bool => ⟨!x.down⟩))
      naturality := by intros; rfl }
    (𝟙 _)
    (by ext U x; rfl)

theorem swapWitnesses_ne_identity (c : C) :
    swapWitnesses ≠ 𝟙 (twoWitnesses (C := C)) := by
  intro same
  have impossible := congrArg
    (fun f : twoWitnesses (C := C) ⟶ twoWitnesses =>
      (f.left.app (Opposite.op c) (ULift.up true)).down) same
  change false = true at impossible
  cases impossible

theorem image_forgets_witness_permutation :
    imageFunctor.map (swapWitnesses (C := C)) =
      imageFunctor.map (𝟙 twoWitnesses) := hom_ext _ _ rfl

theorem image_not_faithful (c : C) : ¬ (imageFunctor (C := C)).Faithful := by
  intro faithful
  exact swapWitnesses_ne_identity c
    (imageFunctor.map_injective image_forgets_witness_permutation)

end Controls

end Mettapedia.GSLT.Topos.ImageComprehension
