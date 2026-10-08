import Mettapedia.GSLT.Topos.YonedaPredicateLimits
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Actual products of Yoneda predicates

The chosen terminal object has the true predicate, and a chosen base product
carries the intersection of the two projection inverse images. Pairing earns
both entailments from the supplied arrows. These objects assemble an actual
cartesian monoidal structure whose projection retains the selected products.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.YonedaPredicate

open _root_.CategoryTheory MonoidalCategory CartesianMonoidalCategory

universe u
variable {C : Type u} [Category.{u} C] [CartesianMonoidalCategory C]

abbrev unit (C : Type u) [Category.{u} C] [CartesianMonoidalCategory C] : Total C :=
  ofPredicate (𝟙_ C) ⊤

def toUnit (object : Total C) : object ⟶ unit C :=
  homOfEntailment (CartesianMonoidalCategory.toUnit object.base) le_top

theorem toUnit_unique (object : Total C) (arrow : object ⟶ unit C) :
    arrow = toUnit object :=
  hom_ext _ _ (CartesianMonoidalCategory.toUnit_unique _ _)

def unitIsTerminal (C : Type u) [Category.{u} C] [CartesianMonoidalCategory C] :
    Limits.IsTerminal (unit C) :=
  Limits.IsTerminal.ofUniqueHom toUnit toUnit_unique

abbrev product (first second : Total C) : Total C :=
  ofPredicate (first.base ⊗ second.base)
    ((predicate first).preimage (yoneda.map (fst first.base second.base)) ⊓
      (predicate second).preimage (yoneda.map (snd first.base second.base)))

def first (a b : Total C) : product a b ⟶ a :=
  homOfEntailment (fst a.base b.base) inf_le_left

def second (a b : Total C) : product a b ⟶ b :=
  homOfEntailment (snd a.base b.base) inf_le_right

def pairing {a b context : Total C} (f : context ⟶ a) (g : context ⟶ b) :
    context ⟶ product a b :=
  homOfEntailment (lift f.base g.base) (by
    rw [preimage_inf]
    apply le_inf
    · rw [← Subfunctor.preimage_comp, ← yoneda.map_comp, lift_fst]
      exact hom_entailment f
    · rw [← Subfunctor.preimage_comp, ← yoneda.map_comp, lift_snd]
      exact hom_entailment g)

@[simp] theorem pairing_first {a b context : Total C}
    (f : context ⟶ a) (g : context ⟶ b) : pairing f g ≫ first a b = f :=
  hom_ext _ _ (lift_fst _ _)

@[simp] theorem pairing_second {a b context : Total C}
    (f : context ⟶ a) (g : context ⟶ b) : pairing f g ≫ second a b = g :=
  hom_ext _ _ (lift_snd _ _)

theorem pairing_unique {a b context : Total C} (f : context ⟶ a) (g : context ⟶ b)
    (candidate : context ⟶ product a b)
    (fstReading : candidate ≫ first a b = f)
    (sndReading : candidate ≫ second a b = g) : candidate = pairing f g := by
  apply hom_ext
  apply CartesianMonoidalCategory.hom_ext
  · exact (congrArg Pseudofunctor.CoGrothendieck.Hom.base fstReading).trans
      (lift_fst f.base g.base).symm
  · exact (congrArg Pseudofunctor.CoGrothendieck.Hom.base sndReading).trans
      (lift_snd f.base g.base).symm

def productIsLimit (a b : Total C) :
    Limits.IsLimit (Limits.BinaryFan.mk (first a b) (second a b)) :=
  Limits.BinaryFan.isLimitMk (fun cone => pairing cone.fst cone.snd)
    (fun cone => pairing_first cone.fst cone.snd)
    (fun cone => pairing_second cone.fst cone.snd)
    (fun cone candidate f g => pairing_unique cone.fst cone.snd candidate f g)

noncomputable instance cartesian : CartesianMonoidalCategory (Total C) :=
  CartesianMonoidalCategory.ofChosenFiniteProducts
    { cone := Limits.asEmptyCone (unit C), isLimit := unitIsTerminal C }
    (fun a b =>
      { cone := Limits.BinaryFan.mk (first a b) (second a b)
        isLimit := productIsLimit a b })

def productMap {a a' b b' : Total C} (f : a ⟶ a') (g : b ⟶ b') :
    product a b ⟶ product a' b' :=
  pairing (first a b ≫ f) (second a b ≫ g)

theorem tensorLeft_map (a : Total C) {b c : Total C} (f : b ⟶ c) :
    (tensorLeft a).map f = productMap (𝟙 a) f := rfl

theorem projection_productComparison (a b : Total C) :
    prodComparison (projection C) a b = 𝟙 (a.base ⊗ b.base) := by
  change lift (fst a.base b.base) (snd a.base b.base) = 𝟙 _
  exact lift_fst_snd

set_option backward.isDefEq.respectTransparency false in
noncomputable instance projectionPreservesProducts :
    Limits.PreservesLimitsOfShape (Discrete Limits.WalkingPair) (projection C) := by
  have (a b : Total C) : IsIso (prodComparison (projection C) a b) := by
    rw [projection_productComparison]
    exact inferInstanceAs (IsIso (𝟙 (a.base ⊗ b.base)))
  exact preservesLimitsOfShape_discrete_walkingPair_of_isIso_prodComparison _

end Mettapedia.GSLT.Topos.YonedaPredicate
