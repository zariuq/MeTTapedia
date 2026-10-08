import Mettapedia.CategoryTheory.PredicateDoctrineCartesian
import Mettapedia.GSLT.Topos.PresheafPredicateFirstOrder
import Mettapedia.GSLT.Topos.PresheafPredicateTotalProducts

/-!
# Generic truth for the actual predicate fibration

The generic predicate consists of the maximal sieves of the presheaf truth
object. Its inverse images are precisely the classified subfunctors. The
characteristic map gives an actual Cartesian arrow in the existing total
predicate category, and its full Cartesian universal property determines that
arrow uniquely. Arbitrary entailing arrows into truth are not classifications.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.PresheafPredicateGenericTruth

open _root_.CategoryTheory _root_.CategoryTheory.Functor Opposite
open Mettapedia.CategoryTheory.PredicateDoctrine

universe u
variable {C : Type u} [Category.{u} C]

/-- Truth is the predicate of sieves containing the identity, hence all arrows. -/
noncomputable def truthPredicate (C : Type u) [Category.{u} C] :
    Subfunctor (omegaFunctor (C := C)) :=
  subfunctorOfChi _ (𝟙 _)

theorem truth_iff_top (world : Cᵒᵖ) (sieve : Sieve world.unop) :
    sieve ∈ (truthPredicate C).obj world ↔ sieve = ⊤ := by
  change sieve.arrows (𝟙 world.unop) ↔ sieve = ⊤
  constructor
  · intro contains
    apply Sieve.ext
    intro next arrow
    exact iff_of_true (by simpa using sieve.downward_closed contains arrow) trivial
  · intro same
    rw [same]
    trivial

/-- The chosen generic predicate is the image of the actual classifier truth
map, not a Boolean approximation to sieve-valued propositions. -/
theorem truth_is_range : truthPredicate C = Subfunctor.range (trueNatTrans (C := C)) := by
  ext world sieve
  constructor
  · intro holds
    exact ⟨PUnit.unit, ((truth_iff_top world sieve).mp holds).symm⟩
  · rintro ⟨_, same⟩
    exact (truth_iff_top world sieve).mpr same.symm

theorem preimage_truth {P : Cᵒᵖ ⥤ Type u} (χ : P ⟶ omegaFunctor (C := C)) :
    (truthPredicate C).preimage χ = subfunctorOfChi P χ := rfl

theorem characteristic_classifies (P : Cᵒᵖ ⥤ Type u) (φ : Subfunctor P) :
    (truthPredicate C).preimage (chiOfSubfunctor P φ) = φ := by
  rw [preimage_truth]
  exact (natTransEquivSubfunctor P).apply_symm_apply φ

theorem characteristic_unique (P : Cᵒᵖ ⥤ Type u) (φ : Subfunctor P)
    (χ : P ⟶ omegaFunctor (C := C)) (classifies : (truthPredicate C).preimage χ = φ) :
    χ = chiOfSubfunctor P φ := by
  apply (natTransEquivSubfunctor P).injective
  exact (preimage_truth χ).symm.trans
    (classifies.trans ((natTransEquivSubfunctor P).apply_symm_apply φ).symm)

/-- The explicit higher-order generic-predicate data, with both halves of
its classifying property proved for actual subfunctors. -/
noncomputable def generic (C : Type u) [Category.{u} C] :
    GenericPredicate (Cᵒᵖ ⥤ Type u) (PresheafPredicateFirstOrder.indexed C) where
  object := omegaFunctor (C := C)
  truth := truthPredicate C
  characteristic := chiOfSubfunctor
  classifies := characteristic_classifies
  unique := characteristic_unique

noncomputable abbrev totalTruth (C : Type u) [Category.{u} C] : PresheafPredicateTotal C :=
  totalOfPredicate (omegaFunctor (C := C)) (truthPredicate C)

/-- The complete classification arrow in the existing total category. -/
noncomputable def classify (a : PresheafPredicateTotal C) : a ⟶ totalTruth C :=
  (generic C).classify a

theorem classify_base (a : PresheafPredicateTotal C) :
    (classify a).base = chiOfSubfunctor a.base (objectPredicate a) := rfl

/-- Cartesian arrows are exactly inverse-image predicate presentations. -/
theorem cartesian_iff_exact {a b : PresheafPredicateTotal C} (arrow : a ⟶ b) :
    IsStronglyCartesian (presheafPredicateProjection C) arrow.base arrow ↔
      objectPredicate a = (objectPredicate b).preimage arrow.base :=
  (PresheafPredicateFirstOrder.indexed C).cartesian_iff_predicate_eq arrow

theorem classify_cartesian (a : PresheafPredicateTotal C) :
    IsStronglyCartesian (presheafPredicateProjection C) (classify a).base (classify a) :=
  (generic C).classify_cartesian a

/-- Every supplied total predicate has precisely one Cartesian arrow to
generic truth. Its base is the independently constructed characteristic map. -/
theorem unique_cartesian_classification (a : PresheafPredicateTotal C) :
    ∃! arrow : a ⟶ totalTruth C,
      IsStronglyCartesian (presheafPredicateProjection C) arrow.base arrow :=
  (generic C).unique_cartesian_classification a

theorem classification_unique (a : PresheafPredicateTotal C) (arrow : a ⟶ totalTruth C)
    [IsStronglyCartesian (presheafPredicateProjection C) arrow.base arrow] :
    arrow = classify a := by
  apply hom_ext
  exact characteristic_unique a.base (objectPredicate a) arrow.base
    ((cartesian_iff_exact arrow).mp inferInstance).symm

/-- Changing context changes the characteristic map by actual composition. -/
theorem characteristic_substitution {P Q : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q)
    (φ : Subfunctor Q) :
    chiOfSubfunctor P (φ.preimage f) = f ≫ chiOfSubfunctor Q φ :=
  (generic C).characteristic_reindex f φ

end Mettapedia.GSLT.Topos.PresheafPredicateGenericTruth
