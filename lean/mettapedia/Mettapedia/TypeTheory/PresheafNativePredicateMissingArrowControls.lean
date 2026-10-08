import Mettapedia.TypeTheory.PresheafNativePredicateLogicalRestriction
import Mettapedia.GSLT.Topos.PresheafPredicateQuantifierBaseChangeControls

/-!
# Object coverage without future-arrow coverage

The source theory reaches every object of the target theory but retains
only identity arrows. A native argument family is empty at the supplied
world and acquires an inhabitant after a genuine target restriction.
The actual native universal judgment is false before restriction and true
after the future arrow has been omitted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.PresheafNativePredicateMissingArrowControls

open _root_.CategoryTheory
open Mettapedia.GSLT.Topos
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafCwf
open ContextualLocalUniverses NativeLocalTypeFormers NativeLocalTheoryRestriction
open PresheafNativePredicateQuantifierSubstitution
open PresheafPredicateQuantifierBaseChangeControls

abbrev Sparse := Discrete Context

def omitArrows : Sparse ⥤ Context := Discrete.functor id

theorem every_target_object_is_reached (world : Context) :
    ∃ source : Sparse, omitArrows.obj source = world := ⟨Discrete.mk world, rfl⟩

abbrev growthFamily : DisplayedFamily unitPrograms :=
  CategoryOfElements.π unitPrograms ⋙ growing

abbrev argument : NativeType unitPrograms := LocalType.present growthFamily

def sparseSpot : Sparseᵒᵖ := Opposite.op (Discrete.mk spot.unop)

theorem complete_universal_is_false :
    () ∉ (nativeForall argument (⊥ : Subfunctor (totalSpace argument.decoded))).obj spot := by
  intro holds
  exact holds future restriction ⟨(), ()⟩ rfl

theorem restricted_universal_is_true :
    () ∈ (nativeForall (restrict omitArrows argument)
      (PresheafNativeRefinementRestriction.predicate omitArrows argument ⊥)).obj sparseSpot := by
  intro next arrow supplied over
  have same : next = sparseSpot :=
    Opposite.unop_injective (Discrete.ext (Discrete.eq_of_hom arrow.unop))
  subst next
  exact Empty.elim supplied.2

/-- Every target object is reached, yet the independently formed
native universal predicates disagree at an actual supplied program. -/
theorem object_coverage_does_not_preserve_native_universal :
    LogicalTransport.restrictPredicate omitArrows
        (nativeForall argument (⊥ : Subfunctor (totalSpace argument.decoded))) ≠
      nativeForall (restrict omitArrows argument)
        (PresheafNativeRefinementRestriction.predicate omitArrows argument ⊥) := by
  intro same
  have belongs := restricted_universal_is_true
  rw [← same] at belongs
  exact complete_universal_is_false belongs

theorem omitted_arrows_do_not_supply_geometric_coverage :
    ¬ LogicalTransport.LiftsRestrictions omitArrows := by
  intro lifting
  exact object_coverage_does_not_preserve_native_universal
    (PresheafNativePredicateLogicalRestriction.forall_restriction_eq
      omitArrows lifting argument ⊥)

end Mettapedia.TypeTheory.PresheafNativePredicateMissingArrowControls
