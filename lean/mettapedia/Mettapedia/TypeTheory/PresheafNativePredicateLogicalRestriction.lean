import Mettapedia.TypeTheory.PresheafNativeRefinementRestriction
import Mettapedia.TypeTheory.PresheafNativePredicateQuantifierSubstitution

/-!
# Logical predicate operations of the native theory action

The predicate operations below use the actual native comprehension and its
weakening arrow. Theory restriction preserves existential image and image
types. Implication and universal quantification have colax comparisons in
general, with equality when every future restriction lifts up to an
isomorphism. An equivalence of theories supplies that geometric condition.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.PresheafNativePredicateLogicalRestriction

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder Mettapedia.GSLT.Topos
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafCwf
open DisplayedPresheafTheoryRestriction
open ContextualLocalUniverses NativeLocalTypeFormers NativeLocalTheoryRestriction
open NativeLocalTheoryTransformation
open PresheafNativeRefinementRestriction PresheafNativePredicateQuantifierSubstitution

universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {P : Dᵒᵖ ⥤ Type u}

/-- Fullness supplies every future arrow and essential surjectivity its
endpoint. The factorization is an actual geometric lifting condition. -/
theorem equivalence_lifts (F : C ⥤ D) [F.IsEquivalence] :
    LogicalTransport.LiftsRestrictions F := by
  intro world future arrow
  let preimage := F.op.objPreimage future
  let endpoint := F.op.objObjPreimageIso future
  refine ⟨preimage, F.op.preimage (arrow ≫ endpoint.inv), endpoint, ?_⟩
  rw [Functor.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Existential native judgments retain the actual selected argument
through the comprehension comparison. -/
theorem exists_restriction (F : C ⥤ D) (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded)) :
    LogicalTransport.restrictPredicate F (nativeExists A selected) =
      nativeExists (restrict F A) (predicate F A selected) := by
  ext world value
  rfl

theorem image_restriction (F : C ⥤ D) (A : NativeType P) :
    LogicalTransport.restrictPredicate F (nativeImage A) = nativeImage (restrict F A) := by
  ext world value
  rfl

/-- A source universal judgment covers the future arrows admitted by
the restricted native context. No converse coverage is inferred. -/
theorem forall_restriction_le (F : C ⥤ D) (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded)) :
    LogicalTransport.restrictPredicate F (nativeForall A selected) ≤
      nativeForall (restrict F A) (predicate F A selected) := by
  intro world value holds future arrow argument over
  exact holds (F.op.obj future) (F.op.map arrow)
    ((totalComparison F P A.decoded).hom.app future argument) over

/-- Geometric future coverage makes the native universal comparison
an equality, using the actual presheaf quantifier rather than an assumed
whole preservation contract. -/
theorem forall_restriction_eq (F : C ⥤ D)
    (lifting : LogicalTransport.LiftsRestrictions F) (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded)) :
    LogicalTransport.restrictPredicate F (nativeForall A selected) =
      nativeForall (restrict F A) (predicate F A selected) := by
  have lifted := LogicalTransport.restrict_forall_eq lifting
    ((nativeLocalModel D).toCwf.wk A) selected
  exact lifted

theorem forall_equivalence (F : C ⥤ D) [F.IsEquivalence] (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded)) :
    LogicalTransport.restrictPredicate F (nativeForall A selected) =
      nativeForall (restrict F A) (predicate F A selected) :=
  forall_restriction_eq F (equivalence_lifts F) A selected

/-- Classified conjunction and disjunction use the restricted complete
native argument context, including its retained inhabitants. -/
theorem predicate_inf (F : C ⥤ D) (A : NativeType P)
    (first second : Subfunctor (totalSpace A.decoded)) :
    predicate F A (first ⊓ second) = predicate F A first ⊓ predicate F A second := by
  ext world value
  rfl

theorem predicate_sup (F : C ⥤ D) (A : NativeType P)
    (first second : Subfunctor (totalSpace A.decoded)) :
    predicate F A (first ⊔ second) = predicate F A first ⊔ predicate F A second := by
  ext world value
  rfl

theorem predicate_implication_le (F : C ⥤ D) (A : NativeType P)
    (first second : Subfunctor (totalSpace A.decoded)) :
    predicate F A (first ⇨ second) ≤ predicate F A first ⇨ predicate F A second := by
  rw [predicate, predicate, predicate, ← preimage_himp]
  intro world value belongs
  exact LogicalTransport.restrict_implication_le F first second world belongs

theorem predicate_implication_eq (F : C ⥤ D)
    (lifting : LogicalTransport.LiftsRestrictions F) (A : NativeType P)
    (first second : Subfunctor (totalSpace A.decoded)) :
    predicate F A (first ⇨ second) = predicate F A first ⇨ predicate F A second := by
  rw [predicate, predicate, predicate, ← preimage_himp,
    LogicalTransport.restrict_implication_eq lifting]

theorem predicate_implication_equivalence (F : C ⥤ D) [F.IsEquivalence]
    (A : NativeType P) (first second : Subfunctor (totalSpace A.decoded)) :
    predicate F A (first ⇨ second) = predicate F A first ⇨ predicate F A second :=
  predicate_implication_eq F (equivalence_lifts F) A first second

end Mettapedia.TypeTheory.PresheafNativePredicateLogicalRestriction
