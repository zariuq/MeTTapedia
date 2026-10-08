import Mettapedia.TypeTheory.DisplayedPresheafClassifier
import Mettapedia.TypeTheory.DisplayedPresheafTheoryRestrictionAction
import Mettapedia.TypeTheory.DisplayedPresheafTheoryTransformation
import Mettapedia.GSLT.Topos.ClassifierRestriction

/-!
# Classified dependent predicates under theory restriction

The truth comparison acts on actual contextual sieves. It composes with
the dependent-family action, classifies the restricted predicate, and is
compatible with substitution of the program base. These laws do not assert
that the comparison is invertible for an arbitrary theory functor.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafClassifierCoherence

open _root_.CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSliceSubstitution DisplayedPresheafClassifier
open DisplayedPresheafTheoryRestriction DisplayedPresheafTheoryRestrictionAction
open DisplayedPresheafTheoryTransformation
open Mettapedia.GSLT.Topos

universe u
variable {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]

/-- A dependent truth value restricts by inverse image of its sieve,
including all arrows of the source theory. -/
def comparison (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u) :
    restrictFamily F P (propositions P) ⟶ propositions (F.op ⋙ P) :=
  Functor.whiskerLeft (CategoryOfElements.π (F.op ⋙ P))
    (ClassifierRestriction.comparison F)

theorem comparison_apply (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (point : (F.op ⋙ P).Elements) (sieve : Sieve (F.obj point.1.unop)) :
    (comparison F P).app point sieve = Sieve.functorPullback F sieve := rfl

theorem comparison_identity (P : Cᵒᵖ ⥤ Type u) :
    comparison (𝟭 C) P = 𝟙 (propositions P) := by
  ext point sieve
  apply Sieve.ext
  intro future arrow
  rfl

/-- The full natural comparison, rather than an unrelated equivalence
of truth carriers, satisfies theory-composition coherence. -/
theorem comparison_composition (F : C ⥤ D) (G : D ⥤ E)
    (P : Eᵒᵖ ⥤ Type u) :
    comparison (F ⋙ G) P =
      (restrictionFunctor F (G.op ⋙ P)).map (comparison G P) ≫
        comparison F (G.op ⋙ P) := by
  ext point sieve
  apply Sieve.ext
  intro future arrow
  rfl

theorem truth_restriction (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u) :
    (restrictionFunctor F P).map (truth P) ≫ comparison F P = truth (F.op ⋙ P) := by
  ext point value
  apply Sieve.ext
  intro future arrow
  rfl

/-- The dependent characteristic square uses the actual comprehension
reassociation map, retaining both the program and its supplied evidence. -/
theorem characteristic_restriction (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (predicate : A ⟶ propositions P) :
    totalCharacteristic ((restrictionFunctor F P).map predicate ≫ comparison F P) =
      (totalComparison F P A).hom ≫
        Functor.whiskerLeft F.op (totalCharacteristic predicate) ≫
          ClassifierRestriction.comparison F := by
  ext world value
  rfl

/-- The classified subfunctor is the restricted predicate, expressed
over the actual dependent total-space presentation. -/
theorem predicate_restriction (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (predicate : A ⟶ propositions P) :
    predicateEquiv (restrictFamily F P A)
        ((restrictionFunctor F P).map predicate ≫ comparison F P) =
      (LogicalTransport.restrictPredicate F (predicateEquiv A predicate)).preimage
        (totalComparison F P A).hom := by
  ext world value
  change (predicate.app ⟨F.op.obj world, value.1⟩ value.2).arrows
      (F.map (𝟙 world.unop)) ↔
    (predicate.app ⟨F.op.obj world, value.1⟩ value.2).arrows (𝟙 (F.obj world.unop))
  rw [F.map_id]

/-- Program substitution leaves the same theory truth comparison at
every dependent point; it supplies no coverage of additional observers. -/
theorem comparison_substitution (F : C ⥤ D)
    {P Q : Dᵒᵖ ⥤ Type u} (programMap : P ⟶ Q) :
    (reindexFunctor (Functor.whiskerLeft F.op programMap)).map (comparison F Q) =
      comparison F P := by
  ext point sieve
  rfl

/-- A general theory transformation gives a lax truth comparison. Its
future components may add arrows to the pulled-back sieve. -/
theorem transformation_le {F G : C ⥤ D} (change : F ⟶ G)
    (P : Dᵒᵖ ⥤ Type u) (point : (G.op ⋙ P).Elements)
    (sieve : Sieve (G.obj point.1.unop)) :
    @LE.le (Sieve point.1.unop) inferInstance
      ((comparison G P).app point sieve)
      (((reindexFunctor (baseMap change P)).map (comparison F P)).app point
        ((familyMap change P (propositions P)).app point sieve)) := by
  intro future arrow belongs
  change sieve.arrows (G.map arrow) at belongs
  change sieve.arrows (F.map arrow ≫ change.app point.1.unop)
  rw [change.naturality arrow]
  exact sieve.downward_closed belongs (change.app future)

/-- Invertible theory transformations recover equality of the entire
native truth comparison square. -/
theorem transformation_iso {F G : C ⥤ D} (change : F ≅ G)
    (P : Dᵒᵖ ⥤ Type u) :
    familyMap change.hom P (propositions P) ≫
      (reindexFunctor (baseMap change.hom P)).map (comparison F P) =
        comparison G P := by
  ext point sieve
  change (((reindexFunctor (baseMap change.hom P)).map (comparison F P)).app point
    ((familyMap change.hom P (propositions P)).app point sieve) : Sieve point.1.unop) =
      (comparison G P).app point sieve
  apply @le_antisymm (Sieve point.1.unop) inferInstance
  · intro future arrow belongs
    change sieve.arrows (F.map arrow ≫ change.hom.app point.1.unop) at belongs
    change sieve.arrows (G.map arrow)
    have recovered : change.inv.app future ≫
        (F.map arrow ≫ change.hom.app point.1.unop) = G.map arrow := by
      rw [change.hom.naturality arrow, ← Category.assoc]
      have cancel := congrArg (fun natural => natural.app future) change.inv_hom_id
      change change.inv.app future ≫ change.hom.app future = 𝟙 (G.obj future) at cancel
      rw [cancel, Category.id_comp]
    exact recovered ▸ sieve.downward_closed belongs (change.inv.app future)
  · exact transformation_le change.hom P point sieve

end Mettapedia.TypeTheory.DisplayedPresheafClassifierCoherence
