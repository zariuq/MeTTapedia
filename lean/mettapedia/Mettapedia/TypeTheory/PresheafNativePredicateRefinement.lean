import Mettapedia.TypeTheory.PresheafNativeLogicalAction
import Mettapedia.GSLT.Topos.PresheafImageComprehension

/-!
# Predicate refinement of varying native families

A classified predicate on a dependent family's complete total space selects
the satisfying inhabitants in each contextual fibre. The refinement retains
the original inhabitant; only the proof of predicate membership is
propositional. Its full comprehension space is isomorphic to the actual
predicate subfunctor, and its forgetful display arrow is the inclusion of
that subfunctor expressed over the original program context.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafNativePredicateRefinement

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafSlice
open DisplayedPresheafCwf DisplayedPresheafSliceSubstitution ContextualLocalUniverses
open NativeLocalTypeFormers NativeLocalTheoryTransformation NativeLocalDisplayComparisons
open Mettapedia.GSLT.Topos

universe u
variable {C : Type u} [Category.{u} C] {P Q : Cᵒᵖ ⥤ Type u}

local instance decodedCategory (P : Cᵒᵖ ⥤ Type u) :
    Category.{u} ((presheafCwf.{u, u, u} C).Ty P) :=
  inferInstanceAs (Category.{u} (DisplayedFamily.{u, u, u, u} P))

/-- The selected fibre consists of original inhabitants together with
membership in the predicate on the complete dependent context. -/
def displayed (A : DisplayedFamily P) (predicate : Subfunctor (totalSpace A)) :
    DisplayedFamily P where
  obj point := {value : A.obj point // (⟨point.2, value⟩ : (totalSpace A).obj point.1) ∈
    predicate.obj point.1}
  map arrow := TypeCat.ofHom fun value => ⟨A.map arrow value.val, by
    have transported := predicate.map arrow.val value.property
    change totalMap A arrow.val ⟨_, value.val⟩ ∈ predicate.obj _ at transported
    rw [totalMap_of_base_arrow A arrow value.val] at transported
    exact transported⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro value
    apply Subtype.ext
    exact A.map_id_apply point value.val
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro value
    apply Subtype.ext
    exact A.map_comp_apply first second value.val

def forgetFamily (A : DisplayedFamily P) (predicate : Subfunctor (totalSpace A)) :
    displayed A predicate ⟶ A where
  app _ := TypeCat.ofHom Subtype.val
  naturality _ _ _ := by ext value; rfl

/-- The native refinement presentation is available for every varying
external native family and every predicate on its actual total context. -/
def refinement (A : NativeType P) (predicate : Subfunctor (totalSpace A.decoded)) :
    NativeType P := LocalType.present (displayed A.decoded predicate)

def forgetDisplay (A : NativeType P) (predicate : Subfunctor (totalSpace A.decoded)) :
    (⟨refinement A predicate⟩ : TypeOver (nativeLocalModel C).toCwf P) ⟶ ⟨A⟩ :=
  displayHom _ _ (forgetFamily A.decoded predicate)

def forgetTotal (A : DisplayedFamily P) (predicate : Subfunctor (totalSpace A)) :
    totalSpace (displayed A predicate) ⟶ totalSpace A :=
  totalHom (forgetFamily A predicate)

theorem forgetDisplay_substitution (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded)) :
    (forgetDisplay A predicate).substitution = forgetTotal A.decoded predicate := rfl

/-- The full refinement context is the actual subfunctor comprehension,
with the original program point and selected inhabitant intact. -/
def totalIso (A : DisplayedFamily P) (predicate : Subfunctor (totalSpace A)) :
    totalSpace (displayed A predicate) ≅ predicate.toFunctor where
  hom :=
    { app := fun _ => TypeCat.ofHom fun value =>
        ⟨⟨value.1, value.2.val⟩, value.2.property⟩
      naturality := by
        intro first second arrow
        ext value
        apply Subtype.ext
        rfl }
  inv :=
    { app := fun _ => TypeCat.ofHom fun value =>
        ⟨value.val.1, ⟨value.val.2, value.property⟩⟩
      naturality := by
        intro first second arrow
        ext value
        rfl }
  hom_inv_id := by ext world value; rfl
  inv_hom_id := by ext world value; rfl

theorem forget_is_comprehension (A : DisplayedFamily P)
    (predicate : Subfunctor (totalSpace A)) :
    (totalIso A predicate).hom ≫ predicate.ι = forgetTotal A predicate := by
  ext world value
  rfl

/-- Refinement contains precisely the supplied predicate. It does not
replace the original dependent value by an erased inhabited-support test. -/
theorem image_forget (A : DisplayedFamily P) (predicate : Subfunctor (totalSpace A)) :
    Subfunctor.range (forgetTotal A predicate) = predicate := by
  ext world value
  constructor
  · rintro ⟨refined, same⟩
    change (⟨refined.1, refined.2.val⟩ : (totalSpace A).obj world) = value at same
    exact same ▸ refined.2.property
  · intro belongs
    exact ⟨⟨value.1, ⟨value.2, belongs⟩⟩, rfl⟩

def imageComprehensionIso (A : DisplayedFamily P)
    (predicate : Subfunctor (totalSpace A)) :
    Arrow.mk (forgetTotal A predicate) ≅
      ImageComprehension.comprehensionObject (totalOfPredicate (totalSpace A) predicate) :=
  Arrow.isoMk (totalIso A predicate) (Iso.refl _) (forget_is_comprehension A predicate)

noncomputable def classifiedRefinement (A : NativeType P)
    (predicate : A.decoded ⟶ DisplayedPresheafClassifier.propositions P) : NativeType P :=
  refinement A (DisplayedPresheafClassifier.predicateEquiv A.decoded predicate)

end Mettapedia.TypeTheory.PresheafNativePredicateRefinement
