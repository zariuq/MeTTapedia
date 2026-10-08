import Mettapedia.TypeTheory.PresheafNativePredicateIntroduction

/-!
# Change of base for predicate comprehension

Predicate refinement commutes with inverse image on its complete dependent
context. The comparison acts on each original inhabitant, and its complete
context lift commutes with forgetting, identities and composition. The
introduction and elimination section squares use these same actual maps.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafNativePredicateSubstitution

open _root_.CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafSlice
open PresheafNativePredicateRefinement

universe u
variable {C : Type u} [Category.{u} C]
variable {P Q R : Cᵒᵖ ⥤ Type u}

def pulled (substitution : Q ⟶ P) (A : DisplayedFamily P)
    (predicate : Subfunctor (totalSpace A)) :
    Subfunctor (totalSpace (reindexDisplayed substitution A)) :=
  predicate.preimage (totalReindexMap substitution A)

def substitutionIso (substitution : Q ⟶ P) (A : DisplayedFamily P)
    (predicate : Subfunctor (totalSpace A)) :
    reindexDisplayed substitution (displayed A predicate) ≅
      displayed (reindexDisplayed substitution A) (pulled substitution A predicate) where
  hom :=
    { app := fun _ => TypeCat.ofHom fun value => ⟨value.val, value.property⟩
      naturality := by intro first second arrow; ext value; rfl }
  inv :=
    { app := fun _ => TypeCat.ofHom fun value => ⟨value.val, value.property⟩
      naturality := by intro first second arrow; ext value; rfl }
  hom_inv_id := by ext point value; rfl
  inv_hom_id := by ext point value; rfl

def lift (substitution : Q ⟶ P) (A : DisplayedFamily P)
    (predicate : Subfunctor (totalSpace A)) :
    totalSpace (displayed (reindexDisplayed substitution A) (pulled substitution A predicate)) ⟶
      totalSpace (displayed A predicate) :=
  totalHom (substitutionIso substitution A predicate).inv ≫
    totalReindexMap substitution (displayed A predicate)

theorem forget_square (substitution : Q ⟶ P) (A : DisplayedFamily P)
    (predicate : Subfunctor (totalSpace A)) :
    lift substitution A predicate ≫ forgetTotal A predicate =
      forgetTotal (reindexDisplayed substitution A) (pulled substitution A predicate) ≫
        totalReindexMap substitution A := by
  ext world value
  rfl

theorem projection_square (substitution : Q ⟶ P) (A : DisplayedFamily P)
    (predicate : Subfunctor (totalSpace A)) :
    lift substitution A predicate ≫ totalProjection (displayed A predicate) =
      totalProjection (displayed (reindexDisplayed substitution A)
        (pulled substitution A predicate)) ≫ substitution := by
  ext world value
  rfl

theorem pulled_identity (A : DisplayedFamily P) (predicate : Subfunctor (totalSpace A)) :
    pulled (𝟙 P) A predicate = predicate := by
  ext world value
  rfl

theorem pulled_composition (earlier : R ⟶ Q) (later : Q ⟶ P)
    (A : DisplayedFamily P) (predicate : Subfunctor (totalSpace A)) :
    pulled (earlier ≫ later) A predicate =
      pulled earlier (reindexDisplayed later A) (pulled later A predicate) := by
  ext world value
  rfl

theorem lift_identity (A : DisplayedFamily P) (predicate : Subfunctor (totalSpace A)) :
    lift (𝟙 P) A predicate = 𝟙 (totalSpace (displayed A predicate)) := by
  ext world value
  rfl

theorem lift_composition (earlier : R ⟶ Q) (later : Q ⟶ P)
    (A : DisplayedFamily P) (predicate : Subfunctor (totalSpace A)) :
    lift earlier (reindexDisplayed later A) (pulled later A predicate) ≫
        lift later A predicate = lift (earlier ≫ later) A predicate := by
  ext world value
  rfl

theorem pulledSatisfaction (substitution : Q ⟶ P) (A : DisplayedFamily P)
    (predicate : Subfunctor (totalSpace A)) (term : A.sections)
    (satisfies : ∀ world (base : P.obj world),
      (⟨base, term.val ⟨world, base⟩⟩ : (totalSpace A).obj world) ∈ predicate.obj world) :
    ∀ world (base : Q.obj world),
      (⟨base, (reindexDisplayedSection substitution A term).val ⟨world, base⟩⟩ :
        (totalSpace (reindexDisplayed substitution A)).obj world) ∈
      (pulled substitution A predicate).obj world :=
  fun world base => satisfies world (substitution.app world base)

theorem introduction_square (substitution : Q ⟶ P) (A : DisplayedFamily P)
    (predicate : Subfunctor (totalSpace A)) (term : A.sections)
    (satisfies : ∀ world (base : P.obj world),
      (⟨base, term.val ⟨world, base⟩⟩ : (totalSpace A).obj world) ∈ predicate.obj world) :
    (Functor.sectionsFunctor Q.Elements).map (substitutionIso substitution A predicate).hom
        (reindexDisplayedSection substitution (displayed A predicate)
          (introSection A predicate term satisfies)) =
      introSection (reindexDisplayed substitution A) (pulled substitution A predicate)
        (reindexDisplayedSection substitution A term)
        (pulledSatisfaction substitution A predicate term satisfies) := by
  apply (Functor.sections_ext_iff).2
  intro point
  rfl

theorem elimination_square (substitution : Q ⟶ P) (A : DisplayedFamily P)
    (predicate : Subfunctor (totalSpace A)) (term : (displayed A predicate).sections) :
    forgetSection (reindexDisplayed substitution A) (pulled substitution A predicate)
        ((Functor.sectionsFunctor Q.Elements).map (substitutionIso substitution A predicate).hom
          (reindexDisplayedSection substitution (displayed A predicate) term)) =
      reindexDisplayedSection substitution A (forgetSection A predicate term) := by
  apply (Functor.sections_ext_iff).2
  intro point
  rfl

end Mettapedia.TypeTheory.PresheafNativePredicateSubstitution
