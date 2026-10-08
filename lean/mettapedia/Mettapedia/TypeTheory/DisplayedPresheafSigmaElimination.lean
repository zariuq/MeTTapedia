import Mettapedia.TypeTheory.DisplayedPresheafSliceSigma

/-!
# Dependent pair elimination in the native presheaf model

The elimination motive is a family over the complete dependent pair
context. Its body is a section over the unpacked two-variable context.
The existing comprehension reassociation supplies elimination with beta,
eta, and naturality in the motive. Both components of the dependent pair
are retained throughout.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafSigmaElimination

open _root_.CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSigma DisplayedPresheafSliceSigma

universe u
variable {C : Type u} [Category.{u} C] {P Q : Cᵒᵖ ⥤ Type u}

def eliminate (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A))
    (motive : DisplayedFamily (totalSpace (sigmaDisplayed A B)))
    (body : (reindexDisplayed (sigmaTotalIso A B).inv motive).sections) : motive.sections where
  val point := body.val ((sigmaTotalIso A B).hom.mapElements.obj point)
  property arrow := body.property ((sigmaTotalIso A B).hom.mapElements.map arrow)

/-- Unpacking and then eliminating a freshly constructed pair computes
the supplied dependent body at those exact two witnesses. -/
theorem beta (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A))
    (motive : DisplayedFamily (totalSpace (sigmaDisplayed A B)))
    (body : (reindexDisplayed (sigmaTotalIso A B).inv motive).sections) :
    reindexDisplayedSection (sigmaTotalIso A B).inv motive (eliminate A B motive body) = body := by
  apply (Functor.sections_ext_iff).2
  intro point
  rfl

theorem eta (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A))
    (motive : DisplayedFamily (totalSpace (sigmaDisplayed A B))) (term : motive.sections) :
    eliminate A B motive (reindexDisplayedSection (sigmaTotalIso A B).inv motive term) = term := by
  apply (Functor.sections_ext_iff).2
  intro point
  rfl

/-- The independent two-variable and pair-context presentations give the
same dependent terms, with actual witnesses rather than support predicates. -/
def sectionEquiv (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A))
    (motive : DisplayedFamily (totalSpace (sigmaDisplayed A B))) :
    (reindexDisplayed (sigmaTotalIso A B).inv motive).sections ≃ motive.sections where
  toFun := eliminate A B motive
  invFun := reindexDisplayedSection (sigmaTotalIso A B).inv motive
  left_inv := beta A B motive
  right_inv := eta A B motive

theorem eliminate_naturality (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A))
    {motive other : DisplayedFamily (totalSpace (sigmaDisplayed A B))}
    (changeMotive : motive ⟶ other)
    (body : (reindexDisplayed (sigmaTotalIso A B).inv motive).sections) :
    (Functor.sectionsFunctor _).map changeMotive (eliminate A B motive body) =
      eliminate A B other ((Functor.sectionsFunctor _).map
        (Functor.whiskerLeft (sigmaTotalIso A B).inv.mapElements changeMotive) body) := by
  apply (Functor.sections_ext_iff).2
  intro point
  rfl

/-- Context substitution on pairs follows the existing comprehension
reassociation and the two actual dependent substitution maps. -/
def substitutedPairMap (f : Q ⟶ P) (A : DisplayedFamily P)
    (B : DisplayedFamily (totalSpace A)) :
    totalSpace (sigmaDisplayed (reindexDisplayed f A)
      (reindexDisplayed (totalReindexMap f A) B)) ⟶ totalSpace (sigmaDisplayed A B) :=
  (sigmaTotalIso (reindexDisplayed f A) (reindexDisplayed (totalReindexMap f A) B)).hom ≫
    totalReindexMap (totalReindexMap f A) B ≫ (sigmaTotalIso A B).inv

theorem eliminate_substitution (f : Q ⟶ P) (A : DisplayedFamily P)
    (B : DisplayedFamily (totalSpace A))
    (motive : DisplayedFamily (totalSpace (sigmaDisplayed A B)))
    (body : (reindexDisplayed (sigmaTotalIso A B).inv motive).sections) :
    reindexDisplayedSection (substitutedPairMap f A B) motive (eliminate A B motive body) =
      eliminate (reindexDisplayed f A) (reindexDisplayed (totalReindexMap f A) B)
        (reindexDisplayed (substitutedPairMap f A B) motive)
        (reindexDisplayedSection (totalReindexMap (totalReindexMap f A) B)
          (reindexDisplayed (sigmaTotalIso A B).inv motive) body) := by
  apply (Functor.sections_ext_iff).2
  intro point
  rfl

end Mettapedia.TypeTheory.DisplayedPresheafSigmaElimination
