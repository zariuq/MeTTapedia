import Mettapedia.CategoryTheory.PseudoTwoArrowCoherence
import Mettapedia.CategoryTheory.AdjunctionSquareNaturality
import Mathlib.CategoryTheory.Bicategory.InducedBicategory

/-!
# Adjunctions as objects of a two-category

Objects retain two endpoint categories, both adjoints and their actual
unit and counit. Morphisms consist of endpoint maps and an invertible
right-adjoint square. The left comparison is its canonical mate.
Invertibility of the right square does not assert invertibility of that
mate. The latter is a separate strong-morphism property, closed under
identity and composition by the mate-pasting theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.CategoryTheory

open _root_.CategoryTheory _root_.CategoryTheory.Bicategory

universe w v u
variable (B : Type u) [Bicategory.{w,v} B]

structure AdjunctionObject where
  source : B
  target : B
  left : source ⟶ target
  right : target ⟶ source
  adjunction : left ⊣ right

namespace AdjunctionObject

def rightArrow (object : AdjunctionObject B) : PseudoTwoArrow B :=
  ⟨object.target, object.source, object.right⟩

end AdjunctionObject

/-- The induced construction keeps precisely the actual invertible square
morphisms and compatible endpoint cells; only its objects acquire adjunctions. -/
abbrev AdjunctionTwoCategory :=
  InducedBicategory (PseudoTwoArrow B) (AdjunctionObject.rightArrow (B := B))

namespace AdjunctionTwoCategory

variable {B}

def forget : StrictPseudofunctor (AdjunctionTwoCategory B) (PseudoTwoArrow B) :=
  InducedBicategory.forget

instance localFaithful (source target : AdjunctionTwoCategory B) :
    (forget.mapFunctor source target).Faithful where
  map_injective same := InducedBicategory.hom₂_ext same

instance localFull (source target : AdjunctionTwoCategory B) :
    (forget.mapFunctor source target).Full where
  map_surjective change := ⟨⟨change⟩, rfl⟩

/-- The comparison is computed from the supplied adjunctions and the
complete right-square comparison, including their units and counits. -/
def leftMate {source target : AdjunctionTwoCategory B} (route : source ⟶ target) :
    route.hom.right ≫ target.left ⟶ source.left ≫ route.hom.left :=
  (mateEquiv source.adjunction target.adjunction).symm route.hom.comm.hom

@[simp] theorem mate_leftMate {source target : AdjunctionTwoCategory B}
    (route : source ⟶ target) :
    mateEquiv source.adjunction target.adjunction (leftMate route) =
      route.hom.comm.hom :=
  (mateEquiv source.adjunction target.adjunction).apply_symm_apply _

/-- Right and left compatibility cubes are equivalent for the complete
chosen comparison. Thus endpoint cells preserve both adjunction faces. -/
theorem leftMate_cell {source target : AdjunctionTwoCategory B}
    {first second : source ⟶ target} (change : first ⟶ second) :
    change.hom.right ▷ target.left ≫ leftMate second =
      leftMate first ≫ source.left ◁ change.hom.left := by
  apply (AdjunctionSquareNaturality.compatibility_iff source.adjunction target.adjunction
    change.hom.right change.hom.left (leftMate first) (leftMate second)).mpr
  have same := change.hom.compatible
  change source.right ◁ change.hom.right ≫ second.hom.comm.hom =
    first.hom.comm.hom ≫ change.hom.left ▷ target.right at same
  exact (congrArg₂ (fun earlier later =>
    source.right ◁ change.hom.right ≫ later = earlier ≫ change.hom.left ▷ target.right)
    (mate_leftMate first) (mate_leftMate second)).mpr same

/-- The independently computed mate of a pasted right comparison is the
pasting of the independently computed left comparisons. -/
theorem leftMate_composition {source middle target : AdjunctionTwoCategory B}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    leftMate (first ≫ second) =
      leftAdjointSquare.vcomp (leftMate first) (leftMate second) := by
  apply (mateEquiv source.adjunction target.adjunction).injective
  exact (mate_leftMate (first ≫ second)).trans
    ((congrArg₂ rightAdjointSquare.vcomp (mate_leftMate first)
      (mate_leftMate second)).symm.trans
        (mateEquiv_vcomp source.adjunction middle.adjunction target.adjunction
          (leftMate first) (leftMate second)).symm)

theorem leftMate_identity (source : AdjunctionTwoCategory B) :
    leftMate (𝟙 source : source ⟶ source) =
      (λ_ source.left).hom ≫ (ρ_ source.left).inv := by
  apply (mateEquiv source.adjunction source.adjunction).injective
  exact (mate_leftMate (𝟙 source)).trans
    (mateEquiv_leftUnitor_hom_rightUnitor_inv source.adjunction).symm

/-- The strong profile is a property of the actual canonical mate, not a
second freely chosen comparison and not part of the ambient morphism type. -/
def Strong {source target : AdjunctionTwoCategory B} (route : source ⟶ target) : Prop :=
  IsIso (leftMate route)

theorem strong_identity (source : AdjunctionTwoCategory B) :
    Strong (𝟙 source : source ⟶ source) := by
  unfold Strong
  rw [leftMate_identity]
  infer_instance

theorem strong_composition {source middle target : AdjunctionTwoCategory B}
    (first : source ⟶ middle) (second : middle ⟶ target)
    (firstStrong : Strong first) (secondStrong : Strong second) :
    Strong (first ≫ second) := by
  let : IsIso (leftMate first) := firstStrong
  let : IsIso (leftMate second) := secondStrong
  unfold Strong
  rw [leftMate_composition]
  unfold leftAdjointSquare.vcomp
  infer_instance

noncomputable def leftComparison {source target : AdjunctionTwoCategory B}
    (route : source ⟶ target) (strong : Strong route) :
    route.hom.right ≫ target.left ≅ source.left ≫ route.hom.left := by
  letI : IsIso (leftMate route) := strong
  exact asIso (leftMate route)

@[simp] theorem leftComparison_hom {source target : AdjunctionTwoCategory B}
    (route : source ⟶ target) (strong : Strong route) :
    (leftComparison route strong).hom = leftMate route := rfl

end AdjunctionTwoCategory
end Mettapedia.CategoryTheory
