import Mettapedia.TypeTheory.ContextualWitnessCover
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassPresheafProducts

/-!
# Small witness covers over actual displayed families

The free cover on the category of elements of a small displayed family gives
an actual small dependent sum over that family. Its first-coordinate
projection is natural and pointwise surjective. An authored possibly wide
witness functor on those element points receives a natural map from this
small cover, retaining both the displayed value and transported witness.

The wider dependent-sum functor is constructed with explicit laws; its fibre
universe is `max u v`. The cover's fibre remains literally `Type u`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedContextualWitnessCover

open CategoryTheory ContextualWitnessCover
open Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassPresheafProducts
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

universe u v

variable {D : Type u} [Category.{u} D] (A : D ⥤ Type u)

/-- Reuse the actual constructive dependent-sum functor on the category of
elements of the displayed family. No collecting carrier is supplied. -/
def smallCover : D ⥤ Type u := IndexedSigma.family A (free (E := A.Elements))

def projection : NatTrans (smallCover A) A where
  app _ := TypeCat.ofHom Sigma.fst
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro _
    rfl

def localLift (point : D) (value : A.obj point) : (smallCover A).obj point :=
  ⟨value, seed (E := A.Elements) (⟨point, value⟩ : A.Elements)⟩

theorem projection_surjective (point : D) : Function.Surjective ((projection A).app point) :=
  fun value => ⟨localLift A point value, rfl⟩

variable (R : A.Elements ⥤ Type v)

private theorem map_heq {first second other : A.Elements} (same : second = other)
    (left : first ⟶ second) (right : first ⟶ other) (sameArrow : HEq left.val right.val)
    (witness : R.obj first) : HEq (R.map left witness) (R.map right witness) := by
  cases same
  have arrows : left = right := Subtype.ext (eq_of_heq sameArrow)
  cases arrows
  rfl

/-- The actual wider witness relation over the displayed family. -/
def totalWitnesses : D ⥤ Type (max u v) where
  obj point := Σ value : A.obj point, R.obj ⟨point, value⟩
  map arrow := TypeCat.ofHom (fun receipt =>
    ⟨A.map arrow receipt.1, R.map (argumentMap A arrow receipt.1) receipt.2⟩)
  map_id point := by
    apply ConcreteCategory.hom_ext
    rintro ⟨value, witness⟩
    apply Sigma.ext (A.map_id_apply point value)
    have same : (⟨point, A.map (𝟙 point) value⟩ : A.Elements) = ⟨point, value⟩ :=
      Sigma.ext rfl (heq_of_eq (A.map_id_apply point value))
    exact (map_heq A R same (argumentMap A (𝟙 point) value) (𝟙 _) (heq_of_eq rfl) witness).trans
      (heq_of_eq (R.map_id_apply _ witness))
  map_comp {first middle last} earlier later := by
    apply ConcreteCategory.hom_ext
    rintro ⟨value, witness⟩
    apply Sigma.ext (A.map_comp_apply earlier later value)
    have same : (⟨last, A.map (earlier ≫ later) value⟩ : A.Elements) =
        ⟨last, A.map later (A.map earlier value)⟩ :=
      Sigma.ext rfl (heq_of_eq (A.map_comp_apply earlier later value))
    exact (map_heq A R same (argumentMap A (earlier ≫ later) value)
      (argumentMap A earlier value ≫ argumentMap A later (A.map earlier value))
      (heq_of_eq rfl) witness).trans (heq_of_eq (R.map_comp_apply _ _ witness))

def witnessProjection : NaturalHom (totalWitnesses A R) A where
  app _ := Sigma.fst
  naturality _ _ := rfl

/-- The actual small contextual cover maps naturally into a wider relation
using only authored local witness data. The first coordinate is retained. -/
def witnessMap (witness : ∀ point, R.obj point) :
    NaturalHom (smallCover A) (totalWitnesses A R) where
  app point receipt := ⟨receipt.1, (fromWitness R witness).app ⟨point, receipt.1⟩ receipt.2⟩
  naturality arrow receipt :=
    congrArg (Sigma.mk (A.map arrow receipt.1))
      ((fromWitness R witness).naturality (argumentMap A arrow receipt.1) receipt.2)

theorem witnessMap_projection (witness : ∀ point, R.obj point) :
    (witnessMap A R witness).comp (witnessProjection A R) =
      NaturalHom.ofNatTrans (projection A) := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem witnessMap_localLift (witness : ∀ point, R.obj point) (point : D) (value : A.obj point) :
    (witnessMap A R witness).app point (localLift A point value) =
      ⟨value, witness ⟨point, value⟩⟩ :=
  congrArg (fun term : R.obj ⟨point, value⟩ =>
    (⟨value, term⟩ : (totalWitnesses A R).obj point)) (fromWitness_seed R witness ⟨point, value⟩)

end Mettapedia.TypeTheory.DisplayedContextualWitnessCover
