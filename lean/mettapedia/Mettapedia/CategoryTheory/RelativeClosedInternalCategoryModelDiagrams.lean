import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryMeaning
import Mettapedia.CategoryTheory.CartesianEqualizerPullback
import Mettapedia.CategoryTheory.InternalCategoryPresentedDiagrams

/-!
# Actual target categories from local evidence diagrams

The target's product equalizers independently supply matching pairs and
triples. Endpoint admission earns their complete source and target readouts.
Two finite unit diagrams and one triple diagram then derive associativity
at every context and construct an actual internal category.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedInternalCategory.ModelDiagrams

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe k w z

variable {C : Type k} [Category.{k} C] (vertex : C)
variable {D : Type w} [Category.{z} D] [CartesianMonoidalCategory D] [HasFiniteLimits D]
variable (base : C ⥤ D) (meaning : Meaning.Operations (base.obj vertex))
variable (endpointLaws : Meaning.EndpointLaws vertex base meaning)

def endpoints : InternalCategoryPresentedDiagrams.Endpoints D where
  vertex := base.obj vertex
  edge := meaning.edge
  source := meaning.source
  target := meaning.target
  pair := CartesianEqualizerPullback.cone meaning.target meaning.source
  pairLimit := CartesianEqualizerPullback.isLimit meaning.target meaning.source
  unit := meaning.unit
  composition := meaning.composition
  unitSource := endpointLaws.unitSource
  unitTarget := endpointLaws.unitTarget
  compositionSource := endpointLaws.compositionSource
  compositionTarget := endpointLaws.compositionTarget

def triples : InternalCategoryPresentedDiagrams.TripleCone (endpoints vertex base meaning endpointLaws) :=
  CartesianEqualizerPullback.cone (meaning.toGraph.second ≫ meaning.target) meaning.source

def tripleLimit : IsLimit (triples vertex base meaning endpointLaws) :=
  CartesianEqualizerPullback.isLimit (meaning.toGraph.second ≫ meaning.target) meaning.source

abbrev LocalLaws := InternalCategoryPresentedDiagrams.Laws
  (endpoints vertex base meaning endpointLaws) (triples vertex base meaning endpointLaws)

theorem pair_lift_read {stage : D} (first second : stage ⟶ meaning.edge)
    (matching : first ≫ meaning.target = second ≫ meaning.source) :
    InternalCategoryPresentedDiagrams.pairLift (endpoints vertex base meaning endpointLaws) first second matching =
      CartesianEqualizerPullback.lift meaning.target meaning.source first second matching := by
  apply PullbackCone.IsLimit.hom_ext (endpoints vertex base meaning endpointLaws).pairLimit
  · exact (PullbackCone.IsLimit.lift_fst _ _ _ _).trans
      (CartesianEqualizerPullback.lift_first meaning.target meaning.source first second matching).symm
  · exact (PullbackCone.IsLimit.lift_snd _ _ _ _).trans
      (CartesianEqualizerPullback.lift_second meaning.target meaning.source first second matching).symm

def category (laws : LocalLaws vertex base meaning endpointLaws) : InternalCategory D :=
  InternalCategoryPresentedDiagrams.category (endpoints vertex base meaning endpointLaws)
    (triples vertex base meaning endpointLaws) (tripleLimit vertex base meaning endpointLaws) laws

theorem category_compose_read (laws : LocalLaws vertex base meaning endpointLaws) {stage : D}
    (first second : stage ⟶ meaning.edge)
    (matching : first ≫ meaning.target = second ≫ meaning.source) :
    (category vertex base meaning endpointLaws laws).compose first second matching =
      CartesianEqualizerPullback.lift meaning.target meaning.source first second matching ≫ meaning.composition := by
  exact (InternalCategoryPresentedDiagrams.chosen_compose_read
    (endpoints vertex base meaning endpointLaws) first second matching).trans
      (congrArg (fun arrow => arrow ≫ meaning.composition)
        (pair_lift_read vertex base meaning endpointLaws first second matching))

end Mettapedia.CategoryTheory.RelativeClosedInternalCategory.ModelDiagrams
