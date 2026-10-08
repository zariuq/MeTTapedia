import Mettapedia.CategoryTheory.CartesianEqualizerPullback
import Mettapedia.CategoryTheory.InternalCategoryPresentedDiagrams

/-!
# Complete product-equalizer presentation of an internal category

The supplied category uses its chosen pullback. Matching pairs and triples
are independently formed as product equalizers. Comparison of their full
universal lifts derives all seven local diagrams and a complete internal
category map back to the supplied model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalCategoryEqualizerPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable [HasFiniteLimits C] (original : InternalCategory C)

def endpoints : InternalCategoryPresentedDiagrams.Endpoints C where
  toInternalGraph := original.toInternalGraph
  pair := CartesianEqualizerPullback.cone original.target original.source
  pairLimit := CartesianEqualizerPullback.isLimit original.target original.source
  unit := original.unit
  composition := original.compose
    (CartesianEqualizerPullback.first original.target original.source)
    (CartesianEqualizerPullback.second original.target original.source)
    (CartesianEqualizerPullback.condition original.target original.source)
  unitSource := original.unit_source
  unitTarget := original.unit_target
  compositionSource := original.compose_source _ _ _
  compositionTarget := original.compose_target _ _ _

def triples : InternalCategoryPresentedDiagrams.TripleCone (endpoints original) :=
  CartesianEqualizerPullback.cone ((endpoints original).pair.snd ≫ original.target) original.source

def tripleLimit : IsLimit (triples original) :=
  CartesianEqualizerPullback.isLimit ((endpoints original).pair.snd ≫ original.target) original.source

theorem complete_compose_read {stage : C} (first second : stage ⟶ original.edge)
    (matching : first ≫ original.target = second ≫ original.source) :
    InternalCategoryPresentedDiagrams.compose (endpoints original) first second matching =
      original.compose first second matching := by
  change InternalCategoryPresentedDiagrams.pairLift (endpoints original) first second matching ≫
      (pullback.lift
        (CartesianEqualizerPullback.first original.target original.source)
        (CartesianEqualizerPullback.second original.target original.source) _ ≫ original.composition) =
    pullback.lift first second matching ≫ original.composition
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    exact PullbackCone.IsLimit.lift_fst (endpoints original).pairLimit first second matching
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
    exact PullbackCone.IsLimit.lift_snd (endpoints original).pairLimit first second matching

theorem complete_pair_read :
    (triples original).fst ≫ (endpoints original).composition =
      original.compose
        (InternalCategoryPresentedDiagrams.first (endpoints original) (triples original))
        (InternalCategoryPresentedDiagrams.middle (endpoints original) (triples original))
        (InternalCategoryPresentedDiagrams.first_matching (endpoints original) (triples original)) := by
  rw [← complete_compose_read original]
  change (triples original).fst ≫ (endpoints original).composition =
    InternalCategoryPresentedDiagrams.pairLift (endpoints original)
      ((triples original).fst ≫ (endpoints original).pair.fst)
      ((triples original).fst ≫ (endpoints original).pair.snd) _ ≫
        (endpoints original).composition
  congr 1
  apply PullbackCone.IsLimit.hom_ext (endpoints original).pairLimit
  · exact (PullbackCone.IsLimit.lift_fst _ _ _ _).symm
  · exact (PullbackCone.IsLimit.lift_snd _ _ _ _).symm

omit [CartesianMonoidalCategory C] in
theorem compose_congr {stage : C} {first first' second second' : stage ⟶ original.edge}
    (firstRead : first = first') (secondRead : second = second')
    (matching : first ≫ original.target = second ≫ original.source)
    (matching' : first' ≫ original.target = second' ≫ original.source) :
    original.compose first second matching = original.compose first' second' matching' := by
  subst first'
  subst second'
  rfl

theorem laws : InternalCategoryPresentedDiagrams.Laws (endpoints original) (triples original) where
  leftUnit := (complete_compose_read original _ _ _).trans original.unit_left
  rightUnit := (complete_compose_read original _ _ _).trans original.unit_right
  associativity := by
    let first := InternalCategoryPresentedDiagrams.first (endpoints original) (triples original)
    let middle := InternalCategoryPresentedDiagrams.middle (endpoints original) (triples original)
    let last := (triples original).snd
    have firstMatch : first ≫ original.target = middle ≫ original.source :=
      InternalCategoryPresentedDiagrams.first_matching (endpoints original) (triples original)
    have secondMatch : middle ≫ original.target = last ≫ original.source :=
      InternalCategoryPresentedDiagrams.second_matching (endpoints original) (triples original)
    have leftRead : InternalCategoryPresentedDiagrams.associateLeft
        (endpoints original) (triples original) =
        original.compose (original.compose first middle firstMatch) last
          (by rw [original.compose_target]; exact secondMatch) := by
      unfold InternalCategoryPresentedDiagrams.associateLeft
      rw [complete_compose_read original]
      congr 1
      exact complete_pair_read original
    have rightRead : InternalCategoryPresentedDiagrams.associateRight
        (endpoints original) (triples original) =
        original.compose first (original.compose middle last secondMatch)
          (by rw [original.compose_source]; exact firstMatch) := by
      unfold InternalCategoryPresentedDiagrams.associateRight
      exact (complete_compose_read original _ _ _).trans
        (compose_congr original rfl (complete_compose_read original middle last secondMatch) _ _)
    exact leftRead.trans ((original.associativity _ first middle last firstMatch secondMatch).trans rightRead.symm)

def category : InternalCategory C :=
  InternalCategoryPresentedDiagrams.category (endpoints original) (triples original)
    (tripleLimit original) (laws original)

theorem category_compose_read {stage : C} (first second : stage ⟶ original.edge)
    (matching : first ≫ original.target = second ≫ original.source) :
    (category original).compose first second matching = original.compose first second matching :=
  (InternalCategoryPresentedDiagrams.chosen_compose_read (endpoints original) first second matching).trans
    (complete_compose_read original first second matching)

def graphMap : InternalGraph.Hom (category original).toInternalGraph original.toInternalGraph where
  vertex := 𝟙 original.vertex
  edge := 𝟙 original.edge
  source := (Category.id_comp _).trans (Category.comp_id _).symm
  target := (Category.id_comp _).trans (Category.comp_id _).symm

theorem composition_read : (category original).composition = original.composition := by
    have actual := category_compose_read original (pullback.fst original.target original.source)
      (pullback.snd original.target original.source) pullback.condition
    change pullback.lift (pullback.fst _ _) (pullback.snd _ _) _ ≫
      (category original).composition =
        pullback.lift (pullback.fst _ _) (pullback.snd _ _) _ ≫ original.composition at actual
    have liftRead : pullback.lift (pullback.fst original.target original.source)
        (pullback.snd original.target original.source) pullback.condition = 𝟙 _ := by
      apply pullback.hom_ext <;> simp only [pullback.lift_fst, pullback.lift_snd, Category.id_comp]
    have lifted := congrArg (fun arrow : original.toInternalGraph.Composable ⟶ original.toInternalGraph.Composable =>
      arrow ≫ (category original).composition) liftRead
    have originalLift := congrArg (fun arrow : original.toInternalGraph.Composable ⟶ original.toInternalGraph.Composable =>
      arrow ≫ original.composition) liftRead
    exact (Category.id_comp _).symm.trans
      (lifted.symm.trans (actual.trans (originalLift.trans (Category.id_comp _))))

theorem graphMap_composable : (graphMap original).composableMap = 𝟙 original.toInternalGraph.Composable := by
  apply pullback.hom_ext
  · exact ((graphMap original).composableMap_first).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  · exact ((graphMap original).composableMap_second).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm)

def toOriginal : InternalCategory.Hom (category original) original where
  toHom := graphMap original
  unit := (Category.comp_id _).trans (Category.id_comp _).symm
  composition := (Category.comp_id _).trans ((composition_read original).trans
    ((Category.id_comp _).symm.trans
      (congrArg (fun arrow => arrow ≫ original.composition) (graphMap_composable original)).symm))

end Mettapedia.CategoryTheory.InternalCategoryEqualizerPresentation
