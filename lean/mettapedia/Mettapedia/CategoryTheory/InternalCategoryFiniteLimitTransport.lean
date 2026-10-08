import Mettapedia.CategoryTheory.InternalCategoryPresentedDiagrams
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Internal category transport through preserved matching pullbacks

The mapped edge object retains the complete supplied evidence. Composition
uses the image of the original matching-pair object and its earned pullback
universal property. The mapped matching-triple diagram derives associativity
at every target stage, including stages outside the functor's object image.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransport

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {D : Type w} [Category.{z} D]
variable (F : C ⥤ D) [PreservesLimitsOfShape WalkingCospan F]
variable (original : InternalCategory C)

def endpoints : InternalCategoryPresentedDiagrams.Endpoints D where
  vertex := F.obj original.vertex
  edge := F.obj original.edge
  source := F.map original.source
  target := F.map original.target
  pair := PullbackCone.mk (F.map (pullback.fst original.target original.source))
    (F.map (pullback.snd original.target original.source))
    (by rw [← F.map_comp, ← F.map_comp, pullback.condition])
  pairLimit := isLimitOfHasPullbackOfPreservesLimit F original.target original.source
  unit := F.map original.unit
  composition := F.map original.composition
  unitSource := by rw [← F.map_comp, original.unit_source, F.map_id]
  unitTarget := by rw [← F.map_comp, original.unit_target, F.map_id]
  compositionSource := by
    change F.map original.composition ≫ F.map original.source =
      F.map (pullback.fst original.target original.source) ≫ F.map original.source
    exact (F.map_comp _ _).symm.trans
      ((congrArg F.map original.composition_source).trans (F.map_comp _ _))
  compositionTarget := by
    change F.map original.composition ≫ F.map original.target =
      F.map (pullback.snd original.target original.source) ≫ F.map original.target
    exact (F.map_comp _ _).symm.trans
      ((congrArg F.map original.composition_target).trans (F.map_comp _ _))

def originalEndpoints : InternalCategoryLocalDiagrams.Endpoints C where
  toInternalGraph := original.toInternalGraph
  unit := original.unit
  composition := original.composition
  unit_source := original.unit_source
  unit_target := original.unit_target
  composition_source := original.composition_source
  composition_target := original.composition_target

def triples : InternalCategoryPresentedDiagrams.TripleCone (endpoints F original) :=
  PullbackCone.mk
    (F.map (InternalCategoryLocalDiagrams.initialPair (originalEndpoints original)))
    (F.map (InternalCategoryLocalDiagrams.last (originalEndpoints original)))
    (by
      have actual := congrArg F.map (pullback.condition
        (f := pullback.snd original.target original.source ≫ original.target) (g := original.source))
      simpa only [originalEndpoints, InternalCategoryLocalDiagrams.initialPair,
        InternalCategoryLocalDiagrams.last, InternalCategoryLocalDiagrams.triples,
        endpoints, PullbackCone.mk_snd, F.map_comp] using actual)

def tripleLimit : IsLimit (triples F original) := by
  let mapped := isLimitOfHasPullbackOfPreservesLimit F
    (pullback.snd original.target original.source ≫ original.target) original.source
  let lift : ∀ s : InternalCategoryPresentedDiagrams.TripleCone (endpoints F original),
      s.pt ⟶ (triples F original).pt := fun s =>
    PullbackCone.IsLimit.lift mapped s.fst s.snd (by
      rw [F.map_comp]
      exact s.condition)
  refine PullbackCone.isLimitAux (triples F original) lift ?_ ?_ ?_
  · intro s
    exact PullbackCone.IsLimit.lift_fst mapped _ _ _
  · intro s
    exact PullbackCone.IsLimit.lift_snd mapped _ _ _
  · intro s m readings
    apply PullbackCone.IsLimit.hom_ext mapped
    · exact (readings WalkingCospan.left).trans (PullbackCone.IsLimit.lift_fst mapped _ _ _).symm
    · exact (readings WalkingCospan.right).trans (PullbackCone.IsLimit.lift_snd mapped _ _ _).symm

theorem mapped_matching {stage : C} (first second : stage ⟶ original.edge)
    (matching : first ≫ original.target = second ≫ original.source) :
    F.map first ≫ (endpoints F original).target = F.map second ≫ (endpoints F original).source := by
  change F.map first ≫ F.map original.target = F.map second ≫ F.map original.source
  rw [← F.map_comp, ← F.map_comp, matching]

theorem complete_pair_lift {stage : C} (first second : stage ⟶ original.edge)
    (matching : first ≫ original.target = second ≫ original.source) :
    InternalCategoryPresentedDiagrams.pairLift (endpoints F original)
        (F.map first) (F.map second) (mapped_matching F original first second matching) =
      F.map (pullback.lift first second matching) := by
  apply PullbackCone.IsLimit.hom_ext (endpoints F original).pairLimit
  · rw [InternalCategoryPresentedDiagrams.pairLift, PullbackCone.IsLimit.lift_fst]
    change F.map first = F.map (pullback.lift first second matching) ≫ F.map (pullback.fst _ _)
    rw [← F.map_comp, pullback.lift_fst]
  · rw [InternalCategoryPresentedDiagrams.pairLift, PullbackCone.IsLimit.lift_snd]
    change F.map second = F.map (pullback.lift first second matching) ≫ F.map (pullback.snd _ _)
    rw [← F.map_comp, pullback.lift_snd]

theorem complete_compose_read {stage : C} (first second : stage ⟶ original.edge)
    (matching : first ≫ original.target = second ≫ original.source) :
    InternalCategoryPresentedDiagrams.compose (endpoints F original)
        (F.map first) (F.map second) (mapped_matching F original first second matching) =
      F.map (original.compose first second matching) := by
  change InternalCategoryPresentedDiagrams.pairLift (endpoints F original)
    (F.map first) (F.map second) _ ≫ F.map original.composition =
      F.map (pullback.lift first second matching ≫ original.composition)
  rw [complete_pair_lift, F.map_comp]

theorem first_read :
    InternalCategoryPresentedDiagrams.first (endpoints F original) (triples F original) =
      F.map (InternalCategoryLocalDiagrams.first (originalEndpoints original)) := by
  change F.map (pullback.fst _ _) ≫ F.map (pullback.fst original.target original.source) = _
  exact (F.map_comp _ _).symm

theorem middle_read :
    InternalCategoryPresentedDiagrams.middle (endpoints F original) (triples F original) =
      F.map (InternalCategoryLocalDiagrams.middle (originalEndpoints original)) := by
  change F.map (pullback.fst _ _) ≫ F.map (pullback.snd original.target original.source) = _
  exact (F.map_comp _ _).symm

theorem original_initial_compose :
    InternalCategoryLocalDiagrams.initialPair (originalEndpoints original) ≫ original.composition =
      original.compose
        (InternalCategoryLocalDiagrams.first (originalEndpoints original))
        (InternalCategoryLocalDiagrams.middle (originalEndpoints original))
        (InternalCategoryLocalDiagrams.first_matching (originalEndpoints original)) := by
  change pullback.fst _ _ ≫ original.composition = pullback.lift _ _ _ ≫ original.composition
  congr 1
  apply pullback.hom_ext
  · exact (pullback.lift_fst _ _ _).symm
  · exact (pullback.lift_snd _ _ _).symm

theorem initial_compose_read :
    (triples F original).fst ≫ (endpoints F original).composition =
      F.map (original.compose
        (InternalCategoryLocalDiagrams.first (originalEndpoints original))
        (InternalCategoryLocalDiagrams.middle (originalEndpoints original))
        (InternalCategoryLocalDiagrams.first_matching (originalEndpoints original))) := by
  change F.map (InternalCategoryLocalDiagrams.initialPair (originalEndpoints original)) ≫
    F.map original.composition = _
  rw [← F.map_comp, original_initial_compose]

theorem laws : InternalCategoryPresentedDiagrams.Laws (endpoints F original) (triples F original) where
  leftUnit := by
    have input : (endpoints F original).source ≫ (endpoints F original).unit =
        F.map (original.source ≫ original.unit) := (F.map_comp _ _).symm
    exact (InternalCategoryPresentedDiagrams.compose_congr (endpoints F original)
      input (F.map_id original.edge).symm _ _).trans
      ((complete_compose_read F original (original.source ≫ original.unit) (𝟙 original.edge) _).trans
        ((congrArg F.map original.unit_left).trans (F.map_id original.edge)))
  rightUnit := by
    have input : (endpoints F original).target ≫ (endpoints F original).unit =
        F.map (original.target ≫ original.unit) := (F.map_comp _ _).symm
    exact (InternalCategoryPresentedDiagrams.compose_congr (endpoints F original)
      (F.map_id original.edge).symm input _ _).trans
      ((complete_compose_read F original (𝟙 original.edge) (original.target ≫ original.unit) _).trans
        ((congrArg F.map original.unit_right).trans (F.map_id original.edge)))
  associativity := by
    let before := InternalCategoryLocalDiagrams.first (originalEndpoints original)
    let middle := InternalCategoryLocalDiagrams.middle (originalEndpoints original)
    let after := InternalCategoryLocalDiagrams.last (originalEndpoints original)
    have firstMatch : before ≫ original.target = middle ≫ original.source :=
      InternalCategoryLocalDiagrams.first_matching (originalEndpoints original)
    have secondMatch : middle ≫ original.target = after ≫ original.source :=
      InternalCategoryLocalDiagrams.second_matching (originalEndpoints original)
    have leftRead : InternalCategoryPresentedDiagrams.associateLeft (endpoints F original) (triples F original) =
        F.map (original.compose (original.compose before middle firstMatch) after
          (by rw [original.compose_target]; exact secondMatch)) := by
      unfold InternalCategoryPresentedDiagrams.associateLeft
      exact (InternalCategoryPresentedDiagrams.compose_congr (endpoints F original)
        (initial_compose_read F original) rfl _ _).trans
          (complete_compose_read F original _ _ _)
    have innerRead : InternalCategoryPresentedDiagrams.compose (endpoints F original)
        (InternalCategoryPresentedDiagrams.middle (endpoints F original) (triples F original))
        (triples F original).snd
        (InternalCategoryPresentedDiagrams.second_matching (endpoints F original) (triples F original)) =
      F.map (original.compose middle after secondMatch) :=
      (InternalCategoryPresentedDiagrams.compose_congr (endpoints F original)
        (middle_read F original) rfl _ _).trans
          (complete_compose_read F original _ _ _)
    have rightRead : InternalCategoryPresentedDiagrams.associateRight (endpoints F original) (triples F original) =
        F.map (original.compose before (original.compose middle after secondMatch)
          (by rw [original.compose_source]; exact firstMatch)) := by
      unfold InternalCategoryPresentedDiagrams.associateRight
      exact (InternalCategoryPresentedDiagrams.compose_congr (endpoints F original)
        (first_read F original) innerRead _ _).trans
          (complete_compose_read F original _ _ _)
    exact leftRead.trans
      ((congrArg F.map (original.associativity _ before middle after firstMatch secondMatch)).trans rightRead.symm)

variable [HasPullbacks D]

def category : InternalCategory D :=
  InternalCategoryPresentedDiagrams.category (endpoints F original) (triples F original)
    (tripleLimit F original) (laws F original)

theorem complete_chosen_pair_lift :
    InternalCategoryPresentedDiagrams.pairLift (endpoints F original)
      (pullback.fst (F.map original.target) (F.map original.source))
      (pullback.snd (F.map original.target) (F.map original.source)) pullback.condition =
      (PreservesPullback.iso F original.target original.source).inv := by
  apply PullbackCone.IsLimit.hom_ext (endpoints F original).pairLimit
  · exact (PullbackCone.IsLimit.lift_fst _ _ _ _).trans
      (PreservesPullback.iso_inv_fst F original.target original.source).symm
  · exact (PullbackCone.IsLimit.lift_snd _ _ _ _).trans
      (PreservesPullback.iso_inv_snd F original.target original.source).symm

theorem complete_composition :
    (category F original).composition =
      (PreservesPullback.iso F original.target original.source).inv ≫ F.map original.composition := by
  change InternalCategoryPresentedDiagrams.pairLift (endpoints F original) _ _ _ ≫
    F.map original.composition = _
  exact congrArg (fun arrow => arrow ≫ F.map original.composition)
    (complete_chosen_pair_lift F original)

theorem category_compose_read {stage : C} (first second : stage ⟶ original.edge)
    (matching : first ≫ original.target = second ≫ original.source) :
    (category F original).compose (F.map first) (F.map second)
        (mapped_matching F original first second matching) =
      F.map (original.compose first second matching) :=
  (InternalCategoryPresentedDiagrams.chosen_compose_read (endpoints F original) _ _ _).trans
    (complete_compose_read F original first second matching)

end Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransport
