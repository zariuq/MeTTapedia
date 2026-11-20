import Mettapedia.OSLF.Syntax.CartesianModelFilteredPresentation
import Mathlib.CategoryTheory.Limits.FintypeCat
import Mathlib.CategoryTheory.ComposableArrows.One
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.TransfiniteCompositionOfShape

/-!
# Finite observations that merge after stage transport

Two different observations of the represented two-element context land in
the represented one-element context. Transport to the represented empty
context identifies them. This is a filtered diagram of genuinely finitely
presented cartesian models, with an explicit colimit and a single-route
equality witness. Equality at the initial stage is false.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CartesianContextModels.FilteredControls

open CategoryTheory CategoryTheory.Limits Opposite

abbrev Context := FintypeCat.Skeleton.{0}

noncomputable instance : HasFiniteProducts Context :=
  ⟨fun _ => Adjunction.hasLimitsOfShape_of_equivalence FintypeCat.Skeleton.incl⟩

def finiteModel (n : Nat) : FinitelyPresentedModels Context :=
  (representedFiniteModel Context).obj (op (FintypeCat.Skeleton.mk n))

def leftSelector : FintypeCat.Skeleton.mk 1 ⟶ FintypeCat.Skeleton.mk 2 :=
  fun _ => ULift.up (0 : Fin 2)

def rightSelector : FintypeCat.Skeleton.mk 1 ⟶ FintypeCat.Skeleton.mk 2 :=
  fun _ => ULift.up (1 : Fin 2)

def emptyInclusion : FintypeCat.Skeleton.mk 0 ⟶ FintypeCat.Skeleton.mk 1 :=
  fun value => Fin.elim0 value.down

def firstObservation : (finiteModel 2).obj ⟶ (finiteModel 1).obj :=
  (representedContext Context).map leftSelector.op

def secondObservation : (finiteModel 2).obj ⟶ (finiteModel 1).obj :=
  (representedContext Context).map rightSelector.op

def transport : (finiteModel 1).obj ⟶ (finiteModel 0).obj :=
  (representedContext Context).map emptyInclusion.op

theorem observations_distinct : firstObservation ≠ secondObservation := by
  intro same
  have maps := (representedContext Context).map_injective same
  have selectors : leftSelector = rightSelector := Quiver.Hom.op_inj maps
  have values := congrArg (fun f => (f (ULift.up (0 : Fin 1))).down) selectors
  change (0 : Fin 2) = 1 at values
  exact (by decide : (0 : Fin 2) ≠ 1) values

theorem observations_merge : firstObservation ≫ transport = secondObservation ≫ transport := by
  have arrows : leftSelector.op ≫ emptyInclusion.op =
      rightSelector.op ≫ emptyInclusion.op := by
    apply Quiver.Hom.unop_inj
    funext value
    exact Fin.elim0 value.down
  exact ((representedContext Context).map_comp leftSelector.op emptyInclusion.op).symm.trans
    ((congrArg (fun f => (representedContext Context).map f) arrows).trans
      ((representedContext Context).map_comp rightSelector.op emptyInclusion.op))

def diagram : Fin 2 ⥤ Models Context := ComposableArrows.mk₁ transport

/-- The second stage is terminal in the indexing category; its model and
cocone are the explicit colimit. Both stages have their compactness proof. -/
noncomputable abbrev presentation : FilteredModelPresentation (finiteModel 0).obj where
  Stage := Fin 2
  category := inferInstance
  filtered := by
    have : HasTerminal (Fin 2) := (Fin.isTerminalLast 1).hasTerminal
    infer_instance
  presentation := {
    diag := diagram
    ι := (coconeOfDiagramTerminal (Fin.isTerminalLast 1) diagram).ι
    isColimit := colimitOfDiagramTerminal (Fin.isTerminalLast 1) diagram
  }
  compact := by
    intro stage
    fin_cases stage
    · exact (finiteModel 1).property
    · exact (finiteModel 0).property

theorem initial_images_equal :
    firstObservation ≫ presentation.presentation.ι.app 0 =
      secondObservation ≫ presentation.presentation.ι.app 0 := by
  simpa [presentation, diagram, coconeOfDiagramTerminal] using observations_merge

/-- The general compactness interface produces one common later route. -/
theorem equality_has_single_route :
    ∃ (stage : presentation.Stage) (route : (0 : presentation.Stage) ⟶ stage),
      firstObservation ≫ presentation.presentation.diag.map route =
        secondObservation ≫ presentation.presentation.diag.map route :=
  presentation.observations_equal_from_stage (finiteModel 2) (original := (0 : presentation.Stage))
    firstObservation secondObservation initial_images_equal

/-- Every such route leaves the initial stage: its two maps are not equal
there, although their images in the colimit are equal. -/
theorem equality_route_leaves_initial {stage : presentation.Stage}
    (route : (0 : presentation.Stage) ⟶ stage)
    (same : firstObservation ≫ presentation.presentation.diag.map route =
      secondObservation ≫ presentation.presentation.diag.map route) :
    stage ≠ 0 := by
  intro initial
  subst stage
  have identity : route = 𝟙 _ := Subsingleton.elim _ _
  have : IsIso route := by
    rw [identity]
    infer_instance
  apply observations_distinct
  exact (cancel_mono (presentation.presentation.diag.map route)).1 same

#print axioms presentation
#print axioms observations_distinct
#print axioms equality_has_single_route
#print axioms equality_route_leaves_initial

end Mettapedia.OSLF.CartesianContextModels.FilteredControls
