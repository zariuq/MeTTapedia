import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ExecutionRectangle

/-!
# The exact admission domain of a proposed execution rectangle

Every complete shuffle is admitted exactly when every edge of the finite
rectangle is admitted. Preparations, component framing and residual coherence
belong to the supplied diagram; they are not inferred from equal endpoints.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ExecutionGeometry.Rectangle

universe uV uE
variable {V : Type uV} [Quiver.{uE} V] (permit : WideSubquiver V)

theorem allPermitted_zero (grid : Rectangle V 0 0) : AllPermitted permit grid :=
  ⟨fun i => i.elim0, fun _ j => j.elim0⟩

theorem allPermitted_horizontal {width : Nat} (grid : Rectangle V (width + 1) 0)
    (head : grid.firstHorizontal ∈ permit _ _)
    (lower : AllPermitted permit grid.dropHorizontal) : AllPermitted permit grid := by
  constructor
  · intro i j
    have lastJ : j = Fin.last 0 := by apply Fin.ext; omega
    subst j
    by_cases last : i = Fin.last width
    · subst i
      exact head
    · have before : i.val < width := by
        have bounded := i.isLt
        have different : i.val ≠ width := fun same => last (Fin.ext same)
        omega
      exact lower.horizontal ⟨i.val, before⟩ (Fin.last 0)
  · intro _ j
    exact j.elim0

theorem allPermitted_vertical {height : Nat} (grid : Rectangle V 0 (height + 1))
    (head : grid.firstVertical ∈ permit _ _)
    (lower : AllPermitted permit grid.dropVertical) : AllPermitted permit grid := by
  constructor
  · intro i
    exact i.elim0
  · intro i j
    have lastI : i = Fin.last 0 := by apply Fin.ext; omega
    subst i
    by_cases last : j = Fin.last height
    · subst j
      exact head
    · have before : j.val < height := by
        have bounded := j.isLt
        have different : j.val ≠ height := fun same => last (Fin.ext same)
        omega
      exact lower.vertical (Fin.last 0) ⟨j.val, before⟩

theorem allPermitted_successors {width height : Nat}
    (grid : Rectangle V (width + 1) (height + 1))
    (headH : grid.firstHorizontal ∈ permit _ _)
    (headV : grid.firstVertical ∈ permit _ _)
    (lowerH : AllPermitted permit grid.dropHorizontal)
    (lowerV : AllPermitted permit grid.dropVertical) : AllPermitted permit grid := by
  constructor
  · intro i j
    by_cases lastI : i = Fin.last width
    · subst i
      by_cases lastJ : j = Fin.last (height + 1)
      · subst j
        exact headH
      · have before : j.val < height + 1 := by
          have bounded := j.isLt
          have different : j.val ≠ height + 1 := fun same => lastJ (Fin.ext same)
          omega
        exact lowerV.horizontal (Fin.last width) ⟨j.val, before⟩
    · have before : i.val < width := by
        have bounded := i.isLt
        have different : i.val ≠ width := fun same => lastI (Fin.ext same)
        omega
      exact lowerH.horizontal ⟨i.val, before⟩ j
  · intro i j
    by_cases lastJ : j = Fin.last height
    · subst j
      by_cases lastI : i = Fin.last (width + 1)
      · subst i
        exact headV
      · have before : i.val < width + 1 := by
          have bounded := i.isLt
          have different : i.val ≠ width + 1 := fun same => lastI (Fin.ext same)
          omega
        exact lowerH.vertical ⟨i.val, before⟩ (Fin.last height)
    · have before : j.val < height := by
        have bounded := j.isLt
        have different : j.val ≠ height := fun same => lastJ (Fin.ext same)
        omega
      exact lowerV.vertical i ⟨j.val, before⟩

theorem allPermitted_of_all_shuffles : ∀ {width height : Nat}
    (grid : Rectangle V width height), (∀ shuffle, Admitted permit grid shuffle) →
      AllPermitted permit grid
  | 0, 0, grid, _ => allPermitted_zero permit grid
  | width + 1, 0, grid, all =>
      allPermitted_horizontal permit grid
        ((admitted_horizontal_iff grid (Shuffle.canonical width 0)).mp
          (all (.horizontal (Shuffle.canonical width 0)))).1
        (allPermitted_of_all_shuffles grid.dropHorizontal
          (fun shuffle => ((admitted_horizontal_iff grid shuffle).mp (all (.horizontal shuffle))).2))
  | 0, height + 1, grid, all =>
      allPermitted_vertical permit grid
        ((admitted_vertical_iff grid (Shuffle.canonical 0 height)).mp
          (all (.vertical (Shuffle.canonical 0 height)))).1
        (allPermitted_of_all_shuffles grid.dropVertical
          (fun shuffle => ((admitted_vertical_iff grid shuffle).mp (all (.vertical shuffle))).2))
  | width + 1, height + 1, grid, all =>
      allPermitted_successors permit grid
        ((admitted_horizontal_iff grid (Shuffle.canonical width (height + 1))).mp
          (all (.horizontal (Shuffle.canonical width (height + 1))))).1
        ((admitted_vertical_iff grid (Shuffle.canonical (width + 1) height)).mp
          (all (.vertical (Shuffle.canonical (width + 1) height)))).1
        (allPermitted_of_all_shuffles grid.dropHorizontal
          (fun shuffle => ((admitted_horizontal_iff grid shuffle).mp (all (.horizontal shuffle))).2))
        (allPermitted_of_all_shuffles grid.dropVertical
          (fun shuffle => ((admitted_vertical_iff grid shuffle).mp (all (.vertical shuffle))).2))
termination_by width height _ _ => width + height

theorem allPermitted_iff_all_shuffles {width height : Nat} (grid : Rectangle V width height) :
    AllPermitted permit grid ↔ ∀ shuffle, Admitted permit grid shuffle :=
  ⟨fun all shuffle => admitted_of_all shuffle grid all, allPermitted_of_all_shuffles permit grid⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ExecutionGeometry.Rectangle
