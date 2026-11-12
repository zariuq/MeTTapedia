import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ExecutionRectanglePaths
import Mathlib.CategoryTheory.Category.Basic

/-!
# Interchange for interpretations of execution rectangles

An interpretation that identifies each elementary square identifies every
interleaving. Equality of complete boundaries alone need not imply the local
equations. No equation on raw paths is imposed by equal endpoints.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ExecutionGeometry.Rectangle

open _root_.CategoryTheory

universe uV uE uC uH

variable {V : Type uV} [Quiver.{uE} V] {C : Type uC} [Category.{uH} C] (F : V ⥤q C)

def evaluate : ∀ {width height : Nat} (_shuffle : Shuffle width height)
    (grid : Rectangle V width height), F.obj grid.entry ⟶ F.obj grid.exit
  | _, _, .nil, _ => 𝟙 _
  | _, _, .horizontal rest, grid => F.map grid.firstHorizontal ≫ evaluate rest grid.dropHorizontal
  | _, _, .vertical rest, grid => F.map grid.firstVertical ≫ evaluate rest grid.dropVertical

def Commutes {width height : Nat} (grid : Rectangle V width height) : Prop :=
  ∀ i : Fin width, ∀ j : Fin height,
    F.map (grid.horizontal i j.succ) ≫ F.map (grid.vertical i.castSucc j) =
      F.map (grid.vertical i.succ j) ≫ F.map (grid.horizontal i j.castSucc)

theorem Commutes.dropHorizontal {width height : Nat} {grid : Rectangle V (width + 1) height}
    (commutes : Commutes F grid) : Commutes F grid.dropHorizontal :=
  fun i j => commutes i.castSucc j

theorem Commutes.dropVertical {width height : Nat} {grid : Rectangle V width (height + 1)}
    (commutes : Commutes F grid) : Commutes F grid.dropVertical :=
  fun i j => commutes i j.castSucc

theorem vertical_slide (height : Nat) : ∀ (width : Nat) (grid : Rectangle V width (height + 1)),
    Commutes F grid →
      F.map grid.firstVertical ≫ evaluate F (Shuffle.canonical width height) grid.dropVertical =
        evaluate F (Shuffle.canonical width (height + 1)) grid
  | 0, _, _ => rfl
  | width + 1, grid, commutes => by
      change F.map grid.firstVertical ≫
        (F.map grid.dropVertical.firstHorizontal ≫
          evaluate F (Shuffle.canonical width height) grid.dropVertical.dropHorizontal) =
        F.map grid.firstHorizontal ≫ evaluate F (Shuffle.canonical width (height + 1)) grid.dropHorizontal
      have corner : F.map grid.firstVertical ≫ F.map grid.dropVertical.firstHorizontal =
          F.map grid.firstHorizontal ≫ F.map grid.dropHorizontal.firstVertical :=
        (commutes (Fin.last width) (Fin.last height)).symm
      rw [← Category.assoc, corner, Category.assoc]
      exact congrArg (fun tail => F.map grid.firstHorizontal ≫ tail)
        (vertical_slide height width grid.dropHorizontal commutes.dropHorizontal)

theorem evaluate_eq_canonical : ∀ {width height : Nat} (shuffle : Shuffle width height)
    (grid : Rectangle V width height), Commutes F grid →
      evaluate F shuffle grid = evaluate F (Shuffle.canonical width height) grid
  | _, _, .nil, _, _ => rfl
  | width + 1, height, .horizontal rest, grid, commutes =>
      congrArg (fun tail => F.map grid.firstHorizontal ≫ tail)
        (evaluate_eq_canonical rest grid.dropHorizontal commutes.dropHorizontal)
  | width, height + 1, .vertical rest, grid, commutes => by
      rw [evaluate, evaluate_eq_canonical rest grid.dropVertical commutes.dropVertical]
      exact vertical_slide F height width grid commutes

theorem interleavings_agree {width height : Nat} (grid : Rectangle V width height)
    (commutes : Commutes F grid) (first second : Shuffle width height) :
    evaluate F first grid = evaluate F second grid :=
  (evaluate_eq_canonical F first grid commutes).trans
    (evaluate_eq_canonical F second grid commutes).symm

/-- Evaluation is the universal free-path extension, not a separate path semantics. -/
theorem evaluate_free_extension : ∀ {width height : Nat} (shuffle : Shuffle width height)
    (grid : Rectangle V width height),
    (Paths.lift F).map (proposal shuffle grid) = evaluate F shuffle grid
  | _, _, .nil, _ => Paths.lift_nil F _
  | _, _, .horizontal rest, grid => by
      exact ((Paths.lift F).map_comp grid.firstHorizontal.toPath
        (proposal rest grid.dropHorizontal)).trans
          (by rw [Paths.lift_toPath, evaluate_free_extension]; rfl)
  | _, _, .vertical rest, grid => by
      exact ((Paths.lift F).map_comp grid.firstVertical.toPath
        (proposal rest grid.dropVertical)).trans
          (by rw [Paths.lift_toPath, evaluate_free_extension]; rfl)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ExecutionGeometry.Rectangle
