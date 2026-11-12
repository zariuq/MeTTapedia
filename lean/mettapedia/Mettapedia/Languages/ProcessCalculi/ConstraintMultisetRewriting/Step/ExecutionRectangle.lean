import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.Combinatorics.Quiver.Subquiver

/-!
# Finite execution rectangles and their admitted shuffles

Vertices record remaining horizontal and vertical work. Each generator is a
specific quiver edge. Admission is checked in one fixed wide subquiver, without
choosing a scheduler or asserting that arbitrary diamonds are interchanges.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ExecutionGeometry

universe uV uE uW uF

inductive Shuffle : Nat → Nat → Type
  | nil : Shuffle 0 0
  | horizontal {width height : Nat} (rest : Shuffle width height) : Shuffle (width + 1) height
  | vertical {width height : Nat} (rest : Shuffle width height) : Shuffle width (height + 1)

namespace Shuffle

def verticals : (height : Nat) → Shuffle 0 height
  | 0 => .nil
  | height + 1 => .vertical (verticals height)

def horizontals : (width : Nat) → {height : Nat} → Shuffle 0 height → Shuffle width height
  | 0, _, rest => rest
  | width + 1, _, rest => .horizontal (horizontals width rest)

/-- An auxiliary witness for coverage arguments; execution accepts any shuffle. -/
def canonical (width height : Nat) : Shuffle width height := horizontals width (verticals height)

end Shuffle

structure Rectangle (V : Type uV) [Quiver.{uE} V] (width height : Nat) where
  vertex : Fin (width + 1) → Fin (height + 1) → V
  horizontal : (i : Fin width) → (j : Fin (height + 1)) → vertex i.succ j ⟶ vertex i.castSucc j
  vertical : (i : Fin (width + 1)) → (j : Fin height) → vertex i j.succ ⟶ vertex i j.castSucc

namespace Rectangle

variable {V : Type uV} [Quiver.{uE} V]

abbrev entry {width height : Nat} (grid : Rectangle V width height) : V :=
  grid.vertex (Fin.last width) (Fin.last height)

abbrev exit {width height : Nat} (grid : Rectangle V width height) : V :=
  grid.vertex ⟨0, Nat.zero_lt_succ width⟩ ⟨0, Nat.zero_lt_succ height⟩

abbrev dropHorizontal {width height : Nat} (grid : Rectangle V (width + 1) height) :
    Rectangle V width height where
  vertex i j := grid.vertex i.castSucc j
  horizontal i j := grid.horizontal i.castSucc j
  vertical i j := grid.vertical i.castSucc j

abbrev dropVertical {width height : Nat} (grid : Rectangle V width (height + 1)) :
    Rectangle V width height where
  vertex i j := grid.vertex i j.castSucc
  horizontal i j := grid.horizontal i j.castSucc
  vertical i j := grid.vertical i j.castSucc

abbrev firstHorizontal {width height : Nat} (grid : Rectangle V (width + 1) height) :
    grid.entry ⟶ grid.dropHorizontal.entry := grid.horizontal (Fin.last width) (Fin.last height)

abbrev firstVertical {width height : Nat} (grid : Rectangle V width (height + 1)) :
    grid.entry ⟶ grid.dropVertical.entry := grid.vertical (Fin.last width) (Fin.last height)

structure AllPermitted (permit : WideSubquiver V) {width height : Nat}
    (grid : Rectangle V width height) : Prop where
  horizontal : ∀ i j, grid.horizontal i j ∈ permit _ _
  vertical : ∀ i j, grid.vertical i j ∈ permit _ _

theorem AllPermitted.dropHorizontal {permit : WideSubquiver V} {width height : Nat}
    {grid : Rectangle V (width + 1) height} (all : AllPermitted permit grid) :
    AllPermitted permit grid.dropHorizontal :=
  ⟨fun i j => all.horizontal i.castSucc j, fun i j => all.vertical i.castSucc j⟩

theorem AllPermitted.dropVertical {permit : WideSubquiver V} {width height : Nat}
    {grid : Rectangle V width (height + 1)} (all : AllPermitted permit grid) :
    AllPermitted permit grid.dropVertical :=
  ⟨fun i j => all.horizontal i j.castSucc, fun i j => all.vertical i j.castSucc⟩

inductive Admitted (permit : WideSubquiver V) : {width height : Nat} →
    Rectangle V width height → Shuffle width height → Prop
  | nil (grid : Rectangle V 0 0) : Admitted permit grid .nil
  | horizontal {width height : Nat} {grid : Rectangle V (width + 1) height}
      {rest : Shuffle width height} (head : grid.firstHorizontal ∈ permit _ _)
      (tail : Admitted permit grid.dropHorizontal rest) : Admitted permit grid (.horizontal rest)
  | vertical {width height : Nat} {grid : Rectangle V width (height + 1)}
      {rest : Shuffle width height} (head : grid.firstVertical ∈ permit _ _)
      (tail : Admitted permit grid.dropVertical rest) : Admitted permit grid (.vertical rest)

theorem admitted_horizontal_iff {permit : WideSubquiver V} {width height : Nat}
    (grid : Rectangle V (width + 1) height) (rest : Shuffle width height) :
    Admitted permit grid (.horizontal rest) ↔
      grid.firstHorizontal ∈ permit _ _ ∧ Admitted permit grid.dropHorizontal rest := by
  constructor
  · intro admitted
    cases admitted with
    | horizontal head tail => exact ⟨head, tail⟩
  · exact fun ⟨head, tail⟩ => .horizontal head tail

theorem admitted_vertical_iff {permit : WideSubquiver V} {width height : Nat}
    (grid : Rectangle V width (height + 1)) (rest : Shuffle width height) :
    Admitted permit grid (.vertical rest) ↔
      grid.firstVertical ∈ permit _ _ ∧ Admitted permit grid.dropVertical rest := by
  constructor
  · intro admitted
    cases admitted with
    | vertical head tail => exact ⟨head, tail⟩
  · exact fun ⟨head, tail⟩ => .vertical head tail

theorem admitted_of_all {permit : WideSubquiver V} : ∀ {width height : Nat}
    (shuffle : Shuffle width height) (grid : Rectangle V width height),
    AllPermitted permit grid → Admitted permit grid shuffle
  | _, _, .nil, grid, _ => .nil grid
  | width + 1, height, .horizontal rest, grid, all =>
      .horizontal (all.horizontal (Fin.last width) (Fin.last height))
        (admitted_of_all rest grid.dropHorizontal all.dropHorizontal)
  | width, height + 1, .vertical rest, grid, all =>
      .vertical (all.vertical (Fin.last width) (Fin.last height))
        (admitted_of_all rest grid.dropVertical all.dropVertical)

variable (permit : WideSubquiver V) {W : Type uW} [Quiver.{uF} W]
  (objects : V → W)
  (generators : ∀ {source target : V} (edge : source ⟶ target),
    edge ∈ permit source target → (objects source ⟶ objects target))

def interpret : ∀ {width height : Nat} (shuffle : Shuffle width height)
    (grid : Rectangle V width height), Admitted permit grid shuffle →
      Quiver.Path (objects grid.entry) (objects grid.exit)
  | _, _, .nil, _, _ => .nil
  | _, _, .horizontal rest, grid, admitted =>
      let parts := (admitted_horizontal_iff grid rest).mp admitted
      (generators grid.firstHorizontal parts.1).toPath.comp
        (interpret rest grid.dropHorizontal parts.2)
  | _, _, .vertical rest, grid, admitted =>
      let parts := (admitted_vertical_iff grid rest).mp admitted
      (generators grid.firstVertical parts.1).toPath.comp
        (interpret rest grid.dropVertical parts.2)

theorem interpret_length : ∀ {width height : Nat} (shuffle : Shuffle width height)
    (grid : Rectangle V width height) (admitted : Admitted permit grid shuffle),
    (interpret permit objects generators shuffle grid admitted).length = width + height
  | _, _, .nil, _, _ => rfl
  | _, _, .horizontal rest, grid, admitted => by
      simp only [interpret, Quiver.Path.length_comp, Quiver.Hom.toPath,
        Quiver.Path.length_cons, Quiver.Path.length_nil]
      rw [interpret_length]
      omega
  | _, _, .vertical rest, grid, admitted => by
      simp only [interpret, Quiver.Path.length_comp, Quiver.Hom.toPath,
        Quiver.Path.length_cons, Quiver.Path.length_nil]
      rw [interpret_length]
      omega

end Rectangle
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ExecutionGeometry
