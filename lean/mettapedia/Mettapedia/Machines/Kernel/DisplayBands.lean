import Mathlib.Data.Nat.Basic

/-!
# Reusing a Display run across a band

The selected layer can change only at a clipped rectangle edge. Vertical
edges determine the band. Only layers covering that band contribute
horizontal edges. This theory treats layer selection and leaves pixel
shading and scanout to the native compositor.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.DisplayBands

structure Rect where
  left : Nat
  right : Nat
  top : Nat
  bottom : Nat
  deriving DecidableEq, Repr

structure Layer (Name : Type) where
  name : Name
  bounds : Rect
  deriving DecidableEq, Repr

def nextEdge (start limit : Nat) : List Nat → Nat
  | [] => limit
  | edge :: rest =>
      let next := nextEdge start limit rest
      if start < edge then min edge next else next

theorem nextEdge_progress (start limit : Nat) (edges : List Nat) (room : start < limit) :
    start < nextEdge start limit edges := by
  induction edges with
  | nil => exact room
  | cons edge rest ih =>
      by_cases ahead : start < edge
      · simpa [nextEdge, ahead] using lt_min ahead ih
      · simpa [nextEdge, ahead] using ih

theorem nextEdge_before_member (start limit edge : Nat) (edges : List Nat)
    (member : edge ∈ edges) (ahead : start < edge) : nextEdge start limit edges ≤ edge := by
  induction edges with
  | nil => simp at member
  | cons head rest ih =>
      rcases List.mem_cons.mp member with same | later
      · subst head
        simpa [nextEdge, ahead] using (min_le_left edge (nextEdge start limit rest))
      · by_cases headAhead : start < head
        · simpa [nextEdge, headAhead] using
            Nat.le_trans (min_le_right head (nextEdge start limit rest)) (ih later)
        · simpa [nextEdge, headAhead] using ih later

private theorem sameInterval {left right start stop point : Nat}
    (lower : start ≤ point) (upper : point < stop)
    (leftEdge : start < left → stop ≤ left)
    (rightEdge : start < right → stop ≤ right) :
    (left ≤ start ∧ start < right) ↔ (left ≤ point ∧ point < right) := by
  constructor
  · intro h
    have bound := rightEdge h.2
    omega
  · intro h
    constructor
    · apply Nat.le_of_not_gt
      intro late
      have bound := leftEdge late
      omega
    · omega

def Rect.covers (r : Rect) (x y : Nat) : Bool :=
  decide (r.left ≤ x ∧ x < r.right) && decide (r.top ≤ y ∧ y < r.bottom)

variable {Name : Type}

def verticalEdges (layers : List (Layer Name)) : List Nat :=
  layers.flatMap fun l => [l.bounds.top, l.bounds.bottom]

def horizontalEdges (layers : List (Layer Name)) (y : Nat) : List Nat :=
  layers.flatMap fun l => if l.bounds.top ≤ y ∧ y < l.bounds.bottom
    then [l.bounds.left, l.bounds.right] else []

def winner (layers : List (Layer Name)) (eligible : Layer Name → Bool) (x y : Nat) :
    Option (Layer Name) :=
  layers.find? fun l => eligible l && l.bounds.covers x y

private theorem find_same {α : Type} {layers : List α} {a b : α → Bool}
    (same : ∀ l ∈ layers, a l = b l) : layers.find? a = layers.find? b := by
  induction layers with
  | nil => rfl
  | cons l rest ih =>
      rw [List.find?_cons, List.find?_cons, same l (by simp)]
      rw [ih (fun item member => same item (List.mem_cons_of_mem _ member))]

theorem winner_constant (layers : List (Layer Name)) (eligible : Layer Name → Bool)
    {x₀ y₀ x y width height : Nat}
    (xLo : x₀ ≤ x) (xHi : x < nextEdge x₀ width (horizontalEdges layers y₀))
    (yLo : y₀ ≤ y) (yHi : y < nextEdge y₀ height (verticalEdges layers)) :
    winner layers eligible x₀ y₀ = winner layers eligible x y := by
  apply find_same
  intro l present
  have yMember : ∀ e ∈ [l.bounds.top, l.bounds.bottom], e ∈ verticalEdges layers := by
    intro e member
    exact List.mem_flatMap.mpr ⟨l, present, member⟩
  have ySame := sameInterval yLo yHi
    (nextEdge_before_member _ _ _ _ (yMember l.bounds.top (by simp)))
    (nextEdge_before_member _ _ _ _ (yMember l.bounds.bottom (by simp)))
  by_cases vertical : l.bounds.top ≤ y₀ ∧ y₀ < l.bounds.bottom
  · have xMember : ∀ e ∈ [l.bounds.left, l.bounds.right], e ∈ horizontalEdges layers y₀ := by
      intro e member
      exact List.mem_flatMap.mpr ⟨l, present, by simpa [vertical] using member⟩
    have xSame := sameInterval xLo xHi
      (nextEdge_before_member _ _ _ _ (xMember l.bounds.left (by simp)))
      (nextEdge_before_member _ _ _ _ (xMember l.bounds.right (by simp)))
    simp [Rect.covers, xSame, vertical, ySame.mp vertical]
  · have elsewhere : ¬ (l.bounds.top ≤ y ∧ y < l.bounds.bottom) :=
      fun h => vertical (ySame.mpr h)
    simp [Rect.covers, vertical, elsewhere]

example : nextEdge 5 100 [9, 0, 5, 20, 7] = 7 := by decide
example :
    let scene : List (Layer Nat) := [⟨1, ⟨2, 6, 4, 12⟩⟩, ⟨2, ⟨0, 8, 0, 16⟩⟩]
    (winner scene (fun _ => true) 3 7).map Layer.name = some 1 ∧
    (winner scene (fun _ => true) 6 7).map Layer.name = some 2 := by decide

#print axioms nextEdge_progress
#print axioms winner_constant

end Mettapedia.Machines.Kernel.DisplayBands
