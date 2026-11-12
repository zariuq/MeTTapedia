import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ExecutionRectangleInterchange
import Mathlib.CategoryTheory.Types.Basic

/-!
# Complete observations can hide a failed local interchange

All three complete shuffles of a two-by-one rectangle have the same function
as their observation, yet one elementary square does not commute. The initial
constant function hides its suffix. Local-square reflection therefore cannot
be inferred from complete-boundary agreement without further hypotheses.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ExecutionRectangleInterchangeControls

open _root_.CategoryTheory ExecutionGeometry

inductive Vertex where
  | point

instance : Quiver Vertex where
  Hom _ _ := Bool → Bool

def interpretation : Vertex ⥤q Type where
  obj _ := Bool
  map function := ↾function

def freeze (_ : Bool) : Bool := false

def grid : Rectangle Vertex 2 1 where
  vertex _ _ := .point
  horizontal _ j := if j.val = 1 then freeze else id
  vertical i _ := if i.val = 2 then freeze else id

theorem every_boundary_is_frozen (shuffle : Shuffle 2 1) :
    Rectangle.evaluate interpretation shuffle grid = ↾freeze := by
  cases shuffle with
  | horizontal rest =>
      cases rest with
      | horizontal rest =>
          cases rest with
          | vertical rest => cases rest; rfl
      | vertical rest =>
          cases rest with
          | horizontal rest => cases rest; rfl
  | vertical rest =>
      cases rest with
      | horizontal rest =>
          cases rest with
          | horizontal rest => cases rest; rfl

theorem complete_interleavings_agree (first second : Shuffle 2 1) :
    Rectangle.evaluate interpretation first grid = Rectangle.evaluate interpretation second grid :=
  (every_boundary_is_frozen first).trans (every_boundary_is_frozen second).symm

theorem local_interchange_fails : ¬Rectangle.Commutes interpretation grid := by
  intro commutes
  have corner := commutes ⟨0, by decide⟩ ⟨0, by decide⟩
  have wrong := congrArg (fun function : Bool ⟶ Bool => function true) corner
  change false = true at wrong
  cases wrong

theorem boundary_agreement_does_not_reflect_local_squares :
    (∀ first second : Shuffle 2 1,
      Rectangle.evaluate interpretation first grid = Rectangle.evaluate interpretation second grid) ∧
      ¬Rectangle.Commutes interpretation grid :=
  ⟨complete_interleavings_agree, local_interchange_fails⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ExecutionRectangleInterchangeControls
