import Mettapedia.TypeTheory.ContextualWReindexing
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWSignature

/-!
# Signature equivalences commute with contextual tree reindexing

The comparison retains complete future branches. Equality transports of
the independently formed source and target signatures are explicit.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualWSignatureReindexing

open CategoryTheory MaterialSets.Hypersets
open ContextualWReindexing
open ContextualWTypes (RawTree)

universe u
variable {D E : Type u} [Category.{u} D] [Category.{u} E]

abbrev Comparison (first second : Signature D) :=
  ContextualWSignature.Signature (shape := first.1) (nextShape := second.1)
    (position := first.2) (nextPosition := second.2)

def underComparison (change : D ⥤ E) {first second : Signature E}
    (comparison : Comparison first second) : Comparison (under change first) (under change second) where
  shapes point := comparison.shapes (change.obj point)
  shape_natural step label := comparison.shape_natural (change.map step) label
  positions point label := comparison.positions (change.obj point) label
  position_natural step label branch := comparison.position_natural (change.map step) label branch

theorem comparison_heq {first second otherFirst otherSecond : Signature D}
    (source : first = otherFirst) (target : second = otherSecond)
    (left : Comparison first second) (right : Comparison otherFirst otherSecond)
    (shapes : ∀ point, HEq (left.shapes point) (right.shapes point))
    (positions : ∀ point (firstLabel : first.1.obj point) (secondLabel : otherFirst.1.obj point),
      HEq firstLabel secondLabel → HEq (left.positions point firstLabel) (right.positions point secondLabel)) :
    HEq left right := by
  cases source
  cases target
  have labels : left.shapes = right.shapes := funext fun point => eq_of_heq (shapes point)
  rcases left with ⟨leftShapes, leftNatural, leftPositions, leftPositionNatural⟩
  rcases right with ⟨rightShapes, rightNatural, rightPositions, rightPositionNatural⟩
  dsimp only at labels
  cases labels
  have branches : leftPositions = rightPositions := by
    funext point label
    exact eq_of_heq (positions point label label HEq.rfl)
  cases branches
  rfl

theorem mapRaw_heq {first second otherFirst otherSecond : Signature D}
    (source : first = otherFirst) (target : second = otherSecond)
    (left : Comparison first second) (right : Comparison otherFirst otherSecond) (same : HEq left right)
    {point : D} (leftTree : Raw first point) (rightTree : Raw otherFirst point) (trees : HEq leftTree rightTree) :
    HEq (ContextualWSignature.mapRaw left leftTree) (ContextualWSignature.mapRaw right rightTree) := by
  cases source
  cases target
  cases eq_of_heq same
  cases eq_of_heq trees
  rfl

theorem map_pull_data (change : D ⥤ E) {first second : Signature E}
    (comparison : Comparison first second) {target : E} (tree : Raw first target) :
    ∀ point : D, ∀ same : change.obj point = target,
      ContextualWSignature.mapRaw (underComparison change comparison) (pullData change first tree point same) =
        pullData change second (ContextualWSignature.mapRaw comparison tree) point same := by
  induction tree with
  | @sup target label children earlier =>
    intro point same
    cases same
    apply RawTree.sup_eq_of_cast rfl
    intro next arrow branch
    exact earlier _ _ _ next rfl

theorem map_pull (change : D ⥤ E) {first second : Signature E}
    (comparison : Comparison first second) (point : D) (tree : Raw first (change.obj point)) :
    ContextualWSignature.mapRaw (underComparison change comparison) (pull change first point tree) =
      pull change second point (ContextualWSignature.mapRaw comparison tree) :=
  map_pull_data change comparison tree point rfl

end Mettapedia.TypeTheory.ContextualWSignatureReindexing
