import Mathlib.Tactic

/-!
# Globular sets and levelwise thinness

A globular set is the raw boundary shape underlying globular higher-category
theories: cells in every natural dimension, source and target maps, and the
two globular identities.  It does not by itself supply identities,
composition, inverses, fillers, or coherence laws.

This module isolates a small but important independence result.  Uniqueness
of parallel cells at one dimension does not force uniqueness at the next
dimension.  The concrete canary has one cell in dimensions zero through two
and two cells from dimension three onward.  Consequently its parallel
two-cell fibres are subsingletons while one parallel three-cell fibre contains
two distinct elements.

Thus local thinness of a selected 2-cell semantics is a levelwise property,
not a proof that all possible higher structure is truncated.  Any stronger
conclusion needs an explicit truncation hypothesis or a model of the intended
higher categorical structure.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.Higher

universe u v

/-- A globular set: dimension-indexed cells with source and target satisfying
the globular boundary equations. -/
structure GlobularSet where
  Cell : Nat → Type u
  source : (dimension : Nat) → Cell (dimension + 1) → Cell dimension
  target : (dimension : Nat) → Cell (dimension + 1) → Cell dimension
  source_source : ∀ dimension (cell : Cell (dimension + 2)),
    source dimension (source (dimension + 1) cell) =
      source dimension (target (dimension + 1) cell)
  target_source : ∀ dimension (cell : Cell (dimension + 2)),
    target dimension (source (dimension + 1) cell) =
      target dimension (target (dimension + 1) cell)

namespace GlobularSet

/-- Cells one dimension above `sourceCell` and `targetCell` with exactly that
globular boundary. -/
def BoundaryFiber (tower : GlobularSet.{u}) (dimension : Nat)
    (sourceCell targetCell : tower.Cell dimension) : Type u :=
  { cell : tower.Cell (dimension + 1) //
      tower.source dimension cell = sourceCell ∧
      tower.target dimension cell = targetCell }

/-- All parallel cells immediately above `dimension` are unique.  For
`dimension = 1`, this is ordinary local thinness of 2-cells. -/
def LocallyThinAt (tower : GlobularSet.{u}) (dimension : Nat) : Prop :=
  ∀ sourceCell targetCell,
    Subsingleton (tower.BoundaryFiber dimension sourceCell targetCell)

/-- A specified dimension has genuinely distinct parallel cells above it. -/
def HasDistinctParallelAt (tower : GlobularSet.{u})
    (dimension : Nat) : Prop :=
  ∃ sourceCell targetCell,
    ∃ first second : tower.BoundaryFiber dimension sourceCell targetCell,
      first ≠ second

/-- A displayed family over cells at one dimension contains genuinely
distinct data over a common base cell.  This is deliberately separate from
having distinct cells in the globular base. -/
def HasDistinctDisplayedAt (tower : GlobularSet.{u}) (dimension : Nat)
    (Displayed : tower.Cell dimension → Type v) : Prop :=
  ∃ base, ∃ first second : Displayed base, first ≠ second

/-- Distinct parallel cells refute local thinness at their dimension. -/
theorem not_locallyThinAt_of_hasDistinctParallelAt
    (tower : GlobularSet.{u}) (dimension : Nat)
    (distinct : tower.HasDistinctParallelAt dimension) :
    ¬ tower.LocallyThinAt dimension := by
  rintro thin
  obtain ⟨sourceCell, targetCell, first, second, different⟩ := distinct
  exact different ((thin sourceCell targetCell).allEq first second)

end GlobularSet

/-! ## A tower thin at 2-cells and thick at 3-cells -/

namespace ThinTwoThickThree

/-- Boolean labels constrained to `false` through dimension two.  From
dimension three onward the constraint is vacuous and both labels occur. -/
def Cell (dimension : Nat) : Type :=
  { label : Bool // dimension ≤ 2 → label = false }

/-- The common source/target boundary map.  At low dimensions it returns the
unique label; from dimension three onward it retains the label. -/
def boundary (dimension : Nat) : Cell (dimension + 1) → Cell dimension :=
  fun cell =>
    if low : dimension ≤ 2 then
      ⟨false, fun _ => rfl⟩
    else
      ⟨cell.1, fun atMostTwo => (low atMostTwo).elim⟩

/-- A globular tower whose source and target maps coincide.  The globular
identities are therefore definitional. -/
def tower : GlobularSet where
  Cell := Cell
  source := boundary
  target := boundary
  source_source := by
    intro _dimension _cell
    rfl
  target_source := by
    intro _dimension _cell
    rfl

/-- Through dimension two the label constraint leaves exactly one cell. -/
theorem cell_subsingleton_of_le_two (dimension : Nat)
    (low : dimension ≤ 2) : Subsingleton (Cell dimension) where
  allEq := by
    intro first second
    apply Subtype.ext
    exact (first.2 low).trans (second.2 low).symm

/-- Parallel 2-cells are unique. -/
theorem locallyThinAt_twoCells : tower.LocallyThinAt 1 := by
  intro sourceCell targetCell
  constructor
  intro first second
  apply Subtype.ext
  exact (cell_subsingleton_of_le_two 2 (by omega)).allEq first.1 second.1

def twoCell : Cell 2 :=
  ⟨false, fun _ => rfl⟩

def falseThreeCell : Cell 3 :=
  ⟨false, fun impossible => by omega⟩

def trueThreeCell : Cell 3 :=
  ⟨true, fun impossible => by omega⟩

def falseThreeCellInFiber : tower.BoundaryFiber 2 twoCell twoCell := by
  refine ⟨falseThreeCell, ?_⟩
  simp [tower, boundary, twoCell]

def trueThreeCellInFiber : tower.BoundaryFiber 2 twoCell twoCell := by
  refine ⟨trueThreeCell, ?_⟩
  simp [tower, boundary, twoCell]

/-- A proof-history family displayed over the unique 2-cell.  Its two
inhabitants model distinct receipts or derivations without turning those
receipts into additional mode 2-cells. -/
def ProofHistory (_cell : Cell 2) : Type := Bool

theorem proofHistory_hasDistinctDisplayedAt :
    tower.HasDistinctDisplayedAt 2 ProofHistory :=
  ⟨twoCell, false, true, Bool.false_ne_true⟩

theorem threeCells_distinct :
    falseThreeCellInFiber ≠ trueThreeCellInFiber := by
  intro equalCells
  have equalLabels := congrArg (fun cell => cell.1.1) equalCells
  exact Bool.false_ne_true equalLabels

/-- There are two distinct parallel 3-cells over the unique 2-cell boundary. -/
theorem hasDistinctParallelAt_threeCells :
    tower.HasDistinctParallelAt 2 :=
  ⟨twoCell, twoCell, falseThreeCellInFiber, trueThreeCellInFiber,
    threeCells_distinct⟩

theorem not_locallyThinAt_threeCells : ¬ tower.LocallyThinAt 2 :=
  tower.not_locallyThinAt_of_hasDistinctParallelAt 2
    hasDistinctParallelAt_threeCells

/-- Every dimension is inhabited, even though the tower changes from thin to
thick between dimensions two and three. -/
theorem cell_nonempty (dimension : Nat) : Nonempty (Cell dimension) :=
  ⟨⟨false, fun _ => rfl⟩⟩

end ThinTwoThickThree

/-! ## Independence theorem -/

/-- Local thinness of 2-cells alone does not imply local thinness of 3-cells. -/
theorem twoCellThinness_does_not_imply_threeCellThinness :
    ¬ ∀ tower : GlobularSet.{0},
      tower.LocallyThinAt 1 → tower.LocallyThinAt 2 := by
  intro implication
  exact ThinTwoThickThree.not_locallyThinAt_threeCells
    (implication ThinTwoThickThree.tower
      ThinTwoThickThree.locallyThinAt_twoCells)

/-- Local thinness of mode 2-cells is compatible with proof-relevant data
displayed over those cells.  The base comparison and its carried history are
different layers of structure. -/
theorem twoCellThinness_coexists_with_displayedProofRelevance :
    ∃ (tower : GlobularSet.{0}) (Displayed : tower.Cell 2 → Type),
      tower.LocallyThinAt 1 ∧ tower.HasDistinctDisplayedAt 2 Displayed := by
  exact ⟨ThinTwoThickThree.tower, ThinTwoThickThree.ProofHistory,
    ThinTwoThickThree.locallyThinAt_twoCells,
    ThinTwoThickThree.proofHistory_hasDistinctDisplayedAt⟩

/-- All three phenomena can coexist: unique parallel mode 2-cells, multiple
displayed proof histories over the selected 2-cell, and multiple parallel
3-cells.  No one of these axes should be inferred from either of the others. -/
theorem localThinness_displayedProofRelevance_and_higherThickness_coexist :
    ∃ (tower : GlobularSet.{0}) (Displayed : tower.Cell 2 → Type),
      tower.LocallyThinAt 1 ∧
        tower.HasDistinctDisplayedAt 2 Displayed ∧
        tower.HasDistinctParallelAt 2 := by
  exact ⟨ThinTwoThickThree.tower, ThinTwoThickThree.ProofHistory,
    ThinTwoThickThree.locallyThinAt_twoCells,
    ThinTwoThickThree.proofHistory_hasDistinctDisplayedAt,
    ThinTwoThickThree.hasDistinctParallelAt_threeCells⟩

/-! ## Axiom audit -/

#print axioms GlobularSet.not_locallyThinAt_of_hasDistinctParallelAt
#print axioms ThinTwoThickThree.locallyThinAt_twoCells
#print axioms ThinTwoThickThree.hasDistinctParallelAt_threeCells
#print axioms ThinTwoThickThree.proofHistory_hasDistinctDisplayedAt
#print axioms ThinTwoThickThree.not_locallyThinAt_threeCells
#print axioms twoCellThinness_does_not_imply_threeCellThinness
#print axioms twoCellThinness_coexists_with_displayedProofRelevance
#print axioms localThinness_displayedProofRelevance_and_higherThickness_coexist

end Mettapedia.CategoryTheory.Higher
