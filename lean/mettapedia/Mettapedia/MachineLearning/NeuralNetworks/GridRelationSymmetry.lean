import Mettapedia.MachineLearning.NeuralNetworks.EquivariantLinearKernel

/-!
# Exact automorphisms of a rectangular coordinate grid

A permutation of a product type is induced by one permutation of the rows and
one permutation of the columns exactly when it preserves and reflects both
same-row and same-column incidence.  The proof is constructive once one row
and one column are supplied: read the two component maps at those anchors,
then recover bijectivity from the original grid permutation.

This is the finite-coordinate combinatorial core needed to distinguish neuron
permutations from arbitrary entrywise permutations of a weight matrix.  The
theorem itself does not require finiteness.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks

section GridRelations

variable {Row Column : Type*}

/-- A coordinate equivalence preserves and reflects a binary relation. -/
def EquivPreservesRelation
    {Coordinate : Type*}
    (permutation : Equiv.Perm Coordinate)
    (relation : Coordinate → Coordinate → Prop) : Prop :=
  ∀ left right,
    relation (permutation left) (permutation right) ↔ relation left right

/-- Same-row incidence on a rectangular grid. -/
def SameFirst (left right : Row × Column) : Prop :=
  left.1 = right.1

/-- Same-column incidence on a rectangular grid. -/
def SameSecond (left right : Row × Column) : Prop :=
  left.2 = right.2

instance sameFirstDecidableRel [DecidableEq Row] :
    DecidableRel (SameFirst (Row := Row) (Column := Column)) := by
  intro left right
  exact decEq left.1 right.1

instance sameSecondDecidableRel [DecidableEq Column] :
    DecidableRel (SameSecond (Row := Row) (Column := Column)) := by
  intro left right
  exact decEq left.2 right.2

/-- A product permutation acts by one row permutation and one column
permutation, independently of the opposite coordinate. -/
def IsProductPermutation
    (permutation : Equiv.Perm (Row × Column)) : Prop :=
  ∃ rowPermutation : Equiv.Perm Row,
    ∃ columnPermutation : Equiv.Perm Column,
      ∀ row column,
        permutation (row, column) =
          (rowPermutation row, columnPermutation column)

/-- Reading a relation-preserving grid permutation along one row and one
column reconstructs independent row and column permutations. -/
theorem preservesGridRelations_implies_isProductPermutation
    (rowAnchor : Row) (columnAnchor : Column)
    (permutation : Equiv.Perm (Row × Column))
    (preservesRows :
      EquivPreservesRelation permutation SameFirst)
    (preservesColumns :
      EquivPreservesRelation permutation SameSecond) :
    IsProductPermutation permutation := by
  let rowMap : Row → Row :=
    fun row => (permutation (row, columnAnchor)).1
  let columnMap : Column → Column :=
    fun column => (permutation (rowAnchor, column)).2
  have firstComponent (row : Row) (column : Column) :
      (permutation (row, column)).1 = rowMap row := by
    exact
      (preservesRows (row, column) (row, columnAnchor)).2 rfl
  have secondComponent (row : Row) (column : Column) :
      (permutation (row, column)).2 = columnMap column := by
    exact
      (preservesColumns (row, column) (rowAnchor, column)).2 rfl
  have rowInjective : Function.Injective rowMap := by
    intro left right firstEqual
    have secondEqual :
        (permutation (left, columnAnchor)).2 =
          (permutation (right, columnAnchor)).2 :=
      (preservesColumns
        (left, columnAnchor) (right, columnAnchor)).2 rfl
    have imageEqual :
        permutation (left, columnAnchor) =
          permutation (right, columnAnchor) :=
      Prod.ext firstEqual secondEqual
    exact congrArg Prod.fst (permutation.injective imageEqual)
  have rowSurjective : Function.Surjective rowMap := by
    intro target
    let preimage := permutation.symm (target, columnAnchor)
    refine ⟨preimage.1, ?_⟩
    calc
      rowMap preimage.1 =
          (permutation (preimage.1, preimage.2)).1 :=
        (firstComponent preimage.1 preimage.2).symm
      _ = target := by simp [preimage]
  have columnInjective : Function.Injective columnMap := by
    intro left right secondEqual
    have firstEqual :
        (permutation (rowAnchor, left)).1 =
          (permutation (rowAnchor, right)).1 :=
      (preservesRows (rowAnchor, left) (rowAnchor, right)).2 rfl
    have imageEqual :
        permutation (rowAnchor, left) =
          permutation (rowAnchor, right) :=
      Prod.ext firstEqual secondEqual
    exact congrArg Prod.snd (permutation.injective imageEqual)
  have columnSurjective : Function.Surjective columnMap := by
    intro target
    let preimage := permutation.symm (rowAnchor, target)
    refine ⟨preimage.2, ?_⟩
    calc
      columnMap preimage.2 =
          (permutation (preimage.1, preimage.2)).2 :=
        (secondComponent preimage.1 preimage.2).symm
      _ = target := by simp [preimage]
  let rowPermutation : Equiv.Perm Row :=
    Equiv.ofBijective rowMap ⟨rowInjective, rowSurjective⟩
  let columnPermutation : Equiv.Perm Column :=
    Equiv.ofBijective columnMap
      ⟨columnInjective, columnSurjective⟩
  refine ⟨rowPermutation, columnPermutation, ?_⟩
  intro row column
  apply Prod.ext
  · exact firstComponent row column
  · exact secondComponent row column

/-- Independent row and column permutations preserve both grid relations. -/
theorem isProductPermutation_implies_preservesGridRelations
    (permutation : Equiv.Perm (Row × Column))
    (productForm : IsProductPermutation permutation) :
    EquivPreservesRelation permutation SameFirst ∧
      EquivPreservesRelation permutation SameSecond := by
  rcases productForm with
    ⟨rowPermutation, columnPermutation, productForm⟩
  constructor
  · intro left right
    rcases left with ⟨leftRow, leftColumn⟩
    rcases right with ⟨rightRow, rightColumn⟩
    rw [productForm, productForm]
    simp [SameFirst]
  · intro left right
    rcases left with ⟨leftRow, leftColumn⟩
    rcases right with ⟨rightRow, rightColumn⟩
    rw [productForm, productForm]
    simp [SameSecond]

/-- Exact grid-automorphism boundary: preserving both incidence relations is
equivalent to factoring into a row permutation and a column permutation. -/
theorem preservesGridRelations_iff_isProductPermutation
    (rowAnchor : Row) (columnAnchor : Column)
    (permutation : Equiv.Perm (Row × Column)) :
    (EquivPreservesRelation permutation SameFirst ∧
        EquivPreservesRelation permutation SameSecond) ↔
      IsProductPermutation permutation := by
  constructor
  · intro preserves
    exact
      preservesGridRelations_implies_isProductPermutation
        rowAnchor columnAnchor permutation preserves.1 preserves.2
  · exact
      isProductPermutation_implies_preservesGridRelations permutation

namespace GridRelationFixtures

abbrev TinyGrid := Fin 2 × Fin 2

/-- A genuine simultaneous row/column relabeling. -/
def productSwap : Equiv.Perm TinyGrid :=
  Equiv.prodCongr (Equiv.swap 0 1) (Equiv.swap 0 1)

/-- A single-entry exchange whose induced row permutation depends on the
column. -/
def partialRowSwap : Equiv.Perm TinyGrid :=
  Equiv.swap (0, 0) (1, 0)

theorem productSwap_preserves_grid :
    EquivPreservesRelation productSwap SameFirst ∧
      EquivPreservesRelation productSwap SameSecond :=
  isProductPermutation_implies_preservesGridRelations productSwap
    ⟨Equiv.swap 0 1, Equiv.swap 0 1, by
      intro row column
      rfl⟩

/-- The row relation detects a coordinate permutation that is not a product
of one row and one column permutation. -/
theorem partialRowSwap_does_not_preserve_rows :
    ¬ EquivPreservesRelation partialRowSwap SameFirst := by
  intro preserves
  have original :
      SameFirst ((0, 0) : TinyGrid) (0, 1) := by
    rfl
  have transported :=
    (preserves ((0, 0) : TinyGrid) (0, 1)).2 original
  norm_num
    [SameFirst, partialRowSwap, Equiv.swap_apply_def] at transported

/-- Consequently the partial exchange has no independent row/column
factorization. -/
theorem partialRowSwap_is_not_productPermutation :
    ¬ IsProductPermutation partialRowSwap := by
  intro productForm
  exact partialRowSwap_does_not_preserve_rows
    (isProductPermutation_implies_preservesGridRelations
      partialRowSwap productForm).1

end GridRelationFixtures

#print axioms preservesGridRelations_implies_isProductPermutation
#print axioms preservesGridRelations_iff_isProductPermutation
#print axioms GridRelationFixtures.productSwap_preserves_grid
#print axioms GridRelationFixtures.partialRowSwap_does_not_preserve_rows
#print axioms GridRelationFixtures.partialRowSwap_is_not_productPermutation

end GridRelations

end Mettapedia.MachineLearning.NeuralNetworks
