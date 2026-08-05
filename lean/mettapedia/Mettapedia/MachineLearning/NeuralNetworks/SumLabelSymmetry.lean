import Mathlib.Logic.Equiv.Set

/-!
# Exact automorphisms of a labeled sum

A permutation of `Left ⊕ Right` preserves the summand label exactly when it
factors into one permutation of `Left` and one permutation of `Right`.  The
factorization is constructed by restricting the original equivalence to the
ranges of `Sum.inl` and `Sum.inr`.

This supplies the layer-label component of exact weight-coordinate symmetry
classification.  It is independent of finiteness.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks

section SumLabels

/-- The two summands carry distinct labels. -/
inductive SumSide where
  | left
  | right
  deriving DecidableEq

/-- Label of a coordinate in a binary sum. -/
def sumSide {Left Right : Type*} : Left ⊕ Right → SumSide
  | Sum.inl _ => SumSide.left
  | Sum.inr _ => SumSide.right

/-- A coordinate permutation never moves an element between summands. -/
def PreservesSumSide
    {Left Right : Type*}
    (permutation : Equiv.Perm (Left ⊕ Right)) : Prop :=
  ∀ coordinate,
    sumSide (permutation coordinate) = sumSide coordinate

/-- A sum permutation is assembled independently from the two summands. -/
def IsSumPermutation
    {Left Right : Type*}
    (permutation : Equiv.Perm (Left ⊕ Right)) : Prop :=
  ∃ leftPermutation : Equiv.Perm Left,
    ∃ rightPermutation : Equiv.Perm Right,
      permutation =
        Equiv.sumCongr leftPermutation rightPermutation

lemma mem_range_inl_iff_sumSide_left
    {Left Right : Type*} (coordinate : Left ⊕ Right) :
    coordinate ∈ Set.range (Sum.inl : Left → Left ⊕ Right) ↔
      sumSide coordinate = SumSide.left := by
  rcases coordinate with left | right <;> simp [sumSide]

lemma mem_range_inr_iff_sumSide_right
    {Left Right : Type*} (coordinate : Left ⊕ Right) :
    coordinate ∈ Set.range (Sum.inr : Right → Left ⊕ Right) ↔
      sumSide coordinate = SumSide.right := by
  rcases coordinate with left | right <;> simp [sumSide]

/-- Restrict a side-preserving sum permutation to the two summands. -/
theorem preservesSumSide_implies_isSumPermutation
    {Left Right : Type*}
    (permutation : Equiv.Perm (Left ⊕ Right))
    (preserves : PreservesSumSide permutation) :
    IsSumPermutation permutation := by
  have preservesLeft (coordinate : Left ⊕ Right) :
      coordinate ∈ Set.range (Sum.inl : Left → Left ⊕ Right) ↔
        permutation coordinate ∈
          Set.range (Sum.inl : Left → Left ⊕ Right) := by
    rw [mem_range_inl_iff_sumSide_left,
      mem_range_inl_iff_sumSide_left, preserves coordinate]
  have preservesRight (coordinate : Left ⊕ Right) :
      coordinate ∈ Set.range (Sum.inr : Right → Left ⊕ Right) ↔
        permutation coordinate ∈
          Set.range (Sum.inr : Right → Left ⊕ Right) := by
    rw [mem_range_inr_iff_sumSide_right,
      mem_range_inr_iff_sumSide_right, preserves coordinate]
  let leftRestriction : Equiv.Perm Left :=
    (Equiv.Set.rangeInl Left Right).symm.trans
      ((permutation.subtypeEquiv preservesLeft).trans
        (Equiv.Set.rangeInl Left Right))
  let rightRestriction : Equiv.Perm Right :=
    (Equiv.Set.rangeInr Left Right).symm.trans
      ((permutation.subtypeEquiv preservesRight).trans
        (Equiv.Set.rangeInr Left Right))
  refine ⟨leftRestriction, rightRestriction, ?_⟩
  apply Equiv.ext
  intro coordinate
  rcases coordinate with left | right
  · have imageLeft :
        permutation (Sum.inl left) ∈
          Set.range (Sum.inl : Left → Left ⊕ Right) :=
      (preservesLeft (Sum.inl left)).1 (Set.mem_range_self left)
    obtain ⟨left', imageEq⟩ := imageLeft
    have extracted :
        (Equiv.Set.rangeInl Left Right)
            ⟨permutation (Sum.inl left),
              (preservesLeft (Sum.inl left)).1
                (Set.mem_range_self left)⟩ =
          left' := by
      have subtypeEq :
          (⟨permutation (Sum.inl left),
              (preservesLeft (Sum.inl left)).1
                (Set.mem_range_self left)⟩ :
              Set.range (Sum.inl : Left → Left ⊕ Right)) =
            ⟨Sum.inl left', Set.mem_range_self left'⟩ := by
        apply Subtype.ext
        exact imageEq.symm
      rw [subtypeEq]
      rfl
    change
      permutation (Sum.inl left) =
        Sum.inl (leftRestriction left)
    rw [show
      leftRestriction left =
          (Equiv.Set.rangeInl Left Right)
            ⟨permutation (Sum.inl left),
              (preservesLeft (Sum.inl left)).1
                (Set.mem_range_self left)⟩ by rfl]
    rw [extracted]
    exact imageEq.symm
  · have imageRight :
        permutation (Sum.inr right) ∈
          Set.range (Sum.inr : Right → Left ⊕ Right) :=
      (preservesRight (Sum.inr right)).1
        (Set.mem_range_self right)
    obtain ⟨right', imageEq⟩ := imageRight
    have extracted :
        (Equiv.Set.rangeInr Left Right)
            ⟨permutation (Sum.inr right),
              (preservesRight (Sum.inr right)).1
                (Set.mem_range_self right)⟩ =
          right' := by
      have subtypeEq :
          (⟨permutation (Sum.inr right),
              (preservesRight (Sum.inr right)).1
                (Set.mem_range_self right)⟩ :
              Set.range (Sum.inr : Right → Left ⊕ Right)) =
            ⟨Sum.inr right', Set.mem_range_self right'⟩ := by
        apply Subtype.ext
        exact imageEq.symm
      rw [subtypeEq]
      rfl
    change
      permutation (Sum.inr right) =
        Sum.inr (rightRestriction right)
    rw [show
      rightRestriction right =
          (Equiv.Set.rangeInr Left Right)
            ⟨permutation (Sum.inr right),
              (preservesRight (Sum.inr right)).1
                (Set.mem_range_self right)⟩ by rfl]
    rw [extracted]
    exact imageEq.symm

/-- Independent summand permutations preserve the summand label. -/
theorem isSumPermutation_implies_preservesSumSide
    {Left Right : Type*}
    (permutation : Equiv.Perm (Left ⊕ Right))
    (sumForm : IsSumPermutation permutation) :
    PreservesSumSide permutation := by
  rcases sumForm with
    ⟨leftPermutation, rightPermutation, rfl⟩
  intro coordinate
  rcases coordinate with left | right <;> rfl

/-- Exact layer-label boundary: preserving the side label is equivalent to a
layerwise sum permutation. -/
theorem preservesSumSide_iff_isSumPermutation
    {Left Right : Type*}
    (permutation : Equiv.Perm (Left ⊕ Right)) :
    PreservesSumSide permutation ↔
      IsSumPermutation permutation :=
  ⟨preservesSumSide_implies_isSumPermutation permutation,
    isSumPermutation_implies_preservesSumSide permutation⟩

namespace SumLabelFixtures

abbrev TinySum := Fin 2 ⊕ Fin 2

def layerwiseSwap : Equiv.Perm TinySum :=
  Equiv.sumCongr (Equiv.swap 0 1) (Equiv.swap 0 1)

def crossSideSwap : Equiv.Perm TinySum :=
  Equiv.swap (Sum.inl 0) (Sum.inr 0)

theorem layerwiseSwap_preserves_side :
    PreservesSumSide layerwiseSwap :=
  isSumPermutation_implies_preservesSumSide layerwiseSwap
    ⟨Equiv.swap 0 1, Equiv.swap 0 1, rfl⟩

theorem crossSideSwap_does_not_preserve_side :
    ¬ PreservesSumSide crossSideSwap := by
  intro preserves
  have changed := preserves (Sum.inl (0 : Fin 2))
  simp [crossSideSwap, sumSide] at changed

theorem crossSideSwap_is_not_sumPermutation :
    ¬ IsSumPermutation crossSideSwap := by
  intro sumForm
  exact crossSideSwap_does_not_preserve_side
    (isSumPermutation_implies_preservesSumSide
      crossSideSwap sumForm)

end SumLabelFixtures

#print axioms preservesSumSide_implies_isSumPermutation
#print axioms preservesSumSide_iff_isSumPermutation
#print axioms SumLabelFixtures.layerwiseSwap_preserves_side
#print axioms SumLabelFixtures.crossSideSwap_does_not_preserve_side
#print axioms SumLabelFixtures.crossSideSwap_is_not_sumPermutation

end SumLabels

end Mettapedia.MachineLearning.NeuralNetworks
