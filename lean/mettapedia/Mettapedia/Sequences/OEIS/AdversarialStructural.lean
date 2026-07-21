import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Multiset.FinsetOps
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic
import Mettapedia.Sequences.OEIS.Constructions
import Mettapedia.Sequences.OEIS.Elementary49

/-!
# Structural specifications from the weak-evidence cohort

These five entries require finite extremal objects or an asserted finite
classification.  The definitions below expose the actual proof obligations:
existence and optimality are not replaced by precomputed numerals.
-/

namespace Mettapedia.Sequences.OEIS.AdversarialStructural

open scoped BigOperators
open Mettapedia.Sequences.OEIS.Constructions
open Mettapedia.Sequences.OEIS.Elementary49

/-- A natural number is triangular when it is `t*(t+1)/2`; the doubled form
avoids any division convention. -/
def Triangular (value : Nat) : Prop :=
  ∃ t : Nat, 2 * value = t * (t + 1)

namespace A180928

def source := sourceOf "A180928" "da69082a2666308dfa3de3c8c0feb2ffdd15c13c7ce1e0cfb20d5538ba0327ec" 1
def publishedValues : List Nat := [0, 1, 5, 27]
def spec := finiteNatSpec 1 publishedValues
def formalization := formalizationOf source spec

/-- The pairwise property asserted for the finite list. -/
def PairwiseTriangular (values : List Nat) : Prop :=
  ∀ first ∈ values, ∀ second ∈ values,
    first ≠ second → Triangular (1 + first * second)

theorem published_pairwise_triangular : PairwiseTriangular publishedValues := by
  have one : Triangular 1 := ⟨1, by norm_num⟩
  have six : Triangular 6 := ⟨3, by norm_num⟩
  have twentyEight : Triangular 28 := ⟨7, by norm_num⟩
  have oneThirtySix : Triangular 136 := ⟨16, by norm_num⟩
  simp only [PairwiseTriangular]
  intro first firstMem second secondMem different
  simp [publishedValues] at firstMem secondMem
  rcases firstMem with rfl | rfl | rfl | rfl <;>
    rcases secondMem with rfl | rfl | rfl | rfl
  all_goals first | exact (different rfl).elim | simpa using one |
    simpa using six | simpa using twentyEight | simpa using oneThirtySix

/-- An additional integer would extend the nonzero triple if all three new
products also gave triangular numbers.  The source's maximality claim is this
predicate's nonexistence, not a definitional shortcut. -/
def ExtendsNonzeroTriple (candidate : Nat) : Prop :=
  candidate ∉ ({1, 5, 27} : Finset Nat) ∧
    Triangular (1 + candidate) ∧
    Triangular (1 + 5 * candidate) ∧
    Triangular (1 + 27 * candidate)

end A180928

namespace A294369

def source := sourceOf "A294369" "ef998367503439765f158f10b115f7a7c24a783d73c3444095ae9dbc12fecd2e" 1
def publishedValues : List Nat := [0, 1, 2, 4, 8, 10]
def spec := finiteNatSpec 1 publishedValues
def formalization := formalizationOf source spec
def Qualifies (index : Nat) : Prop := Triangular (Nat.fib index)

theorem published_values_qualify : ∀ index ∈ publishedValues, Qualifies index := by
  have zero : Qualifies 0 := ⟨0, by norm_num [Qualifies, Triangular, Nat.fib]⟩
  have one : Qualifies 1 := ⟨1, by norm_num [Qualifies, Triangular, Nat.fib]⟩
  have two : Qualifies 2 := ⟨1, by norm_num [Qualifies, Triangular, Nat.fib]⟩
  have four : Qualifies 4 := ⟨2, by norm_num [Qualifies, Triangular, Nat.fib]⟩
  have eight : Qualifies 8 := ⟨6, by norm_num [Qualifies, Triangular, Nat.fib]⟩
  have ten : Qualifies 10 := ⟨10, by norm_num [Qualifies, Triangular, Nat.fib]⟩
  intro index membership
  simp [publishedValues] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
  · exact zero
  · exact one
  · exact two
  · exact four
  · exact eight
  · exact ten

end A294369

namespace A125620

def source := sourceOf "A125620" "5948b5fdacba47d23f8bfb2697870881bb2b7d200b28787fba81d8a35fd49b96" 2

/-- A family of blocks splits every three-element subset when one block meets
each such subset in exactly one point. -/
def IsSplittingSystem {groundSize : Nat}
    (blocks : Finset (Finset (Fin groundSize))) : Prop :=
  ∀ triple : Finset (Fin groundSize), triple.card = 3 →
    ∃ block ∈ blocks, (block ∩ triple).card = 1

def ExistsWithExactly (blockCount groundSize : Nat) : Prop :=
  ∃ blocks : Finset (Finset (Fin groundSize)),
    blocks.card = blockCount ∧ IsSplittingSystem blocks

def IsMaximumGroundSize (blockCount groundSize : Nat) : Prop :=
  ExistsWithExactly blockCount groundSize ∧
    ∀ other, ExistsWithExactly blockCount other → other ≤ groundSize

noncomputable def maximumGroundSize (blockCount : Nat) : Nat :=
  by
    classical
    exact if existsMaximum : ∃ groundSize, IsMaximumGroundSize blockCount groundSize then
      Classical.choose existsMaximum
    else 0

theorem maximumGroundSize_spec {blockCount : Nat}
    (existsMaximum : ∃ groundSize, IsMaximumGroundSize blockCount groundSize) :
    IsMaximumGroundSize blockCount (maximumGroundSize blockCount) := by
  classical
  rw [maximumGroundSize]
  simp only [dif_pos existsMaximum]
  exact Classical.choose_spec existsMaximum

noncomputable def spec : SequenceSpec where
  offset := 2
  Domain := fun index =>
    2 ≤ index ∧ ∃ groundSize, IsMaximumGroundSize index.toNat groundSize
  value := fun index => Int.ofNat (maximumGroundSize index.toNat)

noncomputable def formalization := formalizationOf source spec

end A125620

namespace A097911

def source := sourceOf "A097911" "b65361b4a74fa012baaa1e37e90a1c5e76d1dacd2d2b6b782b6806c37dbec129" 1

/-- An injective vertex map preserving adjacency and non-adjacency is an
induced embedding. -/
def InducedEmbeds {smallSize largeSize : Nat}
    (small : SimpleGraph (Fin smallSize)) (large : SimpleGraph (Fin largeSize)) : Prop :=
  ∃ vertices : Fin smallSize → Fin largeSize,
    Function.Injective vertices ∧
      ∀ first second, small.Adj first second ↔
        large.Adj (vertices first) (vertices second)

def HasInducedUniversalGraph (smallSize largeSize : Nat) : Prop :=
  ∃ universal : SimpleGraph (Fin largeSize),
    ∀ small : SimpleGraph (Fin smallSize), InducedEmbeds small universal

noncomputable def leastUniversalSize (smallSize : Nat) : Nat :=
  sInf {largeSize | HasInducedUniversalGraph smallSize largeSize}

noncomputable def spec : SequenceSpec where
  offset := 1
  Domain := fun index =>
    1 ≤ index ∧ ∃ largeSize, HasInducedUniversalGraph index.toNat largeSize
  value := fun index => Int.ofNat (leastUniversalSize index.toNat)

noncomputable def formalization := formalizationOf source spec

end A097911

namespace A265286

def source := sourceOf "A265286" "4cc7a03296471b67774b3225dde5caeae42046f414874f1effb0432e4f3b3a88" 1

def IsCake (pieces : Multiset Rat) : Prop :=
  (∀ piece ∈ pieces, 0 < piece) ∧ pieces.sum = 1

/-- `groups` is a multiplicity-preserving partition of `pieces`. -/
def IsPartition {groupCount : Nat} (pieces : Multiset Rat)
    (groups : Fin groupCount → Multiset Rat) : Prop :=
  ∀ piece : Rat, pieces.count piece = ∑ group, (groups group).count piece

def SupportsDivision (pieces : Multiset Rat) (groupCount : Nat) : Prop :=
  0 < groupCount ∧
    ∃ groups : Fin groupCount → Multiset Rat,
      IsPartition pieces groups ∧
      ∀ group, (groups group).sum = 1 / (groupCount : Rat)

def SupportsEveryDivisionUpTo (bound : Nat) (pieces : Multiset Rat) : Prop :=
  ∀ groupCount, 1 ≤ groupCount → groupCount ≤ bound →
    SupportsDivision pieces groupCount

def ExistsCake (bound pieceCount : Nat) : Prop :=
  ∃ pieces : Multiset Rat,
    pieces.card = pieceCount ∧ IsCake pieces ∧
      SupportsEveryDivisionUpTo bound pieces

noncomputable def leastPieceCount (bound : Nat) : Nat :=
  sInf {pieceCount | ExistsCake bound pieceCount}

noncomputable def spec : SequenceSpec where
  offset := 1
  Domain := fun index => 1 ≤ index ∧ ∃ pieceCount, ExistsCake index.toNat pieceCount
  value := fun index => Int.ofNat (leastPieceCount index.toNat)

noncomputable def formalization := formalizationOf source spec

end A265286

noncomputable def registry : List (String × SequenceSpec) :=
  [("A180928", A180928.spec), ("A294369", A294369.spec),
   ("A125620", A125620.spec), ("A097911", A097911.spec),
   ("A265286", A265286.spec)]

theorem registry_length : registry.length = 5 := by rfl

#print axioms A180928.published_pairwise_triangular
#print axioms A294369.published_values_qualify
#print axioms A125620.maximumGroundSize_spec
#print axioms registry_length

end Mettapedia.Sequences.OEIS.AdversarialStructural
