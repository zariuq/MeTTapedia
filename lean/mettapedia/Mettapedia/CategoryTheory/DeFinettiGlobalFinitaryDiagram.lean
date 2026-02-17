import Mettapedia.CategoryTheory.DeFinettiPerNDiagram
import Mathlib.Data.Set.Finite.Basic
import Mathlib.GroupTheory.Perm.Support

/-!
# Global Finitary-Permutation Index for de Finetti Diagrams

This file adds an explicit global finitary-permutation index over `ℕ`:
- `FinSuppPermNat` (finitary permutations),
- its one-object category wrapper `GlobalFinSuppPermIndex`,
- and a canonical lift of per-`n` permutations into this global index.

It also proves that the corresponding lifted per-`n` commutation predicate is
equivalent to the existing `IsPrefixLawCone` interface.

Implementation note:
the extension construction `extendFinPermToNat` follows the same idea as
`extendFinPerm` in Cameron Freer's `exchangeability` project (vendored at
`Mettapedia/external/exchangeability`).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory

open MeasureTheory
open CategoryTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Subgroup of finitary permutations of `ℕ`, i.e. permutations with finite moved-point set. -/
def FinSuppPermNatSubgroup : Subgroup (Equiv.Perm ℕ) where
  carrier := {σ | ({i : ℕ | σ i ≠ i} : Set ℕ).Finite}
  one_mem' := by
    simp
  mul_mem' := by
    intro σ τ hσ hτ
    refine (hσ.union hτ).subset ?_
    simpa using (Equiv.Perm.set_support_mul_subset (p := σ) (q := τ))
  inv_mem' := by
    intro σ hσ
    simpa [Equiv.Perm.set_support_symm_eq (p := σ)] using hσ

/-- Type of finitary permutations of `ℕ`. -/
abbrev FinSuppPermNat : Type := FinSuppPermNatSubgroup

/-- One-object category indexed by global finitary permutations of `ℕ`. -/
abbrev GlobalFinSuppPermIndex : Type := CategoryTheory.SingleObj FinSuppPermNat

/-- Unique object in the global finitary-permutation index category. -/
abbrev globalFinSuppPermStar : GlobalFinSuppPermIndex :=
  CategoryTheory.SingleObj.star FinSuppPermNat

/-- Extend a permutation of `Fin n` to a permutation of `ℕ` by identity off `[0, n)`. -/
def extendFinPermToNat {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm ℕ where
  toFun i := if h : i < n then (σ ⟨i, h⟩).1 else i
  invFun i := if h : i < n then (σ.symm ⟨i, h⟩).1 else i
  left_inv i := by
    by_cases h : i < n <;> simp [h, Fin.eta, Equiv.symm_apply_apply]
  right_inv i := by
    by_cases h : i < n <;> simp [h, Fin.eta, Equiv.apply_symm_apply]

lemma movedPoints_extendFinPermToNat_subset_Iio {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ({i : ℕ | extendFinPermToNat σ i ≠ i} : Set ℕ) ⊆ Set.Iio n := by
  intro i hi
  by_contra hlt
  have hnot : ¬ i < n := by
    simpa [Set.mem_Iio] using hlt
  have hfix : extendFinPermToNat σ i = i := by
    simp [extendFinPermToNat, hnot]
  exact hi hfix

lemma extendFinPermToNat_finiteSupport {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ({i : ℕ | extendFinPermToNat σ i ≠ i} : Set ℕ).Finite := by
  exact (Set.finite_lt_nat n).subset (movedPoints_extendFinPermToNat_subset_Iio σ)

/-- Lift a finite-prefix permutation to the global finitary permutation index. -/
def finPermToFinSuppPermNat {n : ℕ} (σ : Equiv.Perm (Fin n)) : FinSuppPermNat :=
  ⟨extendFinPermToNat σ, extendFinPermToNat_finiteSupport σ⟩

lemma extendFinPermToNat_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    extendFinPermToNat (σ * τ) = (extendFinPermToNat σ) * (extendFinPermToNat τ) := by
  ext i
  by_cases hi : i < n
  · have hτ : (τ ⟨i, hi⟩).1 < n := (τ ⟨i, hi⟩).2
    simp [extendFinPermToNat, hi, hτ, Equiv.Perm.mul_apply]
  · simp [extendFinPermToNat, hi]

/-- Monoid hom from per-`n` permutations into global finitary permutations. -/
def finPermToFinSuppPermNatMonoidHom (n : ℕ) : Equiv.Perm (Fin n) →* FinSuppPermNat where
  toFun := finPermToFinSuppPermNat
  map_one' := by
    ext i
    by_cases hi : i < n <;> simp [finPermToFinSuppPermNat, extendFinPermToNat]
  map_mul' := by
    intro σ τ
    ext i
    by_cases hi : i < n
    · have hτ : (τ ⟨i, hi⟩).1 < n := (τ ⟨i, hi⟩).2
      simp [finPermToFinSuppPermNat, extendFinPermToNat, hi, hτ, Equiv.Perm.mul_apply]
    · simp [finPermToFinSuppPermNat, extendFinPermToNat, hi]

/-- Functor embedding the per-`n` permutation index into the global finitary index. -/
abbrev perNToGlobalFinSuppPermFunctor (n : ℕ) :
    CategoryTheory.Functor (PerNPermIndex n) GlobalFinSuppPermIndex :=
  MonoidHom.toFunctor (finPermToFinSuppPermNatMonoidHom n)

/-- Per-`n` prefix-diagram map, with the finite permutation viewed through the
global finitary index via `finPermToFinSuppPermNat`. -/
def perNPrefixDiagramMapFromGlobalLift (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    BoolPrefixObj n → BoolPrefixObj n :=
  let _τ : FinSuppPermNat := finPermToFinSuppPermNat σ
  perNPrefixDiagramMap n σ

/-! ## Direct Global Action on Sequence-Law Objects -/

/-- Canonical binary sequence space `Bool^ℕ`. -/
abbrev GlobalBinarySeq : Type := ℕ → Bool

/-- Direct action of a finitary permutation on binary sequences. -/
def finSuppPermuteSeq (τ : FinSuppPermNat) (ω : GlobalBinarySeq) : GlobalBinarySeq :=
  fun i => ω ((τ.1).symm i)

/-- Prefix cylinder event on `Bool^ℕ`. -/
def globalSeqPrefixEvent (n : ℕ) (xs : Fin n → Bool) : Set GlobalBinarySeq :=
  {ω | ∀ i : Fin n, ω i = xs i}

/-- Sequence-law objects: set-indexed mass functionals on binary sequences. -/
abbrev GlobalBinarySeqLawObj : Type := Set GlobalBinarySeq → ENNReal

/-- Direct global `τ`-action on sequence-law objects by preimage. -/
def finSuppPermActionOnSeqLaw
    (τ : FinSuppPermNat) (L : GlobalBinarySeqLawObj) : GlobalBinarySeqLawObj :=
  fun A => L {ω | finSuppPermuteSeq τ ω ∈ A}

/-- Prefix-law object induced from a sequence-law object. -/
def prefixLawObjOfSeqLaw (L : GlobalBinarySeqLawObj) (n : ℕ) : BoolPrefixObj n :=
  fun xs => L (globalSeqPrefixEvent n xs)

/-- Prefix-law action induced from the global `τ`-action on sequence-law objects. -/
def globalPrefixLawActionFromSeqLaw
    (τ : FinSuppPermNat) (L : GlobalBinarySeqLawObj) (n : ℕ) : BoolPrefixObj n :=
  prefixLawObjOfSeqLaw (finSuppPermActionOnSeqLaw τ L) n

/-- Compatibility of direct global action with lifted per-`n` action:
for lifted finite permutations, acting on sequence-laws and then extracting
prefix-laws agrees with `perNPrefixDiagramMap`. -/
theorem globalPrefixLawActionFromSeqLaw_compatible_with_lift
    (L : GlobalBinarySeqLawObj) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    globalPrefixLawActionFromSeqLaw (finPermToFinSuppPermNat σ) L n =
      perNPrefixDiagramMap n σ (prefixLawObjOfSeqLaw L n) := by
  funext xs
  have hset :
      {ω : GlobalBinarySeq | ∀ i : Fin n, ω ↑((Equiv.symm σ) i) = xs i} =
        {ω : GlobalBinarySeq | ∀ i : Fin n, ω ↑i = xs (σ i)} := by
    ext ω
    constructor
    · intro h i
      simpa using h (σ i)
    · intro h i
      simpa using h (σ.symm i)
  unfold globalPrefixLawActionFromSeqLaw prefixLawObjOfSeqLaw
  simp [finSuppPermActionOnSeqLaw, perNPrefixDiagramMap, perNPrefixDiagramFunctor,
    boolPrefixPermAction, globalSeqPrefixEvent, finSuppPermuteSeq, finPermToFinSuppPermNat,
    extendFinPermToNat, permuteBoolTuple, hset]

/-- Lifted commutation predicate using the global finitary-permutation index. -/
def GlobalLiftedPrefixLawConeCommutes
    (X : ℕ → Ω → Bool) (μ : Measure Ω) : Prop :=
  ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
    perNPrefixDiagramMapFromGlobalLift n σ (prefixLaw X μ n) = prefixLaw X μ n

/-- The global-lifted commutation predicate is equivalent to the existing per-`n`
categorical commutation family. -/
theorem globalLiftedPrefixLawConeCommutes_iff_perNPrefixLawConeCommutes
    (X : ℕ → Ω → Bool) (μ : Measure Ω) :
    GlobalLiftedPrefixLawConeCommutes (Ω := Ω) X μ ↔
      ∀ n : ℕ, PerNPrefixLawConeCommutes (Ω := Ω) X μ n := by
  constructor
  · intro h n σ
    simpa [GlobalLiftedPrefixLawConeCommutes, perNPrefixDiagramMapFromGlobalLift] using h n σ
  · intro h n σ
    simpa [GlobalLiftedPrefixLawConeCommutes, perNPrefixDiagramMapFromGlobalLift] using h n σ

/-- Diagram-action commutation equivalence:
the global finitary lifted commutation laws are equivalent to `IsPrefixLawCone`. -/
theorem isPrefixLawCone_iff_globalLiftedPrefixLawConeCommutes
    (X : ℕ → Ω → Bool) (μ : Measure Ω) :
    IsPrefixLawCone (Ω := Ω) X μ ↔
      GlobalLiftedPrefixLawConeCommutes (Ω := Ω) X μ := by
  constructor
  · intro h n σ
    simpa [GlobalLiftedPrefixLawConeCommutes, perNPrefixDiagramMapFromGlobalLift,
      IsPrefixLawCone, perNPrefixDiagramMap, perNPermStar] using h n σ.symm
  · intro h n σ
    simpa [GlobalLiftedPrefixLawConeCommutes, perNPrefixDiagramMapFromGlobalLift,
      IsPrefixLawCone, perNPrefixDiagramMap, perNPermStar] using h n σ.symm

end Mettapedia.CategoryTheory
