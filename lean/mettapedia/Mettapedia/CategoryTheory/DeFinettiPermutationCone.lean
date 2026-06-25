import Mettapedia.CategoryTheory.DeFinettiCategoricalInterface
import Mettapedia.ProbabilityTheory.Exchangeability.Core

/-!
# Permutation-Cone Interface for de Finetti

This file provides a qualitative cone-style interface for exchangeability:
finite-prefix laws commute with finite permutations. It then bridges that
interface to categorical de Finetti factorization.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory

open MeasureTheory
open Mettapedia.ProbabilityTheory.Exchangeability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Finite-coordinate permutation action on Boolean tuples. -/
def permuteBoolTuple {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (xs : Fin n → Bool) : Fin n → Bool :=
  xs ∘ σ.symm

/-- Finite-prefix law of a process at horizon `n`. -/
def prefixLaw (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (n : ℕ) (xs : Fin n → Bool) : ENNReal :=
  μ {ω | ∀ i : Fin n, X i.val ω = xs i}

/-- Cone-style exchangeability interface:
prefix laws are invariant under finite-coordinate permutations. -/
def ExchangeablePrefixCone
    (X : ℕ → Ω → Bool) (μ : Measure Ω) : Prop :=
  ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) (xs : Fin n → Bool),
    prefixLaw X μ n xs = prefixLaw X μ n (permuteBoolTuple σ xs)

private theorem prefixLaw_perm_target_eq
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (xs : Fin n → Bool) :
    μ {ω | ∀ i : Fin n, X (σ i).val ω = xs i} =
      prefixLaw X μ n (permuteBoolTuple σ xs) := by
  unfold prefixLaw permuteBoolTuple
  congr 1
  ext ω
  constructor <;> intro h i
  · have hi := h (σ.symm i)
    simpa using hi
  · have hi := h (σ i)
    simpa using hi

/-- Existing `InfiniteExchangeable` implies the cone-style interface. -/
theorem exchangeablePrefixCone_of_infiniteExchangeable
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hexch : InfiniteExchangeable X μ) :
    ExchangeablePrefixCone X μ := by
  intro n σ xs
  have hseg : FiniteExchangeable n (fun i : Fin n => X i.val) μ :=
    hexch.finite_segments n
  have hperm :
      μ {ω | ∀ i : Fin n, X i.val ω = xs i} =
        μ {ω | ∀ i : Fin n, X i.val ω = xs (σ.symm i)} := by
    simpa [Function.comp] using
      (finiteExchangeable_perm_values
        (X := fun i : Fin n => X i.val) (μ := μ) hseg σ xs)
  simpa [prefixLaw, permuteBoolTuple] using hperm

/-- The cone-style interface implies existing `InfiniteExchangeable`. -/
theorem infiniteExchangeable_of_exchangeablePrefixCone
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hcone : ExchangeablePrefixCone X μ) :
    InfiniteExchangeable X μ := by
  refine ⟨?_⟩
  intro n
  refine ⟨?_⟩
  intro σ vals
  have hcone_n : prefixLaw X μ n vals = prefixLaw X μ n (permuteBoolTuple σ vals) :=
    hcone n σ vals
  have hreindex :
      prefixLaw X μ n (permuteBoolTuple σ vals) =
        μ {ω | ∀ i : Fin n, X (σ i).val ω = vals i} := by
    simpa using
      (prefixLaw_perm_target_eq (X := X) (μ := μ) (n := n) (σ := σ) (xs := vals)).symm
  calc
    μ {ω | ∀ i : Fin n, X i.val ω = vals i}
        = prefixLaw X μ n vals := by rfl
    _ = prefixLaw X μ n (permuteBoolTuple σ vals) := hcone_n
    _ = μ {ω | ∀ i : Fin n, X (σ i).val ω = vals i} := hreindex

/-- Equivalence between the old exchangeability notion and the cone-style interface. -/
theorem infiniteExchangeable_iff_exchangeablePrefixCone
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    InfiniteExchangeable X μ ↔ ExchangeablePrefixCone X μ := by
  constructor
  · intro hexch
    exact exchangeablePrefixCone_of_infiniteExchangeable X μ hexch
  · intro hcone
    exact infiniteExchangeable_of_exchangeablePrefixCone X μ hcone

/-- Cone-style factorization theorem:
permutation-cone exchangeability is equivalent to categorical de Finetti factorization. -/
theorem exchangeablePrefixCone_iff_categoricalDeFinettiFactorization
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hX : ∀ i : ℕ, Measurable (X i)) :
    ExchangeablePrefixCone X μ ↔ CategoricalDeFinettiFactorization X μ := by
  constructor
  · intro hcone
    have hexch : InfiniteExchangeable X μ :=
      infiniteExchangeable_of_exchangeablePrefixCone X μ hcone
    exact categoricalDeFinetti_factorization_of_exchangeable X μ hX hexch
  · intro hfac
    have hexch : InfiniteExchangeable X μ :=
      (exchangeable_iff_categoricalDeFinettiFactorization X μ hX).2 hfac
    exact exchangeablePrefixCone_of_infiniteExchangeable X μ hexch

/-- Limit-cone phrasing for exchangeability on finite prefixes.

`DeFinettiLimitCone X μ` means the finite-prefix law of `X` at `μ` is a cone
over finite-coordinate permutation actions. -/
def DeFinettiLimitCone
    (X : ℕ → Ω → Bool) (μ : Measure Ω) : Prop :=
  ExchangeablePrefixCone X μ

/-- Universal-factorization direction in limit-cone language. -/
theorem deFinetti_limitCone_universal_factorization
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hX : ∀ i : ℕ, Measurable (X i)) :
    DeFinettiLimitCone X μ → CategoricalDeFinettiFactorization X μ := by
  intro hcone
  exact (exchangeablePrefixCone_iff_categoricalDeFinettiFactorization X μ hX).1 hcone

/-- Converse direction: a categorical factorization induces the limit-cone laws. -/
theorem deFinetti_factorization_induces_limitCone
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hX : ∀ i : ℕ, Measurable (X i)) :
    CategoricalDeFinettiFactorization X μ → DeFinettiLimitCone X μ := by
  intro hfac
  exact (exchangeablePrefixCone_iff_categoricalDeFinettiFactorization X μ hX).2 hfac

/-- Limit-cone form of the qualitative de Finetti theorem. -/
theorem deFinetti_limitCone_iff_categoricalFactorization
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hX : ∀ i : ℕ, Measurable (X i)) :
    DeFinettiLimitCone X μ ↔ CategoricalDeFinettiFactorization X μ := by
  exact exchangeablePrefixCone_iff_categoricalDeFinettiFactorization X μ hX

end Mettapedia.CategoryTheory
