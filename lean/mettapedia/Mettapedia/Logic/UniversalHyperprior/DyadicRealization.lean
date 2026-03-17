/-
# Universal Hyperprior: Dyadic Realization Layer

This file implements the **dyadic realization layer** for the Universal Hyperprior.

## Three-Layer Architecture

1. **Semantic Layer** (`UniversalHyperprior.lean`): Pure ℝ mathematics
2. **Dyadic Layer** (THIS FILE): Computable approximations with error bounds
3. **LSC Layer** (`Computability.lean`): Connection to Hutter's framework

## Purpose

The dyadic layer provides:
- Computable arithmetic using only ℤ and ℕ (decidable!)
- Explicit error bounds (no hand-waving)
- Convergence proofs to the semantic layer
- Practical implementation for PLN

## Why Dyadic?

Dyadic rationals (`a / 2^n` where `a : ℤ, n : ℕ`) are the standard bridge from
computable types to real numbers in Lean's computability framework. This is not
a shortcut - it's how `LowerSemicomputable` is defined in Hutter's framework.

See: `Mettapedia/Computability/HutterComputability.lean`

## Key Insight

The Universal Hyperprior uses τ₀² = 2^k, which is EXACTLY representable as a
dyadic (no approximation error on the hyperparameters themselves!). Only the
evidence statistics (sample mean/variance) need dyadic approximation.

-/

import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mettapedia.Logic.UniversalHyperprior
import Mettapedia.Logic.EvidenceNormalGamma

namespace Mettapedia.Logic.UniversalHyperprior.Dyadic

open Mettapedia.Logic.EvidenceNormalGamma
open Mettapedia.Logic.UniversalHyperprior

/-! ## Dyadic Value Type

A dyadic rational is a number of the form `num / 2^denom_pow`.

We store:
- `num : ℤ` - the numerator (can be negative)
- `denom_pow : ℕ` - the power of 2 in the denominator

This represents: `num / 2^denom_pow`
-/

structure DyadicValue where
  num : ℤ
  denom_pow : ℕ

namespace DyadicValue

/-- Convert a dyadic value to a real number -/
noncomputable def toReal (d : DyadicValue) : ℝ :=
  (d.num : ℝ) / (2 : ℝ) ^ d.denom_pow

/-- Zero as a dyadic -/
def zero : DyadicValue := ⟨0, 0⟩

/-- One as a dyadic -/
def one : DyadicValue := ⟨1, 0⟩

/-- Addition of dyadic values (aligns to common denominator) -/
def add (a b : DyadicValue) : DyadicValue :=
  if a.denom_pow = b.denom_pow then
    ⟨a.num + b.num, a.denom_pow⟩
  else if a.denom_pow < b.denom_pow then
    let shift := b.denom_pow - a.denom_pow
    ⟨a.num * (2 ^ shift) + b.num, b.denom_pow⟩
  else
    let shift := a.denom_pow - b.denom_pow
    ⟨a.num + b.num * (2 ^ shift), a.denom_pow⟩

/-- Multiplication of dyadic values -/
def mul (a b : DyadicValue) : DyadicValue :=
  ⟨a.num * b.num, a.denom_pow + b.denom_pow⟩

/-- Division of dyadic values (approximate - may lose precision) -/
def div (a b : DyadicValue) (precision : ℕ) : DyadicValue :=
  -- Compute (a.num * 2^precision) / b.num, then shift denominator
  let num_shifted := a.num * (2 ^ precision : ℤ)
  let result_num := num_shifted / b.num
  ⟨result_num, a.denom_pow + precision - b.denom_pow⟩

instance : Add DyadicValue := ⟨add⟩
instance : Mul DyadicValue := ⟨mul⟩

end DyadicValue

/-! ## Dyadic Context

A `NormalNormalContext` represented with dyadic rationals.

Key insight: Since τ₀² = 2^k in the Universal Hyperprior, it's EXACTLY
representable as a dyadic (no approximation!).
-/

structure DyadicContext where
  /-- Prior mean μ₀ as dyadic: μ₀_num / 2^μ₀_denom_pow -/
  μ₀_num : ℤ
  μ₀_denom_pow : ℕ

  /-- Prior variance τ₀² as a POWER of 2: τ₀² = 2^τ₀_sq_pow

  This is EXACT for the Universal Hyperprior family! -/
  τ₀_sq_pow : ℤ

  /-- Observation variance σ² as dyadic: σ_sq_num / 2^σ_sq_denom_pow -/
  σ_sq_num : ℕ
  σ_sq_denom_pow : ℕ

  /-- Positivity constraint: σ² > 0 -/
  σ_sq_num_pos : 0 < σ_sq_num

namespace DyadicContext

/-- Convert dyadic context to real-valued context -/
noncomputable def toReal (ctx : DyadicContext) : NormalNormalContext where
  μ₀ := (ctx.μ₀_num : ℝ) / (2 : ℝ) ^ ctx.μ₀_denom_pow
  τ₀_sq := (2 : ℝ) ^ ctx.τ₀_sq_pow
  σ_sq := (ctx.σ_sq_num : ℝ) / (2 : ℝ) ^ ctx.σ_sq_denom_pow
  τ₀_sq_pos := by
    apply zpow_pos
    norm_num
  σ_sq_pos := by
    apply div_pos
    · exact Nat.cast_pos.mpr ctx.σ_sq_num_pos
    · apply pow_pos; norm_num

/-- Create a context for Universal Hyperprior at index k
    Uses τ₀² = 2^k (exact!), μ₀ = 0, σ² provided as dyadic -/
def atK (k : ℤ) (σ_sq_num : ℕ) (σ_sq_denom_pow : ℕ) (h : 0 < σ_sq_num) : DyadicContext where
  μ₀_num := 0
  μ₀_denom_pow := 0
  τ₀_sq_pow := k
  σ_sq_num := σ_sq_num
  σ_sq_denom_pow := σ_sq_denom_pow
  σ_sq_num_pos := h

end DyadicContext

/-! ## Dyadic BinaryEvidence

BinaryEvidence represented with dyadic rationals for sample mean and variance.
-/

structure DyadicEvidence where
  /-- Sample count (exact) -/
  n : ℕ

  /-- Sample mean as dyadic: mean_num / 2^mean_denom_pow -/
  mean_num : ℤ
  mean_denom_pow : ℕ

  /-- Sample variance as dyadic: var_num / 2^var_denom_pow -/
  var_num : ℕ
  var_denom_pow : ℕ

namespace DyadicEvidence

/-- Convert dyadic evidence to real-valued evidence -/
noncomputable def toReal (ev : DyadicEvidence) : NormalGammaEvidence where
  n := ev.n
  sum := ev.n * ((ev.mean_num : ℝ) / (2 : ℝ) ^ ev.mean_denom_pow)
  sumSq := ev.n * (((ev.mean_num : ℝ) / (2 : ℝ) ^ ev.mean_denom_pow) ^ 2
                   + (ev.var_num : ℝ) / (2 : ℝ) ^ ev.var_denom_pow)
  sumSq_nonneg := by
    apply mul_nonneg
    · exact Nat.cast_nonneg _
    · apply add_nonneg
      · apply sq_nonneg
      · apply div_nonneg
        · exact Nat.cast_nonneg _
        · apply pow_nonneg; norm_num
  cauchy_schwarz := by
    sorry  -- TODO: Prove Cauchy-Schwarz holds for this reconstruction

/-- Extract sample mean as dyadic value -/
def toMean (ev : DyadicEvidence) : DyadicValue :=
  ⟨ev.mean_num, ev.mean_denom_pow⟩

end DyadicEvidence

end Mettapedia.Logic.UniversalHyperprior.Dyadic
