import Mettapedia.Computability.KolmogorovComplexity.PrefixComplexity
import Mettapedia.Computability.HutterComputability
import Mettapedia.Computability.KolmogorovComplexity.Uncomputability
import Mettapedia.UniversalAI.SolomonoffInduction
import Mettapedia.UniversalAI.UniversalPrediction

/-!
# Simplicity & Uncertainty (Hutter 2005, Chapter 2) — entrypoint

Chapter 1 of Hutter’s book is a narrative tour. The first substantial mathematical
content begins in Chapter 2, which introduces:

- prefix/monotone machines and Kolmogorov complexity
- (semi)measures on binary strings
- Solomonoff’s universal prior `M`

This module is intentionally lightweight: it *re-exports* the existing formalization
pieces and exposes a small set of “Chapter‑2 interface” definitions/lemmas that later
chapters (especially Chapter 3 weights `2^{-Kpf}` and Chapter 4 mixtures) depend on.

No attempt is made here to prove the major convergence theorems yet.
-/

namespace Mettapedia.UniversalAI.SimplicityUncertainty

open scoped Classical BigOperators

open Mettapedia.Computability.Hutter
open Mettapedia.UniversalAI.SolomonoffPrior
open Mettapedia.UniversalAI.SolomonoffInduction
open Mettapedia.UniversalAI.UniversalPrediction

abbrev BinString := Mettapedia.UniversalAI.SolomonoffPrior.BinString
abbrev PrefixFreeMachine := Mettapedia.UniversalAI.SolomonoffPrior.PrefixFreeMachine
abbrev UniversalPFM := Mettapedia.UniversalAI.SolomonoffPrior.UniversalPFM
abbrev MonotoneMachine := Mettapedia.UniversalAI.SolomonoffPrior.MonotoneMachine
abbrev Semimeasure := Mettapedia.UniversalAI.SolomonoffInduction.Semimeasure

/-! ## Kolmogorov complexity (prefix-free)

We use the prefix-free complexity `Kpf` from
`Mettapedia.Computability.KolmogorovComplexity.PrefixComplexity`.
-/

/-- Invariance theorem for prefix-free complexity (machine-independence up to an additive constant). -/
theorem invariance_Kpf (U V : PrefixFreeMachine) [UniversalPFM U] [UniversalPFM V] :
    ∃ c : ℕ, ∀ x : BinString, Kpf[U](x) ≤ Kpf[V](x) + c :=
  KolmogorovComplexity.invariance_Kpf (U := U) (V := V)

/-- Kraft/summability for the algorithmic-style weights `2^{-Kpf}`. -/
theorem tsum_two_pow_neg_Kpf_le_one (U : PrefixFreeMachine) [UniversalPFM U] :
    (∑' x : BinString, (2 : ENNReal) ^ (-(Kpf[U](x) : ℤ))) ≤ 1 :=
  KolmogorovComplexity.tsum_weightByKpf_le_one_ennreal (U := U)

/-! ## Computability notions (Hutter Definition 2.12) -/

abbrev FinitelyComputable {α β : Type*} [Primcodable α] [Primcodable β] (f : α → β) : Prop :=
  Mettapedia.Computability.Hutter.FinitelyComputable f

abbrev Approximable {α : Type*} [Primcodable α] (f : α → ℝ) : Prop :=
  Mettapedia.Computability.Hutter.Approximable f

abbrev LowerSemicomputable {α : Type*} [Primcodable α] (f : α → ℝ) : Prop :=
  Mettapedia.Computability.Hutter.LowerSemicomputable f

abbrev UpperSemicomputable {α : Type*} [Primcodable α] (f : α → ℝ) : Prop :=
  Mettapedia.Computability.Hutter.UpperSemicomputable f

abbrev Enumerable {α : Type*} [Primcodable α] (f : α → ℝ) : Prop :=
  Mettapedia.Computability.Hutter.Enumerable f

abbrev CoEnumerable {α : Type*} [Primcodable α] (f : α → ℝ) : Prop :=
  Mettapedia.Computability.Hutter.CoEnumerable f

abbrev Estimable {α : Type*} [Primcodable α] (f : α → ℝ) : Prop :=
  Mettapedia.Computability.Hutter.Estimable f

/-! ## Noncomputability of plain Kolmogorov complexity (Hutter Theorem 2.13) -/

/-- Hutter (2005), Theorem 2.13: plain Kolmogorov complexity is not finitely computable. -/
theorem kolmogorovComplexity_not_finitelyComputable :
    ¬ FinitelyComputable (KolmogorovComplexity.kolmogorovComplexity : BinString → ℕ) :=
  KolmogorovComplexity.kolmogorovComplexity_not_finitelyComputable

/-! ## Universal mixture ξ (Equation (2.26))

Hutter’s proof of Theorem 2.23 introduces the universal mixture

`ξ(x) := ∑ᵢ 2^{-K(i)} νᵢ(x)`

and notes that dominance (2.27) is “obvious” since the sum includes the `i`-th term.
The hard part (Levin’s enumeration theorem + relating `ξ` to `M`) is treated as cited
background and is tracked as a separate checklist item.
-/

/-- Algorithmic prior weight `w(i) = 2^{-Kpf(i)}` (ENNReal form). -/
noncomputable abbrev kpfWeight (U : PrefixFreeMachine) [UniversalPFM U] (i : BinString) : ENNReal :=
  Mettapedia.UniversalAI.UniversalPrediction.kpfWeight (U := U) i

/-- The universal mixture `ξ` built from a `BinString`-indexed family of semimeasures. -/
noncomputable abbrev xiKpf (U : PrefixFreeMachine) [UniversalPFM U] (ν : BinString → Semimeasure) :
    Semimeasure :=
  Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure (U := U) ν

/-- Dominance of `ξ` over each component (Hutter Eq. (2.27)). -/
theorem xiKpf_dominates_index (U : PrefixFreeMachine) [UniversalPFM U]
    (ν : BinString → Semimeasure) (i x : BinString) :
    kpfWeight U i * ν i x ≤ (xiKpf (U := U) ν) x := by
  simpa [kpfWeight, xiKpf] using
    (Mettapedia.UniversalAI.UniversalPrediction.xiKpf_dominates_index (U := U) (ν := ν) i x)

/-! ## Bayes update for countable mixtures (Theorem 2.19-style) -/

/-- Generic countable mixture `ξ(x) := ∑ᵢ w(i) νᵢ(x)` as an `ENNReal` function. -/
noncomputable abbrev xiFun {ι : Type*} (ν : ι → Semimeasure) (w : ι → ENNReal) (x : BinString) :
    ENNReal :=
  Mettapedia.UniversalAI.UniversalPrediction.xiFun ν w x

/-- Posterior weight `w(i|x) = w(i) νᵢ(x) / ξ(x)` (and `0` when `ξ(x)=0`). -/
noncomputable abbrev posteriorWeight {ι : Type*} (ν : ι → Semimeasure) (w : ι → ENNReal)
    (x : BinString) (i : ι) : ENNReal :=
  Mettapedia.UniversalAI.UniversalPrediction.posteriorWeight ν w x i

theorem tsum_posteriorWeight {ι : Type*} (ν : ι → Semimeasure) (w : ι → ENNReal)
    (hw : (∑' i : ι, w i) ≤ 1) (x : BinString) :
    (∑' i : ι, posteriorWeight ν w x i) = if xiFun ν w x = 0 then 0 else 1 := by
  simpa [xiFun, posteriorWeight] using
    (Mettapedia.UniversalAI.UniversalPrediction.tsum_posteriorWeight (ν := ν) (w := w) hw x)

/-- ENNReal conditional probability for a semimeasure: `μ(y|x) := μ(xy) / μ(x)`. -/
noncomputable abbrev conditionalENN (μ : Semimeasure) (y x : BinString) : ENNReal :=
  Mettapedia.UniversalAI.UniversalPrediction.conditionalENN μ y x

/-- Mixture conditional as posterior-weighted sum of component conditionals (Bayes mixture form). -/
theorem xi_conditionalENN_eq_tsum_posterior_mul {ι : Type*} (ν : ι → Semimeasure) (w : ι → ENNReal)
    (x y : BinString) :
    xiFun ν w (x ++ y) / xiFun ν w x =
      ∑' i : ι, posteriorWeight ν w x i * conditionalENN (ν i) y x := by
  simpa [xiFun, posteriorWeight, conditionalENN] using
    (Mettapedia.UniversalAI.UniversalPrediction.xi_conditionalENN_eq_tsum_posterior_mul (ν := ν) (w := w) x y)

/-! ## (Semi)measures and Solomonoff induction

`Semimeasure` is Hutter’s Definition 2.22. Solomonoff’s universal prior `M` is encoded as the
`universalPrior` semimeasure built from the cylinder construction on a monotone machine.
-/

/-- Hutter’s universal prior `M` (Equation (2.21)) as a semimeasure. -/
noncomputable abbrev M (U : MonotoneMachine) (programs : Finset BinString)
    (hpf : PrefixFree (↑programs : Set BinString)) : Semimeasure :=
  universalPrior U programs hpf

theorem M_root_le_one (U : MonotoneMachine) (programs : Finset BinString)
    (hpf : PrefixFree (↑programs : Set BinString)) :
    M U programs hpf [] ≤ 1 :=
  (M U programs hpf).root_le_one'

theorem M_superadditive (U : MonotoneMachine) (programs : Finset BinString)
    (hpf : PrefixFree (↑programs : Set BinString)) (x : BinString) :
    M U programs hpf (x ++ [false]) + M U programs hpf (x ++ [true]) ≤ M U programs hpf x :=
  (M U programs hpf).superadditive' x

end Mettapedia.UniversalAI.SimplicityUncertainty
