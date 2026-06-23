import Mettapedia.Computability.HutterComputability
import Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.FiniteHorizon
import Mettapedia.Logic.UniversalPrediction

/-!
# Hutter-Style Computable Enumerations (Finite Alphabet)

This file is the finite-alphabet analogue of `Mettapedia/Logic/UniversalPrediction/HutterEnumeration.lean`.

Hutter (2005), Chapter 2, works with **enumerable (lower semicomputable) semimeasures**.
To connect those Chapter‑2 computability notions to the Chapter‑3 dominance→regret bounds, we
fix the computability predicate to:

* lower semicomputability of the real-valued map `x ↦ (ξ x).toReal`,
  expressed via computable monotone dyadic approximations.

Unlike the binary development, this file is alphabet-parametric: it targets semimeasures and
prefix measures on `Word α := List α`.

The corresponding “enumeration theorem” implementation lives in:
* `Mettapedia/Logic/UniversalPrediction/FiniteAlphabet/HutterEnumerationTheoremSemimeasure.lean`.
-/

noncomputable section

namespace Mettapedia.Logic.UniversalPrediction.FiniteAlphabet

open scoped Classical BigOperators

open Mettapedia.Computability.Hutter
open FiniteHorizon

/-! ## Hutter-style lower semicomputability predicates -/

variable {α : Type*} [Fintype α] [Primcodable α]

/-- Hutter-style “enumerable / lower semicomputable” semimeasure on `Word α`.

We express this via lower semicomputability of the real-valued map `x ↦ (ξ x).toReal`. -/
def LowerSemicomputableSemimeasure (ξ : Semimeasure α) : Prop :=
  LowerSemicomputable (fun x : Word α => (ξ x).toReal)

/-- Hutter-style “enumerable / lower semicomputable” prefix measure on `Word α`. -/
def LowerSemicomputablePrefixMeasure (μ : PrefixMeasure α) : Prop :=
  LowerSemicomputable (fun x : Word α => (μ x).toReal)

/-! ## Enumeration stubs, sufficient to “turn on” Chapter‑3 bounds -/

/-- A semimeasure enumeration with Hutter's lower-semicomputability predicate.

This is the Chapter‑2 object Hutter wants: **enumerable semimeasures**. -/
structure LSCSemimeasureEnumeration where
  /-- Code space indexing the enumeration. -/
  Code : Type*
  /-- The code space is countable. -/
  [enc : Encodable Code]
  /-- Interpret a code as a semimeasure. -/
  eval : Code → Semimeasure α
  /-- Enumeration theorem (as an interface): every LSC semimeasure has some code. -/
  surj_eval :
    ∀ ξ : Semimeasure α, LowerSemicomputableSemimeasure (α := α) ξ → ∃ c : Code, eval c = ξ

attribute [instance] LSCSemimeasureEnumeration.enc

namespace LSCSemimeasureEnumeration

/-- The universal `encodeWeight` mixture induced by a semimeasure enumeration. -/
noncomputable def xi (E : LSCSemimeasureEnumeration (α := α)) : Semimeasure α :=
  xiSemimeasure (ν := E.eval) (w := Mettapedia.Logic.UniversalPrediction.encodeWeight)
    (hw := Mettapedia.Logic.UniversalPrediction.tsum_encodeWeight_le_one (ι := E.Code))

/-- The mixture `ξ` dominates each enumerated component with its code weight. -/
theorem xi_dominates_eval (E : LSCSemimeasureEnumeration (α := α)) (c : E.Code) :
    Dominates (E.xi) (E.eval c) (Mettapedia.Logic.UniversalPrediction.encodeWeight c) := by
  intro x
  -- Termwise dominance inside a `tsum`.
  simpa [LSCSemimeasureEnumeration.xi, xiSemimeasure, xiFun] using
    (xi_dominates_index (ν := E.eval) (w := Mettapedia.Logic.UniversalPrediction.encodeWeight) (i := c) (x := x))

theorem encodeWeight_ne_zero (E : LSCSemimeasureEnumeration (α := α)) (c : E.Code) :
    Mettapedia.Logic.UniversalPrediction.encodeWeight c ≠ 0 := by
  unfold Mettapedia.Logic.UniversalPrediction.encodeWeight
  exact pow_ne_zero _ (by simp)

/-- View a lower-semicomputable prefix measure as a lower-semicomputable semimeasure. -/
theorem lscPrefixMeasure_toSemimeasure (μ : PrefixMeasure α)
    (hμ : LowerSemicomputablePrefixMeasure (α := α) μ) :
    LowerSemicomputableSemimeasure (α := α) μ.toSemimeasure := by
  -- Same underlying `toReal` function, since `μ.toSemimeasure x = μ x`.
  simpa [LowerSemicomputableSemimeasure, LowerSemicomputablePrefixMeasure,
    PrefixMeasure.toSemimeasure_apply] using hμ

/-- Convenience lemma: dominance→regret for any lower-semicomputable **measure** μ,
using the universal mixture induced by an **enumeration of semimeasures**. -/
theorem relEntropy_le_log_inv_of_LSC (E : LSCSemimeasureEnumeration (α := α)) (μ : PrefixMeasure α)
    (hμ : LowerSemicomputablePrefixMeasure (α := α) μ) (n : ℕ) :
    ∃ c : ENNReal, c ≠ 0 ∧ Dominates (E.xi) μ c ∧
      relEntropy μ (E.xi) n ≤ Real.log (1 / c.toReal) := by
  classical
  -- Get a code for `μ` viewed as a semimeasure.
  obtain ⟨code, hcode⟩ :=
    E.surj_eval μ.toSemimeasure (lscPrefixMeasure_toSemimeasure (μ := μ) hμ)
  have hdom :
      Dominates (E.xi) μ (Mettapedia.Logic.UniversalPrediction.encodeWeight code) := by
    intro x
    have hdom' : Mettapedia.Logic.UniversalPrediction.encodeWeight code * (E.eval code) x ≤ (E.xi) x := by
      simpa [LSCSemimeasureEnumeration.xi, xiSemimeasure] using
        (xi_dominates_index (ν := E.eval) (w := Mettapedia.Logic.UniversalPrediction.encodeWeight)
          (i := code) (x := x))
    -- Rewrite the chosen semimeasure back to `μ`.
    have hcode_x : E.eval code x = μ x := by
      have := congrArg (fun ξ : Semimeasure α => ξ x) hcode
      simpa [PrefixMeasure.toSemimeasure_apply] using this
    simpa [hcode_x] using hdom'
  refine ⟨Mettapedia.Logic.UniversalPrediction.encodeWeight code, E.encodeWeight_ne_zero code, hdom, ?_⟩
  exact relEntropy_le_log_inv_of_dominates (μ := μ) (ξ := E.xi) (hdom := hdom)
    (hc0 := E.encodeWeight_ne_zero code) n

end LSCSemimeasureEnumeration

end Mettapedia.Logic.UniversalPrediction.FiniteAlphabet
