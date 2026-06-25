import Mettapedia.UniversalAI.UniversalPrediction
import Mettapedia.UniversalAI.UniversalPrediction.FiniteHorizon

/-!
# Enumeration Bridge (Chapter 2 → Chapter 3)

This file packages the *missing interface* needed to connect:

* a universal mixture `ξ` (Chapter 3), and
* “all computable / enumerable environments” (Chapter 2)

without committing to a particular machine model.

The idea is:

1. Assume we have a *countable code space* `Code` and an evaluator `eval : Code → PrefixMeasure`.
2. Form the universal mixture

   `ξ := xiEncodeSemimeasure (fun c => (eval c).toSemimeasure)`

   using the provably summable weights `encodeWeight`.
3. Then `ξ` trivially dominates each component `eval c` with constant `encodeWeight c`.
4. Therefore all Chapter‑3 dominance → regret bounds apply *immediately* once we have an
   enumeration theorem stating that every “computable” environment has some code.

This is the clean “mixture route”: it keeps the deep Levin / machine representation theorems
out of the critical path while making the dependency explicit and localized.
-/

noncomputable section

namespace Mettapedia.UniversalAI.UniversalPrediction
namespace EnumerationBridge

open scoped Classical BigOperators ENNReal
open FiniteHorizon

/-- An abstract enumeration of (cylinder) probability measures on prefixes.

`IsComputable` is intentionally left abstract: in different developments this can mean
"computable", "lower semicomputable", "enumerable semimeasure", etc.

The only thing Chapter 3 needs is: *there exists a code for each environment in-scope*. -/
structure PrefixMeasureEnumeration where
  /-- Code space indexing the enumeration. -/
  Code : Type*
  /-- The code space is countable. -/
  [enc : Encodable Code]
  /-- Interpret a code as a prefix measure (a genuine measure on cylinders). -/
  eval : Code → PrefixMeasure
  /-- Predicate selecting the class of environments this enumeration is meant to cover. -/
  IsComputable : PrefixMeasure → Prop
  /-- **Enumeration bridge (placeholder interface)**:
  every environment in scope has some code in the enumeration. -/
  surj_eval : ∀ μ : PrefixMeasure, IsComputable μ → ∃ c : Code, eval c = μ

attribute [instance] PrefixMeasureEnumeration.enc

namespace PrefixMeasureEnumeration

/-- The universal mixture induced by an enumeration, using the summable `encodeWeight`.

This is a semimeasure `ξ` (not necessarily a measure), exactly as in Hutter Chapter 3. -/
noncomputable def xi (E : PrefixMeasureEnumeration) : Semimeasure :=
  xiEncodeSemimeasure (ι := E.Code) (fun c => (E.eval c).toSemimeasure)

/-- The mixture `ξ` dominates each enumerated environment with its code weight. -/
theorem xi_dominates_eval (E : PrefixMeasureEnumeration) (c : E.Code) :
    Dominates (E.xi) (E.eval c) (encodeWeight c) := by
  intro x
  -- `xiEncode_dominates_index` gives componentwise dominance for the semimeasure mixture.
  simpa [PrefixMeasureEnumeration.xi, PrefixMeasure.toSemimeasure_apply] using
    (xiEncode_dominates_index (ι := E.Code) (ν := fun d => (E.eval d).toSemimeasure) c x)

theorem encodeWeight_ne_zero (E : PrefixMeasureEnumeration) (c : E.Code) :
    encodeWeight c ≠ 0 := by
  -- `encodeWeight c = (1/2)^(encode c + 1)`, and `1/2 ≠ 0`.
  unfold encodeWeight
  exact pow_ne_zero _ (by simp)

/-- Dominance for any in-scope environment, via the surjectivity bridge. -/
theorem exists_dominance_of_IsComputable (E : PrefixMeasureEnumeration) (μ : PrefixMeasure)
    (hμ : E.IsComputable μ) :
    ∃ c : E.Code, Dominates (E.xi) μ (encodeWeight c) ∧ encodeWeight c ≠ 0 := by
  obtain ⟨c, rfl⟩ := E.surj_eval μ hμ
  refine ⟨c, E.xi_dominates_eval c, E.encodeWeight_ne_zero c⟩

/-- **Log-loss regret bound** (finite horizon) for any in-scope environment.

This is the standard Chapter‑3 consequence of dominance:
`Dₙ(μ‖ξ) ≤ log(1/c)` where `c` is the dominance constant.
-/
theorem relEntropy_le_log_inv_of_IsComputable (E : PrefixMeasureEnumeration) (μ : PrefixMeasure)
    (hμ : E.IsComputable μ) (n : ℕ) :
    ∃ c : ENNReal, c ≠ 0 ∧ Dominates (E.xi) μ c ∧
      relEntropy μ (E.xi) n ≤ Real.log (1 / c.toReal) := by
  obtain ⟨code, hdom, hc0⟩ := E.exists_dominance_of_IsComputable μ hμ
  refine ⟨encodeWeight code, hc0, hdom, ?_⟩
  exact relEntropy_le_log_inv_of_dominates (μ := μ) (ξ := E.xi) (hdom := hdom) (hc0 := hc0) n

end PrefixMeasureEnumeration

end EnumerationBridge
end Mettapedia.UniversalAI.UniversalPrediction

