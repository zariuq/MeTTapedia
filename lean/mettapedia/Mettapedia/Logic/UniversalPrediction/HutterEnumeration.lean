import Mettapedia.Computability.HutterComputability
import Mettapedia.Logic.UniversalPrediction.EnumerationBridge

/-!
# Hutter-Style Computable Enumerations (Bridge Stub)

This file refines the abstract `EnumerationBridge.PrefixMeasureEnumeration` interface by
pinning down a *concrete* notion of “computable / enumerable environment” in the sense of
Hutter (2005), Chapter 2, Definition 2.12:

* **lower semicomputable** real-valued functions (via computable monotone dyadic approximations)

The key point is to make the “real enumeration theorem” dependency explicit:

*If* we have a countable code space `Code` and an evaluator `eval : Code → PrefixMeasure` that is
surjective onto the class of lower semicomputable prefix measures, then all of the Chapter‑3
dominance→regret results in `EnumerationBridge` apply immediately.

This keeps the heavy Levin/representation theorem (turning a computability predicate into an
effective enumeration) out of the critical path, but makes the required assumption precise.
-/

noncomputable section

namespace Mettapedia.Logic.UniversalPrediction

open scoped Classical

namespace HutterEnumeration

open Mettapedia.Computability.Hutter
open EnumerationBridge
open FiniteHorizon

/-- Hutter-style “enumerable / lower semicomputable” semimeasure on binary strings.

We express this via lower semicomputability of the real-valued map `x ↦ (ξ x).toReal`.

Notes:
* For semimeasures/prefix measures in this development, values are bounded by `1`, so `⊤` never
  occurs and `ENNReal.toReal` is faithful on the range. -/
def LowerSemicomputableSemimeasure (ξ : Semimeasure) : Prop :=
  LowerSemicomputable (fun x : BinString => (ξ x).toReal)

/-- Hutter-style “enumerable / lower semicomputable” prefix measure on binary strings. -/
def LowerSemicomputablePrefixMeasure (μ : PrefixMeasure) : Prop :=
  LowerSemicomputable (fun x : BinString => (μ x).toReal)

/-- A `PrefixMeasureEnumeration` whose `IsComputable` predicate is fixed to Hutter’s
lower-semicomputability notion. -/
structure LSCPrefixMeasureEnumeration where
  /-- Code space indexing the enumeration. -/
  Code : Type*
  /-- The code space is countable. -/
  [enc : Encodable Code]
  /-- Interpret a code as a prefix measure. -/
  eval : Code → PrefixMeasure
  /-- **Enumeration theorem (assumed as an interface)**:
  every lower semicomputable prefix measure has some code. -/
  surj_eval :
    ∀ μ : PrefixMeasure, LowerSemicomputablePrefixMeasure μ → ∃ c : Code, eval c = μ

attribute [instance] LSCPrefixMeasureEnumeration.enc

namespace LSCPrefixMeasureEnumeration

/-- View an `LSCPrefixMeasureEnumeration` as the abstract `PrefixMeasureEnumeration`
expected by `EnumerationBridge`. -/
def toPrefixMeasureEnumeration (E : LSCPrefixMeasureEnumeration) :
    PrefixMeasureEnumeration where
  Code := E.Code
  eval := E.eval
  IsComputable := LowerSemicomputablePrefixMeasure
  surj_eval := E.surj_eval

/-- Convenience lemma: log-loss regret bound for any Hutter-lower-semicomputable prefix measure. -/
theorem relEntropy_le_log_inv_of_LSC (E : LSCPrefixMeasureEnumeration) (μ : PrefixMeasure)
    (hμ : LowerSemicomputablePrefixMeasure μ) (n : ℕ) :
    ∃ c : ENNReal, c ≠ 0 ∧ Dominates (E.toPrefixMeasureEnumeration.xi) μ c ∧
      relEntropy μ (E.toPrefixMeasureEnumeration.xi) n ≤ Real.log (1 / c.toReal) := by
  simpa [LSCPrefixMeasureEnumeration.toPrefixMeasureEnumeration] using
    (PrefixMeasureEnumeration.relEntropy_le_log_inv_of_IsComputable
      (E := E.toPrefixMeasureEnumeration) (μ := μ) hμ n)

end LSCPrefixMeasureEnumeration

end HutterEnumeration

end Mettapedia.Logic.UniversalPrediction
