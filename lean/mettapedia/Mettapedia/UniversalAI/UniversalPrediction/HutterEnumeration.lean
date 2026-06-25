import Mettapedia.Computability.HutterComputability
import Mettapedia.UniversalAI.UniversalPrediction.EnumerationBridge

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

namespace Mettapedia.UniversalAI.UniversalPrediction

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

/-- A semimeasure enumeration with Hutter's lower-semicomputability notion.

This is the Chapter‑2 object Hutter ultimately wants: **enumerable semimeasures**.
We keep it parallel to `LSCPrefixMeasureEnumeration` so we can reuse the same
dominance→regret lemmas (which are stated for a true `PrefixMeasure` μ and a
comparison `Semimeasure` ξ). -/
structure LSCSemimeasureEnumeration where
  /-- Code space indexing the enumeration. -/
  Code : Type*
  /-- The code space is countable. -/
  [enc : Encodable Code]
  /-- Interpret a code as a semimeasure. -/
  eval : Code → Semimeasure
  /-- **Enumeration theorem (assumed as an interface)**:
  every lower semicomputable semimeasure has some code. -/
  surj_eval :
    ∀ ξ : Semimeasure, LowerSemicomputableSemimeasure ξ → ∃ c : Code, eval c = ξ

attribute [instance] LSCSemimeasureEnumeration.enc

namespace LSCSemimeasureEnumeration

/-- The universal `encodeWeight` mixture induced by a semimeasure enumeration. -/
noncomputable def xi (E : LSCSemimeasureEnumeration) : Semimeasure :=
  xiEncodeSemimeasure (ι := E.Code) (fun c => E.eval c)

/-- The mixture `ξ` dominates each enumerated component with its code weight. -/
theorem xi_dominates_eval (E : LSCSemimeasureEnumeration) (c : E.Code) :
    Dominates (E.xi) (E.eval c) (encodeWeight c) := by
  intro x
  simpa [LSCSemimeasureEnumeration.xi] using
    (xiEncode_dominates_index (ι := E.Code) (ν := fun d => E.eval d) c x)

theorem encodeWeight_ne_zero (E : LSCSemimeasureEnumeration) (c : E.Code) :
    encodeWeight c ≠ 0 := by
  unfold encodeWeight
  exact pow_ne_zero _ (by simp)

theorem lscPrefixMeasure_toSemimeasure (μ : PrefixMeasure)
    (hμ : LowerSemicomputablePrefixMeasure μ) : LowerSemicomputableSemimeasure μ.toSemimeasure := by
  -- Same underlying `toReal` function, since `μ.toSemimeasure x = μ x`.
  simpa [LowerSemicomputableSemimeasure, LowerSemicomputablePrefixMeasure] using hμ

/-- Convenience lemma: dominance→regret for any lower-semicomputable **measure** μ,
using the universal mixture induced by an **enumeration of semimeasures**. -/
theorem relEntropy_le_log_inv_of_LSC (E : LSCSemimeasureEnumeration) (μ : PrefixMeasure)
    (hμ : LowerSemicomputablePrefixMeasure μ) (n : ℕ) :
    ∃ c : ENNReal, c ≠ 0 ∧ Dominates (E.xi) μ c ∧
      relEntropy μ (E.xi) n ≤ Real.log (1 / c.toReal) := by
  classical
  -- Get a code for `μ` viewed as a semimeasure.
  obtain ⟨code, hcode⟩ :=
    E.surj_eval μ.toSemimeasure (lscPrefixMeasure_toSemimeasure (μ := μ) hμ)
  have hdom : Dominates (E.xi) μ (encodeWeight code) := by
    intro x
    simpa [hcode, PrefixMeasure.toSemimeasure_apply] using (E.xi_dominates_eval code x)
  refine ⟨encodeWeight code, E.encodeWeight_ne_zero code, hdom, ?_⟩
  exact relEntropy_le_log_inv_of_dominates (μ := μ) (ξ := E.xi) (hdom := hdom)
    (hc0 := E.encodeWeight_ne_zero code) n

end LSCSemimeasureEnumeration

end HutterEnumeration

end Mettapedia.UniversalAI.UniversalPrediction
