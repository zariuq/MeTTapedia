import Mettapedia.Logic.UniversalPrediction.HutterEnumerationTheorem

/-!
# Levin/Hutter Enumeration Theorem (Lower-Semicomputable Semimeasures)

This file is the semimeasure analogue of `HutterEnumerationTheorem.lean`.

Hutter (2005), Chapter 2, treats **enumerable semimeasures** as the canonical
computability class for universal prediction.  Our Chapter‑3 regret bounds are
stated for a true environment `μ : PrefixMeasure` and a comparison
`ξ : Semimeasure`, so the main deliverable here is:

* a concrete, surjective enumeration of all lower-semicomputable semimeasures, and
* a “turn‑on” lemma that instantiates dominance→regret with the induced universal
  mixture `ξ := xiEncodeSemimeasure eval`.

The construction follows the same pattern as the prefix-measure enumeration:
extract `Nat.Partrec.Code` from a dyadic witness and choose the unique semimeasure
realized by that code.
-/

noncomputable section

namespace Mettapedia.Logic.UniversalPrediction

open scoped Classical

namespace HutterEnumerationTheoremSemimeasure

open Mettapedia.Computability.Hutter
open HutterEnumeration

open HutterEnumerationTheorem

/-! ## Code witnesses (semimeasure version) -/

/-- A code `c` witnesses a semimeasure `ξ` if `approxOfCode c` gives a monotone dyadic
approximation converging to `ξ(x)` for every prefix `x`. -/
def CodeWitness (c : Nat.Partrec.Code) (ξ : Semimeasure) : Prop :=
  (∀ x : BinString, Monotone (fun n => dyadic (approxOfCode c x n) n)) ∧
    ∀ x : BinString,
      Filter.Tendsto (fun n => dyadic (approxOfCode c x n) n) Filter.atTop (nhds ((ξ x).toReal))

theorem codeWitness_unique (c : Nat.Partrec.Code) {ξ₁ ξ₂ : Semimeasure}
    (h₁ : CodeWitness c ξ₁) (h₂ : CodeWitness c ξ₂) : ξ₁ = ξ₂ := by
  -- Two limits of the same sequence must agree pointwise.
  have hEq_toReal : ∀ x : BinString, (ξ₁ x).toReal = (ξ₂ x).toReal := by
    intro x
    exact tendsto_nhds_unique (h₁.2 x) (h₂.2 x)
  -- `ENNReal.toReal` is injective on semimeasure values (bounded by `1`).
  have hEq_val : ∀ x : BinString, ξ₁ x = ξ₂ x := by
    intro x
    have hTop₁ : ξ₁ x ≠ (⊤ : ENNReal) := by
      have hle : ξ₁ x ≤ 1 := semimeasure_le_one (μ := ξ₁) x
      exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
    have hTop₂ : ξ₂ x ≠ (⊤ : ENNReal) := by
      have hle : ξ₂ x ≤ 1 := semimeasure_le_one (μ := ξ₂) x
      exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
    exact (ENNReal.toReal_eq_toReal_iff' hTop₁ hTop₂).1 (hEq_toReal x)
  -- Conclude equality of structures by proof irrelevance on the Prop fields.
  cases ξ₁ with
  | mk f₁ s₁ r₁ =>
    cases ξ₂ with
    | mk f₂ s₂ r₂ =>
      have hf : f₁ = f₂ := funext hEq_val
      cases hf
      have hs : s₁ = s₂ := Subsingleton.elim _ _
      have hr : r₁ = r₂ := Subsingleton.elim _ _
      cases hs
      cases hr
      rfl

/-! ## A concrete enumeration of LSC semimeasures -/

/-- Interpret a code as the (unique) semimeasure it lower-semicomputes, if any;
otherwise return a harmless default semimeasure. -/
noncomputable def evalLSC (c : Nat.Partrec.Code) : Semimeasure :=
  if h : ∃ ξ : Semimeasure, CodeWitness c ξ then
    Classical.choose h
  else
    -- Any fixed semimeasure works as a default; use the uniform cylinder measure's semimeasure.
    HutterEnumerationTheorem.uniformPrefixMeasure.toSemimeasure

theorem evalLSC_spec {c : Nat.Partrec.Code} (h : ∃ ξ : Semimeasure, CodeWitness c ξ) :
    CodeWitness c (evalLSC c) := by
  classical
  simp [evalLSC, h, Classical.choose_spec]

theorem surj_evalLSC :
    ∀ ξ : Semimeasure, LowerSemicomputableSemimeasure ξ → ∃ c : Nat.Partrec.Code, evalLSC c = ξ := by
  intro ξ hξ
  rcases hξ with ⟨a, ha_comp, ha_mono, ha_tendsto⟩
  rcases exists_code_of_computable₂ (a := a) ha_comp with ⟨c, hc⟩
  -- Show this code witnesses `ξ`.
  have hW : CodeWitness c ξ := by
    refine ⟨?_, ?_⟩
    · intro x
      simpa [hc] using ha_mono x
    · intro x
      simpa [hc] using ha_tendsto x
  have hex : ∃ ξ' : Semimeasure, CodeWitness c ξ' := ⟨ξ, hW⟩
  refine ⟨c, ?_⟩
  -- `evalLSC c` chooses the unique semimeasure witnessed by `c`.
  have hChosen : CodeWitness c (evalLSC c) := evalLSC_spec (c := c) hex
  exact codeWitness_unique c hChosen hW

/-- The concrete `LSCSemimeasureEnumeration` (Levin/Hutter enumeration theorem, semimeasure form). -/
noncomputable def lscSemimeasureEnumeration : HutterEnumeration.LSCSemimeasureEnumeration :=
  { Code := Nat.Partrec.Code
    eval := evalLSC
    surj_eval := surj_evalLSC }

end HutterEnumerationTheoremSemimeasure

open FiniteHorizon

/-- Convenience: dominance→regret bound specialized to the concrete LSC semimeasure enumeration. -/
theorem relEntropy_le_log_inv_of_LSC_semimeasure_concrete (μ : PrefixMeasure)
    (hμ : HutterEnumeration.LowerSemicomputablePrefixMeasure μ) (n : ℕ) :
    ∃ c : ENNReal, c ≠ 0 ∧
      Dominates (HutterEnumerationTheoremSemimeasure.lscSemimeasureEnumeration.xi) μ c ∧
        relEntropy μ (HutterEnumerationTheoremSemimeasure.lscSemimeasureEnumeration.xi) n ≤
          Real.log (1 / c.toReal) := by
  simpa [HutterEnumerationTheoremSemimeasure.lscSemimeasureEnumeration,
    HutterEnumeration.LSCSemimeasureEnumeration.xi] using
    (HutterEnumeration.LSCSemimeasureEnumeration.relEntropy_le_log_inv_of_LSC
      (E := HutterEnumerationTheoremSemimeasure.lscSemimeasureEnumeration) (μ := μ) hμ n)

end Mettapedia.Logic.UniversalPrediction

