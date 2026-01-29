import Mathlib.Computability.PartrecCode
import Mettapedia.Logic.UniversalPrediction.HutterEnumeration

/-!
# Levin/Hutter Enumeration Theorem (Lower-Semicomputable Prefix Measures)

This file turns the *interface stub* in `Mettapedia/Logic/UniversalPrediction/HutterEnumeration.lean`
into a concrete `LSCPrefixMeasureEnumeration` instance.

## What this provides (and what it does not)

* We work with Hutter's notion of **lower semicomputability** via computable monotone dyadic
  approximations (`Mettapedia/Computability/HutterComputability.lean`).
* From such an approximation `a`, we extract a *partial recursive code* `c : Nat.Partrec.Code`
  using mathlib's universal partial recursive function (`Nat.Partrec.Code.exists_code`).
* We then build a *surjective enumeration* of all lower semicomputable `PrefixMeasure`s, indexed
  by `Nat.Partrec.Code`, sufficient to instantiate the Chapter‑3 dominance→regret theorems.

This is intentionally the “mixture-route” level needed for `EnumerationBridge`:
we do **not** yet prove a full representation theorem by monotone machines or prefix-free UTMs.
The code `c` is a concrete computational witness for the dyadic approximation, which is the
effective content required by `LowerSemicomputable`.
-/

noncomputable section

namespace Mettapedia.Logic.UniversalPrediction

open scoped Classical

namespace HutterEnumerationTheorem

open Mettapedia.Computability.Hutter
open HutterEnumeration

/-! ## A canonical default prefix measure -/

/-- The uniform Bernoulli(1/2) cylinder measure: `μ(x) = (1/2)^{|x|}`. -/
noncomputable def uniformPrefixMeasure : PrefixMeasure :=
  { toFun := fun x => (2⁻¹ : ENNReal) ^ x.length
    root_eq_one' := by
      simp
    additive' := by
      intro x
      -- `|x ++ [b]| = |x| + 1`
      have hlen : (x ++ [false]).length = x.length + 1 := by simp
      have hlen' : (x ++ [true]).length = x.length + 1 := by simp
      -- Reduce to the algebraic identity `(1/2)^(n+1) + (1/2)^(n+1) = (1/2)^n`.
      simp [hlen, hlen', pow_succ]
      -- `2⁻¹ + 2⁻¹ = 1` in `ℝ≥0∞`.
      have hle : (2⁻¹ : ENNReal) ≤ (1 : ENNReal) := by
        -- Avoid a linter warning about `simp` being a no-op on numerals.
        have : (1 : ENNReal) ≤ (2 : ENNReal) := by
          exact_mod_cast (by decide : (1 : ℕ) ≤ 2)
        exact ENNReal.inv_le_one.2 this
      have hhalf : (2⁻¹ : ENNReal) + (2⁻¹ : ENNReal) = (1 : ENNReal) := by
        have h : (2⁻¹ : ENNReal) + ((1 : ENNReal) - (2⁻¹ : ENNReal)) = (1 : ENNReal) := by
          simpa using (add_tsub_cancel_of_le hle)
        simpa [ENNReal.one_sub_inv_two] using h
      -- Finish by factoring out `2⁻¹ ^ |x|`.
      calc
        (2⁻¹ : ENNReal) ^ x.length * (2⁻¹ : ENNReal) + (2⁻¹ : ENNReal) ^ x.length * (2⁻¹ : ENNReal)
            = (2⁻¹ : ENNReal) ^ x.length * ((2⁻¹ : ENNReal) + (2⁻¹ : ENNReal)) := by
                simpa using
                  (mul_add ((2⁻¹ : ENNReal) ^ x.length) (2⁻¹ : ENNReal) (2⁻¹ : ENNReal)).symm
        _ = (2⁻¹ : ENNReal) ^ x.length * 1 := by simp [hhalf]
        _ = (2⁻¹ : ENNReal) ^ x.length := by simp }

/-! ## Extracting dyadic witnesses from `Nat.Partrec.Code` -/

/-- Interpret a `Nat.Partrec.Code` as a total `ℕ`-valued function on `(BinString × ℕ)` by
running the code on `encode (x,n)` and defaulting to `0` if it diverges. -/
noncomputable def approxOfCode (c : Nat.Partrec.Code) (x : BinString) (n : ℕ) : ℕ :=
  -- `Nat.Partrec.Code.eval` returns a `Part ℕ` encoding the *encoded* output.
  -- We totalize it using classical `toOption`, then decode the output back to `ℕ`.
  match (Nat.Partrec.Code.eval c (Encodable.encode (x, n))).toOption with
  | none => 0
  | some k => (Encodable.decode (α := ℕ) k).getD 0

/-- A code `c` is a *witness* that `μ` is lower semicomputable if the dyadic sequence obtained
from `approxOfCode c` converges to `μ(x)` for every `x`. -/
def CodeWitness (c : Nat.Partrec.Code) (μ : PrefixMeasure) : Prop :=
  (∀ x : BinString, Monotone (fun n => dyadic (approxOfCode c x n) n)) ∧
    ∀ x : BinString,
      Filter.Tendsto (fun n => dyadic (approxOfCode c x n) n) Filter.atTop (nhds ((μ x).toReal))

theorem codeWitness_unique (c : Nat.Partrec.Code) {μ₁ μ₂ : PrefixMeasure}
    (h₁ : CodeWitness c μ₁) (h₂ : CodeWitness c μ₂) : μ₁ = μ₂ := by
  -- Two limits of the same sequence must agree pointwise.
  have hEq_toReal : ∀ x : BinString, (μ₁ x).toReal = (μ₂ x).toReal := by
    intro x
    exact tendsto_nhds_unique (h₁.2 x) (h₂.2 x)
  -- `ENNReal.toReal` is injective on the range of a prefix measure (values are ≤ 1, hence ≠ ⊤).
  have hEq_val : ∀ x : BinString, μ₁ x = μ₂ x := by
    intro x
    have hTop₁ : μ₁ x ≠ (⊤ : ENNReal) := by
      -- A prefix measure is a semimeasure, hence bounded by 1.
      have hle : μ₁.toSemimeasure x ≤ 1 := semimeasure_le_one (μ := μ₁.toSemimeasure) x
      have : μ₁.toSemimeasure x ≠ (⊤ : ENNReal) := by
        exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
      simpa using this
    have hTop₂ : μ₂ x ≠ (⊤ : ENNReal) := by
      have hle : μ₂.toSemimeasure x ≤ 1 := semimeasure_le_one (μ := μ₂.toSemimeasure) x
      have : μ₂.toSemimeasure x ≠ (⊤ : ENNReal) := by
        exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
      simpa using this
    exact (ENNReal.toReal_eq_toReal_iff' hTop₁ hTop₂).1 (hEq_toReal x)
  -- Conclude equality of structures by proof irrelevance on the Prop fields.
  cases μ₁ with
  | mk f₁ r₁ a₁ =>
    cases μ₂ with
    | mk f₂ r₂ a₂ =>
      have hf : f₁ = f₂ := funext hEq_val
      cases hf
      -- Now only Prop fields differ.
      have hr : r₁ = r₂ := Subsingleton.elim _ _
      have ha : a₁ = a₂ := Subsingleton.elim _ _
      cases hr
      cases ha
      rfl

/-! ## From a dyadic witness to a code -/

/-- If `a` is a total computable dyadic witness (in Hutter's sense), then it has a
`Nat.Partrec.Code` which reproduces it on all inputs. -/
theorem exists_code_of_computable₂ (a : BinString → ℕ → ℕ) (ha : Computable₂ a) :
    ∃ c : Nat.Partrec.Code, ∀ x n, approxOfCode c x n = a x n := by
  -- `Computable₂ a` is `Partrec` for the curried function on `(BinString × ℕ)`.
  -- Unfolding `Computable`/`Partrec` exposes a `Nat.Partrec` function on encoded inputs,
  -- which we can then code using `Nat.Partrec.Code.exists_code`.
  classical
  -- Let `f : BinString × ℕ → ℕ` be the uncurried version of `a`.
  let f : (BinString × ℕ) → ℕ := fun p => a p.1 p.2
  have hf : Computable f := ha
  -- `Computable f` is definitionally `Partrec (fun p => (f p : Part ℕ))`.
  have hf' : Partrec (f : (BinString × ℕ) →. ℕ) := hf
  -- Unfold `Partrec` to get a `Nat.Partrec` statement.
  -- The underlying `Nat.Partrec` function computes `f` on `encode`d inputs.
  have hfNat :
      Nat.Partrec
        (fun n : ℕ =>
          Part.bind (Encodable.decode (α := BinString × ℕ) n) fun p =>
            (f p : Part ℕ).map Encodable.encode) := by
    simpa [Partrec] using hf'
  rcases (Nat.Partrec.Code.exists_code).1 hfNat with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro x n
  unfold approxOfCode
  -- Use the computed code equality.
  have hEval :
      Nat.Partrec.Code.eval c (Encodable.encode (x, n)) =
        Part.bind (Encodable.decode (α := BinString × ℕ) (Encodable.encode (x, n)))
          (fun p => (f p : Part ℕ).map Encodable.encode) := by
    simpa using congrArg (fun g => g (Encodable.encode (x, n))) hc
  -- Reduce `decode (encode (x,n))` and simplify.
  have hdecode :
      Encodable.decode (α := BinString × ℕ) (Encodable.encode (x, n)) = some (x, n) :=
    Encodable.encodek (x, n)
  have hEval' :
      Nat.Partrec.Code.eval c (Encodable.encode (x, n)) = Part.some (Encodable.encode (a x n)) := by
    -- `bind` over `decode (encode ...)` and `map` over `some` are definitional for `Part`.
    calc
      Nat.Partrec.Code.eval c (Encodable.encode (x, n))
          = Part.bind (Encodable.decode (α := BinString × ℕ) (Encodable.encode (x, n)))
              (fun p => (f p : Part ℕ).map Encodable.encode) := hEval
      _ = Part.bind (some (x, n)) (fun p => (f p : Part ℕ).map Encodable.encode) := by
            simp
      _ = (f (x, n) : Part ℕ).map Encodable.encode := by
            simp [Part.bind_some]
      _ = Part.some (Encodable.encode (f (x, n))) := by
            simp [Part.map_some]
      _ = Part.some (Encodable.encode (a x n)) := rfl
  -- Now `approxOfCode` is just reading back the encoded value.
  rw [hEval']
  simp

/-! ## A concrete enumeration of LSC prefix measures -/

/-- Enumerate all lower semicomputable `PrefixMeasure`s by their dyadic-witness codes. -/
noncomputable def evalLSC (c : Nat.Partrec.Code) : PrefixMeasure :=
  if h : ∃ μ : PrefixMeasure, CodeWitness c μ then
    Classical.choose h
  else
    uniformPrefixMeasure

theorem evalLSC_spec {c : Nat.Partrec.Code} (h : ∃ μ : PrefixMeasure, CodeWitness c μ) :
    CodeWitness c (evalLSC c) := by
  classical
  simp [evalLSC, h, Classical.choose_spec]

theorem surj_evalLSC :
    ∀ μ : PrefixMeasure, LowerSemicomputablePrefixMeasure μ → ∃ c : Nat.Partrec.Code, evalLSC c = μ := by
  intro μ hμ
  rcases hμ with ⟨a, ha_comp, ha_mono, ha_tendsto⟩
  rcases exists_code_of_computable₂ (a := a) ha_comp with ⟨c, hc⟩
  -- Show this code witnesses `μ`.
  have hW : CodeWitness c μ := by
    refine ⟨?_, ?_⟩
    · intro x
      -- Transfer monotonicity along `hc`.
      simpa [hc] using ha_mono x
    · intro x
      -- Transfer convergence along `hc`.
      simpa [hc] using ha_tendsto x
  have hex : ∃ μ' : PrefixMeasure, CodeWitness c μ' := ⟨μ, hW⟩
  refine ⟨c, ?_⟩
  -- `evalLSC c` chooses the unique measure witnessed by `c`.
  have hChosen : CodeWitness c (evalLSC c) := evalLSC_spec (c := c) hex
  exact codeWitness_unique c hChosen hW

/-- The concrete `LSCPrefixMeasureEnumeration` promised by `HutterEnumeration.lean`. -/
noncomputable def lscPrefixMeasureEnumeration : HutterEnumeration.LSCPrefixMeasureEnumeration :=
  { Code := Nat.Partrec.Code
    eval := evalLSC
    surj_eval := surj_evalLSC }

end HutterEnumerationTheorem

/-! ## Turning on the Chapter‑3 regret bounds -/

open EnumerationBridge
open FiniteHorizon

/-- Convenience: the dominance→regret bound specialized to the concrete Levin/Hutter enumeration. -/
theorem relEntropy_le_log_inv_of_LSC_concrete (μ : PrefixMeasure)
    (hμ : HutterEnumeration.LowerSemicomputablePrefixMeasure μ) (n : ℕ) :
    ∃ c : ENNReal, c ≠ 0 ∧
      Dominates (HutterEnumerationTheorem.lscPrefixMeasureEnumeration.toPrefixMeasureEnumeration.xi) μ c ∧
        relEntropy μ (HutterEnumerationTheorem.lscPrefixMeasureEnumeration.toPrefixMeasureEnumeration.xi) n ≤
          Real.log (1 / c.toReal) := by
  simpa using
    (HutterEnumeration.LSCPrefixMeasureEnumeration.relEntropy_le_log_inv_of_LSC
      (E := HutterEnumerationTheorem.lscPrefixMeasureEnumeration) (μ := μ) hμ n)

end Mettapedia.Logic.UniversalPrediction
