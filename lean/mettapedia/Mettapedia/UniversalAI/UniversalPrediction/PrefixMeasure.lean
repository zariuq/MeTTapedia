import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mettapedia.UniversalAI.UniversalPrediction

/-!
# Prefix Measures on Binary Strings (Hutter Chapter 3)

Hutter (2005) works extensively with *prefix probabilities* `μ(x)` for finite strings `x : 𝔹*`.

For a genuine probability measure on infinite sequences, these satisfy the **cylinder partition**
equations:

* `μ(ε) = 1`
* `μ(x) = μ(x0) + μ(x1)`

This file packages that interface as `PrefixMeasure` and provides:

* coercion to the existing `Semimeasure` API (by weakening equality to inequality)
* the induced finite-horizon distribution `PMF (Fin n → Bool)` of length-`n` prefixes

This is a convenient formal “bridge” for Chapter 3: we can reason about prediction using
finite prefixes without committing to a full measure-theoretic development on `𝔹^ℕ`.
-/

noncomputable section

namespace Mettapedia.UniversalAI.UniversalPrediction

open scoped Classical BigOperators

/-- A probability measure on cylinder events, represented as a function on finite prefixes. -/
structure PrefixMeasure where
  /-- Prefix probability `μ(x)` for a finite string `x`. -/
  toFun : BinString → ENNReal
  /-- Normalization: `μ(ε) = 1`. -/
  root_eq_one' : toFun [] = 1
  /-- Cylinder partition: `μ(x) = μ(x0) + μ(x1)`. -/
  additive' : ∀ x : BinString, toFun (x ++ [false]) + toFun (x ++ [true]) = toFun x

instance : CoeFun PrefixMeasure (fun _ => BinString → ENNReal) where
  coe := PrefixMeasure.toFun

namespace PrefixMeasure

variable (μ : PrefixMeasure)

/-- A prefix measure is (in particular) a semimeasure. -/
def toSemimeasure : Semimeasure :=
  { toFun := μ
    superadditive' := by
      intro x
      exact le_of_eq (μ.additive' x)
    root_le_one' := by
      exact le_of_eq μ.root_eq_one' }

@[simp]
theorem toSemimeasure_apply (x : BinString) : μ.toSemimeasure x = μ x := rfl

@[simp]
theorem toSemimeasure_root : μ.toSemimeasure [] = 1 := by
  simp [toSemimeasure, μ.root_eq_one']

@[simp]
theorem toSemimeasure_additive (x : BinString) :
    μ.toSemimeasure (x ++ [false]) + μ.toSemimeasure (x ++ [true]) = μ.toSemimeasure x := by
  simpa [toSemimeasure] using μ.additive' x

end PrefixMeasure

/-! ## Mixtures of prefix measures -/

/-- Mixture of prefix measures with weights summing to 1, yielding a prefix measure. -/
noncomputable def xiPrefixMeasure {ι : Type*} (ν : ι → PrefixMeasure) (w : ι → ENNReal)
    (hw : (∑' i : ι, w i) = 1) : PrefixMeasure :=
  { toFun := fun x => xiFun (fun i => (ν i).toSemimeasure) w x
    root_eq_one' := by
      unfold xiFun
      have h :
          (∑' i : ι, w i * (ν i).toSemimeasure []) = ∑' i : ι, w i := by
        refine tsum_congr ?_
        intro i
        simp [PrefixMeasure.toSemimeasure, (ν i).root_eq_one']
      rw [h]
      simp [hw]
    additive' := by
      intro x
      unfold xiFun
      have hsum :
          (∑' i, w i * (ν i).toSemimeasure (x ++ [false])) +
              (∑' i, w i * (ν i).toSemimeasure (x ++ [true])) =
            ∑' i, (w i * (ν i).toSemimeasure (x ++ [false]) + w i * (ν i).toSemimeasure (x ++ [true])) := by
        simpa using
          (ENNReal.tsum_add (f := fun i => w i * (ν i).toSemimeasure (x ++ [false]))
            (g := fun i => w i * (ν i).toSemimeasure (x ++ [true]))).symm
      calc
        (∑' i, w i * (ν i).toSemimeasure (x ++ [false])) +
            (∑' i, w i * (ν i).toSemimeasure (x ++ [true]))
            = ∑' i, (w i * (ν i).toSemimeasure (x ++ [false]) + w i * (ν i).toSemimeasure (x ++ [true])) := hsum
        _ = ∑' i, w i * ((ν i).toSemimeasure (x ++ [false]) + (ν i).toSemimeasure (x ++ [true])) := by
              refine tsum_congr ?_
              intro i
              simp [mul_add]
        _ = ∑' i, w i * (ν i).toSemimeasure x := by
              refine tsum_congr ?_
              intro i
              simpa using congrArg (fun t => w i * t) ((ν i).toSemimeasure_additive x)
        _ = ∑' i, w i * (ν i).toSemimeasure x := rfl }

/-! ## Finite-horizon distributions of prefixes -/

/-- The probability mass function on length-`n` bitstrings induced by a prefix measure. -/
noncomputable def prefixPMF (μ : PrefixMeasure) (n : ℕ) : PMF (Fin n → Bool) :=
  ⟨fun f => μ (List.ofFn f),
    by
      classical
      -- `PMF` is `HasSum _ 1`; for finite spaces we can show this by a finite sum computation.
      -- We prove `∑ f, μ(ofFn f) = 1` by induction on `n`, splitting by the last bit.
      have hsum : (∑ f : Fin n → Bool, μ (List.ofFn f)) = 1 := by
        induction n with
        | zero =>
          -- There is exactly one `Fin 0 → Bool`, and its `ofFn` list is `[]`.
          simp [μ.root_eq_one']
        | succ n ih =>
          -- Rewrite the sum using `Fin.snocEquiv` (split into initial `n` bits and the last bit).
          have hEquiv :
              (∑ p : Bool × (Fin n → Bool),
                    μ (List.ofFn ((Fin.snocEquiv fun _ : Fin (n + 1) => Bool) p))) =
                ∑ f : Fin (n + 1) → Bool, μ (List.ofFn f) := by
            refine Fintype.sum_equiv (Fin.snocEquiv fun _ : Fin (n + 1) => Bool)
              (fun p => μ (List.ofFn ((Fin.snocEquiv fun _ : Fin (n + 1) => Bool) p)))
              (fun f => μ (List.ofFn f)) ?_
            intro p
            rfl
          -- Replace `List.ofFn (Fin.snoc g b)` with `List.ofFn g ++ [b]`.
          have hOfFn : ∀ (b : Bool) (g : Fin n → Bool),
              μ (List.ofFn (Fin.snoc g b)) = μ (List.ofFn g ++ [b]) := by
            intro b g
            have hlist :
                List.ofFn (Fin.snoc g b) = (List.ofFn g).concat b := by
              simpa [List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last] using
                (List.ofFn_succ' (f := Fin.snoc g b))
            rw [hlist]
            simp [List.concat_eq_append]
          calc
            (∑ f : Fin (n + 1) → Bool, μ (List.ofFn f))
                = ∑ p : Bool × (Fin n → Bool),
                    μ (List.ofFn ((Fin.snocEquiv fun _ : Fin (n + 1) => Bool) p)) := by
                      simpa using hEquiv.symm
            _ = ∑ b : Bool, ∑ g : Fin n → Bool, μ (List.ofFn (Fin.snoc g b)) := by
                  -- Uncurry, and simplify `snocEquiv` into `Fin.snoc`.
                  simp [Fintype.sum_prod_type, Fin.snocEquiv]
            _ = ∑ g : Fin n → Bool, (μ (List.ofFn g ++ [false]) + μ (List.ofFn g ++ [true])) := by
                  -- Swap the order of summation (`Bool` ↔ prefix), then evaluate the inner `Bool` sum.
                  have hswap :
                      (∑ b : Bool, ∑ g : Fin n → Bool, μ (List.ofFn (Fin.snoc g b))) =
                        ∑ g : Fin n → Bool, ∑ b : Bool, μ (List.ofFn (Fin.snoc g b)) := by
                    simpa using
                      (Finset.sum_comm (s := (Finset.univ : Finset Bool))
                        (t := (Finset.univ : Finset (Fin n → Bool)))
                        (f := fun b g => μ (List.ofFn (Fin.snoc g b))))
                  rw [hswap]
                  refine Fintype.sum_congr
                    (fun g : Fin n → Bool => ∑ b : Bool, μ (List.ofFn (Fin.snoc g b)))
                    (fun g : Fin n → Bool =>
                      μ (List.ofFn g ++ [false]) + μ (List.ofFn g ++ [true])) ?_
                  intro g
                  calc
                    (∑ b : Bool, μ (List.ofFn (Fin.snoc g b))) =
                        μ (List.ofFn (Fin.snoc g true)) + μ (List.ofFn (Fin.snoc g false)) := by
                          exact
                            (Fintype.sum_bool (fun b : Bool => μ (List.ofFn (Fin.snoc g b))))
                    _ = μ (List.ofFn g ++ [true]) + μ (List.ofFn g ++ [false]) := by
                          rw [hOfFn true g, hOfFn false g]
                    _ = μ (List.ofFn g ++ [false]) + μ (List.ofFn g ++ [true]) := by
                          simp [add_comm]
            _ = ∑ g : Fin n → Bool, μ (List.ofFn g) := by
                  refine Fintype.sum_congr
                    (fun g : Fin n → Bool => μ (List.ofFn g ++ [false]) + μ (List.ofFn g ++ [true]))
                    (fun g : Fin n → Bool => μ (List.ofFn g)) ?_
                  intro g
                  simpa using μ.additive' (List.ofFn g)
            _ = 1 := ih
      -- Finish: convert the finite sum identity into a `HasSum`.
      simpa [hsum] using (hasSum_fintype (fun f : Fin n → Bool => μ (List.ofFn f)))⟩

/-- For a prefix measure, the one-step conditionals sum to `1` whenever `μ(x) ≠ 0`. -/
theorem conditionalENN_bool_sum (μ : PrefixMeasure) (x : BinString) (hx0 : μ x ≠ 0) :
    conditionalENN μ.toSemimeasure [false] x + conditionalENN μ.toSemimeasure [true] x = 1 := by
  have hx0' : μ.toSemimeasure x ≠ 0 := by
    simpa using hx0
  have hxTop : μ.toSemimeasure x ≠ (⊤ : ENNReal) :=
    semimeasure_ne_top μ.toSemimeasure x
  calc
    conditionalENN μ.toSemimeasure [false] x + conditionalENN μ.toSemimeasure [true] x =
        (μ.toSemimeasure (x ++ [false]) + μ.toSemimeasure (x ++ [true])) / μ.toSemimeasure x := by
          simp [conditionalENN, ENNReal.div_add_div_same]
    _ = μ.toSemimeasure x / μ.toSemimeasure x := by
          rw [μ.toSemimeasure_additive x]
    _ = 1 := ENNReal.div_self hx0' hxTop

end Mettapedia.UniversalAI.UniversalPrediction
