import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.Basic

/-!
# Prefix Measures (Finite Alphabet)

This is the finite-alphabet analogue of `UniversalPrediction/PrefixMeasure.lean`.

For a finite alphabet `α`, a prefix measure assigns a weight `μ(x)` to each finite word `x : List α`
such that:
* `μ([]) = 1`
* `μ(x) = ∑ a : α, μ(x ++ [a])`

This file also defines the induced finite-horizon distribution `prefixPMF μ n : PMF (Fin n → α)`.
-/

noncomputable section

namespace Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet

open scoped Classical BigOperators

/-! ## Prefix measures -/

/-- A probability measure on cylinder events for sequences over a finite alphabet `α`,
represented as a function on finite prefixes `x : List α`. -/
structure PrefixMeasure (α : Type*) [Fintype α] where
  /-- Prefix probability `μ(x)` for a finite word `x`. -/
  toFun : Word α → ENNReal
  /-- Normalization: `μ(ε) = 1`. -/
  root_eq_one' : toFun [] = 1
  /-- Cylinder partition: `μ(x) = ∑ₐ μ(xa)`. -/
  additive' : ∀ x : Word α, (∑ a : α, toFun (x ++ [a])) = toFun x

instance {α : Type*} [Fintype α] : CoeFun (PrefixMeasure α) (fun _ => Word α → ENNReal) where
  coe := PrefixMeasure.toFun

namespace PrefixMeasure

variable {α : Type*} [Fintype α] (μ : PrefixMeasure α)

/-- A prefix measure is (in particular) a semimeasure. -/
def toSemimeasure : Semimeasure α :=
  { toFun := μ
    superadditive' := by
      intro x
      exact le_of_eq (μ.additive' x)
    root_le_one' := by
      exact le_of_eq μ.root_eq_one' }

@[simp] theorem toSemimeasure_apply (x : Word α) : μ.toSemimeasure x = μ x := rfl

@[simp] theorem toSemimeasure_root : μ.toSemimeasure ([] : Word α) = 1 := by
  simp [toSemimeasure, μ.root_eq_one']

end PrefixMeasure

/-! ## Mixtures of prefix measures -/

/-- Mixture of prefix measures with weights summing to `1`, yielding a prefix measure. -/
noncomputable def xiPrefixMeasure {α ι : Type*} [Fintype α] (ν : ι → PrefixMeasure α) (w : ι → ENNReal)
    (hw : (∑' i : ι, w i) = 1) : PrefixMeasure α :=
  { toFun := fun x => xiFun (fun i => (ν i).toSemimeasure) w x
    root_eq_one' := by
      -- `xi([]) = ∑' i, w i * μ_i([]) = ∑' i, w i`.
      unfold xiFun
      -- Each component satisfies `(ν i) [] = 1`, so the mixture root is `∑' i, w i`.
      have h :
          (∑' i : ι, w i * (ν i) ([] : Word α)) = ∑' i : ι, w i := by
        refine tsum_congr ?_
        intro i
        simp [(ν i).root_eq_one']
      -- Unfold `toSemimeasure` in the goal so it matches `h`.
      simp [PrefixMeasure.toSemimeasure, h, hw]
    additive' := by
      intro x
      classical
      -- Same computation as in `xi_superadditive`, but with equality since each component is a measure.
      have hswap :
          (∑ a : α, xiFun (fun i => (ν i).toSemimeasure) w (x ++ [a])) =
            ∑' i : ι, ∑ a : α, w i * (ν i).toSemimeasure (x ++ [a]) := by
        calc
          (∑ a : α, xiFun (fun i => (ν i).toSemimeasure) w (x ++ [a]))
              = ∑' a : α, xiFun (fun i => (ν i).toSemimeasure) w (x ++ [a]) := by
                  simp [tsum_fintype]
          _ = ∑' i : ι, ∑' a : α, w i * (ν i).toSemimeasure (x ++ [a]) := by
                  -- Expand `xiFun` and commute the two `tsum`s.
                  simpa [xiFun, -tsum_fintype] using
                    (ENNReal.tsum_comm (f := fun a i => w i * (ν i).toSemimeasure (x ++ [a])))
          _ = ∑' i : ι, ∑ a : α, w i * (ν i).toSemimeasure (x ++ [a]) := by
                  refine tsum_congr ?_
                  intro i
                  simp [tsum_fintype]
      have hinner :
          (fun i : ι => ∑ a : α, w i * (ν i).toSemimeasure (x ++ [a])) =
            fun i : ι => w i * (ν i).toSemimeasure x := by
        funext i
        -- Unfold `toSemimeasure` and use `additive'` for the component.
        simp [PrefixMeasure.toSemimeasure]
        calc
          (∑ a : α, w i * (ν i) (x ++ [a]))
              = w i * ∑ a : α, (ν i) (x ++ [a]) := by
                  simpa using
                    (Finset.mul_sum (a := w i) (f := fun a : α => (ν i) (x ++ [a]))
                      (s := (Finset.univ : Finset α))).symm
          _ = w i * (ν i) x := by
                  simpa using congrArg (fun t => w i * t) ((ν i).additive' x)
      -- Finish.
      calc
        (∑ a : α, xiFun (fun i => (ν i).toSemimeasure) w (x ++ [a]))
            = ∑' i : ι, ∑ a : α, w i * (ν i).toSemimeasure (x ++ [a]) := hswap
        _ = ∑' i : ι, w i * (ν i).toSemimeasure x := by
              -- Apply `hinner` under the `tsum`.
              simpa using congrArg (fun f : ι → ENNReal => ∑' i : ι, f i) hinner
        _ = xiFun (fun i => (ν i).toSemimeasure) w x := by
              simp [xiFun] }

/-! ## Finite-horizon distributions of prefixes -/

/-- The probability mass function on length-`n` strings induced by a prefix measure. -/
noncomputable def prefixPMF {α : Type*} [Fintype α] (μ : PrefixMeasure α) (n : ℕ) : PMF (Fin n → α) :=
  ⟨fun f => μ (List.ofFn f),
    by
      classical
      -- Show `∑ f, μ(ofFn f) = 1` by induction on `n`, splitting by the last symbol.
      have hsum : (∑ f : Fin n → α, μ (List.ofFn f)) = 1 := by
        induction n with
        | zero =>
            simp [μ.root_eq_one']
        | succ n ih =>
            -- Rewrite the sum using `Fin.snocEquiv` (split into initial `n` symbols and the last one).
            have hEquiv :
                (∑ p : α × (Fin n → α),
                      μ (List.ofFn ((Fin.snocEquiv fun _ : Fin (n + 1) => α) p))) =
                  ∑ f : Fin (n + 1) → α, μ (List.ofFn f) := by
              refine Fintype.sum_equiv (Fin.snocEquiv fun _ : Fin (n + 1) => α)
                (fun p => μ (List.ofFn ((Fin.snocEquiv fun _ : Fin (n + 1) => α) p)))
                (fun f => μ (List.ofFn f)) ?_
              intro p
              rfl
            have hOfFn : ∀ (a : α) (g : Fin n → α),
                μ (List.ofFn (Fin.snoc g a)) = μ (List.ofFn g ++ [a]) := by
              intro a g
              have hlist :
                  List.ofFn (Fin.snoc g a) = (List.ofFn g).concat a := by
                simpa [List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last] using
                  (List.ofFn_succ' (f := Fin.snoc g a))
              rw [hlist]
              simp [List.concat_eq_append]
            calc
              (∑ f : Fin (n + 1) → α, μ (List.ofFn f))
                  = ∑ p : α × (Fin n → α),
                      μ (List.ofFn ((Fin.snocEquiv fun _ : Fin (n + 1) => α) p)) := by
                        simpa using hEquiv.symm
              _ = ∑ a : α, ∑ g : Fin n → α, μ (List.ofFn (Fin.snoc g a)) := by
                    simp [Fintype.sum_prod_type, Fin.snocEquiv]
              _ = ∑ g : Fin n → α, ∑ a : α, μ (List.ofFn (Fin.snoc g a)) := by
                    -- Swap the order of summation.
                    simpa using
                      (Finset.sum_comm (s := (Finset.univ : Finset α))
                        (t := (Finset.univ : Finset (Fin n → α)))
                        (f := fun a g => μ (List.ofFn (Fin.snoc g a))))
              _ = ∑ g : Fin n → α, μ (List.ofFn g) := by
                    refine Fintype.sum_congr
                      (fun g : Fin n → α => ∑ a : α, μ (List.ofFn (Fin.snoc g a)))
                      (fun g : Fin n → α => μ (List.ofFn g)) ?_
                    intro g
                    calc
                      (∑ a : α, μ (List.ofFn (Fin.snoc g a)))
                          = ∑ a : α, μ (List.ofFn g ++ [a]) := by
                              refine Finset.sum_congr rfl ?_
                              intro a ha
                              simpa using hOfFn a g
                      _ = μ (List.ofFn g) := by
                              simpa using (μ.additive' (List.ofFn g))
              _ = 1 := ih
      -- Convert the finite sum identity into `HasSum`.
      simpa [hsum] using (hasSum_fintype (fun f : Fin n → α => μ (List.ofFn f)))⟩

end Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet
