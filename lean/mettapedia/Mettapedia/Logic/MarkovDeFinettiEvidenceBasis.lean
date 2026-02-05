import Mathlib.Data.List.OfFn
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mettapedia.Logic.MarkovDeFinettiHardBase
import Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge

/-!
# Markov de Finetti — Evidence Partitions (Basis Infrastructure)

This file implements the “Markov analogue of the Bernstein basis” suggested by the classical
Diaconis–Freedman proof strategy:

For each horizon `n`, consider the **finite** set of length-`n+1` trajectories `Fin (n+1) → Fin k`.
Each such trajectory has a Markov sufficient-statistic summary:

* `start : Fin k`
* transition-count matrix `counts : TransCounts k`
* `last : Fin k`

This induces:

* a weight `wμ n e` for any prefix measure `μ` (sum of `μ(xs)` over trajectories with summary `e`),
* a continuous “evidence polynomial” `W n e : MarkovParam k → ℝ≥0∞` (sum of `wordProb θ xs` over the
  same fiber).

The key property is that for each fixed `n`, the family `{W n e}` forms a **finite partition of
unity** on `MarkovParam k`, and `{wμ n e}` forms a probability vector.

These are the reusable objects needed to restate the Markov de Finetti hard direction as one
representability lemma:

> ∃ π on `MarkovParam k` such that `∫ W n e dπ = wμ n e` for all `n,e`.

Once such a `π` exists, per-word mixture formulas follow by regrouping.
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical BigOperators
open scoped NNReal ENNReal

open MeasureTheory

namespace MarkovDeFinettiHard

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.FiniteAlphabet
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovExchangeability

variable {k : ℕ}

/-! ## Horizon-`n` trajectories and their evidence summaries -/

/-- Length-`n+1` trajectories over `Fin k` (so there are `n` transitions). -/
abbrev Traj (k : ℕ) (n : ℕ) := Fin (n + 1) → Fin k

/-- Coerce a trajectory to the corresponding list. -/
def trajToList {n : ℕ} (xs : Traj k n) : List (Fin k) :=
  List.ofFn xs

@[simp] lemma length_trajToList {n : ℕ} (xs : Traj k n) :
    (trajToList (k := k) xs).length = n + 1 := by
  simp [trajToList]

/-- Evidence state = (start, transition counts, last). -/
@[ext]
structure MarkovState (k : ℕ) where
  start : Fin k
  counts : TransCounts k
  last : Fin k
deriving DecidableEq

instance : Countable (MarkovState k) := by
  classical
  -- `MarkovState k` is a triple of countable types.
  have hf :
      Function.Injective (fun e : MarkovState k => (e.start, e.counts, e.last)) := by
    intro e₁ e₂ h
    cases e₁
    cases e₂
    cases h
    rfl
  exact hf.countable

/-- The evidence state of a trajectory. -/
def stateOfTraj {n : ℕ} (xs : Traj k n) : MarkovState k :=
  ⟨xs 0, MarkovExchangeabilityBridge.countsOfFn (k := k) xs, xs (Fin.last n)⟩


/-! ## Markov-exchangeability: constancy on evidence fibers -/

private lemma evidenceOf_eq_of_stateOfTraj_eq {n : ℕ} {xs ys : Traj k n}
    (h : stateOfTraj (k := k) xs = stateOfTraj (k := k) ys) :
    MarkovExchangeability.evidenceOf (α := Fin k) (n := n) xs =
      MarkovExchangeability.evidenceOf (α := Fin k) (n := n) ys := by
  -- `evidenceOf` records start + transition counts.
  apply MarkovExchangeability.MarkovEvidence.ext
  · simpa [MarkovExchangeability.evidenceOf] using congrArg MarkovState.start h
  · funext a b
    -- `stateOfTraj.counts` is `countsOfFn`, i.e. `transCount`.
    have hcounts :
        (MarkovExchangeabilityBridge.countsOfFn (k := k) xs).counts a b =
          (MarkovExchangeabilityBridge.countsOfFn (k := k) ys).counts a b := by
      simpa using congrArg (fun e : MarkovState k => e.counts.counts a b) h
    simpa [MarkovExchangeability.evidenceOf, MarkovExchangeabilityBridge.countsOfFn] using hcounts

/-- If `μ` is Markov-exchangeable, then `μ` is constant on each evidence fiber. -/
lemma mu_const_on_state_fiber
    (μ : PrefixMeasure (Fin k)) (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    {n : ℕ} {xs ys : Traj k n} (h : stateOfTraj (k := k) xs = stateOfTraj (k := k) ys) :
    μ (trajToList (k := k) xs) = μ (trajToList (k := k) ys) := by
  -- Reduce to the `evidenceOf` equality expected by `hμ`.
  have he :
      MarkovExchangeability.evidenceOf (α := Fin k) (n := n) xs =
        MarkovExchangeability.evidenceOf (α := Fin k) (n := n) ys :=
    evidenceOf_eq_of_stateOfTraj_eq (k := k) h
  simpa [trajToList] using hμ n xs ys he

/-- Transition-product along a length-`n+1` trajectory, starting from the first symbol. -/
private def transProd (θ : MarkovParam k) {n : ℕ} (xs : Traj k n) : ℝ≥0 :=
  ∏ i : Fin n, stepProb (k := k) θ (xs (Fin.castSucc i)) (xs (Fin.succ i))

private lemma wordProbAux_ofFn_tail (θ : MarkovParam k) :
    ∀ {n : ℕ} (xs : Traj k n),
      wordProbAux (k := k) θ (xs 0) (List.ofFn (fun i : Fin n => xs i.succ))
        = transProd (k := k) θ xs := by
  intro n xs
  induction n with
  | zero =>
      -- No transitions.
      simp [transProd, wordProbAux]
  | succ n ih =>
      -- Split off the first transition, then apply IH to the tail.
      have hlist :
          List.ofFn (fun i : Fin (n + 1) => xs i.succ) =
            xs 1 :: List.ofFn (fun i : Fin n => xs i.succ.succ) := by
        simp [List.ofFn_succ]
      -- Define the tail trajectory.
      let xsTail : Traj k n := fun i => xs i.succ
      have htail : List.ofFn (fun i : Fin n => xs i.succ.succ) =
          List.ofFn (fun i : Fin n => xsTail i.succ) := by
        rfl
      have ih' :
          wordProbAux (k := k) θ (xs 1) (List.ofFn (fun i : Fin n => xs i.succ.succ))
            = transProd (k := k) θ xsTail := by
        simpa [xsTail, htail] using (ih (xs := xsTail))
      -- Unfold `wordProbAux` on the head symbol.
      -- The RHS product splits as the first transition times the tail product.
      have hprod :
          transProd (k := k) θ xs =
            stepProb (k := k) θ (xs 0) (xs 1) * transProd (k := k) θ xsTail := by
        -- `Fin.prod_univ_succ` for the product over `Fin (n+1)`.
        -- Rewrite the product to match our `transProd` definitions.
        simp [transProd, xsTail, Fin.prod_univ_succ]
      calc
        wordProbAux (k := k) θ (xs 0) (List.ofFn (fun i : Fin (n + 1) => xs i.succ))
            = wordProbAux (k := k) θ (xs 0) (xs 1 :: List.ofFn (fun i : Fin n => xs i.succ.succ)) := by
                simp
        _ = stepProb (k := k) θ (xs 0) (xs 1) *
              wordProbAux (k := k) θ (xs 1) (List.ofFn (fun i : Fin n => xs i.succ.succ)) := by
                simp [wordProbAux]
        _ = stepProb (k := k) θ (xs 0) (xs 1) * transProd (k := k) θ xsTail := by
                simp [ih']
        _ = transProd (k := k) θ xs := by
                simp [hprod]

private lemma wordProbNN_ofFn (θ : MarkovParam k) {n : ℕ} (xs : Traj k n) :
    wordProbNN (k := k) θ (trajToList (k := k) xs) =
      initProb (k := k) θ (xs 0) * transProd (k := k) θ xs := by
  classical
  -- `trajToList xs = xs 0 :: ofFn tail`.
  have hcons :
      trajToList (k := k) xs = xs 0 :: List.ofFn (fun i : Fin n => xs i.succ) := by
    simp [trajToList, List.ofFn_succ]
  -- Expand `wordProbNN` and apply `wordProbAux_ofFn_tail`.
  cases n with
  | zero =>
      -- Length-1 words have no tail product.
      simp [trajToList, wordProbNN, transProd, wordProbAux]
  | succ n =>
      -- `wordProbNN (a :: tail) = initProb a * wordProbAux a tail`.
      have hlist :
          List.ofFn (fun i : Fin (n + 1) => xs i.succ) =
            xs 1 :: List.ofFn (fun i : Fin n => xs i.succ.succ) := by
        simp [List.ofFn_succ]
      have haux0 :
          wordProbAux (k := k) θ (xs 0) (List.ofFn (fun i : Fin (n + 1) => xs i.succ))
            = transProd (k := k) θ xs :=
        wordProbAux_ofFn_tail (k := k) (θ := θ) xs
      have haux :
          wordProbAux (k := k) θ (xs 0) (xs 1 :: List.ofFn (fun i : Fin n => xs i.succ.succ))
            = transProd (k := k) θ xs := by
        simpa [hlist] using haux0
      calc
        wordProbNN (k := k) θ (trajToList (k := k) xs)
            = initProb (k := k) θ (xs 0) *
                wordProbAux (k := k) θ (xs 0) (List.ofFn (fun i : Fin (n + 1) => xs i.succ)) := by
                  simp [wordProbNN, hcons]
        _ = initProb (k := k) θ (xs 0) * transProd (k := k) θ xs := by
              -- Ensure the `wordProbAux` tail is in the cons form used by simp.
              simp [haux]

private lemma transProd_eq_prod_pow_transCount (θ : MarkovParam k) {n : ℕ} (xs : Traj k n) :
    transProd (k := k) θ xs =
      ∏ ab : Fin k × Fin k,
        (stepProb (k := k) θ ab.1 ab.2) ^ transCount (n := n) xs ab.1 ab.2 := by
  classical
  -- Group the product over indices `i : Fin n` by the adjacent pair `(xs i, xs (i+1))`.
  let s : Finset (Fin n) := Finset.univ
  let key : Fin n → Fin k × Fin k := fun i => (xs (Fin.castSucc i), xs (Fin.succ i))
  let step : Fin n → ℝ≥0 := fun i => stepProb (k := k) θ (xs (Fin.castSucc i)) (xs (Fin.succ i))
  have hfiber :
      (∏ ab : Fin k × Fin k, ∏ i ∈ s with key i = ab, step i) = ∏ i ∈ s, step i :=
    Finset.prod_fiberwise (s := s) (g := key) (f := step)
  have hstep :
      (∏ i : Fin n, step i) = ∏ i ∈ s, step i := by
    simp [s]
  have hinner :
      ∀ ab : Fin k × Fin k,
        (∏ i ∈ s with key i = ab, step i) =
          (stepProb (k := k) θ ab.1 ab.2) ^ (s.filter (fun i => key i = ab)).card := by
    intro ab
    rcases ab with ⟨a, b⟩
    have hconst :
        (∏ i ∈ s with key i = (a, b), step i) =
          ∏ _i ∈ s.filter (fun i => key i = (a, b)), stepProb (k := k) θ a b := by
      refine Finset.prod_congr rfl ?_
      intro i hi
      have hkey : key i = (a, b) := (Finset.mem_filter.1 hi).2
      have hab : xs (Fin.castSucc i) = a ∧ xs (Fin.succ i) = b := by
        simpa [key] using hkey
      simp [step, hab.1, hab.2]
    calc
      (∏ i ∈ s with key i = (a, b), step i)
          = ∏ _i ∈ s.filter (fun i => key i = (a, b)), stepProb (k := k) θ a b := hconst
      _ = (stepProb (k := k) θ a b) ^ (s.filter (fun i => key i = (a, b))).card := by
            exact Finset.prod_const (s := s.filter (fun i => key i = (a, b)))
              (b := stepProb (k := k) θ a b)
  -- Replace the fiber-card with `transCount`.
  calc
    transProd (k := k) θ xs
        = ∏ i : Fin n, step i := by
            simp [transProd, step]
    _ = ∏ i ∈ s, step i := by
          simpa using hstep.symm
    _ = ∏ ab : Fin k × Fin k, ∏ i ∈ s with key i = ab, step i := by
          simp [hfiber]
    _ = ∏ ab : Fin k × Fin k,
          (stepProb (k := k) θ ab.1 ab.2) ^ (s.filter (fun i => key i = ab)).card := by
          exact Fintype.prod_congr _ _ hinner
    _ = ∏ ab : Fin k × Fin k,
          (stepProb (k := k) θ ab.1 ab.2) ^ transCount (n := n) xs ab.1 ab.2 := by
          refine Fintype.prod_congr _ _ ?_
          intro ab
          -- `key i = (a,b)` is definitional equal to the predicate used in `transCount`.
          have :
              (s.filter (fun i : Fin n => key i = ab)).card =
                transCount (n := n) xs ab.1 ab.2 := by
            -- Rewrite the fiber predicate into the conjunction predicate.
            have hfilter :
                s.filter (fun i : Fin n => key i = ab) =
                  s.filter (fun i : Fin n =>
                    xs (Fin.castSucc i) = ab.1 ∧ xs (Fin.succ i) = ab.2) := by
              ext i
              simp [key, Prod.ext_iff]
            -- `transCount` is exactly this filtered-card.
            simp [transCount, hfilter, s]
          simp [this]

private lemma wordProbNN_ofFn_eq_prod_pow_transCount (θ : MarkovParam k) {n : ℕ} (xs : Traj k n) :
    wordProbNN (k := k) θ (trajToList (k := k) xs) =
      initProb (k := k) θ (xs 0) *
        ∏ ab : Fin k × Fin k,
          (stepProb (k := k) θ ab.1 ab.2) ^ transCount (n := n) xs ab.1 ab.2 := by
  classical
  -- Combine the head-and-tail formula with the grouped transition product.
  simp [wordProbNN_ofFn (k := k) (θ := θ) xs,
    transProd_eq_prod_pow_transCount (k := k) (θ := θ) xs]

/-- `wordProbNN θ` depends only on the Markov evidence (`start`, `transCount`) of the trajectory,
hence is constant on each evidence fiber. -/
lemma wordProbNN_const_on_state_fiber
    {n : ℕ} (θ : MarkovParam k) {xs ys : Traj k n}
    (h : stateOfTraj (k := k) xs = stateOfTraj (k := k) ys) :
    wordProbNN (k := k) θ (trajToList (k := k) xs) =
      wordProbNN (k := k) θ (trajToList (k := k) ys) := by
  classical
  have he :
      MarkovExchangeability.evidenceOf (α := Fin k) (n := n) xs =
        MarkovExchangeability.evidenceOf (α := Fin k) (n := n) ys :=
    evidenceOf_eq_of_stateOfTraj_eq (k := k) h
  have hstart : xs 0 = ys 0 := by
    simpa [MarkovExchangeability.evidenceOf] using congrArg MarkovEvidence.start he
  have htrans : ∀ a b : Fin k, transCount (n := n) xs a b = transCount (n := n) ys a b := by
    intro a b
    simpa [MarkovExchangeability.evidenceOf] using congrArg (fun e => e.trans a b) he
  -- Rewrite both words into the product-of-powers normal form.
  simp [wordProbNN_ofFn_eq_prod_pow_transCount (k := k) (θ := θ),
    hstart, htrans]

/-- `wordProb θ` is constant on each evidence fiber (it depends only on `start` and `transCount`). -/
lemma wordProb_const_on_state_fiber
    {n : ℕ} (θ : MarkovParam k) {xs ys : Traj k n}
    (h : stateOfTraj (k := k) xs = stateOfTraj (k := k) ys) :
    wordProb (k := k) θ (trajToList (k := k) xs) =
      wordProb (k := k) θ (trajToList (k := k) ys) := by
  -- `wordProb` is just a coercion of `wordProbNN`.
  simp [wordProb, wordProbNN_const_on_state_fiber (k := k) (θ := θ) h]

/-
## `wordProb` defines a prefix measure

For the Markov de Finetti hard direction it is convenient to view `wordProb θ` as a
`FiniteAlphabet.PrefixMeasure`.  We package the elementary additivity proof here so it can be
reused in tower/regrouping arguments.
-/

private lemma sum_singleton_eq_one (μ0 : MeasureTheory.ProbabilityMeasure (Fin k)) :
    (∑ a : Fin k, μ0 (Set.singleton a)) = 1 := by
  classical
  let μ : Measure (Fin k) := (μ0 : Measure (Fin k))
  -- Work in `ENNReal` first, using the finite partition of `univ` by singletons.
  have hsum0 :
      (∑ a ∈ (Finset.univ : Finset (Fin k)), μ (Set.singleton a)) =
        μ (Finset.univ : Finset (Fin k)) :=
    (MeasureTheory.sum_measure_singleton (μ := μ) (s := (Finset.univ : Finset (Fin k))))
  have hsum :
      (∑ a : Fin k, μ (Set.singleton a)) = μ Set.univ := by
    -- Avoid rewriting `hsum0` by simp; just unfold the coercions explicitly.
    simpa [μ, Finset.coe_univ] using hsum0
  have hμuniv : μ Set.univ = 1 := by
    simp [μ]
  have hsum1 : (∑ a : Fin k, μ (Set.singleton a)) = (1 : ENNReal) := by
    simpa [hμuniv] using hsum
  -- Convert the ENNReal identity to NNReal by `toNNReal`, distributing over finite sums.
  have hf :
      ∀ a ∈ (Finset.univ : Finset (Fin k)), μ (Set.singleton a) ≠ (⊤ : ENNReal) := by
    intro a ha
    simp [μ]
  have htoNN :
      ENNReal.toNNReal (∑ a : Fin k, μ (Set.singleton a)) =
        ∑ a : Fin k, ENNReal.toNNReal (μ (Set.singleton a)) := by
    simpa using
      (ENNReal.toNNReal_sum (s := (Finset.univ : Finset (Fin k)))
        (f := fun a : Fin k => μ (Set.singleton a)) hf)
  have hpm :
      (∑ a : Fin k, μ0 (Set.singleton a)) =
        ∑ a : Fin k, ENNReal.toNNReal (μ (Set.singleton a)) := by
    simp [MeasureTheory.ProbabilityMeasure.coeFn_def, μ]
  calc
    (∑ a : Fin k, μ0 (Set.singleton a))
        = ∑ a : Fin k, ENNReal.toNNReal (μ (Set.singleton a)) := hpm
    _ = ENNReal.toNNReal (∑ a : Fin k, μ (Set.singleton a)) := by
          exact htoNN.symm
    _ = ENNReal.toNNReal (1 : ENNReal) := by
          simp [hsum1]
    _ = 1 := by simp

private lemma wordProbAux_additive (θ : MarkovParam k) (prev : Fin k) :
    ∀ xs : List (Fin k),
      (∑ a : Fin k, wordProbAux (k := k) θ prev (xs ++ [a])) =
        wordProbAux (k := k) θ prev xs := by
  intro xs
  induction xs generalizing prev with
  | nil =>
      -- `xs = []`: `wordProbAux prev [a] = stepProb prev a`, and `∑ a, stepProb prev a = 1`.
      have hstep : (∑ a : Fin k, stepProb (k := k) θ prev a) = 1 := by
        simpa [stepProb] using (sum_singleton_eq_one (k := k) (μ0 := θ.trans prev))
      -- Now simplify the goal to `hstep`.
      simpa [wordProbAux, stepProb, hstep]
  | cons b xs ih =>
      -- Factor out the constant first transition probability.
      have hmul :
          (∑ a : Fin k,
              stepProb (k := k) θ prev b * wordProbAux (k := k) θ b (xs ++ [a])) =
            stepProb (k := k) θ prev b * ∑ a : Fin k, wordProbAux (k := k) θ b (xs ++ [a]) := by
        -- `∑ a, c * f a = c * ∑ a, f a`.
        simpa using
          (Finset.mul_sum (a := stepProb (k := k) θ prev b)
            (s := (Finset.univ : Finset (Fin k)))
            (f := fun a : Fin k => wordProbAux (k := k) θ b (xs ++ [a]))).symm
      calc
        (∑ a : Fin k, wordProbAux (k := k) θ prev ((b :: xs) ++ [a]))
            = ∑ a : Fin k,
                stepProb (k := k) θ prev b * wordProbAux (k := k) θ b (xs ++ [a]) := by
                  simp [wordProbAux, List.cons_append]
        _ = stepProb (k := k) θ prev b * ∑ a : Fin k, wordProbAux (k := k) θ b (xs ++ [a]) := hmul
        _ = stepProb (k := k) θ prev b * wordProbAux (k := k) θ b xs := by
              simp [ih (prev := b)]
        _ = wordProbAux (k := k) θ prev (b :: xs) := by
              simp [wordProbAux]

private lemma wordProbNN_additive (θ : MarkovParam k) :
    ∀ xs : List (Fin k),
      (∑ a : Fin k, wordProbNN (k := k) θ (xs ++ [a])) =
        wordProbNN (k := k) θ xs := by
  intro xs
  classical
  cases xs with
  | nil =>
      -- `wordProbNN [a] = initProb a`, and `∑ a, initProb a = 1`.
      have hinit : (∑ a : Fin k, initProb (k := k) θ a) = 1 := by
        simpa [initProb] using (sum_singleton_eq_one (k := k) (μ0 := θ.init))
      simpa [wordProbNN, wordProbAux, initProb, hinit]
  | cons a xs =>
      have hmul :
          (∑ b : Fin k, initProb (k := k) θ a * wordProbAux (k := k) θ a (xs ++ [b])) =
            initProb (k := k) θ a * ∑ b : Fin k, wordProbAux (k := k) θ a (xs ++ [b]) := by
        simpa using
          (Finset.mul_sum (a := initProb (k := k) θ a)
            (s := (Finset.univ : Finset (Fin k)))
            (f := fun b : Fin k => wordProbAux (k := k) θ a (xs ++ [b]))).symm
      calc
        (∑ b : Fin k, wordProbNN (k := k) θ ((a :: xs) ++ [b]))
            = ∑ b : Fin k,
                initProb (k := k) θ a * wordProbAux (k := k) θ a (xs ++ [b]) := by
                  simp [wordProbNN, List.cons_append]
        _ = initProb (k := k) θ a * ∑ b : Fin k, wordProbAux (k := k) θ a (xs ++ [b]) := hmul
        _ = initProb (k := k) θ a * wordProbAux (k := k) θ a xs := by
              simp [wordProbAux_additive (k := k) (θ := θ) (prev := a) xs]
        _ = wordProbNN (k := k) θ (a :: xs) := by
              simp [wordProbNN]

/-- The `FiniteAlphabet.PrefixMeasure` induced by a fixed Markov parameter `θ`. -/
noncomputable def wordProbPrefixMeasure (θ : MarkovParam k) : PrefixMeasure (Fin k) :=
  { toFun := fun xs => wordProb (k := k) θ xs
    root_eq_one' := by
      simp [wordProb, wordProbNN]
    additive' := by
      intro xs
      -- Prove additivity in `NNReal` and then coerce to `ENNReal`.
      have hNN : (∑ a : Fin k, wordProbNN (k := k) θ (xs ++ [a])) = wordProbNN (k := k) θ xs :=
        wordProbNN_additive (k := k) (θ := θ) xs
      -- `NNReal` coerces to `ENNReal` preserving finite sums.
      -- `simp` rewrites the cast of a sum into a sum of casts.
      have hENN : ((∑ a : Fin k, wordProbNN (k := k) θ (xs ++ [a])) : ENNReal) =
          (wordProbNN (k := k) θ xs : ENNReal) := by
        simpa using congrArg (fun t : NNReal => (t : ENNReal)) hNN
      -- Expand `wordProb` on both sides.
      simpa [wordProb] using hENN }

lemma wordProbPrefixMeasure_apply (θ : MarkovParam k) (xs : List (Fin k)) :
    wordProbPrefixMeasure (k := k) θ xs = wordProb (k := k) θ xs := rfl

/-- `wordProbPrefixMeasure θ` is Markov-exchangeable (it depends only on `evidenceOf`). -/
theorem wordProbPrefixMeasure_markovExchangeable (θ : MarkovParam k) :
    MarkovExchangeablePrefixMeasure (k := k) (wordProbPrefixMeasure (k := k) θ) := by
  intro n xs₁ xs₂ he
  -- `wordProbNN` depends only on the start symbol and transition counts.
  have hstart : xs₁ 0 = xs₂ 0 := by
    simpa [MarkovExchangeability.evidenceOf] using congrArg MarkovEvidence.start he
  have htrans : ∀ a b : Fin k, transCount (n := n) xs₁ a b = transCount (n := n) xs₂ a b := by
    intro a b
    simpa [MarkovExchangeability.evidenceOf] using congrArg (fun e => e.trans a b) he
  have hNN :
      wordProbNN (k := k) θ (trajToList (k := k) xs₁) =
        wordProbNN (k := k) θ (trajToList (k := k) xs₂) := by
    classical
    -- Rewrite both sides in the product-of-powers normal form.
    simp [wordProbNN_ofFn_eq_prod_pow_transCount (k := k) (θ := θ),
      hstart, htrans]
  -- Lift to `ENNReal` and unfold the prefix measure.
  have hENN :
      wordProb (k := k) θ (trajToList (k := k) xs₁) =
        wordProb (k := k) θ (trajToList (k := k) xs₂) := by
    -- `wordProb` is a coercion of `wordProbNN`.
    simpa [wordProb] using congrArg (fun t : NNReal => (t : ENNReal)) hNN
  simpa [wordProbPrefixMeasure, trajToList] using hENN

@[simp] lemma stateOfTraj_start {n : ℕ} (xs : Traj k n) :
    (stateOfTraj (k := k) xs).start = xs 0 := rfl

@[simp] lemma stateOfTraj_last {n : ℕ} (xs : Traj k n) :
    (stateOfTraj (k := k) xs).last = xs (Fin.last n) := rfl

/-! ## Extending trajectories and evidence states -/

/-- Append a symbol to a trajectory. -/
def trajSnoc {n : ℕ} (xs : Traj k n) (x : Fin k) : Traj k (n + 1) :=
  Fin.snoc (α := fun _ : Fin (n + 2) => Fin k) xs x

/-- Drop the last symbol of a trajectory. -/
def trajInit {n : ℕ} (xs : Traj k (n + 1)) : Traj k n :=
  fun i => xs (Fin.castSucc i)

/-- Prefix of a trajectory, keeping the first `n+1` symbols. -/
def trajPrefix {n N : ℕ} (h : n ≤ N) (xs : Traj k N) : Traj k n :=
  fun i => xs (Fin.castLE (Nat.succ_le_succ h) i)

@[simp] lemma trajPrefix_self {n : ℕ} (xs : Traj k n) :
    trajPrefix (k := k) (n := n) (N := n) le_rfl xs = xs := by
  funext i
  simp [trajPrefix]

/-- Appending a symbol does not change the earlier prefix of a trajectory. -/
@[simp] lemma trajPrefix_trajSnoc {n N : ℕ} (h : n ≤ N) (xs : Traj k N) (x : Fin k) :
    trajPrefix (k := k) (n := n) (N := N + 1) (Nat.le_trans h (Nat.le_succ N))
        (trajSnoc (k := k) xs x) =
      trajPrefix (k := k) (n := n) (N := N) h xs := by
  funext i
  -- Unfold both sides. On the LHS we must coerce the `Fin (n+1)` index into `Fin (N+2)`.
  -- We do this via `castSucc` after first casting into `Fin (N+1)`, so `Fin.snoc_castSucc` applies.
  dsimp [trajPrefix, trajSnoc]
  let j : Fin (N + 1) := Fin.castLE (Nat.succ_le_succ h) i
  have hj :
      Fin.castLE (Nat.succ_le_succ (Nat.le_trans h (Nat.le_succ N))) i = j.castSucc := by
    apply Fin.ext
    simp [j]
  -- Rewrite the coerced index into the `castSucc` form so `Fin.snoc_castSucc` applies.
  rw [hj]
  -- Now the goal is definitional.
  simpa [j] using
    (Fin.snoc_castSucc (α := fun _ : Fin (N + 2) => Fin k) (p := xs) (x := x) (i := j))

/-- Evidence state of a prefix of a longer trajectory. -/
def prefixState {n N : ℕ} (h : n ≤ N) (xs : Traj k N) : MarkovState k :=
  stateOfTraj (k := k) (trajPrefix (k := k) h xs)

@[simp] lemma prefixState_self {n : ℕ} (xs : Traj k n) :
    prefixState (k := k) (n := n) (N := n) le_rfl xs = stateOfTraj (k := k) xs := by
  simp [prefixState]

/-- Appending a symbol does not change the earlier evidence prefix state. -/
@[simp] lemma prefixState_trajSnoc {n N : ℕ} (h : n ≤ N) (xs : Traj k N) (x : Fin k) :
    prefixState (k := k) (n := n) (N := N + 1) (Nat.le_trans h (Nat.le_succ N))
        (trajSnoc (k := k) xs x) =
      prefixState (k := k) (n := n) (N := N) h xs := by
  simp [prefixState, trajPrefix_trajSnoc (k := k) (h := h) (xs := xs) (x := x)]

/-- `trajToList` of an extended trajectory is list append. -/
lemma trajToList_trajSnoc {n : ℕ} (xs : Traj k n) (x : Fin k) :
    trajToList (k := k) (trajSnoc (k := k) xs x) = trajToList (k := k) xs ++ [x] := by
  -- `List.ofFn` for a `Fin.snoc` is a `concat`/append.
  unfold trajToList trajSnoc
  -- `ofFn_succ'` turns `List.ofFn` into a `concat` form; we rewrite `concat` into `++ [x]`.
  rw [List.ofFn_succ' (f := Fin.snoc (α := fun _ : Fin (n + 2) => Fin k) xs x)]
  simp [List.concat_eq_append]

/-- `trajInit` is left inverse to `trajSnoc`. -/
lemma trajInit_trajSnoc {n : ℕ} (xs : Traj k n) (x : Fin k) :
    trajInit (k := k) (trajSnoc (k := k) xs x) = xs := by
  funext i
  simp [trajInit, trajSnoc]

/-- `trajSnoc` is right inverse to `trajInit` with the last symbol. -/
lemma trajSnoc_trajInit {n : ℕ} (xs : Traj k (n + 1)) :
    trajSnoc (k := k) (trajInit (k := k) xs) (xs (Fin.last (n + 1))) = xs := by
  funext i
  cases i using Fin.lastCases with
  | last =>
      simp [trajSnoc]
  | cast j =>
      simp [trajSnoc, trajInit]

/-- Update an evidence state by appending a next symbol. -/
def MarkovState.snoc (e : MarkovState k) (x : Fin k) : MarkovState k :=
  ⟨e.start, TransCounts.bump e.counts e.last x, x⟩

@[simp] lemma MarkovState.snoc_start (e : MarkovState k) (x : Fin k) :
    (MarkovState.snoc (k := k) e x).start = e.start := rfl

@[simp] lemma MarkovState.snoc_last (e : MarkovState k) (x : Fin k) :
    (MarkovState.snoc (k := k) e x).last = x := rfl

lemma countsOfFn_trajSnoc {n : ℕ} (xs : Traj k n) (x : Fin k) :
    MarkovExchangeabilityBridge.countsOfFn (k := k) (trajSnoc (k := k) xs x) =
      TransCounts.bump (MarkovExchangeabilityBridge.countsOfFn (k := k) xs) (xs (Fin.last n)) x := by
  classical
  ext a b
  -- Expand the `transCount` recursion.
  have htc :
      transCount (n := n + 1) (trajSnoc (k := k) xs x) a b =
        transCount (n := n) xs a b + (if xs (Fin.last n) = a ∧ x = b then 1 else 0) := by
    -- `trajSnoc` is definitional `Fin.snoc`.
    simpa [trajSnoc] using
      (transCount_snoc (n := n) (xs := xs) (x := x) (a := a) (b := b))
  -- Turn the `transCount` statement into `TransCounts.bump`.
  by_cases h : a = xs (Fin.last n) ∧ b = x
  · rcases h with ⟨ha, hb⟩
    subst ha; subst hb
    -- Both sides are `transCount xs (xs last) x + 1`.
    simp [MarkovExchangeabilityBridge.countsOfFn, TransCounts.bump, htc]
  · have h' : ¬(xs (Fin.last n) = a ∧ x = b) := by
        intro h'
        apply h
        exact ⟨h'.1.symm, h'.2.symm⟩
    -- Both sides reduce to `transCount xs a b`.
    simp [MarkovExchangeabilityBridge.countsOfFn, TransCounts.bump, htc, h, h']

lemma stateOfTraj_trajSnoc {n : ℕ} (xs : Traj k n) (x : Fin k) :
    stateOfTraj (k := k) (trajSnoc (k := k) xs x) =
      MarkovState.snoc (k := k) (stateOfTraj (k := k) xs) x := by
  classical
  refine MarkovState.ext ?_ ?_ ?_
  · -- start
    simp [stateOfTraj, trajSnoc, MarkovState.snoc]
  · -- counts
    simpa [stateOfTraj, MarkovState.snoc] using countsOfFn_trajSnoc (k := k) (xs := xs) (x := x)
  · -- last
    simp [stateOfTraj, trajSnoc, MarkovState.snoc]

/-! ## Injectivity of `trajSnoc` (fixed last symbol) -/

lemma trajSnoc_inj {n : ℕ} (x : Fin k) :
    Function.Injective (fun xs : Traj k n => trajSnoc (k := k) xs x) := by
  intro xs ys h
  -- Apply `trajInit` to both sides.
  have h' : trajInit (k := k) (trajSnoc (k := k) xs x) =
      trajInit (k := k) (trajSnoc (k := k) ys x) := by
    simpa using congrArg (trajInit (k := k)) h
  -- `trajInit_trajSnoc` is a left inverse.
  simpa [trajInit_trajSnoc (k := k)] using h'

/-! ## Finite partitions over evidence classes -/

/-- Finite set of all length-`n+1` trajectories. -/
def trajFinset (k : ℕ) (n : ℕ) : Finset (Traj k n) :=
  Finset.univ

/-! ### Aliases matching the “evidence partition” terminology -/

/-- Alias: finite set of words (trajectories) of length `n+1`. -/
def Words (k : ℕ) (n : ℕ) : Finset (Traj k n) :=
  trajFinset k n

/-- The finite set of evidence states realized at horizon `n`. -/
def stateFinset (k : ℕ) (n : ℕ) : Finset (MarkovState k) :=
  (trajFinset k n).image (stateOfTraj (k := k))

/-- Alias: finite evidence class set at horizon `n`. -/
def E_n (k : ℕ) (n : ℕ) : Finset (MarkovState k) :=
  stateFinset k n

/-! ### Evidence fibers and prefix fibers -/

/-- The evidence fiber at horizon `N` for state `eN`. -/
def fiber (k : ℕ) (N : ℕ) (eN : MarkovState k) : Finset (Traj k N) :=
  (trajFinset k N).filter (fun xs => stateOfTraj (k := k) xs = eN)

/-- The prefix fiber: trajectories in the fiber with prefix state `e`. -/
def prefixFiber (k : ℕ) {n N : ℕ} (h : n ≤ N) (e : MarkovState k) (eN : MarkovState k) :
    Finset (Traj k N) :=
  (fiber k N eN).filter (fun xs => prefixState (k := k) h xs = e)

/-- Coefficient: fraction of the fiber whose prefix state equals `e`. -/
def prefixCoeff (k : ℕ) {n N : ℕ} (h : n ≤ N) (e : MarkovState k) (eN : MarkovState k) : ENNReal :=
  if _ : (fiber k N eN).card = 0 then 0
  else
    ((prefixFiber (k := k) h e eN).card : ENNReal) / ((fiber k N eN).card : ENNReal)

lemma stateOfTraj_mem_stateFinset {n : ℕ} (xs : Traj k n) :
    stateOfTraj (k := k) xs ∈ stateFinset k n := by
  classical
  refine Finset.mem_image.2 ?_
  exact ⟨xs, by simp [trajFinset], rfl⟩

lemma prefixState_mem_stateFinset {n N : ℕ} (h : n ≤ N) (xs : Traj k N) :
    prefixState (k := k) (n := n) (N := N) h xs ∈ stateFinset k n := by
  -- `prefixState` is `stateOfTraj` of the `n`-prefix trajectory.
  simpa [prefixState] using
    stateOfTraj_mem_stateFinset (k := k) (xs := trajPrefix (k := k) (n := n) (N := N) h xs)

lemma fiber_nonempty_of_mem_stateFinset {N : ℕ} {eN : MarkovState k}
    (heN : eN ∈ stateFinset k N) :
    (fiber k N eN).Nonempty := by
  classical
  rcases Finset.mem_image.1 heN with ⟨xs, hxs, rfl⟩
  refine ⟨xs, ?_⟩
  exact Finset.mem_filter.2 ⟨hxs, rfl⟩

lemma fiber_card_ne_zero_of_mem_stateFinset {N : ℕ} {eN : MarkovState k}
    (heN : eN ∈ stateFinset k N) :
    (fiber k N eN).card ≠ 0 := by
  classical
  exact Finset.card_ne_zero.2 (fiber_nonempty_of_mem_stateFinset (k := k) (N := N) (eN := eN) heN)

lemma fiber_eq_biUnion_prefixFiber {n N : ℕ} (h : n ≤ N) (eN : MarkovState k) :
    fiber k N eN =
      (stateFinset k n).biUnion (fun e => prefixFiber (k := k) h e eN) := by
  classical
  ext xs
  constructor
  · intro hxs
    have he : prefixState (k := k) (n := n) (N := N) h xs ∈ stateFinset k n :=
      prefixState_mem_stateFinset (k := k) (h := h) xs
    refine Finset.mem_biUnion.2 ?_
    refine ⟨prefixState (k := k) (n := n) (N := N) h xs, he, ?_⟩
    refine Finset.mem_filter.2 ?_
    refine ⟨hxs, ?_⟩
    simp
  · intro hxs
    rcases Finset.mem_biUnion.1 hxs with ⟨e, he, hx⟩
    -- Membership in a prefix fiber is membership in the underlying fiber.
    exact (Finset.mem_filter.1 hx).1

lemma prefixFiber_disjoint {n N : ℕ} (h : n ≤ N) {e₁ e₂ : MarkovState k}
    (hne : e₁ ≠ e₂) (eN : MarkovState k) :
    Disjoint (prefixFiber (k := k) h e₁ eN) (prefixFiber (k := k) h e₂ eN) := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro xs hx₁ hx₂
  have h₁ : prefixState (k := k) (n := n) (N := N) h xs = e₁ := (Finset.mem_filter.1 hx₁).2
  have h₂ : prefixState (k := k) (n := n) (N := N) h xs = e₂ := (Finset.mem_filter.1 hx₂).2
  exact hne (h₁.symm.trans h₂)

lemma fiber_card_eq_sum_prefixFiber_card {n N : ℕ} (h : n ≤ N) (eN : MarkovState k) :
    (fiber k N eN).card =
      ∑ e ∈ stateFinset k n, (prefixFiber (k := k) h e eN).card := by
  classical
  -- Rewrite `fiber` as a disjoint union of prefix fibers, then apply `card_biUnion`.
  have hdisj :
      (stateFinset k n : Set (MarkovState k)).PairwiseDisjoint (fun e => prefixFiber (k := k) h e eN) := by
    intro e₁ he₁ e₂ he₂ hne
    exact prefixFiber_disjoint (k := k) (h := h) (e₁ := e₁) (e₂ := e₂) hne eN
  calc
    (fiber k N eN).card
        = ((stateFinset k n).biUnion (fun e => prefixFiber (k := k) h e eN)).card := by
            simp [fiber_eq_biUnion_prefixFiber (k := k) (h := h) (eN := eN)]
    _ = ∑ e ∈ stateFinset k n, (prefixFiber (k := k) h e eN).card := by
            simpa using (Finset.card_biUnion (s := stateFinset k n)
              (t := fun e => prefixFiber (k := k) h e eN) hdisj)

lemma sum_prefixCoeff_eq_one_of_mem_stateFinset {n N : ℕ} (h : n ≤ N) (eN : MarkovState k)
    (heN : eN ∈ stateFinset k N) :
    (∑ e ∈ stateFinset k n, prefixCoeff (k := k) h e eN) = 1 := by
  classical
  have hcard : (fiber k N eN).card ≠ 0 :=
    fiber_card_ne_zero_of_mem_stateFinset (k := k) (N := N) (eN := eN) heN
  have hcard' : ((fiber k N eN).card : ENNReal) ≠ 0 := by exact_mod_cast hcard
  have hcard_top : ((fiber k N eN).card : ENNReal) ≠ (⊤ : ENNReal) := by simp
  -- Expand `prefixCoeff` (the `if` branch is false since the fiber is nonempty).
  have hcoeff :
      (∑ e ∈ stateFinset k n, prefixCoeff (k := k) h e eN) =
        (∑ e ∈ stateFinset k n,
          ((prefixFiber (k := k) h e eN).card : ENNReal) / ((fiber k N eN).card : ENNReal)) := by
    refine Finset.sum_congr rfl ?_
    intro e he
    simp [prefixCoeff, hcard]
  -- Use the partition cardinality identity.
  have hsumCard :
      (∑ e ∈ stateFinset k n, ((prefixFiber (k := k) h e eN).card : ENNReal))
        = ((fiber k N eN).card : ENNReal) := by
    have := fiber_card_eq_sum_prefixFiber_card (k := k) (h := h) (eN := eN) (n := n) (N := N)
    -- Cast the Nat identity into `ENNReal`.
    exact_mod_cast this.symm
  -- Finish by pulling out the constant denominator.
  calc
    (∑ e ∈ stateFinset k n, prefixCoeff (k := k) h e eN)
        = (∑ e ∈ stateFinset k n,
            ((prefixFiber (k := k) h e eN).card : ENNReal) / ((fiber k N eN).card : ENNReal)) := hcoeff
    _ = (∑ e ∈ stateFinset k n,
            ((prefixFiber (k := k) h e eN).card : ENNReal) * (((fiber k N eN).card : ENNReal)⁻¹)) := by
            simp [div_eq_mul_inv]
    _ = (∑ e ∈ stateFinset k n,
            ((prefixFiber (k := k) h e eN).card : ENNReal)) * (((fiber k N eN).card : ENNReal)⁻¹) := by
            simp [Finset.sum_mul]
    _ = ((fiber k N eN).card : ENNReal) * (((fiber k N eN).card : ENNReal)⁻¹) := by
            simp [hsumCard]
    _ = 1 := by
            simp [ENNReal.mul_inv_cancel hcard' hcard_top]

lemma prefixCoeff_eq_zero_of_not_mem_stateFinset {n N : ℕ} (h : n ≤ N) (e : MarkovState k)
    (eN : MarkovState k) (he : e ∉ stateFinset k n) :
    prefixCoeff (k := k) h e eN = 0 := by
  classical
  by_cases hcard : (fiber k N eN).card = 0
  · simp [prefixCoeff, hcard]
  · -- If the fiber is nonempty, the prefix state of any trajectory in it is always in `stateFinset k n`,
    -- so the filter defining `prefixFiber` is empty when `e ∉ stateFinset k n`.
    have hempty : prefixFiber (k := k) h e eN = ∅ := by
      ext xs
      constructor
      · intro hxs
        have hs : prefixState (k := k) (n := n) (N := N) h xs ∈ stateFinset k n :=
          prefixState_mem_stateFinset (k := k) (h := h) xs
        have : prefixState (k := k) (n := n) (N := N) h xs = e := (Finset.mem_filter.1 hxs).2
        exact (he (by simpa [this] using hs)).elim
      · intro hxs
        -- `xs ∈ ∅` is impossible.
        exact (False.elim (Finset.notMem_empty xs hxs))
    simp [prefixCoeff, hcard, hempty]

/-! ## Evidence weights `wμ` and evidence polynomials `W` -/

/-- Weight of an evidence state under a prefix measure `μ` at horizon `n`. -/
def wμ (μ : PrefixMeasure (Fin k)) (n : ℕ) (e : MarkovState k) : ENNReal :=
  ∑ xs ∈ (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e),
    μ (trajToList (k := k) xs)

lemma wμ_eq_sum_fiber
    (μ : PrefixMeasure (Fin k)) (N : ℕ) (eN : MarkovState k) :
    wμ (k := k) μ N eN =
      ∑ xs ∈ fiber k N eN, μ (trajToList (k := k) xs) := by
  rfl

lemma prefixFiber_subset_fiber {n N : ℕ} (h : n ≤ N) (e : MarkovState k) (eN : MarkovState k) :
    prefixFiber (k := k) h e eN ⊆ fiber k N eN := by
  intro xs hx
  exact (Finset.mem_filter.1 hx).1

/-! ### Tower identities (prefix-mass regrouping) -/

/-- The mass of length-`N+1` trajectories whose length-`n+1` prefix has evidence state `e`. -/
def prefixMass (μ : PrefixMeasure (Fin k)) {n N : ℕ} (h : n ≤ N) (e : MarkovState k) : ENNReal :=
  ∑ xs : Traj k N, if prefixState (k := k) h xs = e then μ (trajToList (k := k) xs) else 0

lemma prefixMass_eq_sum_filter
    (μ : PrefixMeasure (Fin k)) {n N : ℕ} (h : n ≤ N) (e : MarkovState k) :
    prefixMass (k := k) μ h e =
      ∑ xs ∈ (trajFinset k N).filter (fun xs => prefixState (k := k) h xs = e),
        μ (trajToList (k := k) xs) := by
  classical
  -- `trajFinset` is `univ`, so the `Fintype` sum is the `Finset` sum over `univ` with an `if`.
  simp [prefixMass, trajFinset, Finset.sum_filter]

lemma prefixMass_base
    (μ : PrefixMeasure (Fin k)) (n : ℕ) (e : MarkovState k) :
    prefixMass (k := k) μ (n := n) (N := n) (le_rfl) e = wμ (k := k) μ n e := by
  classical
  -- For `N = n`, `prefixState` is definitional `stateOfTraj`, so `prefixMass` is the indicator
  -- sum defining `wμ`.
  simp [prefixMass, wμ, prefixState, trajFinset, Finset.sum_filter]

lemma prefixMass_succ
    (μ : PrefixMeasure (Fin k)) {n N : ℕ} (h : n ≤ N) (e : MarkovState k) :
    prefixMass (k := k) μ (n := n) (N := N + 1) (Nat.le_trans h (Nat.le_succ N)) e =
      prefixMass (k := k) μ (n := n) (N := N) h e := by
  classical
  -- Split `Traj k (N+1)` into its initial `N+1` trajectory and last symbol using `Fin.snocEquiv`.
  -- Then use `μ.additive'` to sum out the last symbol, and `prefixState_trajSnoc` to show the
  -- prefix evidence state is unchanged by appending.
  have hEquiv :
      (∑ p : (Fin k) × (Traj k N),
            if prefixState (k := k) (n := n) (N := N + 1) (Nat.le_trans h (Nat.le_succ N))
                (trajSnoc (k := k) p.2 p.1) = e then
              μ (trajToList (k := k) (trajSnoc (k := k) p.2 p.1)) else 0) =
        ∑ xs : Traj k (N + 1),
            if prefixState (k := k) (n := n) (N := N + 1) (Nat.le_trans h (Nat.le_succ N)) xs = e then
              μ (trajToList (k := k) xs) else 0 := by
    -- `Fin.snocEquiv` has type `Fin k × Traj k N ≃ Traj k (N+1)`.
    refine (Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (N + 2) => Fin k))
      (fun p => if prefixState (k := k) (n := n) (N := N + 1) (Nat.le_trans h (Nat.le_succ N))
                  (trajSnoc (k := k) p.2 p.1) = e then
                μ (trajToList (k := k) (trajSnoc (k := k) p.2 p.1)) else 0)
      (fun xs => if prefixState (k := k) (n := n) (N := N + 1) (Nat.le_trans h (Nat.le_succ N)) xs = e then
                μ (trajToList (k := k) xs) else 0) ?_)
    intro p
    -- `Fin.snocEquiv` is definitional `trajSnoc` in this constant-codomain setting.
    rfl
  -- Rewrite the LHS of the goal using `hEquiv`, then compute the sum over the product type.
  -- `p.1` is the last symbol, `p.2` is the initial trajectory.
  -- The prefix evidence state depends only on `p.2` (by `prefixState_trajSnoc`), so the `if`
  -- factor is independent of `p.1` and we can use `μ.additive'`.
  have hOfFn : ∀ (xs : Traj k N) (x : Fin k),
      μ (trajToList (k := k) (trajSnoc (k := k) xs x)) = μ (trajToList (k := k) xs ++ [x]) := by
    intro xs x
    simp [trajToList_trajSnoc (k := k) (xs := xs) (x := x)]
  unfold prefixMass
  -- Use the equivalence to rewrite the `Fintype` sum.
  -- `hEquiv` is oriented `(∑ p, ...) = (∑ xs, ...)`, so rewrite the goal's LHS.
  have hsum :
      (∑ xs : Traj k (N + 1),
          if prefixState (k := k) (n := n) (N := N + 1) (Nat.le_trans h (Nat.le_succ N)) xs = e then
            μ (trajToList (k := k) xs) else 0) =
        (∑ p : (Fin k) × (Traj k N),
          if prefixState (k := k) (n := n) (N := N + 1) (Nat.le_trans h (Nat.le_succ N))
              (trajSnoc (k := k) p.2 p.1) = e then
            μ (trajToList (k := k) (trajSnoc (k := k) p.2 p.1)) else 0) := by
    simpa using hEquiv.symm
  -- Reduce the sum over the product type.
  -- First, swap summations and factor the condition which depends only on `p.2`.
  -- Then apply `μ.additive'` to eliminate the last symbol.
  -- Finally, use `prefixState_trajSnoc` to simplify the condition.
  -- This is a direct analogue of the `prefixPMF` recursion proof.
  -- (We keep it as a separate `calc` block for clarity.)
  calc
    (∑ xs : Traj k (N + 1),
        if prefixState (k := k) (n := n) (N := N + 1) (Nat.le_trans h (Nat.le_succ N)) xs = e then
          μ (trajToList (k := k) xs) else 0)
        =
      ∑ p : (Fin k) × (Traj k N),
        if prefixState (k := k) (n := n) (N := N + 1) (Nat.le_trans h (Nat.le_succ N))
            (trajSnoc (k := k) p.2 p.1) = e then
          μ (trajToList (k := k) (trajSnoc (k := k) p.2 p.1)) else 0 := by
            simp [hsum]
    _ =
      ∑ xs : Traj k N,
        ∑ x : Fin k,
          if prefixState (k := k) (n := n) (N := N) h xs = e then
            μ (trajToList (k := k) xs ++ [x]) else 0 := by
            -- Rewrite the sum over the product type as iterated sum over the second component,
            -- then simplify the prefix-state condition and list append form.
            simp [Fintype.sum_prod_type_right, prefixState_trajSnoc (k := k) (h := h), hOfFn]
    _ =
      ∑ xs : Traj k N,
        if prefixState (k := k) (n := n) (N := N) h xs = e then
          μ (trajToList (k := k) xs) else 0 := by
            -- Use `μ.additive'` on the last symbol sum when the condition holds.
            refine Fintype.sum_congr (fun xs => ∑ x : Fin k,
              if prefixState (k := k) (n := n) (N := N) h xs = e then
                μ (trajToList (k := k) xs ++ [x]) else 0)
              (fun xs => if prefixState (k := k) (n := n) (N := N) h xs = e then
                μ (trajToList (k := k) xs) else 0) ?_
            intro xs
            by_cases hx : prefixState (k := k) (n := n) (N := N) h xs = e
            · -- condition true: use additivity
              simp [hx, μ.additive' (trajToList (k := k) xs)]
            · -- condition false: both sides are 0
              simp [hx]
    _ = prefixMass (k := k) μ (n := n) (N := N) h e := by
          rfl

lemma prefixMass_eq_wμ
    (μ : PrefixMeasure (Fin k)) {n N : ℕ} (h : n ≤ N) (e : MarkovState k) :
    prefixMass (k := k) μ (n := n) (N := N) h e = wμ (k := k) μ n e := by
  classical
  -- Prove by induction over horizons `N` starting at `n`.  The predicate depends on the proof
  -- `n ≤ N`, matching `Nat.le_induction`'s binder.
  refine Nat.le_induction (m := n)
    (P := fun N hN => prefixMass (k := k) μ (n := n) (N := N) hN e = wμ (k := k) μ n e)
    ?base ?succ N h
  · simpa using prefixMass_base (k := k) (μ := μ) n e
  · intro N hN ih
    exact (prefixMass_succ (k := k) (μ := μ) (n := n) (N := N) (h := hN) e).trans ih

lemma wμ_eq_card_mul_of_state
    (μ : PrefixMeasure (Fin k)) (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    {n : ℕ} {e : MarkovState k} {xs0 : Traj k n}
    (hxs0 : stateOfTraj (k := k) xs0 = e) :
    wμ (k := k) μ n e =
      (( (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e)).card : ENNReal) *
        μ (trajToList (k := k) xs0) := by
  classical
  -- All terms in the sum are equal by Markov exchangeability.
  have hconst :
      ∀ xs ∈ (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e),
        μ (trajToList (k := k) xs) = μ (trajToList (k := k) xs0) := by
    intro xs hxs
    -- Extract the state equality from the filter.
    have hxse : stateOfTraj (k := k) xs = e := by
      simpa using (Finset.mem_filter.1 hxs).2
    exact mu_const_on_state_fiber (k := k) (μ := μ) hμ (hxs0 ▸ hxse)
  -- Rewrite the sum as a constant sum.
  have hsum :
      (∑ xs ∈ (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e),
          μ (trajToList (k := k) xs))
        =
      (∑ xs ∈ (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e),
          μ (trajToList (k := k) xs0)) := by
    refine Finset.sum_congr rfl ?_
    intro xs hxs
    exact hconst xs hxs
  -- Evaluate the constant sum.
  calc
    wμ (k := k) μ n e
        = (∑ xs ∈ (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e),
            μ (trajToList (k := k) xs)) := by rfl
    _ = (∑ xs ∈ (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e),
            μ (trajToList (k := k) xs0)) := hsum
    _ = (( (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e)).card : ENNReal) *
          μ (trajToList (k := k) xs0) := by
          -- `Finset.sum_const` for `ENNReal`
          simp [Finset.sum_const, mul_comm]

lemma wμ_prefix_eq_coeff_mul
    (μ : PrefixMeasure (Fin k)) (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    {n N : ℕ} (h : n ≤ N) (e : MarkovState k) (eN : MarkovState k) :
    (∑ xs ∈ prefixFiber (k := k) h e eN, μ (trajToList (k := k) xs)) =
      prefixCoeff (k := k) h e eN * wμ (k := k) μ N eN := by
  classical
  by_cases hcard : (fiber k N eN).card = 0
  · -- Empty fiber: both sides are 0.
    have hfiber : fiber k N eN = ∅ := by
      simpa [Finset.card_eq_zero] using hcard
    simp [prefixCoeff, wμ_eq_sum_fiber, hfiber, prefixFiber]
  · -- Nonempty fiber: μ is constant on the fiber.
    have hnonempty : (fiber k N eN).Nonempty := by
      exact Finset.card_ne_zero.mp hcard
    rcases hnonempty with ⟨xs0, hxs0⟩
    have hxs0' : stateOfTraj (k := k) xs0 = eN := by
      exact (Finset.mem_filter.1 hxs0).2
    have hconst :
        ∀ xs ∈ prefixFiber (k := k) h e eN,
          μ (trajToList (k := k) xs) = μ (trajToList (k := k) xs0) := by
      intro xs hxs
      have hxsf : xs ∈ fiber k N eN := prefixFiber_subset_fiber (k := k) h e eN hxs
      have hxse : stateOfTraj (k := k) xs = eN := by
        exact (Finset.mem_filter.1 hxsf).2
      exact mu_const_on_state_fiber (k := k) (μ := μ) hμ (by simpa [hxs0'] using hxse)
    -- Sum over the prefix fiber is constant.
    have hsum :
        (∑ xs ∈ prefixFiber (k := k) h e eN, μ (trajToList (k := k) xs)) =
          ((prefixFiber (k := k) h e eN).card : ENNReal) * μ (trajToList (k := k) xs0) := by
      have hsum' :
          (∑ xs ∈ prefixFiber (k := k) h e eN, μ (trajToList (k := k) xs)) =
            (∑ xs ∈ prefixFiber (k := k) h e eN, μ (trajToList (k := k) xs0)) := by
        refine Finset.sum_congr rfl ?_
        intro xs hxs
        exact hconst xs hxs
      calc
        (∑ xs ∈ prefixFiber (k := k) h e eN, μ (trajToList (k := k) xs))
            = (∑ xs ∈ prefixFiber (k := k) h e eN, μ (trajToList (k := k) xs0)) := hsum'
        _ = ((prefixFiber (k := k) h e eN).card : ENNReal) * μ (trajToList (k := k) xs0) := by
              simp [Finset.sum_const, mul_comm]
    -- Use the existing fiber-card formula for `wμ`.
    have hwμ :
        wμ (k := k) μ N eN =
          ((fiber k N eN).card : ENNReal) * μ (trajToList (k := k) xs0) := by
      simpa [wμ_eq_sum_fiber] using
        (wμ_eq_card_mul_of_state (k := k) (μ := μ) hμ (n := N) (e := eN) (xs0 := xs0) hxs0')
    have hcard_ne0 : ((fiber k N eN).card : ENNReal) ≠ 0 := by
      exact_mod_cast hcard
    have hcard_ne_top : ((fiber k N eN).card : ENNReal) ≠ (⊤ : ENNReal) := by
      simp
    -- Assemble the coefficient identity.
    calc
      (∑ xs ∈ prefixFiber (k := k) h e eN, μ (trajToList (k := k) xs))
          = ((prefixFiber (k := k) h e eN).card : ENNReal) * μ (trajToList (k := k) xs0) := hsum
      _ = (((prefixFiber (k := k) h e eN).card : ENNReal) / ((fiber k N eN).card : ENNReal)) *
            (((fiber k N eN).card : ENNReal) * μ (trajToList (k := k) xs0)) := by
            calc
              ((prefixFiber (k := k) h e eN).card : ENNReal) * μ (trajToList (k := k) xs0)
                  = (((prefixFiber (k := k) h e eN).card : ENNReal) / ((fiber k N eN).card : ENNReal) *
                      ((fiber k N eN).card : ENNReal)) * μ (trajToList (k := k) xs0) := by
                        simp [ENNReal.div_mul_cancel hcard_ne0 hcard_ne_top]
              _ = (((prefixFiber (k := k) h e eN).card : ENNReal) / ((fiber k N eN).card : ENNReal)) *
                    (((fiber k N eN).card : ENNReal) * μ (trajToList (k := k) xs0)) := by
                      simp [mul_assoc, mul_comm]
      _ = prefixCoeff (k := k) h e eN * wμ (k := k) μ N eN := by
            simp [prefixCoeff, hcard, hwμ]

/-- Tower identity: the mass `wμ n e` can be regrouped by the final evidence class at horizon `N`. -/
theorem wμ_eq_sum_prefixCoeff_mul_wμ
    (μ : PrefixMeasure (Fin k)) (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    {n N : ℕ} (h : n ≤ N) (e : MarkovState k) :
    wμ (k := k) μ n e =
      ∑ eN ∈ stateFinset k N, prefixCoeff (k := k) h e eN * wμ (k := k) μ N eN := by
  classical
  -- Start from the prefix-mass view at horizon `N` and regroup by the final evidence state.
  have hprefix :
      wμ (k := k) μ n e =
        ∑ xs ∈ (trajFinset k N).filter (fun xs => prefixState (k := k) h xs = e),
          μ (trajToList (k := k) xs) := by
    have hm :
        wμ (k := k) μ n e = prefixMass (k := k) μ (n := n) (N := N) h e := by
      simpa using (prefixMass_eq_wμ (k := k) (μ := μ) (n := n) (N := N) h e).symm
    have hm' :
        prefixMass (k := k) μ (n := n) (N := N) h e =
          ∑ xs ∈ (trajFinset k N).filter (fun xs => prefixState (k := k) h xs = e),
            μ (trajToList (k := k) xs) :=
      prefixMass_eq_sum_filter (k := k) (μ := μ) (n := n) (N := N) h e
    exact hm.trans hm'

  -- Regroup the RHS by the final evidence state `eN = stateOfTraj xs`.
  let f : Traj k N → ENNReal :=
    fun xs => if prefixState (k := k) h xs = e then μ (trajToList (k := k) xs) else 0

  have hfilter :
      ∀ eN : MarkovState k,
        (∑ xs ∈ (trajFinset k N).filter (fun xs => stateOfTraj (k := k) xs = eN), f xs) =
          ∑ xs ∈ trajFinset k N, (if stateOfTraj (k := k) xs = eN then f xs else 0) := by
    intro eN
    simpa [f] using
      (Finset.sum_filter (s := trajFinset k N) (p := fun xs => stateOfTraj (k := k) xs = eN) (f := f))

  have hswap :
      (∑ eN ∈ stateFinset k N,
          ∑ xs ∈ trajFinset k N, (if stateOfTraj (k := k) xs = eN then f xs else 0)) =
        ∑ xs ∈ trajFinset k N,
          ∑ eN ∈ stateFinset k N, (if stateOfTraj (k := k) xs = eN then f xs else 0) := by
    exact
      (Finset.sum_comm (s := stateFinset k N) (t := trajFinset k N)
        (f := fun eN xs => if stateOfTraj (k := k) xs = eN then f xs else 0))

  have hcollapse :
      ∀ xs : Traj k N,
        (∑ eN ∈ stateFinset k N, (if stateOfTraj (k := k) xs = eN then f xs else 0)) = f xs := by
    intro xs
    have hmem : stateOfTraj (k := k) xs ∈ stateFinset k N :=
      stateOfTraj_mem_stateFinset (k := k) xs
    simp [eq_comm, hmem, f]

  have hregroup :
      (∑ xs ∈ (trajFinset k N).filter (fun xs => prefixState (k := k) h xs = e),
          μ (trajToList (k := k) xs)) =
        ∑ eN ∈ stateFinset k N,
          ∑ xs ∈ prefixFiber (k := k) h e eN, μ (trajToList (k := k) xs) := by
    -- Rewrite the LHS as a sum over `trajFinset` with indicator `f`.
    have hlhs :
        (∑ xs ∈ (trajFinset k N).filter (fun xs => prefixState (k := k) h xs = e),
            μ (trajToList (k := k) xs)) =
          ∑ xs ∈ trajFinset k N, f xs := by
      simpa [f] using
        (Finset.sum_filter (s := trajFinset k N) (p := fun xs => prefixState (k := k) h xs = e)
          (f := fun xs => μ (trajToList (k := k) xs)))
    calc
      (∑ xs ∈ (trajFinset k N).filter (fun xs => prefixState (k := k) h xs = e),
            μ (trajToList (k := k) xs))
          = ∑ xs ∈ trajFinset k N, f xs := hlhs
      _ = ∑ eN ∈ stateFinset k N,
            ∑ xs ∈ (trajFinset k N).filter (fun xs => stateOfTraj (k := k) xs = eN), f xs := by
            -- Regroup by evidence class using the standard indicator-sum trick.
            have :
                (∑ xs ∈ trajFinset k N, f xs) =
                  ∑ eN ∈ stateFinset k N,
                    ∑ xs ∈ (trajFinset k N).filter (fun xs => stateOfTraj (k := k) xs = eN), f xs := by
              calc
                (∑ xs ∈ trajFinset k N, f xs)
                    = ∑ xs ∈ trajFinset k N,
                        ∑ eN ∈ stateFinset k N, (if stateOfTraj (k := k) xs = eN then f xs else 0) := by
                          refine Finset.sum_congr rfl ?_
                          intro xs hxs
                          simp [hcollapse xs]
                _ = ∑ eN ∈ stateFinset k N,
                        ∑ xs ∈ trajFinset k N, (if stateOfTraj (k := k) xs = eN then f xs else 0) := by
                          simp [hswap]
                _ = ∑ eN ∈ stateFinset k N,
                        ∑ xs ∈ (trajFinset k N).filter (fun xs => stateOfTraj (k := k) xs = eN), f xs := by
                          refine Finset.sum_congr rfl ?_
                          intro eN heN
                          simp [hfilter eN]
            simp [this]
      _ = ∑ eN ∈ stateFinset k N,
            ∑ xs ∈ prefixFiber (k := k) h e eN, μ (trajToList (k := k) xs) := by
            refine Finset.sum_congr rfl ?_
            intro eN heN
            -- Replace the `if` inside `f` by an extra filter.
            -- This is exactly the definition of `prefixFiber`.
            simpa [fiber, prefixFiber, f] using
              (Finset.sum_filter (s := fiber k N eN)
                (p := fun xs => prefixState (k := k) h xs = e)
                (f := fun xs => μ (trajToList (k := k) xs))).symm

  -- Finish by applying `wμ_prefix_eq_coeff_mul` inside the regrouped sum.
  calc
    wμ (k := k) μ n e
        = ∑ xs ∈ (trajFinset k N).filter (fun xs => prefixState (k := k) h xs = e),
            μ (trajToList (k := k) xs) := hprefix
    _ = ∑ eN ∈ stateFinset k N,
          ∑ xs ∈ prefixFiber (k := k) h e eN, μ (trajToList (k := k) xs) := hregroup
    _ = ∑ eN ∈ stateFinset k N,
          prefixCoeff (k := k) h e eN * wμ (k := k) μ N eN := by
          refine Finset.sum_congr rfl ?_
          intro eN heN
          simpa using (wμ_prefix_eq_coeff_mul (k := k) (μ := μ) hμ (h := h) (e := e) (eN := eN))

/-- For any fixed Markov parameter `θ`, `wordProb θ` is constant on evidence fibers, hence the sum
over a prefix fiber is `prefixCoeff *` the sum over the full fiber. -/
lemma wordProb_prefix_eq_coeff_mul
    (θ : MarkovParam k)
    {n N : ℕ} (h : n ≤ N) (e : MarkovState k) (eN : MarkovState k) :
    (∑ xs ∈ prefixFiber (k := k) h e eN, wordProb (k := k) θ (trajToList (k := k) xs)) =
      prefixCoeff (k := k) h e eN *
        (∑ xs ∈ fiber k N eN, wordProb (k := k) θ (trajToList (k := k) xs)) := by
  classical
  by_cases hcard : (fiber k N eN).card = 0
  · -- Empty fiber: both sides are 0.
    have hfiber : fiber k N eN = ∅ := by
      simpa [Finset.card_eq_zero] using hcard
    simp [prefixCoeff, hfiber, prefixFiber]
  · -- Nonempty fiber: `wordProb` is constant on the fiber.
    have hnonempty : (fiber k N eN).Nonempty := Finset.card_ne_zero.mp hcard
    rcases hnonempty with ⟨xs0, hxs0⟩
    have hxs0' : stateOfTraj (k := k) xs0 = eN := (Finset.mem_filter.1 hxs0).2
    have hconst :
        ∀ xs ∈ prefixFiber (k := k) h e eN,
          wordProb (k := k) θ (trajToList (k := k) xs) =
            wordProb (k := k) θ (trajToList (k := k) xs0) := by
      intro xs hxs
      have hxsf : xs ∈ fiber k N eN := prefixFiber_subset_fiber (k := k) h e eN hxs
      have hxse : stateOfTraj (k := k) xs = eN := (Finset.mem_filter.1 hxsf).2
      exact wordProb_const_on_state_fiber (k := k) (θ := θ) (by simpa [hxs0'] using hxse)
    have hsumPrefix :
        (∑ xs ∈ prefixFiber (k := k) h e eN, wordProb (k := k) θ (trajToList (k := k) xs)) =
          ((prefixFiber (k := k) h e eN).card : ENNReal) *
            wordProb (k := k) θ (trajToList (k := k) xs0) := by
      have hsum' :
          (∑ xs ∈ prefixFiber (k := k) h e eN, wordProb (k := k) θ (trajToList (k := k) xs)) =
            (∑ xs ∈ prefixFiber (k := k) h e eN, wordProb (k := k) θ (trajToList (k := k) xs0)) := by
        refine Finset.sum_congr rfl ?_
        intro xs hxs
        exact hconst xs hxs
      calc
        (∑ xs ∈ prefixFiber (k := k) h e eN, wordProb (k := k) θ (trajToList (k := k) xs))
            = (∑ xs ∈ prefixFiber (k := k) h e eN,
                wordProb (k := k) θ (trajToList (k := k) xs0)) := hsum'
        _ = ((prefixFiber (k := k) h e eN).card : ENNReal) *
              wordProb (k := k) θ (trajToList (k := k) xs0) := by
              simp [Finset.sum_const, mul_comm]
    have hsumFiber :
        (∑ xs ∈ fiber k N eN, wordProb (k := k) θ (trajToList (k := k) xs)) =
          ((fiber k N eN).card : ENNReal) *
            wordProb (k := k) θ (trajToList (k := k) xs0) := by
      have hconstF :
          ∀ xs ∈ fiber k N eN,
            wordProb (k := k) θ (trajToList (k := k) xs) =
              wordProb (k := k) θ (trajToList (k := k) xs0) := by
        intro xs hxs
        have hxse : stateOfTraj (k := k) xs = eN := (Finset.mem_filter.1 hxs).2
        exact wordProb_const_on_state_fiber (k := k) (θ := θ) (by simpa [hxs0'] using hxse)
      have hsum' :
          (∑ xs ∈ fiber k N eN, wordProb (k := k) θ (trajToList (k := k) xs)) =
            (∑ xs ∈ fiber k N eN, wordProb (k := k) θ (trajToList (k := k) xs0)) := by
        refine Finset.sum_congr rfl ?_
        intro xs hxs
        exact hconstF xs hxs
      calc
        (∑ xs ∈ fiber k N eN, wordProb (k := k) θ (trajToList (k := k) xs))
            = (∑ xs ∈ fiber k N eN,
                wordProb (k := k) θ (trajToList (k := k) xs0)) := hsum'
        _ = ((fiber k N eN).card : ENNReal) *
              wordProb (k := k) θ (trajToList (k := k) xs0) := by
              simp [Finset.sum_const, mul_comm]
    have hcard_ne0 : ((fiber k N eN).card : ENNReal) ≠ 0 := by
      exact_mod_cast hcard
    have hcard_ne_top : ((fiber k N eN).card : ENNReal) ≠ (⊤ : ENNReal) := by
      simp
    -- Assemble the coefficient identity.
    calc
      (∑ xs ∈ prefixFiber (k := k) h e eN, wordProb (k := k) θ (trajToList (k := k) xs))
          = ((prefixFiber (k := k) h e eN).card : ENNReal) *
              wordProb (k := k) θ (trajToList (k := k) xs0) := hsumPrefix
      _ = (((prefixFiber (k := k) h e eN).card : ENNReal) / ((fiber k N eN).card : ENNReal)) *
            (((fiber k N eN).card : ENNReal) *
              wordProb (k := k) θ (trajToList (k := k) xs0)) := by
            calc
              ((prefixFiber (k := k) h e eN).card : ENNReal) *
                  wordProb (k := k) θ (trajToList (k := k) xs0)
                  =
                  (((prefixFiber (k := k) h e eN).card : ENNReal) / ((fiber k N eN).card : ENNReal) *
                      ((fiber k N eN).card : ENNReal)) *
                    wordProb (k := k) θ (trajToList (k := k) xs0) := by
                      simp [ENNReal.div_mul_cancel hcard_ne0 hcard_ne_top]
              _ = (((prefixFiber (k := k) h e eN).card : ENNReal) / ((fiber k N eN).card : ENNReal)) *
                    (((fiber k N eN).card : ENNReal) *
                      wordProb (k := k) θ (trajToList (k := k) xs0)) := by
                      simp [mul_assoc, mul_comm]
      _ = prefixCoeff (k := k) h e eN *
            (∑ xs ∈ fiber k N eN, wordProb (k := k) θ (trajToList (k := k) xs)) := by
            simp [prefixCoeff, hcard, hsumFiber]

/-- Evidence polynomial: probability (under parameter `θ`) of landing in evidence class `e` at
horizon `n`, computed by summing `wordProb θ` over the fiber. -/
def W (n : ℕ) (e : MarkovState k) : MarkovParam k → ℝ≥0∞ :=
  fun θ =>
    ∑ xs ∈ (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e),
      wordProb (k := k) θ (trajToList (k := k) xs)

/-- For `μθ := wordProbPrefixMeasure θ`, the evidence weight `wμ μθ n e` is exactly `W n e θ`. -/
lemma wμ_wordProbPrefixMeasure_eq_W (θ : MarkovParam k) (n : ℕ) (e : MarkovState k) :
    wμ (k := k) (wordProbPrefixMeasure (k := k) θ) n e = W (k := k) n e θ := by
  classical
  simp [wμ, W, wordProbPrefixMeasure]

/-- Tower identity for evidence polynomials: regroup by the final evidence class at horizon `N`. -/
theorem W_eq_sum_prefixCoeff_mul_W
    (θ : MarkovParam k) {n N : ℕ} (h : n ≤ N) (e : MarkovState k) :
    W (k := k) n e θ =
      ∑ eN ∈ stateFinset k N, prefixCoeff (k := k) h e eN * W (k := k) N eN θ := by
  -- Apply the already-proved tower identity for `wμ` to the prefix measure `wordProbPrefixMeasure θ`.
  let μθ : PrefixMeasure (Fin k) := wordProbPrefixMeasure (k := k) θ
  have hμθ : MarkovExchangeablePrefixMeasure (k := k) μθ :=
    wordProbPrefixMeasure_markovExchangeable (k := k) θ
  have hw :
      wμ (k := k) μθ n e =
        ∑ eN ∈ stateFinset k N, prefixCoeff (k := k) h e eN * wμ (k := k) μθ N eN :=
    wμ_eq_sum_prefixCoeff_mul_wμ (k := k) (μ := μθ) hμθ (h := h) (e := e)
  -- Rewrite `wμ μθ` as `W θ`.
  simpa [μθ, wμ_wordProbPrefixMeasure_eq_W (k := k) (θ := θ)] using hw

/-! ## `ℝ`-valued evidence polynomials live in the coordinate subalgebra -/

/-- `ℝ`-valued evidence polynomial (finite sum of `wordProbReal`). -/
def Wreal (n : ℕ) (e : MarkovState k) : C(MarkovParam k, ℝ) :=
  (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e)
    |>.sum (fun xs => wordProbReal (k := k) (trajToList (k := k) xs))

lemma Wreal_apply (n : ℕ) (e : MarkovState k) (θ : MarkovParam k) :
    Wreal (k := k) n e θ =
      ∑ xs ∈ (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e),
        (wordProbNN (k := k) θ (trajToList (k := k) xs) : ℝ) := by
  classical
  -- unfold and use `wordProbReal_apply`
  simp [Wreal, wordProbReal_apply]

lemma Wreal_mem_coordSubalg (n : ℕ) (e : MarkovState k) :
    Wreal (k := k) n e ∈ coordSubalg (k := k) := by
  classical
  -- `coordSubalg` is closed under finite sums; each `wordProbReal` term lies in it.
  -- We prove this by induction on the filtered finite set.
  let s : Finset (Traj k n) :=
    (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e)
  have hterm : ∀ xs : Traj k n,
      wordProbReal (k := k) (trajToList (k := k) xs) ∈ coordSubalg (k := k) := by
    intro xs
    exact wordProbReal_mem_coordSubalg (k := k) (trajToList (k := k) xs)
  -- Use the Subalgebra sum lemma directly.
  have hsum :
      s.sum (fun xs => wordProbReal (k := k) (trajToList (k := k) xs)) ∈ coordSubalg (k := k) := by
    refine Subalgebra.sum_mem (S := coordSubalg (k := k)) ?_
    intro xs hxs
    exact hterm xs
  -- Unfold `Wreal` and rewrite to the `Finset.sum` form.
  simpa [Wreal, s] using hsum

@[simp] lemma wμ_nonneg (μ : PrefixMeasure (Fin k)) (n : ℕ) (e : MarkovState k) :
    0 ≤ wμ (k := k) μ n e := by
  classical
  simp [wμ]

lemma wμ_eq_zero_of_not_mem_stateFinset
    (μ : PrefixMeasure (Fin k)) (n : ℕ) (e : MarkovState k)
    (he : e ∉ stateFinset k n) :
    wμ (k := k) μ n e = 0 := by
  classical
  -- If `e` is not realized by any trajectory, the filtered finset is empty.
  have hnone :
      ∀ xs ∈ trajFinset k n, stateOfTraj (k := k) xs ≠ e := by
    intro xs hxs hxe
    -- Then `e` would be in the image.
    have : e ∈ stateFinset k n := by
      refine Finset.mem_image.2 ?_
      exact ⟨xs, hxs, hxe⟩
    exact (he this).elim
  have hfilter :
      (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro xs hxs
    exact hnone xs hxs
  simp [wμ, hfilter]

@[simp] lemma W_nonneg (n : ℕ) (e : MarkovState k) (θ : MarkovParam k) :
    0 ≤ W (k := k) n e θ := by
  classical
  simp [W]

/-! ## Partition-of-unity identities (finite, hence proof-friendly) -/

private lemma sum_wordProb_trajToList_eq_one (θ : MarkovParam k) (n : ℕ) :
    (∑ xs : Traj k n, wordProb (k := k) θ (trajToList (k := k) xs)) = 1 := by
  classical
  -- Package `wordProb` as a finite-alphabet prefix measure and use `prefixPMF`'s normalization.
  -- TODO: build `PrefixMeasure` for `wordProb` and reuse `FiniteAlphabet.prefixPMF`.
  -- First show that singleton masses of a `ProbabilityMeasure (Fin k)` sum to `1` (in `NNReal`).
  have sum_singleton_eq_one (μ0 : MeasureTheory.ProbabilityMeasure (Fin k)) :
      (∑ a : Fin k, μ0 (Set.singleton a)) = 1 := by
    classical
    let μ : Measure (Fin k) := (μ0 : Measure (Fin k))
    -- Work in `ENNReal` first, using the finite partition of `univ` by singletons.
    have hsum0 :
        (∑ a ∈ (Finset.univ : Finset (Fin k)), μ (Set.singleton a)) =
          μ (Finset.univ : Finset (Fin k)) :=
      (MeasureTheory.sum_measure_singleton (μ := μ) (s := (Finset.univ : Finset (Fin k))))
    have hsum :
        (∑ a : Fin k, μ (Set.singleton a)) = μ Set.univ := by
      -- Avoid `simp` on `hsum0` (it would rewrite it to `True` using `[simp]` itself).
      simpa [μ, Finset.coe_univ] using hsum0
    have hμuniv : μ Set.univ = 1 := by
      simp [μ]
    have hsum1 : (∑ a : Fin k, μ (Set.singleton a)) = (1 : ENNReal) := by
      simpa [hμuniv] using hsum
    -- Convert the ENNReal identity to NNReal by `toNNReal`, distributing over finite sums.
    have hf :
        ∀ a ∈ (Finset.univ : Finset (Fin k)), μ (Set.singleton a) ≠ (⊤ : ENNReal) := by
      intro a ha
      simp [μ]
    have htoNN :
        ENNReal.toNNReal (∑ a : Fin k, μ (Set.singleton a)) =
          ∑ a : Fin k, ENNReal.toNNReal (μ (Set.singleton a)) := by
      simpa using
        (ENNReal.toNNReal_sum (s := (Finset.univ : Finset (Fin k)))
          (f := fun a : Fin k => μ (Set.singleton a)) hf)
    have hpm :
        (∑ a : Fin k, μ0 (Set.singleton a)) =
          ∑ a : Fin k, ENNReal.toNNReal (μ (Set.singleton a)) := by
      simp [MeasureTheory.ProbabilityMeasure.coeFn_def, μ]
    calc
      (∑ a : Fin k, μ0 (Set.singleton a))
          = ∑ a : Fin k, ENNReal.toNNReal (μ (Set.singleton a)) := hpm
      _ = ENNReal.toNNReal (∑ a : Fin k, μ (Set.singleton a)) := by
            exact htoNN.symm
      _ = ENNReal.toNNReal (1 : ENNReal) := by
            simp [hsum1]
      _ = 1 := by simp

  -- Markov recursion: show the auxiliary tail kernel is prefix-additive.
  have wordProbAux_additive (prev : Fin k) :
      ∀ xs : List (Fin k),
        (∑ a : Fin k, wordProbAux (k := k) θ prev (xs ++ [a])) =
          wordProbAux (k := k) θ prev xs := by
    intro xs
    induction xs generalizing prev with
    | nil =>
        -- `xs = []`: `wordProbAux prev [a] = stepProb prev a`, and `∑ a, stepProb prev a = 1`.
        have hstep : (∑ a : Fin k, stepProb (k := k) θ prev a) = 1 := by
          simpa [stepProb] using (sum_singleton_eq_one (μ0 := θ.trans prev))
        -- Now simplify the goal to `hstep`.
        simpa [wordProbAux, stepProb, hstep]
    | cons b xs ih =>
        -- Factor out the constant first transition probability.
        have hmul :
            (∑ a : Fin k, stepProb (k := k) θ prev b * wordProbAux (k := k) θ b (xs ++ [a])) =
              stepProb (k := k) θ prev b * ∑ a : Fin k, wordProbAux (k := k) θ b (xs ++ [a]) := by
          -- `∑ a, c * f a = c * ∑ a, f a`.
          simpa using
            (Finset.mul_sum (a := stepProb (k := k) θ prev b)
              (s := (Finset.univ : Finset (Fin k)))
              (f := fun a : Fin k => wordProbAux (k := k) θ b (xs ++ [a]))).symm
        calc
          (∑ a : Fin k, wordProbAux (k := k) θ prev ((b :: xs) ++ [a]))
              = ∑ a : Fin k, stepProb (k := k) θ prev b * wordProbAux (k := k) θ b (xs ++ [a]) := by
                  simp [wordProbAux, List.cons_append]
          _ = stepProb (k := k) θ prev b * ∑ a : Fin k, wordProbAux (k := k) θ b (xs ++ [a]) := hmul
          _ = stepProb (k := k) θ prev b * wordProbAux (k := k) θ b xs := by
                simp [ih (prev := b)]
          _ = wordProbAux (k := k) θ prev (b :: xs) := by
                simp [wordProbAux]

  -- Now show `wordProb` is a `PrefixMeasure`, and use `prefixPMF` normalization.
  let μθ : PrefixMeasure (Fin k) :=
    { toFun := fun xs => wordProb (k := k) θ xs
      root_eq_one' := by
        simp [wordProb, wordProbNN]
      additive' := by
        intro xs
        classical
        cases xs with
        | nil =>
            -- `wordProb [a] = initProb a`, so the sum is `1`.
            have hinitNN : (∑ a : Fin k, initProb (k := k) θ a) = 1 := by
              simpa [initProb] using (sum_singleton_eq_one (μ0 := θ.init))
            have hinitENN : (∑ a : Fin k, (initProb (k := k) θ a : ENNReal)) = 1 := by
              have hcast :
                  ((∑ a : Fin k, initProb (k := k) θ a) : ENNReal) = (1 : ENNReal) := by
                simpa using congrArg (fun t : NNReal => (t : ENNReal)) hinitNN
              -- Rewrite the casted sum to a sum of casts.
              have hcoe :
                  ((∑ a : Fin k, initProb (k := k) θ a) : ENNReal) =
                    ∑ a : Fin k, (initProb (k := k) θ a : ENNReal) := by
                simp
              -- Finish.
              simpa [hcoe] using hcast
            simpa [wordProb, wordProbNN, wordProbAux] using hinitENN
        | cons a xs =>
            -- Factor out the fixed initial probability `initProb a`.
            have hmul :
                (∑ b : Fin k,
                      (initProb (k := k) θ a : ℝ≥0∞) *
                        (wordProbAux (k := k) θ a (xs ++ [b]) : ℝ≥0∞)) =
                  (initProb (k := k) θ a : ℝ≥0∞) *
                    ∑ b : Fin k, (wordProbAux (k := k) θ a (xs ++ [b]) : ℝ≥0∞) := by
              simpa using
                (Finset.mul_sum (a := (initProb (k := k) θ a : ℝ≥0∞))
                  (s := (Finset.univ : Finset (Fin k)))
                  (f := fun b : Fin k => (wordProbAux (k := k) θ a (xs ++ [b]) : ℝ≥0∞))).symm
            -- Use additivity of the auxiliary kernel.
            have haux :
                (∑ b : Fin k, (wordProbAux (k := k) θ a (xs ++ [b]) : ℝ≥0∞)) =
                  (wordProbAux (k := k) θ a xs : ℝ≥0∞) := by
              -- Coerce the NNReal equality, and rewrite casts so the sum is of casts (not a cast of a sum).
              have hNN : (∑ b : Fin k, wordProbAux (k := k) θ a (xs ++ [b])) =
                  wordProbAux (k := k) θ a xs := by
                simpa using (wordProbAux_additive (prev := a) xs)
              have hcast :
                  ((∑ b : Fin k, wordProbAux (k := k) θ a (xs ++ [b])) : ENNReal) =
                    (wordProbAux (k := k) θ a xs : ENNReal) := by
                simpa using congrArg (fun t : NNReal => (t : ENNReal)) hNN
              have hcoe :
                  ((∑ b : Fin k, wordProbAux (k := k) θ a (xs ++ [b])) : ENNReal) =
                    ∑ b : Fin k, (wordProbAux (k := k) θ a (xs ++ [b]) : ENNReal) := by
                simp
              -- Conclude.
              simpa [hcoe] using hcast
            calc
              (∑ b : Fin k, wordProb (k := k) θ ((a :: xs) ++ [b]))
                  = ∑ b : Fin k, (initProb (k := k) θ a : ℝ≥0∞) *
                        (wordProbAux (k := k) θ a (xs ++ [b]) : ℝ≥0∞) := by
                        simp [wordProb, wordProbNN, List.cons_append]
              _ = (initProb (k := k) θ a : ℝ≥0∞) *
                    ∑ b : Fin k, (wordProbAux (k := k) θ a (xs ++ [b]) : ℝ≥0∞) := hmul
              _ = (initProb (k := k) θ a : ℝ≥0∞) *
                    (wordProbAux (k := k) θ a xs : ℝ≥0∞) := by
                      simp [haux]
              _ = wordProb (k := k) θ (a :: xs) := by
                    simp [wordProb, wordProbNN]
    }

  -- `prefixPMF μθ (n+1)` is a PMF on length-`n+1` trajectories.
  have htsum : (∑' xs : Traj k n, μθ (trajToList (k := k) xs)) = 1 := by
    simpa [FiniteAlphabet.prefixPMF, trajToList] using
      (PMF.tsum_coe (FiniteAlphabet.prefixPMF μθ (n + 1)))
  -- Convert the `tsum` on a fintype into a finite sum.
  simpa [tsum_fintype, μθ, trajToList] using htsum

theorem sum_W_eq_one (n : ℕ) (θ : MarkovParam k) :
    (∑ e ∈ stateFinset k n, W (k := k) n e θ) =
      (∑ xs : Traj k n, wordProb (k := k) θ (trajToList (k := k) xs)) := by
  classical
  -- Each trajectory contributes exactly once, to its own evidence class.
  let f : Traj k n → ENNReal := fun xs => wordProb (k := k) θ (trajToList (k := k) xs)
  -- Rewrite the filtered fiber sum as an `ite` over all trajectories.
  have hfilter :
      ∀ e : MarkovState k,
        (∑ xs ∈ (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e), f xs) =
          ∑ xs ∈ trajFinset k n, (if stateOfTraj (k := k) xs = e then f xs else 0) := by
    intro e
    -- `sum_filter` expands the fiber sum.
    simpa [f] using
      (Finset.sum_filter (s := trajFinset k n) (p := fun xs => stateOfTraj (k := k) xs = e) (f := f))
  -- Now swap the two finite sums.
  have hswap :
      (∑ e ∈ stateFinset k n,
          ∑ xs ∈ trajFinset k n, (if stateOfTraj (k := k) xs = e then f xs else 0)) =
        ∑ xs ∈ trajFinset k n,
          ∑ e ∈ stateFinset k n, (if stateOfTraj (k := k) xs = e then f xs else 0) := by
    exact
      (Finset.sum_comm (s := stateFinset k n) (t := trajFinset k n)
        (f := fun e xs => if stateOfTraj (k := k) xs = e then f xs else 0))
  -- For a fixed trajectory, the inner sum over `e` collapses to `f xs`.
  have hcollapse :
      ∀ xs : Traj k n,
        (∑ e ∈ stateFinset k n, (if stateOfTraj (k := k) xs = e then f xs else 0)) = f xs := by
    intro xs
    have hmem : stateOfTraj (k := k) xs ∈ stateFinset k n :=
      stateOfTraj_mem_stateFinset (k := k) xs
    -- `sum_ite_eq` evaluates the sum of a single-support indicator.
    -- `Finset.sum_ite_eq` is stated using `e = a`; rewrite with `eq_comm`.
    simp [eq_comm, hmem]
  -- Put it together.
  calc
    (∑ e ∈ stateFinset k n, W (k := k) n e θ)
        = ∑ e ∈ stateFinset k n,
            ∑ xs ∈ (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e), f xs := by
              simp [W, f]
    _ = ∑ e ∈ stateFinset k n,
            ∑ xs ∈ trajFinset k n, (if stateOfTraj (k := k) xs = e then f xs else 0) := by
              refine Finset.sum_congr rfl ?_
              intro e he
              simp [hfilter e]
    _ = ∑ xs ∈ trajFinset k n,
            ∑ e ∈ stateFinset k n, (if stateOfTraj (k := k) xs = e then f xs else 0) := by
              simp [hswap]
    _ = ∑ xs ∈ trajFinset k n, f xs := by
          refine Finset.sum_congr rfl ?_
          intro xs hxs
          simp [hcollapse xs]
    _ = ∑ xs : Traj k n, f xs := by
          simp [trajFinset]
    _ = ∑ xs : Traj k n, wordProb (k := k) θ (trajToList (k := k) xs) := by
          rfl

theorem sum_W_eq_one' (n : ℕ) (θ : MarkovParam k) :
    (∑ e ∈ stateFinset k n, W (k := k) n e θ) = 1 := by
  classical
  -- Combine regrouping with the fact that the Markov kernel is a prefix measure.
  have hregroup := sum_W_eq_one (k := k) n θ
  -- TODO: finish once `sum_wordProb_trajToList_eq_one` is proved.
  simpa [hregroup] using (sum_wordProb_trajToList_eq_one (k := k) θ n)

-- Same statement with the `E_n` alias.
theorem sum_W_eq_one_E (n : ℕ) (θ : MarkovParam k) :
    (∑ e ∈ E_n k n, W (k := k) n e θ) = 1 := by
  simpa [E_n] using (sum_W_eq_one' (k := k) n θ)

theorem sum_wμ_eq_one (μ : PrefixMeasure (Fin k)) (n : ℕ) :
    (∑ e ∈ stateFinset k n, wμ (k := k) μ n e) =
      (∑ xs : Traj k n, μ (trajToList (k := k) xs)) := by
  classical
  let f : Traj k n → ENNReal := fun xs => μ (trajToList (k := k) xs)
  have hfilter :
      ∀ e : MarkovState k,
        (∑ xs ∈ (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e), f xs) =
          ∑ xs ∈ trajFinset k n, (if stateOfTraj (k := k) xs = e then f xs else 0) := by
    intro e
    simpa [f] using
      (Finset.sum_filter (s := trajFinset k n) (p := fun xs => stateOfTraj (k := k) xs = e) (f := f))
  have hswap :
      (∑ e ∈ stateFinset k n,
          ∑ xs ∈ trajFinset k n, (if stateOfTraj (k := k) xs = e then f xs else 0)) =
        ∑ xs ∈ trajFinset k n,
          ∑ e ∈ stateFinset k n, (if stateOfTraj (k := k) xs = e then f xs else 0) := by
    exact
      (Finset.sum_comm (s := stateFinset k n) (t := trajFinset k n)
        (f := fun e xs => if stateOfTraj (k := k) xs = e then f xs else 0))
  have hcollapse :
      ∀ xs : Traj k n,
        (∑ e ∈ stateFinset k n, (if stateOfTraj (k := k) xs = e then f xs else 0)) = f xs := by
    intro xs
    have hmem : stateOfTraj (k := k) xs ∈ stateFinset k n :=
      stateOfTraj_mem_stateFinset (k := k) xs
    simp [eq_comm, hmem]
  calc
    (∑ e ∈ stateFinset k n, wμ (k := k) μ n e)
        = ∑ e ∈ stateFinset k n,
            ∑ xs ∈ (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e), f xs := by
              simp [wμ, f]
    _ = ∑ e ∈ stateFinset k n,
            ∑ xs ∈ trajFinset k n, (if stateOfTraj (k := k) xs = e then f xs else 0) := by
                refine Finset.sum_congr rfl ?_
                intro e he
                simp [hfilter e]
      _ = ∑ xs ∈ trajFinset k n,
              ∑ e ∈ stateFinset k n, (if stateOfTraj (k := k) xs = e then f xs else 0) := by
                simp [hswap]
    _ = ∑ xs ∈ trajFinset k n, f xs := by
            refine Finset.sum_congr rfl ?_
            intro xs hxs
            simp [hcollapse xs]
    _ = ∑ xs : Traj k n, f xs := by
          simp [trajFinset]
    _ = ∑ xs : Traj k n, μ (trajToList (k := k) xs) := by
          rfl

theorem sum_wμ_eq_one' (μ : PrefixMeasure (Fin k)) (n : ℕ) :
    (∑ e ∈ stateFinset k n, wμ (k := k) μ n e) = 1 := by
  classical
  have hregroup := sum_wμ_eq_one (k := k) (μ := μ) n
  -- The RHS is exactly the normalization statement already proved for `prefixPMF`.
  have hsum : (∑ xs : Traj k n, μ (trajToList (k := k) xs)) = 1 := by
    have htsum : (∑' xs : Traj k n, μ (trajToList (k := k) xs)) = 1 := by
      simpa [FiniteAlphabet.prefixPMF, trajToList] using
        (PMF.tsum_coe (FiniteAlphabet.prefixPMF μ (n + 1)))
    simpa [tsum_fintype] using htsum
  simp [hregroup, hsum]

-- Same statement with the `E_n` alias.
theorem sum_wμ_eq_one_E (μ : PrefixMeasure (Fin k)) (n : ℕ) :
    (∑ e ∈ E_n k n, wμ (k := k) μ n e) = 1 := by
  simpa [E_n] using (sum_wμ_eq_one' (k := k) (μ := μ) n)


end MarkovDeFinettiHard

end Mettapedia.Logic
