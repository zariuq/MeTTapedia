import Mathlib.Data.List.OfFn
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mettapedia.Logic.MarkovDeFinettiHardBase
import Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge

/-!
# Markov de Finetti — Evidence Basis (Finite Counting Substrate)

This file ports the finite evidence/state layer needed by the Euler-trail counting route.
It provides:

- finite trajectories `Traj k n`
- evidence states `MarkovState k = (start, counts, last)`
- prefix/snoc operations on trajectories and states
- finite evidence fibers `stateFinset`, `fiber`, and `prefixFiber`

These are the basic objects used by the finite conditioned-prefix counting route:
fix an evidence state, count trajectories or Euler trails inside that fiber, and
compare prefix-conditioned subevents by exact finite combinatorics.
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

private lemma evidenceOf_eq_of_stateOfTraj_eq {n : ℕ} {xs ys : Traj k n}
    (h : stateOfTraj (k := k) xs = stateOfTraj (k := k) ys) :
    MarkovExchangeability.evidenceOf (α := Fin k) (n := n) xs =
      MarkovExchangeability.evidenceOf (α := Fin k) (n := n) ys := by
  apply MarkovExchangeability.MarkovEvidence.ext
  · simpa [MarkovExchangeability.evidenceOf, stateOfTraj] using congrArg MarkovState.start h
  · funext a b
    have hcounts :
        (MarkovExchangeabilityBridge.countsOfFn (k := k) xs).counts a b =
          (MarkovExchangeabilityBridge.countsOfFn (k := k) ys).counts a b := by
      simpa [stateOfTraj] using congrArg (fun e : MarkovState k => e.counts.counts a b) h
    simpa [MarkovExchangeability.evidenceOf, MarkovExchangeabilityBridge.countsOfFn] using hcounts

/-- If `μ` is Markov-exchangeable, then `μ` is constant on each evidence fiber. -/
lemma mu_const_on_state_fiber
    (μ : PrefixMeasure (Fin k)) (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    {n : ℕ} {xs ys : Traj k n} (h : stateOfTraj (k := k) xs = stateOfTraj (k := k) ys) :
    μ (trajToList (k := k) xs) = μ (trajToList (k := k) ys) := by
  have he :
      MarkovExchangeability.evidenceOf (α := Fin k) (n := n) xs =
        MarkovExchangeability.evidenceOf (α := Fin k) (n := n) ys :=
    evidenceOf_eq_of_stateOfTraj_eq (k := k) h
  simpa [trajToList] using hμ n xs ys he

@[simp] lemma stateOfTraj_start {n : ℕ} (xs : Traj k n) :
    (stateOfTraj (k := k) xs).start = xs 0 := rfl

@[simp] lemma stateOfTraj_last {n : ℕ} (xs : Traj k n) :
    (stateOfTraj (k := k) xs).last = xs (Fin.last n) := rfl

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

@[simp] lemma trajPrefix_trajSnoc {n N : ℕ} (h : n ≤ N) (xs : Traj k N) (x : Fin k) :
    trajPrefix (k := k) (n := n) (N := N + 1) (Nat.le_trans h (Nat.le_succ N))
        (trajSnoc (k := k) xs x) =
      trajPrefix (k := k) (n := n) (N := N) h xs := by
  funext i
  dsimp [trajPrefix, trajSnoc]
  let j : Fin (N + 1) := Fin.castLE (Nat.succ_le_succ h) i
  have hj :
      Fin.castLE (Nat.succ_le_succ (Nat.le_trans h (Nat.le_succ N))) i = j.castSucc := by
    apply Fin.ext
    simp [j]
  rw [hj]
  simpa [j] using
    (Fin.snoc_castSucc (α := fun _ : Fin (N + 2) => Fin k) (p := xs) (x := x) (i := j))

/-- Evidence state of a prefix of a longer trajectory. -/
def prefixState {n N : ℕ} (h : n ≤ N) (xs : Traj k N) : MarkovState k :=
  stateOfTraj (k := k) (trajPrefix (k := k) h xs)

@[simp] lemma prefixState_self {n : ℕ} (xs : Traj k n) :
    prefixState (k := k) (n := n) (N := n) le_rfl xs = stateOfTraj (k := k) xs := by
  simp [prefixState]

@[simp] lemma prefixState_trajSnoc {n N : ℕ} (h : n ≤ N) (xs : Traj k N) (x : Fin k) :
    prefixState (k := k) (n := n) (N := N + 1) (Nat.le_trans h (Nat.le_succ N))
        (trajSnoc (k := k) xs x) =
      prefixState (k := k) (n := n) (N := N) h xs := by
  simp [prefixState, trajPrefix_trajSnoc (k := k) (h := h) (xs := xs) (x := x)]

lemma trajToList_trajSnoc {n : ℕ} (xs : Traj k n) (x : Fin k) :
    trajToList (k := k) (trajSnoc (k := k) xs x) = trajToList (k := k) xs ++ [x] := by
  unfold trajToList trajSnoc
  rw [List.ofFn_succ' (f := Fin.snoc (α := fun _ : Fin (n + 2) => Fin k) xs x)]
  simp [List.concat_eq_append]

lemma trajInit_trajSnoc {n : ℕ} (xs : Traj k n) (x : Fin k) :
    trajInit (k := k) (trajSnoc (k := k) xs x) = xs := by
  funext i
  simp [trajInit, trajSnoc]

lemma trajSnoc_trajInit {n : ℕ} (xs : Traj k (n + 1)) :
    trajSnoc (k := k) (trajInit (k := k) xs) (xs (Fin.last (n + 1))) = xs := by
  funext i
  cases i using Fin.lastCases with
  | last => simp [trajSnoc]
  | cast j => simp [trajSnoc, trajInit]

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
  have htc :
      transCount (n := n + 1) (trajSnoc (k := k) xs x) a b =
        transCount (n := n) xs a b + (if xs (Fin.last n) = a ∧ x = b then 1 else 0) := by
    simpa [trajSnoc] using
      (transCount_snoc (n := n) (xs := xs) (x := x) (a := a) (b := b))
  by_cases h : a = xs (Fin.last n) ∧ b = x
  · rcases h with ⟨ha, hb⟩
    subst ha; subst hb
    simp [MarkovExchangeabilityBridge.countsOfFn, TransCounts.bump, htc]
  · have h' : ¬(xs (Fin.last n) = a ∧ x = b) := by
      intro h'
      apply h
      exact ⟨h'.1.symm, h'.2.symm⟩
    simp [MarkovExchangeabilityBridge.countsOfFn, TransCounts.bump, htc, h, h']

lemma stateOfTraj_trajSnoc {n : ℕ} (xs : Traj k n) (x : Fin k) :
    stateOfTraj (k := k) (trajSnoc (k := k) xs x) =
      MarkovState.snoc (k := k) (stateOfTraj (k := k) xs) x := by
  classical
  refine MarkovState.ext ?_ ?_ ?_
  · simp [stateOfTraj, trajSnoc, MarkovState.snoc]
  · simpa [stateOfTraj, MarkovState.snoc] using countsOfFn_trajSnoc (k := k) (xs := xs) (x := x)
  · simp [stateOfTraj, trajSnoc, MarkovState.snoc]

lemma trajSnoc_inj {n : ℕ} (x : Fin k) :
    Function.Injective (fun xs : Traj k n => trajSnoc (k := k) xs x) := by
  intro xs ys h
  have h' : trajInit (k := k) (trajSnoc (k := k) xs x) =
      trajInit (k := k) (trajSnoc (k := k) ys x) := by
    simpa using congrArg (trajInit (k := k)) h
  simpa [trajInit_trajSnoc (k := k)] using h'

/-- Finite set of all length-`n+1` trajectories. -/
def trajFinset (k : ℕ) (n : ℕ) : Finset (Traj k n) :=
  Finset.univ

/-- Alias: finite set of words (trajectories) of length `n+1`. -/
def Words (k : ℕ) (n : ℕ) : Finset (Traj k n) :=
  trajFinset k n

/-- The finite set of evidence states realized at horizon `n`. -/
def stateFinset (k : ℕ) (n : ℕ) : Finset (MarkovState k) :=
  (trajFinset k n).image (stateOfTraj (k := k))

/-- Alias: finite evidence class set at horizon `n`. -/
def E_n (k : ℕ) (n : ℕ) : Finset (MarkovState k) :=
  stateFinset k n

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
  else ((prefixFiber (k := k) h e eN).card : ENNReal) / ((fiber k N eN).card : ENNReal)

lemma stateOfTraj_mem_stateFinset {n : ℕ} (xs : Traj k n) :
    stateOfTraj (k := k) xs ∈ stateFinset k n := by
  classical
  refine Finset.mem_image.2 ?_
  exact ⟨xs, by simp [trajFinset], rfl⟩

lemma prefixState_mem_stateFinset {n N : ℕ} (h : n ≤ N) (xs : Traj k N) :
    prefixState (k := k) (n := n) (N := N) h xs ∈ stateFinset k n := by
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
  exact Finset.card_ne_zero.2
    (fiber_nonempty_of_mem_stateFinset (k := k) (N := N) (eN := eN) heN)

/-- On any finite subset of a fixed evidence fiber, a Markov-exchangeable prefix
measure is constant, so the total mass is the cardinality times any representative
mass from that subset. -/
lemma sum_mu_eq_card_mul_of_subset_fiber
    (μ : PrefixMeasure (Fin k)) (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    {N : ℕ} {eN : MarkovState k} {A : Finset (Traj k N)} {xs0 : Traj k N}
    (hA : A ⊆ fiber k N eN) (hxs0 : xs0 ∈ A) :
    (∑ xs ∈ A, μ (trajToList (k := k) xs)) =
      (A.card : ENNReal) * μ (trajToList (k := k) xs0) := by
  classical
  have hstate0 : stateOfTraj (k := k) xs0 = eN := by
    exact (Finset.mem_filter.1 (hA hxs0)).2
  have hconst :
      ∀ xs ∈ A, μ (trajToList (k := k) xs) = μ (trajToList (k := k) xs0) := by
    intro xs hxs
    have hstate : stateOfTraj (k := k) xs = eN := by
      exact (Finset.mem_filter.1 (hA hxs)).2
    exact mu_const_on_state_fiber (k := k) (μ := μ) hμ (hstate.trans hstate0.symm)
  have hsum :
      (∑ xs ∈ A, μ (trajToList (k := k) xs)) =
        (∑ xs ∈ A, μ (trajToList (k := k) xs0)) := by
    refine Finset.sum_congr rfl ?_
    intro xs hxs
    exact hconst xs hxs
  calc
    (∑ xs ∈ A, μ (trajToList (k := k) xs))
        = (∑ xs ∈ A, μ (trajToList (k := k) xs0)) := hsum
    _ = (A.card : ENNReal) * μ (trajToList (k := k) xs0) := by
          simp [Finset.sum_const, mul_comm]

end MarkovDeFinettiHard
end Mettapedia.Logic
