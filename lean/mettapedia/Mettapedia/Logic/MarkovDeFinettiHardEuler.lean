import Mettapedia.Logic.MarkovDeFinettiEvidenceBasis
import Mathlib.Data.Fintype.BigOperators

/-!
# Markov de Finetti (Hard Direction) — Euler/Counting Preliminaries

This file sets up the basic combinatorial facts needed for the Euler‑trail
counting route (Diaconis–Freedman core).  We start with elementary identities
about transition‑count matrices:

* total transitions = sum of all transition counts;
* out‑degree / in‑degree definitions in terms of `TransCounts`.

These facts are used to normalize counting formulas later.
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical BigOperators

namespace MarkovDeFinettiHardEuler

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovExchangeability
open Mettapedia.Logic.MarkovDeFinettiHard

variable {k : ℕ}

/-! ## Degree definitions -/

def outdeg (e : MarkovState k) (a : Fin k) : ℕ :=
  e.counts.rowTotal a

def indeg (e : MarkovState k) (b : Fin k) : ℕ :=
  ∑ a : Fin k, e.counts.counts a b

@[simp] lemma outdeg_eq_rowTotal (e : MarkovState k) (a : Fin k) :
    outdeg (k := k) e a = e.counts.rowTotal a := rfl

@[simp] lemma indeg_eq_sum_col (e : MarkovState k) (b : Fin k) :
    indeg (k := k) e b = ∑ a : Fin k, e.counts.counts a b := rfl

/-! ## Total transition counts -/

lemma sum_transCount_eq
    {n : ℕ} (xs : Fin (n + 1) → Fin k) :
    ∑ a : Fin k, ∑ b : Fin k, transCount (n := n) xs a b = n := by
  classical
  let f : Fin n → Fin k × Fin k := fun i =>
    (xs (Fin.castSucc i), xs (Fin.succ i))
  -- Sum of fiber cardinalities equals the cardinality of the domain.
  have hcard :
      (Finset.univ : Finset (Fin n)).card =
        ∑ p ∈ (Finset.univ.image f),
          (Finset.univ.filter (fun i : Fin n => f i = p)).card := by
    simpa using (Finset.card_eq_sum_card_image (f := f) (s := (Finset.univ : Finset (Fin n))))
  -- Replace the sum over the image by a sum over all pairs (fiber count is zero outside the image).
  have hsum :
      ∑ p : Fin k × Fin k,
        (Finset.univ.filter (fun i : Fin n => f i = p)).card =
          ∑ p ∈ (Finset.univ.image f),
            (Finset.univ.filter (fun i : Fin n => f i = p)).card := by
    classical
    -- Use `sum_subset` with the zero‑outside‑image fact.
    have hsubset : (Finset.univ.image f) ⊆ (Finset.univ : Finset (Fin k × Fin k)) := by
      intro p hp
      exact Finset.mem_univ p
    have hzero :
        ∀ p ∈ (Finset.univ : Finset (Fin k × Fin k)), p ∉ (Finset.univ.image f) →
          (Finset.univ.filter (fun i : Fin n => f i = p)).card = 0 := by
      intro p _ hp
      have hempty :
          (Finset.univ.filter (fun i : Fin n => f i = p)) = ∅ := by
        apply (Finset.filter_eq_empty_iff).2
        intro i hi hfp
        exact hp (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hfp⟩)
      simp [hempty]
    -- `sum_subset` gives the equality in the opposite direction, so rewrite with `Finset.univ`.
    have hsum' :
        ∑ p ∈ (Finset.univ.image f),
          (Finset.univ.filter (fun i : Fin n => f i = p)).card =
          ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)),
            (Finset.univ.filter (fun i : Fin n => f i = p)).card := by
      exact Finset.sum_subset hsubset hzero
    -- Convert the RHS to the `Fintype` sum.
    simpa using hsum'.symm
  -- Now rewrite the sum of fibers as the sum of transition counts.
  have htrans :
      ∑ a : Fin k, ∑ b : Fin k, transCount (n := n) xs a b =
        ∑ p : Fin k × Fin k,
          (Finset.univ.filter (fun i : Fin n => f i = p)).card := by
    classical
    -- Rewrite as a sum over the product type, then unfold `transCount`.
    have hsumprod :
        (∑ a : Fin k, ∑ b : Fin k, transCount (n := n) xs a b) =
          ∑ p : Fin k × Fin k, transCount (n := n) xs p.1 p.2 := by
      simpa using (Fintype.sum_prod_type' (f := fun a b => transCount (n := n) xs a b)).symm
    have htrans' :
        ∀ p : Fin k × Fin k,
          transCount (n := n) xs p.1 p.2 =
            (Finset.univ.filter (fun i : Fin n => f i = p)).card := by
      intro p
      -- `f i = p` is the same as the conjunction in `transCount`.
      simp [transCount, f, Prod.ext_iff]
    -- Combine.
    simpa [htrans'] using hsumprod
  -- Finish by the fiber cardinality identity.
  have hcard_univ : (Finset.univ : Finset (Fin n)).card = n := by
    simp
  calc
    ∑ a : Fin k, ∑ b : Fin k, transCount (n := n) xs a b
        = ∑ p : Fin k × Fin k,
            (Finset.univ.filter (fun i : Fin n => f i = p)).card := htrans
    _ = (Finset.univ : Finset (Fin n)).card := by
          -- use `hsum` and `hcard`
          simpa [hsum] using hcard.symm
    _ = n := hcard_univ

lemma sum_counts_stateOfTraj {n : ℕ} (xs : Traj k n) :
    ∑ a : Fin k, ∑ b : Fin k, (stateOfTraj (k := k) xs).counts.counts a b = n := by
  -- `stateOfTraj.counts` is `countsOfFn`, hence uses `transCount`.
  simpa [stateOfTraj, countsOfFn] using (sum_transCount_eq (k := k) (xs := xs))

lemma sum_counts_of_mem_stateFinset {N : ℕ} {eN : MarkovState k}
    (heN : eN ∈ stateFinset k N) :
    ∑ a : Fin k, ∑ b : Fin k, eN.counts.counts a b = N := by
  classical
  rcases Finset.mem_image.1 heN with ⟨xs, hxs, rfl⟩
  simpa [stateOfTraj] using (sum_counts_stateOfTraj (k := k) (xs := xs))

lemma sum_outdeg_of_mem_stateFinset {N : ℕ} {eN : MarkovState k}
    (heN : eN ∈ stateFinset k N) :
    ∑ a : Fin k, outdeg (k := k) eN a = N := by
  -- Sum of row totals is the total number of transitions.
  have hsum : ∑ a : Fin k, outdeg (k := k) eN a =
      ∑ a : Fin k, ∑ b : Fin k, eN.counts.counts a b := by
    simp [outdeg, TransCounts.rowTotal]
  simpa [hsum] using (sum_counts_of_mem_stateFinset (k := k) (N := N) (eN := eN) heN)

lemma sum_indeg_of_mem_stateFinset {N : ℕ} {eN : MarkovState k}
    (heN : eN ∈ stateFinset k N) :
    ∑ b : Fin k, indeg (k := k) eN b = N := by
  -- Sum of column totals is also the total number of transitions.
  have hsum1 :
      ∑ b : Fin k, indeg (k := k) eN b =
        ∑ b : Fin k, ∑ a : Fin k, eN.counts.counts a b := by
    simp [indeg]
  have hsum2 :
      ∑ b : Fin k, ∑ a : Fin k, eN.counts.counts a b =
        ∑ a : Fin k, ∑ b : Fin k, eN.counts.counts a b := by
    -- Reorder the double sum via a product‑type sum.
    classical
    have hprodA :
        ∑ a : Fin k, ∑ b : Fin k, eN.counts.counts a b =
          ∑ p : Fin k × Fin k, eN.counts.counts p.1 p.2 := by
      simpa using
        (Fintype.sum_prod_type' (f := fun a b => eN.counts.counts a b)).symm
    have hprodB :
        ∑ b : Fin k, ∑ a : Fin k, eN.counts.counts a b =
          ∑ p : Fin k × Fin k, eN.counts.counts p.2 p.1 := by
      simpa using
        (Fintype.sum_prod_type' (f := fun b a => eN.counts.counts a b)).symm
    have hswap :
        ∑ p : Fin k × Fin k, eN.counts.counts p.2 p.1 =
          ∑ p : Fin k × Fin k, eN.counts.counts p.1 p.2 := by
      refine (Fintype.sum_equiv (Equiv.prodComm (Fin k) (Fin k))
        (fun p => eN.counts.counts p.2 p.1)
        (fun p => eN.counts.counts p.1 p.2) ?_)
      intro p
      rfl
    -- Both sides equal the product sum, so they are equal.
    exact hprodB.trans (hswap.trans hprodA.symm)
  simpa [hsum1, hsum2] using (sum_counts_of_mem_stateFinset (k := k) (N := N) (eN := eN) heN)

/-! ## Flow balance for a single trajectory -/

lemma card_positions_eq_prev_plus_last {n : ℕ} (xs : Traj k n) (a : Fin k) :
    (Finset.univ.filter (fun i : Fin (n + 1) => xs i = a)).card =
      (Finset.univ.filter (fun i : Fin n => xs (Fin.castSucc i) = a)).card +
        (if xs (Fin.last n) = a then 1 else 0) := by
  classical
  set S := (Finset.univ.filter (fun i : Fin (n + 1) => xs i = a)) with hS
  set S1 := (Finset.univ.image Fin.castSucc).filter (fun i : Fin (n + 1) => xs i = a) with hS1
  have hcast :
      S1.card = (Finset.univ.filter (fun i : Fin n => xs (Fin.castSucc i) = a)).card := by
    -- Rewrite `S1` as an image of a filtered set, then use injectivity.
    have hS1' :
        S1 =
          (Finset.univ.filter (fun i : Fin n => xs (Fin.castSucc i) = a)).image
            Fin.castSucc := by
      simpa [hS1] using
        (Finset.filter_image (s := Finset.univ)
          (f := Fin.castSucc) (p := fun i : Fin (n + 1) => xs i = a))
    have hcard' :
        ((Finset.univ.filter (fun i : Fin n => xs (Fin.castSucc i) = a)).image
            Fin.castSucc).card =
          (Finset.univ.filter (fun i : Fin n => xs (Fin.castSucc i) = a)).card := by
      refine Finset.card_image_iff.2 ?_
      intro i hi j hj h
      exact Fin.castSucc_inj.mp h
    simpa [hS1'] using hcard'
  by_cases hlast : xs (Fin.last n) = a
  · -- last satisfies predicate
    have hS_union : S = S1 ∪ {Fin.last n} := by
      ext i
      constructor
      · intro hi
        have hcases := Fin.eq_castSucc_or_eq_last (n := n) i
        cases hcases with
        | inl h =>
            refine Finset.mem_union.2 (Or.inl ?_)
            have : (i ∈ Finset.univ.image Fin.castSucc) := by
              rcases h with ⟨j, rfl⟩
              exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩
            exact Finset.mem_filter.2 ⟨this, by simpa using (Finset.mem_filter.1 hi).2⟩
        | inr h =>
            refine Finset.mem_union.2 (Or.inr ?_)
            simp [h]
      · intro hi
        rcases Finset.mem_union.1 hi with hi | hi
        · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hi).2⟩
        · have : i = Fin.last n := by simpa using hi
          subst this
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hlast⟩
    have hdisj : Disjoint S1 ({Fin.last n} : Finset (Fin (n + 1))) := by
      refine Finset.disjoint_left.2 ?_
      intro i hi1 hi2
      rcases Finset.mem_image.1 (Finset.mem_filter.1 hi1).1 with ⟨j, _hj, rfl⟩
      rcases Finset.mem_singleton.1 hi2 with hlast'
      exact (Fin.castSucc_ne_last j) hlast'
    have hcard : S.card = S1.card + 1 := by
      have hcard' := Finset.card_union_of_disjoint (s := S1) (t := {Fin.last n}) hdisj
      simpa [hS_union, hlast] using hcard'
    calc
      (Finset.univ.filter (fun i : Fin (n + 1) => xs i = a)).card = S.card := by simp [hS]
      _ = S1.card + 1 := hcard
      _ = (Finset.univ.filter (fun i : Fin n => xs (Fin.castSucc i) = a)).card + 1 := by
            simp [hcast]
      _ = (Finset.univ.filter (fun i : Fin n => xs (Fin.castSucc i) = a)).card +
            (if xs (Fin.last n) = a then 1 else 0) := by
            simp [hlast]
  · -- last does not satisfy predicate
    have hS_eq : S = S1 := by
      ext i
      constructor
      · intro hi
        have hcases := Fin.eq_castSucc_or_eq_last (n := n) i
        cases hcases with
        | inl h =>
            have : (i ∈ Finset.univ.image Fin.castSucc) := by
              rcases h with ⟨j, rfl⟩
              exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩
            exact Finset.mem_filter.2 ⟨this, by simpa using (Finset.mem_filter.1 hi).2⟩
        | inr h =>
            exfalso
            have hi' := (Finset.mem_filter.1 hi).2
            have : xs (Fin.last n) = a := by
              simpa [h] using hi'
            exact hlast this
      · intro hi
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hi).2⟩
    have hcard : S.card = S1.card := by simp [hS_eq]
    calc
      (Finset.univ.filter (fun i : Fin (n + 1) => xs i = a)).card = S.card := by simp [hS]
      _ = S1.card := hcard
      _ = (Finset.univ.filter (fun i : Fin n => xs (Fin.castSucc i) = a)).card := by
            simp [hcast]
      _ = (Finset.univ.filter (fun i : Fin n => xs (Fin.castSucc i) = a)).card +
            (if xs (Fin.last n) = a then 1 else 0) := by
            simp [hlast]

lemma card_positions_eq_succ_plus_head {n : ℕ} (xs : Traj k n) (a : Fin k) :
    (Finset.univ.filter (fun i : Fin (n + 1) => xs i = a)).card =
      (Finset.univ.filter (fun i : Fin n => xs (Fin.succ i) = a)).card +
        (if xs 0 = a then 1 else 0) := by
  classical
  set S := (Finset.univ.filter (fun i : Fin (n + 1) => xs i = a)) with hS
  set S1 := (Finset.univ.image Fin.succ).filter (fun i : Fin (n + 1) => xs i = a) with hS1
  have hcast :
      S1.card = (Finset.univ.filter (fun i : Fin n => xs (Fin.succ i) = a)).card := by
    -- Rewrite `S1` as an image of a filtered set, then use injectivity.
    have hS1' :
        S1 =
          (Finset.univ.filter (fun i : Fin n => xs (Fin.succ i) = a)).image
            Fin.succ := by
      simpa [hS1] using
        (Finset.filter_image (s := Finset.univ)
          (f := Fin.succ) (p := fun i : Fin (n + 1) => xs i = a))
    have hcard' :
        ((Finset.univ.filter (fun i : Fin n => xs (Fin.succ i) = a)).image
            Fin.succ).card =
          (Finset.univ.filter (fun i : Fin n => xs (Fin.succ i) = a)).card := by
      refine Finset.card_image_iff.2 ?_
      intro i hi j hj h
      exact Fin.succ_inj.mp h
    simpa [hS1'] using hcard'
  by_cases hhead : xs 0 = a
  · -- head satisfies predicate
    have hS_union : S = S1 ∪ {0} := by
      ext i
      constructor
      · intro hi
        have hcases : i = 0 ∨ ∃ j : Fin n, i = Fin.succ j := by
          cases i using Fin.cases with
          | zero => exact Or.inl rfl
          | succ j => exact Or.inr ⟨j, rfl⟩
        cases hcases with
        | inl h =>
            refine Finset.mem_union.2 (Or.inr ?_)
            simp [h]
        | inr h =>
            refine Finset.mem_union.2 (Or.inl ?_)
            have : (i ∈ Finset.univ.image Fin.succ) := by
              rcases h with ⟨j, rfl⟩
              exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩
            exact Finset.mem_filter.2 ⟨this, by simpa using (Finset.mem_filter.1 hi).2⟩
      · intro hi
        rcases Finset.mem_union.1 hi with hi | hi
        · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hi).2⟩
        · have : i = 0 := by simpa using hi
          subst this
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hhead⟩
    have hdisj : Disjoint S1 ({0} : Finset (Fin (n + 1))) := by
      refine Finset.disjoint_left.2 ?_
      intro i hi1 hi2
      rcases Finset.mem_image.1 (Finset.mem_filter.1 hi1).1 with ⟨j, _hj, rfl⟩
      rcases Finset.mem_singleton.1 hi2 with hzero
      exact (Fin.succ_ne_zero j) hzero
    have hcard : S.card = S1.card + 1 := by
      have hcard' := Finset.card_union_of_disjoint (s := S1) (t := {0}) hdisj
      simpa [hS_union, hhead] using hcard'
    calc
      (Finset.univ.filter (fun i : Fin (n + 1) => xs i = a)).card = S.card := by simp [hS]
      _ = S1.card + 1 := hcard
      _ = (Finset.univ.filter (fun i : Fin n => xs (Fin.succ i) = a)).card + 1 := by
            simp [hcast]
      _ = (Finset.univ.filter (fun i : Fin n => xs (Fin.succ i) = a)).card +
            (if xs 0 = a then 1 else 0) := by
            simp [hhead]
  · -- head does not satisfy predicate
    have hS_eq : S = S1 := by
      ext i
      constructor
      · intro hi
        have hcases : i = 0 ∨ ∃ j : Fin n, i = Fin.succ j := by
          cases i using Fin.cases with
          | zero => exact Or.inl rfl
          | succ j => exact Or.inr ⟨j, rfl⟩
        cases hcases with
        | inl h =>
            exfalso
            have : xs 0 = a := by simpa [h] using (Finset.mem_filter.1 hi).2
            exact hhead this
        | inr h =>
            have : (i ∈ Finset.univ.image Fin.succ) := by
              rcases h with ⟨j, rfl⟩
              exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩
            exact Finset.mem_filter.2 ⟨this, by simpa using (Finset.mem_filter.1 hi).2⟩
      · intro hi
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hi).2⟩
    have hcard : S.card = S1.card := by simp [hS_eq]
    calc
      (Finset.univ.filter (fun i : Fin (n + 1) => xs i = a)).card = S.card := by simp [hS]
      _ = S1.card := hcard
      _ = (Finset.univ.filter (fun i : Fin n => xs (Fin.succ i) = a)).card := by
            simp [hcast]
      _ = (Finset.univ.filter (fun i : Fin n => xs (Fin.succ i) = a)).card +
            (if xs 0 = a then 1 else 0) := by
            simp [hhead]

/-! ## Transition counts vs. position counts -/

lemma outdeg_eq_card_prev {n : ℕ} (xs : Traj k n) (a : Fin k) :
    outdeg (k := k) (stateOfTraj (k := k) xs) a =
      (Finset.univ.filter (fun i : Fin n => xs (Fin.castSucc i) = a)).card := by
  classical
  -- `outdeg` is the row sum of the transition counts.
  have hout :
      outdeg (k := k) (stateOfTraj (k := k) xs) a =
        ∑ b : Fin k, transCount (n := n) xs a b := by
    simp [outdeg, stateOfTraj, countsOfFn, TransCounts.rowTotal]
  -- Partition indices by the next symbol.
  let s : Finset (Fin n) := Finset.univ.filter (fun i => xs (Fin.castSucc i) = a)
  let g : Fin n → Fin k := fun i => xs (Fin.succ i)
  have hcard :
      s.card =
        ∑ b ∈ s.image g, (s.filter (fun i => g i = b)).card := by
    simpa using (Finset.card_eq_sum_card_image (f := g) (s := s))
  have hsum :
      ∑ b : Fin k, (s.filter (fun i => g i = b)).card =
        ∑ b ∈ s.image g, (s.filter (fun i => g i = b)).card := by
    -- Use `sum_subset` with the zero‑outside‑image fact.
    have hsubset : s.image g ⊆ (Finset.univ : Finset (Fin k)) := by
      intro b hb
      exact Finset.mem_univ b
    have hzero :
        ∀ b ∈ (Finset.univ : Finset (Fin k)), b ∉ s.image g →
          (s.filter (fun i => g i = b)).card = 0 := by
      intro b _ hb
      have hempty : s.filter (fun i => g i = b) = ∅ := by
        apply (Finset.filter_eq_empty_iff).2
        intro i hi hgi
        exact hb (Finset.mem_image.2 ⟨i, hi, hgi⟩)
      simp [hempty]
    have hsum' :
        ∑ b ∈ s.image g, (s.filter (fun i => g i = b)).card =
          ∑ b ∈ (Finset.univ : Finset (Fin k)), (s.filter (fun i => g i = b)).card := by
      exact Finset.sum_subset hsubset hzero
    simpa using hsum'.symm
  have htrans_point :
      ∀ b : Fin k,
        transCount (n := n) xs a b =
          (s.filter (fun i => g i = b)).card := by
    intro b
    have hfilter :
        s.filter (fun i => g i = b) =
          Finset.univ.filter (fun i : Fin n =>
            xs (Fin.castSucc i) = a ∧ xs (Fin.succ i) = b) := by
      ext i
      simp [s, g]
    simp [transCount, hfilter, s, g]
  have htrans :
      ∑ b : Fin k, transCount (n := n) xs a b =
        ∑ b : Fin k, (s.filter (fun i => g i = b)).card := by
    classical
    simp [htrans_point]
  -- Combine the identities.
  calc
    outdeg (k := k) (stateOfTraj (k := k) xs) a
        = ∑ b : Fin k, transCount (n := n) xs a b := hout
    _ = ∑ b : Fin k, (s.filter (fun i => g i = b)).card := htrans
    _ = ∑ b ∈ s.image g, (s.filter (fun i => g i = b)).card := hsum
    _ = s.card := by simp [hcard]
    _ = (Finset.univ.filter (fun i : Fin n => xs (Fin.castSucc i) = a)).card := by
          simp [s]

lemma indeg_eq_card_succ {n : ℕ} (xs : Traj k n) (a : Fin k) :
    indeg (k := k) (stateOfTraj (k := k) xs) a =
      (Finset.univ.filter (fun i : Fin n => xs (Fin.succ i) = a)).card := by
  classical
  -- `indeg` is the column sum of the transition counts.
  have hind :
      indeg (k := k) (stateOfTraj (k := k) xs) a =
        ∑ b : Fin k, transCount (n := n) xs b a := by
    simp [indeg, stateOfTraj, countsOfFn]
  -- Partition indices by the previous symbol.
  let s : Finset (Fin n) := Finset.univ.filter (fun i => xs (Fin.succ i) = a)
  let g : Fin n → Fin k := fun i => xs (Fin.castSucc i)
  have hcard :
      s.card =
        ∑ b ∈ s.image g, (s.filter (fun i => g i = b)).card := by
    simpa using (Finset.card_eq_sum_card_image (f := g) (s := s))
  have hsum :
      ∑ b : Fin k, (s.filter (fun i => g i = b)).card =
        ∑ b ∈ s.image g, (s.filter (fun i => g i = b)).card := by
    have hsubset : s.image g ⊆ (Finset.univ : Finset (Fin k)) := by
      intro b hb
      exact Finset.mem_univ b
    have hzero :
        ∀ b ∈ (Finset.univ : Finset (Fin k)), b ∉ s.image g →
          (s.filter (fun i => g i = b)).card = 0 := by
      intro b _ hb
      have hempty : s.filter (fun i => g i = b) = ∅ := by
        apply (Finset.filter_eq_empty_iff).2
        intro i hi hgi
        exact hb (Finset.mem_image.2 ⟨i, hi, hgi⟩)
      simp [hempty]
    have hsum' :
        ∑ b ∈ s.image g, (s.filter (fun i => g i = b)).card =
          ∑ b ∈ (Finset.univ : Finset (Fin k)), (s.filter (fun i => g i = b)).card := by
      exact Finset.sum_subset hsubset hzero
    simpa using hsum'.symm
  have htrans_point :
      ∀ b : Fin k,
        transCount (n := n) xs b a =
          (s.filter (fun i => g i = b)).card := by
    intro b
    have hfilter :
        s.filter (fun i => g i = b) =
          Finset.univ.filter (fun i : Fin n =>
            xs (Fin.castSucc i) = b ∧ xs (Fin.succ i) = a) := by
      ext i
      constructor
      · intro hi
        have hi' := Finset.mem_filter.1 hi
        have hsucc : xs (Fin.succ i) = a := by
          simpa using (Finset.mem_filter.1 hi'.1).2
        have hprev : xs (Fin.castSucc i) = b := by
          simpa [g] using hi'.2
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨hprev, hsucc⟩⟩
      · intro hi
        have hi' := Finset.mem_filter.1 hi
        have hprev : xs (Fin.castSucc i) = b := hi'.2.1
        have hsucc : xs (Fin.succ i) = a := hi'.2.2
        have hs : i ∈ s := by
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hsucc⟩
        exact Finset.mem_filter.2 ⟨hs, by simpa [g] using hprev⟩
    simp [transCount, hfilter, s, g]
  have htrans :
      ∑ b : Fin k, transCount (n := n) xs b a =
        ∑ b : Fin k, (s.filter (fun i => g i = b)).card := by
    classical
    simp [htrans_point]
  calc
    indeg (k := k) (stateOfTraj (k := k) xs) a
        = ∑ b : Fin k, transCount (n := n) xs b a := hind
    _ = ∑ b : Fin k, (s.filter (fun i => g i = b)).card := htrans
    _ = ∑ b ∈ s.image g, (s.filter (fun i => g i = b)).card := hsum
    _ = s.card := by simp [hcard]
    _ = (Finset.univ.filter (fun i : Fin n => xs (Fin.succ i) = a)).card := by
          simp [s]

lemma flow_balance_stateOfTraj {n : ℕ} (xs : Traj k n) (a : Fin k) :
    outdeg (k := k) (stateOfTraj (k := k) xs) a +
        (if xs (Fin.last n) = a then 1 else 0) =
      indeg (k := k) (stateOfTraj (k := k) xs) a +
        (if xs 0 = a then 1 else 0) := by
  -- Both sides equal the total number of positions of `a` in the trajectory.
  have hprev :=
    card_positions_eq_prev_plus_last (k := k) (xs := xs) (a := a)
  have hsucc :=
    card_positions_eq_succ_plus_head (k := k) (xs := xs) (a := a)
  -- Rewrite both via `outdeg` and `indeg`.
  have hout := outdeg_eq_card_prev (k := k) (xs := xs) (a := a)
  have hind := indeg_eq_card_succ (k := k) (xs := xs) (a := a)
  -- Combine.
  calc
    outdeg (k := k) (stateOfTraj (k := k) xs) a +
        (if xs (Fin.last n) = a then 1 else 0)
        = (Finset.univ.filter (fun i : Fin n => xs (Fin.castSucc i) = a)).card +
            (if xs (Fin.last n) = a then 1 else 0) := by simpa [hout]
    _ = (Finset.univ.filter (fun i : Fin (n + 1) => xs i = a)).card := by
          simpa using hprev.symm
    _ = (Finset.univ.filter (fun i : Fin n => xs (Fin.succ i) = a)).card +
            (if xs 0 = a then 1 else 0) := by
          simpa using hsucc
    _ = indeg (k := k) (stateOfTraj (k := k) xs) a +
            (if xs 0 = a then 1 else 0) := by
          rw [hind]
end MarkovDeFinettiHardEuler

end Mettapedia.Logic
