import Mettapedia.Logic.MarkovDeFinettiHardExcursions
import Mettapedia.Logic.MarkovDeFinettiEvidenceBasis
import Mettapedia.Logic.MarkovDeFinettiHardApprox
import Mettapedia.Logic.MarkovDeFinettiHardWithoutReplacement
import Mettapedia.Logic.MarkovDeFinettiHardWithoutReplacementModel

/-!
# Markov de Finetti (Hard Direction) — Excursion model

This file defines an explicit excursion decomposition of a finite trajectory.
It is a purely combinatorial object (no measure theory).

The main purpose is to provide a concrete “sampling without replacement”
model for prefixes: a trajectory yields a list of excursions between returns to
the start state; uniform sampling over trajectories induces a uniform sampling
over ordered excursion lists (subject to the global transition‑count constraint).

The exact probabilistic bounds are proven downstream.
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical BigOperators List

namespace MarkovDeFinettiHardExcursionModel

open Mettapedia.Logic.MarkovDeFinettiHardExcursions
open Mettapedia.Logic.MarkovDeFinettiHard
open Mettapedia.Logic.MarkovDeFinettiHardWithoutReplacement
open Mettapedia.Logic.MarkovDeFinettiHardWithoutReplacementModel

variable {k : ℕ}

/-! ## Excursion types -/

abbrev ExcursionType (k : ℕ) := List (Fin k)

abbrev ExcursionList (k : ℕ) := List (ExcursionType k)

/-! ## Excursion sampling probabilities -/

def excursionMultiset (elist : ExcursionList k) : Multiset (ExcursionType k) :=
  Multiset.ofList elist

def empiricalExcursionProb (elist : ExcursionList k) : ExcursionType k → ℝ :=
  fun a =>
    probWeight ((excursionMultiset (k := k) elist).count a)
      (excursionMultiset (k := k) elist).card

def excursionWithoutReplacementProb (elist pref : ExcursionList k) : ℝ :=
  worProb (excursionMultiset (k := k) elist) pref

def excursionWithReplacementProb (elist pref : ExcursionList k) : ℝ :=
  wrProb (excursionMultiset (k := k) elist) pref

/-! ## Segments between return positions -/

/-- A trajectory segment between two indices (inclusive), defined using `min/max`
so it is total without order assumptions. -/
def trajSegment {n : ℕ} (xs : Traj k n) (i j : Fin (n + 1)) : List (Fin k) :=
  let lo := Nat.min i.1 j.1
  let hi := Nat.max i.1 j.1
  (trajToList (k := k) xs).drop lo |>.take (hi - lo + 1)

/-! ## Excursion list -/

/-- Excursions extracted from consecutive return positions. -/
def excursionsOfTraj {n : ℕ} (xs : Traj k n) : List (List (Fin k)) :=
  (excursionPairs (k := k) xs).map (fun p => trajSegment (k := k) xs p.1 p.2)

def excursionListOfTraj {n : ℕ} (xs : Traj k n) : ExcursionList k :=
  excursionsOfTraj (k := k) xs

@[simp] lemma length_excursionsOfTraj {n : ℕ} (xs : Traj k n) :
    (excursionsOfTraj (k := k) xs).length = numExcursions (k := k) xs := by
  classical
  simp [excursionsOfTraj, length_excursionPairs]

/-! ## Uniform‑fiber probability as “without replacement” -/

lemma prefixCoeff_eq_uniformFiber
    {n N : ℕ} (h : n ≤ N) (e : MarkovState k) (eN : MarkovState k)
    (heN : eN ∈ stateFinset k N) :
    prefixCoeff (k := k) h e eN =
      ∑ xs ∈ prefixFiber (k := k) h e eN,
        (uniformFiberPMF (k := k) N eN heN) xs := by
  -- Reuse the already proven identity in `MarkovDeFinettiHardApprox`.
  simpa using
    (prefixCoeff_eq_uniformFiberPMF (k := k) (h := h) (e := e) (eN := eN) heN)

/-! ## Excursion prefix events (without‑replacement model) -/

def excursionsTake (m : ℕ) (elist : ExcursionList k) : ExcursionList k :=
  elist.take m

def excursionPrefixFiber {N : ℕ} (m : ℕ)
    (elist : ExcursionList k) (eN : MarkovState k) : Finset (Traj k N) :=
  (fiber k N eN).filter (fun xs => excursionsTake (k := k) m (excursionListOfTraj (k := k) xs) = elist)

def excursionPrefixCoeff {N : ℕ} (m : ℕ)
    (elist : ExcursionList k) (eN : MarkovState k) : ENNReal :=
  ((excursionPrefixFiber (k := k) (N := N) m elist eN).card : ENNReal) /
    ((fiber k N eN).card : ENNReal)

lemma excursionPrefixCoeff_eq_card_ratio {N : ℕ} (m : ℕ)
    (elist : ExcursionList k) (eN : MarkovState k) :
    excursionPrefixCoeff (k := k) (N := N) m elist eN =
      ((excursionPrefixFiber (k := k) (N := N) m elist eN).card : ENNReal) /
        ((fiber k N eN).card : ENNReal) := by
  rfl

lemma excursionPrefixCoeff_eq_uniformFiber
    {N : ℕ} (m : ℕ) (elist : ExcursionList k) (eN : MarkovState k)
    (heN : eN ∈ stateFinset k N) :
    excursionPrefixCoeff (k := k) (N := N) m elist eN =
      ∑ xs ∈ excursionPrefixFiber (k := k) (N := N) m elist eN,
        (uniformFiberPMF (k := k) N eN heN) xs := by
  classical
  -- use uniform fiber PMF definition
  have hsum :
      ∑ xs ∈ excursionPrefixFiber (k := k) (N := N) m elist eN,
        (uniformFiberPMF (k := k) N eN heN) xs =
          ((excursionPrefixFiber (k := k) (N := N) m elist eN).card : ENNReal) /
            ((fiber k N eN).card : ENNReal) := by
    classical
    -- uniform fiber PMF is constant on the fiber
    have hconst :
        ∀ xs ∈ excursionPrefixFiber (k := k) (N := N) m elist eN,
          (uniformFiberPMF (k := k) N eN heN) xs =
            ((fiber k N eN).card : ENNReal)⁻¹ := by
      intro xs hxs
      have hxsf : xs ∈ fiber k N eN := by
        exact (Finset.mem_filter.1 hxs).1
      simp [uniformFiberPMF, PMF.ofFinset_apply, hxsf]
    -- sum of constant weight
    calc
      ∑ xs ∈ excursionPrefixFiber (k := k) (N := N) m elist eN,
        (uniformFiberPMF (k := k) N eN heN) xs
          = ∑ xs ∈ excursionPrefixFiber (k := k) (N := N) m elist eN,
              ((fiber k N eN).card : ENNReal)⁻¹ := by
                refine Finset.sum_congr rfl ?_
                intro xs hx
                exact hconst xs hx
      _ = ((excursionPrefixFiber (k := k) (N := N) m elist eN).card : ENNReal) *
            ((fiber k N eN).card : ENNReal)⁻¹ := by
              simp
      _ = ((excursionPrefixFiber (k := k) (N := N) m elist eN).card : ENNReal) /
            ((fiber k N eN).card : ENNReal) := by
              simp [div_eq_mul_inv]
  simp [excursionPrefixCoeff, hsum]

/-! ## Product bounds for excursion probabilities -/

def excursionsProb (p : ExcursionType k → ℝ) (elist : ExcursionList k) : ℝ :=
  (elist.map p).prod

lemma excursionsProb_eq_wrProb (elist pref : ExcursionList k) :
    excursionsProb (empiricalExcursionProb (k := k) elist) pref =
      excursionWithReplacementProb (k := k) elist pref := by
  rfl

lemma abs_excursionsProb_diff_le_length_mul_eps
    (elist : ExcursionList k) (p q : ExcursionType k → ℝ) (ε : ℝ)
    (hbound : ∀ a ∈ elist, |p a - q a| ≤ ε)
    (h : ∀ a ∈ elist, 0 ≤ p a ∧ p a ≤ 1 ∧ 0 ≤ q a ∧ q a ≤ 1) :
    |excursionsProb (k := k) p elist - excursionsProb (k := k) q elist| ≤
      (elist.length : ℝ) * ε := by
  simpa [excursionsProb] using
      (MarkovDeFinettiHardWithoutReplacement.abs_prod_diff_le_length_mul_eps
      (xs := elist) (p := p) (q := q) (ε := ε) hbound h)

lemma abs_excursion_wor_wr_le_length_mul_eps
    (elist pref : ExcursionList k) (ε : ℝ)
    (hbound :
      ∀ p ∈ stepPairs (excursionMultiset (k := k) elist)
            (excursionMultiset (k := k) elist) pref,
        |p.1 - p.2| ≤ ε) :
    |excursionWithoutReplacementProb (k := k) elist pref -
      excursionWithReplacementProb (k := k) elist pref| ≤
      (pref.length : ℝ) * ε := by
  have hrange :
      ∀ p ∈ stepPairs (excursionMultiset (k := k) elist)
            (excursionMultiset (k := k) elist) pref,
        0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 := by
    simpa using
      (stepPairs_range
        (ms0 := excursionMultiset (k := k) elist)
        (ms := excursionMultiset (k := k) elist) (xs := pref))
  simpa [excursionWithoutReplacementProb, excursionWithReplacementProb]
    using
      (abs_worProb_sub_wrProb_le_length_mul_eps
        (ms0 := excursionMultiset (k := k) elist)
        (ms := excursionMultiset (k := k) elist)
        (xs := pref) (ε := ε) hbound hrange)

/-! ## Submultiset for `take` and the generic O(1/R) bound -/

lemma ofList_take_le_ofList (elist : ExcursionList k) (m : ℕ) :
    (Multiset.ofList (elist.take m)) ≤ (Multiset.ofList elist) := by
  classical
  -- `take` is a sublist, hence subperm, hence count‑bounded.
  have hsubperm : List.Subperm (elist.take m) elist :=
    (List.take_sublist m elist).subperm
  have hcount :
      ∀ a,
        @List.count (ExcursionType k) instBEqOfDecidableEq a (elist.take m) ≤
          @List.count (ExcursionType k) instBEqOfDecidableEq a elist := by
    intro a
    have hsubperm' : elist.take m <+~ elist := by
      simpa using hsubperm
    exact (List.subperm_iff_count).1 hsubperm' a
  -- convert to multisets
  refine (Multiset.le_iff_count).2 ?_
  intro a
  simpa [Multiset.coe_count] using hcount a

lemma abs_excursion_wor_wr_le_take
    (elist : ExcursionList k) (m : ℕ)
    (hmlen : m ≤ elist.length)
    (hR : 2 * m ≤ (excursionMultiset (k := k) elist).card) :
    |excursionWithoutReplacementProb (k := k) elist (elist.take m) -
      excursionWithReplacementProb (k := k) elist (elist.take m)| ≤
      (4 * (m : ℝ) * (m : ℝ)) / ((excursionMultiset (k := k) elist).card : ℝ) := by
  classical
  -- bound each step pair by ε = 4 m / R
  let R : ℕ := (excursionMultiset (k := k) elist).card
  have hsub : (Multiset.ofList (elist.take m)) ≤ excursionMultiset (k := k) elist := by
    simpa [excursionMultiset] using (ofList_take_le_ofList (k := k) elist m)
  have hlen_nat : (elist.take m).length = m := by
    -- length of `take` is `min`, and `m ≤ length`
    simp [List.length_take, Nat.min_eq_left hmlen]
  have hR' : 2 * (elist.take m).length ≤ (excursionMultiset (k := k) elist).card := by
    simpa [hlen_nat] using hR
  have hbound :
      ∀ p ∈ stepPairs (excursionMultiset (k := k) elist)
            (excursionMultiset (k := k) elist) (elist.take m),
        |p.1 - p.2| ≤ (4 * (m : ℝ)) / (R : ℝ) := by
    -- use the generic submultiset bound from the without‑replacement model
    simpa [R, hlen_nat] using
      (stepPairs_bound_of_submultiset
        (ms0 := excursionMultiset (k := k) elist)
        (xs := elist.take m) (hsub := hsub) (hR := hR'))
  have hlen : ((elist.take m).length : ℝ) = (m : ℝ) := by
    exact_mod_cast hlen_nat
  -- apply the product bound
  have h := abs_excursion_wor_wr_le_length_mul_eps
    (k := k) (elist := elist) (pref := elist.take m)
    (ε := (4 * (m : ℝ)) / (R : ℝ)) hbound
  -- rewrite the RHS
  have hRpos : 0 ≤ (R : ℝ) := by exact_mod_cast (Nat.zero_le R)
  have hmul :
      (elist.take m).length * ((4 * (m : ℝ)) / (R : ℝ)) =
        (4 * (m : ℝ) * (m : ℝ)) / (R : ℝ) := by
    -- convert length to `m`
    calc
      (elist.take m).length * ((4 * (m : ℝ)) / (R : ℝ))
          = (m : ℝ) * ((4 * (m : ℝ)) / (R : ℝ)) := by
            -- rewrite via `hlen`
            simpa using
              congrArg (fun t : ℝ => t * ((4 * (m : ℝ)) / (R : ℝ))) hlen
      _ = (4 * (m : ℝ) * (m : ℝ)) / (R : ℝ) := by
            ring
  -- finish
  have hmul2 :
      (m : ℝ) * ((4 * (m : ℝ)) / (R : ℝ)) =
        (4 * (m : ℝ) * (m : ℝ)) / (R : ℝ) := by
    ring
  have hmin :
      min (m : ℝ) (elist.length : ℝ) = (m : ℝ) := by
    apply min_eq_left
    exact_mod_cast hmlen
  simpa [hmin, hmul2] using h

end MarkovDeFinettiHardExcursionModel

end Mettapedia.Logic
