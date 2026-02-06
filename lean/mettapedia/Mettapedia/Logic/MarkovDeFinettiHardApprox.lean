import Mettapedia.Logic.MarkovDeFinettiEvidenceBasis
import Mettapedia.Logic.MarkovDeFinettiHardEmpirical
import Mettapedia.Logic.MarkovDeFinettiRecurrence
import Mettapedia.Logic.MarkovDeFinettiHardEuler
import Mettapedia.Logic.MarkovDeFinettiHardApproxBounds
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Set.Pairwise.Basic

/-!
# Markov de Finetti (Hard Direction) — Empirical Approximation Lemma

This file isolates the single remaining analytic core: the weighted approximation
lemma comparing empirical Markov parameters to prefix coefficients.
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical BigOperators

namespace MarkovDeFinettiHard

open MeasureTheory

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.FiniteAlphabet
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovDeFinettiRecurrence
open Mettapedia.Logic.EvidenceDirichlet
open Mettapedia.Logic.MarkovDeFinettiHardEuler

/-! ## Uniform distribution on evidence fibers -/

/-- Uniform PMF on the evidence fiber, for a nonempty fiber. -/
noncomputable def uniformFiberPMF
    (k : ℕ) (N : ℕ) (eN : MarkovState k)
    (heN : eN ∈ stateFinset k N) : PMF (Traj k N) :=
  by
    classical
    -- uniform weights on the fiber
    let s := fiber k N eN
    have hcard : s.card ≠ 0 := fiber_card_ne_zero_of_mem_stateFinset (k := k) (N := N) (eN := eN) heN
    let w : Traj k N → ENNReal := fun xs => if xs ∈ s then (s.card : ENNReal)⁻¹ else 0
    have hsum : ∑ xs ∈ s, w xs = 1 := by
      -- sum over the fiber: card * (1/card) = 1
      have hcard' : (s.card : ENNReal) ≠ 0 := by exact_mod_cast hcard
      have hcard_top : (s.card : ENNReal) ≠ (⊤ : ENNReal) := by simp
      calc
        ∑ xs ∈ s, w xs
            = ∑ xs ∈ s, (s.card : ENNReal)⁻¹ := by
                refine Finset.sum_congr rfl ?_
                intro xs hxs
                simp [w, hxs]
        _ = (s.card : ENNReal) * (s.card : ENNReal)⁻¹ := by
              simp [Finset.sum_const]
        _ = 1 := by
              simp [ENNReal.mul_inv_cancel hcard' hcard_top]
    refine PMF.ofFinset w s hsum ?_
    intro xs hx
    simp [w, hx]

/-- `prefixCoeff` as the probability of the prefix state under the uniform fiber PMF. -/
lemma prefixCoeff_eq_uniformFiberPMF
    (k : ℕ) {n N : ℕ} (h : n ≤ N) (e : MarkovState k) (eN : MarkovState k)
    (heN : eN ∈ stateFinset k N) :
    prefixCoeff (k := k) h e eN =
      ∑ xs ∈ prefixFiber (k := k) h e eN,
        (uniformFiberPMF (k := k) N eN heN) xs := by
  classical
  -- Expand the uniform PMF definition: constant weight over the fiber.
  have hcard : (fiber k N eN).card ≠ 0 :=
    fiber_card_ne_zero_of_mem_stateFinset (k := k) (N := N) (eN := eN) heN
  have hcard' : ((fiber k N eN).card : ENNReal) ≠ 0 := by exact_mod_cast hcard
  have hcard_top : ((fiber k N eN).card : ENNReal) ≠ (⊤ : ENNReal) := by simp
  -- compute the sum: card(prefixFiber) * (1/card(fiber))
  have hsum :
      ∑ xs ∈ prefixFiber (k := k) h e eN,
        (uniformFiberPMF (k := k) N eN heN) xs =
          ((prefixFiber (k := k) h e eN).card : ENNReal) * ((fiber k N eN).card : ENNReal)⁻¹ := by
    -- unpack `uniformFiberPMF` and sum the constant weight
    have hsubset :
        prefixFiber (k := k) h e eN ⊆ fiber k N eN :=
      prefixFiber_subset_fiber (k := k) h e eN
    have hsum' :
        ∑ xs ∈ prefixFiber (k := k) h e eN,
          (uniformFiberPMF (k := k) N eN heN) xs =
            ∑ xs ∈ prefixFiber (k := k) h e eN,
              ((fiber k N eN).card : ENNReal)⁻¹ := by
      refine Finset.sum_congr rfl ?_
      intro xs hxs
      have hx : xs ∈ fiber k N eN := hsubset hxs
      simp [uniformFiberPMF, PMF.ofFinset_apply, hx]
    calc
      ∑ xs ∈ prefixFiber (k := k) h e eN,
          (uniformFiberPMF (k := k) N eN heN) xs
          = ∑ xs ∈ prefixFiber (k := k) h e eN,
              ((fiber k N eN).card : ENNReal)⁻¹ := hsum'
      _ = ((prefixFiber (k := k) h e eN).card : ENNReal) * ((fiber k N eN).card : ENNReal)⁻¹ := by
            simp [Finset.sum_const]
  -- rewrite `prefixCoeff` and match the computed sum
  calc
    prefixCoeff (k := k) h e eN
        = ((prefixFiber (k := k) h e eN).card : ENNReal) / ((fiber k N eN).card : ENNReal) := by
            simp [prefixCoeff, hcard]
    _ = ((prefixFiber (k := k) h e eN).card : ENNReal) * ((fiber k N eN).card : ENNReal)⁻¹ := by
            simp [div_eq_mul_inv]
    _ = ∑ xs ∈ prefixFiber (k := k) h e eN,
          (uniformFiberPMF (k := k) N eN heN) xs := by
            simp [hsum]

/-! ## Basic bounds -/

lemma prefixCoeff_nonneg
    (k : ℕ) {n N : ℕ} (h : n ≤ N) (e : MarkovState k) (eN : MarkovState k) :
    0 ≤ prefixCoeff (k := k) h e eN := by
  by_cases hcard : (fiber k N eN).card = 0
  · simp [prefixCoeff, hcard]
  · simp [prefixCoeff, hcard]

lemma prefixCoeff_le_one_of_mem_stateFinset
    (k : ℕ) {n N : ℕ} (h : n ≤ N) (e : MarkovState k) (eN : MarkovState k)
    (heN : eN ∈ stateFinset k N) :
    prefixCoeff (k := k) h e eN ≤ 1 := by
  classical
  by_cases he : e ∈ stateFinset k n
  · have hsum := sum_prefixCoeff_eq_one_of_mem_stateFinset (k := k) (h := h) (eN := eN) heN
    have hle :
        prefixCoeff (k := k) h e eN ≤
          ∑ e' ∈ stateFinset k n, prefixCoeff (k := k) h e' eN := by
      refine Finset.single_le_sum (f := fun e' =>
        prefixCoeff (k := k) h e' eN) ?_ he
      intro e' he'
      exact prefixCoeff_nonneg (k := k) (h := h) (e := e') (eN := eN)
    simpa [hsum] using hle
  · have hzero :
        prefixCoeff (k := k) h e eN = 0 :=
      prefixCoeff_eq_zero_of_not_mem_stateFinset (k := k) (h := h) (e := e) (eN := eN) he
    simp [hzero]

lemma W_le_one
    (k : ℕ) (n : ℕ) (e : MarkovState k) (θ : MarkovParam k) :
    W (k := k) n e θ ≤ 1 := by
  classical
  by_cases he : e ∈ stateFinset k n
  · have hsum := sum_W_eq_one' (k := k) (n := n) (θ := θ)
    have hle :
        W (k := k) n e θ ≤
          ∑ e' ∈ stateFinset k n, W (k := k) n e' θ := by
      refine Finset.single_le_sum (f := fun e' => W (k := k) n e' θ) ?_ he
      intro e' he'
      exact W_nonneg (k := k) (n := n) (e := e') (θ := θ)
    simpa [hsum] using hle
  · -- outside the state finset, `W` is zero
    have hempty :
        (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e) = ∅ := by
      classical
      ext xs
      constructor
      · intro hxs
        -- this would witness `e ∈ stateFinset`
        have he' : e ∈ stateFinset k n := by
          refine Finset.mem_image.2 ?_
          refine ⟨xs, ?_, ?_⟩
          · exact (Finset.mem_filter.1 hxs).1
          · exact (Finset.mem_filter.1 hxs).2
        exact (he he').elim
      · intro hxs
        exact (Finset.notMem_empty xs hxs).elim
    have hzero : W (k := k) n e θ = 0 := by
      simp [W, hempty]
    simp [hzero]

variable {k : ℕ}

/-! ## Basic real bounds for toReal -/

lemma W_toReal_le_one
    (k : ℕ) (n : ℕ) (e : MarkovState k) (θ : MarkovParam k) :
    (W (k := k) n e θ).toReal ≤ 1 := by
  have hle := W_le_one (k := k) (n := n) (e := e) (θ := θ)
  -- `1` is `ENNReal.ofReal 1`.
  exact ENNReal.toReal_le_of_le_ofReal (by exact zero_le_one) (by simpa using hle)

lemma prefixCoeff_toReal_le_one
    (k : ℕ) {n N : ℕ} (h : n ≤ N) (e : MarkovState k) (eN : MarkovState k)
    (heN : eN ∈ stateFinset k N) :
    (prefixCoeff (k := k) (h := h) e eN).toReal ≤ 1 := by
  have hle :
      prefixCoeff (k := k) (h := h) e eN ≤ 1 :=
    prefixCoeff_le_one_of_mem_stateFinset (k := k) (h := h) (e := e) (eN := eN) heN
  exact ENNReal.toReal_le_of_le_ofReal (by exact zero_le_one) (by simpa using hle)

lemma prefixCoeff_toReal_nonneg
    (k : ℕ) {n N : ℕ} (h : n ≤ N) (e : MarkovState k) (eN : MarkovState k) :
    0 ≤ (prefixCoeff (k := k) (h := h) e eN).toReal := by
  exact ENNReal.toReal_nonneg

lemma W_toReal_nonneg
    (k : ℕ) (n : ℕ) (e : MarkovState k) (θ : MarkovParam k) :
    0 ≤ (W (k := k) n e θ).toReal := by
  exact ENNReal.toReal_nonneg

lemma abs_sub_le_one_of_unit_interval {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |x - y| ≤ 1 := by
  -- Use the symmetric form `x - y ≤ 1` and `y - x ≤ 1`.
  have h1 : x - y ≤ 1 := by linarith
  have h2 : y - x ≤ 1 := by linarith
  exact (abs_sub_le_iff.2 ⟨h1, h2⟩)

lemma abs_diffTerm_le_one
    (hk : 0 < k)
    {n N : ℕ} (hN : Nat.succ n ≤ N)
    (e : MarkovState k) (s : MarkovState k)
    (hs : s ∈ stateFinset k N) :
    |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
        - (prefixCoeff (k := k) (h := hN) e s).toReal| ≤ 1 := by
  have hx0 : 0 ≤ (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal :=
    W_toReal_nonneg (k := k) (n := Nat.succ n) (e := e)
      (θ := empiricalParam (k := k) hk s)
  have hx1 : (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal ≤ 1 :=
    W_toReal_le_one (k := k) (n := Nat.succ n) (e := e)
      (θ := empiricalParam (k := k) hk s)
  have hy0 : 0 ≤ (prefixCoeff (k := k) (h := hN) e s).toReal :=
    prefixCoeff_toReal_nonneg (k := k) (h := hN) (e := e) (eN := s)
  have hy1 : (prefixCoeff (k := k) (h := hN) e s).toReal ≤ 1 :=
    prefixCoeff_toReal_le_one (k := k) (h := hN) (e := e) (eN := s) hs
  exact abs_sub_le_one_of_unit_interval hx0 hx1 hy0 hy1

/-! ## Recurrence counter (returns to start) -/

/-- Number of returns to the start state, encoded via indegree at `start`. -/
def returnsToStart (s : MarkovState k) : ℕ :=
  indeg (k := k) s s.start

lemma returnsToStart_stateOfTraj {n : ℕ} (xs : Traj k n) :
    returnsToStart (k := k) (stateOfTraj (k := k) xs) =
      (Finset.univ.filter (fun i : Fin n => xs i.succ = xs 0)).card := by
  classical
  -- `indeg` counts transitions into the start symbol.
  have hind := indeg_eq_card_succ (k := k) (xs := xs) (a := xs 0)
  simpa [returnsToStart, stateOfTraj] using hind

/-! ## Prefix trajectories and return counts on streams -/

/-- The length-`N+1` trajectory obtained by restricting a stream to its first `N+1` entries. -/
def prefixTraj (ω : ℕ → Fin k) (N : ℕ) : Traj k N :=
  fun i => ω i.1

/-- Number of returns to the initial state within the first `N+1` entries of a stream. -/
def returnsCount (ω : ℕ → Fin k) (N : ℕ) : ℕ :=
  returnsToStart (k := k) (stateOfTraj (k := k) (prefixTraj (k := k) ω N))

lemma returnsCount_eq_card (ω : ℕ → Fin k) (N : ℕ) :
    returnsCount (k := k) ω N =
      (Finset.univ.filter (fun i : Fin N => ω i.succ = ω 0)).card := by
  -- unfold via the trajectory counting formula
  simpa [returnsCount, prefixTraj] using
    (returnsToStart_stateOfTraj (k := k) (xs := prefixTraj (k := k) ω N))

lemma returnsCount_le_succ (ω : ℕ → Fin k) (N : ℕ) :
    returnsCount (k := k) ω N ≤ returnsCount (k := k) ω (N + 1) := by
  classical
  -- define the return-index sets
  let sN : Finset (Fin N) :=
    Finset.univ.filter (fun i : Fin N => ω i.succ = ω 0)
  let sN1 : Finset (Fin (N + 1)) :=
    Finset.univ.filter (fun i : Fin (N + 1) => ω i.succ = ω 0)
  have hN : returnsCount (k := k) ω N = sN.card := by
    simpa [sN] using (returnsCount_eq_card (k := k) (ω := ω) (N := N))
  have hN1 : returnsCount (k := k) ω (N + 1) = sN1.card := by
    simpa [sN1] using (returnsCount_eq_card (k := k) (ω := ω) (N := N + 1))
  -- `Fin.castSucc` embeds `Fin N` into `Fin (N+1)`
  have hinj : Function.Injective (fun i : Fin N => Fin.castSucc i) := by
    intro i j h
    apply Fin.ext
    -- compare the underlying natural values
    exact by simpa using congrArg Fin.val h
  have hcard : sN.card = (sN.image (fun i : Fin N => Fin.castSucc i)).card := by
    simpa using (Finset.card_image_of_injective sN hinj).symm
  have hsubset : sN.image (fun i : Fin N => Fin.castSucc i) ⊆ sN1 := by
    intro j hj
    rcases Finset.mem_image.1 hj with ⟨i, hi, rfl⟩
    have hi' : ω i.succ = ω 0 := by
      simpa [sN] using (Finset.mem_filter.1 hi).2
    have hcast : ω (Fin.castSucc i).succ = ω i.succ := by rfl
    refine Finset.mem_filter.2 ?_
    refine ⟨by simp, ?_⟩
    -- use the preserved predicate under `castSucc`
    simpa [hcast] using hi'
  have hle' : (sN.image (fun i : Fin N => Fin.castSucc i)).card ≤ sN1.card :=
    Finset.card_le_card hsubset
  -- conclude
  have hle : sN.card ≤ sN1.card := by simpa [hcard] using hle'
  simpa [hN, hN1] using hle

lemma returnsCount_mono (ω : ℕ → Fin k) : Monotone (fun N => returnsCount (k := k) ω N) := by
  refine monotone_nat_of_le_succ ?_
  intro N
  exact returnsCount_le_succ (k := k) (ω := ω) N

lemma returnsCount_succ_ge_of_return (ω : ℕ → Fin k) (N : ℕ)
    (hret : ω (N + 1) = ω 0) :
    returnsCount (k := k) ω (N + 1) ≥ returnsCount (k := k) ω N + 1 := by
  classical
  let sN : Finset (Fin N) :=
    Finset.univ.filter (fun i : Fin N => ω i.succ = ω 0)
  let sN1 : Finset (Fin (N + 1)) :=
    Finset.univ.filter (fun i : Fin (N + 1) => ω i.succ = ω 0)
  have hN : returnsCount (k := k) ω N = sN.card := by
    simpa [sN] using (returnsCount_eq_card (k := k) (ω := ω) (N := N))
  have hN1 : returnsCount (k := k) ω (N + 1) = sN1.card := by
    simpa [sN1] using (returnsCount_eq_card (k := k) (ω := ω) (N := N + 1))
  have hinj : Function.Injective (fun i : Fin N => Fin.castSucc i) := by
    intro i j h
    apply Fin.ext
    exact by simpa using congrArg Fin.val h
  have hcard : sN.card = (sN.image (fun i : Fin N => Fin.castSucc i)).card := by
    simpa using (Finset.card_image_of_injective sN hinj).symm
  have hsubset : sN.image (fun i : Fin N => Fin.castSucc i) ⊆ sN1 := by
    intro i hi
    rcases Finset.mem_image.1 hi with ⟨j, hj, rfl⟩
    have hj' : ω j.succ = ω 0 := by
      simpa [sN] using (Finset.mem_filter.1 hj).2
    have hj'' : ω (Fin.castSucc j).succ = ω 0 := by
      simpa using hj'
    exact Finset.mem_filter.2 ⟨by simp, hj''⟩
  have hlast : Fin.last N ∈ sN1 := by
    have : ω (Fin.last N).succ = ω 0 := by
      simpa using hret
    exact Finset.mem_filter.2 ⟨by simp, this⟩
  have hnot : (Fin.last N) ∉ sN.image (fun i : Fin N => Fin.castSucc i) := by
    intro h
    rcases Finset.mem_image.1 h with ⟨j, _hj, hlast'⟩
    exact (Fin.castSucc_ne_last j) hlast'
  have hlt : (sN.image (fun i : Fin N => Fin.castSucc i)).card < sN1.card := by
    apply Finset.card_lt_card
    refine ⟨hsubset, ?_⟩
    intro hsub
    exact hnot (hsub hlast)
  have hge : (sN.image (fun i : Fin N => Fin.castSucc i)).card + 1 ≤ sN1.card :=
    Nat.succ_le_of_lt hlt
  have : returnsCount (k := k) ω N + 1 ≤ returnsCount (k := k) ω (N + 1) := by
    simpa [hN, hN1, hcard] using hge
  exact this

lemma returnsCount_ge_of_return_after (ω : ℕ → Fin k) {N n : ℕ}
    (hn : N < n) (hret : ω n = ω 0) :
    returnsCount (k := k) ω n ≥ returnsCount (k := k) ω N + 1 := by
  have hmono := returnsCount_mono (k := k) (ω := ω)
  have hle : N ≤ n - 1 := by
    exact Nat.le_pred_of_lt hn
  have hstep : returnsCount (k := k) ω (n - 1) ≥ returnsCount (k := k) ω N := hmono hle
  have hret' : ω ((n - 1) + 1) = ω 0 := by
    have hn1 : 1 ≤ n := by
      exact Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le N) hn)
    simpa [Nat.sub_add_cancel hn1] using hret
  have hsucc :
      returnsCount (k := k) ω (n - 1 + 1) ≥ returnsCount (k := k) ω (n - 1) + 1 :=
    returnsCount_succ_ge_of_return (k := k) (ω := ω) (N := n - 1) hret'
  have hstep' : returnsCount (k := k) ω (n - 1) + 1 ≥ returnsCount (k := k) ω N + 1 := by
    simpa [add_comm, add_left_comm, add_assoc] using (add_le_add_right hstep 1)
  have hsucc' : returnsCount (k := k) ω n ≥ returnsCount (k := k) ω (n - 1) + 1 := by
    simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le N) hn))] using hsucc
  exact le_trans hstep' hsucc'

lemma recurrentEvent_exists_returns_ge (ω : ℕ → Fin k)
    (hrec : ω ∈ recurrentEvent (k := k)) (M : ℕ) :
    ∃ N, returnsCount (k := k) ω N ≥ M := by
  classical
  have hrec' : ∀ N, ∃ n ≥ N, ω n = ω 0 := by
    intro N
    have hN := (Set.mem_iInter.mp hrec) N
    rcases Set.mem_iUnion.mp hN with ⟨n, hn⟩
    rcases Set.mem_iUnion.mp hn with ⟨hnN, hret⟩
    exact ⟨n, hnN, hret⟩
  induction M with
  | zero =>
      refine ⟨0, by simp⟩
  | succ M ih =>
      rcases ih with ⟨N0, hN0⟩
      rcases hrec' (N0 + 1) with ⟨n, hnN, hret⟩
      have hgt : N0 < n := by
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self N0) hnN
      refine ⟨n, ?_⟩
      have hge :=
        returnsCount_ge_of_return_after (k := k) (ω := ω) (N := N0) (n := n) hgt hret
      have hM : M + 1 ≤ returnsCount (k := k) ω N0 + 1 := by
        exact Nat.succ_le_succ hN0
      exact le_trans hM hge

@[simp] lemma trajToList_getElem {n : ℕ} (xs : Traj k n) (i : Fin (n + 1)) :
    (trajToList (k := k) xs)[i.1] = xs i := by
  have hlen : i.1 < (trajToList (k := k) xs).length := by
    simpa [length_trajToList] using i.is_lt
  have hget :
      (trajToList (k := k) xs)[i.1] =
        xs ⟨i.1, by simpa [length_trajToList] using i.is_lt⟩ := by
    simpa [trajToList] using (List.getElem_ofFn (f := xs) (i := i.1) hlen)
  have hi :
      (⟨i.1, by simpa [length_trajToList] using i.is_lt⟩ : Fin (n + 1)) = i := by
    apply Fin.ext; rfl
  simpa [hi] using hget

lemma trajToList_getElem' {n : ℕ} (xs : Traj k n) (i : ℕ)
    (hi : i < (trajToList (k := k) xs).length) :
    (trajToList (k := k) xs)[i]'hi =
      xs ⟨i, by simpa [length_trajToList] using hi⟩ := by
  simpa [trajToList] using (List.getElem_ofFn (f := xs) (i := i) hi)

lemma prefixTraj_eq_of_mem_cylinder {N : ℕ} (xs : Traj k N) (ω : ℕ → Fin k)
    (hω : ω ∈ MarkovDeFinettiRecurrence.cylinder (k := k) (trajToList (k := k) xs)) :
    prefixTraj (k := k) ω N = xs := by
  -- use the cylinder characterization on trajectories
  have hmem : ∀ i : Fin (N + 1), ω i.1 = xs i := by
    intro i
    -- eliminate casts by destructing the index
    cases' i with i_val i_lt
    -- build the matching index for the cylinder set
    have hlen : i_val < (trajToList (k := k) xs).length := by
      simpa [length_trajToList] using i_lt
    have hmem' := (Set.mem_iInter.mp hω) (⟨i_val, hlen⟩ : Fin (trajToList (k := k) xs).length)
    -- rewrite the list entry to the trajectory value
    have hlist :
        (trajToList (k := k) xs)[i_val]'hlen = xs ⟨i_val, i_lt⟩ := by
      simpa using (trajToList_getElem' (k := k) (xs := xs) (i := i_val) (hi := hlen))
    -- `i'.1` is definitional `i_val`
    have hmem'' : ω i_val = (trajToList (k := k) xs)[i_val]'hlen := by
      simpa [Fin.val_mk] using hmem'
    exact hmem''.trans hlist
  funext i
  simpa [prefixTraj] using hmem i

lemma returnsCount_eq_of_mem_cylinder {N : ℕ} (xs : Traj k N) (ω : ℕ → Fin k)
    (hω : ω ∈ MarkovDeFinettiRecurrence.cylinder (k := k) (trajToList (k := k) xs)) :
    returnsCount (k := k) ω N =
      returnsToStart (k := k) (stateOfTraj (k := k) xs) := by
  simp [returnsCount, prefixTraj_eq_of_mem_cylinder (k := k) xs ω hω]

/-- Bad event: fewer than `M` returns to the initial state by time `N`. -/
def badEvent (N M : ℕ) : Set (ℕ → Fin k) :=
  { ω | returnsCount (k := k) ω N < M }

lemma mem_cylinder_prefixTraj (ω : ℕ → Fin k) (N : ℕ) :
    ω ∈ MarkovDeFinettiRecurrence.cylinder (k := k) (trajToList (k := k) (prefixTraj (k := k) ω N)) := by
  -- by definition, the cylinder is satisfied by the prefix trajectory
  refine (Set.mem_iInter).2 ?_
  intro i
  -- `trajToList` is `List.ofFn`, so `getElem` reduces to the trajectory value.
  have hlen : i.1 < (trajToList (k := k) (prefixTraj (k := k) ω N)).length := by
    simpa [length_trajToList] using i.is_lt
  have hget :
      (trajToList (k := k) (prefixTraj (k := k) ω N))[i.1] =
        (prefixTraj (k := k) ω N)
          ⟨i.1, by simpa [length_trajToList] using i.is_lt⟩ := by
    simpa [trajToList] using
      (List.getElem_ofFn (f := prefixTraj (k := k) ω N) (i := i.1) hlen)
  -- flip the equality to match the cylinder definition
  simpa [prefixTraj] using hget.symm

lemma badEvent_eq_iUnion_cylinder (N M : ℕ) :
    badEvent (k := k) N M =
      ⋃ xs ∈ (trajFinset k N).filter
        (fun xs => returnsToStart (k := k) (stateOfTraj (k := k) xs) < M),
          MarkovDeFinettiRecurrence.cylinder (k := k) (trajToList (k := k) xs) := by
  classical
  ext ω
  constructor
  · intro hbad
    -- choose the prefix trajectory
    let xs : Traj k N := prefixTraj (k := k) ω N
    have hxmem : xs ∈ trajFinset k N := by simp [trajFinset]
    have hcount : returnsToStart (k := k) (stateOfTraj (k := k) xs) < M := by
      simpa [returnsCount, xs] using hbad
    -- show ω lies in the corresponding cylinder
    have hmem_cyl :
        ω ∈ MarkovDeFinettiRecurrence.cylinder (k := k) (trajToList (k := k) xs) := by
      -- by definition of cylinder, ω matches the prefix
      simpa [xs] using mem_cylinder_prefixTraj (k := k) ω N
    refine Set.mem_iUnion.2 ?_
    refine ⟨xs, ?_⟩
    refine Set.mem_iUnion.2 ?_
    refine ⟨?_, hmem_cyl⟩
    exact Finset.mem_filter.2 ⟨hxmem, hcount⟩
  · intro hω
    rcases Set.mem_iUnion.1 hω with ⟨xs, hω⟩
    rcases Set.mem_iUnion.1 hω with ⟨hxs, hω⟩
    have hcount : returnsToStart (k := k) (stateOfTraj (k := k) xs) < M :=
      (Finset.mem_filter.1 hxs).2
    have hcount' :
        returnsCount (k := k) ω N =
          returnsToStart (k := k) (stateOfTraj (k := k) xs) :=
      returnsCount_eq_of_mem_cylinder (k := k) xs ω hω
    exact by
      -- rewrite and apply the bound
      simpa [badEvent, hcount'] using hcount

lemma badEvent_antitone (M : ℕ) : Antitone (fun N => badEvent (k := k) N M) := by
  intro N N' hNN' ω hω
  have hmono := returnsCount_mono (k := k) (ω := ω)
  exact lt_of_le_of_lt (hmono hNN') hω

lemma measurable_cylinder (xs : List (Fin k)) :
    MeasurableSet (MarkovDeFinettiRecurrence.cylinder (k := k) xs) := by
  classical
  unfold MarkovDeFinettiRecurrence.cylinder
  refine MeasurableSet.iInter ?_
  intro i
  have hf : Measurable fun ω : ℕ → Fin k => ω i.1 := measurable_pi_apply i.1
  have hg : Measurable fun ω : ℕ → Fin k => xs[i.1] := by
    exact measurable_const
  simpa using (measurableSet_eq_fun hf hg)

lemma measurable_badEvent (N M : ℕ) : MeasurableSet (badEvent (k := k) N M) := by
  classical
  have hbad := badEvent_eq_iUnion_cylinder (k := k) (N := N) (M := M)
  -- finite union of cylinders
  refine hbad ▸
    (Finset.measurableSet_biUnion
      (s := (trajFinset k N).filter
        (fun xs => returnsToStart (k := k) (stateOfTraj (k := k) xs) < M)) ?_)
  intro xs hx
  exact measurable_cylinder (k := k) (trajToList (k := k) xs)

lemma iInter_badEvent_subset_recurrent_compl (M : ℕ) :
    (⋂ N, badEvent (k := k) N M) ⊆ (recurrentEvent (k := k))ᶜ := by
  intro ω hω hrec
  have hrec' := recurrentEvent_exists_returns_ge (k := k) (ω := ω) hrec M
  rcases hrec' with ⟨N, hN⟩
  have hN' : returnsCount (k := k) ω N < M := by
    exact (Set.mem_iInter.mp hω) N
  exact (not_lt_of_ge hN) hN'

lemma cylinder_disjoint_of_traj_ne {N : ℕ} {xs ys : Traj k N} (hxy : xs ≠ ys) :
    Disjoint
      (MarkovDeFinettiRecurrence.cylinder (k := k) (trajToList (k := k) xs))
      (MarkovDeFinettiRecurrence.cylinder (k := k) (trajToList (k := k) ys)) := by
  classical
  refine Set.disjoint_left.2 ?_
  intro ω hx hy
  have hx' := prefixTraj_eq_of_mem_cylinder (k := k) xs ω hx
  have hy' := prefixTraj_eq_of_mem_cylinder (k := k) ys ω hy
  exact hxy (hx'.symm.trans hy')

/-! ## Bad mass (low‑return evidence states) -/

/-- Total `wμ` mass of evidence states with fewer than `M` returns to start. -/
def badMass (μ : PrefixMeasure (Fin k)) (N M : ℕ) : ℝ :=
  ∑ s ∈ stateFinset k N,
    (if returnsToStart (k := k) s < M then (wμ (k := k) μ N s).toReal else 0)

lemma badMass_nonneg (μ : PrefixMeasure (Fin k)) (N M : ℕ) :
    0 ≤ badMass (k := k) μ N M := by
  classical
  unfold badMass
  have hnonneg :
      ∀ s ∈ stateFinset k N,
        0 ≤ (if returnsToStart (k := k) s < M then (wμ (k := k) μ N s).toReal else 0) := by
    intro s hs
    by_cases h : returnsToStart (k := k) s < M
    · simp [h]
    · simp [h]
  exact Finset.sum_nonneg (by
    intro s hs; exact hnonneg s hs)

lemma badMass_eq_sum_traj
    (μ : PrefixMeasure (Fin k)) (N M : ℕ) :
    badMass (k := k) μ N M =
      ∑ xs ∈ trajFinset k N,
        (if returnsToStart (k := k) (stateOfTraj (k := k) xs) < M
         then (μ (trajToList (k := k) xs)).toReal else 0) := by
  classical
  unfold badMass
  let f : Traj k N → ℝ := fun xs => (μ (trajToList (k := k) xs)).toReal
  have hwμ :
      ∀ s : MarkovState k,
        (wμ (k := k) μ N s).toReal =
          ∑ xs ∈ (trajFinset k N).filter (fun xs => stateOfTraj (k := k) xs = s), f xs := by
    intro s
    -- `wμ` is the sum of μ over the fiber; use `toReal_sum` (finite) since each term is finite.
    have hfinite :
        ∀ xs ∈ (trajFinset k N).filter (fun xs => stateOfTraj (k := k) xs = s),
          μ (trajToList (k := k) xs) ≠ (⊤ : ENNReal) := by
      intro xs hxs
      -- Prefix measures are semimeasures, hence bounded by 1.
      exact
        (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.Semimeasure.ne_top
          (μ := μ.toSemimeasure) (trajToList (k := k) xs))
    -- convert the finite ENNReal sum to a real sum
    have hsum :
        (wμ (k := k) μ N s).toReal =
          ∑ xs ∈ (trajFinset k N).filter (fun xs => stateOfTraj (k := k) xs = s),
            (μ (trajToList (k := k) xs)).toReal := by
      -- `ENNReal.toReal_sum` on the finite fiber
      simpa [wμ] using
        (ENNReal.toReal_sum
          (s := (trajFinset k N).filter (fun xs => stateOfTraj (k := k) xs = s))
          (f := fun xs => μ (trajToList (k := k) xs))
          hfinite)
    simpa [f] using hsum
  -- swap sums and collapse by `stateOfTraj`
  have hcollapse :
      ∀ xs : Traj k N,
        (∑ s ∈ stateFinset k N,
          if stateOfTraj (k := k) xs = s then
            (if returnsToStart (k := k) s < M then f xs else 0)
          else 0) =
        (if returnsToStart (k := k) (stateOfTraj (k := k) xs) < M then f xs else 0) := by
    intro xs
    have hmem : stateOfTraj (k := k) xs ∈ stateFinset k N :=
      stateOfTraj_mem_stateFinset (k := k) xs
    simp [hmem]
  calc
    ∑ s ∈ stateFinset k N,
        (if returnsToStart (k := k) s < M then (wμ (k := k) μ N s).toReal else 0)
        = ∑ s ∈ stateFinset k N,
            (if returnsToStart (k := k) s < M then
              ∑ xs ∈ (trajFinset k N).filter (fun xs => stateOfTraj (k := k) xs = s),
                f xs else 0) := by
                  refine Finset.sum_congr rfl ?_
                  intro s hs
                  simp [hwμ]
    _ = ∑ s ∈ stateFinset k N,
          ∑ xs ∈ trajFinset k N,
            if stateOfTraj (k := k) xs = s then
              (if returnsToStart (k := k) s < M then f xs else 0)
            else 0 := by
          refine Finset.sum_congr rfl ?_
          intro s hs
          have hsum_filter :
              ∑ xs ∈ (trajFinset k N).filter (fun xs => stateOfTraj (k := k) xs = s), f xs
                = ∑ xs ∈ trajFinset k N, if stateOfTraj (k := k) xs = s then f xs else 0 := by
              simp [Finset.sum_filter]
          by_cases h : returnsToStart (k := k) s < M
          · simp [h, hsum_filter]
          · simp [h]
    _ = ∑ xs ∈ trajFinset k N,
          ∑ s ∈ stateFinset k N,
            if stateOfTraj (k := k) xs = s then
              (if returnsToStart (k := k) s < M then f xs else 0)
            else 0 := by
          -- swap the two finite sums
          have hcomm :=
            (Finset.sum_comm (s := stateFinset k N) (t := trajFinset k N)
              (f := fun s xs =>
                if stateOfTraj (k := k) xs = s then
                  (if returnsToStart (k := k) s < M then f xs else 0)
                else 0))
          simpa using hcomm
    _ = ∑ xs ∈ trajFinset k N,
          (if returnsToStart (k := k) (stateOfTraj (k := k) xs) < M then f xs else 0) := by
          refine Finset.sum_congr rfl ?_
          intro xs hx
          simp [hcollapse, f]

lemma badMass_eq_measure_badEvent_of_witness
    (μ : PrefixMeasure (Fin k)) (N M : ℕ)
    (P : Measure (ℕ → Fin k)) (hP : IsProbabilityMeasure P)
    (hμP : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs)) :
    badMass (k := k) μ N M = (P (badEvent (k := k) N M)).toReal := by
  classical
  -- rewrite badMass as a sum over trajectories
  have hsum :
      badMass (k := k) μ N M =
        ∑ xs ∈ (trajFinset k N).filter
          (fun xs => returnsToStart (k := k) (stateOfTraj (k := k) xs) < M),
            (P (MarkovDeFinettiRecurrence.cylinder (k := k) (trajToList (k := k) xs))).toReal := by
    -- start from the traj-sum form
    have h1 := badMass_eq_sum_traj (k := k) (μ := μ) (N := N) (M := M)
    -- rewrite via filter and the cylinder representation
    simp [h1, hμP, Finset.sum_filter]  -- `if`-sum ↔ filter sum
  -- compute the measure of the union of cylinders
  have hpair :
      Set.PairwiseDisjoint
        (s := (↑((trajFinset k N).filter
          (fun xs => returnsToStart (k := k) (stateOfTraj (k := k) xs) < M)) : Set (Traj k N)))
        (fun xs => MarkovDeFinettiRecurrence.cylinder (k := k) (trajToList (k := k) xs)) := by
    intro xs hx ys hy hxy
    exact cylinder_disjoint_of_traj_ne (k := k) (N := N) (hxy := hxy)
  have hmeas :
      ∀ xs ∈ (trajFinset k N).filter
        (fun xs => returnsToStart (k := k) (stateOfTraj (k := k) xs) < M),
          MeasurableSet (MarkovDeFinettiRecurrence.cylinder (k := k) (trajToList (k := k) xs)) := by
    intro xs hx
    -- cylinder sets are measurable
    classical
    -- unfold `cylinder` measurability
    -- reuse the definition from `MarkovDeFinettiRecurrence`
    unfold MarkovDeFinettiRecurrence.cylinder
    refine MeasurableSet.iInter ?_
    intro i
    have hf : Measurable fun ω : ℕ → Fin k => ω i.1 := measurable_pi_apply i.1
    have hg : Measurable fun ω : ℕ → Fin k => (trajToList (k := k) xs)[i.1] := by
      exact measurable_const
    simpa using (measurableSet_eq_fun hf hg)
  have hunion :
      P (badEvent (k := k) N M) =
        ∑ xs ∈ (trajFinset k N).filter
          (fun xs => returnsToStart (k := k) (stateOfTraj (k := k) xs) < M),
            P (MarkovDeFinettiRecurrence.cylinder (k := k) (trajToList (k := k) xs)) := by
    -- use the union-of-cylinders representation
    have hbad := badEvent_eq_iUnion_cylinder (k := k) (N := N) (M := M)
    -- apply measure of finite disjoint union
    simpa [hbad] using
      (measure_biUnion_finset (μ := P) (s := (trajFinset k N).filter
        (fun xs => returnsToStart (k := k) (stateOfTraj (k := k) xs) < M))
        (f := fun xs => MarkovDeFinettiRecurrence.cylinder (k := k) (trajToList (k := k) xs))
        hpair hmeas)
  -- convert the measure equality to reals
  have hfinite :
      ∀ xs ∈ (trajFinset k N).filter
        (fun xs => returnsToStart (k := k) (stateOfTraj (k := k) xs) < M),
          P (MarkovDeFinettiRecurrence.cylinder (k := k) (trajToList (k := k) xs)) ≠ (⊤ : ENNReal) := by
    intro xs hx
    exact measure_ne_top P (MarkovDeFinettiRecurrence.cylinder (k := k) (trajToList (k := k) xs))
  have hunion_real :
      (P (badEvent (k := k) N M)).toReal =
        ∑ xs ∈ (trajFinset k N).filter
          (fun xs => returnsToStart (k := k) (stateOfTraj (k := k) xs) < M),
            (P (MarkovDeFinettiRecurrence.cylinder (k := k) (trajToList (k := k) xs))).toReal := by
    -- apply `toReal_sum` to the finite sum
    simpa [hunion] using
      (ENNReal.toReal_sum
        (s := (trajFinset k N).filter
          (fun xs => returnsToStart (k := k) (stateOfTraj (k := k) xs) < M))
        (f := fun xs => P (MarkovDeFinettiRecurrence.cylinder (k := k) (trajToList (k := k) xs)))
        hfinite)
  -- finish
  simp [hsum, hunion_real]

lemma badMass_eq_measure_badEvent
    (μ : PrefixMeasure (Fin k)) (N M : ℕ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ) :
    ∃ P : Measure (ℕ → Fin k),
      IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs)) ∧
      badMass (k := k) μ N M = (P (badEvent (k := k) N M)).toReal := by
  classical
  rcases hrec with ⟨P, hP, hμP, hrecP⟩
  refine ⟨P, hP, hμP, ?_⟩
  exact badMass_eq_measure_badEvent_of_witness (k := k) (μ := μ) (N := N) (M := M) P hP hμP

lemma badMass_tendsto_zero
    (μ : PrefixMeasure (Fin k)) (M : ℕ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ) :
    Filter.Tendsto (fun N => badMass (k := k) μ N M) Filter.atTop (nhds 0) := by
  classical
  -- obtain the recurrent witness measure
  rcases hrec with ⟨P, hP, hμP, hrecP⟩
  have hrec' : MarkovRecurrentPrefixMeasure (k := k) μ := ⟨P, hP, hμP, hrecP⟩
  -- measurability of badEvent
  have hmeas : ∀ N, NullMeasurableSet (badEvent (k := k) N M) P := by
    intro N
    exact (measurable_badEvent (k := k) (N := N) (M := M)).nullMeasurableSet
  -- decreasing sequence of events
  have hmono : Antitone (fun N => badEvent (k := k) N M) :=
    badEvent_antitone (k := k) M
  have hfin : ∃ N, P (badEvent (k := k) N M) ≠ (⊤ : ENNReal) := by
    refine ⟨0, ?_⟩
    exact measure_ne_top P (badEvent (k := k) 0 M)
  have htend :
      Filter.Tendsto (fun N => P (badEvent (k := k) N M)) Filter.atTop
        (nhds (P (⋂ N, badEvent (k := k) N M))) :=
    tendsto_measure_iInter_atTop (μ := P) hmeas hmono hfin
  -- the intersection is contained in the complement of recurrence
  have hsubset : (⋂ N, badEvent (k := k) N M) ⊆ (recurrentEvent (k := k))ᶜ :=
    iInter_badEvent_subset_recurrent_compl (k := k) M
  have hcompl : P ((recurrentEvent (k := k))ᶜ) = 0 := by
    have hmeas : MeasurableSet (recurrentEvent (k := k)) := measurable_recurrentEvent (k := k)
    have hcomp : P ((recurrentEvent (k := k))ᶜ) = 1 - P (recurrentEvent (k := k)) := by
      simpa [measure_univ] using (measure_compl (μ := P) (s := recurrentEvent (k := k)) hmeas)
    simpa [hrecP] using hcomp
  have hzero : P (⋂ N, badEvent (k := k) N M) = 0 := by
    have hle := measure_mono (μ := P) hsubset
    simpa [hcompl] using hle
  -- convert toReal and rewrite badMass
  have htend0 :
      Filter.Tendsto (fun N => (P (badEvent (k := k) N M)).toReal) Filter.atTop (nhds 0) := by
    have hne : ∀ N, P (badEvent (k := k) N M) ≠ (⊤ : ENNReal) := by
      intro N; exact measure_ne_top P (badEvent (k := k) N M)
    have htend0' :
        Filter.Tendsto (fun N => P (badEvent (k := k) N M)) Filter.atTop (nhds 0) := by
      simpa [hzero] using htend
    exact (ENNReal.tendsto_toReal_zero_iff hne).2 htend0'
  -- rewrite badMass using the cylinder representation
  have hbadN : ∀ N, badMass (k := k) μ N M = (P (badEvent (k := k) N M)).toReal := by
    intro N
    exact badMass_eq_measure_badEvent_of_witness (k := k) (μ := μ) (N := N) (M := M) P hP hμP
  simpa [hbadN] using htend0

/-! ## Weighted approximation error (definitions) -/

def weightedDiffCore
    (hk : 0 < k)
    (μ : PrefixMeasure (Fin k))
    (n : ℕ) (e : MarkovState k) (N : ℕ) (hN : Nat.succ n ≤ N) : ℝ :=
  ∑ s ∈ stateFinset k N,
    ((W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
      - (prefixCoeff (k := k) (h := hN) e s).toReal) *
      (wμ (k := k) μ N s).toReal

def weightedDiff
    (hk : 0 < k)
    (μ : PrefixMeasure (Fin k))
    (n : ℕ) (e : MarkovState k) (N : ℕ) : ℝ :=
  if hN : Nat.succ n ≤ N then
    weightedDiffCore (k := k) hk μ n e N hN
  else
    0

@[simp] lemma weightedDiff_eq_weightedDiffCore
    (hk : 0 < k) (μ : PrefixMeasure (Fin k)) (n : ℕ) (e : MarkovState k) (N : ℕ)
    (hN : Nat.succ n ≤ N) :
    weightedDiff (k := k) hk μ n e N =
      weightedDiffCore (k := k) hk μ n e N hN := by
  simp [weightedDiff, hN, weightedDiffCore]

/-! ## Good‑state bound (Diaconis–Freedman core) -/

lemma wμ_le_one (μ : PrefixMeasure (Fin k)) (N : ℕ) (s : MarkovState k) :
    wμ (k := k) μ N s ≤ 1 := by
  classical
  by_cases hs : s ∈ stateFinset k N
  · have hsum := sum_wμ_eq_one' (k := k) (μ := μ) N
    have hle :
        wμ (k := k) μ N s ≤
          ∑ e ∈ stateFinset k N, wμ (k := k) μ N e := by
      refine Finset.single_le_sum (f := fun e => wμ (k := k) μ N e) ?_ hs
      intro e he
      exact wμ_nonneg (k := k) (μ := μ) (n := N) (e := e)
    simpa [hsum] using hle
  · have hw0 :
        wμ (k := k) μ N s = 0 :=
      wμ_eq_zero_of_not_mem_stateFinset (k := k) (μ := μ) (n := N) (e := s) hs
    simp [hw0]

lemma sum_wμ_toReal_eq_one (μ : PrefixMeasure (Fin k)) (N : ℕ) :
    ∑ s ∈ stateFinset k N, (wμ (k := k) μ N s).toReal = 1 := by
  classical
  have hsum := sum_wμ_eq_one' (k := k) (μ := μ) N
  have hfinite :
      ∀ s ∈ stateFinset k N, wμ (k := k) μ N s ≠ (⊤ : ENNReal) := by
    intro s hs
    have hle : wμ (k := k) μ N s ≤ 1 := wμ_le_one (k := k) (μ := μ) (N := N) s
    exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)
  have hsum_real :
      (∑ s ∈ stateFinset k N, (wμ (k := k) μ N s).toReal) =
        (∑ s ∈ stateFinset k N, wμ (k := k) μ N s).toReal := by
    simpa using
      (ENNReal.toReal_sum
        (s := stateFinset k N)
        (f := fun s => wμ (k := k) μ N s)
        hfinite).symm
  have hsum_toReal :
      (∑ s ∈ stateFinset k N, wμ (k := k) μ N s).toReal = 1 := by
    simp [hsum]
  exact hsum_real.trans hsum_toReal

end MarkovDeFinettiHard

end Mettapedia.Logic
