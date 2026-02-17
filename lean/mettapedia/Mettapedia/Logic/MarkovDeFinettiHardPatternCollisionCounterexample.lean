import Mettapedia.Logic.MarkovDeFinettiHardGoodStateBound
import Mathlib.Tactic

noncomputable section

namespace Mettapedia.Logic
namespace MarkovDeFinettiHard
namespace PatternCollisionCounterexample

open scoped Classical BigOperators
open MeasureTheory
open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.FiniteAlphabet
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovDeFinettiRecurrence
open Mettapedia.Logic.EvidenceDirichlet
open Mettapedia.Logic.MarkovDeFinettiHardExcursions
open Mettapedia.Logic.MarkovDeFinettiHardExcursionModel
open Mettapedia.Logic.MarkovDeFinettiHardWithoutReplacement
open Mettapedia.Logic.MarkovDeFinettiHardWithoutReplacementModel
open Mettapedia.Logic.MarkovDeFinettiHardBEST

abbrev kCE : ℕ := 6
abbrev nCE : ℕ := 0
abbrev NCE : ℕ := 25

lemma hkCE : 0 < kCE := by decide
lemma hNCE : Nat.succ nCE ≤ NCE := by decide

/-- Constant short trajectory (length `2`). -/
def trajShort : Traj kCE (Nat.succ nCE) := fun _ => 0

/-- Constant long trajectory (length `26`). -/
def trajLong : Traj kCE NCE := fun _ => 0

def e : MarkovState kCE := stateOfTraj (k := kCE) trajShort
def s : MarkovState kCE := stateOfTraj (k := kCE) trajLong
def p : ExcursionList kCE := excursionListOfTraj (k := kCE) trajShort

lemma hs : s ∈ stateFinset kCE NCE := by
  unfold stateFinset trajFinset s
  exact Finset.mem_image.2 ⟨trajLong, by simp, rfl⟩

/-- Symbolic return-count formula for the constant long trajectory. -/
lemma returnsToStart_s : returnsToStart (k := kCE) s = NCE := by
  change returnsToStart (k := kCE) (stateOfTraj (k := kCE) trajLong) = NCE
  simpa [trajLong] using
    (returnsToStart_stateOfTraj (k := kCE) (xs := trajLong))

lemma returnsToStart_pos : 0 < returnsToStart (k := kCE) s := by
  rw [returnsToStart_s]
  norm_num

lemma counts00 : s.counts.counts 0 0 = NCE := by
  simp [s, stateOfTraj, MarkovExchangeabilityBridge.countsOfFn,
    MarkovExchangeability.transCount, trajLong]

lemma counts0b_zero (b : Fin kCE) (hb : b ≠ 0) : s.counts.counts 0 b = 0 := by
  have hb' : (0 : Fin kCE) ≠ b := by simpa using hb.symm
  simp [s, stateOfTraj, MarkovExchangeabilityBridge.countsOfFn,
    MarkovExchangeability.transCount, trajLong, hb']

lemma rowTotal0 : s.counts.rowTotal 0 = NCE := by
  unfold TransCounts.rowTotal
  have hsum :
      (∑ b : Fin kCE, s.counts.counts 0 b) = s.counts.counts 0 0 := by
    classical
    refine Finset.sum_eq_single 0 ?_ ?_
    · intro b _ hb
      exact counts0b_zero b hb
    · intro h0
      exact (h0 (Finset.mem_univ 0)).elim
  simpa [counts00] using hsum

lemma trajShort_mem_fiber : trajShort ∈ fiber kCE (Nat.succ nCE) e := by
  simp [fiber, trajFinset, e]

lemma eq_trajShort_of_mem_shortFiber {ys : Traj kCE (Nat.succ nCE)}
    (hys : ys ∈ fiber kCE (Nat.succ nCE) e) : ys = trajShort := by
  have hstate : stateOfTraj (k := kCE) ys = e := (Finset.mem_filter.1 hys).2
  have h0 : ys 0 = 0 := by
    have hstart := congrArg MarkovState.start hstate
    simpa [e, stateOfTraj, trajShort] using hstart
  have hlast : ys (Fin.last (Nat.succ nCE)) = 0 := by
    have hlast' := congrArg MarkovState.last hstate
    simpa [e, stateOfTraj, trajShort] using hlast'
  have h1 : ys 1 = 0 := by
    simpa [nCE] using hlast
  ext i
  fin_cases i
  · simpa [trajShort] using h0
  · simpa [trajShort] using h1

lemma shortFiber_eq_singleton : fiber kCE (Nat.succ nCE) e = {trajShort} := by
  ext ys
  constructor
  · intro hys
    simp [eq_trajShort_of_mem_shortFiber (hys := hys)]
  · intro hys
    rcases Finset.mem_singleton.1 hys with rfl
    exact trajShort_mem_fiber

lemma shortPatternFiber_eq_singleton :
    shortPatternFiber (k := kCE) nCE e p = {trajShort} := by
  ext ys
  constructor
  · intro hys
    have hyFiber : ys ∈ fiber kCE (Nat.succ nCE) e := (Finset.mem_filter.1 hys).1
    simp [eq_trajShort_of_mem_shortFiber (hys := hyFiber)]
  · intro hys
    rcases Finset.mem_singleton.1 hys with rfl
    exact Finset.mem_filter.2 ⟨trajShort_mem_fiber, by simp [p]⟩

/-- Symbolic start-row Laplace-smoothed step probability. -/
lemma empiricalStepProb_00 :
    empiricalStepProb (k := kCE) hkCE s.counts 0 0 = (26 / 31 : ℝ) := by
  rw [empiricalStepProb]
  simp [counts00, rowTotal0, DirichletParams.uniformPrior, DirichletParams.uniform,
    DirichletParams.totalConcentration]
  norm_num

lemma initProb_empiricalParam_local (a : Fin kCE) :
    initProb (k := kCE) (empiricalParam (k := kCE) hkCE s) a =
      (if a = s.start then 1 else 0) := by
  classical
  by_cases h : a = s.start
  · subst h
    have hm : s.start ∈ Set.singleton s.start := Set.mem_singleton _
    simp [initProb, empiricalParam, Set.indicator, hm]
  · have hm : s.start ∉ Set.singleton a := by
      intro hs0
      exact h hs0.symm
    simp [initProb, empiricalParam, Set.indicator, hm, h]

lemma initProb_empiricalParam_start :
    initProb (k := kCE) (empiricalParam (k := kCE) hkCE s) 0 = 1 := by
  have hstart : s.start = 0 := by
    simp [s, stateOfTraj, trajLong]
  simpa [hstart] using (initProb_empiricalParam_local (a := 0))

lemma stepProb_empiricalParam_00 :
    (stepProb (k := kCE) (empiricalParam (k := kCE) hkCE s) 0 0 : ℝ) = (26 / 31 : ℝ) := by
  simpa [empiricalStepProb_00] using
    (stepProb_empiricalParam (k := kCE) (hk := hkCE) (s := s) (a := 0) (b := 0))

lemma wordProb_trajShort :
    (wordProb (k := kCE) (empiricalParam (k := kCE) hkCE s)
      (trajToList (k := kCE) trajShort)).toReal = (26 / 31 : ℝ) := by
  have hlist : trajToList (k := kCE) trajShort = [0, 0] := by
    simp [trajToList, trajShort]
  simp [wordProb, wordProbNN, wordProbAux, hlist,
    initProb_empiricalParam_start, stepProb_empiricalParam_00]

/-- Symbolic WR single-pattern mass in the constant-trajectory setup. -/
lemma wrPatternMass_p :
    (wrPatternMass (k := kCE) hkCE nCE e s p).toReal = (26 / 31 : ℝ) := by
  unfold wrPatternMass
  rw [shortFiber_eq_singleton]
  simp [p, wordProb_trajShort]

lemma firstStep_zero_of_mem_longFiber {xs : Traj kCE NCE}
    (hxs : xs ∈ fiber kCE NCE s) : xs 1 = 0 := by
  have hstate : stateOfTraj (k := kCE) xs = s := (Finset.mem_filter.1 hxs).2
  have hstart : xs 0 = 0 := by
    have hstart' := congrArg MarkovState.start hstate
    simpa [s, stateOfTraj, trajLong] using hstart'
  by_contra h1
  let b : Fin kCE := xs 1
  have hb : b ≠ 0 := by simpa [b] using h1
  have hmem0 :
      (0 : Fin NCE) ∈
        (Finset.univ.filter
          (fun i : Fin NCE => xs (Fin.castSucc i) = (0 : Fin kCE) ∧ xs (Fin.succ i) = b)) := by
    refine Finset.mem_filter.2 ?_
    refine ⟨by simp, ?_⟩
    simp [hstart, b]
  have hcnt_ge1 :
      1 ≤ MarkovExchangeability.transCount (n := NCE) xs 0 b := by
    unfold MarkovExchangeability.transCount
    exact Finset.one_le_card.mpr ⟨0, hmem0⟩
  have hcnt_eq :
      MarkovExchangeability.transCount (n := NCE) xs 0 b = s.counts.counts 0 b := by
    have hcountsEq := congrArg (fun st : MarkovState kCE => st.counts.counts 0 b) hstate
    simpa [stateOfTraj, MarkovExchangeabilityBridge.countsOfFn] using hcountsEq
  have hcnt_zero : s.counts.counts 0 b = 0 := counts0b_zero b hb
  have hcontra : (1 : ℕ) ≤ 0 := by
    calc
      1 ≤ MarkovExchangeability.transCount (n := NCE) xs 0 b := hcnt_ge1
      _ = s.counts.counts 0 b := hcnt_eq
      _ = 0 := hcnt_zero
  exact Nat.not_succ_le_zero 0 hcontra

lemma prefixEq_trajShort_of_mem_longFiber {xs : Traj kCE NCE}
    (hxs : xs ∈ fiber kCE NCE s) :
    trajPrefix (k := kCE) hNCE xs = trajShort := by
  have hstate : stateOfTraj (k := kCE) xs = s := (Finset.mem_filter.1 hxs).2
  have h0 : xs 0 = 0 := by
    have hstart' := congrArg MarkovState.start hstate
    simpa [s, stateOfTraj, trajLong] using hstart'
  have h1 : xs 1 = 0 := firstStep_zero_of_mem_longFiber (hxs := hxs)
  ext i
  fin_cases i
  · simp [trajPrefix, trajShort, h0]
  · simpa [trajPrefix, trajShort, hNCE, nCE] using h1

lemma prefixPatternFiber_eq_longFiber :
    prefixPatternFiber (k := kCE) (hN := hNCE) e s p = fiber kCE NCE s := by
  ext xs
  constructor
  · intro hxs
    exact (Finset.mem_filter.1 ((Finset.mem_filter.1 hxs).1)).1
  · intro hxs
    have hprefixEq : trajPrefix (k := kCE) hNCE xs = trajShort :=
      prefixEq_trajShort_of_mem_longFiber (hxs := hxs)
    have hprefixState : prefixState (k := kCE) (n := Nat.succ nCE) (N := NCE) hNCE xs = e := by
      simp [prefixState, e, hprefixEq]
    refine Finset.mem_filter.2 ?_
    refine ⟨Finset.mem_filter.2 ⟨hxs, hprefixState⟩, ?_⟩
    simp [p, hprefixEq]

/-- Symbolic WOR single-pattern mass in the constant-trajectory setup. -/
lemma worPatternMass_p :
    (worPatternMass (k := kCE) (hN := hNCE) e s p).toReal = 1 := by
  have hfiber_card_ne :
      (fiber kCE NCE s).card ≠ 0 :=
    fiber_card_ne_zero_of_mem_stateFinset (k := kCE) (N := NCE) (eN := s) hs
  unfold worPatternMass
  have hden_ne : ((fiber kCE NCE s).card : ENNReal) ≠ 0 := by
    exact_mod_cast hfiber_card_ne
  have hden_top : ((fiber kCE NCE s).card : ENNReal) ≠ ⊤ := by simp
  have hdiv_one :
      ((fiber kCE NCE s).card : ENNReal) / ((fiber kCE NCE s).card : ENNReal) = 1 := by
    exact (ENNReal.div_eq_one_iff hden_ne hden_top).2 rfl
  simp [prefixPatternFiber_eq_longFiber, hdiv_one]

lemma patternSet_eq_singleton :
    excursionPatternSet (k := kCE) (hN := hNCE) e s = {p} := by
  rw [excursionPatternSet_eq_shortImage (k := kCE) (hN := hNCE) (e := e) (s := s)]
  rw [shortFiber_eq_singleton]
  simp [p]

/-- Counterexample: collision-only positive-return pattern bound is false for `k=6`. -/
theorem not_HasPatternCollisionPosAll_k6 :
    ¬ HasPatternCollisionPosAll (k := kCE) := by
  intro hposAll
  let f : ExcursionList kCE → ℝ := fun q =>
    |(wrPatternMass (k := kCE) hkCE nCE e s q).toReal -
      (worPatternMass (k := kCE) (hN := hNCE) e s q).toReal|
  have hboundSum :
      (∑ q ∈ excursionPatternSet (k := kCE) (hN := hNCE) e s, f q) ≤
        (4 * ((Nat.succ nCE : ℕ) : ℝ) * ((Nat.succ nCE : ℕ) : ℝ)) /
          (returnsToStart (k := kCE) s : ℝ) := by
    simpa [f] using
      hposAll (hk := hkCE) (n := nCE) (e := e)
        (N := NCE) (hN := hNCE) (s := s) hs returnsToStart_pos
  have hfinal :
      f p ≤
        (4 * ((Nat.succ nCE : ℕ) : ℝ) * ((Nat.succ nCE : ℕ) : ℝ)) /
          (returnsToStart (k := kCE) s : ℝ) := by
    simpa [patternSet_eq_singleton, f] using hboundSum
  have hnumFalse : ¬ (|(26 / 31 : ℝ) - 1| ≤ (4 / 25 : ℝ)) := by
    norm_num
  exact hnumFalse (by simpa [f, wrPatternMass_p, worPatternMass_p, returnsToStart_s] using hfinal)

end PatternCollisionCounterexample
end MarkovDeFinettiHard
end Mettapedia.Logic
