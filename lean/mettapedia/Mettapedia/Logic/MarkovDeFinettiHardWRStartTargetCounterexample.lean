import Mettapedia.Logic.MarkovDeFinettiHardBEST
import Mathlib.Tactic

noncomputable section

namespace Mettapedia.Logic
namespace MarkovDeFinettiHardBEST
namespace WRBridgeCounterexample

open MarkovDeFinettiHard

/-- In the tiny counterexample state, `empiricalParamStartTarget` has the same
initial distribution as `empiricalParam`. -/
lemma initProb_empiricalParamStartTarget_start_file :
    initProb (k := k0) (empiricalParamStartTarget (k := k0) hk0 s) 0 = 1 := by
  have hinit_eq :
      initProb (k := k0) (empiricalParamStartTarget (k := k0) hk0 s) 0 =
        initProb (k := k0) (empiricalParam (k := k0) hk0 s) 0 := by
    simp [initProb, empiricalParamStartTarget, empiricalParam]
  simpa [hinit_eq] using initProb_empiricalParam_start

lemma empiricalStepProbTarget_00_file :
    empiricalStepProbTarget (k := k0) hk0 s.counts 0 0 = 1 := by
  have hcounts00 : s.counts.counts 0 0 = 3 := by
    native_decide
  have hrow : s.counts.rowTotal 0 = 3 := by
    native_decide
  simp [empiricalStepProbTarget, hcounts00, hrow]

lemma stepProb_empiricalParamStartTarget_00_file :
    (stepProb (k := k0) (empiricalParamStartTarget (k := k0) hk0 s) 0 0 : ℝ) = 1 := by
  have hstart : s.start = 0 := by
    simp [s, stateOfTraj, traj0000]
  have hstep :
      (stepProb (k := k0) (empiricalParamStartTarget (k := k0) hk0 s) 0 0 : ℝ) =
        empiricalStepProbTarget (k := k0) hk0 s.counts 0 0 := by
    simpa [hstart] using
      (stepProb_empiricalParamStartTarget
        (k := k0) (hk := hk0) (s := s) (a := 0) (b := 0))
  simpa [hstep] using empiricalStepProbTarget_00_file

lemma wordProb_traj000_startTarget_file :
    (wordProb (k := k0) (empiricalParamStartTarget (k := k0) hk0 s)
      (trajToList (k := k0) traj000)).toReal = 1 := by
  have hlist : trajToList (k := k0) traj000 = [0, 0, 0] := by
    simp [trajToList, traj000]
  simp [wordProb, wordProbNN, wordProbAux, hlist,
    initProb_empiricalParamStartTarget_start_file, stepProb_empiricalParamStartTarget_00_file]

/-- Tiny-model scalar sanity check: exact `W` value for `empiricalParamStartTarget`
in the `k=2,n=1,N=3` constant-trajectory example. -/
lemma W_toReal_tiny_example_startTarget_file :
    (W (k := k0) (Nat.succ n0) e (empiricalParamStartTarget (k := k0) hk0 s)).toReal = 1 := by
  have hW :=
    W_eq_card_mul_wordProb_of_mem_fiber
      (k := k0) (N := Nat.succ n0)
      (θ := empiricalParamStartTarget (k := k0) hk0 s) (s := e)
      traj000 traj000_mem_fiber
  have hW' :
      (W (k := k0) (Nat.succ n0) e (empiricalParamStartTarget (k := k0) hk0 s)).toReal =
        ((fiber k0 (Nat.succ n0) e).card : ENNReal).toReal *
          (wordProb (k := k0) (empiricalParamStartTarget (k := k0) hk0 s)
            (trajToList (k := k0) traj000)).toReal := by
    simpa [ENNReal.toReal_mul] using congrArg ENNReal.toReal hW
  calc
    (W (k := k0) (Nat.succ n0) e (empiricalParamStartTarget (k := k0) hk0 s)).toReal
        = ((fiber k0 (Nat.succ n0) e).card : ENNReal).toReal *
            (wordProb (k := k0) (empiricalParamStartTarget (k := k0) hk0 s)
              (trajToList (k := k0) traj000)).toReal := hW'
    _ = (1 : ℝ) * 1 := by
          simp [short_fiber_card, wordProb_traj000_startTarget_file]
    _ = 1 := by ring

/-- Tiny-model start-target scalar gap: exact value `9/25`. -/
lemma W_gap_empirical_vs_startTarget_tiny_example_file :
    |(W (k := k0) (Nat.succ n0) e (empiricalParam (k := k0) hk0 s)).toReal -
      (W (k := k0) (Nat.succ n0) e (empiricalParamStartTarget (k := k0) hk0 s)).toReal| =
      (9 / 25 : ℝ) := by
  rw [W_toReal_tiny_example, W_toReal_tiny_example_startTarget_file]
  norm_num

/-- Tiny-model witness for the start-target scalar rate shape with `Cw = 27/25`. -/
lemma tiny_startTargetWClose_rate_file :
    |(W (k := k0) (Nat.succ n0) e (empiricalParam (k := k0) hk0 s)).toReal -
      (W (k := k0) (Nat.succ n0) e (empiricalParamStartTarget (k := k0) hk0 s)).toReal| ≤
      (27 / 25 : ℝ) / (returnsToStart (k := k0) s : ℝ) := by
  rw [W_gap_empirical_vs_startTarget_tiny_example_file, returnsToStart_s]
  norm_num

/-- Sharp tiny-model lower bound: this witness shape forces `Cw ≥ 27/25`. -/
lemma tiny_Cw_lower_bound_for_startTarget_file
    {Cw : ℝ}
    (hbound :
      |(W (k := k0) (Nat.succ n0) e (empiricalParam (k := k0) hk0 s)).toReal -
        (W (k := k0) (Nat.succ n0) e (empiricalParamStartTarget (k := k0) hk0 s)).toReal| ≤
        Cw / (returnsToStart (k := k0) s : ℝ)) :
    (27 / 25 : ℝ) ≤ Cw := by
  rw [W_gap_empirical_vs_startTarget_tiny_example_file, returnsToStart_s] at hbound
  have hmult : (27 / 25 : ℝ) ≤ Cw := by
    have : (9 / 25 : ℝ) ≤ Cw / 3 := by simpa using hbound
    nlinarith
  exact hmult

end WRBridgeCounterexample
end MarkovDeFinettiHardBEST
end Mettapedia.Logic
