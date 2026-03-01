import Mettapedia.Logic.PremiseSelectionSelectorSpec
import Mettapedia.Logic.PremiseSelectionOptimality
import Mettapedia.Logic.PremiseSelectionRankingStability
import Mettapedia.Logic.PremiseSelectionCoverage

/-!
# Chapter 13 Inference-Control Canaries

Executable fixture theorems for Chapter-13 inference-control behavior:

1. Ranking transfer from NB to PLN under explicit emulation assumptions.
2. Positive margin-stability witness under bounded perturbation.
3. Negative witness: ranking can flip when margin assumptions are dropped.
4. Coverage objective insertion law on a finite fixture.
5. Selector default gate range sanity check.
-/

namespace Mettapedia.Logic.PLNInferenceControlCanary

open Mettapedia.Logic.PremiseSelection
open Mettapedia.Logic.PremiseSelectionOptimality

noncomputable section

def ηBool : Bool → ℝ
  | true => 0.9
  | false => 0.1

def sNBBool : Bool → ℝ := ηBool
def sPLNBool : Bool → ℝ := ηBool

/-- Positive canary: NB ranking optimality transfers to the PLN-emulated score. -/
theorem canary_ch13_pln_inherits_nb_ranking_bool :
    BayesOptimalRanking ηBool sPLNBool := by
  refine pln_inherits_nb_ranking ηBool sNBBool sPLNBool ?_ rfl
  refine ⟨id, ?_, ?_⟩
  · simpa using (strictMono_id : StrictMono (fun x : ℝ => x))
  · funext x
    rfl

def sWide : Bool → ℝ := fun b => if b then 4 else 0
def δSmall : Bool → ℝ := fun b => if b then (-(1 / 2 : ℝ)) else (1 / 2 : ℝ)

/-- Positive canary: with margin `> 2ε`, bounded perturbation preserves pair order. -/
theorem canary_ch13_pairwise_stable_of_margin :
    perturbedScore sWide δSmall false < perturbedScore sWide δSmall true := by
  refine pairwise_lt_stable_of_margin (s := sWide) (δ := δSmall)
      (x := false) (y := true) (ε := (1 : ℝ)) ?_ ?_ ?_
  · norm_num [sWide]
  · norm_num [δSmall]
  · norm_num [δSmall]

def sNarrow : Bool → ℝ := fun b => if b then 1 else 0
def δFlip : Bool → ℝ := fun b => if b then (-1) else 1

/-- Negative canary (non-equivalence): without margin assumptions, order can flip. -/
theorem canary_ch13_ranking_flip_without_margin :
    sNarrow false ≤ sNarrow true
      ∧ ¬ (perturbedScore sNarrow δFlip false ≤ perturbedScore sNarrow δFlip true) := by
  constructor
  · norm_num [sNarrow]
  · norm_num [perturbedScore, sNarrow, δFlip]

/-- Coverage insertion law canary on a finite Bool fixture. -/
theorem canary_ch13_dependencyCoverage_insert_gain_bool :
    dependencyCoverage ({true} : Finset Bool) (insert true ({false} : Finset Bool)) =
      dependencyCoverage ({true} : Finset Bool) ({false} : Finset Bool)
      + dependencyGain ({true} : Finset Bool) ({false} : Finset Bool) true := by
  simpa using
    (dependencyCoverage_insert (D := ({true} : Finset Bool))
      (S := ({false} : Finset Bool)) (a := true))

/-- Selector defaults canary: the neutral gate remains in `[0,1]`. -/
theorem canary_ch13_selector_default_gate_bounds :
    0 ≤ (selectorDefaults_halfGate Unit Bool).gate () true
      ∧ (selectorDefaults_halfGate Unit Bool).gate () true ≤ 1 := by
  exact ⟨(selectorDefaults_halfGate Unit Bool).gate_lower () true,
    (selectorDefaults_halfGate Unit Bool).gate_upper () true⟩

end

end Mettapedia.Logic.PLNInferenceControlCanary
