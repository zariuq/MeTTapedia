import Mettapedia.Logic.PLNEndToEnd

/-!
# Proof-Carrying Factor-Graph Contraction Demo

This file packages one explicit "PLN-style rule firing" story in the corrected WM setting.

- The semantic truthmaker is a small binary factor graph / BN.
- Each derived step is a local contraction with explicit Sigma obligations and provenance.
- The exact fragment matches the existing chain/fork theorem surface.
- Two negative controls show why the gate matters:
  a soft-gated perturbation and a collider abduction counterexample.

The demo is intentionally thin.  It does not add a new BN proof stack; it gives a worked
numeric wrapper around the already-proved exactness / no-go endpoints exposed by
`PLNEndToEnd`.
-/

namespace Mettapedia.Logic.PLNProofCarryingContractionDemo

open scoped BigOperators
open Finset
open Mettapedia.Logic
open Mettapedia.Logic.PLN

/-! ## Provenance Surface -/

/-- Small proof-carrying object for the demo.

It is intentionally not a naked derived link.  The carried data makes the local
Sigma assumptions and theorem provenance explicit. -/
structure ProofCarryingContraction where
  query : String
  exactValue : ℚ
  sigma : List String
  provenance : List String
  gate : Option String

/-! ## Base 5-Node Fixture

The worked example uses the explicit binary graph

`A <- H -> B -> C -> D`

with rational parameters so that the exact semantic answers can be reduced by `norm_num`.
-/

/-- Bernoulli mass at a Boolean value. -/
def bern (p : ℚ) (b : Bool) : ℚ :=
  if b then p else 1 - p

def pH : ℚ := 1 / 5

def pA_given_H : Bool → ℚ
  | true => 9 / 10
  | false => 1 / 10

def pB_given_H : Bool → ℚ
  | true => 4 / 5
  | false => 1 / 5

def pC_given_B : Bool → ℚ
  | true => 17 / 20
  | false => 3 / 20

def pD_given_C : Bool → ℚ
  | true => 9 / 10
  | false => 1 / 10

/-- Exact semantic joint weight for the base fixture. -/
def baseWeight (h a b c d : Bool) : ℚ :=
  bern pH h *
    bern (pA_given_H h) a *
    bern (pB_given_H h) b *
    bern (pC_given_B b) c *
    bern (pD_given_C c) d

def baseProb_A_true : ℚ :=
  ∑ h : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool,
    baseWeight h true b c d

def baseProb_B_true : ℚ :=
  ∑ h : Bool, ∑ a : Bool, ∑ c : Bool, ∑ d : Bool,
    baseWeight h a true c d

def baseProb_C_true : ℚ :=
  ∑ h : Bool, ∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
    baseWeight h a b true d

def baseProb_D_true : ℚ :=
  ∑ h : Bool, ∑ a : Bool, ∑ b : Bool, ∑ c : Bool,
    baseWeight h a b c true

def baseProb_B_true_given_A_true : ℚ :=
  (∑ h : Bool, ∑ c : Bool, ∑ d : Bool, baseWeight h true true c d) / baseProb_A_true

def baseProb_C_true_given_A_true : ℚ :=
  (∑ h : Bool, ∑ b : Bool, ∑ d : Bool, baseWeight h true b true d) / baseProb_A_true

def baseProb_D_true_given_A_true : ℚ :=
  (∑ h : Bool, ∑ b : Bool, ∑ c : Bool, baseWeight h true b c true) / baseProb_A_true

theorem baseProb_A_true_value : baseProb_A_true = 13 / 50 := by
  norm_num [baseProb_A_true, baseWeight, bern, pH, pA_given_H, pB_given_H, pC_given_B, pD_given_C]

theorem baseProb_B_true_value : baseProb_B_true = 8 / 25 := by
  norm_num [baseProb_B_true, baseWeight, bern, pH, pA_given_H, pB_given_H, pC_given_B, pD_given_C]

theorem baseProb_C_true_value : baseProb_C_true = 187 / 500 := by
  norm_num [baseProb_C_true, baseWeight, bern, pH, pA_given_H, pB_given_H, pC_given_B, pD_given_C]

theorem baseProb_D_true_value : baseProb_D_true = 499 / 1250 := by
  norm_num [baseProb_D_true, baseWeight, bern, pH, pA_given_H, pB_given_H, pC_given_B, pD_given_C]

theorem baseProb_B_true_given_A_true_value : baseProb_B_true_given_A_true = 8 / 13 := by
  norm_num [baseProb_B_true_given_A_true, baseProb_A_true, baseWeight, bern,
    pH, pA_given_H, pB_given_H, pC_given_B, pD_given_C]

theorem baseProb_C_true_given_A_true_value : baseProb_C_true_given_A_true = 151 / 260 := by
  norm_num [baseProb_C_true_given_A_true, baseProb_A_true, baseWeight, bern,
    pH, pA_given_H, pB_given_H, pC_given_B, pD_given_C]

theorem baseProb_D_true_given_A_true_value : baseProb_D_true_given_A_true = 367 / 650 := by
  norm_num [baseProb_D_true_given_A_true, baseProb_A_true, baseWeight, bern,
    pH, pA_given_H, pB_given_H, pC_given_B, pD_given_C]

/-! ## Exact Contraction Steps -/

/-- Exact fork-style contraction for `P(B=1 | A=1)`. -/
def forkStep_B_given_A : ProofCarryingContraction where
  query := "P(B=1 | A=1)"
  exactValue := baseProb_B_true_given_A_true
  sigma :=
    [ "fork screening-off via H"
    , "positivity: P(H=1) in (0,1)"
    , "exact semantic baseline by finite factor-graph elimination" ]
  provenance :=
    [ "PLNEndToEnd.forkFormulaExact"
    , "PLNXiDerivedBNRules.Typed.xi_sourceRule_rewrite_of_forkBN_sigma_concrete" ]
  gate := some "exact"

/-- Exact chain-style contraction for `P(C=1 | A=1)`. -/
def chainStep_C_given_A : ProofCarryingContraction where
  query := "P(C=1 | A=1)"
  exactValue := baseProb_C_true_given_A_true
  sigma :=
    [ "chain screening-off via B"
    , "positivity: P(B=1) in (0,1)"
    , "exact semantic baseline by finite factor-graph elimination" ]
  provenance :=
    [ "PLNEndToEnd.chainFormulaExact"
    , "PLNXiDerivedBNRules.Typed.xi_deduction_rewrite_of_chainBN_sigma_concrete" ]
  gate := some "exact"

/-- Exact second chain-style contraction for `P(D=1 | A=1)`. -/
def chainStep_D_given_A : ProofCarryingContraction where
  query := "P(D=1 | A=1)"
  exactValue := baseProb_D_true_given_A_true
  sigma :=
    [ "chain screening-off via C"
    , "positivity: P(C=1) in (0,1)"
    , "exact semantic baseline by finite factor-graph elimination" ]
  provenance :=
    [ "PLNEndToEnd.chainFormulaExact"
    , "PLNXiDerivedBNRules.Typed.xi_deduction_rewrite_of_chainBN_sigma_concrete" ]
  gate := some "exact"

theorem fork_contraction_matches_exact_semantics :
    plnInductionStrength (9 / 10 : ℝ) (4 / 5 : ℝ) (13 / 50 : ℝ) (1 / 5 : ℝ) (8 / 25 : ℝ) =
      (8 / 13 : ℝ) := by
  norm_num [plnInductionStrength, bayesInversion, plnDeductionStrength]

theorem chain_contraction_C_matches_exact_semantics :
    plnDeductionStrength (8 / 13 : ℝ) (17 / 20 : ℝ) (8 / 25 : ℝ) (187 / 500 : ℝ) =
      (151 / 260 : ℝ) := by
  norm_num [plnDeductionStrength]

theorem chain_contraction_D_matches_exact_semantics :
    plnDeductionStrength (151 / 260 : ℝ) (9 / 10 : ℝ) (187 / 500 : ℝ) (499 / 1250 : ℝ) =
      (367 / 650 : ℝ) := by
  norm_num [plnDeductionStrength]

/-! ## Soft-Gated Perturbation

Now `C` depends weakly on `A` as well as `B`, so the screened-off chain contraction
is no longer exact.
-/

def pC_given_A_B_soft : Bool → Bool → ℚ
  | false, false => 3 / 20
  | true, false => 1 / 4
  | false, true => 17 / 20
  | true, true => 9 / 10

def softWeight (h a b c d : Bool) : ℚ :=
  bern pH h *
    bern (pA_given_H h) a *
    bern (pB_given_H h) b *
    bern (pC_given_A_B_soft a b) c *
    bern (pD_given_C c) d

def softProb_C_true : ℚ :=
  ∑ h : Bool, ∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
    softWeight h a b true d

def softProb_C_true_given_A_true : ℚ :=
  (∑ h : Bool, ∑ b : Bool, ∑ d : Bool, softWeight h true b true d) / baseProb_A_true

def softProb_C_true_given_B_true : ℚ :=
  (∑ h : Bool, ∑ a : Bool, ∑ d : Bool, softWeight h a true true d) / baseProb_B_true

noncomputable def softNaiveChainFromB_only : ℝ :=
  let sAB := baseProb_B_true_given_A_true
  let sBC := softProb_C_true_given_B_true
  let sB := baseProb_B_true
  let sC := softProb_C_true
  plnDeductionStrength (sAB : ℝ) (sBC : ℝ) (sB : ℝ) (sC : ℝ)

theorem softProb_C_true_value : softProb_C_true = 49 / 125 := by
  norm_num [softProb_C_true, softWeight, baseWeight, bern, pH, pA_given_H, pB_given_H,
    pC_given_A_B_soft, pD_given_C]

theorem softProb_C_true_given_A_true_value : softProb_C_true_given_A_true = 13 / 20 := by
  norm_num [softProb_C_true_given_A_true, baseProb_A_true, softWeight, baseWeight, bern,
    pH, pA_given_H, pB_given_H, pC_given_A_B_soft, pC_given_B, pD_given_C]

theorem softProb_C_true_given_B_true_value : softProb_C_true_given_B_true = 7 / 8 := by
  norm_num [softProb_C_true_given_B_true, baseProb_B_true, softWeight, baseWeight, bern,
    pH, pA_given_H, pB_given_H, pC_given_A_B_soft, pC_given_B, pD_given_C]

theorem softNaiveChainFromB_only_value :
    softNaiveChainFromB_only = (133 / 221 : ℝ) := by
  norm_num [softNaiveChainFromB_only, baseProb_B_true_given_A_true, softProb_C_true_given_B_true,
    baseProb_B_true, softProb_C_true, baseProb_A_true, softWeight, baseWeight, bern,
    pH, pA_given_H, pB_given_H, pC_given_A_B_soft, pC_given_B, pD_given_C,
    plnDeductionStrength]

theorem soft_gate_blocks_exact_contraction :
    softNaiveChainFromB_only ≠ (softProb_C_true_given_A_true : ℝ) := by
  norm_num [softNaiveChainFromB_only, softProb_C_true_given_A_true, baseProb_B_true_given_A_true,
    softProb_C_true_given_B_true, baseProb_B_true, softProb_C_true, baseProb_A_true, softWeight,
    baseWeight, bern, pH, pA_given_H, pB_given_H, pC_given_A_B_soft, pC_given_B, pD_given_C,
    plnDeductionStrength]

def softGateStep_C_given_A : ProofCarryingContraction where
  query := "P(C=1 | A=1) with residual A -> C dependence"
  exactValue := softProb_C_true_given_A_true
  sigma :=
    [ "screening-off via B is not discharged"
    , "C retains direct dependence on A"
    , "exact semantic baseline by finite factor-graph elimination" ]
  provenance :=
    [ "soft_gate_blocks_exact_contraction"
    , "PLNEndToEnd.chainFormulaExact (blocked here by Sigma)" ]
  gate := some "blocked"

/-! ## Collider Negative Control -/

def colliderExactProb_B_true_given_A_true : ℚ := 1 / 2

def colliderNaiveAbduction : ℚ := 2 / 3

theorem colliderNaiveAbduction_value :
    plnAbductionStrength (1 : ℝ) (1 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) (1 / 2 : ℝ) =
      (2 / 3 : ℝ) := by
  norm_num [plnAbductionStrength, bayesInversion, plnDeductionStrength]

theorem collider_negative_control_blocks_naive_abduction :
    plnAbductionStrength (1 : ℝ) (1 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) (1 / 2 : ℝ) ≠
      (colliderExactProb_B_true_given_A_true : ℝ) := by
  simpa [colliderExactProb_B_true_given_A_true] using PLNEndToEnd.colliderNotExact

def colliderNegativeControl : ProofCarryingContraction where
  query := "P(B=1 | A=1) in OR-gate collider"
  exactValue := colliderExactProb_B_true_given_A_true
  sigma :=
    [ "collider topology does not discharge the old naive abduction rule"
    , "exact semantic answer remains the truthmaker" ]
  provenance :=
    [ "PLNEndToEnd.colliderNotExact"
    , "collider_negative_control_blocks_naive_abduction" ]
  gate := some "blocked"

end Mettapedia.Logic.PLNProofCarryingContractionDemo
