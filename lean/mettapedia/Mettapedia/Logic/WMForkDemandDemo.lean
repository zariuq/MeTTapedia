/-!
# Fork+Chain Demand Demo: Demand Propagation on a Non-Trivial BN

Graduate-level backward chaining demo. Uses the SAME `A ← H → B → C → D`
topology from `PLNProofCarryingContractionDemo.lean` (which has exact ℚ
semantics, 17 theorems, 0 sorry) and adds demand propagation on top.

## Why the fork matters

On a straight chain (WMDemandDemo), demand flows linearly. On a fork,
the hidden cause H produces BOTH A and B. When querying D, demand
arrives at H via TWO paths:

    D ← C ← B ← H → A

Path 1 (chain): D→C→B→H (high demand — B is unknown)
Path 2 (fork):  A→H       (low demand — A is observed)

Demand at H = max(path1, path2) — not sum (they share the same latent).

This is Ben Goertzel's core contribution in "PLN Backward-Chaining in MORK
via Factor Graphs" (§4.1 aggregation, §7.3 max vs additive).

## Parameters

Same as PLNProofCarryingContractionDemo:
- P(H=1) = 1/5, P(A=1|H) = 9/10 or 1/10, P(B=1|H) = 4/5 or 1/5
- P(C=1|B) = 17/20 or 3/20, P(D=1|C) = 9/10 or 1/10

Exact marginals (proven in contraction demo):
- P(A=1) = 13/50 = 0.260, P(B=1) = 8/25 = 0.320
- P(B=1|A=1) = 8/13 ≈ 0.615 (fork contraction)

## Encoding

All values × 1000 as Nat for kernel-checkable arithmetic.

0 sorry.
-/

namespace Mettapedia.Logic.WMForkDemandDemo

/-! ## §1: Fork+chain nodes

Topology: `A ← H → B → C → D`

H is hidden (unobserved). A is observed. B, C, D are unknown before supply.
Query target: D. -/

structure STV1k where
  s : Nat  -- strength × 1000
  c : Nat  -- confidence × 1000
  deriving DecidableEq, BEq, Repr

-- STVs from the BN parameters (strengths = marginal probabilities × 1000)
def vH    : STV1k := ⟨200, 0⟩      -- P(H=1)=0.2, HIDDEN (unobserved)
def vA    : STV1k := ⟨260, 900⟩    -- P(A=1)=0.26, OBSERVED (high confidence)
def vB    : STV1k := ⟨320, 0⟩      -- P(B=1)=0.32, unknown before supply
def vC    : STV1k := ⟨374, 0⟩      -- P(C=1)=0.374, unknown
def vD    : STV1k := ⟨399, 0⟩      -- P(D=1)=0.399, QUERY TARGET

-- Rule STVs (conditional probabilities as link strengths)
def vHtoA : STV1k := ⟨900, 800⟩    -- P(A|H=1)=0.9, well-established
def vHtoB : STV1k := ⟨800, 800⟩    -- P(B|H=1)=0.8, well-established
def vBtoC : STV1k := ⟨850, 600⟩    -- P(C|B=1)=0.85, moderate confidence
def vCtoD : STV1k := ⟨900, 600⟩    -- P(D|C=1)=0.9, moderate confidence

/-! ## §2: Information need -/

def need (tv : STV1k) : Nat := 1000 - tv.c

theorem need_H : need vH = 1000 := by decide     -- HIDDEN: maximum need
theorem need_A : need vA = 100 := by decide       -- OBSERVED: low need
theorem need_B : need vB = 1000 := by decide      -- unknown: maximum need
theorem need_C : need vC = 1000 := by decide
theorem need_D : need vD = 1000 := by decide

/-! ## §3: Backward demand from D (chain path: D→C→B)

Query D with demand = 1000 (= 1.0). -/

def demD : Nat := 1000

-- At factor f_CD: conclusion D, premises C and C→D
def sens_fCD_C : Nat := max vCtoD.s vCtoD.c          -- max(900, 600) = 900
def sens_fCD_rule : Nat := max vC.s vC.c              -- max(374, 0) = 374
def S_fCD : Nat := max sens_fCD_C sens_fCD_rule       -- 900

def nsens_fCD_C : Nat := sens_fCD_C * 1000 / S_fCD         -- 1000
def nsens_fCD_rule : Nat := sens_fCD_rule * 1000 / S_fCD   -- 415

def demC : Nat := min 1000 (demD * nsens_fCD_C / 1000 * need vC / 1000)
def demCtoD : Nat := min 1000 (demD * nsens_fCD_rule / 1000 * need vCtoD / 1000)

theorem demand_C : demC = 1000 := by decide
theorem demand_CtoD : demCtoD = 166 := by decide

-- At factor f_BC: conclusion C, premises B and B→C
def sens_fBC_B : Nat := max vBtoC.s vBtoC.c          -- max(850, 600) = 850
def sens_fBC_rule : Nat := max vB.s vB.c              -- max(320, 0) = 320
def S_fBC : Nat := max sens_fBC_B sens_fBC_rule       -- 850

def nsens_fBC_B : Nat := sens_fBC_B * 1000 / S_fBC         -- 1000
def nsens_fBC_rule : Nat := sens_fBC_rule * 1000 / S_fBC   -- 376

def demB : Nat := min 1000 (demC * nsens_fBC_B / 1000 * need vB / 1000)
def demBtoC : Nat := min 1000 (demC * nsens_fBC_rule / 1000 * need vBtoC / 1000)

theorem demand_B : demB = 1000 := by decide
theorem demand_BtoC : demBtoC = 150 := by decide

/-! ## §4: Backward demand at the fork (H produces both A and B)

At factor f_HB: conclusion B, premise H
At factor f_HA: conclusion A, premise H

H receives demand from BOTH paths. -/

-- Path 1: via B (chain path to query D)
def sens_fHB_H : Nat := max vHtoB.s vHtoB.c     -- max(800, 800) = 800
def S_fHB : Nat := sens_fHB_H                    -- single premise

def demH_via_B : Nat := min 1000 (demB * 1000 / 1000 * need vH / 1000)
  -- dem(B) × nsens(H in f_HB) × need(H) = 1000 × 1.0 × 1.0 = 1000

-- Path 2: via A (fork arm — but A is observed, low need at A)
-- First compute demand at A through the fork
def sens_fHA_H : Nat := max vHtoA.s vHtoA.c     -- max(900, 800) = 900
-- A is observed, so demand at A flows backward through f_HA
-- But A has LOW demand because its need is only 100 (confidence = 0.9)
def demA : Nat := 0  -- A is observed, no backward demand reaches it externally
-- If we did propagate demand from A: dem_H_via_A = demA × nsens × need
def demH_via_A : Nat := min 1000 (demA * 1000 / 1000 * need vH / 1000)

theorem demH_via_B_value : demH_via_B = 1000 := by decide
theorem demH_via_A_value : demH_via_A = 0 := by decide

/-! ## §5: Max-aggregation at H — THE KEY SECTION

H receives demand from two paths. Per Ben's §4.1, demand aggregates by max
(not sum) because the paths share the same latent variable. Sum would
double-count the demand for H's information. -/

def demH : Nat := max demH_via_B demH_via_A

-- Chain path completely dominates: observed A contributes no demand to H
theorem chain_demand_dominates_fork : demH_via_B > demH_via_A := by decide

-- Max aggregation = chain path demand (fork path adds nothing)
theorem max_aggregation_at_H : demH = demH_via_B := by decide

-- The full demand ordering across all nodes
theorem demand_ordering :
    demH ≥ demB ∧ demB ≥ demC ∧ demC > demCtoD ∧
    demCtoD > demBtoC ∧ demH > demA := by decide

-- Hidden cause H and unknown intermediates B, C all have maximum demand
-- Rules and observed facts have lower demand
theorem hidden_and_unknown_max :
    demH = 1000 ∧ demB = 1000 ∧ demC = 1000 := by decide

/-! ## §6: Demand contraction after supply

Forward supply computes B from H (via fork), then C from B, then D from C.
After supply, B's confidence increases → demand at H contracts. -/

-- After supply: B gets confidence from the fork contraction
-- P(B|A) = 8/13 ≈ 0.615, confidence from fork = c_H × c_HtoB ≈ varies
-- Use simplified: supply gives B confidence ≈ 600 (moderate from fork)
def cB_after_supply : Nat := 600
def need_B_after : Nat := 1000 - cB_after_supply  -- 400

def demB_after : Nat := min 1000 (demC * nsens_fBC_B / 1000 * need_B_after / 1000)
def demH_after : Nat := min 1000 (demB_after * 1000 / 1000 * need vH / 1000)

theorem demand_B_contracts : demB_after < demB := by decide
theorem demand_H_contracts : demH_after < demH := by decide
theorem demand_B_after_value : demB_after = 400 := by decide
theorem demand_H_after_value : demH_after = 400 := by decide

/-! ## §7: Forgetting observation A reopens the fork arm

If we forget A's observation, A becomes unknown. Now demand CAN flow
backward through A to H via the fork arm. H's demand potentially
increases because there's a NEW information gap at A.

This is the fork-specific version of the `forget` pattern from
EvidentialLedger — the same pattern that showed Wikipedia was
corroborative (Pain), IASP was critical (Pain), and uncalibrated
sources reopen intervals (AI outcomes). -/

-- After forgetting A: A becomes unknown (need = 1000)
def need_A_after_forget : Nat := 1000

-- Now A gets demand from the chain (backpropagated through the fork)
-- A is now an unknown that the system should investigate
-- Demand at A (which was 0 when observed) is now significant
def demA_after_forget : Nat :=
  -- A participates in the fork: if H is known, A can be predicted
  -- But H is also unknown → demand at A = need(A) (simplified)
  need_A_after_forget

-- Forgetting the observation REOPENS demand
theorem forget_A_reopens_demand : demA_after_forget > demA := by decide

-- After forgetting A, the fork arm becomes active
-- H now has demand from BOTH paths
def demH_via_A_after_forget : Nat :=
  min 1000 (demA_after_forget * 1000 / 1000 * need vH / 1000)

-- The fork arm now contributes demand to H (was 0 before)
theorem fork_arm_activates : demH_via_A_after_forget > demH_via_A := by decide

-- Both paths now contribute equally to H's demand
theorem fork_balanced_after_forget :
    demH_via_A_after_forget = demH_via_B := by decide

/-! ## §8: End-to-end summary -/

theorem end_to_end :
    -- Demand ordering: hidden/unknown nodes get maximum demand
    demH = 1000 ∧ demB = 1000 ∧ demC = 1000 ∧
    -- Chain path dominates fork path (A observed → no fork demand)
    demH_via_B > demH_via_A ∧
    -- Max aggregation
    demH = max demH_via_B demH_via_A ∧
    -- Supply contracts demand
    demB_after < demB ∧ demH_after < demH ∧
    -- Forgetting reopens the fork arm
    demA_after_forget > demA ∧
    -- After forgetting: both fork arms contribute equally
    demH_via_A_after_forget = demH_via_B := by decide

end Mettapedia.Logic.WMForkDemandDemo
