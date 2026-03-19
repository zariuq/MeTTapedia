/-!
# Demand-Driven Backward Activation Demo: Mammal(Lassie)

Kernel-checked worked example from Goertzel, "PLN Backward-Chaining in MORK
via Factor Graphs" (March 2026), §6.1. Demonstrates that backward demand
propagation directs inference resources to the most uncertain, most sensitive
premises — on the same factor graph used for forward belief propagation.

## The Example

Chain: Collie(Lassie) → Dog(Lassie) → Mammal(Lassie)
Query: Mammal(Lassie) with demand = 1.

Dog(Lassie) is UNKNOWN (confidence 0). The demand computation identifies it
as the highest-priority premise: it has maximum information need (1 - c = 1)
AND high sensitivity to the query.

## What This Demonstrates for WM-PLN

1. **Demand as a quantale** — `([0,1], ≤, ×, max)` parallels the evidence quantale
2. **Backward demand = targeted sensitivity analysis** — like `forget` but precise
3. **Forward supply uses the same algebra** — heuristic modus ponens on STVs
4. **Data-backed states matter** — the DTV (§5.7) preserves distribution shape
   that the STV compresses away; demand sensitivity depends on this shape

## Encoding

All values × 1000 as Nat for kernel-checkable arithmetic.
E.g., strength 0.95 → 950, confidence 0.80 → 800.

## Reference

Goertzel, "PLN Backward-Chaining in MORK via Factor Graphs", §6.1, Eq. (49-65).
File: literature/Probabilistic_Logic/Goertzel_2026_PLN_Backward_Chaining_Factor_Graphs_MORK.pdf

0 sorry.
-/

namespace Mettapedia.Logic.WMDemandDemo

/-! ## §1: Simple Truth Values (× 1000 encoding) -/

structure STV1k where
  s : Nat  -- strength × 1000
  c : Nat  -- confidence × 1000
  deriving DecidableEq, BEq, Repr

/-! ## §2: The factor graph nodes

From Ben's §6.1, Eq. (49-53): -/

def vA     : STV1k := ⟨950, 950⟩   -- Collie(Lassie): (0.95, 0.95)
def vAtoB  : STV1k := ⟨990, 800⟩   -- Collie(x) → Dog(x): (0.99, 0.80)
def vB     : STV1k := ⟨500, 0⟩     -- Dog(Lassie): (0.5, 0) UNKNOWN
def vBtoC  : STV1k := ⟨950, 600⟩   -- Dog(x) → Mammal(x): (0.95, 0.60)
def vC     : STV1k := ⟨500, 0⟩     -- Mammal(Lassie): (0.5, 0) QUERY TARGET

/-! ## §3: Forward supply (zero-default heuristic modus ponens)

φ(s_A, s_AB) = s_A × s_AB  (with π_B = 0)
c_out = c_A × c_AB

Eq. (64-65): s_B = 0.95 × 0.99 = 0.9405, c_B = 0.95 × 0.80 = 0.76
             s_C = 0.9405 × 0.95 = 0.8935, c_C = 0.76 × 0.60 = 0.456 -/

-- Forward at factor f₁: A, A→B ⊢ B
def sB_fwd : Nat := vA.s * vAtoB.s / 1000    -- 950 × 990 / 1000 = 940
def cB_fwd : Nat := vA.c * vAtoB.c / 1000    -- 950 × 800 / 1000 = 760

-- Forward at factor f₂: B, B→C ⊢ C
def sC_fwd : Nat := sB_fwd * vBtoC.s / 1000  -- 940 × 950 / 1000 = 893
def cC_fwd : Nat := cB_fwd * vBtoC.c / 1000  -- 760 × 600 / 1000 = 456

theorem forward_sB : sB_fwd = 940 := by decide
theorem forward_cB : cB_fwd = 760 := by decide
theorem forward_sC : sC_fwd = 893 := by decide
theorem forward_cC : cC_fwd = 456 := by decide

/-! ## §4: Information need

need(α) = 1 - c.  Higher need = more uncertain = more worth investigating.
Eq. (1): demand is modulated by information need. -/

def need (tv : STV1k) : Nat := 1000 - tv.c

theorem need_A : need vA = 50 := by decide          -- well-known: low need
theorem need_AtoB : need vAtoB = 200 := by decide    -- moderately known
theorem need_B : need vB = 1000 := by decide          -- UNKNOWN: maximum need
theorem need_BtoC : need vBtoC = 400 := by decide     -- somewhat known

/-! ## §5: Sensitivity (Jacobian of forward truth-value map)

For zero-default modus ponens φ(s_A, s_AB) = s_A × s_AB:
  ∂s_out/∂s_A = s_AB,  ∂s_out/∂s_AB = s_A

Block sensitivity (Eq. 4-5):
  sens_f(A) = max(|s_AB - π_B|, c_AB) = max(s_AB, c_AB) when π_B = 0
  sens_f(A→B) = max(s_A, c_A)

Normalized: s̃ens = sens / max_j(sens_j) -/

-- At factor f₂: conclusion = C, premises = B and B→C
-- sens(B) = max(s_{B→C}, c_{B→C}) = max(950, 600) = 950
-- sens(B→C) = max(s_B, c_B) — but B is unknown at demand time, use current STV
--           = max(500, 0) = 500
def sens_f2_B : Nat := max vBtoC.s vBtoC.c      -- 950
def sens_f2_BtoC : Nat := max vB.s vB.c          -- 500
def S_f2 : Nat := max sens_f2_B sens_f2_BtoC     -- 950

-- Normalized sensitivities
def nsens_f2_B : Nat := sens_f2_B * 1000 / S_f2        -- 950/950 × 1000 = 1000
def nsens_f2_BtoC : Nat := sens_f2_BtoC * 1000 / S_f2  -- 500/950 × 1000 = 526

theorem sensitivity_B_dominates : sens_f2_B > sens_f2_BtoC := by decide
theorem nsens_B : nsens_f2_B = 1000 := by decide
theorem nsens_BtoC : nsens_f2_BtoC = 526 := by decide

/-! ## §6: Backward demand computation

Demand adjoint (Eq. 1):
  Ψ_f(d_v; α_{1:k})_i = clip(d_v × s̃ens(i) × need(α_i))

With dem(v_C) = 1000 (= 1.0):
  dem(B) = dem(C) × nsens_f2(B) × need(B) / 1000000
         = 1000 × 1000 × 1000 / 1000000 = 1000
  dem(B→C) = dem(C) × nsens_f2(B→C) × need(B→C) / 1000000
           = 1000 × 526 × 400 / 1000000 = 210 -/

def demC : Nat := 1000  -- query demand = 1.0

-- Demand at factor f₂ premises
def demB : Nat := min 1000 (demC * nsens_f2_B / 1000 * need vB / 1000)
def demBtoC : Nat := min 1000 (demC * nsens_f2_BtoC / 1000 * need vBtoC / 1000)

theorem demand_B : demB = 1000 := by decide
theorem demand_BtoC : demBtoC = 210 := by decide

-- THE KEY RESULT: Dog(Lassie) gets maximum demand because it is
-- both maximally uncertain (need = 1.0) AND maximally sensitive (nsens = 1.0)
theorem unknown_gets_highest_demand : demB > demBtoC := by decide

/-! ## §7: Demand at factor f₁ (continuing backward)

At f₁: conclusion = B, premises = A and A→B
  sens(A) = max(s_{A→B}, c_{A→B}) = max(990, 800) = 990
  sens(A→B) = max(s_A, c_A) = max(950, 950) = 950

With dem(B) = 1000 from above. -/

def sens_f1_A : Nat := max vAtoB.s vAtoB.c      -- 990
def sens_f1_AtoB : Nat := max vA.s vA.c          -- 950
def S_f1 : Nat := max sens_f1_A sens_f1_AtoB     -- 990

def nsens_f1_A : Nat := sens_f1_A * 1000 / S_f1        -- 1000
def nsens_f1_AtoB : Nat := sens_f1_AtoB * 1000 / S_f1  -- 959

def demA : Nat := min 1000 (demB * nsens_f1_A / 1000 * need vA / 1000)
def demAtoB : Nat := min 1000 (demB * nsens_f1_AtoB / 1000 * need vAtoB / 1000)

-- Demand drops sharply at well-known premises
theorem demand_A : demA = 50 := by decide
theorem demand_AtoB : demAtoB = 191 := by decide

-- The expansion threshold (say τ = 200) would halt backward search at A
-- but keep the boundary edge active for forward supply
theorem A_below_threshold : demA < 200 := by decide
theorem AtoB_below_threshold : demAtoB < 200 := by decide

/-! ## §8: Demand ordering — the full picture

Dog(Lassie) → B→C rule → A→B rule → Collie(Lassie)
1000          210         191         50

Demand correctly identifies the inference bottleneck:
the unknown intermediate fact Dog(Lassie). -/

theorem demand_ordering :
    demB > demBtoC ∧ demBtoC > demAtoB ∧ demAtoB > demA := by decide

/-! ## §9: Demand contraction after forward supply

After forward supply computes Dog(Lassie) = (940, 760), recompute demand.
Dog's need drops from 1.0 to 0.24. Demand CONTRACTS — this is Ben's
Proposition 2 (contraction on trees): each backward-then-forward cycle
reduces demand by the confidence gain.

This closes the loop: demand → activate → supply → demand drops. -/

-- After supply, Dog(Lassie) is no longer unknown
def vB_supplied : STV1k := ⟨sB_fwd, cB_fwd⟩

-- Updated information need: Dog is now well-supported
def need_B_after : Nat := 1000 - cB_fwd  -- 1000 - 760 = 240

-- Recomputed demand at B with updated need
def demB_after : Nat := min 1000 (demC * nsens_f2_B / 1000 * need_B_after / 1000)

theorem need_B_drops : need_B_after = 240 := by decide
theorem demand_B_after : demB_after = 240 := by decide

-- KEY: Demand contracts after supply (from 1000 to 240)
theorem demand_contracts_after_supply : demB_after < demB := by decide

-- The contraction is proportional to the confidence gain
theorem contraction_is_confidence_gain :
    demB - demB_after = need vB - need_B_after := by decide

/-! ## §10: Provenance-aware forgetting reopens demand

The answer Mammal(Lassie) depends on 4 inputs. Forgetting one observation
(Collie(Lassie)) makes that premise unknown again, REOPENING demand there.

This is the same `forget` pattern that showed:
- Wikipedia was corroborative (Pain reclassification)
- IASP was critical (Pain reclassification)
- Uncalibrated sources reopen intervals (AI outcomes)
- PairAffinity is the gate (UWCSE)

Here it shows: forgetting an observation reopens demand at the affected
premise — the demand system correctly detects the new information gap. -/

-- Forget Collie(Lassie): premise A becomes unknown again
def need_A_after_forget : Nat := 1000  -- confidence drops to 0

-- Demand at A with the forgotten observation
def demA_after_forget : Nat :=
  min 1000 (demB * nsens_f1_A / 1000 * need_A_after_forget / 1000)

-- Forgetting REOPENS demand (from 50 to 1000)
theorem forgetting_reopens_demand : demA_after_forget > demA := by decide

-- The reopened demand correctly identifies the new bottleneck
theorem forget_collie_shifts_bottleneck :
    demA_after_forget = 1000 := by decide

-- After forgetting Collie(Lassie), demand at A matches demand at B
-- (both are unknown with maximum need)
theorem forget_equalizes_demand :
    demA_after_forget = demB := by decide

/-! ## §11: End-to-end summary -/

theorem end_to_end :
    -- Forward supply produces correct marginals
    sB_fwd = 940 ∧ cB_fwd = 760 ∧ sC_fwd = 893 ∧ cC_fwd = 456 ∧
    -- Unknown intermediate gets maximum demand
    demB = 1000 ∧
    -- Demand ordering matches inference bottleneck
    demB > demBtoC ∧ demBtoC > demAtoB ∧ demAtoB > demA ∧
    -- Demand contracts after supply (Proposition 2)
    demB_after < demB ∧
    -- Forgetting reopens demand
    demA_after_forget > demA ∧
    -- Forgetting equalizes with the original bottleneck
    demA_after_forget = demB := by decide

end Mettapedia.Logic.WMDemandDemo
