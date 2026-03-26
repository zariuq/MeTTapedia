import Mettapedia.Logic.MarkovLogicIndividuation
import Mettapedia.Logic.MarkovLogicInfiniteVariableNeighborhoodWorldOfViews

/-!
# Capstone: The Trust Triangle — Ontology Extension Made Concrete

A tight-knit community of three agents {0, 1, 2} forms a **trust triangle**:
each pair is connected by a mutual trust clause.  An infinite chain of
agents {3, 4, 5, ...} operates independently — no clause connects the
triangle to the chain.

Two specifications share the triangle's clauses but differ on the chain's
weights.  The capstone theorem proves: the WM truth value of "does agent 1
believe?" is **exactly the same** under both specs.

This is individuation made concrete.  The trust triangle's internal beliefs
are robust to arbitrarily large changes in the surrounding social network,
as long as no new clause penetrates the triangle's interaction boundary.

**Sociopolitical reading.**  A resilient community core — three people who
trust each other deeply — maintains its shared understanding regardless of
how the wider society evolves.  The formalization makes the boundary
condition precise: it is not metaphorical robustness but exact mathematical
invariance.

**What formalization caught.**  The earlier attempt used the belief line,
where no finite region is interaction-closed (every boundary agent has an
exterior neighbor).  The trust triangle works because the triangle is a
**disconnected component** in the interaction graph — a genuinely autonomous
community.
-/

namespace Mettapedia.Logic.MarkovLogicTrustTriangleExample

open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFiniteVolume
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicOntologyGrowth
open Mettapedia.Logic.MarkovLogicIndividuation
open Mettapedia.Logic.MarkovLogicInfiniteVariableNeighborhoodWorldOfViews
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicAbstract.MassState
open MeasureTheory

-- ═══════════════════════════════════════════════════════════════════════════
-- The interaction graph: triangle {0,1,2} + chain {3,4,5,...}
-- ═══════════════════════════════════════════════════════════════════════════

/-- Neighborhood function for the trust triangle + chain topology.
    - Atoms 0, 1, 2: mutual triangle (each connected to the other two).
    - Atom 3: start of chain (connected to 4 only).
    - Atoms n ≥ 4: chain (connected to n-1 and n+1). -/
def triangleChainNbrs : Nat → Finset Nat
  | 0 => {1, 2}
  | 1 => {0, 2}
  | 2 => {0, 1}
  | 3 => {4}
  | (n + 4) => {n + 3, n + 5}

/-- The neighborhood is symmetric: b ∈ nbrs(a) ↔ a ∈ nbrs(b). -/
theorem triangleChainNbrs_symm : ∀ a b, b ∈ triangleChainNbrs a ↔ a ∈ triangleChainNbrs b := by
  intro a b
  -- Strategy: case split on whether a, b are in {0,1,2} or ≥ 3.
  -- Triangle-triangle: handled by simp on all 9 pairs.
  -- Triangle-chain or chain-triangle: both sides are False (no cross edges).
  -- Chain-chain: handled by omega on the {n+3, n+5} structure.
  match a, b with
  | 0, 0 | 0, 1 | 0, 2 | 1, 0 | 1, 1 | 1, 2 | 2, 0 | 2, 1 | 2, 2 =>
      simp [triangleChainNbrs]
  | 0, 3 | 1, 3 | 2, 3 | 3, 0 | 3, 1 | 3, 2 =>
      simp [triangleChainNbrs]
  | 0, (n + 4) => simp [triangleChainNbrs]
  | 1, (n + 4) => simp [triangleChainNbrs]
  | 2, (n + 4) => simp [triangleChainNbrs]
  | (n + 4), 0 => simp [triangleChainNbrs]
  | (n + 4), 1 => simp [triangleChainNbrs]
  | (n + 4), 2 => simp [triangleChainNbrs]
  | 3, 3 => simp [triangleChainNbrs]
  | 3, (n + 4) => simp [triangleChainNbrs]
  | (n + 4), 3 => simp [triangleChainNbrs]
  | (n + 4), (m + 4) =>
      simp [triangleChainNbrs]
      constructor
      · intro h; rcases h with rfl | rfl <;> omega
      · intro h; rcases h with rfl | rfl <;> omega

-- ═══════════════════════════════════════════════════════════════════════════
-- Two specifications: same triangle, different chain weights
-- ═══════════════════════════════════════════════════════════════════════════

/-- Trust weight function: `wt` for triangle edges, `wc` for chain edges,
    0 for non-edges (the gating in varNClauseGated handles this). -/
def triangleChainTrust (wt wc : ℝ) : Nat → Nat → ℝ :=
  fun a b =>
    if a ≤ 2 ∧ b ≤ 2 then wt      -- triangle edge
    else if a ≥ 3 ∧ b ≥ 3 then wc  -- chain edge
    else 0                           -- cross-component (never used — gated out)

/-- Prior weight: uniform across all agents. -/
def uniformPrior (_a : Nat) : ℝ := 0.5

/-- Specification with triangle weight `wt` and chain weight `wc`. -/
noncomputable abbrev triangleChainSpec (wt wc : ℝ) :=
  varNeighborhoodSpec triangleChainNbrs triangleChainNbrs
    triangleChainNbrs_symm (triangleChainTrust wt wc) uniformPrior

-- ═══════════════════════════════════════════════════════════════════════════
-- The core region and query
-- ═══════════════════════════════════════════════════════════════════════════

/-- The trust triangle: agents {0, 1, 2}. -/
def coreTriangle : Region Nat := {0, 1, 2}

/-- The query: "does agent 1 believe?" -/
def agent1Query : ConstraintQuery Nat := [⟨1, true⟩]

theorem agent1Query_supported :
    ∀ p ∈ agent1Query, (p : Sigma fun _ : Nat => Bool).1 ∈ coreTriangle := by
  intro p hp; simp [agent1Query] at hp; subst hp; simp [coreTriangle]

-- ═══════════════════════════════════════════════════════════════════════════
-- Interaction closure: the triangle's neighbors are all in the triangle
-- ═══════════════════════════════════════════════════════════════════════════

/-- The trust triangle is interaction-closed: every atom in {0,1,2} has
    all its neighbors also in {0,1,2}.  This is the formal individuation
    condition — the triangle is a genuinely autonomous community. -/
theorem triangleCore_interactionClosed (wt wc : ℝ) :
    InteractionClosed (triangleChainSpec wt wc) coreTriangle := by
  intro a ha
  simp only [coreTriangle, Finset.mem_insert, Finset.mem_singleton] at ha
  intro b hb
  simp only [coreTriangle, Finset.mem_insert, Finset.mem_singleton]
  -- atomInteractionNeighborhood = (regionSupport {a}).biUnion (clause.atoms.erase a)
  -- For varNeighborhoodSpec, regionSupport {a} contains priors + influence clauses
  -- touching a. For a ∈ {0,1,2}, only triangle clauses touch a.
  -- The atoms of those clauses (minus a) are in {0,1,2}.
  unfold atomInteractionNeighborhood at hb
  simp only [triangleChainSpec, varNeighborhoodSpec, varNRegionSupport,
    triangleChainNbrs, Finset.mem_biUnion, Finset.mem_image,
    Finset.singleton_biUnion, Finset.mem_union] at hb
  -- For each atom a ∈ {0,1,2}: unfold everything and let simp + omega close it.
  rcases ha with rfl | rfl | rfl <;> {
    simp only [atomInteractionNeighborhood, triangleChainSpec, varNeighborhoodSpec,
      varNRegionSupport, triangleChainNbrs, varNClauseGated,
      varNInfluenceClause, varNPriorClause, GroundClause.atoms, Literal.atom,
      Finset.mem_biUnion, Finset.mem_union, Finset.mem_image, Finset.mem_insert,
      Finset.mem_singleton, Finset.singleton_biUnion, Finset.mem_erase,
      Finset.image_insert, Finset.image_singleton, Finset.image_empty,
      Finset.biUnion_insert, Finset.biUnion_singleton, Finset.biUnion_empty,
      Finset.empty_union, Finset.union_empty,
      coreTriangle] at hb ⊢
    aesop
  }

-- ═══════════════════════════════════════════════════════════════════════════
-- Specs agree on the triangle core
-- ═══════════════════════════════════════════════════════════════════════════

/-- Two triangle-chain specs with the same triangle weight agree on the
    triangle core, regardless of their chain weights. -/
private theorem specs_agree_regionSupport (wt wc₁ wc₂ : ℝ)
    (Λ : Region Nat) (_ : Λ ⊆ coreTriangle) (_ : Λ.Nonempty) :
    (triangleChainSpec wt wc₁).regionSupport Λ =
    (triangleChainSpec wt wc₂).regionSupport Λ := by
  show varNRegionSupport triangleChainNbrs triangleChainNbrs Λ =
    varNRegionSupport triangleChainNbrs triangleChainNbrs Λ
  rfl

private theorem specs_agree_clause (wt wc₁ wc₂ : ℝ)
    (j : VarNClauseId) (_ : j ∈ (triangleChainSpec wt wc₁).regionSupport coreTriangle) :
    (triangleChainSpec wt wc₁).clause j =
    (triangleChainSpec wt wc₂).clause j := by
  show varNClauseGated triangleChainNbrs j = varNClauseGated triangleChainNbrs j
  rfl

private theorem trust_agree_on_triangle_atoms (wt wc₁ wc₂ : ℝ) (a b : Nat)
    (ha : a ≤ 2) (hb : b ≤ 2) :
    triangleChainTrust wt wc₁ a b = triangleChainTrust wt wc₂ a b := by
  simp [triangleChainTrust, ha, hb]

private theorem triangle_support_influence_atoms_le_two
    (wt wc : ℝ) {a b : Nat}
    (hj : VarNClauseId.influence a b ∈ (triangleChainSpec wt wc).regionSupport coreTriangle) :
    a ≤ 2 ∧ b ≤ 2 := by
  simp [triangleChainSpec, varNeighborhoodSpec, varNRegionSupport,
    triangleChainNbrs, coreTriangle] at hj
  omega

private theorem specs_agree_logWeight (wt wc₁ wc₂ : ℝ)
    (j : VarNClauseId)
    (hj : j ∈ (triangleChainSpec wt wc₁).regionSupport coreTriangle) :
    (triangleChainSpec wt wc₁).logWeight j =
    (triangleChainSpec wt wc₂).logWeight j := by
  cases j with
  | prior n =>
      rfl
  | influence a b =>
      rcases triangle_support_influence_atoms_le_two wt wc₁ hj with ⟨ha, hb⟩
      exact trust_agree_on_triangle_atoms wt wc₁ wc₂ a b ha hb

set_option maxHeartbeats 800000 in
theorem specs_agree_on_triangle (wt wc₁ wc₂ : ℝ) :
    SpecAgreesOnRegion (triangleChainSpec wt wc₁) (triangleChainSpec wt wc₂) coreTriangle :=
  ⟨specs_agree_regionSupport wt wc₁ wc₂,
   specs_agree_clause wt wc₁ wc₂,
   specs_agree_logWeight wt wc₁ wc₂⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- Dobrushin budget
-- ═══════════════════════════════════════════════════════════════════════════

/-- The Dobrushin budget for the triangle-chain spec holds when the
    triangle weight and chain weight are both small enough. -/
theorem triangleChainSpec_budget (wt wc : ℝ)
    (hwt : |wt| < 1 / 2) (hwc : |wc| < 1 / 2) :
    (triangleChainSpec wt wc).PaperUniformSmallTotalInfluence := by
  refine varNeighborhoodSpec_uniformSmallTotalInfluence
    (nbrs := triangleChainNbrs)
    (reverseNbrs := triangleChainNbrs)
    (hrev := triangleChainNbrs_symm)
    (tw := triangleChainTrust wt wc)
    (pw := uniformPrior) ?_
  refine ⟨2 * max |wt| |wc|, by positivity, ?_, ?_⟩
  · have hmax : max |wt| |wc| < 1 / 2 := max_lt hwt hwc
    nlinarith
  · intro a
    cases a with
    | zero =>
        have hrow0 :
            (triangleChainNbrs 0).sum
                (fun b => (1 / 2 : ℝ) * |triangleChainTrust wt wc 0 b|) +
              (triangleChainNbrs 0).sum
                (fun c => (1 / 2 : ℝ) * |triangleChainTrust wt wc c 0|) =
              2 * |wt| := by
          norm_num [triangleChainNbrs, triangleChainTrust]
          ring
        rw [hrow0]
        have hmaxwt : |wt| ≤ max |wt| |wc| := le_max_left _ _
        nlinarith [abs_nonneg wt, hmaxwt]
    | succ a =>
        cases a with
        | zero =>
            have hrow1 :
                (triangleChainNbrs 1).sum
                    (fun b => (1 / 2 : ℝ) * |triangleChainTrust wt wc 1 b|) +
                  (triangleChainNbrs 1).sum
                    (fun c => (1 / 2 : ℝ) * |triangleChainTrust wt wc c 1|) =
                  2 * |wt| := by
              norm_num [triangleChainNbrs, triangleChainTrust]
              ring
            rw [hrow1]
            have hmaxwt : |wt| ≤ max |wt| |wc| := le_max_left _ _
            nlinarith [abs_nonneg wt, hmaxwt]
        | succ a =>
            cases a with
            | zero =>
                have hrow2 :
                    (triangleChainNbrs 2).sum
                        (fun b => (1 / 2 : ℝ) * |triangleChainTrust wt wc 2 b|) +
                      (triangleChainNbrs 2).sum
                        (fun c => (1 / 2 : ℝ) * |triangleChainTrust wt wc c 2|) =
                      2 * |wt| := by
                  norm_num [triangleChainNbrs, triangleChainTrust]
                  ring
                rw [hrow2]
                have hmaxwt : |wt| ≤ max |wt| |wc| := le_max_left _ _
                nlinarith [abs_nonneg wt, hmaxwt]
            | succ n =>
                cases n with
                | zero =>
                    have hrow3 :
                        (triangleChainNbrs 3).sum
                            (fun b => (1 / 2 : ℝ) * |triangleChainTrust wt wc 3 b|) +
                          (triangleChainNbrs 3).sum
                            (fun c => (1 / 2 : ℝ) * |triangleChainTrust wt wc c 3|) =
                          |wc| := by
                      norm_num [triangleChainNbrs, triangleChainTrust]
                      ring
                    rw [hrow3]
                    have hmaxwc : |wc| ≤ max |wt| |wc| := le_max_right _ _
                    nlinarith [abs_nonneg wc, hmaxwc]
                | succ n =>
                    have hneq : n + 4 ≠ n + 6 := by omega
                    have hrowChain :
                        (triangleChainNbrs (n + 4)).sum
                            (fun b => (1 / 2 : ℝ) * |triangleChainTrust wt wc (n + 4) b|) +
                          (triangleChainNbrs (n + 4)).sum
                            (fun c => (1 / 2 : ℝ) * |triangleChainTrust wt wc c (n + 4)|) =
                          2 * |wc| := by
                      have hnot_le : ¬ n + 4 ≤ 2 := by omega
                      have hge4 : n + 4 ≥ 3 := by omega
                      have hge3 : n + 3 ≥ 3 := by omega
                      have hge5 : n + 5 ≥ 3 := by omega
                      simp [triangleChainNbrs, triangleChainTrust, hnot_le, hge4, hge3, hge5]
                      ring
                    rw [hrowChain]
                    have hmaxwc : |wc| ≤ max |wt| |wc| := le_max_right _ _
                    nlinarith [abs_nonneg wc, hmaxwc]

-- ═══════════════════════════════════════════════════════════════════════════
-- THE CAPSTONE: WM truth value stable under ontology extension
-- ═══════════════════════════════════════════════════════════════════════════

/-- **THE CAPSTONE THEOREM**: the WM truth value of "does agent 1 believe?"
    is exactly the same under two specifications that share the trust
    triangle but differ on the infinite chain.

    This composes the FULL pipeline:
    - Existence (DLR measures exist for both specs)
    - Dobrushin budget (both specs satisfy the contraction condition)
    - Uniqueness (each spec has exactly one DLR measure)
    - WM bridge (queryStrength = μ(q))
    - Ontology invariance (specs agree on the triangle → same answer)

    Sociopolitical reading: the trust triangle's internal beliefs are
    exactly robust to changes in the surrounding social network. -/
theorem trust_triangle_wmStrength_stable
    (wt wc₁ wc₂ : ℝ)
    (hwt : |wt| < 1 / 2) (hwc₁ : |wc₁| < 1 / 2) (hwc₂ : |wc₂| < 1 / 2)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Nat))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Nat))
    (hμ₁ : FixedRegionCylinderDLR
      (triangleChainSpec wt wc₁).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Nat)))
    (hμ₂ : FixedRegionCylinderDLR
      (triangleChainSpec wt wc₂).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Nat))) :
    BinaryWorldModel.queryStrength
      ({infiniteMLNMassSemantics (triangleChainSpec wt wc₁) μ₁ hμ₁} :
        MassState (ConstraintQuery Nat)) agent1Query =
    BinaryWorldModel.queryStrength
      ({infiniteMLNMassSemantics (triangleChainSpec wt wc₂) μ₂ hμ₂} :
        MassState (ConstraintQuery Nat)) agent1Query := by
  -- Compose the full chain:
  -- 1. Construct the individuated subsystem (triangle is interaction-closed)
  -- 2. Apply wmStrength_stable_under_extension (specs agree on core)
  simp only [queryStrength_singleton_eq_queryProb]
  exact queryProb_eq_of_specAgreesOnRegion
    (specs_agree_on_triangle wt wc₁ wc₂)
    (triangleCore_interactionClosed wt wc₁)
    (triangleCore_interactionClosed wt wc₂)
    (triangleChainSpec_budget wt wc₁ hwt hwc₁)
    (triangleChainSpec_budget wt wc₂ hwt hwc₂)
    μ₁ μ₂ hμ₁ hμ₂ agent1Query agent1Query_supported

end Mettapedia.Logic.MarkovLogicTrustTriangleExample
