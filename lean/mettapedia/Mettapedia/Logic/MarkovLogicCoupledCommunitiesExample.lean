import Mettapedia.Logic.MarkovLogicCoupledSubsystems
import Mettapedia.Logic.MarkovLogicInfiniteVariableNeighborhoodWorldOfViews

/-!
# Worked Example: Two Communities Sharing a Protected Carrier

This example instantiates `MarkovLogicCoupledSubsystems` with a concrete
social topology:

- left community: agents `{0,1}`,
- interface: agent `{2}`,
- right community: agents `{3,4}`,
- external tail: agents `{5,6,7,\ldots}`.

The protected carrier is `{0,1,2,3,4}`.  The tail is disconnected from the
carrier, so changing tail weights does not affect left-local, right-local, or
joint carrier queries.

**Positive example.**  Two communities can interact through a liaison layer
inside one protected carrier while remaining exactly stable under distant
changes outside the carrier.

**Negative example.**  If the tail were attached directly to agent `4`, the
carrier would no longer be interaction-closed and the exact theorem would
fail.
-/

namespace Mettapedia.Logic.MarkovLogicCoupledCommunitiesExample

open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFiniteVolume
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicOntologyGrowth
open Mettapedia.Logic.MarkovLogicCoupledSubsystems
open Mettapedia.Logic.MarkovLogicInfiniteVariableNeighborhoodWorldOfViews
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicAbstract.MassState
open MeasureTheory

/-- Neighborhood function for the coupled-communities example. -/
def coupledCommunitiesNbrs : Nat → Finset Nat
  | 0 => {1, 2}
  | 1 => {0, 2}
  | 2 => {0, 1, 3, 4}
  | 3 => {2, 4}
  | 4 => {2, 3}
  | 5 => {6}
  | (n + 6) => {n + 5, n + 7}

/-- The neighborhood relation is symmetric. -/
theorem coupledCommunitiesNbrs_symm :
    ∀ a b, b ∈ coupledCommunitiesNbrs a ↔ a ∈ coupledCommunitiesNbrs b := by
  intro a b
  match a, b with
  | 0, 0 | 0, 1 | 0, 2 | 1, 0 | 1, 1 | 1, 2 | 2, 0 | 2, 1 | 2, 2
  | 2, 3 | 2, 4 | 3, 2 | 3, 3 | 3, 4 | 4, 2 | 4, 3 | 4, 4 =>
      simp [coupledCommunitiesNbrs]
  | 0, 3 | 0, 4 | 1, 3 | 1, 4 | 3, 0 | 3, 1 | 4, 0 | 4, 1 =>
      simp [coupledCommunitiesNbrs]
  | 0, 5 | 1, 5 | 2, 5 | 3, 5 | 4, 5 | 5, 0 | 5, 1 | 5, 2 | 5, 3 | 5, 4 =>
      simp [coupledCommunitiesNbrs]
  | 0, (n + 6) | 1, (n + 6) | 2, (n + 6) | 3, (n + 6) | 4, (n + 6) =>
      simp [coupledCommunitiesNbrs]
  | (n + 6), 0 | (n + 6), 1 | (n + 6), 2 | (n + 6), 3 | (n + 6), 4 =>
      simp [coupledCommunitiesNbrs]
  | 5, 5 => simp [coupledCommunitiesNbrs]
  | 5, (n + 6) => simp [coupledCommunitiesNbrs]
  | (n + 6), 5 => simp [coupledCommunitiesNbrs]
  | (n + 6), (m + 6) =>
      simp [coupledCommunitiesNbrs]
      constructor
      · intro h
        rcases h with rfl | rfl <;> omega
      · intro h
        rcases h with rfl | rfl <;> omega

/-- Trust weight: `wc` inside the carrier, `wt` on the external tail. -/
def coupledCommunitiesTrust (wc wt : ℝ) : Nat → Nat → ℝ :=
  fun a b =>
    if a ≤ 4 ∧ b ≤ 4 then wc
    else if a ≥ 5 ∧ b ≥ 5 then wt
    else 0

/-- Uniform prior weight. -/
def coupledCommunitiesPrior (_a : Nat) : ℝ := 0.5

/-- The coupled-communities MLN specification. -/
noncomputable abbrev coupledCommunitiesSpec (wc wt : ℝ) :=
  varNeighborhoodSpec coupledCommunitiesNbrs coupledCommunitiesNbrs
    coupledCommunitiesNbrs_symm (coupledCommunitiesTrust wc wt) coupledCommunitiesPrior

/-- Protected carrier containing both communities and their interface. -/
def carrierRegion : Region Nat := {0, 1, 2, 3, 4}

/-- Left community core. -/
def leftCore : Region Nat := {0, 1}

/-- Right community core. -/
def rightCore : Region Nat := {3, 4}

/-- A left-local query. -/
def leftQuery : ConstraintQuery Nat := [⟨0, true⟩]

/-- A right-local query. -/
def rightQuery : ConstraintQuery Nat := [⟨3, true⟩]

/-- A joint query spanning both communities. -/
def jointQuery : ConstraintQuery Nat := [⟨0, true⟩, ⟨3, true⟩]

theorem leftQuery_supported :
    ∀ p ∈ leftQuery, (p : Sigma fun _ : Nat => Bool).1 ∈ leftCore := by
  intro p hp
  simp [leftQuery] at hp
  subst hp
  simp [leftCore]

theorem rightQuery_supported :
    ∀ p ∈ rightQuery, (p : Sigma fun _ : Nat => Bool).1 ∈ rightCore := by
  intro p hp
  simp [rightQuery] at hp
  subst hp
  simp [rightCore]

theorem jointQuery_supported :
    ∀ p ∈ jointQuery, (p : Sigma fun _ : Nat => Bool).1 ∈ leftCore ∪ rightCore := by
  intro p hp
  simp [jointQuery] at hp
  rcases hp with rfl | rfl
  · simp [leftCore, rightCore]
  · simp [leftCore, rightCore]

/-- The protected carrier is interaction-closed. -/
theorem carrierRegion_interactionClosed (wc wt : ℝ) :
    InteractionClosed (coupledCommunitiesSpec wc wt) carrierRegion := by
  intro a ha
  simp only [carrierRegion, Finset.mem_insert, Finset.mem_singleton] at ha
  intro b hb
  simp only [carrierRegion, Finset.mem_insert, Finset.mem_singleton]
  unfold atomInteractionNeighborhood at hb
  rcases ha with rfl | rfl | rfl | rfl | rfl <;>
    simp [coupledCommunitiesSpec, varNeighborhoodSpec, varNRegionSupport,
      coupledCommunitiesNbrs, varNClauseGated, varNInfluenceClause,
      varNPriorClause, GroundClause.atoms, Literal.atom] at hb ⊢ <;>
    aesop

/-- Coupled-subsystems package for the protected carrier example. -/
noncomputable def coupledCommunitiesSubsystem (wc wt : ℝ) :
    CoupledSubsystems (coupledCommunitiesSpec wc wt) where
  carrier :=
    { core := carrierRegion
      core_nonempty := ⟨0, by simp [carrierRegion]⟩
      interaction_closed := carrierRegion_interactionClosed wc wt }
  leftCore := leftCore
  rightCore := rightCore
  left_nonempty := ⟨0, by simp [leftCore]⟩
  right_nonempty := ⟨3, by simp [rightCore]⟩
  left_subset_carrier := by intro a ha; simp [leftCore, carrierRegion] at ha ⊢; omega
  right_subset_carrier := by intro a ha; simp [rightCore, carrierRegion] at ha ⊢; omega
  cores_disjoint := by
    refine Finset.disjoint_left.2 ?_
    intro a haLeft haRight
    simp [leftCore, rightCore] at haLeft haRight
    omega

private theorem specs_agree_regionSupport (wc wt₁ wt₂ : ℝ)
    (Λ : Region Nat) (_ : Λ ⊆ carrierRegion) (_ : Λ.Nonempty) :
    (coupledCommunitiesSpec wc wt₁).regionSupport Λ =
    (coupledCommunitiesSpec wc wt₂).regionSupport Λ := by
  show varNRegionSupport coupledCommunitiesNbrs coupledCommunitiesNbrs Λ =
    varNRegionSupport coupledCommunitiesNbrs coupledCommunitiesNbrs Λ
  rfl

private theorem specs_agree_clause (wc wt₁ wt₂ : ℝ)
    (j : VarNClauseId)
    (_ : j ∈ (coupledCommunitiesSpec wc wt₁).regionSupport carrierRegion) :
    (coupledCommunitiesSpec wc wt₁).clause j =
    (coupledCommunitiesSpec wc wt₂).clause j := by
  show varNClauseGated coupledCommunitiesNbrs j =
    varNClauseGated coupledCommunitiesNbrs j
  rfl

private theorem trust_agree_on_carrier_atoms (wc wt₁ wt₂ : ℝ) (a b : Nat)
    (ha : a ≤ 4) (hb : b ≤ 4) :
    coupledCommunitiesTrust wc wt₁ a b =
    coupledCommunitiesTrust wc wt₂ a b := by
  simp [coupledCommunitiesTrust, ha, hb]

private theorem carrier_support_influence_atoms_le_four
    (wc wt : ℝ) {a b : Nat}
    (hj : VarNClauseId.influence a b ∈ (coupledCommunitiesSpec wc wt).regionSupport carrierRegion) :
    a ≤ 4 ∧ b ≤ 4 := by
  simp [coupledCommunitiesSpec, varNeighborhoodSpec, varNRegionSupport,
    coupledCommunitiesNbrs, carrierRegion] at hj
  omega

private theorem specs_agree_logWeight (wc wt₁ wt₂ : ℝ)
    (j : VarNClauseId)
    (hj : j ∈ (coupledCommunitiesSpec wc wt₁).regionSupport carrierRegion) :
    (coupledCommunitiesSpec wc wt₁).logWeight j =
    (coupledCommunitiesSpec wc wt₂).logWeight j := by
  cases j with
  | prior n =>
      rfl
  | influence a b =>
      rcases carrier_support_influence_atoms_le_four wc wt₁ hj with ⟨ha, hb⟩
      exact trust_agree_on_carrier_atoms wc wt₁ wt₂ a b ha hb

theorem specs_agree_on_carrier (wc wt₁ wt₂ : ℝ) :
    SpecAgreesOnRegion (coupledCommunitiesSpec wc wt₁) (coupledCommunitiesSpec wc wt₂) carrierRegion :=
  ⟨specs_agree_regionSupport wc wt₁ wt₂,
   specs_agree_clause wc wt₁ wt₂,
   specs_agree_logWeight wc wt₁ wt₂⟩

/-- Uniform Dobrushin budget for the coupled communities example. -/
theorem coupledCommunitiesSpec_budget (wc wt : ℝ)
    (hwc : |wc| < 1 / 4) (hwt : |wt| < 1 / 2) :
    (coupledCommunitiesSpec wc wt).PaperUniformSmallTotalInfluence := by
  refine varNeighborhoodSpec_uniformSmallTotalInfluence
    (nbrs := coupledCommunitiesNbrs)
    (reverseNbrs := coupledCommunitiesNbrs)
    (hrev := coupledCommunitiesNbrs_symm)
    (tw := coupledCommunitiesTrust wc wt)
    (pw := coupledCommunitiesPrior) ?_
  refine ⟨max (4 * |wc|) (2 * |wt|), by positivity, ?_, ?_⟩
  · have hleft : 4 * |wc| < 1 := by nlinarith [hwc]
    have hright : 2 * |wt| < 1 := by nlinarith [hwt]
    exact max_lt_iff.mpr ⟨hleft, hright⟩
  · intro a
    cases a with
    | zero =>
        have hrow :
            (coupledCommunitiesNbrs 0).sum
                (fun b => (1 / 2 : ℝ) * |coupledCommunitiesTrust wc wt 0 b|) +
              (coupledCommunitiesNbrs 0).sum
                (fun c => (1 / 2 : ℝ) * |coupledCommunitiesTrust wc wt c 0|) =
              2 * |wc| := by
          norm_num [coupledCommunitiesNbrs, coupledCommunitiesTrust]
          ring
        rw [hrow]
        have hmax : 4 * |wc| ≤ max (4 * |wc|) (2 * |wt|) := le_max_left _ _
        nlinarith [abs_nonneg wc, hmax]
    | succ a =>
        cases a with
        | zero =>
            have hrow :
                (coupledCommunitiesNbrs 1).sum
                    (fun b => (1 / 2 : ℝ) * |coupledCommunitiesTrust wc wt 1 b|) +
                  (coupledCommunitiesNbrs 1).sum
                    (fun c => (1 / 2 : ℝ) * |coupledCommunitiesTrust wc wt c 1|) =
                  2 * |wc| := by
              norm_num [coupledCommunitiesNbrs, coupledCommunitiesTrust]
              ring
            rw [hrow]
            have hmax : 4 * |wc| ≤ max (4 * |wc|) (2 * |wt|) := le_max_left _ _
            nlinarith [abs_nonneg wc, hmax]
        | succ a =>
            cases a with
            | zero =>
                have hrow :
                    (coupledCommunitiesNbrs 2).sum
                        (fun b => (1 / 2 : ℝ) * |coupledCommunitiesTrust wc wt 2 b|) +
                      (coupledCommunitiesNbrs 2).sum
                        (fun c => (1 / 2 : ℝ) * |coupledCommunitiesTrust wc wt c 2|) =
                      4 * |wc| := by
                  norm_num [coupledCommunitiesNbrs, coupledCommunitiesTrust]
                  ring
                rw [hrow]
                exact le_max_left _ _
            | succ a =>
                cases a with
                | zero =>
                    have hrow :
                        (coupledCommunitiesNbrs 3).sum
                            (fun b => (1 / 2 : ℝ) * |coupledCommunitiesTrust wc wt 3 b|) +
                          (coupledCommunitiesNbrs 3).sum
                            (fun c => (1 / 2 : ℝ) * |coupledCommunitiesTrust wc wt c 3|) =
                          2 * |wc| := by
                      norm_num [coupledCommunitiesNbrs, coupledCommunitiesTrust]
                      ring
                    rw [hrow]
                    have hmax : 4 * |wc| ≤ max (4 * |wc|) (2 * |wt|) := le_max_left _ _
                    nlinarith [abs_nonneg wc, hmax]
                | succ a =>
                    cases a with
                    | zero =>
                        have hrow :
                            (coupledCommunitiesNbrs 4).sum
                                (fun b => (1 / 2 : ℝ) * |coupledCommunitiesTrust wc wt 4 b|) +
                              (coupledCommunitiesNbrs 4).sum
                                (fun c => (1 / 2 : ℝ) * |coupledCommunitiesTrust wc wt c 4|) =
                              2 * |wc| := by
                          norm_num [coupledCommunitiesNbrs, coupledCommunitiesTrust]
                          ring
                        rw [hrow]
                        have hmax : 4 * |wc| ≤ max (4 * |wc|) (2 * |wt|) := le_max_left _ _
                        nlinarith [abs_nonneg wc, hmax]
                    | succ n =>
                        cases n with
                        | zero =>
                            have hrow :
                                (coupledCommunitiesNbrs 5).sum
                                    (fun b => (1 / 2 : ℝ) * |coupledCommunitiesTrust wc wt 5 b|) +
                                  (coupledCommunitiesNbrs 5).sum
                                    (fun c => (1 / 2 : ℝ) * |coupledCommunitiesTrust wc wt c 5|) =
                                  |wt| := by
                              norm_num [coupledCommunitiesNbrs, coupledCommunitiesTrust]
                              ring
                            rw [hrow]
                            have hmax : 2 * |wt| ≤ max (4 * |wc|) (2 * |wt|) := le_max_right _ _
                            nlinarith [abs_nonneg wt, hmax]
                        | succ n =>
                            have hrow :
                                (coupledCommunitiesNbrs (n + 6)).sum
                                    (fun b => (1 / 2 : ℝ) * |coupledCommunitiesTrust wc wt (n + 6) b|) +
                                  (coupledCommunitiesNbrs (n + 6)).sum
                                    (fun c => (1 / 2 : ℝ) * |coupledCommunitiesTrust wc wt c (n + 6)|) =
                                  2 * |wt| := by
                              have hnot_le : ¬ n + 6 ≤ 4 := by omega
                              have hge5 : n + 6 ≥ 5 := by omega
                              have hgePrev : n + 5 ≥ 5 := by omega
                              have hgeNext : n + 7 ≥ 5 := by omega
                              simp [coupledCommunitiesNbrs, coupledCommunitiesTrust, hnot_le, hge5, hgePrev, hgeNext]
                              ring
                            rw [hrow]
                            have hmax : 2 * |wt| ≤ max (4 * |wc|) (2 * |wt|) := le_max_right _ _
                            exact hmax

/-- Exact carrier-level WM stability for a joint query spanning the two
communities. -/
theorem coupledCommunities_joint_wmStrength_stable
    (wc wt₁ wt₂ : ℝ)
    (hwc : |wc| < 1 / 4) (hwt₁ : |wt₁| < 1 / 2) (hwt₂ : |wt₂| < 1 / 2)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Nat))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Nat))
    (hμ₁ : FixedRegionCylinderDLR
      (coupledCommunitiesSpec wc wt₁).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Nat)))
    (hμ₂ : FixedRegionCylinderDLR
      (coupledCommunitiesSpec wc wt₂).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Nat))) :
    BinaryWorldModel.queryStrength
      ({infiniteMLNMassSemantics (coupledCommunitiesSpec wc wt₁) μ₁ hμ₁} :
        MassState (ConstraintQuery Nat)) jointQuery =
    BinaryWorldModel.queryStrength
      ({infiniteMLNMassSemantics (coupledCommunitiesSpec wc wt₂) μ₂ hμ₂} :
        MassState (ConstraintQuery Nat)) jointQuery := by
  exact (coupledCommunitiesSubsystem wc wt₁).coupled_wmStrength_stable_under_extension
    (specs_agree_on_carrier wc wt₁ wt₂)
    (coupledCommunitiesSubsystem wc wt₂).carrier.interaction_closed
    (coupledCommunitiesSpec_budget wc wt₁ hwc hwt₁)
    (coupledCommunitiesSpec_budget wc wt₂ hwc hwt₂)
    μ₁ μ₂ hμ₁ hμ₂ jointQuery jointQuery_supported

end Mettapedia.Logic.MarkovLogicCoupledCommunitiesExample
