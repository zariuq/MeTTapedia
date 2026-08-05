import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.GaussianFusion
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.LinearGaussianOperator
import Mathlib.Tactic

/-!
# Scalar linear-Gaussian predictive-coding chains

This file contains the pure scalar linear-Gaussian chain theory: links, states,
residuals, energy, clamped equilibria, normal equations, and depth-2 fixtures.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

/-! ## Scalar linear chain equilibrium -/

/-- One scalar predictive-coding link in a linear Gaussian chain. -/
structure PCLink where
  gain : ℝ
  precision : ℝ
  precision_pos : 0 < precision

/-- A scalar chain state with `depth + 1` nodes.  Node `0` is the clamped input. -/
abbrev PCState (depth : ℕ) := Fin (depth + 1) → ℝ

/-- Link residual `zᵢ₊₁ - gainᵢ * zᵢ` for the Fin-indexed chain. -/
noncomputable def pcResidual {depth : ℕ} (links : Fin depth → PCLink)
    (z : PCState depth) (i : Fin depth) : ℝ :=
  z i.succ - (links i).gain * z i.castSucc

/-- Scalar linear-Gaussian predictive-coding chain energy. -/
noncomputable def pcEnergy {depth : ℕ} (links : Fin depth → PCLink)
    (z : PCState depth) : ℝ :=
  ∑ i : Fin depth, (links i).precision * (pcResidual links z i)^2

/-- Pointwise state addition for chain perturbations. -/
noncomputable def pcAddState {depth : ℕ} (z δ : PCState depth) : PCState depth :=
  fun i => z i + δ i

/-- Pointwise state subtraction, used to view a competing state as a perturbation. -/
noncomputable def pcSubState {depth : ℕ} (z y : PCState depth) : PCState depth :=
  fun i => y i - z i

/-- States whose input and output nodes are clamped. -/
def clampedStateSet {depth : ℕ} (x y : ℝ) : Set (PCState depth) :=
  {z | z 0 = x ∧ z (Fin.last depth) = y}

/-- A clamped-chain equilibrium is a state minimizing energy over the fixed
input/output affine slice. -/
def pcEquilibrium {depth : ℕ} (links : Fin depth → PCLink)
    (x y : ℝ) (z : PCState depth) : Prop :=
  z ∈ clampedStateSet x y ∧ IsMinOn (pcEnergy links) (clampedStateSet x y) z

/-- Local stationarity equation at one node. Endpoints are clamped, so their
local equation is vacuous; interior nodes equate incoming and outgoing
precision-weighted residual forces. -/
def pcLocalNormalEquationAt {depth : ℕ} (links : Fin depth → PCLink)
    (z : PCState depth) (i : Fin (depth + 1)) : Prop :=
  if h0 : i.val = 0 then True
  else if hlast : i.val = depth then True
  else
    let prev : Fin depth := ⟨i.val - 1, by omega⟩
    let next : Fin depth := ⟨i.val, by omega⟩
    (links prev).precision * pcResidual links z prev =
      (links next).precision * (links next).gain * pcResidual links z next

/-- Per-node normal equations for the clamped scalar chain. -/
def pcNormalEquations {depth : ℕ} (links : Fin depth → PCLink)
    (z : PCState depth) : Prop :=
  ∀ i : Fin (depth + 1), pcLocalNormalEquationAt links z i

theorem pcResidual_add {depth : ℕ} (links : Fin depth → PCLink)
    (z δ : PCState depth) (i : Fin depth) :
    pcResidual links (pcAddState z δ) i =
      pcResidual links z i + pcResidual links δ i := by
  unfold pcResidual pcAddState
  ring

theorem pcAdd_sub_self {depth : ℕ} (z y : PCState depth) :
    pcAddState z (pcSubState z y) = y := by
  funext i
  unfold pcAddState pcSubState
  ring

/-- Exact finite-chain quadratic expansion for a perturbation. -/
theorem pcEnergy_add_sub_eq_sum {depth : ℕ} (links : Fin depth → PCLink)
    (z δ : PCState depth) :
    pcEnergy links (pcAddState z δ) - pcEnergy links z =
      ∑ i : Fin depth,
        (links i).precision *
          ((pcResidual links δ i)^2 +
            2 * pcResidual links z i * pcResidual links δ i) := by
  unfold pcEnergy
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [pcResidual_add]
  ring

/-- Perturbations that preserve the input and output clamps. -/
def pcZeroEndpointPerturbation {depth : ℕ} (δ : PCState depth) : Prop :=
  δ 0 = 0 ∧ δ (Fin.last depth) = 0

/-- The first variation of the finite-chain energy at `z` in direction `δ`. -/
noncomputable def pcLinearPerturbationTerm {depth : ℕ}
    (links : Fin depth → PCLink) (z δ : PCState depth) : ℝ :=
  ∑ i : Fin depth, (links i).precision *
    (2 * pcResidual links z i * pcResidual links δ i)

/-- Stationarity against all perturbations preserving the input and output clamps. -/
def pcStationaryAgainstPerturbations {depth : ℕ}
    (links : Fin depth → PCLink) (z : PCState depth) : Prop :=
  ∀ δ : PCState depth, pcZeroEndpointPerturbation δ →
    pcLinearPerturbationTerm links z δ = 0

/-- Drop the first link of a nonempty chain. -/
noncomputable def pcTailLinks {depth : ℕ} (links : Fin (depth + 1) → PCLink) :
    Fin depth → PCLink :=
  fun i => links i.succ

/-- Drop the first node of a nonempty chain state. -/
noncomputable def pcTailState {depth : ℕ} (z : PCState (depth + 1)) :
    PCState depth :=
  fun i => z i.succ

theorem pcLinearPerturbationTerm_split {depth : ℕ}
    (links : Fin (depth + 1) → PCLink) (z δ : PCState (depth + 1)) :
    pcLinearPerturbationTerm links z δ =
      (links 0).precision * (2 * pcResidual links z 0 * pcResidual links δ 0) +
        pcLinearPerturbationTerm (pcTailLinks links) (pcTailState z) (pcTailState δ) := by
  unfold pcLinearPerturbationTerm
  rw [Fin.sum_univ_succ]
  rfl

theorem pcTail_normal {depth : ℕ} (links : Fin (depth + 2) → PCLink)
    (z : PCState (depth + 2)) (hnorm : pcNormalEquations links z) :
    pcNormalEquations (pcTailLinks links) (pcTailState z) := by
  intro i
  unfold pcLocalNormalEquationAt
  by_cases h0 : i.val = 0
  · simp [h0]
  · by_cases hlast : i.val = depth + 1
    · simp [hlast]
    · have h := hnorm i.succ
      unfold pcNormalEquations pcLocalNormalEquationAt at h
      have hi_pos : 0 < i.val := Nat.pos_of_ne_zero h0
      have hpred : i.val - 1 + 1 = i.val :=
        Nat.sub_add_cancel (Nat.succ_le_of_lt hi_pos)
      have hcastOrig : (⟨i.val, by omega⟩ : Fin (depth + 3)) = i.castSucc := by
        ext
        simp
      have hsuccOrig : (⟨i.val + 1, by omega⟩ : Fin (depth + 3)) = i.succ := by
        ext
        simp
      simp [h0, hlast, hpred, pcTailLinks, pcTailState, pcResidual,
        hcastOrig, hsuccOrig] at h ⊢
      simpa using h

theorem pcNodeOne_normal {depth : ℕ} (links : Fin (depth + 2) → PCLink)
    (z : PCState (depth + 2)) (hnorm : pcNormalEquations links z) :
    (links 0).precision * pcResidual links z 0 =
      (pcTailLinks links 0).precision * (pcTailLinks links 0).gain *
        pcResidual (pcTailLinks links) (pcTailState z) 0 := by
  have h := hnorm ⟨1, by omega⟩
  unfold pcNormalEquations pcLocalNormalEquationAt at h
  simp [pcTailLinks, pcTailState, pcResidual] at h ⊢
  simpa using h

theorem pcTail_back {depth : ℕ} (links : Fin (depth + 2) → PCLink)
    (z δ : PCState (depth + 2)) :
    2 * ((pcTailLinks links (Fin.last depth)).precision *
        pcResidual (pcTailLinks links) (pcTailState z) (Fin.last depth)) *
        pcTailState δ (Fin.last (depth + 1)) =
      2 * ((links (Fin.last (depth + 1))).precision *
        pcResidual links z (Fin.last (depth + 1))) * δ (Fin.last (depth + 2)) := by
  have hlink : (Fin.last depth).succ = (Fin.last (depth + 1) : Fin (depth + 2)) := by
    ext
    simp
  have hprev : (Fin.last depth).castSucc.succ = (Fin.last (depth + 1)).castSucc := by
    ext
    simp
  have hδ : (Fin.last (depth + 1)).succ = (Fin.last (depth + 2) : Fin (depth + 3)) := by
    ext
    simp
  unfold pcTailLinks pcTailState pcResidual
  simp [hlink, hprev, hδ]

theorem pcLinearTerm_boundary_succ :
    ∀ (depth : ℕ) (links : Fin (depth + 1) → PCLink)
      (z δ : PCState (depth + 1)),
      pcNormalEquations links z →
      2 * ((links 0).precision * (links 0).gain * pcResidual links z 0) * δ 0 +
          pcLinearPerturbationTerm links z δ =
        2 * ((links (Fin.last depth)).precision * pcResidual links z (Fin.last depth)) *
          δ (Fin.last (depth + 1)) := by
  intro depth
  induction depth with
  | zero =>
      intro links z δ _hnorm
      unfold pcLinearPerturbationTerm pcResidual
      rw [Fin.sum_univ_one]
      simp
      ring
  | succ depth ih =>
      intro links z δ hnorm
      have hsplit := pcLinearPerturbationTerm_split links z δ
      have htailNorm := pcTail_normal links z hnorm
      have htail := ih (pcTailLinks links) (pcTailState z) (pcTailState δ) htailNorm
      have hnode := pcNodeOne_normal links z hnorm
      calc
        2 * ((links 0).precision * (links 0).gain * pcResidual links z 0) * δ 0 +
            pcLinearPerturbationTerm links z δ
            = 2 * ((links 0).precision * pcResidual links z 0) * pcTailState δ 0 +
                pcLinearPerturbationTerm (pcTailLinks links) (pcTailState z) (pcTailState δ) := by
              rw [hsplit]
              simp [pcTailState, pcResidual]
              ring
        _ = 2 * ((pcTailLinks links 0).precision * (pcTailLinks links 0).gain *
                pcResidual (pcTailLinks links) (pcTailState z) 0) * pcTailState δ 0 +
                pcLinearPerturbationTerm (pcTailLinks links) (pcTailState z) (pcTailState δ) := by
              rw [hnode]
        _ = 2 * ((pcTailLinks links (Fin.last depth)).precision *
                pcResidual (pcTailLinks links) (pcTailState z) (Fin.last depth)) *
                pcTailState δ (Fin.last (depth + 1)) := htail
        _ = 2 * ((links (Fin.last (depth + 1))).precision *
                pcResidual links z (Fin.last (depth + 1))) *
                δ (Fin.last (depth + 2)) := pcTail_back links z δ

theorem pcNormalEquations_stationary {depth : ℕ} (links : Fin depth → PCLink)
    (z : PCState depth) (hnorm : pcNormalEquations links z) :
    pcStationaryAgainstPerturbations links z := by
  intro δ hδ
  cases depth with
  | zero =>
      unfold pcLinearPerturbationTerm
      simp
  | succ depth =>
      have hboundary := pcLinearTerm_boundary_succ depth links z δ hnorm
      rw [hδ.1, hδ.2] at hboundary
      simpa using hboundary

/-- Pointwise scalar multiplication for perturbations. -/
noncomputable def pcScaleState {depth : ℕ} (r : ℝ) (δ : PCState depth) :
    PCState depth :=
  fun i => r * δ i

/-- The pure quadratic part of the chain energy in a perturbation. -/
noncomputable def pcQuadraticPerturbationTerm {depth : ℕ}
    (links : Fin depth → PCLink) (δ : PCState depth) : ℝ :=
  ∑ i : Fin depth, (links i).precision * (pcResidual links δ i)^2

theorem pcResidual_scale {depth : ℕ} (links : Fin depth → PCLink)
    (r : ℝ) (δ : PCState depth) (i : Fin depth) :
    pcResidual links (pcScaleState r δ) i = r * pcResidual links δ i := by
  unfold pcResidual pcScaleState
  ring

theorem pcScale_zeroEndpoint {depth : ℕ} {r : ℝ} {δ : PCState depth}
    (hδ : pcZeroEndpointPerturbation δ) :
    pcZeroEndpointPerturbation (pcScaleState r δ) := by
  constructor
  · unfold pcScaleState
    rw [hδ.1]
    ring
  · unfold pcScaleState
    rw [hδ.2]
    ring

theorem pcEnergy_add_scaled_sub_eq_quadratic {depth : ℕ}
    (links : Fin depth → PCLink) (z δ : PCState depth) (r : ℝ) :
    pcEnergy links (pcAddState z (pcScaleState r δ)) - pcEnergy links z =
      r^2 * pcQuadraticPerturbationTerm links δ +
        r * pcLinearPerturbationTerm links z δ := by
  rw [pcEnergy_add_sub_eq_sum]
  unfold pcQuadraticPerturbationTerm pcLinearPerturbationTerm
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [pcResidual_scale]
  ring

theorem pcEquilibrium_stationary {depth : ℕ} (links : Fin depth → PCLink)
    (x y₀ : ℝ) (z : PCState depth) (heq : pcEquilibrium links x y₀ z) :
    pcStationaryAgainstPerturbations links z := by
  intro δ hδ
  let Q := pcQuadraticPerturbationTerm links δ
  let L := pcLinearPerturbationTerm links z δ
  have hmin_forall : ∀ u ∈ clampedStateSet x y₀, pcEnergy links z ≤ pcEnergy links u := by
    simpa [IsMinOn, IsMinFilter] using heq.2
  have hpoly : ∀ r : ℝ, 0 ≤ Q * (r * r) + L * r + 0 := by
    intro r
    have hscaled : pcAddState z (pcScaleState r δ) ∈ clampedStateSet x y₀ := by
      constructor
      · unfold pcAddState pcScaleState
        rw [heq.1.1, hδ.1]
        ring
      · unfold pcAddState pcScaleState
        rw [heq.1.2, hδ.2]
        ring
    have hle := hmin_forall (pcAddState z (pcScaleState r δ)) hscaled
    have hnonneg :
        0 ≤ pcEnergy links (pcAddState z (pcScaleState r δ)) - pcEnergy links z :=
      sub_nonneg.mpr hle
    rw [pcEnergy_add_scaled_sub_eq_quadratic] at hnonneg
    dsimp [Q, L] at hnonneg ⊢
    nlinarith
  have hdisc := discrim_le_zero (a := Q) (b := L) (c := (0 : ℝ)) hpoly
  unfold discrim at hdisc
  have hLsq : L^2 = 0 := by
    have hle : L^2 ≤ 0 := by nlinarith
    exact le_antisymm hle (sq_nonneg L)
  exact sq_eq_zero_iff.mp hLsq

/-- Unit perturbation at a single chain node. -/
noncomputable def pcSingleNodePerturbation {depth : ℕ}
    (node : Fin (depth + 1)) : PCState depth :=
  Pi.single node (1 : ℝ)

theorem pcSingleNode_residual_prev {depth : ℕ} (links : Fin depth → PCLink)
    (i : Fin (depth + 1)) (h0 : i.val ≠ 0) (hlast : i.val ≠ depth) :
    let prev : Fin depth := ⟨i.val - 1, by omega⟩
    pcResidual links (pcSingleNodePerturbation i) prev = 1 := by
  intro prev
  have hprevSucc : prev.succ = i := by
    ext
    simp [prev]
    omega
  have hprevCast_ne : prev.castSucc ≠ i := by
    intro h
    have hv : prev.castSucc.val = i.val := by rw [h]
    simp [prev] at hv
    omega
  unfold pcResidual pcSingleNodePerturbation
  simp [hprevSucc, hprevCast_ne]

theorem pcSingleNode_residual_next {depth : ℕ} (links : Fin depth → PCLink)
    (i : Fin (depth + 1)) (_h0 : i.val ≠ 0) (hlast : i.val ≠ depth) :
    let next : Fin depth := ⟨i.val, by omega⟩
    pcResidual links (pcSingleNodePerturbation i) next = - (links next).gain := by
  intro next
  have hnextCast : next.castSucc = i := by
    ext
    simp [next]
  have hnextSucc_ne : next.succ ≠ i := by
    intro h
    have hv : next.succ.val = i.val := by rw [h]
    simp [next] at hv
  unfold pcResidual pcSingleNodePerturbation
  simp [hnextCast, hnextSucc_ne]

theorem pcSingleNode_residual_other {depth : ℕ} (links : Fin depth → PCLink)
    (i : Fin (depth + 1)) (_h0 : i.val ≠ 0) (hlast : i.val ≠ depth) :
    let prev : Fin depth := ⟨i.val - 1, by omega⟩
    let next : Fin depth := ⟨i.val, by omega⟩
    ∀ k : Fin depth, k ≠ prev → k ≠ next →
      pcResidual links (pcSingleNodePerturbation i) k = 0 := by
  intro prev next k hkprev hknext
  have hsucc_ne : k.succ ≠ i := by
    intro h
    apply hkprev
    ext
    have hv : k.succ.val = i.val := by rw [h]
    simp at hv
    simp [prev]
    omega
  have hcast_ne : k.castSucc ≠ i := by
    intro h
    apply hknext
    ext
    have hv : k.castSucc.val = i.val := by rw [h]
    simp at hv
    simp [next]
    exact hv
  unfold pcResidual pcSingleNodePerturbation
  simp [hsucc_ne, hcast_ne]

theorem pcLinearPerturbationTerm_single_node {depth : ℕ}
    (links : Fin depth → PCLink) (z : PCState depth)
    (i : Fin (depth + 1)) (h0 : i.val ≠ 0) (hlast : i.val ≠ depth) :
    let prev : Fin depth := ⟨i.val - 1, by omega⟩
    let next : Fin depth := ⟨i.val, by omega⟩
    pcLinearPerturbationTerm links z (pcSingleNodePerturbation i) =
      2 * ((links prev).precision * pcResidual links z prev -
        (links next).precision * (links next).gain * pcResidual links z next) := by
  intro prev next
  have hprev_ne_next : prev ≠ next := by
    intro h
    have hv : prev.val = next.val := by rw [h]
    simp [prev, next] at hv
    omega
  let f : Fin depth → ℝ := fun k =>
    (links k).precision * (2 * pcResidual links z k *
      pcResidual links (pcSingleNodePerturbation i) k)
  have hfprev : f prev = (links prev).precision * (2 * pcResidual links z prev * 1) := by
    dsimp [f]
    rw [pcSingleNode_residual_prev links i h0 hlast]
  have hfnext :
      f next = (links next).precision *
        (2 * pcResidual links z next * (-(links next).gain)) := by
    dsimp [f]
    rw [pcSingleNode_residual_next links i h0 hlast]
  have hfzero : ∀ k : Fin depth, k ≠ prev → k ≠ next → f k = 0 := by
    intro k hkprev hknext
    dsimp [f]
    rw [pcSingleNode_residual_other links i h0 hlast k hkprev hknext]
    ring
  unfold pcLinearPerturbationTerm
  change (∑ k : Fin depth, f k) = _
  rw [show (∑ k : Fin depth, f k) =
      f prev + ∑ k ∈ (Finset.univ : Finset (Fin depth)).erase prev, f k by
    rw [Finset.add_sum_erase]
    simp]
  have hsum_erase :
      (∑ k ∈ (Finset.univ : Finset (Fin depth)).erase prev, f k) = f next := by
    apply Finset.sum_eq_single next
    · intro k hk hknext
      have hkprev : k ≠ prev := (Finset.mem_erase.mp hk).1
      exact hfzero k hkprev hknext
    · intro hnot
      exfalso
      apply hnot
      exact Finset.mem_erase.mpr ⟨Ne.symm hprev_ne_next, Finset.mem_univ next⟩
  rw [hsum_erase, hfprev, hfnext]
  ring

theorem pcStationary_normalEquations {depth : ℕ} (links : Fin depth → PCLink)
    (z : PCState depth) (hstat : pcStationaryAgainstPerturbations links z) :
    pcNormalEquations links z := by
  intro i
  unfold pcLocalNormalEquationAt
  by_cases h0 : i.val = 0
  · simp [h0]
  · by_cases hlast : i.val = depth
    · simp [hlast]
    · let prev : Fin depth := ⟨i.val - 1, by omega⟩
      let next : Fin depth := ⟨i.val, by omega⟩
      have hzero : pcZeroEndpointPerturbation (pcSingleNodePerturbation i) := by
        constructor
        · have hne : (0 : Fin (depth + 1)) ≠ i := by
            intro h
            have hv := congrArg Fin.val h
            simp at hv
            omega
          simp [pcSingleNodePerturbation, hne]
        · have hne : Fin.last depth ≠ i := by
            intro h
            have hv := congrArg Fin.val h
            simp at hv
            omega
          simp [pcSingleNodePerturbation, hne]
      have hlin := hstat (pcSingleNodePerturbation i) hzero
      rw [pcLinearPerturbationTerm_single_node links z i h0 hlast] at hlin
      have hdiff :
          (links prev).precision * pcResidual links z prev -
              (links next).precision * (links next).gain * pcResidual links z next = 0 := by
        nlinarith
      simpa [h0, hlast, prev, next] using sub_eq_zero.mp hdiff

theorem pcSub_zeroEndpoint {depth : ℕ} {x y₀ : ℝ} {z y : PCState depth}
    (hz : z ∈ clampedStateSet x y₀) (hy : y ∈ clampedStateSet x y₀) :
    pcZeroEndpointPerturbation (pcSubState z y) := by
  constructor
  · unfold pcSubState
    rw [hy.1, hz.1]
    ring
  · unfold pcSubState
    rw [hy.2, hz.2]
    ring

/-- Variational MAP theorem for the general scalar chain: a clamped state whose
first variation vanishes for every clamp-preserving perturbation minimizes the
finite-chain Gaussian energy. -/
theorem pcStationary_isMinOn {depth : ℕ} (links : Fin depth → PCLink)
    (x y₀ : ℝ) (z : PCState depth) (hz : z ∈ clampedStateSet x y₀)
    (hstat : pcStationaryAgainstPerturbations links z) :
    IsMinOn (pcEnergy links) (clampedStateSet x y₀) z := by
  intro y hy
  let δ := pcSubState z y
  have hδzero : pcZeroEndpointPerturbation δ := pcSub_zeroEndpoint hz hy
  have hrewrite : y = pcAddState z δ := by
    rw [pcAdd_sub_self]
  rw [hrewrite]
  have hdiff := pcEnergy_add_sub_eq_sum links z δ
  have hlinear : pcLinearPerturbationTerm links z δ = 0 := hstat δ hδzero
  have hnonneg : 0 ≤ pcEnergy links (pcAddState z δ) - pcEnergy links z := by
    rw [hdiff]
    have hsplit :
        (∑ i : Fin depth,
          (links i).precision *
            ((pcResidual links δ i)^2 +
              2 * pcResidual links z i * pcResidual links δ i)) =
          (∑ i : Fin depth, (links i).precision * (pcResidual links δ i)^2) +
            pcLinearPerturbationTerm links z δ := by
      unfold pcLinearPerturbationTerm
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    rw [hsplit, hlinear, add_zero]
    exact Finset.sum_nonneg (fun i _hi =>
      mul_nonneg (le_of_lt (links i).precision_pos) (sq_nonneg _))
  exact sub_nonneg.mp hnonneg

/-- General-chain equilibrium package from variational stationarity. -/
theorem pcStationary_equilibrium {depth : ℕ} (links : Fin depth → PCLink)
    (x y₀ : ℝ) (z : PCState depth) (hz : z ∈ clampedStateSet x y₀)
    (hstat : pcStationaryAgainstPerturbations links z) :
    pcEquilibrium links x y₀ z :=
  ⟨hz, pcStationary_isMinOn links x y₀ z hz hstat⟩

theorem pcNormalEquations_equilibrium {depth : ℕ} (links : Fin depth → PCLink)
    (x y₀ : ℝ) (z : PCState depth) (hz : z ∈ clampedStateSet x y₀)
    (hnorm : pcNormalEquations links z) :
    pcEquilibrium links x y₀ z :=
  pcStationary_equilibrium links x y₀ z hz
    (pcNormalEquations_stationary links z hnorm)

/-- P2 crown: for the scalar linear-Gaussian chain, clamped equilibria are
exactly clamped states satisfying the finite local normal equations. -/
theorem pcEquilibrium_iff_normalEquations {depth : ℕ} (links : Fin depth → PCLink)
    (x y₀ : ℝ) (z : PCState depth) :
    pcEquilibrium links x y₀ z ↔
      z ∈ clampedStateSet x y₀ ∧ pcNormalEquations links z := by
  constructor
  · intro heq
    exact ⟨heq.1, pcStationary_normalEquations links z
      (pcEquilibrium_stationary links x y₀ z heq)⟩
  · intro h
    exact pcNormalEquations_equilibrium links x y₀ z h.1 h.2

theorem pcEnergy_add_sub_eq_quadratic_linear {depth : ℕ}
    (links : Fin depth → PCLink) (z δ : PCState depth) :
    pcEnergy links (pcAddState z δ) - pcEnergy links z =
      pcQuadraticPerturbationTerm links δ + pcLinearPerturbationTerm links z δ := by
  rw [pcEnergy_add_sub_eq_sum]
  unfold pcQuadraticPerturbationTerm pcLinearPerturbationTerm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

theorem pcQuadraticPerturbationTerm_nonneg {depth : ℕ}
    (links : Fin depth → PCLink) (δ : PCState depth) :
    0 ≤ pcQuadraticPerturbationTerm links δ := by
  unfold pcQuadraticPerturbationTerm
  exact Finset.sum_nonneg (fun i _hi =>
    mul_nonneg (le_of_lt (links i).precision_pos) (sq_nonneg _))

theorem pcResidual_eq_zero_of_quadratic_eq_zero {depth : ℕ}
    (links : Fin depth → PCLink) (δ : PCState depth)
    (hquad : pcQuadraticPerturbationTerm links δ = 0) :
    ∀ i : Fin depth, pcResidual links δ i = 0 := by
  intro i
  have hsum :
      (∑ j : Fin depth, (links j).precision * (pcResidual links δ j)^2) = 0 := by
    simpa [pcQuadraticPerturbationTerm] using hquad
  have hnonneg :
      ∀ j ∈ (Finset.univ : Finset (Fin depth)),
        0 ≤ (links j).precision * (pcResidual links δ j)^2 := by
    intro j _hj
    exact mul_nonneg (le_of_lt (links j).precision_pos) (sq_nonneg _)
  have hterm :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum i (Finset.mem_univ i)
  have hprec_ne : (links i).precision ≠ 0 := ne_of_gt (links i).precision_pos
  have hsquare : (pcResidual links δ i)^2 = 0 :=
    (mul_eq_zero.mp hterm).resolve_left hprec_ne
  exact sq_eq_zero_iff.mp hsquare

theorem pcZeroEndpoint_eq_zero_of_zero_residuals {depth : ℕ}
    (links : Fin depth → PCLink) (δ : PCState depth)
    (hzero : pcZeroEndpointPerturbation δ)
    (hres : ∀ i : Fin depth, pcResidual links δ i = 0) :
    δ = fun _ => 0 := by
  funext i
  have hnode : ∀ n (hn : n < depth + 1), δ ⟨n, hn⟩ = 0 := by
    intro n
    induction n with
    | zero =>
        intro _hn
        simpa using hzero.1
    | succ n ih =>
        intro hn
        have hn_depth : n < depth := by omega
        let prev : Fin depth := ⟨n, hn_depth⟩
        have hprev := hres prev
        have hprev_cast : prev.castSucc = (⟨n, by omega⟩ : Fin (depth + 1)) := by
          ext
          simp [prev]
        have hprev_succ : prev.succ = (⟨n + 1, hn⟩ : Fin (depth + 1)) := by
          ext
          simp [prev]
        have hδprev : δ prev.castSucc = 0 := by
          rw [hprev_cast]
          exact ih (by omega)
        unfold pcResidual at hprev
        rw [hprev_succ, hδprev] at hprev
        nlinarith
  exact hnode i.val i.isLt

/-- P2 uniqueness corollary: the clamped scalar linear-Gaussian chain has at
most one equilibrium. -/
theorem pcEquilibrium_unique {depth : ℕ} (links : Fin depth → PCLink)
    {x y₀ : ℝ} {z y : PCState depth}
    (hz : pcEquilibrium links x y₀ z) (hy : pcEquilibrium links x y₀ y) :
    y = z := by
  let δ := pcSubState z y
  have hδzero : pcZeroEndpointPerturbation δ := pcSub_zeroEndpoint hz.1 hy.1
  have hstat : pcStationaryAgainstPerturbations links z :=
    pcEquilibrium_stationary links x y₀ z hz
  have hlinear : pcLinearPerturbationTerm links z δ = 0 := hstat δ hδzero
  have hrewrite : y = pcAddState z δ := by
    rw [pcAdd_sub_self]
  have hz_forall : ∀ u ∈ clampedStateSet x y₀, pcEnergy links z ≤ pcEnergy links u := by
    simpa [IsMinOn, IsMinFilter] using hz.2
  have hy_forall : ∀ u ∈ clampedStateSet x y₀, pcEnergy links y ≤ pcEnergy links u := by
    simpa [IsMinOn, IsMinFilter] using hy.2
  have henergy_eq : pcEnergy links y = pcEnergy links z := by
    exact le_antisymm (hy_forall z hz.1) (hz_forall y hy.1)
  have hdiff_quad :
      pcEnergy links y - pcEnergy links z = pcQuadraticPerturbationTerm links δ := by
    rw [hrewrite, pcEnergy_add_sub_eq_quadratic_linear, hlinear, add_zero]
  have hdiff_zero : pcEnergy links y - pcEnergy links z = 0 := by
    rw [henergy_eq]
    ring
  have hquad : pcQuadraticPerturbationTerm links δ = 0 := by
    rw [← hdiff_quad, hdiff_zero]
  have hres : ∀ i : Fin depth, pcResidual links δ i = 0 :=
    pcResidual_eq_zero_of_quadratic_eq_zero links δ hquad
  have hδzero_fun : δ = fun _ => 0 :=
    pcZeroEndpoint_eq_zero_of_zero_residuals links δ hδzero hres
  rw [hrewrite]
  funext i
  unfold pcAddState
  have hδi : δ i = 0 := by
    exact congrFun hδzero_fun i
  rw [hδi]
  ring

/-! ## Bayesian semantics of an arbitrary finite chain -/

open MeasureTheory ProbabilityTheory

/-- Euclidean coordinates for the `interior` unclamped nodes of a chain with
`interior + 1` links. -/
abbrev PCInteriorSpace (interior : ℕ) := EuclideanSpace ℝ (Fin interior)

/-- Insert interior coordinates into a zero-endpoint chain perturbation. -/
noncomputable def pcInteriorPerturbation (interior : ℕ)
    (u : PCInteriorSpace interior) : PCState (interior + 1) :=
  fun node =>
    if hzero : node.val = 0 then 0
    else if hlast : node.val = interior + 1 then 0
    else u ⟨node.val - 1, by omega⟩

@[simp] theorem pcInteriorPerturbation_zero (interior : ℕ)
    (u : PCInteriorSpace interior) :
    pcInteriorPerturbation interior u 0 = 0 := by
  simp [pcInteriorPerturbation]

@[simp] theorem pcInteriorPerturbation_last (interior : ℕ)
    (u : PCInteriorSpace interior) :
    pcInteriorPerturbation interior u (Fin.last (interior + 1)) = 0 := by
  simp [pcInteriorPerturbation]

@[simp] theorem pcInteriorPerturbation_interior (interior : ℕ)
    (u : PCInteriorSpace interior) (i : Fin interior) :
    pcInteriorPerturbation interior u ⟨i.val + 1, by omega⟩ = u i := by
  simp [pcInteriorPerturbation]
  omega

/-- Residual formation restricted to zero-endpoint interior perturbations. -/
noncomputable def pcInteriorResidualLinearMap {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) :
    PCInteriorSpace interior →ₗ[ℝ] (Fin (interior + 1) → ℝ) where
  toFun u := fun edge => pcResidual links (pcInteriorPerturbation interior u) edge
  map_add' u v := by
    funext edge
    simp only [pcResidual, pcInteriorPerturbation, Pi.add_apply]
    split_ifs <;> simp <;> ring
  map_smul' r u := by
    funext edge
    simp only [pcResidual, pcInteriorPerturbation, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp <;> ring

@[simp] theorem pcInteriorResidualLinearMap_apply {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) (u : PCInteriorSpace interior)
    (edge : Fin (interior + 1)) :
    pcInteriorResidualLinearMap links u edge =
      pcResidual links (pcInteriorPerturbation interior u) edge := rfl

theorem pcInteriorResidualLinearMap_injective {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) :
    Function.Injective (pcInteriorResidualLinearMap links) := by
  intro u v huv
  have hmapzero : pcInteriorResidualLinearMap links (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  let δ := pcInteriorPerturbation interior (u - v)
  have hδzero : pcZeroEndpointPerturbation δ := by
    constructor <;> simp [δ]
  have hres : ∀ edge : Fin (interior + 1), pcResidual links δ edge = 0 := by
    intro edge
    have hedge := congrFun hmapzero edge
    simpa [δ] using hedge
  have hδ : δ = fun _ => 0 :=
    pcZeroEndpoint_eq_zero_of_zero_residuals links δ hδzero hres
  apply sub_eq_zero.mp
  apply PiLp.ext
  intro i
  have hnode := congrFun hδ (⟨i.val + 1, by omega⟩ : Fin (interior + 2))
  simpa [δ] using hnode

/-- Matrix of the injective residual-incidence map in the standard bases. -/
noncomputable def pcInteriorIncidenceMatrix {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) :
    Matrix (Fin (interior + 1)) (Fin interior) ℝ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin interior) ℝ).toBasis
    (Pi.basisFun ℝ (Fin (interior + 1))) (pcInteriorResidualLinearMap links)

theorem pcInteriorIncidenceMatrix_mulVec {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) (u : PCInteriorSpace interior) :
    (pcInteriorIncidenceMatrix links).mulVec (fun i => u i) =
      pcInteriorResidualLinearMap links u := by
  have h := LinearMap.toMatrix_mulVec_repr
    (EuclideanSpace.basisFun (Fin interior) ℝ).toBasis
    (Pi.basisFun ℝ (Fin (interior + 1)))
    (pcInteriorResidualLinearMap links) u
  have hdomain :
      ⇑((EuclideanSpace.basisFun (Fin interior) ℝ).toBasis.repr u) =
        (fun i => u i) := by
    funext i
    exact EuclideanSpace.basisFun_repr (Fin interior) ℝ u i
  have hcodomain :
      ⇑((Pi.basisFun ℝ (Fin (interior + 1))).repr
        (pcInteriorResidualLinearMap links u)) =
        pcInteriorResidualLinearMap links u := by
    funext edge
    exact Pi.basisFun_repr ℝ (Fin (interior + 1)) _ edge
  rw [hdomain, hcodomain] at h
  exact h

theorem pcInteriorIncidenceMatrix_mulVec_injective {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) :
    Function.Injective (pcInteriorIncidenceMatrix links).mulVec := by
  intro u v huv
  let u' : PCInteriorSpace interior := WithLp.toLp 2 u
  let v' : PCInteriorSpace interior := WithLp.toLp 2 v
  have hlinear : pcInteriorResidualLinearMap links u' =
      pcInteriorResidualLinearMap links v' := by
    rw [← pcInteriorIncidenceMatrix_mulVec links u',
      ← pcInteriorIncidenceMatrix_mulVec links v']
    simpa [u', v'] using huv
  have huv' := pcInteriorResidualLinearMap_injective links hlinear
  funext i
  exact congrArg (fun w : PCInteriorSpace interior => w i) huv'

/-- Diagonal edge-precision matrix of the conditioned chain. -/
noncomputable def pcEdgePrecisionMatrix {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) :
    Matrix (Fin (interior + 1)) (Fin (interior + 1)) ℝ :=
  Matrix.diagonal fun edge => (links edge).precision

/-- Interior posterior precision `Aᵀ Λ A`. -/
noncomputable def pcInteriorPrecisionMatrix {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) :
    Matrix (Fin interior) (Fin interior) ℝ :=
  (pcInteriorIncidenceMatrix links).transpose * pcEdgePrecisionMatrix links *
    pcInteriorIncidenceMatrix links

theorem pcEdgePrecisionMatrix_posDef {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) :
    (pcEdgePrecisionMatrix links).PosDef := by
  unfold pcEdgePrecisionMatrix
  exact Matrix.PosDef.diagonal fun edge => (links edge).precision_pos

/-- The conditioned interior precision is positive definite for every finite
chain with positive edge precisions, including the zero-interior base case. -/
theorem pcInteriorPrecisionMatrix_posDef {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) :
    (pcInteriorPrecisionMatrix links).PosDef := by
  have h := (pcEdgePrecisionMatrix_posDef links).conjTranspose_mul_mul_same
    (pcInteriorIncidenceMatrix_mulVec_injective links)
  simpa [pcInteriorPrecisionMatrix] using h

/-- State containing only the two clamped endpoint observations. -/
noncomputable def pcEndpointState (interior : ℕ) (x y : ℝ) :
    PCState (interior + 1) :=
  fun node =>
    if node.val = 0 then x
    else if node.val = interior + 1 then y
    else 0

/-- Full chain state assembled from clamped endpoints and interior coordinates. -/
noncomputable def pcStateOfInterior (interior : ℕ) (x y : ℝ)
    (u : PCInteriorSpace interior) : PCState (interior + 1) :=
  pcAddState (pcEndpointState interior x y) (pcInteriorPerturbation interior u)

@[simp] theorem pcStateOfInterior_zero (interior : ℕ) (x y : ℝ)
    (u : PCInteriorSpace interior) :
    pcStateOfInterior interior x y u 0 = x := by
  simp [pcStateOfInterior, pcAddState, pcEndpointState]

@[simp] theorem pcStateOfInterior_last (interior : ℕ) (x y : ℝ)
    (u : PCInteriorSpace interior) :
    pcStateOfInterior interior x y u (Fin.last (interior + 1)) = y := by
  simp [pcStateOfInterior, pcAddState, pcEndpointState]

@[simp] theorem pcStateOfInterior_interior (interior : ℕ) (x y : ℝ)
    (u : PCInteriorSpace interior) (i : Fin interior) :
    pcStateOfInterior interior x y u ⟨i.val + 1, by omega⟩ = u i := by
  simp [pcStateOfInterior, pcAddState, pcEndpointState]
  omega

theorem pcStateOfInterior_mem_clamped (interior : ℕ) (x y : ℝ)
    (u : PCInteriorSpace interior) :
    pcStateOfInterior interior x y u ∈ clampedStateSet x y :=
  ⟨pcStateOfInterior_zero interior x y u, pcStateOfInterior_last interior x y u⟩

/-- Extract the interior coordinates of a full chain state. -/
noncomputable def pcInteriorCoordinates (interior : ℕ)
    (z : PCState (interior + 1)) : PCInteriorSpace interior :=
  WithLp.toLp 2 fun i => z ⟨i.val + 1, by omega⟩

@[simp] theorem pcInteriorCoordinates_stateOfInterior (interior : ℕ)
    (x y : ℝ) (u : PCInteriorSpace interior) :
    pcInteriorCoordinates interior (pcStateOfInterior interior x y u) = u := by
  apply PiLp.ext
  intro i
  simp [pcInteriorCoordinates]

theorem pcStateOfInterior_coordinates_of_clamped (interior : ℕ)
    (x y : ℝ) (z : PCState (interior + 1))
    (hz : z ∈ clampedStateSet x y) :
    pcStateOfInterior interior x y (pcInteriorCoordinates interior z) = z := by
  funext node
  by_cases hzero : node.val = 0
  · have hnode : node = 0 := Fin.ext hzero
    subst node
    simpa using hz.1.symm
  by_cases hlast : node.val = interior + 1
  · have hnode : node = Fin.last (interior + 1) := by
      apply Fin.ext
      simpa using hlast
    subst node
    simpa using hz.2.symm
  · have hpos : 0 < node.val := Nat.pos_of_ne_zero hzero
    have hidx : node.val - 1 < interior := by omega
    let i : Fin interior := ⟨node.val - 1, hidx⟩
    have hnode : (⟨i.val + 1, by omega⟩ : Fin (interior + 2)) = node := by
      apply Fin.ext
      simp [i]
      omega
    rw [← hnode, pcStateOfInterior_interior]
    simp [pcInteriorCoordinates, i, hnode]

/-- Residual vector contributed solely by the clamped endpoints. -/
noncomputable def pcEndpointResidualVector {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) (x y : ℝ) :
    Fin (interior + 1) → ℝ :=
  fun edge => pcResidual links (pcEndpointState interior x y) edge

/-- The scalar chain as an instance of the operator-level affine
linear-Gaussian residual model. -/
noncomputable def pcLinearGaussianOperatorModel {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) (x y : ℝ) :
    LinearGaussianOperatorModel (Fin interior) (Fin (interior + 1)) where
  residualMatrix := pcInteriorIncidenceMatrix links
  residualPrecision := pcEdgePrecisionMatrix links
  residualOffset := pcEndpointResidualVector links x y
  residualMatrix_injective := pcInteriorIncidenceMatrix_mulVec_injective links
  residualPrecision_posDef := pcEdgePrecisionMatrix_posDef links

@[simp] theorem pcLinearGaussianOperatorModel_posteriorPrecision {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) (x y : ℝ) :
    (pcLinearGaussianOperatorModel links x y).posteriorPrecision =
      pcInteriorPrecisionMatrix links := rfl

/-- Canonical affine residual vector `A u + c` after conditioning endpoints. -/
noncomputable def pcConditionalResidualVector {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) (x y : ℝ)
    (u : PCInteriorSpace interior) : Fin (interior + 1) → ℝ :=
  (pcInteriorIncidenceMatrix links).mulVec (fun i => u i) +
    pcEndpointResidualVector links x y

theorem pcConditionalResidualVector_eq_pcResidual {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) (x y : ℝ)
    (u : PCInteriorSpace interior) :
    pcConditionalResidualVector links x y u =
      fun edge => pcResidual links (pcStateOfInterior interior x y u) edge := by
  funext edge
  rw [pcStateOfInterior, pcResidual_add]
  simp [pcConditionalResidualVector, pcEndpointResidualVector,
    pcInteriorIncidenceMatrix_mulVec]
  ring

/-- Natural parameter `-Aᵀ Λ c` of the endpoint-conditioned Gaussian. -/
noncomputable def pcConditionalNaturalParameter {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) (x y : ℝ) : Fin interior → ℝ :=
  -((pcInteriorIncidenceMatrix links).transpose.mulVec
    ((pcEdgePrecisionMatrix links).mulVec (pcEndpointResidualVector links x y)))

/-- Conditional posterior mean in canonical Gaussian coordinates, `Q⁻¹ b`. -/
noncomputable def pcConditionalPosteriorMean {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) (x y : ℝ) :
    PCInteriorSpace interior :=
  WithLp.toLp 2 ((pcInteriorPrecisionMatrix links)⁻¹.mulVec
    (pcConditionalNaturalParameter links x y))

/-- The endpoint-conditioned multivariate Gaussian posterior.  Its precision
and natural parameter are obtained directly from the chain residual energy. -/
noncomputable def pcConditionalPosterior {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) (x y : ℝ) :
    Measure (PCInteriorSpace interior) :=
  multivariateGaussian (pcConditionalPosteriorMean links x y)
    (pcInteriorPrecisionMatrix links)⁻¹

@[simp] theorem pcLinearGaussianOperatorModel_naturalParameter {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) (x y : ℝ) :
    (pcLinearGaussianOperatorModel links x y).naturalParameter =
      pcConditionalNaturalParameter links x y := rfl

@[simp] theorem pcLinearGaussianOperatorModel_posteriorMean {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) (x y : ℝ) :
    (pcLinearGaussianOperatorModel links x y).posteriorMean =
      pcConditionalPosteriorMean links x y := rfl

@[simp] theorem pcLinearGaussianOperatorModel_posterior {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) (x y : ℝ) :
    (pcLinearGaussianOperatorModel links x y).posterior =
      pcConditionalPosterior links x y := rfl

theorem pcConditionalPosterior_covariance_posDef {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) :
    ((pcInteriorPrecisionMatrix links)⁻¹).PosDef :=
  (pcLinearGaussianOperatorModel links 0 0).posterior_covariance_posDef

/-- The probabilistic mean of the conditioned Gaussian is its independently
defined canonical solution `Q⁻¹ b`. -/
theorem pcConditionalPosterior_integral_id {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) (x y : ℝ) :
    ∫ u, u ∂pcConditionalPosterior links x y =
      pcConditionalPosteriorMean links x y := by
  exact (pcLinearGaussianOperatorModel links x y).posterior_integral_id

theorem pcInteriorPrecision_mul_posteriorMean {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) (x y : ℝ) :
    (pcInteriorPrecisionMatrix links).mulVec
        (fun i => pcConditionalPosteriorMean links x y i) =
      pcConditionalNaturalParameter links x y := by
  exact (pcLinearGaussianOperatorModel links x y).precision_mul_posteriorMean

/-- The posterior mean makes the conditioned residual force stationary. -/
theorem pcConditionalResidual_stationary {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) (x y : ℝ) :
    (pcInteriorIncidenceMatrix links).transpose.mulVec
        ((pcEdgePrecisionMatrix links).mulVec
          (pcConditionalResidualVector links x y
            (pcConditionalPosteriorMean links x y))) = 0 := by
  exact (pcLinearGaussianOperatorModel links x y).posteriorMean_stationary

/-- Canonical quadratic energy of the endpoint-conditioned Gaussian. -/
noncomputable def pcConditionalCanonicalEnergy {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) (x y : ℝ)
    (u : PCInteriorSpace interior) : ℝ :=
  pcConditionalResidualVector links x y u ⬝ᵥ
    (pcEdgePrecisionMatrix links).mulVec
      (pcConditionalResidualVector links x y u)

@[simp] theorem pcLinearGaussianOperatorModel_energy {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) (x y : ℝ)
    (u : PCInteriorSpace interior) :
    (pcLinearGaussianOperatorModel links x y).energy u =
      pcConditionalCanonicalEnergy links x y u := rfl

theorem pcEnergy_stateOfInterior_eq_canonical {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) (x y : ℝ)
    (u : PCInteriorSpace interior) :
    pcEnergy links (pcStateOfInterior interior x y u) =
      pcConditionalCanonicalEnergy links x y u := by
  rw [pcConditionalCanonicalEnergy]
  rw [pcConditionalResidualVector_eq_pcResidual]
  unfold pcEnergy dotProduct pcEdgePrecisionMatrix
  apply Finset.sum_congr rfl
  intro edge _hedge
  rw [Matrix.mulVec_diagonal]
  ring

theorem pcEdgePrecision_dot_swap {interior : ℕ}
    (links : Fin (interior + 1) → PCLink)
    (a b : Fin (interior + 1) → ℝ) :
    a ⬝ᵥ (pcEdgePrecisionMatrix links).mulVec b =
      b ⬝ᵥ (pcEdgePrecisionMatrix links).mulVec a := by
  exact (pcLinearGaussianOperatorModel links 0 0).precision_dot_swap a b

theorem pcInteriorPrecision_quadratic {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) (d : Fin interior → ℝ) :
    d ⬝ᵥ (pcInteriorPrecisionMatrix links).mulVec d =
      (pcInteriorIncidenceMatrix links).mulVec d ⬝ᵥ
        (pcEdgePrecisionMatrix links).mulVec
          ((pcInteriorIncidenceMatrix links).mulVec d) := by
  exact (pcLinearGaussianOperatorModel links 0 0).posteriorPrecision_quadratic d

/-- Exact completion of the conditioned chain energy around the posterior mean. -/
theorem pcConditionalCanonicalEnergy_sub_mean {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) (x y : ℝ)
    (u : PCInteriorSpace interior) :
    pcConditionalCanonicalEnergy links x y u -
        pcConditionalCanonicalEnergy links x y
          (pcConditionalPosteriorMean links x y) =
      (fun i => u i - pcConditionalPosteriorMean links x y i) ⬝ᵥ
        (pcInteriorPrecisionMatrix links).mulVec
          (fun i => u i - pcConditionalPosteriorMean links x y i) := by
  exact (pcLinearGaussianOperatorModel links x y).energy_sub_posteriorMean u

/-- The chain energy is minimized at the canonical conditional posterior mean. -/
theorem pcConditionalPosteriorMean_isMinOn {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) (x y : ℝ) :
    IsMinOn (fun u => pcEnergy links (pcStateOfInterior interior x y u)) Set.univ
      (pcConditionalPosteriorMean links x y) := by
  rw [isMinOn_univ_iff]
  intro u
  rw [pcEnergy_stateOfInterior_eq_canonical,
    pcEnergy_stateOfInterior_eq_canonical]
  exact (isMinOn_univ_iff.mp
    (pcLinearGaussianOperatorModel links x y).posteriorMean_isMinOn) u

/-- Clamped scalar-chain equilibria are exactly operator-model equilibria in
interior coordinates.  This is the adapter through which the scalar Bayesian
crown inherits the operator theorem. -/
theorem pcEquilibrium_iff_operatorEquilibrium {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) (x y : ℝ)
    (z : PCState (interior + 1)) :
    pcEquilibrium links x y z ↔
      z ∈ clampedStateSet x y ∧
        (pcLinearGaussianOperatorModel links x y).Equilibrium
          (pcInteriorCoordinates interior z) := by
  constructor
  · intro hz
    refine ⟨hz.1, ?_⟩
    change IsMinOn (pcLinearGaussianOperatorModel links x y).energy Set.univ
      (pcInteriorCoordinates interior z)
    rw [isMinOn_univ_iff]
    intro u
    change pcConditionalCanonicalEnergy links x y
        (pcInteriorCoordinates interior z) ≤
      pcConditionalCanonicalEnergy links x y u
    rw [← pcEnergy_stateOfInterior_eq_canonical,
      ← pcEnergy_stateOfInterior_eq_canonical,
      pcStateOfInterior_coordinates_of_clamped interior x y z hz.1]
    exact (isMinOn_iff.mp hz.2) _
      (pcStateOfInterior_mem_clamped interior x y u)
  · rintro ⟨hzclamp, hzoperator⟩
    refine ⟨hzclamp, ?_⟩
    rw [isMinOn_iff]
    intro w hw
    change IsMinOn (pcLinearGaussianOperatorModel links x y).energy Set.univ
      (pcInteriorCoordinates interior z) at hzoperator
    have hle := (isMinOn_univ_iff.mp hzoperator)
      (pcInteriorCoordinates interior w)
    change pcConditionalCanonicalEnergy links x y
        (pcInteriorCoordinates interior z) ≤
      pcConditionalCanonicalEnergy links x y
        (pcInteriorCoordinates interior w) at hle
    rw [← pcEnergy_stateOfInterior_eq_canonical,
      ← pcEnergy_stateOfInterior_eq_canonical,
      pcStateOfInterior_coordinates_of_clamped interior x y z hzclamp,
      pcStateOfInterior_coordinates_of_clamped interior x y w hw] at hle
    exact hle

/-- The state assembled from the conditional posterior mean is a PC equilibrium. -/
theorem pcConditionalPosteriorMean_equilibrium {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) (x y : ℝ) :
    pcEquilibrium links x y
      (pcStateOfInterior interior x y (pcConditionalPosteriorMean links x y)) := by
  refine ⟨pcStateOfInterior_mem_clamped interior x y _, ?_⟩
  have hmin : ∀ u : PCInteriorSpace interior,
      pcEnergy links
          (pcStateOfInterior interior x y (pcConditionalPosteriorMean links x y)) ≤
        pcEnergy links (pcStateOfInterior interior x y u) := by
    simpa [IsMinOn, IsMinFilter] using
      (pcConditionalPosteriorMean_isMinOn links x y)
  intro z hz
  rw [← pcStateOfInterior_coordinates_of_clamped interior x y z hz]
  exact hmin _

/-- Arbitrary-length Bayesian semantics crown: a clamped PC state is an
equilibrium exactly when it is the conditional Gaussian posterior mean. -/
theorem pcEquilibrium_iff_eq_conditionalPosteriorMean {interior : ℕ}
    (links : Fin (interior + 1) → PCLink) (x y : ℝ)
    (z : PCState (interior + 1)) :
    pcEquilibrium links x y z ↔
      z = pcStateOfInterior interior x y
        (∫ u, u ∂pcConditionalPosterior links x y) := by
  constructor
  · intro hz
    have hadapter := (pcEquilibrium_iff_operatorEquilibrium links x y z).mp hz
    have hcoordinates : pcInteriorCoordinates interior z =
        ∫ u, u ∂pcConditionalPosterior links x y := by
      exact ((pcLinearGaussianOperatorModel links x y)
        |>.equilibrium_iff_eq_conditionalPosteriorMean
          (pcInteriorCoordinates interior z)).mp hadapter.2
    calc
      z = pcStateOfInterior interior x y
          (pcInteriorCoordinates interior z) :=
        (pcStateOfInterior_coordinates_of_clamped interior x y z hadapter.1).symm
      _ = pcStateOfInterior interior x y
          (∫ u, u ∂pcConditionalPosterior links x y) := by rw [hcoordinates]
  · intro hz
    subst z
    apply (pcEquilibrium_iff_operatorEquilibrium links x y _).mpr
    refine ⟨pcStateOfInterior_mem_clamped interior x y _, ?_⟩
    rw [pcInteriorCoordinates_stateOfInterior]
    exact ((pcLinearGaussianOperatorModel links x y)
      |>.equilibrium_iff_eq_conditionalPosteriorMean _).mpr rfl

/-- The one-interior-node depth-2 chain energy. -/
noncomputable def pcDepth2Energy (x y gain₀ gain₁ precision₀ precision₁ z₁ : ℝ) : ℝ :=
  precision₀ * (z₁ - gain₀ * x)^2 + precision₁ * (y - gain₁ * z₁)^2

/-- The unique depth-2 MAP/equilibrium interior value. -/
noncomputable def pcDepth2MAP (x y gain₀ gain₁ precision₀ precision₁ : ℝ) : ℝ :=
  (precision₀ * gain₀ * x + precision₁ * gain₁ * y) /
    (precision₀ + precision₁ * gain₁^2)

/-- Depth-2 local normal equation at the single interior node. -/
def pcDepth2NormalEquation
    (x y gain₀ gain₁ precision₀ precision₁ z₁ : ℝ) : Prop :=
  precision₀ * (z₁ - gain₀ * x) =
    precision₁ * gain₁ * (y - gain₁ * z₁)

theorem pcDepth2_den_pos (gain₁ precision₀ precision₁ : ℝ)
    (hprecision₀ : 0 < precision₀) (hprecision₁ : 0 < precision₁) :
    0 < precision₀ + precision₁ * gain₁^2 := by
  have hsquare : 0 ≤ gain₁^2 := sq_nonneg gain₁
  nlinarith

theorem pcDepth2Energy_sub_map_eq_square
    (x y gain₀ gain₁ precision₀ precision₁ z₁ : ℝ)
    (hden : precision₀ + precision₁ * gain₁^2 ≠ 0) :
    pcDepth2Energy x y gain₀ gain₁ precision₀ precision₁ z₁ -
        pcDepth2Energy x y gain₀ gain₁ precision₀ precision₁
          (pcDepth2MAP x y gain₀ gain₁ precision₀ precision₁) =
      (precision₀ + precision₁ * gain₁^2) *
        (z₁ - pcDepth2MAP x y gain₀ gain₁ precision₀ precision₁)^2 := by
  unfold pcDepth2Energy pcDepth2MAP
  field_simp [hden]
  ring

theorem pcDepth2MAP_isMinOn_energy
    (x y gain₀ gain₁ precision₀ precision₁ : ℝ)
    (hprecision₀ : 0 < precision₀) (hprecision₁ : 0 < precision₁) :
    IsMinOn (pcDepth2Energy x y gain₀ gain₁ precision₀ precision₁) Set.univ
      (pcDepth2MAP x y gain₀ gain₁ precision₀ precision₁) := by
  intro z₁ _hz₁
  have hden_pos := pcDepth2_den_pos gain₁ precision₀ precision₁ hprecision₀ hprecision₁
  have hden : precision₀ + precision₁ * gain₁^2 ≠ 0 := ne_of_gt hden_pos
  have hdiff :=
    pcDepth2Energy_sub_map_eq_square x y gain₀ gain₁ precision₀ precision₁ z₁ hden
  have hnonneg :
      0 ≤ pcDepth2Energy x y gain₀ gain₁ precision₀ precision₁ z₁ -
        pcDepth2Energy x y gain₀ gain₁ precision₀ precision₁
          (pcDepth2MAP x y gain₀ gain₁ precision₀ precision₁) := by
    rw [hdiff]
    exact mul_nonneg (le_of_lt hden_pos) (sq_nonneg _)
  exact sub_nonneg.mp hnonneg

theorem pcDepth2NormalEquation_iff_eq_map
    (x y gain₀ gain₁ precision₀ precision₁ z₁ : ℝ)
    (hprecision₀ : 0 < precision₀) (hprecision₁ : 0 < precision₁) :
    pcDepth2NormalEquation x y gain₀ gain₁ precision₀ precision₁ z₁ ↔
      z₁ = pcDepth2MAP x y gain₀ gain₁ precision₀ precision₁ := by
  have hden_pos := pcDepth2_den_pos gain₁ precision₀ precision₁ hprecision₀ hprecision₁
  have hden : precision₀ + precision₁ * gain₁^2 ≠ 0 := ne_of_gt hden_pos
  constructor
  · intro h
    unfold pcDepth2NormalEquation at h
    unfold pcDepth2MAP
    field_simp [hden]
    nlinarith
  · intro hz
    unfold pcDepth2NormalEquation
    unfold pcDepth2MAP at hz
    subst z₁
    field_simp [hden]
    ring

/-! ### Scalar Kalman correspondence -/

/-- The two links of a chain with one latent interior node. -/
noncomputable def pcDepthTwoLinks
    (gain₀ gain₁ precision₀ precision₁ : ℝ)
    (hprecision₀ : 0 < precision₀) (hprecision₁ : 0 < precision₁) :
    Fin 2 → PCLink :=
  fun edge =>
    if edge.val = 0 then
      { gain := gain₀, precision := precision₀, precision_pos := hprecision₀ }
    else
      { gain := gain₁, precision := precision₁, precision_pos := hprecision₁ }

/-- The arbitrary-chain posterior mean specializes to the closed-form
one-interior-node MAP value. -/
theorem pcConditionalPosteriorMean_depthTwo_eq_map
    (x y gain₀ gain₁ precision₀ precision₁ : ℝ)
    (hprecision₀ : 0 < precision₀) (hprecision₁ : 0 < precision₁) :
    pcConditionalPosteriorMean
        (pcDepthTwoLinks gain₀ gain₁ precision₀ precision₁ hprecision₀ hprecision₁)
        x y 0 =
      pcDepth2MAP x y gain₀ gain₁ precision₀ precision₁ := by
  let links := pcDepthTwoLinks gain₀ gain₁ precision₀ precision₁
    hprecision₀ hprecision₁
  let m := pcConditionalPosteriorMean links x y
  have heq := pcConditionalPosteriorMean_equilibrium links x y
  have hnorm := (pcEquilibrium_iff_normalEquations links x y
    (pcStateOfInterior 1 x y m)).mp heq |>.2
  have hnode := hnorm (⟨1, by omega⟩ : Fin 3)
  have hnormal :
      pcDepth2NormalEquation x y gain₀ gain₁ precision₀ precision₁ (m 0) := by
    have hstate1 : pcStateOfInterior 1 x y m (1 : Fin 3) = m 0 := by
      simpa using pcStateOfInterior_interior 1 x y m (0 : Fin 1)
    have hstate2 : pcStateOfInterior 1 x y m (2 : Fin 3) = y := by
      simpa using pcStateOfInterior_last 1 x y m
    simpa [pcLocalNormalEquationAt, links, pcDepthTwoLinks, pcResidual,
      hstate1, hstate2, pcDepth2NormalEquation] using hnode
  exact (pcDepth2NormalEquation_iff_eq_map x y gain₀ gain₁ precision₀ precision₁
    (m 0) hprecision₀ hprecision₁).mp hnormal

/-- Scalar Kalman gain for observation model `y = observationGain * latent + noise`. -/
noncomputable def scalarKalmanGain
    (observationGain priorPrecision observationPrecision : ℝ) : ℝ :=
  observationPrecision * observationGain /
    (priorPrecision + observationPrecision * observationGain ^ 2)

/-- Scalar Kalman posterior update from a prior mean and one observation. -/
noncomputable def scalarKalmanUpdate
    (priorMean observation observationGain priorPrecision observationPrecision : ℝ) : ℝ :=
  priorMean + scalarKalmanGain observationGain priorPrecision observationPrecision *
    (observation - observationGain * priorMean)

theorem pcDepth2MAP_eq_scalarKalmanUpdate
    (x y gain₀ gain₁ precision₀ precision₁ : ℝ)
    (hprecision₀ : 0 < precision₀) (hprecision₁ : 0 < precision₁) :
    pcDepth2MAP x y gain₀ gain₁ precision₀ precision₁ =
      scalarKalmanUpdate (gain₀ * x) y gain₁ precision₀ precision₁ := by
  have hden := ne_of_gt
    (pcDepth2_den_pos gain₁ precision₀ precision₁ hprecision₀ hprecision₁)
  unfold pcDepth2MAP scalarKalmanUpdate scalarKalmanGain
  field_simp [hden]
  ring

/-- Scalar Kalman crown: the probabilistic mean of the conditioned chain is
exactly the Kalman posterior update. -/
theorem pcConditionalPosteriorMean_depthTwo_eq_scalarKalmanUpdate
    (x y gain₀ gain₁ precision₀ precision₁ : ℝ)
    (hprecision₀ : 0 < precision₀) (hprecision₁ : 0 < precision₁) :
    pcConditionalPosteriorMean
        (pcDepthTwoLinks gain₀ gain₁ precision₀ precision₁ hprecision₀ hprecision₁)
        x y 0 =
      scalarKalmanUpdate (gain₀ * x) y gain₁ precision₀ precision₁ := by
  rw [pcConditionalPosteriorMean_depthTwo_eq_map x y gain₀ gain₁ precision₀ precision₁
    hprecision₀ hprecision₁]
  exact pcDepth2MAP_eq_scalarKalmanUpdate x y gain₀ gain₁ precision₀ precision₁
    hprecision₀ hprecision₁

/-- With unit observation gain, the one-interior-node posterior is exactly
the two-source Gaussian fusion primitive. -/
theorem pcDepth2MAP_eq_gaussianFusion_unitObservation
    (x y gain₀ precision₀ precision₁ : ℝ) :
    pcDepth2MAP x y gain₀ 1 precision₀ precision₁ =
      gaussianFusion (gain₀ * x) y precision₀ precision₁ := by
  unfold pcDepth2MAP gaussianFusion
  ring

/-- `GaussianFusion` is the one-interior-node, unit-observation base case of
the arbitrary-length conditional-posterior theorem. -/
theorem pcConditionalPosteriorMean_depthTwo_eq_gaussianFusion
    (x y gain₀ precision₀ precision₁ : ℝ)
    (hprecision₀ : 0 < precision₀) (hprecision₁ : 0 < precision₁) :
    pcConditionalPosteriorMean
        (pcDepthTwoLinks gain₀ 1 precision₀ precision₁ hprecision₀ hprecision₁)
        x y 0 =
      gaussianFusion (gain₀ * x) y precision₀ precision₁ := by
  rw [pcConditionalPosteriorMean_depthTwo_eq_map x y gain₀ 1 precision₀ precision₁
    hprecision₀ hprecision₁]
  exact pcDepth2MAP_eq_gaussianFusion_unitObservation x y gain₀ precision₀ precision₁

theorem pcConditionalPosteriorMean_depthTwo_positive :
    pcConditionalPosteriorMean
        (pcDepthTwoLinks 1 1 1 1 (by norm_num) (by norm_num)) 1 2 0 =
      3 / 2 := by
  rw [pcConditionalPosteriorMean_depthTwo_eq_map]
  norm_num [pcDepth2MAP]

/-- Negative fixture: conditioning blends finite-precision evidence rather
than replacing the latent state by the observation. -/
theorem pcConditionalPosteriorMean_depthTwo_ne_observation :
    pcConditionalPosteriorMean
        (pcDepthTwoLinks 1 1 1 1 (by norm_num) (by norm_num)) 1 2 0 ≠ 2 := by
  rw [pcConditionalPosteriorMean_depthTwo_positive]
  norm_num

/-- Depth-2 scaffold: the single local normal equation is equivalent to MAP. -/
theorem pcDepth2Equilibrium_iff_normalEquation
    (x y gain₀ gain₁ precision₀ precision₁ z₁ : ℝ)
    (hprecision₀ : 0 < precision₀) (hprecision₁ : 0 < precision₁) :
    IsMinOn (pcDepth2Energy x y gain₀ gain₁ precision₀ precision₁) Set.univ z₁ ↔
      pcDepth2NormalEquation x y gain₀ gain₁ precision₀ precision₁ z₁ := by
  have hden_pos := pcDepth2_den_pos gain₁ precision₀ precision₁ hprecision₀ hprecision₁
  have hden : precision₀ + precision₁ * gain₁^2 ≠ 0 := ne_of_gt hden_pos
  have hnormal_iff :=
    pcDepth2NormalEquation_iff_eq_map
      x y gain₀ gain₁ precision₀ precision₁ z₁ hprecision₀ hprecision₁
  have hmap_min :=
    pcDepth2MAP_isMinOn_energy x y gain₀ gain₁ precision₀ precision₁
      hprecision₀ hprecision₁
  constructor
  · intro hmin
    rw [hnormal_iff]
    have hmin_forall :
        ∀ u ∈ (Set.univ : Set ℝ),
          pcDepth2Energy x y gain₀ gain₁ precision₀ precision₁ z₁ ≤
            pcDepth2Energy x y gain₀ gain₁ precision₀ precision₁ u := by
      simpa [IsMinOn, IsMinFilter] using hmin
    have hmap_forall :
        ∀ u ∈ (Set.univ : Set ℝ),
          pcDepth2Energy x y gain₀ gain₁ precision₀ precision₁
              (pcDepth2MAP x y gain₀ gain₁ precision₀ precision₁) ≤
            pcDepth2Energy x y gain₀ gain₁ precision₀ precision₁ u := by
      simpa [IsMinOn, IsMinFilter] using hmap_min
    have hle_from_z₁ :=
      hmin_forall (pcDepth2MAP x y gain₀ gain₁ precision₀ precision₁) trivial
    have hle_from_map := hmap_forall z₁ trivial
    have henergy :
        pcDepth2Energy x y gain₀ gain₁ precision₀ precision₁ z₁ =
          pcDepth2Energy x y gain₀ gain₁ precision₀ precision₁
            (pcDepth2MAP x y gain₀ gain₁ precision₀ precision₁) :=
      le_antisymm hle_from_z₁ hle_from_map
    have hdiff :=
      pcDepth2Energy_sub_map_eq_square x y gain₀ gain₁ precision₀ precision₁ z₁ hden
    have hprod :
        (precision₀ + precision₁ * gain₁^2) *
            (z₁ - pcDepth2MAP x y gain₀ gain₁ precision₀ precision₁)^2 = 0 := by
      rw [← hdiff, henergy]
      ring
    have hsquare :
        (z₁ - pcDepth2MAP x y gain₀ gain₁ precision₀ precision₁)^2 = 0 := by
      exact (mul_eq_zero.mp hprod).resolve_left hden
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  · intro hnormal
    rw [hnormal_iff] at hnormal
    subst z₁
    exact hmap_min

theorem pcDepth2_fixture_normalEquation :
    pcDepth2NormalEquation 1 2 1 1 1 1 (3 / 2 : ℝ) := by
  norm_num [pcDepth2NormalEquation]

theorem pcDepth2_fixture_equilibrium :
    IsMinOn (pcDepth2Energy 1 2 1 1 1 1) Set.univ (3 / 2 : ℝ) := by
  rw [pcDepth2Equilibrium_iff_normalEquation]
  · exact pcDepth2_fixture_normalEquation
  · norm_num
  · norm_num

theorem pcDepth2_shifted_state_has_larger_energy :
    pcDepth2Energy 1 2 1 1 1 1 (3 / 2 : ℝ) <
      pcDepth2Energy 1 2 1 1 1 1 0 := by
  norm_num [pcDepth2Energy]

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
