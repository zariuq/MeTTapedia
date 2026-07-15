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
