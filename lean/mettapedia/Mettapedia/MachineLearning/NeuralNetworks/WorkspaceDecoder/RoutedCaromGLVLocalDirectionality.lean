import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromTwoPopulationCompiler

/-!
# Routed CAROM: local GLV directionality and passage time

Voit and Meyer-Ortmanns, *Hierarchical heteroclinic networks: controlling
the time evolution of complex systems* (2018, arXiv:1806.11039), study the
generalized Lotka--Volterra equation

`s_i' = rho * s_i - gamma * s_i^2 - sum_{j != i} A_ij * s_i * s_j`.

At the single-species equilibrium for resident `i`, a rare invader `j` has
linear rate `rho - A_ji * rho / gamma`.  Equations (3)--(7) of the source
choose predation rates so that two outgoing directions are unstable, the
small-cycle direction is faster, incoming directions dominate it in
contraction magnitude, and all remaining transverse directions are stable.

This file formalizes that local analytic layer.  It proves the exact
one-dimensional restriction and its derivative, recovers the source
parameter inequalities as if-and-only-if rate boundaries, packages them in
a reusable certificate, and connects the certificate to the exact
three-cycle graph compiler.  The linearized passage model also reaches a
threshold at an explicit logarithmic exit time and proves that a
nonpositive rate cannot reach a higher threshold.

The results are local.  They do not claim existence or asymptotic stability
of a global heteroclinic network, stochastic dwell-time laws, robustness
under perturbations, or realization by a trained routed carrier.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

namespace RoutedCarom

open Filter Topology

/-! ## The finite-species GLV vector field -/

/-- The source generalized Lotka--Volterra vector field.  The predation
matrix is indexed as `predation affected predator`, matching Equation (1). -/
noncomputable def glvVectorField
    {Species : Type*} [Fintype Species] [DecidableEq Species]
    (reproduction death : ℝ)
    (predation : Species → Species → ℝ)
    (state : Species → ℝ) (species : Species) : ℝ :=
  reproduction * state species - death * state species ^ 2 -
    ∑ other ∈ Finset.univ.erase species,
      predation species other * state species * state other

/-- The state in which exactly one resident species has abundance
`rho / gamma`. -/
noncomputable def singleSpeciesState
    {Species : Type*} [DecidableEq Species]
    (reproduction death : ℝ) (resident : Species) : Species → ℝ :=
  fun species =>
    if species = resident then reproduction / death else 0

/-- Every single-species state is an exact equilibrium of the finite GLV
field when the death rate is nonzero. -/
theorem glv_singleSpeciesState_is_equilibrium
    {Species : Type*} [Fintype Species] [DecidableEq Species]
    (reproduction death : ℝ)
    (predation : Species → Species → ℝ) (resident : Species)
    (hdeath : death ≠ 0) :
    glvVectorField reproduction death predation
      (singleSpeciesState reproduction death resident) = 0 := by
  funext species
  by_cases hspecies : species = resident
  · subst species
    simp only [glvVectorField, singleSpeciesState, if_pos, Pi.zero_apply]
    have hsum :
        (∑ other ∈ Finset.univ.erase resident,
          predation resident other * (reproduction / death) *
            (if other = resident then reproduction / death else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro other hother
      have hne : other ≠ resident := (Finset.mem_erase.mp hother).1
      simp [hne]
    rw [hsum]
    field_simp
    ring
  · simp [glvVectorField, singleSpeciesState, hspecies]

/-- A two-species probe retaining the resident equilibrium abundance and
giving one invader a variable abundance. -/
noncomputable def residentInvaderState
    {Species : Type*} [DecidableEq Species]
    (reproduction death : ℝ) (resident invader : Species)
    (abundance : ℝ) : Species → ℝ :=
  fun species =>
    if species = resident then reproduction / death
    else if species = invader then abundance
    else 0

/-! ## Single-species GLV linearization -/

/-- The linear growth rate of an invader when the resident is at its
single-species equilibrium `rho / gamma` and all other species are absent. -/
noncomputable def glvInvasionRate
    (reproduction death predation : ℝ) : ℝ :=
  reproduction - predation * reproduction / death

/-- Exact scalar restriction of the invader equation after the resident is
fixed at `rho / gamma`.  Its linearization at zero is `glvInvasionRate`. -/
noncomputable def glvInvaderField
    (reproduction death predation abundance : ℝ) : ℝ :=
  abundance *
    (glvInvasionRate reproduction death predation - death * abundance)

/-- The scalar invader field is not an independent model: it is exactly the
invader coordinate of the full finite-species GLV vector field on the
resident--invader probe. -/
theorem glvVectorField_residentInvaderState_invader
    {Species : Type*} [Fintype Species] [DecidableEq Species]
    (reproduction death : ℝ)
    (predation : Species → Species → ℝ)
    (resident invader : Species) (abundance : ℝ)
    (hne : invader ≠ resident) :
    glvVectorField reproduction death predation
        (residentInvaderState reproduction death resident invader abundance)
        invader =
      glvInvaderField reproduction death
        (predation invader resident) abundance := by
  unfold glvVectorField residentInvaderState glvInvaderField
    glvInvasionRate
  simp only [if_neg hne, if_pos]
  have hsum :
      (∑ other ∈ Finset.univ.erase invader,
        predation invader other * abundance *
          (if other = resident then reproduction / death
          else if other = invader then abundance else 0)) =
        predation invader resident * abundance *
          (reproduction / death) := by
    rw [Finset.sum_eq_single resident]
    · simp
    · intro other hmem hother
      have hother_ne_invader : other ≠ invader :=
        (Finset.mem_erase.mp hmem).1
      simp [hother, hother_ne_invader]
    · simp [hne.symm]
  rw [hsum]
  ring

/-- The invasion rate is a positive scale times the gap between death and
predation.  This is the algebraic core of the source's Table 1. -/
theorem glvInvasionRate_eq_scale_mul_gap
    {reproduction death predation : ℝ} (hdeath : death ≠ 0) :
    glvInvasionRate reproduction death predation =
      (reproduction / death) * (death - predation) := by
  unfold glvInvasionRate
  field_simp

/-- The rate from Table 1 is the actual derivative of the nonlinear scalar
invader field at the single-species boundary. -/
theorem glvInvaderField_hasDerivAt_zero
    (reproduction death predation : ℝ) :
    HasDerivAt (glvInvaderField reproduction death predation)
      (glvInvasionRate reproduction death predation) 0 := by
  unfold glvInvaderField
  have hderiv := (hasDerivAt_id (0 : ℝ)).mul
    ((hasDerivAt_const (x := (0 : ℝ))
        (glvInvasionRate reproduction death predation)).sub
      ((hasDerivAt_id (0 : ℝ)).const_mul death))
  have heq :
      (fun abundance : ℝ => abundance *
          (glvInvasionRate reproduction death predation -
            death * abundance)) =ᶠ[𝓝 0]
        ((fun abundance : ℝ => id abundance) *
          ((fun _ : ℝ =>
              glvInvasionRate reproduction death predation) -
            fun abundance : ℝ => death * id abundance)) :=
    Filter.Eventually.of_forall fun _ => rfl
  exact (hderiv.congr_of_eventuallyEq heq).congr_deriv
    (by norm_num [id])

/-- A direction expands exactly when its predation rate is below the death
rate. -/
theorem glvInvasionRate_pos_iff
    {reproduction death predation : ℝ}
    (hreproduction : 0 < reproduction) (hdeath : 0 < death) :
    0 < glvInvasionRate reproduction death predation ↔
      predation < death := by
  rw [glvInvasionRate_eq_scale_mul_gap hdeath.ne']
  have hscale : 0 < reproduction / death :=
    div_pos hreproduction hdeath
  constructor <;> intro h
  · nlinarith
  · exact mul_pos hscale (sub_pos.mpr h)

/-- A direction contracts exactly when its predation rate is above the death
rate. -/
theorem glvInvasionRate_neg_iff
    {reproduction death predation : ℝ}
    (hreproduction : 0 < reproduction) (hdeath : 0 < death) :
    glvInvasionRate reproduction death predation < 0 ↔
      death < predation := by
  rw [glvInvasionRate_eq_scale_mul_gap hdeath.ne']
  have hscale : 0 < reproduction / death :=
    div_pos hreproduction hdeath
  constructor <;> intro h
  · nlinarith
  · exact mul_neg_of_pos_of_neg hscale (sub_neg.mpr h)

/-- Smaller predation gives a strictly larger invasion rate. -/
theorem glvInvasionRate_order_iff
    {reproduction death first second : ℝ}
    (hreproduction : 0 < reproduction) (hdeath : 0 < death) :
    glvInvasionRate reproduction death second <
        glvInvasionRate reproduction death first ↔
      first < second := by
  rw [glvInvasionRate_eq_scale_mul_gap hdeath.ne',
    glvInvasionRate_eq_scale_mul_gap hdeath.ne']
  have hscale : 0 < reproduction / death :=
    div_pos hreproduction hdeath
  constructor <;> intro h
  · nlinarith
  · exact mul_lt_mul_of_pos_left (sub_lt_sub_left h death) hscale

/-- Exact recovery of the source's contraction-dominance inequality:
`A_contract > 2 * gamma - A_expand` if and only if the contraction magnitude
exceeds the expansion rate. -/
theorem glvContractionDominates_iff
    {reproduction death expansionPredation contractionPredation : ℝ}
    (hreproduction : 0 < reproduction) (hdeath : 0 < death) :
    glvInvasionRate reproduction death expansionPredation <
        -glvInvasionRate reproduction death contractionPredation ↔
      2 * death - expansionPredation < contractionPredation := by
  rw [glvInvasionRate_eq_scale_mul_gap hdeath.ne',
    glvInvasionRate_eq_scale_mul_gap hdeath.ne']
  have hscale : 0 < reproduction / death :=
    div_pos hreproduction hdeath
  constructor <;> intro h <;> nlinarith

/-- Critical predation is a genuine boundary rather than an expanding or
contracting direction. -/
theorem glvInvasionRate_at_critical_predation
    {reproduction death : ℝ} (hdeath : death ≠ 0) :
    glvInvasionRate reproduction death death = 0 := by
  rw [glvInvasionRate_eq_scale_mul_gap hdeath]
  ring

/-! ## A reusable hierarchical local-rate certificate -/

/-- Source equations (3)--(7), separated from any particular nine-species
matrix.  The fields describe the five local direction classes at every
single-species saddle in the symmetric construction. -/
structure GLVLocalDirectionProfile where
  reproduction : ℝ
  death : ℝ
  smallExpansionPredation : ℝ
  largeExpansionPredation : ℝ
  smallContractionPredation : ℝ
  largeContractionPredation : ℝ
  transversePredation : ℝ
  reproduction_pos : 0 < reproduction
  death_pos : 0 < death
  smallExpansion_pos : 0 < smallExpansionPredation
  small_before_large :
    smallExpansionPredation < largeExpansionPredation
  large_below_death : largeExpansionPredation < death
  smallContraction_dominates :
    2 * death - smallExpansionPredation < smallContractionPredation
  largeContraction_dominates :
    2 * death - smallExpansionPredation < largeContractionPredation
  transverse_above_death : death < transversePredation

noncomputable def GLVLocalDirectionProfile.smallExpansionRate
    (profile : GLVLocalDirectionProfile) : ℝ :=
  glvInvasionRate profile.reproduction profile.death
    profile.smallExpansionPredation

noncomputable def GLVLocalDirectionProfile.largeExpansionRate
    (profile : GLVLocalDirectionProfile) : ℝ :=
  glvInvasionRate profile.reproduction profile.death
    profile.largeExpansionPredation

noncomputable def GLVLocalDirectionProfile.smallContractionRate
    (profile : GLVLocalDirectionProfile) : ℝ :=
  glvInvasionRate profile.reproduction profile.death
    profile.smallContractionPredation

noncomputable def GLVLocalDirectionProfile.largeContractionRate
    (profile : GLVLocalDirectionProfile) : ℝ :=
  glvInvasionRate profile.reproduction profile.death
    profile.largeContractionPredation

noncomputable def GLVLocalDirectionProfile.transverseRate
    (profile : GLVLocalDirectionProfile) : ℝ :=
  glvInvasionRate profile.reproduction profile.death
    profile.transversePredation

/-- Rate-level meaning of the source parameter inequalities. -/
structure GLVLocalDirectionCertificate
    (profile : GLVLocalDirectionProfile) : Prop where
  largeExpansion_pos : 0 < profile.largeExpansionRate
  smallExpansion_preferred :
    profile.largeExpansionRate < profile.smallExpansionRate
  smallContraction_dominates :
    profile.smallExpansionRate < -profile.smallContractionRate
  largeContraction_dominates :
    profile.smallExpansionRate < -profile.largeContractionRate
  smallContraction_neg : profile.smallContractionRate < 0
  largeContraction_neg : profile.largeContractionRate < 0
  transverse_neg : profile.transverseRate < 0

/-- Equations (3)--(7) imply the complete local sign and rate-order
certificate. -/
theorem GLVLocalDirectionProfile.certified_directionality
    (profile : GLVLocalDirectionProfile) :
    GLVLocalDirectionCertificate profile := by
  have hdeath_lt_smallContraction :
      profile.death < profile.smallContractionPredation := by
    nlinarith [profile.small_before_large, profile.large_below_death,
      profile.smallContraction_dominates]
  have hdeath_lt_largeContraction :
      profile.death < profile.largeContractionPredation := by
    nlinarith [profile.small_before_large, profile.large_below_death,
      profile.largeContraction_dominates]
  refine
    { largeExpansion_pos :=
        (glvInvasionRate_pos_iff profile.reproduction_pos
          profile.death_pos).2 profile.large_below_death
      smallExpansion_preferred :=
        (glvInvasionRate_order_iff profile.reproduction_pos
          profile.death_pos).2 profile.small_before_large
      smallContraction_dominates :=
        (glvContractionDominates_iff profile.reproduction_pos
          profile.death_pos).2 profile.smallContraction_dominates
      largeContraction_dominates :=
        (glvContractionDominates_iff profile.reproduction_pos
          profile.death_pos).2 profile.largeContraction_dominates
      smallContraction_neg :=
        (glvInvasionRate_neg_iff profile.reproduction_pos
          profile.death_pos).2 hdeath_lt_smallContraction
      largeContraction_neg :=
        (glvInvasionRate_neg_iff profile.reproduction_pos
          profile.death_pos).2 hdeath_lt_largeContraction
      transverse_neg :=
        (glvInvasionRate_neg_iff profile.reproduction_pos
          profile.death_pos).2 profile.transverse_above_death }

/-- The representative parameter choice from the source, kept as exact
rationals rather than decimal approximations. -/
noncomputable def standardHierarchicalGLVProfile :
    GLVLocalDirectionProfile where
  reproduction := 1
  death := 107 / 100
  smallExpansionPredation := 1 / 5
  largeExpansionPredation := 3 / 10
  smallContractionPredation := 2
  largeContractionPredation := 2
  transversePredation := 5 / 4
  reproduction_pos := by norm_num
  death_pos := by norm_num
  smallExpansion_pos := by norm_num
  small_before_large := by norm_num
  large_below_death := by norm_num
  smallContraction_dominates := by norm_num
  largeContraction_dominates := by norm_num
  transverse_above_death := by norm_num

/-- Exact, non-rounded rates for the source's representative profile. -/
theorem standardHierarchicalGLVProfile_exact_rates :
    standardHierarchicalGLVProfile.smallExpansionRate = 87 / 107 ∧
      standardHierarchicalGLVProfile.largeExpansionRate = 77 / 107 ∧
      standardHierarchicalGLVProfile.smallContractionRate = -93 / 107 ∧
      standardHierarchicalGLVProfile.largeContractionRate = -93 / 107 ∧
      standardHierarchicalGLVProfile.transverseRate = -18 / 107 := by
  norm_num [standardHierarchicalGLVProfile,
    GLVLocalDirectionProfile.smallExpansionRate,
    GLVLocalDirectionProfile.largeExpansionRate,
    GLVLocalDirectionProfile.smallContractionRate,
    GLVLocalDirectionProfile.largeContractionRate,
    GLVLocalDirectionProfile.transverseRate, glvInvasionRate]

/-! ## Binding the local rates to the finite graph compiler -/

/-- In the three-cycle fixture, a selected successor gets the small
outgoing predation rate; every other potential invader gets a contracting
rate. -/
noncomputable def threeCycleGLVPredation
    (invader resident : Fin 3) : ℝ :=
  if invader = resident + 1 then (1 / 5 : ℝ) else 2

/-- Executable graph-to-dynamics bridge: away from the radial direction, the
compiled three-cycle edges are exactly the positive local invasion
directions.  Thus the fixture has neither a missing nor a spurious unstable
transition. -/
theorem threeCycle_transition_iff_positive_invasion
    (resident invader : Fin 3) (hne : invader ≠ resident) :
    graphTransition threeCycleGraph resident invader ↔
      0 < glvInvasionRate 1 (107 / 100)
        (threeCycleGLVPredation invader resident) := by
  fin_cases resident <;> fin_cases invader <;>
    simp_all [graphTransition, threeCycleGraph, threeCycleGLVPredation,
      glvInvasionRate] <;>
    norm_num

/-- Negative fixture: a transverse predation rate below death makes that
direction unstable, so condition (6) cannot be dropped. -/
theorem below_death_transverse_direction_is_unstable :
    0 < glvInvasionRate 1 1 (1 / 2) := by
  norm_num [glvInvasionRate]

/-! ## Linearized passage and logarithmic dwell scaling -/

/-- Linearized abundance along one local eigendirection. -/
noncomputable def linearizedAbundance
    (rate initial time : ℝ) : ℝ :=
  initial * Real.exp (rate * time)

/-- Time at which positive linearized growth moves from `initial` to
`threshold`. -/
noncomputable def linearExitTime
    (rate initial threshold : ℝ) : ℝ :=
  Real.log (threshold / initial) / rate

/-- A positive linearized rate reaches the requested positive threshold at
the declared exit time. -/
theorem linearizedAbundance_at_exitTime
    {rate initial threshold : ℝ}
    (hrate : 0 < rate) (hinitial : 0 < initial)
    (hthreshold : 0 < threshold) :
    linearizedAbundance rate initial
      (linearExitTime rate initial threshold) = threshold := by
  unfold linearizedAbundance linearExitTime
  have hrate_ne : rate ≠ 0 := hrate.ne'
  rw [show rate * (Real.log (threshold / initial) / rate) =
      Real.log (threshold / initial) by
    exact mul_div_cancel₀ _ hrate_ne]
  rw [Real.exp_log (div_pos hthreshold hinitial)]
  exact mul_div_cancel₀ threshold hinitial.ne'

/-- The exit time is affine in the logarithm of the initial amplitude. -/
theorem linearExitTime_log_difference
    {rate initial threshold : ℝ}
    (hinitial : initial ≠ 0) (hthreshold : threshold ≠ 0) :
    linearExitTime rate initial threshold =
      (Real.log threshold - Real.log initial) / rate := by
  simp [linearExitTime, Real.log_div hthreshold hinitial]

/-- A positive expanding rate and a higher threshold give a positive passage
time. -/
theorem linearExitTime_pos
    {rate initial threshold : ℝ}
    (hrate : 0 < rate) (hinitial : 0 < initial)
    (hbelow : initial < threshold) :
    0 < linearExitTime rate initial threshold := by
  unfold linearExitTime
  apply div_pos
  · apply Real.log_pos
    exact (one_lt_div hinitial).2 hbelow
  · exact hrate

/-- At fixed positive rate and threshold, a larger positive initial
amplitude exits strictly sooner. -/
theorem linearExitTime_strictAnti_initial
    {rate firstInitial secondInitial threshold : ℝ}
    (hrate : 0 < rate) (hfirst : 0 < firstInitial)
    (hsecond : firstInitial < secondInitial)
    (hthreshold : 0 < threshold) :
    linearExitTime rate secondInitial threshold <
      linearExitTime rate firstInitial threshold := by
  unfold linearExitTime
  rw [div_lt_div_iff_of_pos_right hrate]
  apply Real.strictMonoOn_log
  · exact div_pos hthreshold (lt_trans hfirst hsecond)
  · exact div_pos hthreshold hfirst
  · exact div_lt_div_of_pos_left hthreshold hfirst hsecond

/-- Negative boundary: a nonpositive eigendirection never reaches a strictly
higher threshold at nonnegative time in the linearized model. -/
theorem nonpositive_rate_cannot_reach_higher_threshold
    {rate initial threshold time : ℝ}
    (hrate : rate ≤ 0) (hinitial : 0 < initial)
    (hthreshold : initial < threshold) (htime : 0 ≤ time) :
    linearizedAbundance rate initial time < threshold := by
  unfold linearizedAbundance
  have hproduct : rate * time ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hrate htime
  have hexp : Real.exp (rate * time) ≤ 1 :=
    Real.exp_le_one_iff.mpr hproduct
  have hbounded :
      initial * Real.exp (rate * time) ≤ initial := by
    nlinarith [Real.exp_nonneg (rate * time)]
  exact lt_of_le_of_lt hbounded hthreshold

#print axioms glv_singleSpeciesState_is_equilibrium
#print axioms glvVectorField_residentInvaderState_invader
#print axioms glvInvaderField_hasDerivAt_zero
#print axioms glvInvasionRate_pos_iff
#print axioms glvContractionDominates_iff
#print axioms GLVLocalDirectionProfile.certified_directionality
#print axioms threeCycle_transition_iff_positive_invasion
#print axioms linearizedAbundance_at_exitTime
#print axioms nonpositive_rate_cannot_reach_higher_threshold

end RoutedCarom

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
