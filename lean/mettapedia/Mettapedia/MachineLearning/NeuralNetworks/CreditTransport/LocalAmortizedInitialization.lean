import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.PrimalDualStability

/-!
# Local amortized initialization for nonlinear credit solvers

Global contraction is stronger than the guarantee normally available for a
nonlinear residual solver.  This file isolates the local certificate actually
needed by an amortized initializer: a closed invariant neighborhood, pairwise
contraction inside that neighborhood, and a fixed point inside it.  These data
give finite-step initializer bounds, local fixed-point uniqueness, and a
residual-based stopping rule without promoting a local linearization to a
global statement.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace LocalAmortizedInitialization

open AmortizedInitialization
open PrimalDualStability

variable {State : Type*} [NormedAddCommGroup State]

/-- Membership in the closed norm ball used to certify a local solver. -/
def InClosedBall (center : State) (radius : ℝ) (state : State) : Prop :=
  ‖state - center‖ ≤ radius

/-- A contraction certificate whose obligations are restricted to one
explicit invariant neighborhood. -/
structure LocalContractionCertificate (solver : State → State)
    (center : State) (radius : ℝ) where
  factor : ℝ
  factor_nonneg : 0 ≤ factor
  factor_lt_one : factor < 1
  radius_nonneg : 0 ≤ radius
  maps_ball : ∀ state, InClosedBall center radius state →
    InClosedBall center radius (solver state)
  contracts_on_ball : ∀ left right,
    InClosedBall center radius left → InClosedBall center radius right →
    ‖solver left - solver right‖ ≤ factor * ‖left - right‖

/-- Every finite solver iterate remains in the declared neighborhood. -/
theorem iterate_mem_closedBall
    {solver : State → State} {center : State} {radius : ℝ}
    (certificate : LocalContractionCertificate solver center radius)
    (initial : State) (hinitial : InClosedBall center radius initial)
    (steps : ℕ) :
    InClosedBall center radius (solver^[steps] initial) := by
  induction steps with
  | zero => simpa using hinitial
  | succ steps inductionHypothesis =>
      rw [Function.iterate_succ_apply']
      exact certificate.maps_ball _ inductionHypothesis

/-- A local contraction has at most one fixed point inside its certified
neighborhood. -/
theorem fixedPoint_unique_in_closedBall
    {solver : State → State} {center : State} {radius : ℝ}
    (certificate : LocalContractionCertificate solver center radius)
    {left right : State}
    (hleftMem : InClosedBall center radius left)
    (hrightMem : InClosedBall center radius right)
    (hleft : IsFixedPoint solver left) (hright : IsFixedPoint solver right) :
    left = right := by
  have hcontract := certificate.contracts_on_ball left right hleftMem hrightMem
  rw [hleft, hright] at hcontract
  have hzero : ‖left - right‖ = 0 := by
    by_contra hne
    have hpositive : 0 < ‖left - right‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have hstrict :
        certificate.factor * ‖left - right‖ < ‖left - right‖ := by
      simpa using mul_lt_mul_of_pos_right certificate.factor_lt_one hpositive
    exact (not_lt_of_ge hcontract) hstrict
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

/-- Pairwise dependence on two initializers decays geometrically for as long
as both trajectories start in the invariant neighborhood. -/
theorem iterate_initializer_distance_le
    {solver : State → State} {center : State} {radius : ℝ}
    (certificate : LocalContractionCertificate solver center radius)
    (left right : State)
    (hleft : InClosedBall center radius left)
    (hright : InClosedBall center radius right)
    (steps : ℕ) :
    ‖solver^[steps] left - solver^[steps] right‖ ≤
      certificate.factor ^ steps * ‖left - right‖ := by
  induction steps with
  | zero => simp
  | succ steps inductionHypothesis =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', pow_succ]
      calc
        ‖solver (solver^[steps] left) - solver (solver^[steps] right)‖ ≤
            certificate.factor *
              ‖solver^[steps] left - solver^[steps] right‖ :=
          certificate.contracts_on_ball _ _
            (iterate_mem_closedBall certificate left hleft steps)
            (iterate_mem_closedBall certificate right hright steps)
        _ ≤ certificate.factor *
              (certificate.factor ^ steps * ‖left - right‖) := by
          exact mul_le_mul_of_nonneg_left inductionHypothesis
            certificate.factor_nonneg
        _ = certificate.factor ^ steps.succ * ‖left - right‖ := by
          rw [pow_succ']
          ac_rfl

/-- A locally valid amortized initializer converges geometrically toward any
fixed point in the same certified neighborhood. -/
theorem iterate_initializer_to_fixedPoint_le
    {solver : State → State} {center : State} {radius : ℝ}
    (certificate : LocalContractionCertificate solver center radius)
    (target initial : State)
    (htargetMem : InClosedBall center radius target)
    (hinitial : InClosedBall center radius initial)
    (htarget : IsFixedPoint solver target) (steps : ℕ) :
    ‖solver^[steps] initial - target‖ ≤
      certificate.factor ^ steps * ‖initial - target‖ := by
  have htargetIterate : solver^[steps] target = target := by
    induction steps with
    | zero => simp
    | succ steps inductionHypothesis =>
        rw [Function.iterate_succ_apply', inductionHypothesis, htarget]
  simpa [htargetIterate] using
    iterate_initializer_distance_le certificate initial target
      hinitial htargetMem steps

/-- Inside the invariant neighborhood, the observable residual controls
distance to the local fixed point. -/
theorem fixedPoint_distance_le_residual_div
    {solver : State → State} {center : State} {radius : ℝ}
    (certificate : LocalContractionCertificate solver center radius)
    (target state : State)
    (htargetMem : InClosedBall center radius target)
    (hstateMem : InClosedBall center radius state)
    (htarget : IsFixedPoint solver target) :
    ‖state - target‖ ≤
      ‖state - solver state‖ / (1 - certificate.factor) := by
  have honeMinus : 0 < 1 - certificate.factor := by
    linarith [certificate.factor_lt_one]
  have htriangle :
      ‖state - target‖ ≤
        ‖state - solver state‖ + ‖solver state - target‖ := by
    have hraw := norm_add_le
      (state - solver state) (solver state - solver target)
    rw [htarget] at hraw
    simpa [sub_eq_add_neg, add_assoc] using hraw
  have hcontract :=
    certificate.contracts_on_ball state target hstateMem htargetMem
  rw [htarget] at hcontract
  apply (le_div_iff₀ honeMinus).2
  nlinarith

/-- A residual threshold gives an adaptive stopping rule provided the current
state remains inside the declared local neighborhood. -/
theorem residual_adaptiveStop
    {solver : State → State} {center : State} {radius : ℝ}
    (certificate : LocalContractionCertificate solver center radius)
    (target state : State)
    (htargetMem : InClosedBall center radius target)
    (hstateMem : InClosedBall center radius state)
    (htarget : IsFixedPoint solver target)
    (tolerance : ℝ)
    (hresidual :
      ‖state - solver state‖ < (1 - certificate.factor) * tolerance) :
    ‖state - target‖ < tolerance := by
  have honeMinus : 0 < 1 - certificate.factor := by
    linarith [certificate.factor_lt_one]
  have hbound := fixedPoint_distance_le_residual_div certificate
    target state htargetMem hstateMem htarget
  have hresidualDiv :
      ‖state - solver state‖ / (1 - certificate.factor) < tolerance :=
    (div_lt_iff₀ honeMinus).2 (by simpa [mul_comm] using hresidual)
  exact lt_of_le_of_lt hbound hresidualDiv

/-! ## Nonlinear executable instance and its global boundary -/

/-- Pairwise contraction of the quadratic residual map on the unit ball. -/
theorem localQuadraticErrorMap_pair_distance_le
    (left right : ℝ) (hleft : |left| ≤ 1) (hright : |right| ≤ 1) :
    |localQuadraticErrorMap left - localQuadraticErrorMap right| ≤
      (3 / 4 : ℝ) * |left - right| := by
  rcases abs_le.mp hleft with ⟨hleftLower, hleftUpper⟩
  rcases abs_le.mp hright with ⟨hrightLower, hrightUpper⟩
  have hcoefficient :
      |(1 / 4 : ℝ) + (left + right) / 4| ≤ 3 / 4 := by
    rw [abs_le]
    constructor <;> linarith
  have hdifference :
      localQuadraticErrorMap left - localQuadraticErrorMap right =
        (left - right) * ((1 / 4 : ℝ) + (left + right) / 4) := by
    simp [localQuadraticErrorMap, scalarQuadraticErrorMap]
    ring
  rw [hdifference, abs_mul]
  calc
    |left - right| * |(1 / 4 : ℝ) + (left + right) / 4| ≤
        |left - right| * (3 / 4) :=
      mul_le_mul_of_nonneg_left hcoefficient (abs_nonneg _)
    _ = (3 / 4 : ℝ) * |left - right| := by ring

noncomputable def localQuadraticCertificate :
    LocalContractionCertificate localQuadraticErrorMap 0 1 where
  factor := 3 / 4
  factor_nonneg := by norm_num
  factor_lt_one := by norm_num
  radius_nonneg := by norm_num
  maps_ball := by
    intro state hstate
    have hhalf := localQuadraticErrorMap_maps_unitBall_to_halfBall state
      (by simpa [InClosedBall, Real.norm_eq_abs] using hstate)
    simpa [InClosedBall, Real.norm_eq_abs] using (le_trans hhalf (by norm_num))
  contracts_on_ball := by
    intro left right hleft hright
    simpa [InClosedBall, Real.norm_eq_abs] using
      localQuadraticErrorMap_pair_distance_le left right
        (by simpa [InClosedBall, Real.norm_eq_abs] using hleft)
        (by simpa [InClosedBall, Real.norm_eq_abs] using hright)

theorem localQuadraticErrorMap_zero_fixed :
    IsFixedPoint localQuadraticErrorMap 0 := by
  norm_num [IsFixedPoint, localQuadraticErrorMap, scalarQuadraticErrorMap]

theorem localQuadratic_warmStart_bound_after_two :
    |localQuadraticErrorMap^[2] (1 / 4)| ≤
      (3 / 4 : ℝ) ^ 2 * |(1 / 4 : ℝ)| := by
  have htargetMem : InClosedBall (0 : ℝ) 1 0 := by
    norm_num [InClosedBall]
  have hinitial : InClosedBall (0 : ℝ) 1 (1 / 4) := by
    norm_num [InClosedBall, Real.norm_eq_abs]
  simpa [localQuadraticCertificate, Real.norm_eq_abs] using
    iterate_initializer_to_fixedPoint_le localQuadraticCertificate
      0 (1 / 4) htargetMem hinitial localQuadraticErrorMap_zero_fixed 2

theorem localQuadratic_residual_stops_at_tenth :
    |(1 / 10 : ℝ) - localQuadraticErrorMap (1 / 10)| <
      (1 - localQuadraticCertificate.factor) * (1 / 2) := by
  norm_num [localQuadraticCertificate, localQuadraticErrorMap,
    scalarQuadraticErrorMap, abs_of_nonneg]

theorem localQuadratic_tenth_within_half_of_fixedPoint :
    |(1 / 10 : ℝ) - 0| < 1 / 2 := by
  have htargetMem : InClosedBall (0 : ℝ) 1 0 := by
    norm_num [InClosedBall]
  have hstateMem : InClosedBall (0 : ℝ) 1 (1 / 10) := by
    norm_num [InClosedBall, Real.norm_eq_abs]
  simpa [Real.norm_eq_abs] using
    residual_adaptiveStop localQuadraticCertificate 0 (1 / 10)
      htargetMem hstateMem localQuadraticErrorMap_zero_fixed (1 / 2)
      localQuadratic_residual_stops_at_tenth

/-- The nonlinear fixture is locally contractive but admits no global
contraction certificate.  A local warm-start theorem therefore cannot be
silently promoted to a global solver guarantee. -/
theorem localQuadraticErrorMap_no_globalContractionCertificate :
    ¬ Nonempty (ContractionCertificate localQuadraticErrorMap) := by
  rintro ⟨certificate⟩
  have hcontract := certificate.contracts (4 : ℝ) 0
  have hzero : localQuadraticErrorMap 0 = 0 := by
    norm_num [localQuadraticErrorMap, scalarQuadraticErrorMap]
  have hfour : localQuadraticErrorMap 4 = 5 :=
    localQuadraticErrorMap_globalExpansion.1
  rw [hfour, hzero] at hcontract
  norm_num [Real.norm_eq_abs] at hcontract
  have hfactorBound : certificate.factor * 4 < 4 := by
    nlinarith [certificate.factor_lt_one]
  linarith

#print axioms iterate_mem_closedBall
#print axioms fixedPoint_unique_in_closedBall
#print axioms iterate_initializer_to_fixedPoint_le
#print axioms residual_adaptiveStop
#print axioms localQuadraticErrorMap_pair_distance_le
#print axioms localQuadratic_tenth_within_half_of_fixedPoint
#print axioms localQuadraticErrorMap_no_globalContractionCertificate

end LocalAmortizedInitialization

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
