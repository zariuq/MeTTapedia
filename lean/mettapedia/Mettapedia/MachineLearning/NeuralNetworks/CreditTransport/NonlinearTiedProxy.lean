import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT.HilbertGradient
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DirectionalTaskDescent

/-!
# Nonlinear tied-parameter proxy credit

Local and approximate credit rules are often described at one module or one
temporal occurrence, while the trained parameter is shared by many such
occurrences.  This file makes the missing aggregation explicit.  At a fixed
parameter point, each nonlinear use contributes its Fréchet derivative; local
credit is pulled back by the adjoint derivative and every tied occurrence is
summed.

The main results identify the exact aggregate proxy error, bound it by the sum
of occurrencewise derivative-weighted errors, connect that bound to finite
task descent, and recover the occurrence-aware KKT gradient when the local
credits are exact.  The fixtures show both cancellation and reinforcement:
nonzero local errors can cancel after tied aggregation, while equally small
same-sign errors accumulate and a stale proxy can reverse the aggregate
direction.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace NonlinearTiedProxy

open scoped InnerProductSpace

universe uOwner uOccurrence uNodeSpace uParameterSpace

variable {Owner : Type uOwner} [Fintype Owner]
variable (NodeSpace : Owner → Type uNodeSpace)
variable [∀ owner, NormedAddCommGroup (NodeSpace owner)]
variable [∀ owner, InnerProductSpace ℝ (NodeSpace owner)]
variable [∀ owner, CompleteSpace (NodeSpace owner)]

variable {ParameterSpace : Type uParameterSpace}
variable [NormedAddCommGroup ParameterSpace]
variable [InnerProductSpace ℝ ParameterSpace]
variable [CompleteSpace ParameterSpace]

variable (Occurrence : Owner → Type uOccurrence)
variable [∀ owner, Fintype (Occurrence owner)]

/-- Sum the adjoint-Jacobian credit from every active use of one shared
parameter.  Credits may differ between occurrences of the same owner, which
is needed for stale, asynchronous, or occurrence-conditioned proxies. -/
noncomputable def tiedOccurrenceUpdate
    (active : ∀ {owner}, Occurrence owner → Bool)
    (derivative : ∀ {owner}, Occurrence owner →
      ParameterSpace →L[ℝ] NodeSpace owner)
    (credit : ∀ owner, Occurrence owner → NodeSpace owner) : ParameterSpace :=
  ∑ owner, ∑ occurrence,
    if active occurrence then
      ContinuousLinearMap.adjoint (derivative occurrence)
        (credit owner occurrence)
    else 0

/-- The common special case in which every tied parameter use at one node
receives the same node credit. -/
noncomputable def tiedNodeCreditUpdate
    (active : ∀ {owner}, Occurrence owner → Bool)
    (derivative : ∀ {owner}, Occurrence owner →
      ParameterSpace →L[ℝ] NodeSpace owner)
    (credit : ∀ owner, NodeSpace owner) : ParameterSpace :=
  tiedOccurrenceUpdate NodeSpace Occurrence active derivative
    (fun owner _ => credit owner)

/-- Pointwise nonlinear specialization.  Each use may be a different
nonlinear map of the shared parameter; its derivative is taken at the actual
parameter point before local credit is aggregated. -/
noncomputable def tiedFDerivOccurrenceUpdate
    (active : ∀ {owner}, Occurrence owner → Bool)
    (localUse : ∀ owner, Occurrence owner → ParameterSpace → NodeSpace owner)
    (parameter : ParameterSpace)
    (credit : ∀ owner, Occurrence owner → NodeSpace owner) : ParameterSpace :=
  tiedOccurrenceUpdate NodeSpace Occurrence active
    (fun {owner} occurrence =>
      fderiv ℝ (localUse owner occurrence) parameter)
    credit

/-- Declared Fréchet derivatives of nonlinear tied uses recover the generic
adjoint-occurrence sum exactly. -/
theorem tiedFDerivOccurrenceUpdate_eq
    (active : ∀ {owner}, Occurrence owner → Bool)
    (localUse : ∀ owner, Occurrence owner → ParameterSpace → NodeSpace owner)
    (parameter : ParameterSpace)
    (derivative : ∀ {owner}, Occurrence owner →
      ParameterSpace →L[ℝ] NodeSpace owner)
    (credit : ∀ owner, Occurrence owner → NodeSpace owner)
    (hDerivative : ∀ owner occurrence,
      HasFDerivAt (localUse owner occurrence) (derivative occurrence) parameter) :
    tiedFDerivOccurrenceUpdate NodeSpace Occurrence active localUse parameter credit =
      tiedOccurrenceUpdate NodeSpace Occurrence active derivative credit := by
  simp only [tiedFDerivOccurrenceUpdate, tiedOccurrenceUpdate]
  apply Finset.sum_congr rfl
  intro owner _
  apply Finset.sum_congr rfl
  intro occurrence _
  rw [(hDerivative owner occurrence).fderiv]

/-- Exact decomposition of the shared-parameter update error.  Tied uses must
be aggregated before judging an approximate credit rule. -/
theorem tiedOccurrenceUpdate_sub
    (active : ∀ {owner}, Occurrence owner → Bool)
    (derivative : ∀ {owner}, Occurrence owner →
      ParameterSpace →L[ℝ] NodeSpace owner)
    (proxy exact : ∀ owner, Occurrence owner → NodeSpace owner) :
    tiedOccurrenceUpdate NodeSpace Occurrence active derivative proxy -
        tiedOccurrenceUpdate NodeSpace Occurrence active derivative exact =
      tiedOccurrenceUpdate NodeSpace Occurrence active derivative
        (fun owner occurrence => proxy owner occurrence - exact owner occurrence) := by
  simp only [tiedOccurrenceUpdate]
  calc
    (∑ owner, ∑ occurrence,
          if active occurrence then
            (derivative occurrence).adjoint (proxy owner occurrence)
          else 0) -
        (∑ owner, ∑ occurrence,
          if active occurrence then
            (derivative occurrence).adjoint (exact owner occurrence)
          else 0) =
        ∑ owner,
          ((∑ occurrence,
              if active occurrence then
                (derivative occurrence).adjoint (proxy owner occurrence)
              else 0) -
            (∑ occurrence,
              if active occurrence then
                (derivative occurrence).adjoint (exact owner occurrence)
              else 0)) := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ owner, ∑ occurrence,
          ((if active occurrence then
              (derivative occurrence).adjoint (proxy owner occurrence)
            else 0) -
          (if active occurrence then
              (derivative occurrence).adjoint (exact owner occurrence)
            else 0)) := by
          apply Finset.sum_congr rfl
          intro owner _
          rw [Finset.sum_sub_distrib]
    _ = ∑ owner, ∑ occurrence,
          if active occurrence then
            (derivative occurrence).adjoint
              (proxy owner occurrence - exact owner occurrence)
          else 0 := by
          apply Finset.sum_congr rfl
          intro owner _
          apply Finset.sum_congr rfl
          intro occurrence _
          by_cases enabled : active occurrence = true
          · simp [enabled, map_sub]
          · simp [enabled]

/-- Sum of derivative-weighted local proxy errors.  It is deliberately an
`L¹` occurrence budget: errors may cancel, so this is a sound upper bound and
not generally an equality. -/
noncomputable def tiedCreditErrorBudget
    (active : ∀ {owner}, Occurrence owner → Bool)
    (derivative : ∀ {owner}, Occurrence owner →
      ParameterSpace →L[ℝ] NodeSpace owner)
    (proxy exact : ∀ owner, Occurrence owner → NodeSpace owner) : ℝ :=
  ∑ owner, ∑ occurrence,
    if active occurrence then
      ‖derivative occurrence‖ *
        ‖proxy owner occurrence - exact owner occurrence‖
    else 0

/-- The aggregate shared-parameter error is bounded by the complete active
occurrence budget.  No tied use is silently discarded. -/
theorem norm_tiedOccurrenceUpdate_sub_le
    (active : ∀ {owner}, Occurrence owner → Bool)
    (derivative : ∀ {owner}, Occurrence owner →
      ParameterSpace →L[ℝ] NodeSpace owner)
    (proxy exact : ∀ owner, Occurrence owner → NodeSpace owner) :
    ‖tiedOccurrenceUpdate NodeSpace Occurrence active derivative proxy -
        tiedOccurrenceUpdate NodeSpace Occurrence active derivative exact‖ ≤
      tiedCreditErrorBudget NodeSpace Occurrence active derivative proxy exact := by
  rw [tiedOccurrenceUpdate_sub NodeSpace Occurrence]
  simp only [tiedOccurrenceUpdate, tiedCreditErrorBudget]
  calc
    ‖∑ owner, ∑ occurrence,
        if active occurrence then
          (derivative occurrence).adjoint
            (proxy owner occurrence - exact owner occurrence)
        else 0‖ ≤
        ∑ owner, ‖∑ occurrence,
          if active occurrence then
            (derivative occurrence).adjoint
              (proxy owner occurrence - exact owner occurrence)
          else 0‖ := norm_sum_le _ _
    _ ≤ ∑ owner, ∑ occurrence,
          ‖if active occurrence then
              (derivative occurrence).adjoint
                (proxy owner occurrence - exact owner occurrence)
            else 0‖ := by
          apply Finset.sum_le_sum
          intro owner _
          exact norm_sum_le _ _
    _ ≤ ∑ owner, ∑ occurrence,
          if active occurrence then
            ‖derivative occurrence‖ *
              ‖proxy owner occurrence - exact owner occurrence‖
          else 0 := by
          apply Finset.sum_le_sum
          intro owner _
          apply Finset.sum_le_sum
          intro occurrence _
          by_cases enabled : active occurrence = true
          · simp only [enabled, if_true]
            simpa using
              (ContinuousLinearMap.le_opNorm
                ((derivative occurrence).adjoint)
                (proxy owner occurrence - exact owner occurrence))
          · simp [enabled]

/-- A complete tied-occurrence proxy budget feeds the existing smooth-task
descent theorem.  The exact update is the reference gradient; the proxy update
is licensed only when the aggregate error and finite-step curvature budgets
both fit. -/
theorem smoothTask_strict_descent_of_tiedCreditError
    (loss : ParameterSpace → ℝ) (parameter : ParameterSpace)
    (active : ∀ {owner}, Occurrence owner → Bool)
    (derivative : ∀ {owner}, Occurrence owner →
      ParameterSpace →L[ℝ] NodeSpace owner)
    (proxy exact : ∀ owner, Occurrence owner → NodeSpace owner)
    (beta step : ℝ)
    (certificate : DirectionalTaskDescent.HasSmoothTaskUpperModelAt
      loss parameter
        (tiedOccurrenceUpdate NodeSpace Occurrence active derivative exact) beta)
    (hbeta : 0 ≤ beta) (hstep : 0 < step)
    (hrelative :
      tiedCreditErrorBudget NodeSpace Occurrence active derivative proxy exact <
        ‖tiedOccurrenceUpdate NodeSpace Occurrence active derivative exact‖)
    (htrust :
      beta * step *
          (‖tiedOccurrenceUpdate NodeSpace Occurrence active derivative exact‖ +
            tiedCreditErrorBudget NodeSpace Occurrence active derivative proxy exact) ^ 2 /
            2 <
        ‖tiedOccurrenceUpdate NodeSpace Occurrence active derivative exact‖ *
          (‖tiedOccurrenceUpdate NodeSpace Occurrence active derivative exact‖ -
            tiedCreditErrorBudget NodeSpace Occurrence active derivative proxy exact)) :
    loss (parameter - step •
        tiedOccurrenceUpdate NodeSpace Occurrence active derivative proxy) <
      loss parameter := by
  exact DirectionalTaskDescent.smoothTask_strict_descent_of_norm_error
    certificate
      (norm_tiedOccurrenceUpdate_sub_le NodeSpace Occurrence
        active derivative proxy exact)
      hbeta hstep hrelative htrust

/-! ## Exact bridge to occurrence-aware KKT gradients -/

open KKT

universe uParameter uParameterOccurrence

variable {Parameter : Type uParameter} [Fintype Parameter]
variable (ParameterOccurrence : Parameter → Owner → Type uParameterOccurrence)
variable [∀ parameter owner, Fintype (ParameterOccurrence parameter owner)]
variable (SharedParameterSpace : Parameter → Type uParameterSpace)
variable [∀ parameter, NormedAddCommGroup (SharedParameterSpace parameter)]
variable [∀ parameter, InnerProductSpace ℝ (SharedParameterSpace parameter)]
variable [∀ parameter, CompleteSpace (SharedParameterSpace parameter)]

omit [Fintype Parameter] in
/-- With exact node covectors, the generic tied-occurrence update is precisely
the non-direct part of the KKT parameter gradient already derived from the
actual residual Lagrangian. -/
theorem parameterCovectorGradient_tiedAggregate_eq_direct_add_tiedUpdate
    (active : ∀ {parameter owner},
      ParameterOccurrence parameter owner → Bool)
    (direct : ∀ parameter, ParameterCovector SharedParameterSpace parameter)
    (parameterDerivative : ∀ {parameter owner},
      ParameterOccurrence parameter owner →
        SharedParameterSpace parameter →L[ℝ] NodeSpace owner)
    (credit : ∀ owner, NodeCovector NodeSpace owner)
    (parameter : Parameter) :
    parameterCovectorGradient SharedParameterSpace
        (tiedParameterAggregate
          (NodeSpace := NodeSpace)
          (ParameterOccurrence := ParameterOccurrence)
          (ParameterSpace := SharedParameterSpace)
          active direct parameterDerivative credit parameter) =
      parameterCovectorGradient SharedParameterSpace (direct parameter) +
        tiedNodeCreditUpdate NodeSpace
          (fun owner => ParameterOccurrence parameter owner)
          (fun {_} occurrence => active occurrence)
          (fun {_} occurrence => parameterDerivative occurrence)
          (fun owner => covectorGradient NodeSpace (credit owner)) := by
  simpa [tiedNodeCreditUpdate, tiedOccurrenceUpdate] using
    (parameterCovectorGradient_tiedAggregate
      (NodeSpace := NodeSpace)
      (ParameterOccurrence := ParameterOccurrence)
      (ParameterSpace := SharedParameterSpace)
      active direct parameterDerivative credit parameter)

/-! ## Executable scalar fixtures -/

namespace Fixtures

abbrev ScalarOwner := Fin 1

abbrev TwoOccurrences (_ : ScalarOwner) := Fin 2

def allActive {owner : ScalarOwner} (_ : TwoOccurrences owner) : Bool := true

noncomputable def identityDerivative {owner : ScalarOwner}
    (_ : TwoOccurrences owner) : ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.id ℝ ℝ

def exactCredit (_ : ScalarOwner) (_ : Fin 2) : ℝ := 2

def cancellingProxy (_ : ScalarOwner) (occurrence : Fin 2) : ℝ :=
  if occurrence = 0 then 3 else 1

def reinforcingProxy (_ : ScalarOwner) (_ : Fin 2) : ℝ := 3

def reversedProxy (_ : ScalarOwner) (_ : Fin 2) : ℝ := -2

/-- Two nonzero local errors cancel after tied aggregation.  Therefore the
occurrencewise `L¹` error budget is sufficient but not necessary. -/
theorem cancelling_local_errors_preserve_tied_update :
    tiedOccurrenceUpdate (fun _ : ScalarOwner => ℝ) TwoOccurrences
        allActive identityDerivative cancellingProxy =
      tiedOccurrenceUpdate (fun _ : ScalarOwner => ℝ) TwoOccurrences
        allActive identityDerivative exactCredit ∧
    cancellingProxy 0 0 ≠ exactCredit 0 0 ∧
    cancellingProxy 0 1 ≠ exactCredit 0 1 := by
  norm_num [tiedOccurrenceUpdate, allActive, identityDerivative,
    cancellingProxy, exactCredit, Fin.sum_univ_two, Finset.univ_unique]

/-- Equal same-sign local errors reinforce: the aggregate error is twice the
error of either occurrence.  A bound that silently takes only one tied use is
unsound. -/
theorem reinforcing_local_errors_accumulate :
    ‖tiedOccurrenceUpdate (fun _ : ScalarOwner => ℝ) TwoOccurrences
          allActive identityDerivative reinforcingProxy -
        tiedOccurrenceUpdate (fun _ : ScalarOwner => ℝ) TwoOccurrences
          allActive identityDerivative exactCredit‖ = 2 ∧
      (∀ occurrence : Fin 2,
        ‖reinforcingProxy 0 occurrence - exactCredit 0 occurrence‖ = 1) := by
  constructor
  · norm_num [tiedOccurrenceUpdate, allActive, identityDerivative,
      reinforcingProxy, exactCredit, Fin.sum_univ_two, Finset.univ_unique]
  · intro occurrence
    norm_num [reinforcingProxy, exactCredit]

/-- A stale sign-reversed local proxy becomes an aggregate ascent direction
even though the shared-parameter occurrence accounting itself is exact. -/
theorem stale_proxy_reverses_tied_alignment :
    let exactUpdate :=
      tiedOccurrenceUpdate (fun _ : ScalarOwner => ℝ) TwoOccurrences
        allActive identityDerivative exactCredit
    let proxyUpdate :=
      tiedOccurrenceUpdate (fun _ : ScalarOwner => ℝ) TwoOccurrences
        allActive identityDerivative reversedProxy
    @inner ℝ ℝ _ exactUpdate proxyUpdate = -16 := by
  norm_num [tiedOccurrenceUpdate, allActive, identityDerivative,
    exactCredit, reversedProxy, Fin.sum_univ_two, Finset.univ_unique]

def squareUse (_ : ScalarOwner) (_ : Fin 2) (parameter : ℝ) : ℝ :=
  parameter ^ 2

/-- The nonlinear wrapper uses the actual derivative at the declared point:
two tied square uses at parameter two, each receiving unit credit, produce
aggregate update eight. -/
theorem nonlinear_square_uses_actual_point_derivative :
    tiedFDerivOccurrenceUpdate (fun _ : ScalarOwner => ℝ) TwoOccurrences
        allActive squareUse 2 (fun _ _ => 1) = 8 := by
  rw [tiedFDerivOccurrenceUpdate_eq
    (NodeSpace := fun _ : ScalarOwner => ℝ)
    (Occurrence := TwoOccurrences)
    (active := allActive)
    (localUse := squareUse)
    (parameter := 2)
    (derivative := fun {_} _ =>
      ContinuousLinearMap.toSpanSingleton ℝ (4 : ℝ))
    (credit := fun _ _ => 1)]
  · norm_num [tiedOccurrenceUpdate, allActive, Fin.sum_univ_two,
      Finset.univ_unique, ContinuousLinearMap.adjoint_toSpanSingleton]
  · intro owner occurrence
    change HasFDerivAt (fun parameter : ℝ => parameter ^ 2)
      (ContinuousLinearMap.toSpanSingleton ℝ (4 : ℝ)) 2
    have derivativeAtTwo := hasDerivAt_pow 2 (2 : ℝ)
    norm_num at derivativeAtTwo
    exact derivativeAtTwo.hasFDerivAt

end Fixtures

#print axioms tiedFDerivOccurrenceUpdate_eq
#print axioms tiedOccurrenceUpdate_sub
#print axioms norm_tiedOccurrenceUpdate_sub_le
#print axioms smoothTask_strict_descent_of_tiedCreditError
#print axioms parameterCovectorGradient_tiedAggregate_eq_direct_add_tiedUpdate
#print axioms Fixtures.cancelling_local_errors_preserve_tied_update
#print axioms Fixtures.reinforcing_local_errors_accumulate
#print axioms Fixtures.stale_proxy_reverses_tied_alignment
#print axioms Fixtures.nonlinear_square_uses_actual_point_derivative

end NonlinearTiedProxy

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
