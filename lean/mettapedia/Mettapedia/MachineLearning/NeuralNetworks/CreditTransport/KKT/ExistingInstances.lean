import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT.ForwardComposition
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT.OccurrenceExtensionality
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.ExactReverse

/-!
# Concrete occurrence-aware KKT instances

This module connects the general occurrence calculus to two executable scalar
computations: a shared residual diamond with a tied parameter, and an unrolled
two-step recurrence.  Both examples retain every use occurrence explicitly.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT

noncomputable section

/-- Scalar multiplication as a continuous linear map. -/
def scalarContinuousLinearMap (coefficient : ℝ) : ℝ →L[ℝ] ℝ :=
  coefficient • ContinuousLinearMap.id ℝ ℝ

/-- Reusable derivative certificate for a half-squared affine residual. -/
theorem halfSquaredAffine_hasFDerivAt
    (slope bias point : ℝ) :
    HasRealFDerivAt
      (fun input : ℝ => (scalarContinuousLinearMap slope input + bias) ^ 2 * 2⁻¹)
      (scalarContinuousLinearMap ((slope * point + bias) * slope)) point := by
  have linearAt : HasRealFDerivAt
      (fun input : ℝ => scalarContinuousLinearMap slope input + bias)
      (scalarContinuousLinearMap slope) point :=
    (scalarContinuousLinearMap slope).hasFDerivAt.add_const bias
  have raw := (linearAt.pow 2).mul_const (2⁻¹ : ℝ)
  apply raw.congr_fderiv
  apply ContinuousLinearMap.ext
  intro direction
  simp [scalarContinuousLinearMap]
  ring

/-! ## Shared residual diamond -/

/-- One potential occurrence per ordered pair; the graph mask determines
which of the four diamond edges are part of the differentiated computation. -/
abbrev sharedResidualOccurrence (_source _target : Fin 4) : Type := Unit

/-- The scalar diamond `x0 → {x1,x2} → x3`.  The Boolean mask removes the
second merge occurrence without deleting the independently computed `x2`. -/
def sharedResidualGraph (mask : Bool) :
    RankedOccurrenceDAG sharedResidualOccurrence where
  rank := fun node => node.val
  active := fun {source target} _ => decide (
    (source.val = 0 ∧ target.val = 1) ∨
    (source.val = 0 ∧ target.val = 2) ∨
    (source.val = 1 ∧ target.val = 3) ∨
    (mask = true ∧ source.val = 2 ∧ target.val = 3))
  forward := by
    intro source target _ active
    rcases of_decide_eq_true active with edge | edge | edge | edge
    · omega
    · omega
    · omega
    · omega

/-- Actual local state partials of
`x1 = θ x0`, `x2 = θ x0 + offset`, and `x3 = x1 + 2 x2`.
The fixed graph mask, not this table, decides whether the last partial enters
the differentiated problem. -/
def sharedResidualParentDerivative (theta : ℝ)
    {source target : Fin 4}
    (_occurrence : sharedResidualOccurrence source target) : ℝ →L[ℝ] ℝ :=
  if source.val = 0 ∧ (target.val = 1 ∨ target.val = 2) then
    scalarContinuousLinearMap theta
  else if source.val = 1 ∧ target.val = 3 then
    scalarContinuousLinearMap 1
  else if source.val = 2 ∧ target.val = 3 then
    scalarContinuousLinearMap 2
  else 0

/-- Reverse covectors for the active fixture
`x0=2, θ=3, offset=1, target=5`. -/
def sharedResidualActiveCredit : ∀ _node : Fin 4, ℝ →L[ℝ] ℝ :=
  fun node =>
    if node.val = 0 then scalarContinuousLinearMap 135
    else if node.val = 1 then scalarContinuousLinearMap 15
    else if node.val = 2 then scalarContinuousLinearMap 30
    else scalarContinuousLinearMap 15

/-- The shared input receives both child-occurrence pullbacks, `45 + 90`. -/
theorem sharedResidual_parentAggregate_active_eq_135 :
    RankedOccurrenceDAG.parentAggregate
        (ParentOccurrence := sharedResidualOccurrence)
        (NodeSpace := fun _ : Fin 4 => ℝ)
        (sharedResidualGraph true)
        (sharedResidualParentDerivative 3)
        sharedResidualActiveCredit 0 1 = 135 := by
  have two_ne_zero : (2 : Fin 4) ≠ 0 := by decide
  norm_num [RankedOccurrenceDAG.parentAggregate, sharedResidualGraph,
    sharedResidualOccurrence, sharedResidualParentDerivative,
    sharedResidualActiveCredit, scalarContinuousLinearMap, parentPullback,
    Fin.sum_univ_four, two_ne_zero]

/-- Keeping either shared-state branch alone loses the actual input credit. -/
theorem sharedResidual_single_parent_is_wrong :
    (45 : ℝ) ≠ 135 ∧ (90 : ℝ) ≠ 135 := by
  norm_num

/-- One potential use occurrence at every owner; only the two computed branch
nodes use the shared scalar parameter. -/
abbrev sharedResidualParameterOccurrence
    (_parameter : Unit) (_owner : Fin 4) : Type := Unit

def sharedResidualParameterActive
    {parameter : Unit} {owner : Fin 4}
    (_occurrence : sharedResidualParameterOccurrence parameter owner) : Bool :=
  decide (owner.val = 1 ∨ owner.val = 2)

/-- At the fixture input `x0=2`, each tied use has local derivative two. -/
def sharedResidualParameterDerivative
    {parameter : Unit} {owner : Fin 4}
    (_occurrence : sharedResidualParameterOccurrence parameter owner) : ℝ →L[ℝ] ℝ :=
  scalarContinuousLinearMap 2

def sharedResidualZeroParameterDirect : ∀ _parameter : Unit, ℝ →L[ℝ] ℝ :=
  fun _ => 0

/-- The tied parameter derivative is the occurrence sum `30 + 60 = 90`. -/
theorem sharedResidual_tiedParameterAggregate_active_eq_90 :
    tiedParameterAggregate
        (NodeSpace := fun _ : Fin 4 => ℝ)
        (ParameterOccurrence := sharedResidualParameterOccurrence)
        (ParameterSpace := fun _ : Unit => ℝ)
        sharedResidualParameterActive sharedResidualZeroParameterDirect
        sharedResidualParameterDerivative sharedResidualActiveCredit () 1 = 90 := by
  have two_ne_zero : (2 : Fin 4) ≠ 0 := by decide
  norm_num [tiedParameterAggregate, sharedResidualParameterOccurrence,
    sharedResidualParameterActive, sharedResidualZeroParameterDirect,
    sharedResidualParameterDerivative, sharedResidualActiveCredit,
    scalarContinuousLinearMap, Fin.sum_univ_four, two_ne_zero]

/-- The active diamond's actual scalar task objective. -/
def sharedResidualActiveTask (theta : ℝ) : ℝ :=
  let x0 : ℝ := 2
  let x1 := theta * x0
  let x2 := theta * x0 + 1
  let x3 := x1 + 2 * x2
  (x3 - 5) ^ 2 / 2

/-- The occurrence sum agrees with the derivative of the actual composed
forward computation, rather than a substituted gradient label. -/
theorem sharedResidualActiveTask_hasDerivAt :
    HasRealFDerivAt sharedResidualActiveTask
      (scalarContinuousLinearMap 90) 3 := by
  have polynomial := halfSquaredAffine_hasFDerivAt 6 (-3) 3
  have derivativeEq :
      scalarContinuousLinearMap ((6 * 3 + (-3)) * 6) =
        scalarContinuousLinearMap 90 := by
    norm_num
  have polynomial90 := polynomial.congr_fderiv derivativeEq
  have taskEq : sharedResidualActiveTask =ᶠ[nhds (3 : ℝ)]
      fun theta => (scalarContinuousLinearMap 6 theta + (-3)) ^ 2 * 2⁻¹ :=
    Filter.Eventually.of_forall fun theta => by
      simp [sharedResidualActiveTask, scalarContinuousLinearMap]
      ring
  exact polynomial90.congr_of_eventuallyEq taskEq

/-- Reverse covectors for the same fixture with the second merge occurrence
masked out. -/
def sharedResidualMaskedCredit : ∀ _node : Fin 4, ℝ →L[ℝ] ℝ :=
  fun node =>
    if node.val = 0 then scalarContinuousLinearMap 3
    else if node.val = 1 then scalarContinuousLinearMap 1
    else if node.val = 2 then 0
    else scalarContinuousLinearMap 1

/-- The fixed mask removes the second shared-state contribution. -/
theorem sharedResidual_parentAggregate_masked_eq_3 :
    RankedOccurrenceDAG.parentAggregate
        (ParentOccurrence := sharedResidualOccurrence)
        (NodeSpace := fun _ : Fin 4 => ℝ)
        (sharedResidualGraph false)
        (sharedResidualParentDerivative 3)
        sharedResidualMaskedCredit 0 1 = 3 := by
  have two_ne_zero : (2 : Fin 4) ≠ 0 := by decide
  norm_num [RankedOccurrenceDAG.parentAggregate, sharedResidualGraph,
    sharedResidualOccurrence, sharedResidualParentDerivative,
    sharedResidualMaskedCredit, scalarContinuousLinearMap, parentPullback,
    Fin.sum_univ_four, two_ne_zero]

/-- The masked tied-parameter contribution is exactly `2 + 0 = 2`. -/
theorem sharedResidual_tiedParameterAggregate_masked_eq_2 :
    tiedParameterAggregate
        (NodeSpace := fun _ : Fin 4 => ℝ)
        (ParameterOccurrence := sharedResidualParameterOccurrence)
        (ParameterSpace := fun _ : Unit => ℝ)
        sharedResidualParameterActive sharedResidualZeroParameterDirect
        sharedResidualParameterDerivative sharedResidualMaskedCredit () 1 = 2 := by
  have two_ne_zero : (2 : Fin 4) ≠ 0 := by decide
  norm_num [tiedParameterAggregate, sharedResidualParameterOccurrence,
    sharedResidualParameterActive, sharedResidualZeroParameterDirect,
    sharedResidualParameterDerivative, sharedResidualMaskedCredit,
    scalarContinuousLinearMap, Fin.sum_univ_four, two_ne_zero]

/-- The actual composed task when the second merge branch is masked. -/
def sharedResidualMaskedTask (theta : ℝ) : ℝ :=
  let x0 : ℝ := 2
  let x1 := theta * x0
  let x3 := x1
  (x3 - 5) ^ 2 / 2

/-- The masked occurrence sum again agrees with the derivative of the actual
composed task. -/
theorem sharedResidualMaskedTask_hasFDerivAt :
    HasRealFDerivAt sharedResidualMaskedTask
      (scalarContinuousLinearMap 2) 3 := by
  have polynomial := halfSquaredAffine_hasFDerivAt 2 (-5) 3
  have derivativeEq :
      scalarContinuousLinearMap ((2 * 3 + (-5)) * 2) =
        scalarContinuousLinearMap 2 := by
    norm_num
  have polynomial2 := polynomial.congr_fderiv derivativeEq
  have taskEq : sharedResidualMaskedTask =ᶠ[nhds (3 : ℝ)]
      fun theta => (scalarContinuousLinearMap 2 theta + (-5)) ^ 2 * 2⁻¹ :=
    Filter.Eventually.of_forall fun theta => by
      simp [sharedResidualMaskedTask, scalarContinuousLinearMap]
      ring
  exact polynomial2.congr_of_eventuallyEq taskEq

/-- If the removed branch were assigned its active-case twofold adjoint, the
parameter sum would be six rather than the actual masked derivative two. -/
theorem sharedResidual_spurious_unmasked_parameter_credit :
    (2 + 4 : ℝ) ≠ 2 := by
  norm_num

/-! ## Tied two-step recurrence -/

/-- One potential temporal edge per ordered state pair. -/
abbrev recurrentOccurrence (_source _target : Fin 3) : Type := Unit

/-- The unrolled recurrence `x0 → x1 → x2`. -/
def recurrentGraph : RankedOccurrenceDAG recurrentOccurrence where
  rank := fun node => node.val
  active := fun {source target} _ =>
    decide ((source = 0 ∧ target = 1) ∨ (source = 1 ∧ target = 2))
  forward := by
    intro source target _ active
    rcases of_decide_eq_true active with edge | edge
    · rcases edge with ⟨rfl, rfl⟩
      norm_num
    · rcases edge with ⟨rfl, rfl⟩
      norm_num

def recurrentParentDerivative (weight : ℝ)
    {source target : Fin 3} (_occurrence : recurrentOccurrence source target) :
    ℝ →L[ℝ] ℝ :=
  scalarContinuousLinearMap weight

/-- Exact reverse covectors of the unrolled recurrence. -/
def recurrentCredit
    (problem : Instances.ScalarRecurrentProblem) (weight : ℝ) :
    ∀ _node : Fin 3, ℝ →L[ℝ] ℝ :=
  let firstState := weight * problem.input
  let error := weight * firstState - problem.target
  fun node =>
    if node = 0 then scalarContinuousLinearMap (weight * (weight * error))
    else if node = 1 then scalarContinuousLinearMap (weight * error)
    else scalarContinuousLinearMap error

def recurrentDirect
    (problem : Instances.ScalarRecurrentProblem) (weight : ℝ) :
    ∀ _node : Fin 3, ℝ →L[ℝ] ℝ :=
  let firstState := weight * problem.input
  let error := weight * firstState - problem.target
  fun node => if node = 2 then scalarContinuousLinearMap error else 0

/-- K2 specializes to the ordinary reverse temporal recurrence. -/
theorem recurrentCredit_satisfies_reverseRecursion
    (problem : Instances.ScalarRecurrentProblem) (weight : ℝ) :
    ∀ source,
      recurrentCredit problem weight source =
        RankedOccurrenceDAG.reverseAggregate
          (ParentOccurrence := recurrentOccurrence)
          (NodeSpace := fun _ : Fin 3 => ℝ)
          recurrentGraph (recurrentDirect problem weight)
          (recurrentParentDerivative weight)
          (recurrentCredit problem weight) source := by
  intro source
  fin_cases source <;>
    apply ContinuousLinearMap.ext <;>
    intro direction <;>
    simp [recurrentCredit, recurrentDirect,
      RankedOccurrenceDAG.reverseAggregate,
      RankedOccurrenceDAG.parentAggregate, recurrentGraph,
      recurrentOccurrence, recurrentParentDerivative,
      scalarContinuousLinearMap, parentPullback] <;>
    ring

abbrev recurrentParameterOccurrence
    (_parameter : Unit) (_owner : Fin 3) : Type := Unit

def recurrentParameterActive
    {parameter : Unit} {owner : Fin 3}
    (_occurrence : recurrentParameterOccurrence parameter owner) : Bool :=
  decide (owner = 1 ∨ owner = 2)

/-- Each tied occurrence differentiates its actual transition with respect to
the shared weight, producing the previous state. -/
def recurrentParameterDerivative
    (problem : Instances.ScalarRecurrentProblem) (weight : ℝ)
    {parameter : Unit} {owner : Fin 3}
    (_occurrence : recurrentParameterOccurrence parameter owner) : ℝ →L[ℝ] ℝ :=
  if owner = 1 then scalarContinuousLinearMap problem.input
  else if owner = 2 then scalarContinuousLinearMap (weight * problem.input)
  else 0

def recurrentZeroParameterDirect : ∀ _parameter : Unit, ℝ →L[ℝ] ℝ :=
  fun _ => 0

/-- K5 specializes exactly to the two-occurrence BPTT sum implemented by the
existing executable reverse schedule. -/
theorem recurrent_tiedAggregate_eq_existingBPTT
    (problem : Instances.ScalarRecurrentProblem) (weight : ℝ) :
    tiedParameterAggregate
        (NodeSpace := fun _ : Fin 3 => ℝ)
        (ParameterOccurrence := recurrentParameterOccurrence)
        (ParameterSpace := fun _ : Unit => ℝ)
        recurrentParameterActive recurrentZeroParameterDirect
        (recurrentParameterDerivative problem weight)
        (recurrentCredit problem weight) () 1 =
      Instances.scalarRecurrentBPTTCredit problem weight := by
  simp [tiedParameterAggregate, recurrentParameterOccurrence,
    recurrentParameterActive, recurrentZeroParameterDirect,
    recurrentParameterDerivative, recurrentCredit,
    scalarContinuousLinearMap, Instances.scalarRecurrentBPTTCredit,
    Fin.sum_univ_three]
  ring

#print axioms sharedResidual_parentAggregate_active_eq_135
#print axioms sharedResidual_tiedParameterAggregate_active_eq_90
#print axioms sharedResidualActiveTask_hasDerivAt
#print axioms sharedResidual_parentAggregate_masked_eq_3
#print axioms sharedResidual_tiedParameterAggregate_masked_eq_2
#print axioms sharedResidualMaskedTask_hasFDerivAt
#print axioms sharedResidual_spurious_unmasked_parameter_credit
#print axioms recurrentCredit_satisfies_reverseRecursion
#print axioms recurrent_tiedAggregate_eq_existingBPTT

end

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.KKT
