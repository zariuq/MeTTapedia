import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ShootingStructure
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.RankedDAGTensorDynamics
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Realized scheduled credit on ranked predictive-coding DAGs

This file lifts the scalar sweep-completeness discussion to parameter-credit
vectors in a finite real inner-product space.  A scheduled DAG contribution is
not postulated: it is the existing edge-occurrence contribution multiplied by
an explicit parameter-space readout and admitted by the existing arrival
schedule.

Pairwise-orthogonal contributions have an exact interpretation: squared
cosine of a prefix with complete BP credit is the fraction of BP-credit energy
already captured, hence is monotone with schedule inclusion.  Signed tied
occurrences need not be orthogonal; a legal schedule can then decrease and
later recover cosine by cancellation.

For tensor DAGs, a complete frozen reverse-power sweep is proved equal to the
triangular complete reverse force and therefore to BP occurrence credit.  The
actual reverse-ranked *state-gradient* sweep has a sharp separate boundary:
it agrees with BP only when its state remains the forward state and its local
force is complete.  An executable chain fixture shows that a genuine state
sweep generally crosses that boundary.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace RealizedScheduledCredit

open scoped BigOperators InnerProductSpace
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
open NondimensionalSettlingSchedule

noncomputable section

/-! ## Finite-dimensional prefix geometry -/

variable {Index Credit : Type*}
  [Fintype Index] [DecidableEq Index]
  [NormedAddCommGroup Credit] [InnerProductSpace ℝ Credit]

/-- The contributions supplied by different completed schedule units are
pairwise orthogonal in the realized parameter-credit geometry. -/
def PairwiseOrthogonalContributions (contribution : Index → Credit) : Prop :=
  ∀ left right, left ≠ right →
    ⟪contribution left, contribution right⟫_ℝ = 0

/-- Credit captured by an arbitrary finite schedule prefix. -/
def sweepPrefix (contribution : Index → Credit) (captured : Finset Index) : Credit :=
  ∑ index ∈ captured, contribution index

/-- Complete credit after every schedule contribution has arrived. -/
def sweepTotal (contribution : Index → Credit) : Credit :=
  ∑ index, contribution index

/-- Squared energy of the contributions in a schedule prefix. -/
def sweepCapturedEnergy
    (contribution : Index → Credit) (captured : Finset Index) : ℝ :=
  ∑ index ∈ captured, ⟪contribution index, contribution index⟫_ℝ

/-- Squared energy of all schedule contributions. -/
def sweepTotalEnergy (contribution : Index → Credit) : ℝ :=
  ∑ index, ⟪contribution index, contribution index⟫_ℝ

/-- Squared cosine written without square roots.  As usual in Lean's field
semantics it evaluates to zero when a denominator factor is zero; the exact
fraction theorem assumes nonzero total BP energy. -/
def innerSquaredCosine (left right : Credit) : ℝ :=
  ⟪left, right⟫_ℝ ^ 2 /
    (⟪left, left⟫_ℝ * ⟪right, right⟫_ℝ)

/-- Fraction of complete orthogonal credit energy captured by a prefix. -/
def capturedEnergyFraction
    (contribution : Index → Credit) (captured : Finset Index) : ℝ :=
  sweepCapturedEnergy contribution captured / sweepTotalEnergy contribution

omit [DecidableEq Index] in
theorem contribution_inner_total_eq_self
    (contribution : Index → Credit)
    (orthogonal : PairwiseOrthogonalContributions contribution)
    (index : Index) :
    ⟪contribution index, sweepTotal contribution⟫_ℝ =
      ⟪contribution index, contribution index⟫_ℝ := by
  classical
  rw [sweepTotal, inner_sum]
  apply Fintype.sum_eq_single index
  intro other hne
  exact orthogonal index other hne.symm

omit [Fintype Index] in
theorem contribution_inner_prefix_eq_self
    (contribution : Index → Credit)
    (orthogonal : PairwiseOrthogonalContributions contribution)
    (captured : Finset Index) (index : Index) (mem : index ∈ captured) :
    ⟪contribution index, sweepPrefix contribution captured⟫_ℝ =
      ⟪contribution index, contribution index⟫_ℝ := by
  classical
  rw [sweepPrefix, inner_sum]
  apply Finset.sum_eq_single index
  · intro other _hmem hne
    exact orthogonal index other hne.symm
  · simp [mem]

omit [DecidableEq Index] in
theorem sweepPrefix_inner_total_eq_capturedEnergy
    (contribution : Index → Credit)
    (orthogonal : PairwiseOrthogonalContributions contribution)
    (captured : Finset Index) :
    ⟪sweepPrefix contribution captured, sweepTotal contribution⟫_ℝ =
      sweepCapturedEnergy contribution captured := by
  rw [sweepPrefix, sum_inner]
  apply Finset.sum_congr rfl
  intro index _mem
  exact contribution_inner_total_eq_self contribution orthogonal index

omit [Fintype Index] in
theorem sweepPrefix_inner_self_eq_capturedEnergy
    (contribution : Index → Credit)
    (orthogonal : PairwiseOrthogonalContributions contribution)
    (captured : Finset Index) :
    ⟪sweepPrefix contribution captured, sweepPrefix contribution captured⟫_ℝ =
      sweepCapturedEnergy contribution captured := by
  rw [sweepPrefix, sum_inner]
  apply Finset.sum_congr rfl
  intro index mem
  exact contribution_inner_prefix_eq_self contribution orthogonal captured index mem

omit [DecidableEq Index] in
theorem sweepTotal_inner_self_eq_totalEnergy
    (contribution : Index → Credit)
    (orthogonal : PairwiseOrthogonalContributions contribution) :
    ⟪sweepTotal contribution, sweepTotal contribution⟫_ℝ =
      sweepTotalEnergy contribution := by
  rw [sweepTotal, sum_inner]
  apply Finset.sum_congr rfl
  intro index _mem
  exact contribution_inner_total_eq_self contribution orthogonal index

omit [Fintype Index] [DecidableEq Index] in
theorem sweepCapturedEnergy_nonneg
    (contribution : Index → Credit) (captured : Finset Index) :
    0 ≤ sweepCapturedEnergy contribution captured := by
  unfold sweepCapturedEnergy
  exact Finset.sum_nonneg fun _index _mem => real_inner_self_nonneg

omit [Fintype Index] [DecidableEq Index] in
theorem sweepCapturedEnergy_mono
    (contribution : Index → Credit) {earlier later : Finset Index}
    (subset : earlier ⊆ later) :
    sweepCapturedEnergy contribution earlier ≤
      sweepCapturedEnergy contribution later := by
  unfold sweepCapturedEnergy
  exact Finset.sum_le_sum_of_subset_of_nonneg subset
    (fun _index _later _notEarlier => real_inner_self_nonneg)

/-- Realized finite-dimensional crown: if complete BP credit decomposes into
pairwise-orthogonal schedule contributions, prefix squared cosine is exactly
the fraction of complete credit energy captured by that prefix. -/
theorem prefix_innerSquaredCosine_eq_capturedEnergyFraction
    (contribution : Index → Credit)
    (orthogonal : PairwiseOrthogonalContributions contribution)
    (captured : Finset Index)
    (totalEnergy_pos : 0 < sweepTotalEnergy contribution) :
    innerSquaredCosine (sweepPrefix contribution captured)
        (sweepTotal contribution) =
      capturedEnergyFraction contribution captured := by
  rw [innerSquaredCosine, capturedEnergyFraction,
    sweepPrefix_inner_total_eq_capturedEnergy contribution orthogonal captured,
    sweepPrefix_inner_self_eq_capturedEnergy contribution orthogonal captured,
    sweepTotal_inner_self_eq_totalEnergy contribution orthogonal]
  have totalEnergy_ne : sweepTotalEnergy contribution ≠ 0 :=
    ne_of_gt totalEnergy_pos
  by_cases capturedEnergy_ne : sweepCapturedEnergy contribution captured = 0
  · rw [capturedEnergy_ne]
    norm_num
  · field_simp [capturedEnergy_ne, totalEnergy_ne]

/-- Under the same orthogonality hypothesis, completing more legal schedule
units monotonically improves squared cosine to complete BP credit. -/
theorem prefix_innerSquaredCosine_mono
    (contribution : Index → Credit)
    (orthogonal : PairwiseOrthogonalContributions contribution)
    (totalEnergy_pos : 0 < sweepTotalEnergy contribution)
    {earlier later : Finset Index} (subset : earlier ⊆ later) :
    innerSquaredCosine (sweepPrefix contribution earlier)
        (sweepTotal contribution) ≤
      innerSquaredCosine (sweepPrefix contribution later)
        (sweepTotal contribution) := by
  rw [prefix_innerSquaredCosine_eq_capturedEnergyFraction
      contribution orthogonal earlier totalEnergy_pos,
    prefix_innerSquaredCosine_eq_capturedEnergyFraction
      contribution orthogonal later totalEnergy_pos]
  unfold capturedEnergyFraction
  exact (div_le_div_iff_of_pos_right totalEnergy_pos).2
    (sweepCapturedEnergy_mono contribution subset)

/-! ## Existing DAG schedules realized in parameter-credit space -/

variable {Node Edge : Type*}
  [Fintype Node] [Fintype Edge] [DecidableEq Node] [DecidableEq Edge]

/-- Existing scalar edge credit embedded along the parameter-space direction
owned by that edge occurrence. -/
def dagParameterContribution
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ)
    (readout : Edge → Credit) (edge : Edge) : Credit :=
  dagParentContribution G parentError edge • readout edge

/-- Edge occurrences leaving `source` whose contributions have arrived by
`time`, using the existing `DAGScheduleExactness` arrival convention. -/
def dagArrivedEdges
    (G : SharedLatentDAG Node Edge) (arrival : Edge → ℕ)
    (time : ℕ) (source : Node) : Finset Edge :=
  Finset.univ.filter fun edge => G.source edge = source ∧ arrival edge ≤ time

/-- Real parameter credit produced by the scheduled DAG prefix at one source
node. -/
def dagScheduledParameterCredit
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ)
    (readout : Edge → Credit) (arrival : Edge → ℕ)
    (time : ℕ) (source : Node) : Credit :=
  sweepPrefix (dagParameterContribution G parentError readout)
    (dagArrivedEdges G arrival time source)

/-- Complete parameter credit at one source node. -/
def dagFullParameterCredit
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ)
    (readout : Edge → Credit) (source : Node) : Credit :=
  sweepPrefix (dagParameterContribution G parentError readout)
    (Finset.univ.filter fun edge => G.source edge = source)

omit [DecidableEq Edge] in
theorem dagArrivedEdges_mono
    (G : SharedLatentDAG Node Edge) (arrival : Edge → ℕ)
    {earlier later : ℕ} (time_le : earlier ≤ later) (source : Node) :
    dagArrivedEdges G arrival earlier source ⊆
      dagArrivedEdges G arrival later source := by
  intro edge mem
  simp only [dagArrivedEdges, Finset.mem_filter, Finset.mem_univ, true_and] at mem ⊢
  exact ⟨mem.1, mem.2.trans time_le⟩

omit [DecidableEq Edge] in
theorem dagScheduledParameterCredit_eq_full_of_admissible
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ)
    (readout : Edge → Credit) (arrival : Edge → ℕ)
    (time : ℕ) (source : Node)
    (admissible : dagScheduleAdmissible G arrival time source) :
    dagScheduledParameterCredit G parentError readout arrival time source =
      dagFullParameterCredit G parentError readout source := by
  apply congrArg (sweepPrefix (dagParameterContribution G parentError readout))
  ext edge
  by_cases sourceEdge : G.source edge = source
  · simp [dagArrivedEdges, sourceEdge, admissible edge sourceEdge]
  · simp [dagArrivedEdges, sourceEdge]

/-- The AC stage record and the ranked cut are retained together.  The stage
sets the registered sweep budget; the cut, arrival schedule, and readout own
the realized parameter-credit semantics. -/
structure ACRealizedDAGSchedule where
  stage : ACStage
  cut : SharedLatentDAG Node Edge
  parentError : Node → ℝ
  readout : Edge → Credit
  arrival : Edge → ℕ
  source : Node

def ACRealizedDAGSchedule.credit
    (schedule : ACRealizedDAGSchedule (Node := Node) (Edge := Edge)
      (Credit := Credit)) : Credit :=
  dagScheduledParameterCredit schedule.cut schedule.parentError schedule.readout
    schedule.arrival schedule.stage.schedule.sweeps schedule.source

/-- The existing scalar cut has the canonical ranked-tensor realization used
by the state/error and frozen-force theories. -/
def ACRealizedDAGSchedule.tensorCut
    (schedule : ACRealizedDAGSchedule (Node := Node) (Edge := Edge)
      (Credit := Credit)) : RankedDAGTensor Node Edge Node :=
  sharedLatentDAGTensor schedule.cut

/-! ## Positive and negative executable scheduled-DAG fixtures -/

abbrev FixtureCredit := EuclideanSpace ℝ (Fin 2)

def fixtureAxis0 : FixtureCredit := EuclideanSpace.single 0 1

def fixtureAxis1 : FixtureCredit := EuclideanSpace.single 1 1

def orthogonalReadout : Fin 2 → FixtureCredit
  | 0 => fixtureAxis0
  | 1 => fixtureAxis1

def twoArrival (edge : Fin 2) : ℕ := edge.val

def positiveDAGContribution (edge : Fin 2) : FixtureCredit :=
  dagParameterContribution uniformLongSkipGraph
    uniformLongSkipParentError orthogonalReadout edge

theorem positiveDAGContribution_pairwiseOrthogonal :
    PairwiseOrthogonalContributions positiveDAGContribution := by
  intro left right hne
  fin_cases left <;> fin_cases right
  · exact (hne rfl).elim
  · norm_num [positiveDAGContribution, dagParameterContribution,
      dagParentContribution, uniformLongSkipGraph,
      uniformLongSkipParentError, orthogonalReadout, fixtureAxis0,
      fixtureAxis1, EuclideanSpace.inner_single_left, PiLp.single_apply]
  · norm_num [positiveDAGContribution, dagParameterContribution,
      dagParentContribution, uniformLongSkipGraph,
      uniformLongSkipParentError, orthogonalReadout, fixtureAxis0,
      fixtureAxis1, EuclideanSpace.inner_single_left, PiLp.single_apply]
  · exact (hne rfl).elim

theorem positiveDAG_totalEnergy_pos :
    0 < sweepTotalEnergy positiveDAGContribution := by
  norm_num [sweepTotalEnergy, positiveDAGContribution,
    dagParameterContribution, dagParentContribution, uniformLongSkipGraph,
    uniformLongSkipParentError, orthogonalReadout, fixtureAxis0, fixtureAxis1,
    EuclideanSpace.inner_single_left, PiLp.single_apply,
    Fin.sum_univ_succ]

theorem positiveDAG_schedule_legal_at_one :
    dagScheduleAdmissible uniformLongSkipGraph twoArrival 1 0 := by
  intro edge _source
  fin_cases edge <;> norm_num [twoArrival]

theorem positiveDAG_credit_vectors :
    dagScheduledParameterCredit uniformLongSkipGraph
        uniformLongSkipParentError orthogonalReadout twoArrival 0 0 =
        fixtureAxis0 ∧
      dagScheduledParameterCredit uniformLongSkipGraph
        uniformLongSkipParentError orthogonalReadout twoArrival 1 0 =
        fixtureAxis0 + fixtureAxis1 ∧
      dagFullParameterCredit uniformLongSkipGraph
        uniformLongSkipParentError orthogonalReadout 0 =
        fixtureAxis0 + fixtureAxis1 := by
  constructor
  · ext coordinate
    fin_cases coordinate <;>
      norm_num [dagScheduledParameterCredit, sweepPrefix, dagArrivedEdges,
        dagParameterContribution, dagParentContribution, uniformLongSkipGraph,
        uniformLongSkipParentError, orthogonalReadout, twoArrival,
        fixtureAxis0, fixtureAxis1, PiLp.single_apply, Finset.sum_filter,
        Fin.sum_univ_two]
  constructor
  · ext coordinate
    fin_cases coordinate <;>
      norm_num [dagScheduledParameterCredit, sweepPrefix, dagArrivedEdges,
        dagParameterContribution, dagParentContribution, uniformLongSkipGraph,
        uniformLongSkipParentError, orthogonalReadout, twoArrival,
        fixtureAxis0, fixtureAxis1, PiLp.single_apply, Finset.sum_filter,
        Fin.sum_univ_two]
  · ext coordinate
    fin_cases coordinate <;>
      norm_num [dagFullParameterCredit, sweepPrefix,
        dagParameterContribution, dagParentContribution, uniformLongSkipGraph,
        uniformLongSkipParentError, orthogonalReadout,
        fixtureAxis0, fixtureAxis1, PiLp.single_apply, Finset.sum_filter,
        Fin.sum_univ_two]

theorem positiveDAG_prefix_cosine_values :
    innerSquaredCosine
        (dagScheduledParameterCredit uniformLongSkipGraph
          uniformLongSkipParentError orthogonalReadout twoArrival 0 0)
        (dagFullParameterCredit uniformLongSkipGraph
          uniformLongSkipParentError orthogonalReadout 0) = 1 / 2 ∧
      innerSquaredCosine
        (dagScheduledParameterCredit uniformLongSkipGraph
          uniformLongSkipParentError orthogonalReadout twoArrival 1 0)
        (dagFullParameterCredit uniformLongSkipGraph
          uniformLongSkipParentError orthogonalReadout 0) = 1 := by
  obtain ⟨atZero, atOne, full⟩ := positiveDAG_credit_vectors
  rw [atZero, atOne, full]
  norm_num [innerSquaredCosine, fixtureAxis0, fixtureAxis1,
    PiLp.inner_apply, PiLp.single_apply, PiLp.norm_sq_eq_of_L2,
    Fin.sum_univ_two]

def positiveACRealizedSchedule :
    ACRealizedDAGSchedule (Node := Fin 3) (Edge := Fin 2)
      (Credit := FixtureCredit) where
  stage := .eightStep
  cut := uniformLongSkipGraph
  parentError := uniformLongSkipParentError
  readout := orthogonalReadout
  arrival := twoArrival
  source := 0

theorem positiveACRealizedSchedule_credit_eq_full :
    positiveACRealizedSchedule.credit =
      dagFullParameterCredit uniformLongSkipGraph
        uniformLongSkipParentError orthogonalReadout 0 := by
  apply dagScheduledParameterCredit_eq_full_of_admissible
  intro edge _source
  fin_cases edge <;>
    norm_num [positiveACRealizedSchedule, ACStage.schedule, twoArrival]

/-- A legal arrival order on the existing signed-cancellation DAG. -/
def cancellationArrival (edge : Fin 3) : ℕ := edge.val

/-- The two later signed occurrences share a parameter direction, exposing
the tied-parameter cancellation that orthogonal occurrence coordinates hide. -/
def cancellationReadout : Fin 3 → FixtureCredit
  | 0 => fixtureAxis0
  | 1 => fixtureAxis1
  | 2 => fixtureAxis1

def cancellationDAGContribution (edge : Fin 3) : FixtureCredit :=
  dagParameterContribution signedCancellationGraph
    signedCancellationParentError cancellationReadout edge

theorem cancellationDAGContribution_values :
    cancellationDAGContribution 0 = 2 • fixtureAxis0 ∧
      cancellationDAGContribution 1 = fixtureAxis1 ∧
      cancellationDAGContribution 2 = -fixtureAxis1 := by
  constructor
  · ext coordinate
    fin_cases coordinate <;>
      norm_num [cancellationDAGContribution, dagParameterContribution,
        dagParentContribution, signedCancellationGraph,
        signedCancellationParentError, cancellationReadout, fixtureAxis0,
        fixtureAxis1, PiLp.single_apply]
  constructor
  · ext coordinate
    fin_cases coordinate <;>
      norm_num [cancellationDAGContribution, dagParameterContribution,
        dagParentContribution, signedCancellationGraph,
        signedCancellationParentError, cancellationReadout, fixtureAxis1,
        PiLp.single_apply]
  · ext coordinate
    fin_cases coordinate <;>
      norm_num [cancellationDAGContribution, dagParameterContribution,
        dagParentContribution, signedCancellationGraph,
        signedCancellationParentError, cancellationReadout, fixtureAxis1,
        PiLp.single_apply] <;>
      simp [show (2 : Fin 3) ≠ 0 by decide]

/-- The cancellation fixture violates the positive theorem's load-bearing
orthogonality hypothesis: its two later occurrences share one parameter
direction with opposite signed credit. -/
theorem cancellationDAGContribution_not_pairwiseOrthogonal :
    ¬ PairwiseOrthogonalContributions cancellationDAGContribution := by
  intro orthogonal
  obtain ⟨_zero, one, two⟩ := cancellationDAGContribution_values
  have distinct : (1 : Fin 3) ≠ 2 := by decide
  have contradiction := orthogonal 1 2 distinct
  rw [one, two] at contradiction
  norm_num [fixtureAxis1, PiLp.inner_apply, PiLp.single_apply,
    PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two] at contradiction

theorem cancellationDAG_schedule_legal_at_two :
    dagScheduleAdmissible signedCancellationGraph cancellationArrival 2 0 := by
  intro edge _source
  fin_cases edge <;> norm_num [cancellationArrival]

theorem cancellationDAG_credit_vectors :
    dagScheduledParameterCredit signedCancellationGraph
        signedCancellationParentError cancellationReadout
        cancellationArrival 0 0 = 2 • fixtureAxis0 ∧
      dagScheduledParameterCredit signedCancellationGraph
        signedCancellationParentError cancellationReadout
        cancellationArrival 1 0 = 2 • fixtureAxis0 + fixtureAxis1 ∧
      dagScheduledParameterCredit signedCancellationGraph
        signedCancellationParentError cancellationReadout
        cancellationArrival 2 0 = 2 • fixtureAxis0 ∧
      dagFullParameterCredit signedCancellationGraph
        signedCancellationParentError cancellationReadout 0 =
        2 • fixtureAxis0 := by
  constructor
  · ext coordinate
    fin_cases coordinate <;>
      norm_num [dagScheduledParameterCredit, sweepPrefix, dagArrivedEdges,
        dagParameterContribution, dagParentContribution,
        signedCancellationGraph, signedCancellationParentError,
        cancellationReadout, cancellationArrival, fixtureAxis0, fixtureAxis1,
        PiLp.single_apply, Finset.sum_filter, Fin.sum_univ_three]
  constructor
  · ext coordinate
    fin_cases coordinate <;>
      norm_num [dagScheduledParameterCredit, sweepPrefix, dagArrivedEdges,
        dagParameterContribution, dagParentContribution,
        signedCancellationGraph, signedCancellationParentError,
        cancellationReadout, cancellationArrival, fixtureAxis0, fixtureAxis1,
        PiLp.single_apply, Finset.sum_filter, Fin.sum_univ_three]
  constructor
  · ext coordinate
    fin_cases coordinate <;>
      norm_num [dagScheduledParameterCredit, sweepPrefix, dagArrivedEdges,
        dagParameterContribution, dagParentContribution,
        signedCancellationGraph, signedCancellationParentError,
        cancellationReadout, cancellationArrival, fixtureAxis0, fixtureAxis1,
        PiLp.single_apply, Finset.sum_filter, Fin.sum_univ_three] <;>
      simp
  · ext coordinate
    fin_cases coordinate <;>
      norm_num [dagFullParameterCredit, sweepPrefix,
        dagParameterContribution, dagParentContribution,
        signedCancellationGraph, signedCancellationParentError,
        cancellationReadout, fixtureAxis0, fixtureAxis1,
        PiLp.single_apply, Finset.sum_filter, Fin.sum_univ_three] <;>
      simp

theorem cancellationDAG_prefix_cosine_values :
    innerSquaredCosine
        (dagScheduledParameterCredit signedCancellationGraph
          signedCancellationParentError cancellationReadout
          cancellationArrival 0 0)
        (dagFullParameterCredit signedCancellationGraph
          signedCancellationParentError cancellationReadout 0) = 1 ∧
      innerSquaredCosine
        (dagScheduledParameterCredit signedCancellationGraph
          signedCancellationParentError cancellationReadout
          cancellationArrival 1 0)
        (dagFullParameterCredit signedCancellationGraph
          signedCancellationParentError cancellationReadout 0) = 4 / 5 ∧
      innerSquaredCosine
        (dagScheduledParameterCredit signedCancellationGraph
          signedCancellationParentError cancellationReadout
          cancellationArrival 2 0)
        (dagFullParameterCredit signedCancellationGraph
          signedCancellationParentError cancellationReadout 0) = 1 := by
  obtain ⟨atZero, atOne, atTwo, full⟩ := cancellationDAG_credit_vectors
  rw [atZero, atOne, atTwo, full]
  norm_num [innerSquaredCosine, fixtureAxis0, fixtureAxis1,
    PiLp.inner_apply, PiLp.single_apply, PiLp.norm_sq_eq_of_L2,
    Fin.sum_univ_two]

theorem cancellationDAG_prefix_decreases_then_recovers :
    innerSquaredCosine
        (dagScheduledParameterCredit signedCancellationGraph
          signedCancellationParentError cancellationReadout
          cancellationArrival 1 0)
        (dagFullParameterCredit signedCancellationGraph
          signedCancellationParentError cancellationReadout 0) <
      innerSquaredCosine
        (dagScheduledParameterCredit signedCancellationGraph
          signedCancellationParentError cancellationReadout
          cancellationArrival 0 0)
        (dagFullParameterCredit signedCancellationGraph
          signedCancellationParentError cancellationReadout 0) ∧
      innerSquaredCosine
        (dagScheduledParameterCredit signedCancellationGraph
          signedCancellationParentError cancellationReadout
          cancellationArrival 1 0)
        (dagFullParameterCredit signedCancellationGraph
          signedCancellationParentError cancellationReadout 0) <
      innerSquaredCosine
        (dagScheduledParameterCredit signedCancellationGraph
          signedCancellationParentError cancellationReadout
          cancellationArrival 2 0)
        (dagFullParameterCredit signedCancellationGraph
          signedCancellationParentError cancellationReadout 0) := by
  obtain ⟨first, middle, last⟩ := cancellationDAG_prefix_cosine_values
  rw [first, middle, last]
  norm_num

def cancellationACRealizedSchedule :
    ACRealizedDAGSchedule (Node := Fin 2) (Edge := Fin 3)
      (Credit := FixtureCredit) where
  stage := .eightStep
  cut := signedCancellationGraph
  parentError := signedCancellationParentError
  readout := cancellationReadout
  arrival := cancellationArrival
  source := 0

theorem cancellationACRealizedSchedule_credit_eq_full :
    cancellationACRealizedSchedule.credit =
      dagFullParameterCredit signedCancellationGraph
        signedCancellationParentError cancellationReadout 0 := by
  apply dagScheduledParameterCredit_eq_full_of_admissible
  intro edge _source
  fin_cases edge <;>
    norm_num [cancellationACRealizedSchedule, ACStage.schedule,
      cancellationArrival]

/-! ## Frozen tensor reverse sweep and the state-sweep boundary -/

variable {Coord : Type*} [Fintype Coord] [DecidableEq Coord]

/-- One path-length contribution to the frozen reverse force. -/
def rankedDAGReversePowerForceContribution
    (G : RankedDAGTensor Node Edge Coord) (taskForce : Coord → ℝ)
    (power : ℕ) : Coord → ℝ :=
  Matrix.mulVec (rankedDAGFeedforwardMatrix G ^ power).transpose taskForce

/-- Frozen reverse-force prefix through the given path length. -/
def rankedDAGFrozenReversePowerSweep
    (G : RankedDAGTensor Node Edge Coord) (taskForce : Coord → ℝ)
    (powers : ℕ) : Coord → ℝ :=
  ∑ power ∈ Finset.range powers,
    rankedDAGReversePowerForceContribution G taskForce power

/-- The complete ranked-DAG reverse-power sweep uses exactly the nilpotence
horizon supplied by the maximum coordinate rank. -/
def rankedDAGFrozenCompleteReverseSweep
    (G : RankedDAGTensor Node Edge Coord) (taskForce : Coord → ℝ) : Coord → ℝ :=
  rankedDAGFrozenReversePowerSweep G taskForce
    (rankedDAGMaxCoordinateRank G + 1)

omit [DecidableEq Edge] in
theorem rankedDAGFrozenCompleteReverseSweep_eq_completeReverseForce
    (G : RankedDAGTensor Node Edge Coord) (taskForce : Coord → ℝ) :
    rankedDAGFrozenCompleteReverseSweep G taskForce =
      rankedDAGCompleteReverseForce G taskForce := by
  simp only [rankedDAGFrozenCompleteReverseSweep,
    rankedDAGFrozenReversePowerSweep, rankedDAGReversePowerForceContribution,
    rankedDAGCompleteReverseForce, rankedDAGResolventMatrix]
  rw [Matrix.transpose_sum, Matrix.sum_mulVec]

/-- Whole tensor occurrence-credit vector read from an independently supplied
state and reverse force. -/
def rankedDAGOccurrenceCreditVector
    (G : RankedDAGTensor Node Edge Coord) (state force : Coord → ℝ) :
    Edge → Coord → Coord → ℝ :=
  fun edge output input =>
    rankedDAGOccurrenceCreditFromForce G state force edge output input

omit [DecidableEq Edge] in
/-- Complete frozen reverse-ranked transport equals BP simultaneously for
every edge occurrence and tensor entry.  The assumptions are explicit in the
construction: the state argument is the frozen feedforward state, and the
sweep transports only the terminal/task force. -/
theorem rankedDAG_frozen_completeReverseSweep_creditVector_eq_bp
    (G : RankedDAGTensor Node Edge Coord)
    (forwardState taskForce : Coord → ℝ) :
    rankedDAGOccurrenceCreditVector G forwardState
        (rankedDAGFrozenCompleteReverseSweep G taskForce) =
      fun edge output input =>
        rankedDAGBackpropOccurrenceCredit G forwardState taskForce
          edge output input := by
  rw [rankedDAGFrozenCompleteReverseSweep_eq_completeReverseForce]
  rfl

omit [DecidableEq Edge] in
/-- The energy-derived detached state credit is occurrence credit read from
the actual local precision-weighted residual force. -/
theorem rankedDAGStateDetachedCredit_eq_localForceOccurrenceCredit
    (G : RankedDAGTensor Node Edge Coord) (state : Coord → ℝ)
    (edge : Edge) (output input : Coord) :
    rankedDAGStateDetachedCredit G state edge output input =
      rankedDAGOccurrenceCreditFromForce G state
        (rankedDAGLocalForce G state) edge output input := by
  classical
  unfold rankedDAGStateDetachedCredit rankedDAGOccurrenceCreditFromForce
    rankedDAGLocalForce rankedDAGPrecisionMatrix
  simp only [Matrix.mulVec_diagonal]
  by_cases endpoints :
      G.target edge = G.owner output ∧ G.source edge = G.owner input
  · simp [endpoints]
  · simp [endpoints]

omit [DecidableEq Edge] in
/-- Sufficient frozen-state boundary for an actual reverse-ranked state
sweep: it agrees with BP when the sweep leaves the forward state fixed and
its realized local force is the complete reverse force. -/
theorem rankedDAG_reverseRankStateSweep_credit_eq_bp_of_frozen_complete
    (G : RankedDAGTensor Node Edge Coord) (movable : Finset Coord)
    (rate : ℝ) (initial forwardState taskForce : Coord → ℝ)
    (edge : Edge) (output input : Coord)
    (state_frozen :
      rankedDAGReverseRankSweep G movable rate initial = forwardState)
    (force_complete :
      rankedDAGLocalForce G
          (rankedDAGReverseRankSweep G movable rate initial) =
        rankedDAGCompleteReverseForce G taskForce) :
    rankedDAGStateDetachedCredit G
        (rankedDAGReverseRankSweep G movable rate initial)
        edge output input =
      rankedDAGBackpropOccurrenceCredit G forwardState taskForce
        edge output input := by
  have force_at_forward :
      rankedDAGLocalForce G forwardState =
        rankedDAGCompleteReverseForce G taskForce := by
    rw [← state_frozen]
    exact force_complete
  rw [rankedDAGStateDetachedCredit_eq_localForceOccurrenceCredit,
    state_frozen, force_at_forward]
  exact rankedDAG_frozen_completeReverse_credit_eq_backprop
    G forwardState taskForce edge output input

omit [DecidableEq Edge] in
/-- Sharp necessary boundary for departure of the actual state sweep.  Any
occurrence-level mismatch requires state displacement or an incomplete local
force. -/
theorem rankedDAG_reverseRankStateSweep_departure_requires_boundary_crossing
    (G : RankedDAGTensor Node Edge Coord) (movable : Finset Coord)
    (rate : ℝ) (initial forwardState taskForce : Coord → ℝ)
    (edge : Edge) (output input : Coord)
    (departure :
      rankedDAGStateDetachedCredit G
          (rankedDAGReverseRankSweep G movable rate initial)
          edge output input ≠
        rankedDAGBackpropOccurrenceCredit G forwardState taskForce
          edge output input) :
    rankedDAGReverseRankSweep G movable rate initial ≠ forwardState ∨
      rankedDAGLocalForce G
          (rankedDAGReverseRankSweep G movable rate initial) ≠
        rankedDAGCompleteReverseForce G taskForce := by
  apply rankedDAG_credit_departure_requires_displacement_or_incomplete_force
    G forwardState (rankedDAGReverseRankSweep G movable rate initial)
      taskForce
      (rankedDAGLocalForce G
        (rankedDAGReverseRankSweep G movable rate initial))
      edge output input
  rw [← rankedDAGStateDetachedCredit_eq_localForceOccurrenceCredit]
  exact departure

theorem rankedTensorChain4_bp_firstOccurrence_eq_neg_one :
    rankedDAGBackpropOccurrenceCredit rankedTensorChain4
      rankedTensorChain4ForwardState rankedTensorChain4TerminalForce
      0 1 0 = -1 := by
  rw [rankedDAGBackpropOccurrenceCredit,
    rankedTensorChain4_completeReverseForce_all_one]
  norm_num [rankedDAGOccurrenceCreditFromForce, rankedTensorChain4,
    rankedTensorChain4ForwardState]

/-- Executable positive tensor canary: the complete frozen reverse-power
sweep transports the terminal unit force to every coordinate of the chain. -/
theorem rankedTensorChain4_frozenCompleteReverseSweep_force_all_one :
    rankedDAGFrozenCompleteReverseSweep rankedTensorChain4
      rankedTensorChain4TerminalForce = fun _ => 1 := by
  rw [rankedDAGFrozenCompleteReverseSweep_eq_completeReverseForce,
    rankedTensorChain4_completeReverseForce_all_one]

/-- Executable negative boundary: a complete reverse-ranked gradient sweep
does transport credit through the chain, but its moved-state local credit is
`-1/4`, not the frozen BP credit `-1`. -/
theorem rankedTensorChain4_actualStateSweep_ne_frozenBP :
    rankedDAGStateDetachedCredit rankedTensorChain4
        (rankedDAGReverseRankSweep rankedTensorChain4
          rankedTensorChain4Movable (1 / 2) rankedTensorChain4TaskState)
        0 1 0 ≠
      rankedDAGBackpropOccurrenceCredit rankedTensorChain4
        rankedTensorChain4ForwardState rankedTensorChain4TerminalForce
        0 1 0 := by
  rw [rankedTensorChain4_reverseSweep_upstream_credit_nonzero,
    rankedTensorChain4_bp_firstOccurrence_eq_neg_one]
  norm_num

#print axioms prefix_innerSquaredCosine_eq_capturedEnergyFraction
#print axioms prefix_innerSquaredCosine_mono
#print axioms positiveDAG_prefix_cosine_values
#print axioms cancellationDAGContribution_not_pairwiseOrthogonal
#print axioms cancellationDAG_prefix_decreases_then_recovers
#print axioms rankedDAGFrozenCompleteReverseSweep_eq_completeReverseForce
#print axioms rankedDAG_frozen_completeReverseSweep_creditVector_eq_bp
#print axioms rankedTensorChain4_frozenCompleteReverseSweep_force_all_one
#print axioms rankedDAG_reverseRankStateSweep_departure_requires_boundary_crossing
#print axioms rankedTensorChain4_actualStateSweep_ne_frozenBP

end

end RealizedScheduledCredit

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
