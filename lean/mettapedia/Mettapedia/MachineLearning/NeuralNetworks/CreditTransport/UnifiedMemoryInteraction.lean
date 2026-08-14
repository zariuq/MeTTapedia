import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.EvidenceMemoryDynamics
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RetrievalAddressedAcceleration
import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.AddressableEvidenceMemory
import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.PairedDesignEstimands

/-!
# Unified memory, credit, and finite-intervention identification

This module separates aggregate evidence from addressable sidecar state and
defines the finite factorial estimand needed to test whether memory changes
predictive-coding credit differently from backpropagation.  Parameter and
optimizer inheritance are explicit factors rather than hidden parts of a
``continued'' label.  Theorems here concern finite credit or a declared scalar
endpoint; program discovery requires an additional bridge and is not inferred
from credit geometry alone.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

open Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

namespace UnifiedMemoryInteraction

noncomputable section

/-! ## Named finite treatments -/

inductive CreditRule where
  | backpropagation
  | predictiveCoding
  deriving DecidableEq, Repr

inductive MemoryMode where
  | absent
  | aggregate
  | addressable
  deriving DecidableEq, Repr

inductive InheritanceMode where
  | reset
  | inherited
  deriving DecidableEq, Repr

/-- Every experimental cell names the computational factors and the fixed
external boundary. -/
structure FiniteIntervention
    (Data Initialization Search Checker : Type*) where
  creditRule : CreditRule
  memoryMode : MemoryMode
  parameterInheritance : InheritanceMode
  optimizerInheritance : InheritanceMode
  data : Data
  initialization : Initialization
  search : Search
  checker : Checker
  workBudget : ℕ

/-- A fixed external boundary from which factorial cells are constructed. -/
structure FixedInterventionBoundary
    (Data Initialization Search Checker : Type*) where
  data : Data
  initialization : Initialization
  search : Search
  checker : Checker
  workBudget : ℕ

def FixedInterventionBoundary.cell
    {Data Initialization Search Checker : Type*}
    (boundary : FixedInterventionBoundary Data Initialization Search Checker)
    (creditRule : CreditRule) (memoryMode : MemoryMode)
    (parameterInheritance optimizerInheritance : InheritanceMode) :
    FiniteIntervention Data Initialization Search Checker where
  creditRule := creditRule
  memoryMode := memoryMode
  parameterInheritance := parameterInheritance
  optimizerInheritance := optimizerInheritance
  data := boundary.data
  initialization := boundary.initialization
  search := boundary.search
  checker := boundary.checker
  workBudget := boundary.workBudget

/-- Cells made from one boundary agree exactly on data, initialization,
search, checker, and work.  This holds by construction of `cell` and is an
interface law for the record, not evidence that any executed experiment held
those factors fixed; that obligation belongs to the registration. -/
theorem FixedInterventionBoundary.cell_preserves_boundary
    {Data Initialization Search Checker : Type*}
    (boundary : FixedInterventionBoundary Data Initialization Search Checker)
    (creditRule : CreditRule) (memoryMode : MemoryMode)
    (parameterInheritance optimizerInheritance : InheritanceMode) :
    let cell := boundary.cell creditRule memoryMode
      parameterInheritance optimizerInheritance
    cell.data = boundary.data ∧
      cell.initialization = boundary.initialization ∧
      cell.search = boundary.search ∧
      cell.checker = boundary.checker ∧
      cell.workBudget = boundary.workBudget := by
  simp [FixedInterventionBoundary.cell]

/-! ## Memory-by-credit interaction -/

/-- Difference in memory effect under finite predictive-coding credit versus
backpropagation credit. -/
def memoryPCInteraction
    (response : CreditRule → MemoryMode → ℝ)
    (memoryAbsent memoryPresent : MemoryMode) : ℝ :=
  (response .predictiveCoding memoryPresent -
      response .predictiveCoding memoryAbsent) -
    (response .backpropagation memoryPresent -
      response .backpropagation memoryAbsent)

/-- The interaction vanishes exactly when memory has the same finite effect
under the two credit rules. -/
theorem memoryPCInteraction_eq_zero_iff
    (response : CreditRule → MemoryMode → ℝ)
    (memoryAbsent memoryPresent : MemoryMode) :
    memoryPCInteraction response memoryAbsent memoryPresent = 0 ↔
      response .predictiveCoding memoryPresent -
          response .predictiveCoding memoryAbsent =
        response .backpropagation memoryPresent -
          response .backpropagation memoryAbsent := by
  unfold memoryPCInteraction
  constructor <;> intro h <;> linarith

/-- Additive credit-rule and memory effects have zero interaction. -/
theorem memoryPCInteraction_additive_eq_zero
    (creditEffect : CreditRule → ℝ) (memoryEffect : MemoryMode → ℝ)
    (memoryAbsent memoryPresent : MemoryMode) :
    memoryPCInteraction
      (fun rule memory ↦ creditEffect rule + memoryEffect memory)
      memoryAbsent memoryPresent = 0 := by
  unfold memoryPCInteraction
  ring

/-- Legal positive fixture: addressable memory changes only the PC response. -/
def selectiveAddressableResponse : CreditRule → MemoryMode → ℝ
  | .predictiveCoding, .addressable => 1
  | _, _ => 0

theorem selectiveAddressableResponse_has_nonzero_interaction :
    memoryPCInteraction selectiveAddressableResponse .absent .addressable = 1 := by
  norm_num [memoryPCInteraction, selectiveAddressableResponse]

/-- Four per-cell finite-credit error bounds compose to a four-epsilon
interaction bound.  Existing cold/warm credit theorems can discharge the four
premises independently. -/
theorem memoryPCInteraction_error_le
    (ideal realized : CreditRule → MemoryMode → ℝ)
    (memoryAbsent memoryPresent : MemoryMode) (ε : ℝ)
    (bpAbsent :
      |realized .backpropagation memoryAbsent -
        ideal .backpropagation memoryAbsent| ≤ ε)
    (bpPresent :
      |realized .backpropagation memoryPresent -
        ideal .backpropagation memoryPresent| ≤ ε)
    (pcAbsent :
      |realized .predictiveCoding memoryAbsent -
        ideal .predictiveCoding memoryAbsent| ≤ ε)
    (pcPresent :
      |realized .predictiveCoding memoryPresent -
        ideal .predictiveCoding memoryPresent| ≤ ε) :
    |memoryPCInteraction realized memoryAbsent memoryPresent -
        memoryPCInteraction ideal memoryAbsent memoryPresent| ≤ 4 * ε := by
  rcases (abs_le.mp bpAbsent) with ⟨bpAbsentLower, bpAbsentUpper⟩
  rcases (abs_le.mp bpPresent) with ⟨bpPresentLower, bpPresentUpper⟩
  rcases (abs_le.mp pcAbsent) with ⟨pcAbsentLower, pcAbsentUpper⟩
  rcases (abs_le.mp pcPresent) with ⟨pcPresentLower, pcPresentUpper⟩
  rw [abs_le]
  constructor <;> unfold memoryPCInteraction <;> linarith

/-! ## Why all four cells are needed -/

structure FourCellResponse where
  bpAbsent : ℝ
  bpPresent : ℝ
  pcAbsent : ℝ
  pcPresent : ℝ

def FourCellResponse.interaction (response : FourCellResponse) : ℝ :=
  (response.pcPresent - response.pcAbsent) -
    (response.bpPresent - response.bpAbsent)

/-- Omitting any one cell leaves two observationally equivalent completed
worlds with different interactions. -/
theorem every_missing_cell_is_nonidentifying :
    (∃ left right : FourCellResponse,
      left.bpPresent = right.bpPresent ∧
      left.pcAbsent = right.pcAbsent ∧
      left.pcPresent = right.pcPresent ∧
      left.interaction ≠ right.interaction) ∧
    (∃ left right : FourCellResponse,
      left.bpAbsent = right.bpAbsent ∧
      left.pcAbsent = right.pcAbsent ∧
      left.pcPresent = right.pcPresent ∧
      left.interaction ≠ right.interaction) ∧
    (∃ left right : FourCellResponse,
      left.bpAbsent = right.bpAbsent ∧
      left.bpPresent = right.bpPresent ∧
      left.pcPresent = right.pcPresent ∧
      left.interaction ≠ right.interaction) ∧
    (∃ left right : FourCellResponse,
      left.bpAbsent = right.bpAbsent ∧
      left.bpPresent = right.bpPresent ∧
      left.pcAbsent = right.pcAbsent ∧
      left.interaction ≠ right.interaction) := by
  constructor
  · exact ⟨⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, rfl, rfl, rfl, by norm_num [FourCellResponse.interaction]⟩
  constructor
  · exact ⟨⟨0, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, rfl, rfl, rfl, by norm_num [FourCellResponse.interaction]⟩
  constructor
  · exact ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩, rfl, rfl, rfl, by norm_num [FourCellResponse.interaction]⟩
  · exact ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 1⟩, rfl, rfl, rfl, by norm_num [FourCellResponse.interaction]⟩

/-! ## Continued versus joint-retraining non-identification -/

/-- Finite response decomposed into data, inherited parameters, inherited
optimizer, order, and residual interaction contributions. -/
structure HistoryResponse where
  data : ℝ
  parameters : ℝ
  optimizer : ℝ
  order : ℝ
  interaction : ℝ

def HistoryResponse.total (response : HistoryResponse) : ℝ :=
  response.data + response.parameters + response.optimizer +
    response.order + response.interaction

/-- A family with identical observed total but different parameter and
optimizer contributions. -/
def cancellingHistoryResponse (parameterContribution : ℝ) : HistoryResponse where
  data := 0
  parameters := parameterContribution
  optimizer := -parameterContribution
  order := 0
  interaction := 0

@[simp] theorem cancellingHistoryResponse_total
    (parameterContribution : ℝ) :
    (cancellingHistoryResponse parameterContribution).total = 0 := by
  simp [HistoryResponse.total, cancellingHistoryResponse]

/-- A continued-versus-joint total cannot identify inherited-parameter effect
without separately intervening on optimizer and other history factors. -/
theorem total_does_not_recover_parameter_history :
    ¬ ∃ recover : ℝ → ℝ,
      ∀ response : HistoryResponse,
        recover response.total = response.parameters := by
  apply no_uniform_recovery_of_observation_collision
    HistoryResponse.total HistoryResponse.parameters
    (left := cancellingHistoryResponse 0)
    (right := cancellingHistoryResponse 1)
  · simp
  · norm_num [cancellingHistoryResponse]

/-! ## Aggregate prior plus addressable sidecar -/

open RetrievalAddressedAcceleration

/-- Addressable state is an explicit sidecar beside the aggregate prior. -/
structure AggregatePriorWithSidecar
    (Aggregate Lineage Shape State : Type*) where
  aggregate : Aggregate
  sidecar : List (CachedInitializer Lineage Shape State)

/-- Forgetting addressability recovers the existing aggregate treatment. -/
def AggregatePriorWithSidecar.forgetSidecar
    {Aggregate Lineage Shape State : Type*}
    (memory : AggregatePriorWithSidecar Aggregate Lineage Shape State) : Aggregate :=
  memory.aggregate

@[simp] theorem forgetSidecar_eq_aggregate
    {Aggregate Lineage Shape State : Type*}
    (memory : AggregatePriorWithSidecar Aggregate Lineage Shape State) :
    memory.forgetSidecar = memory.aggregate := rfl

/-- A failed or disabled address lookup is fail-closed to the declared cold
initializer. -/
def routedInitializer
    {Lineage Shape State : Type*}
    (cold : State)
    (candidate : Option (CachedInitializer Lineage Shape State))
    (accept : CachedInitializer Lineage Shape State → Bool) : State :=
  match candidate with
  | none => cold
  | some record => if accept record then record.state else cold

@[simp] theorem routedInitializer_disabled_eq_cold
    {Lineage Shape State : Type*}
    (cold : State)
    (accept : CachedInitializer Lineage Shape State → Bool) :
    routedInitializer cold none accept = cold := rfl

theorem routedInitializer_rejected_eq_cold
    {Lineage Shape State : Type*}
    (cold : State) (record : CachedInitializer Lineage Shape State)
    (accept : CachedInitializer Lineage Shape State → Bool)
    (rejected : accept record = false) :
    routedInitializer cold (some record) accept = cold := by
  simp [routedInitializer, rejected]

/-- Fail-closed safety of the router itself.  If the acceptance predicate is
sound for the existing certified set, then every state the router can return is
either the declared cold initializer or a state carrying exact lineage, exact
shape, and basin membership.  This is a property of `routedInitializer`, not a
re-export of the underlying admission theorem: the disjunction ranges over the
router's whole output. -/
theorem routedInitializer_sound_accept_cold_or_certified
    {Lineage Shape State : Type*} [NormedAddCommGroup State]
    (currentLineage : Lineage) (currentShape : Shape)
    (center : State) (radius : ℝ)
    (cold : State)
    (candidate : Option (CachedInitializer Lineage Shape State))
    (accept : CachedInitializer Lineage Shape State → Bool)
    (acceptSound : ∀ record, accept record = true →
      record ∈ AdmissibleCacheSet currentLineage currentShape center radius) :
    routedInitializer cold candidate accept = cold ∨
      ∃ record, routedInitializer cold candidate accept = record.state ∧
        CacheCompatible currentLineage currentShape record ∧
        LocalAmortizedInitialization.InClosedBall center radius record.state := by
  match candidate with
  | none => exact Or.inl rfl
  | some record =>
      by_cases accepted : accept record = true
      · refine Or.inr ⟨record, ?_, ?_⟩
        · simp [routedInitializer, accepted]
        · exact selected_cache_is_compatible_and_in_basin currentLineage
            currentShape center radius record (acceptSound record accepted)
      · exact Or.inl (routedInitializer_rejected_eq_cold cold record accept
          (by simpa using accepted))

/-- The routing transition makes both observable outputs explicit: the chosen
initializer and the resulting memory.  The certified transition is read-only. -/
def sidecarRoutingTransition
    {Aggregate Lineage Shape State : Type*}
    (memory : AggregatePriorWithSidecar Aggregate Lineage Shape State)
    (cold : State)
    (candidate : Option (CachedInitializer Lineage Shape State))
    (accept : CachedInitializer Lineage Shape State → Bool) :
    State × AggregatePriorWithSidecar Aggregate Lineage Shape State :=
  (routedInitializer cold candidate accept, memory)

/-- Disabled routing returns the cold initializer and the original memory as
one exact transition result.  This holds by definition of the proposed
transition; it is an interface law for the design, not a measurement of any
deployed implementation. -/
@[simp] theorem sidecarRoutingTransition_disabled_eq_cold_original
    {Aggregate Lineage Shape State : Type*}
    (memory : AggregatePriorWithSidecar Aggregate Lineage Shape State)
    (cold : State)
    (accept : CachedInitializer Lineage Shape State → Bool) :
    sidecarRoutingTransition memory cold none accept = (cold, memory) := rfl

/-- Rejected routing is likewise exactly state preserving. -/
theorem sidecarRoutingTransition_rejected_eq_cold_original
    {Aggregate Lineage Shape State : Type*}
    (memory : AggregatePriorWithSidecar Aggregate Lineage Shape State)
    (cold : State) (record : CachedInitializer Lineage Shape State)
    (accept : CachedInitializer Lineage Shape State → Bool)
    (rejected : accept record = false) :
    sidecarRoutingTransition memory cold (some record) accept =
      (cold, memory) := by
  simp [sidecarRoutingTransition, routedInitializer, rejected]

/-- A contrasting transition exposes the storage mutation in its returned
memory rather than hiding it behind an initializer-only interface. -/
def mutatingSidecarRoutingTransition
    {Aggregate Lineage Shape State : Type*}
    (mutate : AggregatePriorWithSidecar Aggregate Lineage Shape State →
      AggregatePriorWithSidecar Aggregate Lineage Shape State)
    (memory : AggregatePriorWithSidecar Aggregate Lineage Shape State)
    (cold : State)
    (candidate : Option (CachedInitializer Lineage Shape State))
    (accept : CachedInitializer Lineage Shape State → Bool) :
    State × AggregatePriorWithSidecar Aggregate Lineage Shape State :=
  (routedInitializer cold candidate accept, mutate memory)

def routingMemoryFixture : AggregatePriorWithSidecar Bool Unit Unit ℕ where
  aggregate := true
  sidecar := []

def routingRecordFixture : CachedInitializer Unit Unit ℕ where
  lineage := ()
  shape := ()
  state := 7

/-- Negative fixture: a disabled router can still mutate storage if its
transition appends a record.  Cold-output equality alone is therefore not a
storage-preservation certificate. -/
theorem mutatingRouter_changes_storage_fixture :
    mutatingSidecarRoutingTransition
        (fun memory ↦ { memory with
          sidecar := routingRecordFixture :: memory.sidecar })
        routingMemoryFixture 0 none (fun _ ↦ false) ≠
      (0, routingMemoryFixture) := by
  intro equality
  have sidecarEquality := congrArg (fun output ↦ output.2.sidecar) equality
  simp [mutatingSidecarRoutingTransition, routedInitializer,
    routingMemoryFixture, routingRecordFixture] at sidecarEquality

/-- The inherited stale-lineage counterexample remains rejected in the
sidecar treatment. -/
theorem staleSidecarFixture_rejected :
    ¬ CacheCompatible true () staleCacheFixture :=
  staleCacheFixture_not_compatible

/-! ## Credit does not itself identify discovery -/

/-- A registered world pairs the four-cell credit response with the verified
program--target relation that its search actually produced. -/
structure CreditDiscoveryWorld where
  response : FourCellResponse
  discovery : SolveRelation Bool Bool

/-- Without a declared bridge, the credit interaction does not identify verified
discovery.  The two witnesses differ in every one of the four credit cells yet
share the same interaction value, so the collision is a genuine property of the
interaction estimand rather than of an arbitrary pair projection. -/
theorem interaction_does_not_uniformly_recover_discovery :
    ¬ ∃ recover : ℝ → SolveRelation Bool Bool,
      ∀ world : CreditDiscoveryWorld,
        recover world.response.interaction = world.discovery := by
  apply no_uniform_recovery_of_observation_collision
    (fun world ↦ world.response.interaction) CreditDiscoveryWorld.discovery
    (left := ⟨⟨0, 0, 0, 0⟩, ∅⟩)
    (right := ⟨⟨1, 1, 1, 1⟩, {(true, true)}⟩)
  · norm_num [FourCellResponse.interaction]
  · simp

end

end UnifiedMemoryInteraction

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
