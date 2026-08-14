import Mettapedia.MachineLearning.ContinualLearning.VirtuallyAddressedParameterMemory
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.FiniteSettlingGradientGap
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.GuardedFiniteAcceleration

/-!
# Retrieval-addressed predictive-coding acceleration

This file composes three previously separate contracts:

* resource-charged approximate addressing of stored initializers;
* finite-depth contraction and Lipschitz credit transport;
* fail-closed retention-advantage and total-work admission.

The main bound first converts addressed latent-energy regret into distance from
the settled state using strong convexity.  Predictive settling contracts that
distance geometrically, and a Lipschitz credit readout transports it to a
parameter-credit budget.  A cold finite reference, two realized-arithmetic
budgets, and guarded selection are then charged explicitly.

No claim is made that storage invariance implies retrieval invariance.  Cache
records therefore carry lineage and shape identities, while soft retrieval is
given a separate concentration bound and a counterexample remains available
when concentration is absent.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace RetrievalAddressedAcceleration

open scoped InnerProductSpace
open Mettapedia.MachineLearning.ContinualLearning
open Mettapedia.MachineLearning.ContinualLearning.VirtuallyAddressedParameterMemory
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
open Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.ModernHopfieldRetrieval
open Mettapedia.MachineLearning.NeuralNetworks.Architecture
open FiniteSolverSubstitution
open FiniteTrajectoryAcceleration
open GuardedFiniteAcceleration
open ConditionalCreditAdvantage
open MinimumInterferenceCredit
open LocalAmortizedInitialization

noncomputable section

/-! ## Lineage- and shape-bound cached initializers -/

/-- A cached PC initializer carries the model lineage and coordinate shape
under which its state was produced. -/
structure CachedInitializer (Lineage Shape State : Type*) where
  lineage : Lineage
  shape : Shape
  state : State

/-- Exact compatibility is deliberately stricter than merely possessing a
stored state: both parameter lineage and coordinate shape must match. -/
def CacheCompatible {Lineage Shape State : Type*}
    (currentLineage : Lineage) (currentShape : Shape)
    (record : CachedInitializer Lineage Shape State) : Prop :=
  record.lineage = currentLineage ∧ record.shape = currentShape

theorem cacheCompatible_lineage
    {Lineage Shape State : Type*}
    {currentLineage : Lineage} {currentShape : Shape}
    {record : CachedInitializer Lineage Shape State}
    (compatible : CacheCompatible currentLineage currentShape record) :
    record.lineage = currentLineage :=
  compatible.1

theorem cacheCompatible_shape
    {Lineage Shape State : Type*}
    {currentLineage : Lineage} {currentShape : Shape}
    {record : CachedInitializer Lineage Shape State}
    (compatible : CacheCompatible currentLineage currentShape record) :
    record.shape = currentShape :=
  compatible.2

/-- Selecting only from the compatibility set makes lineage/shape safety a
consequence of candidate-set membership rather than a payload assertion. -/
theorem selected_cache_is_compatible
    {Lineage Shape State : Type*}
    (currentLineage : Lineage) (currentShape : Shape)
    (record : CachedInitializer Lineage Shape State)
    (selected : record ∈ {candidate |
      CacheCompatible currentLineage currentShape candidate}) :
    CacheCompatible currentLineage currentShape record := by
  exact selected

/-- Runtime admission intersects identity compatibility with the certified
solver basin. -/
def AdmissibleCacheSet
    {Lineage Shape State : Type*} [NormedAddCommGroup State]
    (currentLineage : Lineage) (currentShape : Shape)
    (center : State) (radius : ℝ) :
    Set (CachedInitializer Lineage Shape State) :=
  {record | CacheCompatible currentLineage currentShape record ∧
    InClosedBall center radius record.state}

theorem selected_cache_is_compatible_and_in_basin
    {Lineage Shape State : Type*} [NormedAddCommGroup State]
    (currentLineage : Lineage) (currentShape : Shape)
    (center : State) (radius : ℝ)
    (record : CachedInitializer Lineage Shape State)
    (selected : record ∈ AdmissibleCacheSet currentLineage currentShape
      center radius) :
    CacheCompatible currentLineage currentShape record ∧
      InClosedBall center radius record.state := by
  exact selected

def staleCacheFixture : CachedInitializer Bool Unit ℝ :=
  { lineage := false, shape := (), state := 7 }

/-- A concrete stale record is rejected even though its state has the right
ambient Lean type and its shape agrees. -/
theorem staleCacheFixture_not_compatible :
    ¬ CacheCompatible true () staleCacheFixture := by
  simp [CacheCompatible, staleCacheFixture]

/-! ## Strong convexity converts address regret into initializer distance -/

variable {Address Latent Credit : Type*}
  [NormedAddCommGroup Latent] [InnerProductSpace ℝ Latent]
  [NormedAddCommGroup Credit]

/-- Latent energy exposed as an address objective through the initializer
stored at each address. -/
def initializerEnergy
    {mu L : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (initializer : Address → Latent) (address : Address) : ℝ :=
  model.energy (initializer address)

/-- Total initializer-energy gap certified from a stored comparator: its own
gap above equilibrium, the charged retrieval cost, and router suboptimality. -/
def addressedEnergyGap
    {mu L : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (initializer : Address → Latent) (resource : Address → ℝ)
    (target : Latent) (stored : Address) (penalty ε : ℝ) : ℝ :=
  model.energy (initializer stored) - model.energy target +
    penalty * resource stored + ε

/-- Quadratic growth restricted to an explicit certified region.  This is the
minimal energy hypothesis needed by a nonlinear runtime extractor; it is
strictly weaker than requiring global strong convexity. -/
def QuadraticGrowthOn
    (region : Set Latent) (energy : Latent → ℝ)
    (target : Latent) (mu : ℝ) : Prop :=
  ∀ state ∈ region,
    mu / 2 * ‖state - target‖ ^ 2 ≤ energy state - energy target

/-- Address objective for an arbitrary regional energy certificate. -/
def regionalInitializerEnergy
    (energy : Latent → ℝ) (initializer : Address → Latent)
    (address : Address) : ℝ :=
  energy (initializer address)

/-- Resource-charged addressed energy gap for a regional energy certificate. -/
def regionalAddressedEnergyGap
    (energy : Latent → ℝ) (initializer : Address → Latent)
    (resource : Address → ℝ) (target : Latent) (stored : Address)
    (penalty ε : ℝ) : ℝ :=
  energy (initializer stored) - energy target +
    penalty * resource stored + ε

/-- At a stationary target, the first-order strong-convexity certificate gives
the standard quadratic energy-growth inequality. -/
theorem strongConvex_energyGap_controls_distance_sq
    {mu L : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (target state : Latent) (targetStationary : model.gradient target = 0) :
    mu / 2 * ‖state - target‖ ^ 2 ≤
      model.energy state - model.energy target := by
  have supporting := model.strongConvexFirstOrder target state
  rw [targetStationary, inner_zero_left] at supporting
  linarith

/-- A globally strong-convex first-order model induces quadratic growth on
every chosen region. -/
theorem StrongSmoothLatentEnergy.quadraticGrowthOn
    {mu L : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (region : Set Latent) (target : Latent)
    (targetStationary : model.gradient target = 0) :
    QuadraticGrowthOn region model.energy target mu := by
  intro state _stateInRegion
  exact strongConvex_energyGap_controls_distance_sq model target state
    targetStationary

omit [InnerProductSpace ℝ Latent] in
/- Regional crown for the address-to-initializer bridge.  Only the returned
initializer must lie in the quadratic-growth region. -/
theorem epsilonOptimal_regionalInitializer_distance_le
    {mu : ℝ} (energy : Latent → ℝ) (muPositive : 0 < mu)
    (region : Set Latent) (target : Latent)
    (quadraticGrowth : QuadraticGrowthOn region energy target mu)
    (initializer : Address → Latent) (resource : Address → ℝ)
    (candidates : Set Address)
    (returned stored : Address) (penalty ε : ℝ)
    (penaltyNonneg : 0 ≤ penalty)
    (resourceNonneg : ∀ address, 0 ≤ resource address)
    (optimal : EpsilonOptimalOn candidates
      (penalizedEnergy (regionalInitializerEnergy energy initializer)
        resource penalty) returned ε)
    (storedAvailable : stored ∈ candidates)
    (returnedInRegion : initializer returned ∈ region) :
    ‖initializer returned - target‖ ≤
      Real.sqrt (2 * regionalAddressedEnergyGap energy initializer resource
        target stored penalty ε / mu) := by
  have selectedEnergy := epsilonOptimal_rawEnergy_le_stored_add_cost candidates
    (regionalInitializerEnergy energy initializer) resource penalty ε returned
    stored penaltyNonneg resourceNonneg optimal storedAvailable
  have growth := quadraticGrowth (initializer returned) returnedInRegion
  have budgetLower :
      mu / 2 * ‖initializer returned - target‖ ^ 2 ≤
        regionalAddressedEnergyGap energy initializer resource target stored
          penalty ε := by
    change energy (initializer returned) ≤
      energy (initializer stored) + penalty * resource stored + ε at selectedEnergy
    unfold regionalAddressedEnergyGap
    linarith
  have budgetNonneg :
      0 ≤ regionalAddressedEnergyGap energy initializer resource target stored
        penalty ε := by
    have leftNonneg : 0 ≤ mu / 2 * ‖initializer returned - target‖ ^ 2 :=
      mul_nonneg (div_nonneg muPositive.le (by norm_num)) (sq_nonneg _)
    exact le_trans leftNonneg budgetLower
  have radicandNonneg :
      0 ≤ 2 * regionalAddressedEnergyGap energy initializer resource target
        stored penalty ε / mu :=
    div_nonneg (mul_nonneg (by norm_num) budgetNonneg) muPositive.le
  rw [Real.le_sqrt (norm_nonneg _) radicandNonneg]
  apply (le_div_iff₀ muPositive).2
  nlinarith

/-- Positive strong convexity turns the energy gap into a squared-distance
bound. -/
theorem strongConvex_distance_sq_le_two_energyGap_div
    {mu L : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (muPositive : 0 < mu)
    (target state : Latent) (targetStationary : model.gradient target = 0) :
    ‖state - target‖ ^ 2 ≤
      2 * (model.energy state - model.energy target) / mu := by
  have growth := strongConvex_energyGap_controls_distance_sq
    model target state targetStationary
  apply (le_div_iff₀ muPositive).2
  nlinarith

/-- Square-root form of the energy-to-distance bridge. -/
theorem strongConvex_distance_le_sqrt_two_energyGap_div
    {mu L : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (muPositive : 0 < mu)
    (target state : Latent) (targetStationary : model.gradient target = 0) :
    ‖state - target‖ ≤
      Real.sqrt (2 * (model.energy state - model.energy target) / mu) := by
  have growth := strongConvex_energyGap_controls_distance_sq
    model target state targetStationary
  have gapNonneg : 0 ≤ model.energy state - model.energy target := by
    have leftNonneg : 0 ≤ mu / 2 * ‖state - target‖ ^ 2 :=
      mul_nonneg (div_nonneg muPositive.le (by norm_num)) (sq_nonneg _)
    exact le_trans leftNonneg growth
  have radicandNonneg :
      0 ≤ 2 * (model.energy state - model.energy target) / mu :=
    div_nonneg (mul_nonneg (by norm_num) gapNonneg) muPositive.le
  rw [Real.le_sqrt (norm_nonneg _) radicandNonneg]
  exact strongConvex_distance_sq_le_two_energyGap_div model muPositive
    target state targetStationary

/-- The resource-aware VAMP router bound specialized to latent initializer
energy. -/
theorem epsilonOptimal_initializerEnergy_le_stored_add_cost
    {mu L : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (initializer : Address → Latent) (resource : Address → ℝ)
    (candidates : Set Address)
    (returned stored : Address) (penalty ε : ℝ)
    (penaltyNonneg : 0 ≤ penalty)
    (resourceNonneg : ∀ address, 0 ≤ resource address)
    (optimal : EpsilonOptimalOn candidates
      (penalizedEnergy (initializerEnergy model initializer) resource penalty)
      returned ε)
    (storedAvailable : stored ∈ candidates) :
    model.energy (initializer returned) ≤
      model.energy (initializer stored) + penalty * resource stored + ε := by
  exact epsilonOptimal_rawEnergy_le_stored_add_cost candidates
    (initializerEnergy model initializer) resource penalty ε returned stored
    penaltyNonneg resourceNonneg optimal storedAvailable

/-- Crown address-to-initializer theorem.  Availability of one stored
comparator, approximate resource-charged selection, and local strong convexity
produce an explicit distance certificate for the returned warm initializer. -/
theorem epsilonOptimal_initializer_distance_le
    {mu L : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (muPositive : 0 < mu)
    (initializer : Address → Latent) (resource : Address → ℝ)
    (candidates : Set Address)
    (returned stored : Address) (penalty ε : ℝ)
    (penaltyNonneg : 0 ≤ penalty)
    (resourceNonneg : ∀ address, 0 ≤ resource address)
    (optimal : EpsilonOptimalOn candidates
      (penalizedEnergy (initializerEnergy model initializer) resource penalty)
      returned ε)
    (storedAvailable : stored ∈ candidates)
    (target : Latent) (targetStationary : model.gradient target = 0) :
    ‖initializer returned - target‖ ≤
      Real.sqrt (2 * addressedEnergyGap model initializer resource target stored
        penalty ε / mu) := by
  have selectedEnergy := epsilonOptimal_initializerEnergy_le_stored_add_cost
    model initializer resource candidates returned stored penalty ε
    penaltyNonneg resourceNonneg optimal storedAvailable
  have growth := strongConvex_energyGap_controls_distance_sq model target
    (initializer returned) targetStationary
  have budgetLower :
      mu / 2 * ‖initializer returned - target‖ ^ 2 ≤
        addressedEnergyGap model initializer resource target stored penalty ε := by
    unfold addressedEnergyGap
    linarith
  have budgetNonneg :
      0 ≤ addressedEnergyGap model initializer resource target stored penalty ε := by
    have leftNonneg : 0 ≤ mu / 2 * ‖initializer returned - target‖ ^ 2 :=
      mul_nonneg (div_nonneg muPositive.le (by norm_num)) (sq_nonneg _)
    exact le_trans leftNonneg budgetLower
  have radicandNonneg :
      0 ≤ 2 * addressedEnergyGap model initializer resource target stored
          penalty ε / mu :=
    div_nonneg (mul_nonneg (by norm_num) budgetNonneg) muPositive.le
  rw [Real.le_sqrt (norm_nonneg _) radicandNonneg]
  apply (le_div_iff₀ muPositive).2
  nlinarith

/-- The selected warm initializer's distance to an arbitrary cold initializer
is bounded by its addressed equilibrium radius plus the cold radius. -/
theorem epsilonOptimal_initializer_to_cold_distance_le
    {mu L : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (muPositive : 0 < mu)
    (initializer : Address → Latent) (resource : Address → ℝ)
    (candidates : Set Address)
    (returned stored : Address) (penalty ε : ℝ)
    (penaltyNonneg : 0 ≤ penalty)
    (resourceNonneg : ∀ address, 0 ≤ resource address)
    (optimal : EpsilonOptimalOn candidates
      (penalizedEnergy (initializerEnergy model initializer) resource penalty)
      returned ε)
    (storedAvailable : stored ∈ candidates)
    (target cold : Latent) (targetStationary : model.gradient target = 0) :
    ‖initializer returned - cold‖ ≤
      Real.sqrt (2 * addressedEnergyGap model initializer resource target stored
        penalty ε / mu) + ‖cold - target‖ := by
  have initializerBound := epsilonOptimal_initializer_distance_le model
    muPositive initializer resource candidates returned stored penalty ε
    penaltyNonneg resourceNonneg optimal storedAvailable target targetStationary
  calc
    ‖initializer returned - cold‖ ≤
        ‖initializer returned - target‖ + ‖target - cold‖ := by
      simpa only [sub_add_sub_cancel] using
        norm_add_le (initializer returned - target) (target - cold)
    _ ≤ Real.sqrt (2 * addressedEnergyGap model initializer resource target stored
          penalty ε / mu) + ‖target - cold‖ :=
      add_le_add initializerBound le_rfl
    _ = Real.sqrt (2 * addressedEnergyGap model initializer resource target stored
          penalty ε / mu) + ‖cold - target‖ := by
      rw [show target - cold = -(cold - target) by abel, norm_neg]

omit [InnerProductSpace ℝ Latent] in
theorem epsilonOptimal_regionalInitializer_to_cold_distance_le
    {mu : ℝ} (energy : Latent → ℝ) (muPositive : 0 < mu)
    (region : Set Latent) (target cold : Latent)
    (quadraticGrowth : QuadraticGrowthOn region energy target mu)
    (initializer : Address → Latent) (resource : Address → ℝ)
    (candidates : Set Address)
    (returned stored : Address) (penalty ε : ℝ)
    (penaltyNonneg : 0 ≤ penalty)
    (resourceNonneg : ∀ address, 0 ≤ resource address)
    (optimal : EpsilonOptimalOn candidates
      (penalizedEnergy (regionalInitializerEnergy energy initializer)
        resource penalty) returned ε)
    (storedAvailable : stored ∈ candidates)
    (returnedInRegion : initializer returned ∈ region) :
    ‖initializer returned - cold‖ ≤
      Real.sqrt (2 * regionalAddressedEnergyGap energy initializer resource
        target stored penalty ε / mu) + ‖cold - target‖ := by
  have initializerBound := epsilonOptimal_regionalInitializer_distance_le
    energy muPositive region target quadraticGrowth initializer resource
    candidates returned stored penalty ε penaltyNonneg resourceNonneg optimal
    storedAvailable returnedInRegion
  calc
    ‖initializer returned - cold‖ ≤
        ‖initializer returned - target‖ + ‖target - cold‖ := by
      simpa only [sub_add_sub_cancel] using
        norm_add_le (initializer returned - target) (target - cold)
    _ ≤ Real.sqrt (2 * regionalAddressedEnergyGap energy initializer resource
          target stored penalty ε / mu) + ‖target - cold‖ :=
      add_le_add initializerBound le_rfl
    _ = Real.sqrt (2 * regionalAddressedEnergyGap energy initializer resource
          target stored penalty ε / mu) + ‖cold - target‖ := by
      rw [show target - cold = -(cold - target) by abel, norm_neg]

/-! ## Regional finite-reference certificate -/

/-- The runtime-facing ideal-credit theorem.  Addressing controls the
warm/cold initializer discrepancy, while a local contraction certificate and
the observable first cold residual control the omitted finite cold tail.  No
fixed point or global contraction is assumed for the solver. -/
theorem local_addressedWarmShort_credit_difference_to_coldLong_le
    {mu L K : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (muPositive : 0 < mu)
    (initializer : Address → Latent) (resource : Address → ℝ)
    (candidates : Set Address)
    (returned stored : Address) (penalty ε : ℝ)
    (penaltyNonneg : 0 ≤ penalty)
    (resourceNonneg : ∀ address, 0 ≤ resource address)
    (optimal : EpsilonOptimalOn candidates
      (penalizedEnergy (initializerEnergy model initializer) resource penalty)
      returned ε)
    (storedAvailable : stored ∈ candidates)
    (target cold : Latent) (targetStationary : model.gradient target = 0)
    {solver : Latent → Latent} {center : Latent} {radius : ℝ}
    (certificate : LocalContractionCertificate solver center radius)
    (warmInBasin : InClosedBall center radius (initializer returned))
    (coldInBasin : InClosedBall center radius cold)
    (readout : Latent → Credit) (KNonneg : 0 ≤ K)
    (readoutLipschitz : CreditReadoutPairwiseLipschitz readout K)
    (warmSteps omittedSteps : ℕ) :
    ‖readout (solver^[warmSteps] (initializer returned)) -
        readout (solver^[warmSteps + omittedSteps] cold)‖ ≤
      K * (certificate.factor ^ warmSteps *
        (Real.sqrt (2 * addressedEnergyGap model initializer resource target stored
            penalty ε / mu) + ‖cold - target‖ +
          geometricPrefix certificate.factor omittedSteps *
            ‖cold - solver cold‖)) := by
  have finiteReferenceBound :=
    local_warmShort_credit_difference_to_coldLong_le certificate readout K
      KNonneg readoutLipschitz (initializer returned) cold warmInBasin
      coldInBasin warmSteps omittedSteps
  have initializerBound := epsilonOptimal_initializer_to_cold_distance_le model
    muPositive initializer resource candidates returned stored penalty ε
    penaltyNonneg resourceNonneg optimal storedAvailable target cold
    targetStationary
  apply le_trans finiteReferenceBound
  apply mul_le_mul_of_nonneg_left _ KNonneg
  apply mul_le_mul_of_nonneg_left _
    (pow_nonneg certificate.factor_nonneg warmSteps)
  exact add_le_add initializerBound le_rfl

/-- Regional realized-arithmetic theorem for the exact production contract. -/
theorem local_realized_addressedWarmShort_credit_difference_to_coldLong_le
    {mu L K : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (muPositive : 0 < mu)
    (initializer : Address → Latent) (resource : Address → ℝ)
    (candidates : Set Address)
    (returned stored : Address) (penalty ε : ℝ)
    (penaltyNonneg : 0 ≤ penalty)
    (resourceNonneg : ∀ address, 0 ≤ resource address)
    (optimal : EpsilonOptimalOn candidates
      (penalizedEnergy (initializerEnergy model initializer) resource penalty)
      returned ε)
    (storedAvailable : stored ∈ candidates)
    (target cold : Latent) (targetStationary : model.gradient target = 0)
    {solver : Latent → Latent} {center : Latent} {radius : ℝ}
    (certificate : LocalContractionCertificate solver center radius)
    (warmInBasin : InClosedBall center radius (initializer returned))
    (coldInBasin : InClosedBall center radius cold)
    (readout : Latent → Credit) (KNonneg : 0 ≤ K)
    (readoutLipschitz : CreditReadoutPairwiseLipschitz readout K)
    (warmSteps omittedSteps : ℕ)
    (candidateRealized referenceRealized : Credit)
    (candidatePrecisionError referencePrecisionError : ℝ)
    (candidateReplayBound :
      ‖candidateRealized - readout
        (solver^[warmSteps] (initializer returned))‖ ≤ candidatePrecisionError)
    (referenceReplayBound :
      ‖referenceRealized - readout
        (solver^[warmSteps + omittedSteps] cold)‖ ≤ referencePrecisionError) :
    ‖candidateRealized - referenceRealized‖ ≤
      candidatePrecisionError +
        K * (certificate.factor ^ warmSteps *
          (Real.sqrt (2 * addressedEnergyGap model initializer resource target stored
              penalty ε / mu) + ‖cold - target‖ +
            geometricPrefix certificate.factor omittedSteps *
              ‖cold - solver cold‖)) +
        referencePrecisionError := by
  apply realized_credit_difference_le
    (readout (solver^[warmSteps] (initializer returned)))
    (readout (solver^[warmSteps + omittedSteps] cold))
    candidateRealized referenceRealized
    (K * (certificate.factor ^ warmSteps *
      (Real.sqrt (2 * addressedEnergyGap model initializer resource target stored
          penalty ε / mu) + ‖cold - target‖ +
        geometricPrefix certificate.factor omittedSteps *
          ‖cold - solver cold‖)))
    candidatePrecisionError referencePrecisionError
  · exact local_addressedWarmShort_credit_difference_to_coldLong_le model
      muPositive initializer resource candidates returned stored penalty ε
      penaltyNonneg resourceNonneg optimal storedAvailable target cold
      targetStationary certificate warmInBasin coldInBasin readout KNonneg
      readoutLipschitz warmSteps omittedSteps
  · exact candidateReplayBound
  · exact referenceReplayBound

omit [InnerProductSpace ℝ Latent] in
/- Fully regional finite-reference theorem.  The solver is only contractive
inside its invariant basin, and the energy needs quadratic growth only on the
separately declared energy region containing the selected initializer. -/
theorem regional_addressedWarmShort_credit_difference_to_coldLong_le
    {mu K : ℝ} (energy : Latent → ℝ) (muPositive : 0 < mu)
    (energyRegion : Set Latent) (target cold : Latent)
    (quadraticGrowth : QuadraticGrowthOn energyRegion energy target mu)
    (initializer : Address → Latent) (resource : Address → ℝ)
    (candidates : Set Address)
    (returned stored : Address) (penalty ε : ℝ)
    (penaltyNonneg : 0 ≤ penalty)
    (resourceNonneg : ∀ address, 0 ≤ resource address)
    (optimal : EpsilonOptimalOn candidates
      (penalizedEnergy (regionalInitializerEnergy energy initializer)
        resource penalty) returned ε)
    (storedAvailable : stored ∈ candidates)
    (returnedInEnergyRegion : initializer returned ∈ energyRegion)
    {solver : Latent → Latent} {center : Latent} {radius : ℝ}
    (certificate : LocalContractionCertificate solver center radius)
    (warmInBasin : InClosedBall center radius (initializer returned))
    (coldInBasin : InClosedBall center radius cold)
    (readout : Latent → Credit) (KNonneg : 0 ≤ K)
    (readoutLipschitz : CreditReadoutPairwiseLipschitz readout K)
    (warmSteps omittedSteps : ℕ) :
    ‖readout (solver^[warmSteps] (initializer returned)) -
        readout (solver^[warmSteps + omittedSteps] cold)‖ ≤
      K * (certificate.factor ^ warmSteps *
        (Real.sqrt (2 * regionalAddressedEnergyGap energy initializer resource
            target stored penalty ε / mu) + ‖cold - target‖ +
          geometricPrefix certificate.factor omittedSteps *
            ‖cold - solver cold‖)) := by
  have finiteReferenceBound :=
    local_warmShort_credit_difference_to_coldLong_le certificate readout K
      KNonneg readoutLipschitz (initializer returned) cold warmInBasin
      coldInBasin warmSteps omittedSteps
  have initializerBound :=
    epsilonOptimal_regionalInitializer_to_cold_distance_le energy muPositive
      energyRegion target cold quadraticGrowth initializer resource candidates
      returned stored penalty ε penaltyNonneg resourceNonneg optimal
      storedAvailable returnedInEnergyRegion
  apply le_trans finiteReferenceBound
  apply mul_le_mul_of_nonneg_left _ KNonneg
  apply mul_le_mul_of_nonneg_left _
    (pow_nonneg certificate.factor_nonneg warmSteps)
  exact add_le_add initializerBound le_rfl

omit [InnerProductSpace ℝ Latent] in
theorem regional_realized_addressedWarmShort_credit_difference_to_coldLong_le
    {mu K : ℝ} (energy : Latent → ℝ) (muPositive : 0 < mu)
    (energyRegion : Set Latent) (target cold : Latent)
    (quadraticGrowth : QuadraticGrowthOn energyRegion energy target mu)
    (initializer : Address → Latent) (resource : Address → ℝ)
    (candidates : Set Address)
    (returned stored : Address) (penalty ε : ℝ)
    (penaltyNonneg : 0 ≤ penalty)
    (resourceNonneg : ∀ address, 0 ≤ resource address)
    (optimal : EpsilonOptimalOn candidates
      (penalizedEnergy (regionalInitializerEnergy energy initializer)
        resource penalty) returned ε)
    (storedAvailable : stored ∈ candidates)
    (returnedInEnergyRegion : initializer returned ∈ energyRegion)
    {solver : Latent → Latent} {center : Latent} {radius : ℝ}
    (certificate : LocalContractionCertificate solver center radius)
    (warmInBasin : InClosedBall center radius (initializer returned))
    (coldInBasin : InClosedBall center radius cold)
    (readout : Latent → Credit) (KNonneg : 0 ≤ K)
    (readoutLipschitz : CreditReadoutPairwiseLipschitz readout K)
    (warmSteps omittedSteps : ℕ)
    (candidateRealized referenceRealized : Credit)
    (candidatePrecisionError referencePrecisionError : ℝ)
    (candidateReplayBound :
      ‖candidateRealized - readout
        (solver^[warmSteps] (initializer returned))‖ ≤ candidatePrecisionError)
    (referenceReplayBound :
      ‖referenceRealized - readout
        (solver^[warmSteps + omittedSteps] cold)‖ ≤ referencePrecisionError) :
    ‖candidateRealized - referenceRealized‖ ≤
      candidatePrecisionError +
        K * (certificate.factor ^ warmSteps *
          (Real.sqrt (2 * regionalAddressedEnergyGap energy initializer resource
              target stored penalty ε / mu) + ‖cold - target‖ +
            geometricPrefix certificate.factor omittedSteps *
              ‖cold - solver cold‖)) +
        referencePrecisionError := by
  apply realized_credit_difference_le
    (readout (solver^[warmSteps] (initializer returned)))
    (readout (solver^[warmSteps + omittedSteps] cold))
    candidateRealized referenceRealized
    (K * (certificate.factor ^ warmSteps *
      (Real.sqrt (2 * regionalAddressedEnergyGap energy initializer resource
          target stored penalty ε / mu) + ‖cold - target‖ +
        geometricPrefix certificate.factor omittedSteps *
          ‖cold - solver cold‖)))
    candidatePrecisionError referencePrecisionError
  · exact regional_addressedWarmShort_credit_difference_to_coldLong_le energy
      muPositive energyRegion target cold quadraticGrowth initializer resource
      candidates returned stored penalty ε penaltyNonneg resourceNonneg optimal
      storedAvailable returnedInEnergyRegion certificate warmInBasin coldInBasin
      readout KNonneg readoutLipschitz warmSteps omittedSteps
  · exact candidateReplayBound
  · exact referenceReplayBound

/-! ## Addressed finite settling and credit -/

/-- Address regret contracts through the actual Hilbert gradient-settling
map. -/
theorem addressedSettling_distance_le
    {mu L rate : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (muPositive : 0 < mu) (LNonneg : 0 ≤ L) (rateNonneg : 0 ≤ rate)
    (coefficientNonneg :
      0 ≤ hilbertSettlingContractionSq mu L rate)
    (initializer : Address → Latent) (resource : Address → ℝ)
    (candidates : Set Address)
    (returned stored : Address) (penalty ε : ℝ)
    (penaltyNonneg : 0 ≤ penalty)
    (resourceNonneg : ∀ address, 0 ≤ resource address)
    (optimal : EpsilonOptimalOn candidates
      (penalizedEnergy (initializerEnergy model initializer) resource penalty)
      returned ε)
    (storedAvailable : stored ∈ candidates)
    (target : Latent) (targetStationary : model.gradient target = 0)
    (sweeps : ℕ) :
    ‖(hilbertSettlingStep model rate)^[sweeps] (initializer returned) - target‖ ≤
      hilbertSettlingContraction mu L rate ^ sweeps *
        Real.sqrt (2 * addressedEnergyGap model initializer resource target stored
          penalty ε / mu) := by
  have iterateBound := hilbertSettling_iterate_distance_le model LNonneg
    rateNonneg coefficientNonneg target (initializer returned)
    targetStationary sweeps
  have initializerBound := epsilonOptimal_initializer_distance_le model
    muPositive initializer resource candidates returned stored penalty ε
    penaltyNonneg resourceNonneg optimal storedAvailable target targetStationary
  exact le_trans iterateBound (mul_le_mul_of_nonneg_left initializerBound
    (pow_nonneg (hilbertSettlingContraction_nonneg mu L rate) sweeps))

/-- Addressed settling transported through a Lipschitz parameter-credit
readout. -/
theorem addressedSettling_credit_to_equilibrium_le
    {mu L rate K : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (muPositive : 0 < mu) (LNonneg : 0 ≤ L) (rateNonneg : 0 ≤ rate)
    (coefficientNonneg :
      0 ≤ hilbertSettlingContractionSq mu L rate)
    (initializer : Address → Latent) (resource : Address → ℝ)
    (candidates : Set Address)
    (returned stored : Address) (penalty ε : ℝ)
    (penaltyNonneg : 0 ≤ penalty)
    (resourceNonneg : ∀ address, 0 ≤ resource address)
    (optimal : EpsilonOptimalOn candidates
      (penalizedEnergy (initializerEnergy model initializer) resource penalty)
      returned ε)
    (storedAvailable : stored ∈ candidates)
    (target : Latent) (targetStationary : model.gradient target = 0)
    (readout : Latent → Credit) (KNonneg : 0 ≤ K)
    (readoutLipschitz : HilbertGradientReadoutLipschitzAt readout target K)
    (sweeps : ℕ) :
    ‖readout ((hilbertSettlingStep model rate)^[sweeps]
          (initializer returned)) - readout target‖ ≤
      K * (hilbertSettlingContraction mu L rate ^ sweeps *
        Real.sqrt (2 * addressedEnergyGap model initializer resource target stored
          penalty ε / mu)) := by
  calc
    ‖readout ((hilbertSettlingStep model rate)^[sweeps]
          (initializer returned)) - readout target‖ ≤
        K * ‖(hilbertSettlingStep model rate)^[sweeps]
          (initializer returned) - target‖ :=
      readoutLipschitz _
    _ ≤ K * (hilbertSettlingContraction mu L rate ^ sweeps *
        Real.sqrt (2 * addressedEnergyGap model initializer resource target stored
          penalty ε / mu)) :=
      mul_le_mul_of_nonneg_left
        (addressedSettling_distance_le model muPositive LNonneg rateNonneg
          coefficientNonneg initializer resource candidates returned stored
          penalty ε penaltyNonneg resourceNonneg optimal storedAvailable target
          targetStationary sweeps)
        KNonneg

/-- Ideal-credit comparison between the addressed warm path and an arbitrary
cold finite path converging to the same latent target. -/
theorem addressedWarm_cold_credit_difference_le
    {mu L rate K : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (muPositive : 0 < mu) (LNonneg : 0 ≤ L) (rateNonneg : 0 ≤ rate)
    (coefficientNonneg :
      0 ≤ hilbertSettlingContractionSq mu L rate)
    (initializer : Address → Latent) (resource : Address → ℝ)
    (candidates : Set Address)
    (returned stored : Address) (penalty ε : ℝ)
    (penaltyNonneg : 0 ≤ penalty)
    (resourceNonneg : ∀ address, 0 ≤ resource address)
    (optimal : EpsilonOptimalOn candidates
      (penalizedEnergy (initializerEnergy model initializer) resource penalty)
      returned ε)
    (storedAvailable : stored ∈ candidates)
    (target cold : Latent) (targetStationary : model.gradient target = 0)
    (readout : Latent → Credit) (KNonneg : 0 ≤ K)
    (readoutLipschitz : HilbertGradientReadoutLipschitzAt readout target K)
    (warmSteps coldSteps : ℕ) :
    ‖readout ((hilbertSettlingStep model rate)^[warmSteps]
          (initializer returned)) -
        readout ((hilbertSettlingStep model rate)^[coldSteps] cold)‖ ≤
      K * (hilbertSettlingContraction mu L rate ^ warmSteps *
          Real.sqrt (2 * addressedEnergyGap model initializer resource target stored
            penalty ε / mu)) +
        K * (hilbertSettlingContraction mu L rate ^ coldSteps *
          ‖cold - target‖) := by
  let warmSettled := (hilbertSettlingStep model rate)^[warmSteps]
    (initializer returned)
  let coldSettled := (hilbertSettlingStep model rate)^[coldSteps] cold
  have warmBound := addressedSettling_credit_to_equilibrium_le model muPositive
    LNonneg rateNonneg coefficientNonneg initializer resource candidates
    returned stored penalty ε penaltyNonneg resourceNonneg optimal
    storedAvailable target targetStationary readout KNonneg readoutLipschitz
    warmSteps
  have coldDistance := hilbertSettling_iterate_distance_le model LNonneg
    rateNonneg coefficientNonneg target cold targetStationary coldSteps
  have coldBound :
      ‖readout coldSettled - readout target‖ ≤
        K * (hilbertSettlingContraction mu L rate ^ coldSteps *
          ‖cold - target‖) := by
    calc
      ‖readout coldSettled - readout target‖ ≤ K * ‖coldSettled - target‖ :=
        readoutLipschitz coldSettled
      _ ≤ K * (hilbertSettlingContraction mu L rate ^ coldSteps *
          ‖cold - target‖) := mul_le_mul_of_nonneg_left coldDistance KNonneg
  have reverseColdBound :
      ‖readout target - readout coldSettled‖ ≤
        K * (hilbertSettlingContraction mu L rate ^ coldSteps *
          ‖cold - target‖) := by
    rw [show readout target - readout coldSettled =
      -(readout coldSettled - readout target) by abel, norm_neg]
    exact coldBound
  calc
    ‖readout warmSettled - readout coldSettled‖ ≤
        ‖readout warmSettled - readout target‖ +
          ‖readout target - readout coldSettled‖ := by
      simpa only [sub_add_sub_cancel] using
        norm_add_le (readout warmSettled - readout target)
          (readout target - readout coldSettled)
    _ ≤ K * (hilbertSettlingContraction mu L rate ^ warmSteps *
          Real.sqrt (2 * addressedEnergyGap model initializer resource target stored
            penalty ε / mu)) +
        K * (hilbertSettlingContraction mu L rate ^ coldSteps *
          ‖cold - target‖) := add_le_add warmBound reverseColdBound

/-! ## Realized arithmetic and fail-closed advantage -/

/-- Realized candidate/reference credits charge the addressed finite-depth
budget plus both endpoint arithmetic errors. -/
theorem realized_addressedWarm_cold_credit_difference_le
    {mu L rate K : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (muPositive : 0 < mu) (LNonneg : 0 ≤ L) (rateNonneg : 0 ≤ rate)
    (coefficientNonneg :
      0 ≤ hilbertSettlingContractionSq mu L rate)
    (initializer : Address → Latent) (resource : Address → ℝ)
    (candidates : Set Address)
    (returned stored : Address) (penalty ε : ℝ)
    (penaltyNonneg : 0 ≤ penalty)
    (resourceNonneg : ∀ address, 0 ≤ resource address)
    (optimal : EpsilonOptimalOn candidates
      (penalizedEnergy (initializerEnergy model initializer) resource penalty)
      returned ε)
    (storedAvailable : stored ∈ candidates)
    (target cold : Latent) (targetStationary : model.gradient target = 0)
    (readout : Latent → Credit) (KNonneg : 0 ≤ K)
    (readoutLipschitz : HilbertGradientReadoutLipschitzAt readout target K)
    (warmSteps coldSteps : ℕ)
    (candidateRealized referenceRealized : Credit)
    (candidatePrecisionError referencePrecisionError : ℝ)
    (candidateReplayBound :
      ‖candidateRealized - readout
        ((hilbertSettlingStep model rate)^[warmSteps]
          (initializer returned))‖ ≤ candidatePrecisionError)
    (referenceReplayBound :
      ‖referenceRealized - readout
        ((hilbertSettlingStep model rate)^[coldSteps] cold)‖ ≤
          referencePrecisionError) :
    ‖candidateRealized - referenceRealized‖ ≤
      candidatePrecisionError +
        (K * (hilbertSettlingContraction mu L rate ^ warmSteps *
            Real.sqrt (2 * addressedEnergyGap model initializer resource target stored
              penalty ε / mu)) +
          K * (hilbertSettlingContraction mu L rate ^ coldSteps *
            ‖cold - target‖)) +
        referencePrecisionError := by
  apply realized_credit_difference_le
    (readout ((hilbertSettlingStep model rate)^[warmSteps]
      (initializer returned)))
    (readout ((hilbertSettlingStep model rate)^[coldSteps] cold))
    candidateRealized referenceRealized
    (K * (hilbertSettlingContraction mu L rate ^ warmSteps *
        Real.sqrt (2 * addressedEnergyGap model initializer resource target stored
          penalty ε / mu)) +
      K * (hilbertSettlingContraction mu L rate ^ coldSteps *
        ‖cold - target‖))
    candidatePrecisionError referencePrecisionError
  · exact addressedWarm_cold_credit_difference_le model muPositive LNonneg
      rateNonneg coefficientNonneg initializer resource candidates returned
      stored penalty ε penaltyNonneg resourceNonneg optimal storedAvailable
      target cold targetStationary readout KNonneg readoutLipschitz warmSteps
      coldSteps
  · exact candidateReplayBound
  · exact referenceReplayBound

section GuardedCrown

variable [InnerProductSpace ℝ Credit]

/-- End-to-end scientific crown.  Addressing, finite settling, and realized
arithmetic supply the candidate/reference norm gate; rejection returns the
authenticated cold credit exactly. -/
theorem guardedAddressedWarm_preserves_retentionAdvantage
    {mu L rate K : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (muPositive : 0 < mu) (LNonneg : 0 ≤ L) (rateNonneg : 0 ≤ rate)
    (coefficientNonneg :
      0 ≤ hilbertSettlingContractionSq mu L rate)
    (initializer : Address → Latent) (resource : Address → ℝ)
    (candidates : Set Address)
    (returned stored : Address) (penalty ε : ℝ)
    (penaltyNonneg : 0 ≤ penalty)
    (resourceNonneg : ∀ address, 0 ≤ resource address)
    (optimal : EpsilonOptimalOn candidates
      (penalizedEnergy (initializerEnergy model initializer) resource penalty)
      returned ε)
    (storedAvailable : stored ∈ candidates)
    (target cold : Latent) (targetStationary : model.gradient target = 0)
    (readout : Latent → Credit) (KNonneg : 0 ≤ K)
    (readoutLipschitz : HilbertGradientReadoutLipschitzAt readout target K)
    (warmSteps coldSteps : ℕ)
    (candidateRealized referenceRealized : Credit)
    (candidatePrecisionError referencePrecisionError : ℝ)
    (candidateReplayBound :
      ‖candidateRealized - readout
        ((hilbertSettlingStep model rate)^[warmSteps]
          (initializer returned))‖ ≤ candidatePrecisionError)
    (referenceReplayBound :
      ‖referenceRealized - readout
        ((hilbertSettlingStep model rate)^[coldSteps] cold)‖ ≤
          referencePrecisionError)
    (current replay baseline : Credit) (retentionWeight : ℝ)
    (admitted : Bool)
    (referenceAdvantage :
      retentionWeightedScore current replay retentionWeight baseline <
        retentionWeightedScore current replay retentionWeight referenceRealized)
    (gate : admitted = true →
      let error := candidatePrecisionError +
        (K * (hilbertSettlingContraction mu L rate ^ warmSteps *
            Real.sqrt (2 * addressedEnergyGap model initializer resource target stored
              penalty ε / mu)) +
          K * (hilbertSettlingContraction mu L rate ^ coldSteps *
            ‖cold - target‖)) +
        referencePrecisionError
      ‖combinedGradient current replay retentionWeight‖ * error <
        retentionWeightedScore current replay retentionWeight referenceRealized -
          retentionWeightedScore current replay retentionWeight baseline) :
    retentionWeightedScore current replay retentionWeight baseline <
      retentionWeightedScore current replay retentionWeight
        (guardedCredit admitted referenceRealized candidateRealized) := by
  let error := candidatePrecisionError +
    (K * (hilbertSettlingContraction mu L rate ^ warmSteps *
        Real.sqrt (2 * addressedEnergyGap model initializer resource target stored
          penalty ε / mu)) +
      K * (hilbertSettlingContraction mu L rate ^ coldSteps *
        ‖cold - target‖)) +
    referencePrecisionError
  apply guardedCredit_retains_referenceAdvantage admitted current replay
    referenceRealized candidateRealized baseline retentionWeight
    referenceAdvantage
  intro hadmitted
  apply candidate_score_gt_baseline_of_reference_gap current replay
    referenceRealized candidateRealized baseline retentionWeight error
  · simpa [error] using realized_addressedWarm_cold_credit_difference_le model
      muPositive LNonneg rateNonneg coefficientNonneg initializer resource
      candidates returned stored penalty ε penaltyNonneg resourceNonneg optimal
      storedAvailable target cold targetStationary readout KNonneg
      readoutLipschitz warmSteps coldSteps candidateRealized referenceRealized
      candidatePrecisionError referencePrecisionError candidateReplayBound
      referenceReplayBound
  · simpa [error] using gate hadmitted

/-- Scientific and economic admission are separate obligations and can be
returned together only when both are established. -/
theorem guardedAddressedWarm_preservesAdvantage_and_savesWork
    {mu L rate K : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (muPositive : 0 < mu) (LNonneg : 0 ≤ L) (rateNonneg : 0 ≤ rate)
    (coefficientNonneg :
      0 ≤ hilbertSettlingContractionSq mu L rate)
    (initializer : Address → Latent) (resource : Address → ℝ)
    (candidates : Set Address)
    (returned stored : Address) (penalty ε : ℝ)
    (penaltyNonneg : 0 ≤ penalty)
    (resourceNonneg : ∀ address, 0 ≤ resource address)
    (optimal : EpsilonOptimalOn candidates
      (penalizedEnergy (initializerEnergy model initializer) resource penalty)
      returned ε)
    (storedAvailable : stored ∈ candidates)
    (target cold : Latent) (targetStationary : model.gradient target = 0)
    (readout : Latent → Credit) (KNonneg : 0 ≤ K)
    (readoutLipschitz : HilbertGradientReadoutLipschitzAt readout target K)
    (warmSteps coldSteps : ℕ)
    (candidateRealized referenceRealized : Credit)
    (candidatePrecisionError referencePrecisionError : ℝ)
    (candidateReplayBound :
      ‖candidateRealized - readout
        ((hilbertSettlingStep model rate)^[warmSteps]
          (initializer returned))‖ ≤ candidatePrecisionError)
    (referenceReplayBound :
      ‖referenceRealized - readout
        ((hilbertSettlingStep model rate)^[coldSteps] cold)‖ ≤
          referencePrecisionError)
    (current replay baseline : Credit) (retentionWeight : ℝ)
    (referenceAdvantage :
      retentionWeightedScore current replay retentionWeight baseline <
        retentionWeightedScore current replay retentionWeight referenceRealized)
    (gate :
      let error := candidatePrecisionError +
        (K * (hilbertSettlingContraction mu L rate ^ warmSteps *
            Real.sqrt (2 * addressedEnergyGap model initializer resource target stored
              penalty ε / mu)) +
          K * (hilbertSettlingContraction mu L rate ^ coldSteps *
            ‖cold - target‖)) +
        referencePrecisionError
      ‖combinedGradient current replay retentionWeight‖ * error <
        retentionWeightedScore current replay retentionWeight referenceRealized -
          retentionWeightedScore current replay retentionWeight baseline)
    (profile : GuardedWorkProfile)
    (netSaving : profile.guardedWork true < profile.coldWork) :
    retentionWeightedScore current replay retentionWeight baseline <
        retentionWeightedScore current replay retentionWeight candidateRealized ∧
      profile.guardedWork true < profile.coldWork := by
  constructor
  · simpa using guardedAddressedWarm_preserves_retentionAdvantage model
      muPositive LNonneg rateNonneg coefficientNonneg initializer resource
      candidates returned stored penalty ε penaltyNonneg resourceNonneg optimal
      storedAvailable target cold targetStationary readout KNonneg
      readoutLipschitz warmSteps coldSteps candidateRealized referenceRealized
      candidatePrecisionError referencePrecisionError candidateReplayBound
      referenceReplayBound current replay baseline retentionWeight true
      referenceAdvantage (by intro _; simpa using gate)
  · exact netSaving

/-- Runtime end-to-end crown using the regional finite-reference certificate.
The cold reference is finite and authenticated; candidate selection is
fail-closed and scientific advantage is independent of the work test. -/
theorem guardedLocalAddressedWarmShort_preserves_retentionAdvantage
    {mu L K : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (muPositive : 0 < mu)
    (initializer : Address → Latent) (resource : Address → ℝ)
    (candidates : Set Address)
    (returned stored : Address) (penalty ε : ℝ)
    (penaltyNonneg : 0 ≤ penalty)
    (resourceNonneg : ∀ address, 0 ≤ resource address)
    (optimal : EpsilonOptimalOn candidates
      (penalizedEnergy (initializerEnergy model initializer) resource penalty)
      returned ε)
    (storedAvailable : stored ∈ candidates)
    (target cold : Latent) (targetStationary : model.gradient target = 0)
    {solver : Latent → Latent} {center : Latent} {radius : ℝ}
    (certificate : LocalContractionCertificate solver center radius)
    (warmInBasin : InClosedBall center radius (initializer returned))
    (coldInBasin : InClosedBall center radius cold)
    (readout : Latent → Credit) (KNonneg : 0 ≤ K)
    (readoutLipschitz : CreditReadoutPairwiseLipschitz readout K)
    (warmSteps omittedSteps : ℕ)
    (candidateRealized referenceRealized : Credit)
    (candidatePrecisionError referencePrecisionError : ℝ)
    (candidateReplayBound :
      ‖candidateRealized - readout
        (solver^[warmSteps] (initializer returned))‖ ≤ candidatePrecisionError)
    (referenceReplayBound :
      ‖referenceRealized - readout
        (solver^[warmSteps + omittedSteps] cold)‖ ≤ referencePrecisionError)
    (current replay baseline : Credit) (retentionWeight : ℝ)
    (admitted : Bool)
    (referenceAdvantage :
      retentionWeightedScore current replay retentionWeight baseline <
        retentionWeightedScore current replay retentionWeight referenceRealized)
    (gate : admitted = true →
      let error := candidatePrecisionError +
        K * (certificate.factor ^ warmSteps *
          (Real.sqrt (2 * addressedEnergyGap model initializer resource target stored
              penalty ε / mu) + ‖cold - target‖ +
            geometricPrefix certificate.factor omittedSteps *
              ‖cold - solver cold‖)) +
        referencePrecisionError
      ‖combinedGradient current replay retentionWeight‖ * error <
        retentionWeightedScore current replay retentionWeight referenceRealized -
          retentionWeightedScore current replay retentionWeight baseline) :
    retentionWeightedScore current replay retentionWeight baseline <
      retentionWeightedScore current replay retentionWeight
        (guardedCredit admitted referenceRealized candidateRealized) := by
  let error := candidatePrecisionError +
    K * (certificate.factor ^ warmSteps *
      (Real.sqrt (2 * addressedEnergyGap model initializer resource target stored
          penalty ε / mu) + ‖cold - target‖ +
        geometricPrefix certificate.factor omittedSteps *
          ‖cold - solver cold‖)) +
    referencePrecisionError
  apply guardedCredit_retains_referenceAdvantage admitted current replay
    referenceRealized candidateRealized baseline retentionWeight
    referenceAdvantage
  intro hadmitted
  apply candidate_score_gt_baseline_of_reference_gap current replay
    referenceRealized candidateRealized baseline retentionWeight error
  · simpa [error] using
      local_realized_addressedWarmShort_credit_difference_to_coldLong_le model
        muPositive initializer resource candidates returned stored penalty ε
        penaltyNonneg resourceNonneg optimal storedAvailable target cold
        targetStationary certificate warmInBasin coldInBasin readout KNonneg
        readoutLipschitz warmSteps omittedSteps candidateRealized
        referenceRealized candidatePrecisionError referencePrecisionError
        candidateReplayBound referenceReplayBound
  · simpa [error] using gate hadmitted

/-- Production admission combines the regional scientific crown with exact
total-work accounting. -/
theorem guardedLocalAddressedWarmShort_preservesAdvantage_and_savesWork
    {mu L K : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (muPositive : 0 < mu)
    (initializer : Address → Latent) (resource : Address → ℝ)
    (candidates : Set Address)
    (returned stored : Address) (penalty ε : ℝ)
    (penaltyNonneg : 0 ≤ penalty)
    (resourceNonneg : ∀ address, 0 ≤ resource address)
    (optimal : EpsilonOptimalOn candidates
      (penalizedEnergy (initializerEnergy model initializer) resource penalty)
      returned ε)
    (storedAvailable : stored ∈ candidates)
    (target cold : Latent) (targetStationary : model.gradient target = 0)
    {solver : Latent → Latent} {center : Latent} {radius : ℝ}
    (certificate : LocalContractionCertificate solver center radius)
    (warmInBasin : InClosedBall center radius (initializer returned))
    (coldInBasin : InClosedBall center radius cold)
    (readout : Latent → Credit) (KNonneg : 0 ≤ K)
    (readoutLipschitz : CreditReadoutPairwiseLipschitz readout K)
    (warmSteps omittedSteps : ℕ)
    (candidateRealized referenceRealized : Credit)
    (candidatePrecisionError referencePrecisionError : ℝ)
    (candidateReplayBound :
      ‖candidateRealized - readout
        (solver^[warmSteps] (initializer returned))‖ ≤ candidatePrecisionError)
    (referenceReplayBound :
      ‖referenceRealized - readout
        (solver^[warmSteps + omittedSteps] cold)‖ ≤ referencePrecisionError)
    (current replay baseline : Credit) (retentionWeight : ℝ)
    (referenceAdvantage :
      retentionWeightedScore current replay retentionWeight baseline <
        retentionWeightedScore current replay retentionWeight referenceRealized)
    (gate :
      let error := candidatePrecisionError +
        K * (certificate.factor ^ warmSteps *
          (Real.sqrt (2 * addressedEnergyGap model initializer resource target stored
              penalty ε / mu) + ‖cold - target‖ +
            geometricPrefix certificate.factor omittedSteps *
              ‖cold - solver cold‖)) +
        referencePrecisionError
      ‖combinedGradient current replay retentionWeight‖ * error <
        retentionWeightedScore current replay retentionWeight referenceRealized -
          retentionWeightedScore current replay retentionWeight baseline)
    (profile : GuardedWorkProfile)
    (netSaving : profile.guardedWork true < profile.coldWork) :
    retentionWeightedScore current replay retentionWeight baseline <
        retentionWeightedScore current replay retentionWeight candidateRealized ∧
      profile.guardedWork true < profile.coldWork := by
  constructor
  · simpa using
      guardedLocalAddressedWarmShort_preserves_retentionAdvantage model
        muPositive initializer resource candidates returned stored penalty ε
        penaltyNonneg resourceNonneg optimal storedAvailable target cold
        targetStationary certificate warmInBasin coldInBasin readout KNonneg
        readoutLipschitz warmSteps omittedSteps candidateRealized
        referenceRealized candidatePrecisionError referencePrecisionError
        candidateReplayBound referenceReplayBound current replay baseline
        retentionWeight true referenceAdvantage (by intro _; simpa using gate)
  · exact netSaving

omit [InnerProductSpace ℝ Latent] in
/- General nonlinear runtime crown using only regional quadratic growth and
regional solver contraction. -/
theorem guardedRegionalAddressedWarmShort_preserves_retentionAdvantage
    {mu K : ℝ} (energy : Latent → ℝ) (muPositive : 0 < mu)
    (energyRegion : Set Latent) (target cold : Latent)
    (quadraticGrowth : QuadraticGrowthOn energyRegion energy target mu)
    (initializer : Address → Latent) (resource : Address → ℝ)
    (candidates : Set Address)
    (returned stored : Address) (penalty ε : ℝ)
    (penaltyNonneg : 0 ≤ penalty)
    (resourceNonneg : ∀ address, 0 ≤ resource address)
    (optimal : EpsilonOptimalOn candidates
      (penalizedEnergy (regionalInitializerEnergy energy initializer)
        resource penalty) returned ε)
    (storedAvailable : stored ∈ candidates)
    (returnedInEnergyRegion : initializer returned ∈ energyRegion)
    {solver : Latent → Latent} {center : Latent} {radius : ℝ}
    (certificate : LocalContractionCertificate solver center radius)
    (warmInBasin : InClosedBall center radius (initializer returned))
    (coldInBasin : InClosedBall center radius cold)
    (readout : Latent → Credit) (KNonneg : 0 ≤ K)
    (readoutLipschitz : CreditReadoutPairwiseLipschitz readout K)
    (warmSteps omittedSteps : ℕ)
    (candidateRealized referenceRealized : Credit)
    (candidatePrecisionError referencePrecisionError : ℝ)
    (candidateReplayBound :
      ‖candidateRealized - readout
        (solver^[warmSteps] (initializer returned))‖ ≤ candidatePrecisionError)
    (referenceReplayBound :
      ‖referenceRealized - readout
        (solver^[warmSteps + omittedSteps] cold)‖ ≤ referencePrecisionError)
    (current replay baseline : Credit) (retentionWeight : ℝ)
    (admitted : Bool)
    (referenceAdvantage :
      retentionWeightedScore current replay retentionWeight baseline <
        retentionWeightedScore current replay retentionWeight referenceRealized)
    (gate : admitted = true →
      let error := candidatePrecisionError +
        K * (certificate.factor ^ warmSteps *
          (Real.sqrt (2 * regionalAddressedEnergyGap energy initializer resource
              target stored penalty ε / mu) + ‖cold - target‖ +
            geometricPrefix certificate.factor omittedSteps *
              ‖cold - solver cold‖)) +
        referencePrecisionError
      ‖combinedGradient current replay retentionWeight‖ * error <
        retentionWeightedScore current replay retentionWeight referenceRealized -
          retentionWeightedScore current replay retentionWeight baseline) :
    retentionWeightedScore current replay retentionWeight baseline <
      retentionWeightedScore current replay retentionWeight
        (guardedCredit admitted referenceRealized candidateRealized) := by
  let error := candidatePrecisionError +
    K * (certificate.factor ^ warmSteps *
      (Real.sqrt (2 * regionalAddressedEnergyGap energy initializer resource
          target stored penalty ε / mu) + ‖cold - target‖ +
        geometricPrefix certificate.factor omittedSteps *
          ‖cold - solver cold‖)) +
    referencePrecisionError
  apply guardedCredit_retains_referenceAdvantage admitted current replay
    referenceRealized candidateRealized baseline retentionWeight
    referenceAdvantage
  intro hadmitted
  apply candidate_score_gt_baseline_of_reference_gap current replay
    referenceRealized candidateRealized baseline retentionWeight error
  · simpa [error] using
      regional_realized_addressedWarmShort_credit_difference_to_coldLong_le
        energy muPositive energyRegion target cold quadraticGrowth initializer
        resource candidates returned stored penalty ε penaltyNonneg
        resourceNonneg optimal storedAvailable returnedInEnergyRegion certificate
        warmInBasin coldInBasin readout KNonneg readoutLipschitz warmSteps
        omittedSteps candidateRealized referenceRealized candidatePrecisionError
        referencePrecisionError candidateReplayBound referenceReplayBound
  · simpa [error] using gate hadmitted

end GuardedCrown

/-! ## Soft addressed initializers -/

variable {Key : Type*}

/-- Vector-valued soft associative initializer. -/
def softInitializer [Fintype Key]
    (β : ℝ) (score : Key → ℝ) (value : Key → Latent) : Latent :=
  ∑ key, attentionWeight (fun item ↦ β * score item) key • value key

theorem softInitializer_sub_target
    [Fintype Key] [Nonempty Key] [DecidableEq Key]
    (β : ℝ) (score : Key → ℝ) (value : Key → Latent) (target : Key) :
    softInitializer β score value - value target =
      ∑ key ∈ Finset.univ.erase target,
        attentionWeight (fun item ↦ β * score item) key •
          (value key - value target) := by
  have weightsSum :
      ∑ key, attentionWeight (fun item ↦ β * score item) key = 1 :=
    sum_attentionWeight_eq_one _
  calc
    softInitializer β score value - value target =
        (∑ key, attentionWeight (fun item ↦ β * score item) key • value key) -
          (∑ key, attentionWeight (fun item ↦ β * score item) key) •
            value target := by simp [softInitializer, weightsSum]
    _ = ∑ key, attentionWeight (fun item ↦ β * score item) key •
          (value key - value target) := by
      rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro key _
      module
    _ = ∑ key ∈ Finset.univ.erase target,
        attentionWeight (fun item ↦ β * score item) key •
          (value key - value target) := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ target)]
      simp

/-- Soft routing is a licensed initializer when off-target mass and latent
diameter are both controlled. -/
theorem norm_softInitializer_sub_target_le
    [Fintype Key] [Nonempty Key] [DecidableEq Key]
    (β δ diameter : ℝ) (score : Key → ℝ) (value : Key → Latent) (target : Key)
    (diameterNonneg : 0 ≤ diameter)
    (massBound : offTargetMass β score target ≤ δ)
    (valueDiameter : ∀ key, ‖value key - value target‖ ≤ diameter) :
    ‖softInitializer β score value - value target‖ ≤ diameter * δ := by
  rw [softInitializer_sub_target]
  calc
    ‖∑ key ∈ Finset.univ.erase target,
        attentionWeight (fun item ↦ β * score item) key •
          (value key - value target)‖ ≤
        ∑ key ∈ Finset.univ.erase target,
          ‖attentionWeight (fun item ↦ β * score item) key •
            (value key - value target)‖ := norm_sum_le _ _
    _ ≤ ∑ key ∈ Finset.univ.erase target,
        attentionWeight (fun item ↦ β * score item) key * diameter := by
      apply Finset.sum_le_sum
      intro key _
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (attentionWeight_pos _ key)]
      exact mul_le_mul_of_nonneg_left (valueDiameter key)
        (attentionWeight_pos _ key).le
    _ = diameter * offTargetMass β score target := by
      unfold offTargetMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro key _
      ring
    _ ≤ diameter * δ :=
      mul_le_mul_of_nonneg_left massBound diameterNonneg

/-- Soft-to-hard initializer concentration composes with finite solver
contraction and a pairwise Lipschitz credit readout. -/
theorem softInitializer_settledCredit_difference_le
    [Fintype Key] [Nonempty Key] [DecidableEq Key]
    {solver : Latent → Latent}
    (certificate : AmortizedInitialization.ContractionCertificate solver)
    (readout : Latent → Credit) (K : ℝ) (KNonneg : 0 ≤ K)
    (readoutLipschitz : CreditReadoutPairwiseLipschitz readout K)
    (β δ diameter : ℝ) (score : Key → ℝ) (value : Key → Latent) (target : Key)
    (diameterNonneg : 0 ≤ diameter)
    (massBound : offTargetMass β score target ≤ δ)
    (valueDiameter : ∀ key, ‖value key - value target‖ ≤ diameter)
    (sweeps : ℕ) :
    ‖readout (solver^[sweeps] (softInitializer β score value)) -
        readout (solver^[sweeps] (value target))‖ ≤
      K * (certificate.factor ^ sweeps * (diameter * δ)) := by
  have transported := warmStart_credit_difference_le certificate readout K
    KNonneg readoutLipschitz (softInitializer β score value) (value target)
    sweeps
  have initializerBound := norm_softInitializer_sub_target_le β δ diameter
    score value target diameterNonneg massBound valueDiameter
  exact le_trans transported (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left initializerBound
      (pow_nonneg certificate.factor_nonneg sweeps)) KNonneg)

/-! ## Scalar executable fixtures -/

def unitAddressedEnergy : StrongSmoothLatentEnergy ℝ 1 1 where
  energy state := state ^ 2 / 2
  gradient state := state
  strongConvexFirstOrder := by
    intro x y
    simp only [one_div]
    rw [real_inner_comm]
    simp [Real.norm_eq_abs, sq_abs]
    ring_nf
    exact le_rfl
  gradientLipschitz := by
    intro x y
    simp

def unitAddressedInitializer : Bool → ℝ
  | false => 1
  | true => 2

def unitAddressedResource (_ : Bool) : ℝ := 0

def costSkewedAddressedResource : Bool → ℝ
  | false => 2
  | true => 0

theorem unitAddressed_false_is_exact_energy_minimizer :
    EpsilonOptimalOn Set.univ
      (penalizedEnergy
        (initializerEnergy unitAddressedEnergy unitAddressedInitializer)
        unitAddressedResource 0) false 0 := by
  constructor
  · simp
  · intro candidate _
    cases candidate <;>
      norm_num [penalizedEnergy, initializerEnergy, unitAddressedEnergy,
        unitAddressedInitializer, unitAddressedResource]

/-- Positive end-to-end address bound: exact retrieval of the better stored
initializer receives the sharp unit distance certificate. -/
theorem unitAddressed_initializer_distance_bound :
    ‖unitAddressedInitializer false - (0 : ℝ)‖ ≤
      Real.sqrt (2 * addressedEnergyGap unitAddressedEnergy
        unitAddressedInitializer unitAddressedResource 0 false 0 0 / 1) := by
  apply epsilonOptimal_initializer_distance_le unitAddressedEnergy
    (by norm_num) unitAddressedInitializer unitAddressedResource Set.univ
    false false 0 0
  · norm_num
  · intro address
    cases address <;> norm_num [unitAddressedResource]
  · exact unitAddressed_false_is_exact_energy_minimizer
  · simp
  · norm_num [unitAddressedEnergy]

/-- Positive full-chain fixture: exact addressing followed by two half-rate
settling sweeps gives an identity-credit error of at most one quarter. -/
theorem unitAddressed_twoSweep_credit_bound :
    ‖(id : ℝ → ℝ)
        ((hilbertSettlingStep unitAddressedEnergy (1 / 2))^[2]
          (unitAddressedInitializer false)) - (id : ℝ → ℝ) 0‖ ≤
      1 / 4 := by
  have bound := addressedSettling_credit_to_equilibrium_le
    (Address := Bool) (Credit := ℝ) (rate := (1 / 2 : ℝ)) (K := 1)
    unitAddressedEnergy (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [hilbertSettlingContractionSq])
    unitAddressedInitializer unitAddressedResource Set.univ false false 0 0
    (by norm_num)
    (by intro address; cases address <;> norm_num [unitAddressedResource])
    unitAddressed_false_is_exact_energy_minimizer (by simp) 0 (by rfl)
    id (by norm_num) (by intro state; simp [id]) 2
  convert bound using 1
  norm_num [hilbertSettlingContraction,
    hilbertSettlingContractionSq,
    addressedEnergyGap, unitAddressedEnergy, unitAddressedInitializer,
    unitAddressedResource, id]

/-- The address debit is necessary: an exact penalized router can deliberately
select a higher raw-energy initializer. -/
theorem uncharged_address_quality_not_preserved :
    initializerEnergy unitAddressedEnergy unitAddressedInitializer false <
      initializerEnergy unitAddressedEnergy unitAddressedInitializer true := by
  norm_num [initializerEnergy, unitAddressedEnergy, unitAddressedInitializer]

/-- Exact resource-charged selection can prefer the more expensive raw-energy
initializer; omitting the address debit would therefore be unsound. -/
theorem address_cost_can_select_higher_initializer_energy :
    EpsilonOptimalOn Set.univ
        (penalizedEnergy
          (initializerEnergy unitAddressedEnergy unitAddressedInitializer)
          costSkewedAddressedResource 1) true 0 ∧
      initializerEnergy unitAddressedEnergy unitAddressedInitializer false <
        initializerEnergy unitAddressedEnergy unitAddressedInitializer true := by
  constructor
  · constructor
    · simp
    · intro candidate _
      cases candidate <;>
        norm_num [penalizedEnergy, initializerEnergy, unitAddressedEnergy,
          unitAddressedInitializer, costSkewedAddressedResource]
  · exact uncharged_address_quality_not_preserved

#print axioms strongConvex_energyGap_controls_distance_sq
#print axioms strongConvex_distance_le_sqrt_two_energyGap_div
#print axioms StrongSmoothLatentEnergy.quadraticGrowthOn
#print axioms epsilonOptimal_regionalInitializer_distance_le
#print axioms epsilonOptimal_initializer_distance_le
#print axioms epsilonOptimal_initializer_to_cold_distance_le
#print axioms epsilonOptimal_regionalInitializer_to_cold_distance_le
#print axioms local_addressedWarmShort_credit_difference_to_coldLong_le
#print axioms local_realized_addressedWarmShort_credit_difference_to_coldLong_le
#print axioms regional_addressedWarmShort_credit_difference_to_coldLong_le
#print axioms regional_realized_addressedWarmShort_credit_difference_to_coldLong_le
#print axioms addressedSettling_credit_to_equilibrium_le
#print axioms addressedWarm_cold_credit_difference_le
#print axioms realized_addressedWarm_cold_credit_difference_le
#print axioms guardedAddressedWarm_preserves_retentionAdvantage
#print axioms guardedAddressedWarm_preservesAdvantage_and_savesWork
#print axioms guardedLocalAddressedWarmShort_preserves_retentionAdvantage
#print axioms guardedLocalAddressedWarmShort_preservesAdvantage_and_savesWork
#print axioms guardedRegionalAddressedWarmShort_preserves_retentionAdvantage
#print axioms norm_softInitializer_sub_target_le
#print axioms softInitializer_settledCredit_difference_le
#print axioms staleCacheFixture_not_compatible
#print axioms unitAddressed_initializer_distance_bound
#print axioms unitAddressed_twoSweep_credit_bound
#print axioms uncharged_address_quality_not_preserved
#print axioms address_cost_can_select_higher_initializer_energy

end

end RetrievalAddressedAcceleration

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
