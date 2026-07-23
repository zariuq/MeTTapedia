import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromPathCompleteStability
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Routed CAROM: continuous metastable phase channels

Finite path-complete stability does not by itself supply continuous entry,
attraction, dwell, passage, exit, activation, or halt behavior.  This module
states those obligations for one continuous phase flow and then composes a
finite adjacent phase channel.

The certificate is flow-level rather than vector-field-level.  It does not
infer an ODE, a generalized Lotka--Volterra realization, phase labels, or a
trained controller from a sampled trajectory.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Function Set

namespace RoutedCarom

universe uState uObservation

variable {State : Type uState} [NormedAddCommGroup State]
  {Observation : Type uObservation}

/-- One continuous phase with explicit entry, transverse attraction, finite
dwell, exit, activation-floor, and observation obligations. -/
structure ContinuousMetastablePhase
    (observe : State → Observation) where
  evolution : ℝ → State → State
  center : State
  entryRegion : Set State
  tubeRegion : Set State
  observationRegion : Set State
  exitRegion : Set State
  duration : ℝ
  dwellStart : ℝ
  dwellEnd : ℝ
  duration_pos : 0 < duration
  dwellStart_nonneg : 0 ≤ dwellStart
  dwell_nonempty : dwellStart < dwellEnd
  dwellEnd_le_duration : dwellEnd ≤ duration
  transverseError : State → ℝ
  transverseRate : ℝ
  initialTransverseBound : ℝ
  transverseRate_pos : 0 < transverseRate
  initialTransverseBound_nonneg : 0 ≤ initialTransverseBound
  activation : State → ℝ
  activationFloor : ℝ
  evolution_zero : ∀ state, evolution 0 state = state
  evolution_add : ∀ first second state,
    0 ≤ first → 0 ≤ second →
      evolution (first + second) state =
        evolution second (evolution first state)
  evolution_continuous : ∀ state, Continuous fun time => evolution time state
  transverseError_nonneg : ∀ state, 0 ≤ transverseError state
  entry_transverse_le : ∀ state, state ∈ entryRegion →
    transverseError state ≤ initialTransverseBound
  transverse_attraction : ∀ state, state ∈ entryRegion →
    ∀ time ∈ Set.Icc 0 duration,
      transverseError (evolution time state) ≤
        Real.exp (-transverseRate * time) * initialTransverseBound
  stays_in_tube : ∀ state, state ∈ entryRegion →
    ∀ time ∈ Set.Icc 0 duration, evolution time state ∈ tubeRegion
  dwells_in_observation_region : ∀ state, state ∈ entryRegion →
    ∀ time ∈ Set.Icc dwellStart dwellEnd,
      evolution time state ∈ observationRegion
  observation_constant : ∀ state, state ∈ observationRegion →
    observe state = observe center
  exits : ∀ state, state ∈ entryRegion →
    evolution duration state ∈ exitRegion
  activation_floor : ∀ state, state ∈ entryRegion →
    ∀ time ∈ Set.Icc 0 duration,
      activationFloor ≤ activation (evolution time state)

/-- The declared dwell interval has positive finite duration. -/
theorem ContinuousMetastablePhase.dwellDuration_pos
    (phase : ContinuousMetastablePhase (State := State) observe) :
    0 < phase.dwellEnd - phase.dwellStart := by
  linarith [phase.dwell_nonempty]

/-- The dwell-start state already carries the phase-center observation. -/
theorem ContinuousMetastablePhase.dwellStart_observation
    (phase : ContinuousMetastablePhase (State := State) observe)
    (state : State) (hstate : state ∈ phase.entryRegion) :
    observe (phase.evolution phase.dwellStart state) =
      observe phase.center := by
  apply phase.observation_constant
  apply phase.dwells_in_observation_region state hstate phase.dwellStart
  exact ⟨le_rfl, phase.dwell_nonempty.le⟩

/-- The phase endpoint reaches its declared exit region. -/
theorem ContinuousMetastablePhase.end_mem_exit
    (phase : ContinuousMetastablePhase (State := State) observe)
    (state : State) (hstate : state ∈ phase.entryRegion) :
    phase.evolution phase.duration state ∈ phase.exitRegion :=
  phase.exits state hstate

/-- The activation floor holds at dwell start as one consequence of its
stronger all-times premise. -/
theorem ContinuousMetastablePhase.dwellStart_activation_floor
    (phase : ContinuousMetastablePhase (State := State) observe)
    (state : State) (hstate : state ∈ phase.entryRegion) :
    phase.activationFloor ≤
      phase.activation (phase.evolution phase.dwellStart state) := by
  apply phase.activation_floor state hstate phase.dwellStart
  exact ⟨phase.dwellStart_nonneg,
    le_trans phase.dwell_nonempty.le phase.dwellEnd_le_duration⟩

/-- Adjacent exit regions feed the next phase's entry region. -/
def PhaseChainCompatible (observe : State → Observation) :
    List (ContinuousMetastablePhase observe) → Prop
  | [] => True
  | [_] => True
  | first :: second :: rest =>
      first.exitRegion ⊆ second.entryRegion ∧
        PhaseChainCompatible observe (second :: rest)

/-- Initial-state admission for a possibly empty channel. -/
def ChannelInitialEntry (observe : State → Observation)
    (initial : State) : List (ContinuousMetastablePhase observe) → Prop
  | [] => True
  | phase :: _ => initial ∈ phase.entryRegion

/-- Final state after executing each phase for its full declared duration. -/
def runContinuousChannel (observe : State → Observation) :
    State → List (ContinuousMetastablePhase observe) → State
  | state, [] => state
  | state, phase :: phases =>
      runContinuousChannel observe (phase.evolution phase.duration state) phases

/-- One state sampled at the start of each positive dwell interval. -/
def continuousChannelDwellStates (observe : State → Observation) :
    State → List (ContinuousMetastablePhase observe) → List State
  | _, [] => []
  | state, phase :: phases =>
      phase.evolution phase.dwellStart state ::
        continuousChannelDwellStates observe
          (phase.evolution phase.duration state) phases

/-- Declared center of every phase in channel order. -/
def continuousChannelCenters (observe : State → Observation) :
    List (ContinuousMetastablePhase observe) → List State
  | [] => []
  | phase :: phases => phase.center :: continuousChannelCenters observe phases

/-- Adjacent exit-to-entry compatibility composes the dwell observations into
the declared finite center itinerary. -/
theorem continuousChannelDwellItinerary_eq_centers
    (observe : State → Observation)
    (phases : List (ContinuousMetastablePhase observe))
    (initial : State)
    (hinitial : ChannelInitialEntry observe initial phases)
    (hcompatible : PhaseChainCompatible observe phases) :
    List.map observe (continuousChannelDwellStates observe initial phases) =
      List.map observe (continuousChannelCenters observe phases) := by
  induction phases generalizing initial with
  | nil => simp [continuousChannelDwellStates, continuousChannelCenters]
  | cons first rest ih =>
      have hfirstEntry : initial ∈ first.entryRegion := hinitial
      have hfirstObservation := first.dwellStart_observation initial hfirstEntry
      cases rest with
      | nil =>
          simpa [continuousChannelDwellStates, continuousChannelCenters]
            using congrArg (fun value => [value]) hfirstObservation
      | cons second rest =>
          rcases hcompatible with ⟨hlink, htailCompatible⟩
          have hnextEntry :
              first.evolution first.duration initial ∈ second.entryRegion :=
            hlink (first.exits initial hfirstEntry)
          have htail := ih (first.evolution first.duration initial)
            hnextEntry htailCompatible
          change
            observe (first.evolution first.dwellStart initial) ::
                List.map observe
                  (continuousChannelDwellStates observe
                    (first.evolution first.duration initial) (second :: rest)) =
              observe first.center ::
                List.map observe
                  (continuousChannelCenters observe (second :: rest))
          rw [hfirstObservation, htail]

/-- The last phase's exit region lies within the declared halt region.  The
empty channel deliberately has no last exit. -/
def LastExitWithin (observe : State → Observation) :
    List (ContinuousMetastablePhase observe) → Set State → Prop
  | [], _ => False
  | [phase], haltRegion => phase.exitRegion ⊆ haltRegion
  | _ :: second :: rest, haltRegion =>
      LastExitWithin observe (second :: rest) haltRegion

/-- A compatible nonempty channel reaches every set containing its last exit
region. -/
theorem runContinuousChannel_mem_of_lastExitWithin
    (observe : State → Observation)
    (phases : List (ContinuousMetastablePhase observe))
    (initial : State) (haltRegion : Set State)
    (hinitial : ChannelInitialEntry observe initial phases)
    (hcompatible : PhaseChainCompatible observe phases)
    (hlast : LastExitWithin observe phases haltRegion) :
    runContinuousChannel observe initial phases ∈ haltRegion := by
  induction phases generalizing initial with
  | nil => exact hlast.elim
  | cons first rest ih =>
      have hfirstEntry : initial ∈ first.entryRegion := hinitial
      cases rest with
      | nil =>
          exact hlast (first.exits initial hfirstEntry)
      | cons second rest =>
          rcases hcompatible with ⟨hlink, htailCompatible⟩
          have hnextEntry :
              first.evolution first.duration initial ∈ second.entryRegion :=
            hlink (first.exits initial hfirstEntry)
          exact ih (first.evolution first.duration initial)
            hnextEntry htailCompatible hlast

/-- A continuous halt flow fixes every state in its declared halt region for
all nonnegative future times. -/
structure ContinuousAbsorbingHalt where
  evolution : ℝ → State → State
  haltRegion : Set State
  evolution_zero : ∀ state, evolution 0 state = state
  evolution_continuous : ∀ state, Continuous fun time => evolution time state
  absorbs : ∀ state, state ∈ haltRegion →
    ∀ time, 0 ≤ time → evolution time state = state

/-- A channel whose last exit enters an absorbing halt remains exactly fixed
under the halt flow. -/
theorem continuousChannel_enters_absorbingHalt
    (observe : State → Observation)
    (phases : List (ContinuousMetastablePhase observe))
    (initial : State) (halt : ContinuousAbsorbingHalt (State := State))
    (hinitial : ChannelInitialEntry observe initial phases)
    (hcompatible : PhaseChainCompatible observe phases)
    (hlast : LastExitWithin observe phases halt.haltRegion)
    (time : ℝ) (htime : 0 ≤ time) :
    halt.evolution time (runContinuousChannel observe initial phases) =
      runContinuousChannel observe initial phases := by
  apply halt.absorbs
  · exact runContinuousChannel_mem_of_lastExitWithin observe phases initial
      halt.haltRegion hinitial hcompatible hlast
  · exact htime

/-! ## Explicit exponential two-phase channel -/

/-- Continuous contraction toward one phase center. -/
noncomputable def expContractionFlow (center : ℝ) (time : ℝ) (state : ℝ) : ℝ :=
  center + Real.exp (-time) * (state - center)

theorem expContractionFlow_zero (center state : ℝ) :
    expContractionFlow center 0 state = state := by
  simp [expContractionFlow]

theorem expContractionFlow_add (center first second state : ℝ) :
    expContractionFlow center (first + second) state =
      expContractionFlow center second
        (expContractionFlow center first state) := by
  simp only [expContractionFlow]
  rw [show -(first + second) = -second + -first by ring, Real.exp_add]
  ring

theorem expContractionFlow_continuous (center state : ℝ) :
    Continuous fun time => expContractionFlow center time state := by
  unfold expContractionFlow
  fun_prop

theorem expContractionFlow_distance (center time state : ℝ) :
    ‖expContractionFlow center time state - center‖ =
      Real.exp (-time) * ‖state - center‖ := by
  rw [show expContractionFlow center time state - center =
    Real.exp (-time) * (state - center) by simp [expContractionFlow]]
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- The elementary exponential bound used by the second dwell region. -/
theorem exp_neg_one_le_half : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    simpa using (Real.two_mul_le_exp (x := (1 : ℝ)))
  have hproduct : Real.exp (-1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos (-1), Real.exp_pos 1]

noncomputable def continuousPhaseObservation (state : ℝ) : Bool :=
  decide ((1 / 2 : ℝ) < state)

/-- First phase: a positive dwell at center one. -/
noncomputable def continuousPhaseOne :
    ContinuousMetastablePhase continuousPhaseObservation where
  evolution := expContractionFlow 1
  center := 1
  entryRegion := {1}
  tubeRegion := {1}
  observationRegion := {1}
  exitRegion := {1}
  duration := 2
  dwellStart := 1
  dwellEnd := 2
  duration_pos := by norm_num
  dwellStart_nonneg := by norm_num
  dwell_nonempty := by norm_num
  dwellEnd_le_duration := by norm_num
  transverseError := fun state => ‖state - 1‖
  transverseRate := 1
  initialTransverseBound := 0
  transverseRate_pos := by norm_num
  initialTransverseBound_nonneg := by norm_num
  activation := fun state => state
  activationFloor := 1
  evolution_zero := expContractionFlow_zero 1
  evolution_add := by
    intro first second state _ _
    exact expContractionFlow_add 1 first second state
  evolution_continuous := expContractionFlow_continuous 1
  transverseError_nonneg := fun state => norm_nonneg _
  entry_transverse_le := by
    intro state hstate
    simp only [Set.mem_singleton_iff] at hstate
    subst state
    norm_num
  transverse_attraction := by
    intro state hstate time _
    simp only [Set.mem_singleton_iff] at hstate
    subst state
    norm_num [expContractionFlow]
  stays_in_tube := by
    intro state hstate time _
    simp only [Set.mem_singleton_iff] at hstate ⊢
    subst state
    simp [expContractionFlow]
  dwells_in_observation_region := by
    intro state hstate time _
    simp only [Set.mem_singleton_iff] at hstate ⊢
    subst state
    simp [expContractionFlow]
  observation_constant := by
    intro state hstate
    simp only [Set.mem_singleton_iff] at hstate
    subst state
    rfl
  exits := by
    intro state hstate
    simp only [Set.mem_singleton_iff] at hstate ⊢
    subst state
    simp [expContractionFlow]
  activation_floor := by
    intro state hstate time _
    simp only [Set.mem_singleton_iff] at hstate
    subst state
    simp [expContractionFlow]

/-- Second phase: a genuine continuous contraction from one toward center
zero, with a positive dwell after the observation crosses below one half. -/
noncomputable def continuousPhaseZero :
    ContinuousMetastablePhase continuousPhaseObservation where
  evolution := expContractionFlow 0
  center := 0
  entryRegion := {1}
  tubeRegion := Set.Icc 0 1
  observationRegion := Set.Icc 0 (1 / 2)
  exitRegion := {Real.exp (-2)}
  duration := 2
  dwellStart := 1
  dwellEnd := 2
  duration_pos := by norm_num
  dwellStart_nonneg := by norm_num
  dwell_nonempty := by norm_num
  dwellEnd_le_duration := by norm_num
  transverseError := fun state => ‖state‖
  transverseRate := 1
  initialTransverseBound := 1
  transverseRate_pos := by norm_num
  initialTransverseBound_nonneg := by norm_num
  activation := fun state => state
  activationFloor := 0
  evolution_zero := expContractionFlow_zero 0
  evolution_add := by
    intro first second state _ _
    exact expContractionFlow_add 0 first second state
  evolution_continuous := expContractionFlow_continuous 0
  transverseError_nonneg := fun state => norm_nonneg _
  entry_transverse_le := by
    intro state hstate
    simp only [Set.mem_singleton_iff] at hstate
    subst state
    norm_num
  transverse_attraction := by
    intro state hstate time _
    simp only [Set.mem_singleton_iff] at hstate
    subst state
    have hdistance := expContractionFlow_distance 0 time 1
    simp only [sub_zero, norm_one, mul_one] at hdistance
    rw [hdistance]
    simp
  stays_in_tube := by
    intro state hstate time htime
    simp only [Set.mem_singleton_iff] at hstate
    subst state
    simp only [Set.mem_Icc, expContractionFlow, zero_add, sub_zero, mul_one]
    constructor
    · exact (Real.exp_pos _).le
    · rw [Real.exp_le_one_iff]
      linarith [htime.1]
  dwells_in_observation_region := by
    intro state hstate time htime
    simp only [Set.mem_singleton_iff] at hstate
    subst state
    simp only [Set.mem_Icc, expContractionFlow, zero_add, sub_zero, mul_one]
    constructor
    · exact (Real.exp_pos _).le
    · exact le_trans (Real.exp_le_exp.mpr (by linarith [htime.1]))
        exp_neg_one_le_half
  observation_constant := by
    intro state hstate
    have hnot : ¬ (1 / 2 : ℝ) < state := not_lt_of_ge hstate.2
    unfold continuousPhaseObservation
    rw [decide_eq_decide]
    constructor
    · intro hleft
      exact (hnot hleft).elim
    · intro hright
      norm_num at hright
  exits := by
    intro state hstate
    simp only [Set.mem_singleton_iff] at hstate ⊢
    subst state
    simp [expContractionFlow]
  activation_floor := by
    intro state hstate time _
    simp only [Set.mem_singleton_iff] at hstate
    subst state
    simp only [expContractionFlow, zero_add, sub_zero, mul_one]
    exact (Real.exp_pos _).le

noncomputable def continuousTwoPhaseChannel :
    List (ContinuousMetastablePhase continuousPhaseObservation) :=
  [continuousPhaseOne, continuousPhaseZero]

theorem continuousTwoPhaseChannel_compatible :
    PhaseChainCompatible continuousPhaseObservation continuousTwoPhaseChannel := by
  simp [continuousTwoPhaseChannel, PhaseChainCompatible,
    continuousPhaseOne, continuousPhaseZero]

theorem continuousTwoPhaseChannel_initial :
    ChannelInitialEntry continuousPhaseObservation 1 continuousTwoPhaseChannel := by
  simp [continuousTwoPhaseChannel, ChannelInitialEntry, continuousPhaseOne]

/-- The continuous channel theorem, not a direct evaluation shortcut, yields
the ordered dwell observations. -/
theorem continuousTwoPhaseChannel_dwellItinerary :
    List.map continuousPhaseObservation
        (continuousChannelDwellStates continuousPhaseObservation 1
          continuousTwoPhaseChannel) =
      List.map continuousPhaseObservation
        (continuousChannelCenters continuousPhaseObservation
          continuousTwoPhaseChannel) := by
  exact continuousChannelDwellItinerary_eq_centers continuousPhaseObservation
    continuousTwoPhaseChannel 1 continuousTwoPhaseChannel_initial
    continuousTwoPhaseChannel_compatible

theorem continuousTwoPhaseChannel_dwellItinerary_value :
    List.map continuousPhaseObservation
        (continuousChannelDwellStates continuousPhaseObservation 1
          continuousTwoPhaseChannel) = [true, false] := by
  rw [continuousTwoPhaseChannel_dwellItinerary]
  norm_num [continuousChannelCenters, continuousTwoPhaseChannel,
    continuousPhaseOne, continuousPhaseZero, continuousPhaseObservation]

/-- Identity evolution on the final singleton is an explicit absorbing halt. -/
noncomputable def continuousTwoPhaseHalt : ContinuousAbsorbingHalt (State := ℝ) where
  evolution := fun _time state => state
  haltRegion := {Real.exp (-2)}
  evolution_zero := fun _ => rfl
  evolution_continuous := by intro; fun_prop
  absorbs := by
    intro state _ time _
    rfl

theorem continuousTwoPhaseChannel_lastExit :
    LastExitWithin continuousPhaseObservation continuousTwoPhaseChannel
      continuousTwoPhaseHalt.haltRegion := by
  simp [continuousTwoPhaseChannel, LastExitWithin, continuousPhaseZero,
    continuousTwoPhaseHalt]

theorem continuousTwoPhaseChannel_absorbingHalt
    (time : ℝ) (htime : 0 ≤ time) :
    continuousTwoPhaseHalt.evolution time
        (runContinuousChannel continuousPhaseObservation 1
          continuousTwoPhaseChannel) =
      runContinuousChannel continuousPhaseObservation 1
        continuousTwoPhaseChannel := by
  exact continuousChannel_enters_absorbingHalt continuousPhaseObservation
    continuousTwoPhaseChannel 1 continuousTwoPhaseHalt
    continuousTwoPhaseChannel_initial continuousTwoPhaseChannel_compatible
    continuousTwoPhaseChannel_lastExit time htime

/-! ## Negative boundaries -/

/-- A zero-length dwell interval is incompatible with the phase certificate. -/
theorem ContinuousMetastablePhase.no_zero_dwell
    (phase : ContinuousMetastablePhase (State := State) observe) :
    phase.dwellStart ≠ phase.dwellEnd := by
  exact ne_of_lt phase.dwell_nonempty

/-- Reversing the two valid phases breaks exit-to-entry compatibility: the
second phase exits strictly below one, whereas the first phase only accepts one. -/
theorem reversedContinuousPhases_not_compatible :
    ¬ PhaseChainCompatible continuousPhaseObservation
      [continuousPhaseZero, continuousPhaseOne] := by
  intro hcompatible
  simp only [PhaseChainCompatible, and_true] at hcompatible
  have hmember : Real.exp (-2) ∈ continuousPhaseZero.exitRegion := by
    simp [continuousPhaseZero]
  have hone : Real.exp (-2) = 1 := by
    simpa [continuousPhaseOne] using hcompatible hmember
  have hlt : Real.exp (-2) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  linarith

#print axioms ContinuousMetastablePhase.dwellDuration_pos
#print axioms ContinuousMetastablePhase.dwellStart_observation
#print axioms continuousChannelDwellItinerary_eq_centers
#print axioms runContinuousChannel_mem_of_lastExitWithin
#print axioms continuousChannel_enters_absorbingHalt
#print axioms continuousTwoPhaseChannel_dwellItinerary_value
#print axioms continuousTwoPhaseChannel_absorbingHalt
#print axioms ContinuousMetastablePhase.no_zero_dwell
#print axioms reversedContinuousPhases_not_compatible

end RoutedCarom

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
