import Mathlib.Data.Multiset.Count
import Mettapedia.GSLT.LanguageDef.RefinementInterface
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.ObservationalEquivalence

/-!
# Checker-mediated carrier behavior

Finite carrier trajectories become synthesis evidence only after an external
checker accepts the policy trace as a program.  This module makes that boundary
explicit.  Search schedules retain multiplicity, so repeated occurrences are
counted without being mistaken for distinct or independent evidence.

The accepted-program mass is an unnormalized finite distribution.  Because a
paired comparison uses the same schedule multiset, equality of every mass is
equivalent to equality after normalization whenever the common total mass is
nonzero.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

open StateCarrier

universe uEnvironment uSlow uCommand uPolicy uProgram uGenerationState
  uLeftState uLeftRead uLeftRoute uLeftProposal uLeftObservation
  uRightState uRightRead uRightRoute uRightProposal uRightObservation

/-- A bounded multiset of command schedules together with a checker-owned
acceptance relation on the resulting policy trace.  The carrier cannot alter
the relation: it supplies only the trace being checked. -/
structure CheckerMediatedSearch
    (Command : Type uCommand) (Policy : Type uPolicy) (Program : Type uProgram) where
  schedules : Multiset (List Command)
  accepts : List Policy → Program → Prop

namespace CheckerMediatedSearch

/-- Use a concrete GSLT refinement root as the checker.  `actionsOfPolicies`
is the typed waist from carrier policies to the root's action trace; terminal
execution and decoding remain exactly `RefinementInterface.Accepts`. -/
def ofRefinementInterface
    {Command : Type uCommand} {Policy : Type uPolicy}
    (root : Mettapedia.GSLT.LanguageDef.RefinementInterface.RefinementInterface)
    (budget : Nat) (schedules : Multiset (List Command))
    (actionsOfPolicies : List Policy → List root.Action) :
    CheckerMediatedSearch Command Policy root.Program where
  schedules := schedules
  accepts := fun policies program ↦
    root.Accepts budget (actionsOfPolicies policies) program

end CheckerMediatedSearch

section AcceptedMass

variable
  {Environment : Type uEnvironment} {Slow : Type uSlow}
  {Command : Type uCommand} {Policy : Type uPolicy} {Program : Type uProgram}
  {LeftState : Type uLeftState} {LeftRead : Type uLeftRead}
  {LeftRoute : Type uLeftRoute} {LeftProposal : Type uLeftProposal}
  {LeftObservation : Type uLeftObservation}
  {RightState : Type uRightState} {RightRead : Type uRightRead}
  {RightRoute : Type uRightRoute} {RightProposal : Type uRightProposal}
  {RightObservation : Type uRightObservation}

/-- Number of scheduled occurrences whose complete policy trace is accepted as
the declared program.  This is deliberately a multiplicity, not an assertion
that repeated occurrences are independent evidence. -/
noncomputable def acceptedProgramMass
    (search : CheckerMediatedSearch Command Policy Program)
    (carrier : StateCarrier Environment Slow Command LeftState LeftRead LeftRoute
      LeftProposal LeftObservation Policy)
    (environment : Environment) (slow : Slow) (program : Program) : Nat := by
  classical
  exact search.schedules.countP (fun commands ↦
    search.accepts
      (carrier.policyTrajectoryFromInitial environment slow commands) program)

/-- A paired search has the same accepted-program distribution when every
program has the same exact finite mass under the common schedule multiset. -/
def AcceptedProgramDistributionEquivalent
    (search : CheckerMediatedSearch Command Policy Program)
    (left : StateCarrier Environment Slow Command LeftState LeftRead LeftRoute
      LeftProposal LeftObservation Policy)
    (right : StateCarrier Environment Slow Command RightState RightRead RightRoute
      RightProposal RightObservation Policy) : Prop :=
  ∀ environment slow program,
    acceptedProgramMass search left environment slow program =
      acceptedProgramMass search right environment slow program

/-- Pointwise equality of the policy traces examined by one bounded search is
enough for equality of all checker-accepted program masses. -/
theorem acceptedProgramMass_eq_of_policyTrajectories_eq
    (search : CheckerMediatedSearch Command Policy Program)
    (left : StateCarrier Environment Slow Command LeftState LeftRead LeftRoute
      LeftProposal LeftObservation Policy)
    (right : StateCarrier Environment Slow Command RightState RightRead RightRoute
      RightProposal RightObservation Policy)
    (environment : Environment) (slow : Slow) (program : Program)
    (trajectoriesEqual : ∀ commands ∈ search.schedules,
      left.policyTrajectoryFromInitial environment slow commands =
        right.policyTrajectoryFromInitial environment slow commands) :
    acceptedProgramMass search left environment slow program =
      acceptedProgramMass search right environment slow program := by
  classical
  unfold acceptedProgramMass
  apply Multiset.countP_congr rfl
  intro commands commandsMem
  rw [trajectoriesEqual commands commandsMem]

/-- Finite policy-trajectory equivalence survives the external checker and
therefore implies exact accepted-program distribution equivalence. -/
theorem FinitePolicyTrajectoryEquivalent.acceptedProgramDistributionEquivalent
    {left : StateCarrier Environment Slow Command LeftState LeftRead LeftRoute
      LeftProposal LeftObservation Policy}
    {right : StateCarrier Environment Slow Command RightState RightRead RightRoute
      RightProposal RightObservation Policy}
    (equivalent : FinitePolicyTrajectoryEquivalent left right)
    (search : CheckerMediatedSearch Command Policy Program) :
    AcceptedProgramDistributionEquivalent search left right := by
  intro environment slow program
  exact acceptedProgramMass_eq_of_policyTrajectories_eq search left right
    environment slow program (fun commands _commandsMem ↦
      equivalent environment slow commands)

end AcceptedMass

/-! ## A strict checker boundary -/

/-- A nontrivial checker that accepts only policy traces ending in program
`1`.  Its two schedules preserve raw search multiplicity. -/
def acceptsOnlyOneSearch : CheckerMediatedSearch Unit Nat Nat where
  schedules := ([ [()], [(), ()] ] : List (List Unit))
  accepts := fun policies program ↦
    policies.getLast? = some program ∧ program = 1

/-- The successor and delayed-jump carriers have the same nonzero accepted
mass even though their rejected second-step policies differ. -/
theorem successor_delayedJump_acceptedProgramDistributionEquivalent :
    AcceptedProgramDistributionEquivalent acceptsOnlyOneSearch
      successorCarrier delayedJumpCarrier := by
  intro environment slow program
  rcases environment with ⟨⟩
  rcases slow with ⟨⟩
  by_cases hprogram : program = 1
  · subst program
    simp [acceptedProgramMass, acceptsOnlyOneSearch, successorCarrier,
      delayedJumpCarrier, replacementCarrier, StateCarrier.policyTrajectoryFromInitial,
      StateCarrier.policyTrajectory, StateCarrier.trajectory,
      StateCarrier.policyAtState, StateCarrier.observeAtState, StateCarrier.step]
  · simp [acceptedProgramMass, acceptsOnlyOneSearch, hprogram]

/-- The checker-level converse is invalid: equal accepted distributions need
not expose policy differences that occur only on rejected traces. -/
theorem acceptedProgramDistribution_does_not_imply_finitePolicyTrajectory :
    AcceptedProgramDistributionEquivalent acceptsOnlyOneSearch
        successorCarrier delayedJumpCarrier ∧
      ¬ FinitePolicyTrajectoryEquivalent successorCarrier delayedJumpCarrier :=
  ⟨successor_delayedJump_acceptedProgramDistributionEquivalent,
    successor_delayedJump_not_finite⟩

/-! ## Longitudinal discovery feedback -/

/-- A longitudinal search resolves a carrier's immutable slow input from the
current generation state, runs a bounded checker-mediated search, then advances
the generation state from the complete accepted-mass profile. -/
structure LongitudinalSearchKernel
    (CarrierSlow : Type uSlow) (Command : Type uCommand) (Policy : Type uPolicy)
    (Program : Type uProgram) (GenerationState : Type uGenerationState) where
  carrierSlow : GenerationState → CarrierSlow
  searchAt : GenerationState → CheckerMediatedSearch Command Policy Program
  advance : GenerationState → (Program → Nat) → GenerationState

section Longitudinal

variable
  {Environment : Type uEnvironment} {CarrierSlow : Type uSlow}
  {Command : Type uCommand} {Policy : Type uPolicy} {Program : Type uProgram}
  {GenerationState : Type uGenerationState}
  {LeftState : Type uLeftState} {LeftRead : Type uLeftRead}
  {LeftRoute : Type uLeftRoute} {LeftProposal : Type uLeftProposal}
  {LeftObservation : Type uLeftObservation}
  {RightState : Type uRightState} {RightRead : Type uRightRead}
  {RightRoute : Type uRightRoute} {RightProposal : Type uRightProposal}
  {RightObservation : Type uRightObservation}

/-- The full accepted-program multiplicity profile observed at one generation
state. -/
noncomputable def acceptedProgramProfile
    (kernel : LongitudinalSearchKernel CarrierSlow Command Policy Program
      GenerationState)
    (carrier : StateCarrier Environment CarrierSlow Command LeftState LeftRead
      LeftRoute LeftProposal LeftObservation Policy)
    (environment : Environment) (generationState : GenerationState) : Program → Nat :=
  fun program ↦ acceptedProgramMass (kernel.searchAt generationState) carrier
    environment (kernel.carrierSlow generationState) program

/-- One checker-mediated feedback transition. -/
noncomputable def nextGenerationState
    (kernel : LongitudinalSearchKernel CarrierSlow Command Policy Program
      GenerationState)
    (carrier : StateCarrier Environment CarrierSlow Command LeftState LeftRead
      LeftRoute LeftProposal LeftObservation Policy)
    (environment : Environment) (generationState : GenerationState) : GenerationState :=
  kernel.advance generationState
    (acceptedProgramProfile kernel carrier environment generationState)

/-- Generation state before feedback and after every subsequent bounded search. -/
noncomputable def longitudinalDiscoveryTrajectory
    (kernel : LongitudinalSearchKernel CarrierSlow Command Policy Program
      GenerationState)
    (carrier : StateCarrier Environment CarrierSlow Command LeftState LeftRead
      LeftRoute LeftProposal LeftObservation Policy)
    (environment : Environment) : GenerationState → Nat → List GenerationState
  | generationState, 0 => [generationState]
  | generationState, generations + 1 =>
      generationState :: longitudinalDiscoveryTrajectory kernel carrier environment
        (nextGenerationState kernel carrier environment generationState) generations

/-- Two carriers induce the same longitudinal discovery process when every
finite generation-state trajectory agrees under one common feedback kernel. -/
def LongitudinalDiscoveryProcessEquivalent
    (kernel : LongitudinalSearchKernel CarrierSlow Command Policy Program
      GenerationState)
    (left : StateCarrier Environment CarrierSlow Command LeftState LeftRead
      LeftRoute LeftProposal LeftObservation Policy)
    (right : StateCarrier Environment CarrierSlow Command RightState RightRead
      RightRoute RightProposal RightObservation Policy) : Prop :=
  ∀ environment initialState generations,
    longitudinalDiscoveryTrajectory kernel left environment initialState generations =
      longitudinalDiscoveryTrajectory kernel right environment initialState generations

/-- Equality of the accepted distributions at the slow input actually resolved
from each generation state.  This is the exact information consumed by the
longitudinal feedback transition. -/
def ResolvedAcceptedProgramDistributionsEquivalent
    (kernel : LongitudinalSearchKernel CarrierSlow Command Policy Program
      GenerationState)
    (left : StateCarrier Environment CarrierSlow Command LeftState LeftRead
      LeftRoute LeftProposal LeftObservation Policy)
    (right : StateCarrier Environment CarrierSlow Command RightState RightRead
      RightRoute RightProposal RightObservation Policy) : Prop :=
  ∀ environment generationState program,
    acceptedProgramMass (kernel.searchAt generationState) left environment
        (kernel.carrierSlow generationState) program =
      acceptedProgramMass (kernel.searchAt generationState) right environment
        (kernel.carrierSlow generationState) program

/-- A feedback update is profile-separating when equal successor states force
equality of the complete accepted-program profiles supplied to it. -/
def AcceptedProfileSeparating
    (kernel : LongitudinalSearchKernel CarrierSlow Command Policy Program
      GenerationState) : Prop :=
  ∀ generationState first second,
    kernel.advance generationState first = kernel.advance generationState second →
      first = second

/-- If the paired accepted-program distribution agrees at every reachable
generation state, deterministic feedback preserves the entire longitudinal
discovery process. -/
theorem acceptedProgramDistributionEquivalent_implies_longitudinal
    (kernel : LongitudinalSearchKernel CarrierSlow Command Policy Program
      GenerationState)
    (left : StateCarrier Environment CarrierSlow Command LeftState LeftRead
      LeftRoute LeftProposal LeftObservation Policy)
    (right : StateCarrier Environment CarrierSlow Command RightState RightRead
      RightRoute RightProposal RightObservation Policy)
    (distributionsEqual :
      ResolvedAcceptedProgramDistributionsEquivalent kernel left right) :
    LongitudinalDiscoveryProcessEquivalent kernel left right := by
  classical
  intro environment initialState generations
  induction generations generalizing initialState with
  | zero => rfl
  | succ generations inductionHypothesis =>
      simp only [longitudinalDiscoveryTrajectory]
      have profilesEqual :
          acceptedProgramProfile kernel left environment initialState =
            acceptedProgramProfile kernel right environment initialState := by
        funext program
        exact distributionsEqual environment initialState program
      have nextStatesEqual :
          nextGenerationState kernel left environment initialState =
            nextGenerationState kernel right environment initialState := by
        unfold nextGenerationState
        rw [profilesEqual]
      rw [nextStatesEqual]
      exact congrArg (List.cons initialState)
        (inductionHypothesis
          (nextGenerationState kernel right environment initialState))

/-- Finite carrier equivalence is strong enough to survive both the checker and
arbitrarily many deterministic discovery-feedback generations. -/
theorem FinitePolicyTrajectoryEquivalent.longitudinalDiscoveryProcessEquivalent
    {left : StateCarrier Environment CarrierSlow Command LeftState LeftRead
      LeftRoute LeftProposal LeftObservation Policy}
    {right : StateCarrier Environment CarrierSlow Command RightState RightRead
      RightRoute RightProposal RightObservation Policy}
    (equivalent : FinitePolicyTrajectoryEquivalent left right)
    (kernel : LongitudinalSearchKernel CarrierSlow Command Policy Program
      GenerationState) :
    LongitudinalDiscoveryProcessEquivalent kernel left right :=
  acceptedProgramDistributionEquivalent_implies_longitudinal kernel left right
    (fun environment generationState program ↦
      equivalent.acceptedProgramDistributionEquivalent (kernel.searchAt generationState)
        environment (kernel.carrierSlow generationState) program)

/-- When feedback is profile-separating, equality of the longitudinal process
recovers exactly the accepted distributions observed at each resolved state. -/
theorem LongitudinalDiscoveryProcessEquivalent.resolvedDistributionsEquivalent
    (kernel : LongitudinalSearchKernel CarrierSlow Command Policy Program
      GenerationState)
    (left : StateCarrier Environment CarrierSlow Command LeftState LeftRead
      LeftRoute LeftProposal LeftObservation Policy)
    (right : StateCarrier Environment CarrierSlow Command RightState RightRead
      RightRoute RightProposal RightObservation Policy)
    (longitudinal : LongitudinalDiscoveryProcessEquivalent kernel left right)
    (separating : AcceptedProfileSeparating kernel) :
    ResolvedAcceptedProgramDistributionsEquivalent kernel left right := by
  classical
  intro environment generationState program
  have trajectoryEqual := longitudinal environment generationState 1
  change generationState ::
      [nextGenerationState kernel left environment generationState] =
    generationState ::
      [nextGenerationState kernel right environment generationState] at trajectoryEqual
  have nextStatesEqual :
      nextGenerationState kernel left environment generationState =
        nextGenerationState kernel right environment generationState :=
    (List.cons.inj (List.cons.inj trajectoryEqual).2).1
  have profilesEqual :
      acceptedProgramProfile kernel left environment generationState =
        acceptedProgramProfile kernel right environment generationState := by
    apply separating generationState
    exact nextStatesEqual
  exact congrFun profilesEqual program

end Longitudinal

/-! ## Strictness of the longitudinal boundary -/

/-- A search that accepts the exact terminal policy after two commands. -/
def terminalPolicySearch : CheckerMediatedSearch Unit Nat Nat where
  schedules := ([ [(), ()] ] : List (List Unit))
  accepts := fun policies program ↦ policies.getLast? = some program

/-- A nonconstant feedback process that advances the generation counter but
deliberately discards its accepted-program profile. -/
def profileForgettingIncrementKernel :
    LongitudinalSearchKernel Unit Unit Nat Nat Nat where
  carrierSlow := fun _generation ↦ ()
  searchAt := fun _generation ↦ terminalPolicySearch
  advance := fun generation _profile ↦ generation + 1

/-- The forgetful process has identical, nonconstant generation trajectories
for the two carriers. -/
theorem profileForgetting_longitudinalEquivalent :
    LongitudinalDiscoveryProcessEquivalent profileForgettingIncrementKernel
      successorCarrier delayedJumpCarrier := by
  intro environment initialState generations
  induction generations generalizing initialState with
  | zero => rfl
  | succ generations inductionHypothesis =>
      simp only [longitudinalDiscoveryTrajectory]
      have nextLeft :
          nextGenerationState profileForgettingIncrementKernel successorCarrier
              environment initialState = initialState + 1 := rfl
      have nextRight :
          nextGenerationState profileForgettingIncrementKernel delayedJumpCarrier
              environment initialState = initialState + 1 := rfl
      rw [nextLeft, nextRight]
      exact congrArg (List.cons initialState)
        (inductionHypothesis (initialState + 1))

/-- Nevertheless, the bounded accepted distributions differ: program `2` is
accepted from the successor carrier and not from the delayed-jump carrier. -/
theorem terminalPolicySearch_not_distributionEquivalent :
    ¬ AcceptedProgramDistributionEquivalent terminalPolicySearch
      successorCarrier delayedJumpCarrier := by
  intro equivalent
  have programTwo := equivalent () () 2
  have successorMass :
      acceptedProgramMass terminalPolicySearch successorCarrier () () 2 = 1 := by
    classical
    unfold acceptedProgramMass
    change Multiset.countP _
      (([ [(), ()] ] : List (List Unit)) : Multiset (List Unit)) = 1
    rw [Multiset.coe_countP, List.countP_cons_of_pos]
    · rfl
    rw [decide_eq_true_eq]
    rfl
  have delayedMass :
      acceptedProgramMass terminalPolicySearch delayedJumpCarrier () () 2 = 0 := by
    classical
    unfold acceptedProgramMass
    change Multiset.countP _
      (([ [(), ()] ] : List (List Unit)) : Multiset (List Unit)) = 0
    rw [Multiset.coe_countP, List.countP_cons_of_neg]
    · rfl
    rw [decide_eq_true_eq]
    simp [terminalPolicySearch, delayedJumpCarrier, replacementCarrier,
      StateCarrier.policyTrajectoryFromInitial, StateCarrier.policyTrajectory,
      StateCarrier.policyAtState, StateCarrier.observeAtState, StateCarrier.step]
  rw [successorMass, delayedMass] at programTwo
  omega

/-- The actual distributions resolved by the profile-forgetting kernel differ
at generation zero. -/
theorem profileForgetting_not_resolvedDistributionsEquivalent :
    ¬ ResolvedAcceptedProgramDistributionsEquivalent
      profileForgettingIncrementKernel successorCarrier delayedJumpCarrier := by
  intro equivalent
  exact terminalPolicySearch_not_distributionEquivalent
    (fun environment slow program ↦ by
      simpa [profileForgettingIncrementKernel] using
        equivalent environment 0 program)

/-- Equal longitudinal state trajectories do not recover discarded discovery
profiles.  A faithful feedback map therefore needs an explicit separation or
injectivity condition before the converse is licensed. -/
theorem longitudinalDiscovery_does_not_imply_acceptedProgramDistribution :
    LongitudinalDiscoveryProcessEquivalent profileForgettingIncrementKernel
        successorCarrier delayedJumpCarrier ∧
      ¬ ResolvedAcceptedProgramDistributionsEquivalent
        profileForgettingIncrementKernel successorCarrier delayedJumpCarrier :=
  ⟨profileForgetting_longitudinalEquivalent,
    profileForgetting_not_resolvedDistributionsEquivalent⟩

#print axioms acceptedProgramMass_eq_of_policyTrajectories_eq
#print axioms FinitePolicyTrajectoryEquivalent.acceptedProgramDistributionEquivalent
#print axioms acceptedProgramDistribution_does_not_imply_finitePolicyTrajectory
#print axioms acceptedProgramDistributionEquivalent_implies_longitudinal
#print axioms FinitePolicyTrajectoryEquivalent.longitudinalDiscoveryProcessEquivalent
#print axioms LongitudinalDiscoveryProcessEquivalent.resolvedDistributionsEquivalent
#print axioms longitudinalDiscovery_does_not_imply_acceptedProgramDistribution

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
