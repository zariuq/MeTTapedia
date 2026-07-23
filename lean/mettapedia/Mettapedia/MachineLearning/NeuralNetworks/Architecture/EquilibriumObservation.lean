import Mathlib.Data.List.Basic
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.AcceptedBehavior
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.ExecutionSemantics

/-!
# Observable equilibrium of state carriers

Hidden states cannot be equated across recurrent, workspace, belief, and routed
operator carriers.  The common equilibrium observation is instead eventual
constancy of the policy under repeated execution of one declared command.

An actual command-relative fixed point implies this observation after it is
reached.  The converse is intentionally absent: a hidden cycle may have a
constant policy.  The fixtures also separate observable equilibrium from
finite transients and checker-accepted search behavior.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

open StateCarrier

universe uEnvironment uSlow uCommand uPolicy uProgram
  uLeftState uLeftRead uLeftRoute uLeftProposal uLeftObservation
  uRightState uRightRead uRightRoute uRightProposal uRightObservation

section TerminalPolicy

variable
  {Environment : Type uEnvironment} {Slow : Type uSlow}
  {Command : Type uCommand} {Policy : Type uPolicy}
  {State : Type uLeftState} {Read : Type uLeftRead}
  {Route : Type uLeftRoute} {Proposal : Type uLeftProposal}
  {Observation : Type uLeftObservation}

/-- The final state of a nonempty carrier trajectory is the state produced by
running the same command schedule. -/
theorem StateCarrier.trajectory_getLast?_eq_run
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (state : State) :
    ∀ commands,
      (carrier.trajectory environment slow state commands).getLast? =
        some (carrier.run environment slow state commands)
  | [] => rfl
  | command :: commands => by
      simp only [StateCarrier.trajectory_cons, StateCarrier.run_cons,
        List.getLast?_cons]
      rw [carrier.trajectory_getLast?_eq_run environment slow
        (carrier.step environment slow command state) commands]
      rfl

/-- Reading policies along a carrier trajectory and then taking the final
policy agrees with reading the policy from the terminal run state. -/
theorem StateCarrier.policyTrajectory_getLast?_eq_run
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (state : State)
    (commands : List Command) :
    (carrier.policyTrajectory environment slow state commands).getLast? =
      some (carrier.policyAtState environment slow
        (carrier.run environment slow state commands)) := by
  unfold StateCarrier.policyTrajectory
  rw [List.getLast?_map, carrier.trajectory_getLast?_eq_run]
  rfl

/-- Policy exposed after a declared number of repetitions of one command. -/
def repeatedPolicyAt
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (command : Command)
    (repetitions : Nat) : Policy :=
  carrier.policyAtState environment slow
    (carrier.runFromInitial environment slow
      (List.replicate repetitions command))

/-- The final policy in the explicit trajectory is `repeatedPolicyAt`. -/
theorem policyTrajectoryFromInitial_getLast?_eq_repeatedPolicyAt
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (command : Command)
    (repetitions : Nat) :
    (carrier.policyTrajectoryFromInitial environment slow
      (List.replicate repetitions command)).getLast? =
      some (repeatedPolicyAt carrier environment slow command repetitions) := by
  exact carrier.policyTrajectory_getLast?_eq_run environment slow
    (carrier.initialState environment slow) (List.replicate repetitions command)

end TerminalPolicy

section ObservableEquilibrium

variable
  {Environment : Type uEnvironment} {Slow : Type uSlow}
  {Command : Type uCommand} {Policy : Type uPolicy}
  {LeftState : Type uLeftState} {LeftRead : Type uLeftRead}
  {LeftRoute : Type uLeftRoute} {LeftProposal : Type uLeftProposal}
  {LeftObservation : Type uLeftObservation}
  {RightState : Type uRightState} {RightRead : Type uRightRead}
  {RightRoute : Type uRightRoute} {RightProposal : Type uRightProposal}
  {RightObservation : Type uRightObservation}

/-- A policy is observably equilibrated when it remains constant after a finite
burn-in under repeated execution of one command. -/
def EventuallyObservesPolicy
    (carrier : StateCarrier Environment Slow Command LeftState LeftRead LeftRoute
      LeftProposal LeftObservation Policy)
    (environment : Environment) (slow : Slow) (command : Command)
    (policy : Policy) : Prop :=
  ∃ burnIn, ∀ extra,
    repeatedPolicyAt carrier environment slow command (burnIn + extra) = policy

/-- Cross-representation equilibrium equivalence compares exactly the set of
eventually constant policies under each immutable context and command. -/
def EquilibriumPolicyEquivalent
    (left : StateCarrier Environment Slow Command LeftState LeftRead LeftRoute
      LeftProposal LeftObservation Policy)
    (right : StateCarrier Environment Slow Command RightState RightRead RightRoute
      RightProposal RightObservation Policy) : Prop :=
  ∀ environment slow command policy,
    EventuallyObservesPolicy left environment slow command policy ↔
      EventuallyObservesPolicy right environment slow command policy

/-- Finite policy-trajectory equivalence gives equality of every repeated
terminal policy. -/
theorem FinitePolicyTrajectoryEquivalent.repeatedPolicyAt_eq
    {left : StateCarrier Environment Slow Command LeftState LeftRead LeftRoute
      LeftProposal LeftObservation Policy}
    {right : StateCarrier Environment Slow Command RightState RightRead RightRoute
      RightProposal RightObservation Policy}
    (equivalent : FinitePolicyTrajectoryEquivalent left right)
    (environment : Environment) (slow : Slow) (command : Command)
    (repetitions : Nat) :
    repeatedPolicyAt left environment slow command repetitions =
      repeatedPolicyAt right environment slow command repetitions := by
  have trajectoriesEqual := equivalent environment slow
    (List.replicate repetitions command)
  have terminalPoliciesEqual := congrArg List.getLast? trajectoriesEqual
  simpa only [policyTrajectoryFromInitial_getLast?_eq_repeatedPolicyAt,
    Option.some.injEq] using terminalPoliciesEqual

/-- Equality of all finite policy trajectories therefore preserves observable
equilibrium policies. -/
theorem FinitePolicyTrajectoryEquivalent.equilibriumPolicyEquivalent
    {left : StateCarrier Environment Slow Command LeftState LeftRead LeftRoute
      LeftProposal LeftObservation Policy}
    {right : StateCarrier Environment Slow Command RightState RightRead RightRoute
      RightProposal RightObservation Policy}
    (equivalent : FinitePolicyTrajectoryEquivalent left right) :
    EquilibriumPolicyEquivalent left right := by
  intro environment slow command policy
  constructor
  · rintro ⟨burnIn, eventuallyLeft⟩
    exact ⟨burnIn, fun extra ↦ by
      rw [← equivalent.repeatedPolicyAt_eq environment slow command]
      exact eventuallyLeft extra⟩
  · rintro ⟨burnIn, eventuallyRight⟩
    exact ⟨burnIn, fun extra ↦ by
      rw [equivalent.repeatedPolicyAt_eq environment slow command]
      exact eventuallyRight extra⟩

/-- The carrier reaches an operational equilibrium when repeated execution from
its initializer lands in an actual command-relative fixed state. -/
def ReachesCommandFixedPoint
    (carrier : StateCarrier Environment Slow Command LeftState LeftRead LeftRoute
      LeftProposal LeftObservation Policy)
    (environment : Environment) (slow : Slow) (command : Command) : Prop :=
  ∃ burnIn,
    CommandFixedPoint carrier environment slow command
      (carrier.runFromInitial environment slow
        (List.replicate burnIn command))

/-- Reaching a command-relative fixed point yields an eventually constant
policy observation at its readout. -/
theorem ReachesCommandFixedPoint.eventuallyObservesPolicy
    (carrier : StateCarrier Environment Slow Command LeftState LeftRead LeftRoute
      LeftProposal LeftObservation Policy)
    (environment : Environment) (slow : Slow) (command : Command)
    (reaches : ReachesCommandFixedPoint carrier environment slow command) :
    ∃ fixedState,
      CommandFixedPoint carrier environment slow command fixedState ∧
        EventuallyObservesPolicy carrier environment slow command
          (carrier.policyAtState environment slow fixedState) := by
  rcases reaches with ⟨burnIn, fixed⟩
  let fixedState := carrier.runFromInitial environment slow
    (List.replicate burnIn command)
  refine ⟨fixedState, fixed, burnIn, ?_⟩
  intro extra
  unfold repeatedPolicyAt
  have runToFixed :
      carrier.runFromInitial environment slow
          (List.replicate (burnIn + extra) command) = fixedState := by
    unfold StateCarrier.runFromInitial fixedState
    rw [List.replicate_add, StateCarrier.run_append]
    exact run_replicate_eq_of_commandFixedPoint carrier environment slow command
      (carrier.run environment slow (carrier.initialState environment slow)
        (List.replicate burnIn command)) fixed extra
  rw [runToFixed]

end ObservableEquilibrium

/-! ## Observable constancy need not expose a hidden fixed point -/

/-- A hidden counter advances forever while the public policy is constantly
`Unit`.  This is nontrivial internal motion, not a frozen-state construction. -/
def hiddenSuccessorConstantPolicyCarrier :
    StateCarrier Unit Unit Unit Nat Nat Unit Nat Unit Unit :=
  replacementCarrier
    (fun _environment _slow ↦ 0)
    (fun _environment _slow _command state ↦ state + 1)
    (fun _environment _slow _state ↦ ())
    (fun _environment _slow _observation ↦ ())

theorem hiddenSuccessorConstantPolicyCarrier_eventually_unit :
    EventuallyObservesPolicy hiddenSuccessorConstantPolicyCarrier
      () () () () := by
  refine ⟨0, ?_⟩
  intro extra
  rfl

theorem hiddenSuccessorConstantPolicyCarrier_never_reaches_fixedPoint :
    ¬ ReachesCommandFixedPoint hiddenSuccessorConstantPolicyCarrier
      () () () := by
  rintro ⟨burnIn, fixed⟩
  unfold CommandFixedPoint at fixed
  change hiddenSuccessorConstantPolicyCarrier.runFromInitial () ()
      (List.replicate burnIn ()) + 1 =
    hiddenSuccessorConstantPolicyCarrier.runFromInitial () ()
      (List.replicate burnIn ()) at fixed
  omega

/-- Observable equilibrium alone cannot certify that the hidden dynamics have
reached a command-relative fixed point. -/
theorem observableEquilibrium_does_not_imply_reachesCommandFixedPoint :
    EventuallyObservesPolicy hiddenSuccessorConstantPolicyCarrier
        () () () () ∧
      ¬ ReachesCommandFixedPoint hiddenSuccessorConstantPolicyCarrier
        () () () :=
  ⟨hiddenSuccessorConstantPolicyCarrier_eventually_unit,
    hiddenSuccessorConstantPolicyCarrier_never_reaches_fixedPoint⟩

/-! ## Equal equilibrium with unequal transients -/

/-- Reaches the observable `true` phase after one command. -/
def immediateTrueCarrier :
    StateCarrier Unit Unit Unit Nat Nat Unit Nat Bool Bool :=
  replacementCarrier
    (fun _environment _slow ↦ 0)
    (fun _environment _slow _command _state ↦ 2)
    (fun _environment _slow state ↦ state == 2)
    (fun _environment _slow observation ↦ observation)

/-- Reaches the same observable `true` phase only after two commands. -/
def delayedTrueCarrier :
    StateCarrier Unit Unit Unit Nat Nat Unit Nat Bool Bool :=
  replacementCarrier
    (fun _environment _slow ↦ 0)
    (fun _environment _slow _command state ↦
      match state with
      | 0 => 1
      | _ + 1 => 2)
    (fun _environment _slow state ↦ state == 2)
    (fun _environment _slow observation ↦ observation)

theorem immediateTrueCarrier_two_fixed :
    CommandFixedPoint immediateTrueCarrier () () () 2 := rfl

theorem delayedTrueCarrier_two_fixed :
    CommandFixedPoint delayedTrueCarrier () () () 2 := rfl

theorem immediateTrueCarrier_repeated_zero :
    repeatedPolicyAt immediateTrueCarrier () () () 0 = false := rfl

theorem immediateTrueCarrier_repeated_one_add (extra : Nat) :
    repeatedPolicyAt immediateTrueCarrier () () () (1 + extra) = true := by
  unfold repeatedPolicyAt StateCarrier.runFromInitial
  rw [List.replicate_add, StateCarrier.run_append]
  change immediateTrueCarrier.policyAtState () ()
      (immediateTrueCarrier.run () () 2 (List.replicate extra ())) = true
  rw [run_replicate_eq_of_commandFixedPoint immediateTrueCarrier () () () 2
    immediateTrueCarrier_two_fixed extra]
  rfl

theorem delayedTrueCarrier_repeated_zero :
    repeatedPolicyAt delayedTrueCarrier () () () 0 = false := rfl

theorem delayedTrueCarrier_repeated_one :
    repeatedPolicyAt delayedTrueCarrier () () () 1 = false := rfl

theorem delayedTrueCarrier_repeated_two_add (extra : Nat) :
    repeatedPolicyAt delayedTrueCarrier () () () (2 + extra) = true := by
  unfold repeatedPolicyAt StateCarrier.runFromInitial
  rw [List.replicate_add, StateCarrier.run_append]
  change delayedTrueCarrier.policyAtState () ()
      (delayedTrueCarrier.run () () 2 (List.replicate extra ())) = true
  rw [run_replicate_eq_of_commandFixedPoint delayedTrueCarrier () () () 2
    delayedTrueCarrier_two_fixed extra]
  rfl

theorem immediateTrueCarrier_eventually_true :
    EventuallyObservesPolicy immediateTrueCarrier () () () true := by
  refine ⟨1, ?_⟩
  intro extra
  exact immediateTrueCarrier_repeated_one_add extra

theorem delayedTrueCarrier_eventually_true :
    EventuallyObservesPolicy delayedTrueCarrier () () () true := by
  refine ⟨2, ?_⟩
  intro extra
  exact delayedTrueCarrier_repeated_two_add extra

theorem immediateTrueCarrier_not_eventually_false :
    ¬ EventuallyObservesPolicy immediateTrueCarrier () () () false := by
  rintro ⟨burnIn, eventuallyFalse⟩
  have falseAfterOne := eventuallyFalse 1
  have trueAfterOne :
      repeatedPolicyAt immediateTrueCarrier () () () (burnIn + 1) = true := by
    simpa [Nat.add_comm] using immediateTrueCarrier_repeated_one_add burnIn
  rw [trueAfterOne] at falseAfterOne
  exact Bool.noConfusion falseAfterOne

theorem delayedTrueCarrier_not_eventually_false :
    ¬ EventuallyObservesPolicy delayedTrueCarrier () () () false := by
  rintro ⟨burnIn, eventuallyFalse⟩
  have falseAfterTwo := eventuallyFalse 2
  have trueAfterTwo :
      repeatedPolicyAt delayedTrueCarrier () () () (burnIn + 2) = true := by
    simpa [Nat.add_comm] using delayedTrueCarrier_repeated_two_add burnIn
  rw [trueAfterTwo] at falseAfterTwo
  exact Bool.noConfusion falseAfterTwo

/-- The two carriers expose exactly the same eventually constant policies. -/
theorem immediate_delayed_equilibriumPolicyEquivalent :
    EquilibriumPolicyEquivalent immediateTrueCarrier delayedTrueCarrier := by
  intro environment slow command policy
  rcases environment with ⟨⟩
  rcases slow with ⟨⟩
  rcases command with ⟨⟩
  cases policy with
  | false =>
      exact ⟨fun observed ↦ False.elim
          (immediateTrueCarrier_not_eventually_false observed),
        fun observed ↦ False.elim
          (delayedTrueCarrier_not_eventually_false observed)⟩
  | true =>
      exact ⟨fun _observed ↦ delayedTrueCarrier_eventually_true,
        fun _observed ↦ immediateTrueCarrier_eventually_true⟩

/-- Their one-command policies differ, so equilibrium agreement does not imply
finite trajectory agreement. -/
theorem immediate_delayed_not_finitePolicyTrajectoryEquivalent :
    ¬ FinitePolicyTrajectoryEquivalent immediateTrueCarrier delayedTrueCarrier := by
  intro equivalent
  have oneStep := equivalent () () [()]
  simp [StateCarrier.policyTrajectoryFromInitial, StateCarrier.policyTrajectory,
    StateCarrier.trajectory, StateCarrier.policyAtState,
    StateCarrier.observeAtState, immediateTrueCarrier, delayedTrueCarrier,
    replacementCarrier, StateCarrier.step] at oneStep

theorem equilibriumPolicy_does_not_imply_finitePolicyTrajectory :
    EquilibriumPolicyEquivalent immediateTrueCarrier delayedTrueCarrier ∧
      ¬ FinitePolicyTrajectoryEquivalent immediateTrueCarrier delayedTrueCarrier :=
  ⟨immediate_delayed_equilibriumPolicyEquivalent,
    immediate_delayed_not_finitePolicyTrajectoryEquivalent⟩

/-! ## Equilibrium and checker acceptance are incomparable -/

/-- One scheduled command followed by exact terminal-policy acceptance. -/
def oneStepTerminalPolicySearch : CheckerMediatedSearch Unit Bool Bool where
  schedules := ([ [()] ] : List (List Unit))
  accepts := fun policies program ↦ policies.getLast? = some program

theorem oneStepTerminalPolicySearch_immediate_true_mass :
    acceptedProgramMass oneStepTerminalPolicySearch immediateTrueCarrier
      () () true = 1 := by
  classical
  unfold acceptedProgramMass
  change Multiset.countP _
    (([ [()] ] : List (List Unit)) : Multiset (List Unit)) = 1
  rw [Multiset.coe_countP, List.countP_cons_of_pos]
  · rfl
  rw [decide_eq_true_eq]
  rfl

theorem oneStepTerminalPolicySearch_delayed_true_mass :
    acceptedProgramMass oneStepTerminalPolicySearch delayedTrueCarrier
      () () true = 0 := by
  classical
  unfold acceptedProgramMass
  change Multiset.countP _
    (([ [()] ] : List (List Unit)) : Multiset (List Unit)) = 0
  rw [Multiset.coe_countP, List.countP_cons_of_neg]
  · rfl
  rw [decide_eq_true_eq]
  simp [oneStepTerminalPolicySearch, delayedTrueCarrier, replacementCarrier,
    StateCarrier.policyTrajectoryFromInitial, StateCarrier.policyTrajectory,
    StateCarrier.policyAtState, StateCarrier.observeAtState, StateCarrier.step]

/-- Equal eventual equilibrium does not force equal accepted search mass when
the bounded search observes different transients. -/
theorem oneStepTerminalPolicySearch_not_distributionEquivalent :
    ¬ AcceptedProgramDistributionEquivalent oneStepTerminalPolicySearch
      immediateTrueCarrier delayedTrueCarrier := by
  intro equivalent
  have programTrue := equivalent () () true
  rw [oneStepTerminalPolicySearch_immediate_true_mass,
    oneStepTerminalPolicySearch_delayed_true_mass] at programTrue
  omega

theorem equilibriumPolicy_does_not_imply_acceptedProgramDistribution :
    EquilibriumPolicyEquivalent immediateTrueCarrier delayedTrueCarrier ∧
      ¬ AcceptedProgramDistributionEquivalent oneStepTerminalPolicySearch
        immediateTrueCarrier delayedTrueCarrier :=
  ⟨immediate_delayed_equilibriumPolicyEquivalent,
    oneStepTerminalPolicySearch_not_distributionEquivalent⟩

/-- Successor execution adds exactly one for every repeated command. -/
theorem successorCarrier_run_replicate (state repetitions : Nat) :
    successorCarrier.run () () state (List.replicate repetitions ()) =
      state + repetitions := by
  induction repetitions generalizing state with
  | zero => simp
  | succ repetitions inductionHypothesis =>
      rw [List.replicate_succ]
      change successorCarrier.run () () (state + 1)
          (List.replicate repetitions ()) = state + (repetitions + 1)
      rw [inductionHypothesis]
      omega

/-- Successor execution exposes its step count as policy. -/
theorem successorCarrier_repeatedPolicyAt (repetitions : Nat) :
    repeatedPolicyAt successorCarrier () () () repetitions = repetitions := by
  unfold repeatedPolicyAt StateCarrier.runFromInitial
  change successorCarrier.run () () 0 (List.replicate repetitions ()) = repetitions
  simpa using successorCarrier_run_replicate 0 repetitions

theorem delayedJumpCarrier_reaches_fixedPoint :
    ReachesCommandFixedPoint delayedJumpCarrier () () () := by
  refine ⟨2, ?_⟩
  rfl

theorem delayedJumpCarrier_three_fixed :
    CommandFixedPoint delayedJumpCarrier () () () 3 := rfl

theorem delayedJumpCarrier_eventually_three :
    EventuallyObservesPolicy delayedJumpCarrier () () () 3 := by
  refine ⟨2, ?_⟩
  intro extra
  unfold repeatedPolicyAt StateCarrier.runFromInitial
  rw [List.replicate_add, StateCarrier.run_append]
  change delayedJumpCarrier.policyAtState () ()
      (delayedJumpCarrier.run () () 3 (List.replicate extra ())) = 3
  rw [run_replicate_eq_of_commandFixedPoint delayedJumpCarrier () () () 3
    delayedJumpCarrier_three_fixed extra]
  rfl

theorem successorCarrier_not_eventually_three :
    ¬ EventuallyObservesPolicy successorCarrier () () () 3 := by
  rintro ⟨burnIn, eventuallyThree⟩
  have contradiction := eventuallyThree 4
  rw [successorCarrier_repeatedPolicyAt] at contradiction
  omega

/-- The existing nonzero equal accepted-distribution fixture has unequal
observable equilibria. -/
theorem successor_delayedJump_not_equilibriumPolicyEquivalent :
    ¬ EquilibriumPolicyEquivalent successorCarrier delayedJumpCarrier := by
  intro equivalent
  exact successorCarrier_not_eventually_three
    ((equivalent () () () 3).mpr delayedJumpCarrier_eventually_three)

theorem acceptedProgramDistribution_does_not_imply_equilibriumPolicy :
    AcceptedProgramDistributionEquivalent acceptsOnlyOneSearch
        successorCarrier delayedJumpCarrier ∧
      ¬ EquilibriumPolicyEquivalent successorCarrier delayedJumpCarrier :=
  ⟨successor_delayedJump_acceptedProgramDistributionEquivalent,
    successor_delayedJump_not_equilibriumPolicyEquivalent⟩

/-! ## Observable equilibrium and longitudinal feedback are incomparable -/

/-- A feedback kernel that records the accepted mass of program `true` after
the one-step search.  Unlike a profile-forgetting kernel, it preserves the
part of the checker profile that separates the transient fixtures. -/
def trueMassFeedbackKernel :
    LongitudinalSearchKernel Unit Unit Bool Bool Nat where
  carrierSlow := fun _generation ↦ ()
  searchAt := fun _generation ↦ oneStepTerminalPolicySearch
  advance := fun _generation profile ↦ profile true

theorem trueMassFeedbackKernel_immediate_next_zero :
    nextGenerationState trueMassFeedbackKernel immediateTrueCarrier () 0 = 1 := by
  simpa [nextGenerationState, acceptedProgramProfile, trueMassFeedbackKernel] using
    oneStepTerminalPolicySearch_immediate_true_mass

theorem trueMassFeedbackKernel_delayed_next_zero :
    nextGenerationState trueMassFeedbackKernel delayedTrueCarrier () 0 = 0 := by
  simpa [nextGenerationState, acceptedProgramProfile, trueMassFeedbackKernel] using
    oneStepTerminalPolicySearch_delayed_true_mass

theorem immediate_delayed_not_longitudinalDiscoveryProcessEquivalent :
    ¬ LongitudinalDiscoveryProcessEquivalent trueMassFeedbackKernel
      immediateTrueCarrier delayedTrueCarrier := by
  intro equivalent
  have oneGeneration := equivalent () 0 1
  simp only [longitudinalDiscoveryTrajectory] at oneGeneration
  rw [trueMassFeedbackKernel_immediate_next_zero,
    trueMassFeedbackKernel_delayed_next_zero] at oneGeneration
  simp at oneGeneration

/-- Equal observable equilibria need not survive a feedback process that
records bounded transient acceptance. -/
theorem equilibriumPolicy_does_not_imply_longitudinalDiscoveryProcess :
    EquilibriumPolicyEquivalent immediateTrueCarrier delayedTrueCarrier ∧
      ¬ LongitudinalDiscoveryProcessEquivalent trueMassFeedbackKernel
        immediateTrueCarrier delayedTrueCarrier :=
  ⟨immediate_delayed_equilibriumPolicyEquivalent,
    immediate_delayed_not_longitudinalDiscoveryProcessEquivalent⟩

/-- Conversely, a feedback process that discards its accepted profile can be
longitudinally equal even when the carriers have different equilibria. -/
theorem longitudinalDiscoveryProcess_does_not_imply_equilibriumPolicy :
    LongitudinalDiscoveryProcessEquivalent profileForgettingIncrementKernel
        successorCarrier delayedJumpCarrier ∧
      ¬ EquilibriumPolicyEquivalent successorCarrier delayedJumpCarrier :=
  ⟨profileForgetting_longitudinalEquivalent,
    successor_delayedJump_not_equilibriumPolicyEquivalent⟩

#print axioms StateCarrier.trajectory_getLast?_eq_run
#print axioms FinitePolicyTrajectoryEquivalent.equilibriumPolicyEquivalent
#print axioms ReachesCommandFixedPoint.eventuallyObservesPolicy
#print axioms observableEquilibrium_does_not_imply_reachesCommandFixedPoint
#print axioms equilibriumPolicy_does_not_imply_finitePolicyTrajectory
#print axioms equilibriumPolicy_does_not_imply_acceptedProgramDistribution
#print axioms acceptedProgramDistribution_does_not_imply_equilibriumPolicy
#print axioms equilibriumPolicy_does_not_imply_longitudinalDiscoveryProcess
#print axioms longitudinalDiscoveryProcess_does_not_imply_equilibriumPolicy

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
