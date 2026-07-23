import Mettapedia.Languages.MeTTa.HE.LeaTTaEvaluatorConfigurationConformance
import Mettapedia.Languages.MeTTa.HE.StateFreeExecution
import Mettapedia.Languages.MeTTa.HE.StateFreeInterpreterSteps

/-!
# State-free evaluator configuration conformance

The evaluator configuration boundary depends on the runtime world but not on
the gensym counter.  A derivation-local state-free certificate therefore
transports the complete configuration relation across `interpretFuel` in one
step: the certificate preserves the world, and the counter remains private
operational bookkeeping.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaStateFreeConfigurationConformance

open Mettapedia.Languages.MeTTa.HE
open LeaTTaEvaluatorConfigurationConformance
open StateFreeExecution
open StateFreeInterpreterSteps

/-- Configuration correspondence is insensitive to the runtime gensym
counter.  No alpha spelling is exposed by the carrier. -/
theorem runtimeConfigurationRel_withCounter
    {services : Spec.Eval.Minimal.Services}
    {oracle : LeaTTaSpecTypeService.TypePreparationOracle}
    {space : Space} {groundingTable : Metta.GroundingTable}
    {env : Metta.Minimal.MinEnv} {state : Metta.Minimal.St}
    (configuration : RuntimeConfigurationRel services oracle space
      groundingTable env state)
    (counter : Nat) :
    RuntimeConfigurationRel services oracle space groundingTable env
      { state with counter := counter } := by
  exact
    { serviceLaws := configuration.serviceLaws
      environment := configuration.environment
      emptyWorld := configuration.emptyWorld
      contextPayload := configuration.contextPayload
      preparationFunctional := configuration.preparationFunctional
      preparationRuntime := configuration.preparationRuntime }

/-- Any state with the same world realizes the same evaluator configuration.
This is the exact state-component transport used after a certified run. -/
theorem runtimeConfigurationRel_of_world_eq
    {services : Spec.Eval.Minimal.Services}
    {oracle : LeaTTaSpecTypeService.TypePreparationOracle}
    {space : Space} {groundingTable : Metta.GroundingTable}
    {env : Metta.Minimal.MinEnv} {state nextState : Metta.Minimal.St}
    (configuration : RuntimeConfigurationRel services oracle space
      groundingTable env state)
    (worldEquation : nextState.world = state.world) :
    RuntimeConfigurationRel services oracle space groundingTable env
      nextState := by
  exact
    { serviceLaws := configuration.serviceLaws
      environment := configuration.environment
      emptyWorld := worldEquation.trans configuration.emptyWorld
      contextPayload := configuration.contextPayload
      preparationFunctional := configuration.preparationFunctional
      preparationRuntime := by
        simpa [worldEquation] using configuration.preparationRuntime }

/-- **State-component lifting theorem.**  A derivation-local certificate
transports the complete runtime evaluator configuration through an arbitrary
`interpretFuel` run.  The theorem makes no global claim about unreachable
rules in the environment.  A nontrivial evaluator certificate is a separate
simulation obligation; the generic lifting theorem does not supply one. -/
theorem runtimeConfigurationRel_interpretFuel
    {services : Spec.Eval.Minimal.Services}
    {oracle : LeaTTaSpecTypeService.TypePreparationOracle}
    {space : Space} {groundingTable : Metta.GroundingTable}
    {env : Metta.Minimal.MinEnv} {state : Metta.Minimal.St}
    {Inv : Metta.Minimal.World → Metta.Minimal.Item → Prop}
    (configuration : RuntimeConfigurationRel services oracle space
      groundingTable env state)
    (certificate : Certificate env Inv)
    (fuel : Nat) (work : List Metta.Minimal.Item)
    (done : List (Metta.Atom × Metta.Bindings))
    (reached : ∀ item ∈ work, Inv state.world item) :
    RuntimeConfigurationRel services oracle space groundingTable env
      (Metta.Minimal.interpretFuel env fuel state work done).2 := by
  apply runtimeConfigurationRel_of_world_eq configuration
  exact interpretFuel_preservesWorld certificate fuel state work done reached

/-- Positive canary: changing only the private counter preserves a canonical
configuration. -/
example
    {services : Spec.Eval.Minimal.Services}
    {oracle : LeaTTaSpecTypeService.TypePreparationOracle}
    {space : Space} {groundingTable : Metta.GroundingTable}
    {env : Metta.Minimal.MinEnv} {state : Metta.Minimal.St}
    (configuration : RuntimeConfigurationRel services oracle space
      groundingTable env state) :
    RuntimeConfigurationRel services oracle space groundingTable env
      { state with counter := state.counter + 1 } :=
  runtimeConfigurationRel_withCounter configuration (state.counter + 1)

/-- Negative canary: every related configuration really does start at the
empty runtime world; the state component is not ignored wholesale. -/
theorem runtimeConfigurationRel_world_is_empty
    {services : Spec.Eval.Minimal.Services}
    {oracle : LeaTTaSpecTypeService.TypePreparationOracle}
    {space : Space} {groundingTable : Metta.GroundingTable}
    {env : Metta.Minimal.MinEnv} {state : Metta.Minimal.St}
    (configuration : RuntimeConfigurationRel services oracle space
      groundingTable env state) :
    state.world = Metta.Minimal.World.empty :=
  configuration.emptyWorld

/-- A nontrivial configuration transport through a genuine pending evaluator
run in the shipped prelude environment.  The variable-headed query executes
the evaluator and terminates as `NotReducible`; the derivation-local
certificate, rather than a global purity claim about the prelude, supplies the
world-invariance proof. -/
theorem runtimeConfigurationRel_fullPrelude_pendingVariableEval
    {services : Spec.Eval.Minimal.Services}
    {oracle : LeaTTaSpecTypeService.TypePreparationOracle}
    {space : Space} {groundingTable : Metta.GroundingTable}
    {state : Metta.Minimal.St}
    (configuration : RuntimeConfigurationRel services oracle space
      groundingTable fullPreludeEnv state)
    (fuel : Nat) :
    RuntimeConfigurationRel services oracle space groundingTable
      fullPreludeEnv
      (Metta.Minimal.interpretFuel fullPreludeEnv fuel state
        [pendingVariableEvalItem] []).2 := by
  apply runtimeConfigurationRel_interpretFuel configuration
    (pendingVariableEval_stateFreeExecution fullPreludeEnv)
  intro item member
  have itemEquation : item = pendingVariableEvalItem := by simpa using member
  exact Or.inl itemEquation

end Mettapedia.Languages.MeTTa.HE.LeaTTaStateFreeConfigurationConformance
