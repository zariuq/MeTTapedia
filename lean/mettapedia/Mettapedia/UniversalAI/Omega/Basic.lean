import Mathlib.Data.NNReal.Defs
import Mettapedia.CognitiveArchitecture.ProblemSolvingMethods
import Mettapedia.UniversalAI.SelfModification.ProofBackedImprovement
import Mettapedia.UniversalAI.SolomonoffPrior

/-!
# Omega architecture: source-faithful compositional core

Eray Ozkural, *Omega: An Architecture for AI Unification*
(arXiv:1805.12069, 2018), presents Omega as a synthesis of:

* Solomonoff's Alpha architecture and its open-ended problem-solving methods;
* Schmidhuber's proof-backed self-improvement programme; and
* Ozkural's own architectural deltas: an explicitly assumed AI-kernel
  bootstrap, Heuristic Algorithmic Memory 2.0 over multiple reference
  machines, analysis/synthesis over PSMs, forecast-guided ensemble execution,
  and operation without assuming a substantially known environment.

The reusable components live outside this historical namespace:

* `CognitiveArchitecture.ProblemSolvingMethods` supplies proof-relevant PSM
  registries, evidence-retaining invention, and multiple-reference-machine
  memory;
* `UniversalAI.SelfModification.ProofBackedImprovement` supplies the abstract
  improvement interface; and
* `UniversalAI.SolomonoffPrior` supplies the actual prefix-free universal
  machine interface.

This file composes those parts.  It does not identify Omega with OmegaClaw,
does not identify a tool authorization broker with a PSM registry, and does
not claim that Ozkural's assumed bootstrap was demonstrated in the 2018 paper.
-/

namespace Mettapedia.UniversalAI.Omega

open Mettapedia.CognitiveArchitecture.ProblemSolvingMethods
open Mettapedia.UniversalAI.SelfModification
open Mettapedia.UniversalAI.SolomonoffPrior
open scoped NNReal

universe uProblem uSolution uMethod uMachine uInput uOutput uKernel uCapability
  uAnalysis uSynthesis uValue uMethodAdmission uMethodRealization uProgram uRun
  uRetained uTransfer uBootstrap uImprovement

/-! ## The independently sourced Alpha component -/

/-- Solomonoff's Alpha substrate, represented by an actual universal
prefix-free machine rather than redefined inside Omega. -/
structure AlphaSubstrate where
  machine : PrefixFreeMachine
  universal : UniversalPFM machine

namespace AlphaSubstrate

/-- The inherited Alpha substrate supplies the existing algorithmic
probability, without attributing that construction to Omega. -/
noncomputable def outputWeight (alpha : AlphaSubstrate)
    (programs : Finset BinString) (output : BinString) : ℝ :=
  algorithmicProbability alpha.machine programs output

theorem outputWeight_nonneg (alpha : AlphaSubstrate)
    (programs : Finset BinString) (output : BinString) :
    0 ≤ alpha.outputWeight programs output :=
  algorithmicProbability_nonneg alpha.machine programs output

end AlphaSubstrate

/-! ## Explicit bootstrap and reflective cognition -/

/-- The AI-kernel bootstrap is an explicit premise with its own reachability
evidence.  Ozkural assumes such a kernel in the 2018 architecture; this
definition neither manufactures nor hides that witness. -/
structure BootstrapPremise
    (KernelState : Type uKernel) (Capability : Type uCapability) where
  initialState : KernelState
  targetCapability : Capability
  Reaches : KernelState → Capability → Type uAnalysis
  bootstrap : Reaches initialState targetCapability

/-- Architecture-neutral higher-order analysis and synthesis.

The plan types are intentionally abstract: an architecture may use trees,
graphs, GSLT presentations, or another decomposition language. -/
structure ReflectiveCognition
    (Problem : Type uProblem) (Method : Type uMethod) where
  AnalysisPlan : Type uAnalysis
  SynthesisPlan : Type uSynthesis
  analyzes : Problem → AnalysisPlan → Type uAnalysis
  usesMethod : SynthesisPlan → Method → Type uSynthesis
  producesMethod : SynthesisPlan → Method → Type uSynthesis

/-! ## Forecast-guided ensemble execution -/

/-- An ensemble assigns success forecasts and nonnegative execution budgets.

`forecastMonotone` formalizes only Ozkural's stated ordering discipline: a
method with no lower predicted success receives no lower allocation.  It does
not assert that the forecasts are calibrated or that the ensemble is optimal.
-/
structure ForecastGuidedEnsemble
    (Problem : Type uProblem) (Method : Type uMethod) where
  successForecast : Method → Problem → Set.Icc (0 : ℝ) 1
  allocation : Method → Problem → ℝ≥0
  forecastMonotone : ∀ {left right problem},
    successForecast left problem ≤ successForecast right problem →
      allocation left problem ≤ allocation right problem

/-! ## Environment-knowledge distinction -/

/-- How much environment structure is assumed before learning. -/
inductive InitialEnvironmentKnowledge where
  | unknown
  | partiallyKnown
  | substantiallyKnown
  deriving DecidableEq, Repr

/-- The explicit Omega delta from the substantially-known-environment reading
of the Gödel-machine architecture. -/
def DoesNotAssumeSubstantiallyKnown
    (knowledge : InitialEnvironmentKnowledge) : Prop :=
  knowledge ≠ .substantiallyKnown

theorem unknown_does_not_assume_substantiallyKnown :
    DoesNotAssumeSubstantiallyKnown .unknown := by
  simp [DoesNotAssumeSubstantiallyKnown]

/-- Negative control: labeling an initially known environment as unknown is
not licensed by the distinction. -/
theorem substantiallyKnown_not_unknown :
    ¬ DoesNotAssumeSubstantiallyKnown .substantiallyKnown := by
  simp [DoesNotAssumeSubstantiallyKnown]

/-! ## Composed architecture -/

/-- The source-faithful compositional data of an Omega architecture.

The structure deliberately contains no theorem that its bootstrap succeeds,
its forecasts are calibrated, or its invented methods improve performance;
those are separate profile properties with explicit evidence. -/
structure Architecture
    (Problem : Type uProblem) (Solution : Type uSolution) (Method : Type uMethod)
    (Machine : Type uMachine) (Input : Type uInput) (Output : Type uOutput)
    (KernelState : Type uKernel) (Capability : Type uCapability)
    (Value : Type uValue) [Preorder Value] where
  alpha : AlphaSubstrate
  bootstrap : BootstrapPremise.{uKernel, uCapability, uBootstrap} KernelState Capability
  methods : Registry.{uProblem, uSolution, uMethod, uMethodAdmission,
    uMethodRealization} Problem Solution Method
  referenceMachines : ReferenceMachineFamily.{uInput, uOutput, uMachine, uProgram,
    uRun} Machine Input Output
  memory : MultiMachineMemory.{uInput, uOutput, uMachine, uRetained, uTransfer,
    uProgram, uRun} referenceMachines
  cognition : ReflectiveCognition.{uProblem, uMethod, uAnalysis, uSynthesis} Problem Method
  ensemble : ForecastGuidedEnsemble Problem Method
  selfImprovement : ProofBackedImprovement.{uKernel, uValue, uImprovement}
    KernelState Value
  initialEnvironmentKnowledge : InitialEnvironmentKnowledge

/-- The specifically Ozkuralian claims about one architecture are carried as
evidence rather than silently installed in the general record.

`futureMethods` and `inventedMethod` witness open-ended PSM invention and
retention.  `multiMachineMemory` witnesses the HAM 2.0 multiple-reference-
machine delta.  `unknownEnvironment` witnesses the environmental distinction.
-/
structure SourceProfile
    {Problem : Type uProblem} {Solution : Type uSolution} {Method : Type uMethod}
    {Machine : Type uMachine} {Input : Type uInput} {Output : Type uOutput}
    {KernelState : Type uKernel} {Capability : Type uCapability}
    {Value : Type uValue} [Preorder Value]
    (architecture : Architecture.{uProblem, uSolution, uMethod, uMachine, uInput,
      uOutput, uKernel, uCapability, uAnalysis, uSynthesis, uValue,
      uMethodAdmission, uMethodRealization, uProgram, uRun, uRetained, uTransfer,
      uBootstrap, uImprovement} Problem Solution Method Machine Input Output
      KernelState Capability Value) where
  futureMethods : Registry.{uProblem, uSolution, uMethod, uMethodAdmission,
    uMethodRealization} Problem Solution Method
  invented : Method
  inventedMethod : InventionReceipt architecture.methods futureMethods invented
  multiMachineMemory : UsesMultipleMachines architecture.memory
  unknownEnvironment :
    DoesNotAssumeSubstantiallyKnown architecture.initialEnvironmentKnowledge

namespace SourceProfile

/-- Open-endedness implies that the future registry has a genuinely new
admission receipt. -/
theorem admits_genuinely_new_method
    [Preorder Value]
    {architecture : Architecture Problem Solution Method Machine Input Output
      KernelState Capability Value}
    (profile : SourceProfile architecture) :
    Nonempty (profile.futureMethods.Admission profile.invented) ∧
      IsEmpty (architecture.methods.Admission profile.invented) :=
  ⟨⟨profile.inventedMethod.admittedAfter⟩, profile.inventedMethod.absentBefore⟩

/-- Existing admission receipts survive the source-profile extension
injectively. -/
def retainAdmission
    [Preorder Value]
    {architecture : Architecture Problem Solution Method Machine Input Output
      KernelState Capability Value}
    (profile : SourceProfile architecture) (method : Method) :
    architecture.methods.Admission method ↪ profile.futureMethods.Admission method :=
  profile.inventedMethod.extension.admission method

end SourceProfile

#print axioms unknown_does_not_assume_substantiallyKnown
#print axioms substantiallyKnown_not_unknown
#print axioms SourceProfile.admits_genuinely_new_method

end Mettapedia.UniversalAI.Omega
