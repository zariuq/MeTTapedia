/-
# Prime-internal typed scheduler policies

This module instantiates quantale-valued occurrence-preserving control on the
actual Prime Need reference machine.  A scheduler policy is an ordinary value
of Prime's semantic CwF, while the Need transition relation remains the sole
authority for work generation.  Consequently every controlled emission keeps
its exact Need derivation and transition clock.

The syntax grammar for authored weighted/parity policies is a separate I2
obligation.  This file establishes the semantic internalization boundary and
an open command vocabulary; it does not claim that every Lean function is
already expressible by Prime syntax.
-/

import Mettapedia.GSLT.Core.WeightedMuScheduler
import Mettapedia.Languages.MeTTa.NativeTypeTheoryDerivation
import Mettapedia.Languages.MeTTa.PrimeNeedInferenceControl
import Mettapedia.Logic.ModalMuCalculusEvaluationGame

namespace Mettapedia.Languages.MeTTa.Prime.TypedScheduler

open scoped ENNReal

open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.GSLT.Core.WeightedMuScheduler
open Mettapedia.Languages.MeTTa.NativeTypeTheory
open Mettapedia.Languages.MeTTa.PrimeNeedInferenceControl
open Mettapedia.Languages.MeTTa.PrimeNeedReference

universe uOrigin uLocal uResume uRule uValue uStable uRetry uEffect uFeature

/-! ## An open authored policy vocabulary -/

/-- The fixed structural commands are small; language- or agent-specific rank
features remain an open type parameter instead of extending a host enum. -/
inductive PolicyCommand (Feature : Type uFeature) where
  | breadthFirst
  | depthFirst
  | rankBy (feature : Feature)
deriving DecidableEq, Repr

/-- Interpretation is explicit data at the capability boundary.  A rank
feature is allowed to reorder only; the resulting scheduler still proves exact
frontier permutation. -/
noncomputable def interpretCommand
    (rankScheduler : Feature → Scheduler Node) :
    PolicyCommand Feature → Scheduler Node
  | .breadthFirst => Scheduler.breadthFirst
  | .depthFirst => Scheduler.depthFirst
  | .rankBy feature => rankScheduler feature

/-- An authored policy command is already a program in the generic inference
control language. -/
def commandProgram (command : PolicyCommand Feature) :
    Controller.Program Node Answer (PolicyCommand Feature) Unit where
  initialMemory := ()
  command _ := command
  advance _ _ _ _ := ()

/-! ## Prime Need as a quantale-policy instance -/

section Need

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect : Type}

abbrev NeedMachine
    (Origin : Type uOrigin) (Local : Type uLocal) (Resume : Type uResume)
    (Rule : Type uRule) (Value : Type uValue)
    (StableFault : Type uStable) (RetryableFault : Type uRetry)
    (Effect : Type uEffect) :=
  Machine Origin Local Resume Rule Value StableFault RetryableFault Effect

abbrev NeedOccurrence
    (Origin : Type uOrigin) (Local : Type uLocal) (Resume : Type uResume)
    (Rule : Type uRule) (Value : Type uValue)
    (StableFault : Type uStable) (RetryableFault : Type uRetry)
    (Effect : Type uEffect) :=
  WorkOccurrence
    (NeedMachine Origin Local Resume Rule Value StableFault RetryableFault Effect)

abbrev NeedAnswer (Value : Type uValue) (StableFault : Type uStable)
    (RetryableFault : Type uRetry) :=
  Produced Value StableFault RetryableFault × List Nat

/-- Prime Need's conservative default policy: every occurrence has unit grade
and breadth-first ordering.  Demand behavior remains in the Need machine; this
policy only schedules the machine's live branch occurrences. -/
noncomputable def needPolicy :
    QuantalePolicy ℝ≥0∞
      (NeedOccurrence Origin Local Resume Rule Value StableFault RetryableFault Effect)
      (NeedAnswer Value StableFault RetryableFault) Unit :=
  QuantalePolicy.neutral Scheduler.breadthFirst 1 one_mul mul_one

/-- The neutral quantale instance elaborates to exactly the pre-existing
breadth-first scheduler. -/
theorem needPolicy_scheduler_exact :
    (needPolicy (Origin := Origin) (Local := Local) (Resume := Resume)
      (Rule := Rule) (Value := Value) (StableFault := StableFault)
      (RetryableFault := RetryableFault) (Effect := Effect)).scheduler () =
        (Scheduler.breadthFirst : Scheduler
          (NeedOccurrence Origin Local Resume Rule Value StableFault RetryableFault Effect)) :=
  QuantalePolicy.neutral_scheduler_eq _ 1 one_mul mul_one

/-- Controlled Prime Need execution retains the generic reachability safety
invariant for every observation budget. -/
theorem needPolicy_run_sound
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (initial : NeedMachine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (fuel : Nat) :
    (Snapshot.run (Reference.occurrenceSystem spec) needPolicy.controller fuel
      (Snapshot.initial needPolicy.controller
        [WorkOccurrence.root initial])).search.Sound
      (Reference.occurrenceSystem spec) [WorkOccurrence.root initial] :=
  QuantalePolicy.run_sound needPolicy (Reference.occurrenceSystem spec)
    [WorkOccurrence.root initial] fuel

/-- A scheduler-selected answer still carries an exact Need derivation and
the original occurrence trace. -/
theorem needPolicy_emission_has_steps
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (initial : NeedMachine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (fuel : Nat)
    {event : Emission
      (NeedOccurrence Origin Local Resume Rule Value StableFault RetryableFault Effect)
      (NeedAnswer Value StableFault RetryableFault)}
    (member : event ∈
      (Snapshot.run (Reference.occurrenceSystem spec) needPolicy.controller fuel
        (Snapshot.initial needPolicy.controller
          [WorkOccurrence.root initial])).search.events) :
    Steps spec event.origin.trace.length initial event.origin.state ∧
      haltedOutcome event.origin.state = some event.value.1 ∧
      event.value.2 = event.origin.trace :=
  Reference.controlled_emission_has_steps spec needPolicy.controller initial
    fuel member

/-! ## Semantic Prime internalization -/

/-- Closed stage-zero context of Prime's semantic CwF. -/
abbrev PrimeContext := familiesCwF.empty (stageOfNat 0)

/-- Typed scheduler policies over any admitted quantale carrier are
first-class Prime semantic values.  The carrier remains visible in the type;
PLN evidence, weakness, and cost are therefore instances rather than fields
silently collapsed into one universal score. -/
def policyTyFor (Q : Type) [Semigroup Q] [CompleteLattice Q] [IsQuantale Q] :
    familiesCwF.Ty PrimeContext :=
  fun _ => QuantalePolicy Q
    (NeedOccurrence Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (NeedAnswer Value StableFault RetryableFault) Unit

/-- The existing default policy uses the extended nonnegative reals. -/
abbrev policyTy : familiesCwF.Ty PrimeContext :=
  policyTyFor (Origin := Origin) (Local := Local) (Resume := Resume)
    (Rule := Rule) (Value := Value) (StableFault := StableFault)
    (RetryableFault := RetryableFault) (Effect := Effect) ℝ≥0∞

/-- Temporal objectives are also ordinary Prime semantic values, not an
external scheduler configuration language. -/
def temporalObjectiveTy (State Act : Type) : familiesCwF.Ty PrimeContext :=
  fun _ => TemporalObjective State Act

/-- A weighted parity automaton retains its quantale carrier in its Prime
type.  Its checked progress certificate stays a separate proof-relevant
value, so an automaton is never accepted merely because it is representable. -/
def weightedParityAutomatonTy (Q State : Type)
    [Semigroup Q] [CompleteLattice Q] [IsQuantale Q] :
    familiesCwF.Ty PrimeContext :=
  fun _ => WeightedParityAutomaton Q State

/-- The default Need policy as an ordinary closed Prime term. -/
noncomputable def internalNeedPolicy :
    familiesCwF.Tm PrimeContext
      (policyTy (Origin := Origin) (Local := Local) (Resume := Resume)
        (Rule := Rule) (Value := Value) (StableFault := StableFault)
        (RetryableFault := RetryableFault) (Effect := Effect)) :=
  fun _ => needPolicy

/-- Evaluating the internal term returns exactly the policy used by the
controller realization. -/
@[simp] theorem internalNeedPolicy_apply :
    internalNeedPolicy (Origin := Origin) (Local := Local) (Resume := Resume)
        (Rule := Rule) (Value := Value) (StableFault := StableFault)
        (RetryableFault := RetryableFault) (Effect := Effect) PUnit.unit =
      (needPolicy : QuantalePolicy ℝ≥0∞
        (NeedOccurrence Origin Local Resume Rule Value StableFault RetryableFault Effect)
        (NeedAnswer Value StableFault RetryableFault) Unit) :=
  rfl

end Need

/-! ## Executable presentations of temporal objectives -/

namespace TemporalObjective

open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.Logic.ModalMuCalculus.EvaluationGame

universe uState uAct

variable {State : Type uState} {Act : Type uAct}

/-- The scheduler objective's one ambient variable is the model observation;
fixed-point variables are compiled separately as arena back-edges. -/
def evaluationProgram (objective : TemporalObjective State Act) :
    Program Act Unit :=
  compilePositive objective.formula (fun _ => ()) objective.fixedPointsPositive

/-- Executable finite data presenting the relational LTS and observed-state
set of a scheduler objective. -/
structure FinitePresentation [Fintype State]
    (objective : TemporalObjective State Act) where
  model : FiniteModel State Act Unit
  transition_correct : ∀ source action target,
    model.system.edge source action target = true ↔
      objective.lts.trans source action target
  observation_correct : ∀ state,
    model.holds state () = true ↔ state ∈ objective.observed

/-- The executable presentation and the original scheduler objective have
identical denotational semantics. -/
theorem evaluationProgram_denotes_iff [Fintype State]
    (objective : TemporalObjective State Act)
    (presentation : FinitePresentation objective) (state : State) :
    (evaluationProgram objective).Denotes presentation.model state ↔
      objective.Accepts state := by
  unfold Program.Denotes TemporalObjective.Accepts
  apply satisfies_congr
  · intro source action target
    exact presentation.transition_correct source action target
  · intro index current
    simpa [Program.semanticEnv, evaluationProgram, compilePositive,
      FiniteModel.observationSet] using presentation.observation_correct current

/-- Every temporal objective accepted by the existing positivity gate compiles
to a pointer-safe finite formula graph. -/
theorem evaluationProgram_graph_valid (objective : TemporalObjective State Act) :
    (evaluationProgram objective).graphValid = true :=
  Program.graphValid_eq_true _

/-- The concrete parity arena used by a finite scheduler presentation. -/
def evaluationGame [Fintype State] [DecidableEq State]
    (objective : TemporalObjective State Act)
    (presentation : FinitePresentation objective) :=
  (evaluationProgram objective).game presentation.model

/-! ### A real fixed-point customer -/

def observedSingletonObjective : TemporalObjective Unit Unit where
  lts.trans _ _ _ := False
  observed := Set.univ
  formula := TemporalObjective.eventuallyObserved ()
  fixedPointsPositive := TemporalObjective.eventuallyObserved_positive ()

def observedSingletonPresentation :
    FinitePresentation observedSingletonObjective where
  model.system.edge _ _ _ := false
  model.holds _ _ := true
  transition_correct _ _ _ := by simp [observedSingletonObjective]
  observation_correct _ := by simp [observedSingletonObjective]

theorem observedSingleton_program_graph_valid :
    (evaluationProgram observedSingletonObjective).graphValid = true := by
  exact evaluationProgram_graph_valid _

theorem observedSingleton_denotes :
    (evaluationProgram observedSingletonObjective).Denotes
      observedSingletonPresentation.model () := by
  rw [evaluationProgram_denotes_iff]
  intro candidate preFixed
  apply preFixed ()
  simp [observedSingletonObjective, TemporalObjective.eventuallyObserved,
    satisfies, Env.extend]

/-- A one-state self-loop where the observation is continuously true. -/
def recurringSingletonObjective : TemporalObjective Unit Unit where
  lts.trans _ _ _ := True
  observed := Set.univ
  formula := TemporalObjective.alwaysEventuallyObserved ()
  fixedPointsPositive := TemporalObjective.alwaysEventuallyObserved_positive ()

def recurringSingletonPresentation :
    FinitePresentation recurringSingletonObjective where
  model.system.edge _ _ _ := true
  model.holds _ _ := true
  transition_correct _ _ _ := by simp [recurringSingletonObjective]
  observation_correct _ := by simp [recurringSingletonObjective]

theorem recurringSingleton_denotes :
    (evaluationProgram recurringSingletonObjective).Denotes
      recurringSingletonPresentation.model () := by
  rw [evaluationProgram_denotes_iff]
  refine ⟨Set.univ, by simp, ?_⟩
  intro state _
  constructor
  · intro candidate preFixed
    apply preFixed state
    left
    simp [recurringSingletonObjective, TemporalObjective.alwaysEventuallyObserved,
      satisfies, Env.extend]
  · intro target _
    simp [satisfies, Env.extend]

abbrev recurringProgram : Program Unit Unit :=
  evaluationProgram recurringSingletonObjective

theorem recurringProgram_nodes_length : recurringProgram.nodes.length = 9 := by
  rw [Program.nodes_length]
  decide

def recurringPosition (address : Fin 9) :
    Position Unit Unit Unit recurringProgram :=
  ⟨(), Fin.cast recurringProgram_nodes_length.symm address, true⟩

def recurringStrategy :
    Mettapedia.GSLT.LanguageDef.CertificateGSLT.Parity.Strategy
      (Position Unit Unit Unit recurringProgram) where
  active position := position.polarity &&
    [0, 1, 2, 3, 4, 7, 8].contains position.address.val
  next position :=
    if position.address.val = 0 then recurringPosition 1
    else if position.address.val = 2 then recurringPosition 3
    else if position.address.val = 3 then recurringPosition 4
    else if position.address.val = 4 then recurringPosition 4
    else if position.address.val = 8 then recurringPosition 0
    else position

def recurringMeasure :
    Mettapedia.GSLT.LanguageDef.CertificateGSLT.Parity.ProgressMeasure
      (recurringProgram.game recurringSingletonPresentation.model) where
  rank _ position :=
    if [0, 1, 2, 7, 8].contains position.address.val then 1 else 0

noncomputable def recurringAutomaton :
    WeightedParityAutomaton ℝ≥0∞ (Position Unit Unit Unit recurringProgram) :=
  WeightedParityAutomaton.uniform 1 one_mul mul_one
    (recurringProgram.game recurringSingletonPresentation.model)

def recurringCertificate :
    CyclicProgressCertificate recurringAutomaton recurringStrategy
      (recurringPosition 0) where
  measure := recurringMeasure
  accepted := by decide

/-- The real nested objective satisfies the exact controlled-graph condition
characterized by the generic parity authority. -/
theorem recurringStrategy_noOddThresholdReturn :
    Mettapedia.GSLT.LanguageDef.CertificateGSLT.Parity.ProgressMeasure.NoOddThresholdReturn
      recurringAutomaton.game recurringStrategy := by
  open Mettapedia.GSLT.LanguageDef.CertificateGSLT.Parity in
    have valid := (ProgressMeasure.check_eq_true_iff recurringAutomaton.game
      recurringStrategy recurringMeasure (recurringPosition 0)).1
        recurringCertificate.accepted
    exact ProgressMeasure.globallyValid_noOddThresholdReturn
      recurringAutomaton.game recurringStrategy recurringMeasure valid.2

/-- Re-synthesize the real objective's certificate from its controlled graph,
showing that the generic constructor consumes the same liveness boundary. -/
noncomputable def recurringGeneratedCertificate :
    CyclicProgressCertificate recurringAutomaton recurringStrategy
      (recurringPosition 0) := by
  open Mettapedia.GSLT.LanguageDef.CertificateGSLT.Parity in
    have valid := (ProgressMeasure.check_eq_true_iff recurringAutomaton.game
      recurringStrategy recurringMeasure (recurringPosition 0)).1
        recurringCertificate.accepted
    exact CyclicProgressCertificate.ofNoOddThresholdReturn
      valid.1 recurringStrategy_noOddThresholdReturn

/-- The real `alwaysEventuallyObserved` formula yields a checked cyclic
strategy on its executable evaluation arena. -/
theorem recurringStrategy_winning :
    recurringStrategy.ParityWinning recurringAutomaton.game
      (recurringPosition 0) :=
  recurringCertificate.winning

theorem recurringGeneratedStrategy_winning :
    recurringStrategy.ParityWinning recurringAutomaton.game
      (recurringPosition 0) :=
  recurringGeneratedCertificate.winning

end TemporalObjective

end Mettapedia.Languages.MeTTa.Prime.TypedScheduler
