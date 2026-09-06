import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardBiformTheory
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteOperational
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardToStructuredCSemantics

/-!
# The hot call-guard executor as a biform theory

The hot specification has one kind of sentence: for a family valid at a
snapshot and matching a call, executing the call installs exactly the
successful declarations.  Three algorithms decide it, with the same meaning
assignment and all sound: complete runs of the executor, complete runs of
the executor representation on encoded states, and complete runs of the
lowered StructuredC execute target.  The route from the executor to its
representation is the encoding, and it commutes with the meaning.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteBiformTheory

open _root_.CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.ProofRelevant
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.BiformTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.CallGuardNativeKernel
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControl
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardToStructuredCSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardBiformTheory

/-! ## The logical node: the hot specification -/

/-- A sentence of the hot specification: executing this call under this
compiled family produces this outcome. -/
structure Sentence where
  owned : OwnedSnapshot
  call : Call
  family : CompiledGuardFamily
  outcome : GuardExecution

/-- A sentence holds when, for a family valid at the snapshot and matching
the call, the outcome installs exactly the successful declarations. -/
def Sentence.Holds (sentence : Sentence) : Prop :=
  sentence.family.ValidFor sentence.owned → sentence.family.MatchesCall sentence.call →
    sentence.outcome = .executed (successfulDeclarations ⟨sentence.owned.snapshot, sentence.call⟩)

def hotInstitution : PiInstitution.{0, 0, 0} (Discrete Unit) where
  sentence := (Functor.const (Discrete Unit)).obj Sentence
  consequence _ := ClosureOperator.id _
  translation := by
    intro _ _ _ premises
    exact subset_rfl

def hotNode : PiInstitution.TheoryObject hotInstitution where
  signature := ⟨()⟩
  theory := ⟨{ sentence | sentence.Holds }, rfl⟩

theorem mem_hotNode_iff (sentence : Sentence) : sentence ∈ hotNode.theory.1 ↔ sentence.Holds :=
  Iff.rfl

/-- The reference outcome of a run is the executor's denotation. -/
theorem executed_outcome_holds (owned : OwnedSnapshot) (call : Call)
    (family : CompiledGuardFamily) :
    Sentence.Holds ⟨owned, call, family, (executeControl owned call (.compiled family)).outcome⟩ :=
  fun valid requestMatches => valid_execution_successfulDeclarations_exact valid requestMatches

/-! ## Complete executor runs -/

structure RunEvidence (source target : ExecuteControl) : Type where
  owned : OwnedSnapshot
  call : Call
  family : CompiledGuardFamily
  observation : ControlObservation
  source_eq : source = .request owned call (.compiled family)
  target_eq : target = .halted observation
  run : executeGSLT.MultiStep source target

def runTheory : GSLT where
  Term := ExecuteControl
  equations := ⟨Eq, eq_equivalence⟩
  rewrites source target := Nonempty (RunEvidence source target)
  rewrites_resp_left := by
    intro source source' target equal run
    cases equal
    exact ⟨target, run, rfl⟩
  rewrites_resp_right := by
    intro source target target' run equal
    cases equal
    exact run

def runs : ProofRelevantGSLT where
  theory := runTheory
  steps := ⟨RunEvidence, fun _ _ => Iff.rfl⟩

def meaning (event : runs.Event) : Sentence :=
  ⟨event.evidence.owned, event.evidence.call, event.evidence.family,
    event.evidence.observation.outcome⟩

theorem meaning_sound : MeaningSound hotInstitution hotNode runs meaning := by
  intro event
  obtain ⟨source, target, owned, call, family, observation, sourceEq, targetEq, run⟩ := event
  subst sourceEq
  subst targetEq
  have terminal := executeGSLT_terminal_exact owned call (.compiled family) observation run
  show Sentence.Holds ⟨owned, call, family, observation.outcome⟩
  rw [terminal]
  exact executed_outcome_holds owned call family

/-- The executor as a biform theory over the hot specification. -/
def executorBiform : BiformTheory.{0, 0, 0, 0} hotInstitution where
  logical := hotNode
  algorithm := runs
  meaning := meaning
  meaning_sound := meaning_sound

/-! ## Complete runs of the executor representation -/

theorem irStep_of_executeStep {source target : ExecuteControl}
    (step : executeStep? source = some target) :
    executeIR.semantics.Step (encodeExecuteControl source) (encodeExecuteControl target) :=
  (executeIR_step_iff _ _).2 ⟨target, step, rfl⟩

theorem irMultiStep_of_executeMultiStep :
    ∀ {source target : executeGSLT.Term}, executeGSLT.MultiStep source target →
      executeIR.semantics.MultiStep (encodeExecuteControl source) (encodeExecuteControl target)
  | _, _, .refl _ => .refl _
  | _, _, .step one rest => .step (irStep_of_executeStep one) (irMultiStep_of_executeMultiStep rest)

theorem executeMultiStep_of_irMultiStep' :
    ∀ {start wire : executeIR.semantics.Term}, executeIR.semantics.MultiStep start wire →
      ∀ source : ExecuteControl, start = encodeExecuteControl source →
        ∃ target, executeGSLT.MultiStep source target ∧ wire = encodeExecuteControl target
  | _, _, .refl _, source, equal => ⟨source, .refl _, equal⟩
  | _, _, .step one rest, source, equal => by
      subst equal
      obtain ⟨middle, step, middleEq⟩ := (executeIR_step_iff source _).1 one
      obtain ⟨target, run, targetEq⟩ := executeMultiStep_of_irMultiStep' rest middle middleEq
      exact ⟨target, .step step run, targetEq⟩

theorem executeMultiStep_of_irMultiStep {source : ExecuteControl} {wire : Pattern}
    (run : executeIR.semantics.MultiStep (encodeExecuteControl source) wire) :
    ∃ target, executeGSLT.MultiStep source target ∧ wire = encodeExecuteControl target :=
  executeMultiStep_of_irMultiStep' run source rfl

structure IRRunEvidence (source target : Pattern) : Type where
  owned : OwnedSnapshot
  call : Call
  family : CompiledGuardFamily
  observation : ControlObservation
  source_eq : source = encodeExecuteControl (.request owned call (.compiled family))
  target_eq : target = encodeExecuteControl (.halted observation)
  run : executeIR.semantics.MultiStep source target

def irRunTheory : GSLT where
  Term := Pattern
  equations := ⟨Eq, eq_equivalence⟩
  rewrites source target := Nonempty (IRRunEvidence source target)
  rewrites_resp_left := by
    intro source source' target equal run
    cases equal
    exact ⟨target, run, rfl⟩
  rewrites_resp_right := by
    intro source target target' run equal
    cases equal
    exact run

def irRuns : ProofRelevantGSLT where
  theory := irRunTheory
  steps := ⟨IRRunEvidence, fun _ _ => Iff.rfl⟩

def irMeaning (event : irRuns.Event) : Sentence :=
  ⟨event.evidence.owned, event.evidence.call, event.evidence.family,
    event.evidence.observation.outcome⟩

/-- The executor representation as a biform theory over the same node. -/
def irBiform : BiformTheory.{0, 0, 0, 0} hotInstitution where
  logical := hotNode
  algorithm := irRuns
  meaning := irMeaning
  meaning_sound := by
    intro event
    obtain ⟨source, target, owned, call, family, observation, sourceEq, targetEq, run⟩ := event
    subst sourceEq
    subst targetEq
    obtain ⟨halted, machineRun, encoded⟩ := executeMultiStep_of_irMultiStep run
    have haltedEq : halted = .halted observation := encodeExecuteControl_injective encoded.symm
    subst haltedEq
    have terminal := executeGSLT_terminal_exact owned call (.compiled family) observation machineRun
    show Sentence.Holds ⟨owned, call, family, observation.outcome⟩
    rw [terminal]
    exact executed_outcome_holds owned call family

/-- Encoding executor states is a proof-relevant translation of run
algorithms. -/
noncomputable def encodeRuns : Translation runs irRuns where
  mapTerm := encodeExecuteControl
  mapEquiv equal := congrArg encodeExecuteControl equal
  mapEvidence evidence :=
    { owned := evidence.owned
      call := evidence.call
      family := evidence.family
      observation := evidence.observation
      source_eq := congrArg encodeExecuteControl evidence.source_eq
      target_eq := congrArg encodeExecuteControl evidence.target_eq
      run := irMultiStep_of_executeMultiStep evidence.run }
  liftEvidence := by
    intro source wire evidence
    obtain ⟨owned, call, family, observation, sourceEq, targetEq, run⟩ := evidence
    obtain ⟨target, machineRun, wireEq⟩ :=
      Classical.indefiniteDescription _ (executeMultiStep_of_irMultiStep run)
    refine ⟨target, ⟨owned, call, family, observation,
      encodeExecuteControl_injective sourceEq, ?_, machineRun⟩, ⟨⟨wireEq.symm⟩⟩⟩
    exact encodeExecuteControl_injective (wireEq.symm.trans targetEq)

/-- The biform route from the executor to its representation. -/
noncomputable def encodeRoute : Hom executorBiform irBiform where
  logical := PiInstitution.TheoryHom.identity hotNode
  operational := encodeRuns
  meaning_natural _ := rfl

theorem encodeRoute_compatible :
    Compatible (routePair encodeRoute) ∧
      ∀ route : Hom executorBiform irBiform,
        routePair route = routePair encodeRoute → route = encodeRoute := by
  refine ⟨jointProjection_map_compatible encodeRoute, fun route equal => ?_⟩
  exact Hom.ext_data (congrArg Prod.fst equal) (congrArg Prod.snd equal)

/-! ## Complete runs of the lowered execute target -/

/-- A complete run of the lowered StructuredC execute target within its
budget. -/
structure LoweredRunEvidence (source target : LoweredExecuteTargetState) : Type where
  owned : OwnedSnapshot
  call : Call
  family : CompiledGuardFamily
  outcome : GuardExecution
  events : List ControlEvent
  source_eq : source = loweredExecuteTargetStart owned call (.compiled family)
  target_eq : target = .halted outcome events
  run : runLoweredExecuteTarget (loweredExecuteTargetBudget owned call (.compiled family))
    source = target

def loweredRunTheory : GSLT where
  Term := LoweredExecuteTargetState
  equations := ⟨Eq, eq_equivalence⟩
  rewrites source target := Nonempty (LoweredRunEvidence source target)
  rewrites_resp_left := by
    intro source source' target equal run
    cases equal
    exact ⟨target, run, rfl⟩
  rewrites_resp_right := by
    intro source target target' run equal
    cases equal
    exact run

def loweredRuns : ProofRelevantGSLT where
  theory := loweredRunTheory
  steps := ⟨LoweredRunEvidence, fun _ _ => Iff.rfl⟩

def loweredMeaning (event : loweredRuns.Event) : Sentence :=
  ⟨event.evidence.owned, event.evidence.call, event.evidence.family, event.evidence.outcome⟩

/-- The lowered execute target as a biform theory over the same node: its
meaning is sound by the lowered execution theorem. -/
def loweredBiform : BiformTheory.{0, 0, 0, 0} hotInstitution where
  logical := hotNode
  algorithm := loweredRuns
  meaning := loweredMeaning
  meaning_sound := by
    intro event
    obtain ⟨source, target, owned, call, family, outcome, events, sourceEq, targetEq, run⟩ :=
      event
    subst sourceEq
    subst targetEq
    show Sentence.Holds ⟨owned, call, family, outcome⟩
    intro valid requestMatches
    have lowered := lowered_valid_execution_successfulDeclarations_exact valid requestMatches
    rw [run] at lowered
    exact (LoweredExecuteTargetState.halted.inj lowered).1

/-! ## Negative control -/

/-- Declare every executor run a fallback. -/
def fallbackMeaning (event : runs.Event) : Sentence :=
  ⟨event.evidence.owned, event.evidence.call, event.evidence.family, .fallback .outsideFragment⟩

def emptyOwned : OwnedSnapshot := ⟨⟨0⟩, ⟨0, [], [], []⟩⟩

def emptyCall : Call := ⟨"f", [], [], .atom "y"⟩

def emptyFamily : CompiledGuardFamily := ⟨⟨0⟩, 0, "f", 0, []⟩

/-- The two-step run of the empty family: request, then finished plans. -/
def emptyRun : RunEvidence (.request emptyOwned emptyCall (.compiled emptyFamily))
    (.halted ⟨.executed [], []⟩) where
  owned := emptyOwned
  call := emptyCall
  family := emptyFamily
  observation := ⟨.executed [], []⟩
  source_eq := rfl
  target_eq := rfl
  run := .step rfl (.step rfl (.refl _))

theorem emptyFamily_valid : emptyFamily.ValidFor emptyOwned := by
  decide

theorem emptyFamily_matches : emptyFamily.MatchesCall emptyCall := by
  decide

/-- The altered assignment is not meaning sound: the empty family executes,
it does not fall back. -/
theorem fallbackMeaning_not_sound :
    ¬ MeaningSound hotInstitution hotNode runs fallbackMeaning := by
  intro sound
  have declined := sound ⟨_, _, emptyRun⟩ emptyFamily_valid emptyFamily_matches
  cases declined

#print axioms executorBiform
#print axioms irBiform
#print axioms encodeRoute
#print axioms encodeRoute_compatible
#print axioms loweredBiform
#print axioms fallbackMeaning_not_sound

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteBiformTheory
