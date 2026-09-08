import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteBiformTheory
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCPass

/-!
# The lowered hot executor as a biform theory

A complete lowered hot run is a chain of StructuredC invocations of the
generated hot body from the loaded request to the loaded halted state.  Its
meaning is the hot specification sentence, and the meaning is sound because
every invocation reflects to an executor step, so the chain reflects to an
executor run whose terminal observation is the executor's denotation.
Loading executor runs is a biform route from the executor to this lowering,
compatible and unique with its data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCBiformTheory

open _root_.CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.ProofRelevant
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.BiformTheory
open Mettapedia.GSLT.LanguageDef.IRRunView
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.CallGuardNativeKernel
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControl
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteBiformTheory
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCTotalRealization
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCPass

/-! ## Invocations reflect to executor steps -/

theorem structuredCStep_of_executeStep {source target : ExecuteControl}
    (step : executeStep? source = some target) :
    hotStructuredCRuns.Step (runControl source) (runControl target) :=
  (strategyRunView_step_iff_strategy_of_equiv_eq hotStructuredCIR structuredCProtocol 1 runBudget
    (fun equal => (structuredCEquiv_iff _ _).1 equal) _ _).2 (strategyRun_of_executeStep step)

theorem executeStep_of_structuredCStep {source : ExecuteControl} {exit : Pattern}
    (step : hotStructuredCRuns.Step (runControl source) exit) :
    ∃ target, executeStep? source = some target ∧ exit = runControl target :=
  executeStep_of_strategyRun
    ((strategyRunView_step_iff_strategy_of_equiv_eq hotStructuredCIR structuredCProtocol 1 runBudget
      (fun equal => (structuredCEquiv_iff _ _).1 equal) _ _).1 step)

theorem structuredCMultiStep_of_executeMultiStep :
    ∀ {source target : executeGSLT.Term}, executeGSLT.MultiStep source target →
      hotStructuredCRuns.MultiStep (runControl source) (runControl target)
  | _, _, .refl _ => .refl _
  | _, _, .step one rest =>
      .step (structuredCStep_of_executeStep one) (structuredCMultiStep_of_executeMultiStep rest)

theorem executeMultiStep_of_structuredCMultiStep' :
    ∀ {start final : hotStructuredCRuns.Term}, hotStructuredCRuns.MultiStep start final →
      ∀ source : ExecuteControl, start = runControl source →
        ∃ target, executeGSLT.MultiStep source target ∧ final = runControl target
  | _, _, .refl _, source, equal => ⟨source, .refl _, equal⟩
  | _, _, .step one rest, source, equal => by
      subst equal
      obtain ⟨middle, step, middleEq⟩ := executeStep_of_structuredCStep one
      obtain ⟨target, run, targetEq⟩ :=
        executeMultiStep_of_structuredCMultiStep' rest middle middleEq
      exact ⟨target, .step step run, targetEq⟩

theorem executeMultiStep_of_structuredCMultiStep {source : ExecuteControl} {final : Pattern}
    (run : hotStructuredCRuns.MultiStep (runControl source) final) :
    ∃ target, executeGSLT.MultiStep source target ∧ final = runControl target :=
  executeMultiStep_of_structuredCMultiStep' run source rfl

theorem runControl_injective {left right : ExecuteControl}
    (equal : runControl left = runControl right) : left = right := by
  have stored := congrArg storedControl? equal
  rw [storedControl?_runControl, storedControl?_runControl] at stored
  exact Option.some.inj stored

/-! ## The lowered algorithm -/

/-- A complete lowered hot run, retaining its data. -/
structure LoweredRunEvidence (source target : Pattern) : Type where
  owned : OwnedSnapshot
  call : Call
  family : CompiledGuardFamily
  observation : ControlObservation
  source_eq : source = runControl (.request owned call (.compiled family))
  target_eq : target = runControl (.halted observation)
  run : hotStructuredCRuns.MultiStep source target

def loweredRunTheory : GSLT where
  Term := Pattern
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

/-- The meaning of a lowered run is the hot specification sentence. -/
def loweredMeaning (event : loweredRuns.Event) : Sentence :=
  ⟨event.evidence.owned, event.evidence.call, event.evidence.family,
    event.evidence.observation.outcome⟩

/-- The lowered hot executor as a biform theory over the hot specification
node. -/
def loweredBiform : BiformTheory.{0, 0, 0, 0} hotInstitution where
  logical := hotNode
  algorithm := loweredRuns
  meaning := loweredMeaning
  meaning_sound := by
    intro event
    obtain ⟨source, target, owned, call, family, observation, sourceEq, targetEq, run⟩ := event
    subst sourceEq
    subst targetEq
    obtain ⟨halted, executeRun, loaded⟩ := executeMultiStep_of_structuredCMultiStep run
    have haltedEq : halted = .halted observation := runControl_injective loaded.symm
    subst haltedEq
    have terminal := executeGSLT_terminal_exact owned call (.compiled family) observation executeRun
    show Sentence.Holds ⟨owned, call, family, observation.outcome⟩
    rw [terminal]
    exact executed_outcome_holds owned call family

/-! ## The route from the executor -/

/-- Loading executor states is a proof-relevant translation of run
algorithms. -/
noncomputable def loadRuns : Translation runs loweredRuns where
  mapTerm := runControl
  mapEquiv equal := congrArg runControl equal
  mapEvidence evidence :=
    { owned := evidence.owned
      call := evidence.call
      family := evidence.family
      observation := evidence.observation
      source_eq := congrArg runControl evidence.source_eq
      target_eq := congrArg runControl evidence.target_eq
      run := structuredCMultiStep_of_executeMultiStep evidence.run }
  liftEvidence := by
    intro source final evidence
    obtain ⟨owned, call, family, observation, sourceEq, targetEq, run⟩ := evidence
    obtain ⟨target, executeRun, finalEq⟩ :=
      Classical.indefiniteDescription _ (executeMultiStep_of_structuredCMultiStep run)
    refine ⟨target, ⟨owned, call, family, observation, runControl_injective sourceEq, ?_,
      executeRun⟩, ⟨⟨finalEq.symm⟩⟩⟩
    exact runControl_injective (finalEq.symm.trans targetEq)

/-- The biform route from the executor to its lowering. -/
noncomputable def loadRoute : Hom executorBiform loweredBiform where
  logical := PiInstitution.TheoryHom.identity hotNode
  operational := loadRuns
  meaning_natural _ := rfl

theorem loadRoute_compatible :
    Compatible (routePair loadRoute) ∧
      ∀ route : Hom executorBiform loweredBiform,
        routePair route = routePair loadRoute → route = loadRoute := by
  refine ⟨jointProjection_map_compatible loadRoute, fun route equal => ?_⟩
  exact Hom.ext_data (congrArg Prod.fst equal) (congrArg Prod.snd equal)

#print axioms loweredBiform
#print axioms loadRoute_compatible

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCBiformTheory
