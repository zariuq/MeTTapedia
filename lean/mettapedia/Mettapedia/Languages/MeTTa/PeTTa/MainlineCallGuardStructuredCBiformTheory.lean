import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardBiformTheory
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardStructuredCPass

/-!
# The lowered call-guard compiler as a biform theory

A complete lowered run is a chain of StructuredC invocations from the loaded
start control to the loaded halted control.  Its meaning is the same
specification sentence the compiler machine decides, and the meaning is
sound because every lowered run reflects, invocation by invocation, to a
machine run.

Two biform routes land here: loading a machine run, and loading a cold run
through the state loader of the pass.  Both are compatible, both are the
unique routes with their data, and the two paths from the compiler agree on
every term and on the data of every event, which is all the meaning reads.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardStructuredCBiformTheory

open _root_.CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.ProofRelevant
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.BiformTheory
open Mettapedia.GSLT.LanguageDef.IRRunView
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileCodec
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardMatchMachinePass
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardBiformTheory
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardStructuredCPass

/-! ## Invocations reflect to compiler steps -/

theorem structuredCStep_of_compileStep {source target : CompileLanguageControl}
    (step : compileLanguageStep? source = some target) :
    structuredCRuns.Step (runControl source) (runControl target) :=
  (strategyRunView_step_iff_strategy_of_equiv_eq structuredCIR structuredCProtocol 1 64
    (fun equal => (structuredCEquiv_iff _ _).1 equal) _ _).2 (strategyRun_of_compileStep step)

theorem compileStep_of_structuredCStep {source : CompileLanguageControl} {exit : Pattern}
    (step : structuredCRuns.Step (runControl source) exit) :
    ∃ target, compileLanguageStep? source = some target ∧ exit = runControl target :=
  compileStep_of_strategyRun
    ((strategyRunView_step_iff_strategy_of_equiv_eq structuredCIR structuredCProtocol 1 64
      (fun equal => (structuredCEquiv_iff _ _).1 equal) _ _).1 step)

theorem structuredCMultiStep_of_machineMultiStep :
    ∀ {source target : compileLanguageGSLT.Term},
      compileLanguageGSLT.MultiStep source target →
        structuredCRuns.MultiStep (runControl source) (runControl target)
  | _, _, .refl _ => .refl _
  | _, _, .step one rest =>
      .step (structuredCStep_of_compileStep one) (structuredCMultiStep_of_machineMultiStep rest)

theorem machineMultiStep_of_structuredCMultiStep' :
    ∀ {start final : structuredCRuns.Term}, structuredCRuns.MultiStep start final →
      ∀ source : CompileLanguageControl, start = runControl source →
        ∃ target, compileLanguageGSLT.MultiStep source target ∧ final = runControl target
  | _, _, .refl _, source, equal => ⟨source, .refl _, equal⟩
  | _, _, .step one rest, source, equal => by
      subst equal
      obtain ⟨middle, step, middleEq⟩ := compileStep_of_structuredCStep one
      obtain ⟨target, run, targetEq⟩ :=
        machineMultiStep_of_structuredCMultiStep' rest middle middleEq
      exact ⟨target, .step step run, targetEq⟩

theorem machineMultiStep_of_structuredCMultiStep {source : CompileLanguageControl}
    {final : Pattern} (run : structuredCRuns.MultiStep (runControl source) final) :
    ∃ target, compileLanguageGSLT.MultiStep source target ∧ final = runControl target :=
  machineMultiStep_of_structuredCMultiStep' run source rfl

theorem runControl_injective {left right : CompileLanguageControl}
    (equal : runControl left = runControl right) : left = right := by
  have stored := congrArg storedControl? equal
  rw [storedControl?_runControl, storedControl?_runControl] at stored
  exact Option.some.inj stored

theorem runControl_ne_inadmissible (control : CompileLanguageControl) :
    runControl control ≠ inadmissibleConfig := by
  intro equal
  have stored := congrArg storedControl? equal
  rw [storedControl?_runControl] at stored
  cases stored

/-! ## The lowered algorithm -/

/-- A complete lowered run, retaining its data. -/
structure LoweredRunEvidence (source target : Pattern) : Type where
  owned : OwnedSnapshot
  head : String
  arity : Nat
  result : CompilationResult
  source_eq : source = runControl (compileLanguageStart owned head arity)
  target_eq : target = runControl (.halted result)
  run : structuredCRuns.MultiStep source target

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

/-- The meaning of a lowered run is the same specification sentence. -/
def loweredMeaning (event : loweredRuns.Event) : Sentence :=
  ⟨event.evidence.owned, event.evidence.head, event.evidence.arity, event.evidence.result⟩

/-- The lowered compiler as a biform theory over the specification node. -/
def loweredBiform : BiformTheory.{0, 0, 0, 0} specificationInstitution where
  logical := specificationNode
  algorithm := loweredRuns
  meaning := loweredMeaning
  meaning_sound := by
    intro event
    obtain ⟨source, target, owned, head, arity, result, sourceEq, targetEq, run⟩ := event
    subst sourceEq
    subst targetEq
    obtain ⟨halted, machineRun, loaded⟩ := machineMultiStep_of_structuredCMultiStep run
    have haltedEq : halted = .halted result := runControl_injective loaded.symm
    subst haltedEq
    exact (run_halts_with_specification machineRun).symm

/-! ## The route from the compiler -/

/-- Loading control states is a proof-relevant translation of run
algorithms. -/
noncomputable def loadRuns : Translation runs loweredRuns where
  mapTerm := runControl
  mapEquiv equal := congrArg runControl equal
  mapEvidence evidence :=
    { owned := evidence.owned
      head := evidence.head
      arity := evidence.arity
      result := evidence.result
      source_eq := congrArg runControl evidence.source_eq
      target_eq := congrArg runControl evidence.target_eq
      run := structuredCMultiStep_of_machineMultiStep evidence.run }
  liftEvidence := by
    intro source final evidence
    obtain ⟨owned, head, arity, result, sourceEq, targetEq, run⟩ := evidence
    obtain ⟨target, machineRun, finalEq⟩ :=
      Classical.indefiniteDescription _ (machineMultiStep_of_structuredCMultiStep run)
    refine ⟨target, ⟨owned, head, arity, result, runControl_injective sourceEq, ?_, machineRun⟩,
      ⟨⟨finalEq.symm⟩⟩⟩
    exact runControl_injective (finalEq.symm.trans targetEq)

/-- The biform route from the compiler to its lowering: the identity on the
specification, loading on runs, and the commuting meaning square. -/
noncomputable def loadRoute : Hom compilerBiform loweredBiform where
  logical := PiInstitution.TheoryHom.identity specificationNode
  operational := loadRuns
  meaning_natural _ := rfl

theorem loadRoute_compatible :
    Compatible (routePair loadRoute) ∧
      ∀ route : Hom compilerBiform loweredBiform,
        routePair route = routePair loadRoute → route = loadRoute := by
  refine ⟨jointProjection_map_compatible loadRoute, fun route equal => ?_⟩
  exact Hom.ext_data (congrArg Prod.fst equal) (congrArg Prod.snd equal)

/-! ## The route from the cold language, through the state loader -/

/-- A cold run from an encoded control is a lowered run of the loaded
controls. -/
theorem loweredMultiStep_of_coldMultiStep {source : CompileLanguageControl} {wire : Pattern}
    (run : coldIR.semantics.MultiStep (encodeCompileLanguageControl source) wire) :
    ∃ target, wire = encodeCompileLanguageControl target ∧
      structuredCRuns.MultiStep (runControl source) (runControl target) := by
  obtain ⟨target, machineRun, wireEq⟩ := machineMultiStep_of_coldMultiStep run
  exact ⟨target, wireEq, structuredCMultiStep_of_machineMultiStep machineRun⟩

/-- The state loader of the pass as a proof-relevant translation of run
algorithms. -/
noncomputable def loadColdRuns : Translation coldRuns loweredRuns where
  mapTerm := loadState
  mapEquiv equal := congrArg loadState equal
  mapEvidence := by
    intro sourceTerm sourceTarget evidence
    obtain ⟨owned, head, arity, result, sourceEq, targetEq, run⟩ := evidence
    subst sourceEq
    subst targetEq
    refine ⟨owned, head, arity, result, loadState_encode _, loadState_encode _, ?_⟩
    rw [loadState_encode, loadState_encode]
    obtain ⟨target, encoded, lowered⟩ := loweredMultiStep_of_coldMultiStep run
    have targetEq : target = .halted result :=
      encodeCompileLanguageControl_injective encoded.symm
    subst targetEq
    exact lowered
  liftEvidence := by
    intro source final evidence
    obtain ⟨owned, head, arity, result, sourceEq, targetEq, run⟩ := evidence
    by_cases image : ∃ control, encodeCompileLanguageControl control = source
    · obtain ⟨control, controlEq⟩ := Classical.indefiniteDescription _ image
      subst controlEq
      rw [loadState_encode] at sourceEq run
      have startEq : control = compileLanguageStart owned head arity :=
        runControl_injective sourceEq
      subst startEq
      obtain ⟨target, machineRun, finalEq⟩ :=
        Classical.indefiniteDescription _ (machineMultiStep_of_structuredCMultiStep run)
      have haltedEq : target = .halted result :=
        runControl_injective (finalEq.symm.trans targetEq)
      subst haltedEq
      refine ⟨encodeCompileLanguageControl (.halted result),
        ⟨owned, head, arity, result, rfl, rfl, coldMultiStep_of_machineMultiStep machineRun⟩,
        ⟨⟨?_⟩⟩⟩
      rw [loadState_encode]
      exact finalEq.symm
    · exfalso
      rw [loadState_of_noImage image] at sourceEq
      exact runControl_ne_inadmissible _ sourceEq.symm

/-- The biform route from the cold language to its lowering. -/
noncomputable def loadColdRoute : Hom coldBiform loweredBiform where
  logical := PiInstitution.TheoryHom.identity specificationNode
  operational := loadColdRuns
  meaning_natural := by
    intro event
    obtain ⟨source, target, owned, head, arity, result, sourceEq, targetEq, run⟩ := event
    subst sourceEq
    subst targetEq
    rfl

theorem loadColdRoute_compatible :
    Compatible (routePair loadColdRoute) ∧
      ∀ route : Hom coldBiform loweredBiform,
        routePair route = routePair loadColdRoute → route = loadColdRoute := by
  refine ⟨jointProjection_map_compatible loadColdRoute, fun route equal => ?_⟩
  exact Hom.ext_data (congrArg Prod.fst equal) (congrArg Prod.snd equal)

/-! ## The two paths from the compiler agree -/

/-- Encoding then loading is loading, on every term. -/
theorem encode_then_load_mapTerm :
    (Hom.comp encodeRoute loadColdRoute).operational.mapTerm = loadRoute.operational.mapTerm := by
  funext control
  show loadState (encodeCompileLanguageControl control) = runControl control
  exact loadState_encode control

/-- Encoding then loading is loading, on the data of every event: the
endpoints and the retained snapshot, head, arity, and result. -/
theorem encode_then_load_mapEvent (event : runs.Event) :
    ((Hom.comp encodeRoute loadColdRoute).operational.mapEvent event).source =
        (loadRoute.operational.mapEvent event).source ∧
      ((Hom.comp encodeRoute loadColdRoute).operational.mapEvent event).target =
        (loadRoute.operational.mapEvent event).target ∧
      loweredMeaning ((Hom.comp encodeRoute loadColdRoute).operational.mapEvent event) =
        loweredMeaning (loadRoute.operational.mapEvent event) := by
  obtain ⟨source, target, owned, head, arity, result, sourceEq, targetEq, run⟩ := event
  subst sourceEq
  subst targetEq
  refine ⟨?_, ?_, rfl⟩
  · exact loadState_encode (compileLanguageStart owned head arity)
  · exact loadState_encode (.halted result)

/-- Both paths read the compiler's meaning unchanged. -/
theorem encode_then_load_meaning (event : runs.Event) :
    loweredMeaning ((Hom.comp encodeRoute loadColdRoute).operational.mapEvent event) =
      meaning event := by
  obtain ⟨source, target, owned, head, arity, result, sourceEq, targetEq, run⟩ := event
  subst sourceEq
  subst targetEq
  rfl

/-! ## Negative control: the declined assignment stays unsound after lowering -/

/-- Declare every lowered run declined. -/
def declinedLoweredMeaning (event : loweredRuns.Event) : Sentence :=
  ⟨event.evidence.owned, event.evidence.head, event.evidence.arity, .outsideFragment⟩

theorem declinedLoweredMeaning_not_sound :
    ¬ MeaningSound specificationInstitution specificationNode loweredRuns
      declinedLoweredMeaning := by
  intro sound
  have declined : compileGuards emptyOwned "f" 0 = .outsideFragment :=
    sound ⟨_, _, loadRuns.mapEvidence emptyRun⟩
  simp [compileGuards, compileRelevantGuards, emptyOwned] at declined

#print axioms loweredBiform
#print axioms loadRoute
#print axioms loadRoute_compatible
#print axioms loadColdRoute
#print axioms loadColdRoute_compatible
#print axioms encode_then_load_mapTerm
#print axioms declinedLoweredMeaning_not_sound

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardStructuredCBiformTheory
