import Mettapedia.OSLF.Framework.RhoContextualWorldModel

/-!
# A cue, a performer, and a world model of their interaction

The performer waits for a cue and then emits a note. A matching cue enables
the note; silence and an output on the wrong channel do not. These are closed
terms of the existing, declaration-derived rho calculus, checked by its
canonical stepper. They are an interaction fragment motivated by F1R3Score,
not an implementation of its pitches, durations, weighted clauses, or player.

Two boundaries are proved, not assumed:

* Individually inert processes can communicate when composed. Counting
  observations of individual components is not observing their composition.
* A world model that identifies all independently inert environments loses
  the ability to predict an agent's interaction with them.

An ensemble of alternative environments, queried by the performer, is a
genuine reading of the existing WM calculus. Moving a cue from the world
into the agent preserves the evidence after the query is transported.

The motivating score program is F1R3Score's `examples/call_response.score`:
https://github.com/F1R3FLY-io/F1R3Score
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoScoreWorldModel

open Mettapedia.OSLF.Framework.RhoContextualWorldModel
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusContextEncoding
open Mettapedia.OSLF.Framework.WMCalculusEncoding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.HennessyMilnerRho
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.HennessyMilnerInstance
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelContextAdequacy
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.GSLT.LanguageDef.ReflectionExtension

/-- The cue is an output on the quoted inert channel. -/
def cue : RhoProcess := outputPartner

/-- A note is an output on a different, structurally quoted channel. -/
def note : RhoProcess :=
  ⟨.apply "POutput" [.apply "NQuote" [cue.1], .apply "PZero" []],
    (rhoClosedTermWellSorted_process_iff _).mpr
      ⟨.output (.quote (.output (.quote .unit) .unit)) .unit, by decide⟩⟩

/-- An unrelated message on a third channel: neither a cue nor a note. -/
def wrongCue : RhoProcess :=
  ⟨.apply "POutput" [.apply "NQuote" [waitingInput.1], .apply "PZero" []],
    (rhoClosedTermWellSorted_process_iff _).mpr
      ⟨.output (.quote (.input (.quote .unit) .unit)) .unit, by decide⟩⟩

/-- `cue?(x).note!(0)`: the cue's payload is unused in this fragment. -/
def performer : RhoProcess :=
  ⟨.apply "PInput" [closedNilName.1, .lambda none note.1],
    (rhoClosedTermWellSorted_process_iff _).mpr
      ⟨.input (.quote .unit) (.output (.quote (.output (.quote .unit) .unit)) .unit),
        by decide⟩⟩

/-- Will one interaction of this performer with the environment emit the note? -/
def noteQuery : Query := ⟨performer, .exact note⟩

/-- Does the environment have any step when accompanied by the inert agent? -/
def enabledQuery : Query := ⟨closedNil, .any⟩

/-! ## Executable positive and negative controls -/

/-- A witness from the authored COMM rule, independent of a scheduler. -/
theorem performer_cue_step : rhoLanguageDefGSLT.Step (par performer cue) note := by
  let target : RhoProcess :=
    ⟨.collection .hashBag [note.1] none,
      (rhoClosedTermWellSorted_process_iff _).mpr
        ⟨.parallel (.cons (.output (.quote (.output (.quote .unit) .unit)) .unit) .nil),
          by decide⟩⟩
  have step : rhoRewriteSystem.Reduces (par performer cue) target := by
    have comm := RhoStep.comm (free := FreeSortContext.empty) (bound := [])
      closedNilName.1 note.1 (.apply "PZero" []) []
      (.output (.quote (.output (.quote .unit) .unit)) .unit) .unit
    change RhoStep (par performer cue).1 target.1
    simpa [target, par, performer, note, cue, outputPartner, closedNilName,
      semanticCommSubst, semanticSubstProc, semanticSubstName, semanticSubstNameMark,
      semanticNormalizeName, semanticNormalizeProc, semanticNormalizeProcList] using comm
  exact rhoLanguageDefGSLT.rewrites_resp_right
    (rhoRewriteSystem_reduces_to_gsltStep step) (canonicalize_parallel_singleton note.1)

theorem cue_enables_note : Answers noteQuery cue :=
  ⟨note, performer_cue_step, rfl⟩

theorem silence_does_not_enable_note : ¬ Answers noteQuery closedNil := by decide +kernel

/-- The wrong channel is not mistaken for the requested cue. The proof handles
both canonical orders, avoiding evaluation of the structural sorting codes. -/
theorem wrong_channel_does_not_enable_note : ¬ Answers noteQuery wrongCue := by
  have shape : canonicalize (par performer wrongCue).1 =
      collapseBag (sortPatterns [performer.1, wrongCue.1]) := rfl
  have orders := (List.perm_pair).mp (sortPatterns_perm [performer.1, wrongCue.1]).symm
  have noSuccessors : rewriteAt rhoRuleInterpretation rhoBasePremises rhoCalc 1
      (canonicalize (par performer wrongCue).1) = [] := by
    rw [shape]
    rcases orders with ordered | ordered <;> rw [ordered] <;> decide +kernel
  rintro ⟨target, step, _⟩
  exact no_step_of_successors_nil noSuccessors target step

theorem performer_alone_inert : ¬ CanObserve performer .any := by decide +kernel

theorem cue_alone_inert : ¬ CanObserve cue .any := by decide +kernel

theorem silence_inert : ¬ CanObserve closedNil .any := by decide +kernel

theorem performer_is_cues_world : CanObserve (par cue performer) (.exact note) :=
  (mutual_world performer cue (.exact note)).mp cue_enables_note

/-- Both components are inert in isolation, yet their interaction emits a note. -/
theorem interaction_creates_observation :
    ¬ CanObserve performer .any ∧ ¬ CanObserve cue .any ∧
      CanObserve (par performer cue) (.exact note) :=
  ⟨performer_alone_inert, cue_alone_inert, cue_enables_note⟩

/-! ## The epistemic reading and evidence revision -/

theorem cue_evidence : evidence {cue} noteQuery = ⟨1, 0⟩ :=
  evidence_singleton_yes cue noteQuery cue_enables_note

theorem silence_evidence : evidence {closedNil} noteQuery = ⟨0, 1⟩ :=
  evidence_singleton_no closedNil noteQuery silence_does_not_enable_note

/-- Pooling a successful and an unsuccessful environment test retains both
pieces of evidence. It does not run the two environments concurrently. -/
theorem revised_evidence :
    evidence ({cue} + {closedNil}) noteQuery = ⟨1, 1⟩ := by
  rw [evidence_add, cue_evidence, silence_evidence]
  apply BinaryEvidence.ext' <;> simp [BinaryEvidence.hplus_def]

noncomputable def scoreReading : WMReading State Query BinaryEvidence :=
  reading (fun name => if name = "cue" then {cue} else {closedNil}) (fun _ => noteQuery)

def pooledTest : WMTerm .evidence :=
  .extract (.revise (.state "cue") (.state "silence")) (.query "note")

def combinedTests : WMTerm .evidence :=
  .combine (.extract (.state "cue") (.query "note"))
    (.extract (.state "silence") (.query "note"))

/-- An actual WM-calculus rewrite of the situated score query. -/
theorem score_evidence_rewrite : WMStep pooledTest combinedTests :=
  .evidence_add (.state "cue") (.state "silence") (.query "note")

theorem pooledTest_denotes : scoreReading.denote pooledTest = ⟨1, 1⟩ := by
  change evidence ({cue} + {closedNil}) noteQuery = _
  exact revised_evidence

theorem combinedTests_denotes : scoreReading.denote combinedTests = ⟨1, 1⟩ := by
  have same := (reading_coreLaws
    (fun name => if name = "cue" then {cue} else {closedNil})
    (fun _ => noteQuery)).agree_of_step score_evidence_rewrite
  exact same.symm.trans pooledTest_denotes

/-- Adding the cue to a silent world and moving it into the query's agent
are two presentations of the same experiment. -/
theorem moving_cue_preserves_prediction :
    evidence (extendWorld cue {closedNil}) noteQuery =
      evidence {closedNil} (noteQuery.withPartner cue) :=
  evidence_extendWorld {closedNil} cue noteQuery

theorem extended_silence_evidence :
    evidence (extendWorld cue {closedNil}) noteQuery = ⟨1, 0⟩ := by
  change evidence (Multiset.map (fun environment => par environment cue) {closedNil}) noteQuery = _
  rw [Multiset.map_singleton]
  apply evidence_singleton_yes
  exact (answers_equiv noteQuery
    ((par_comm_equiv closedNil cue).trans (par_nil_equiv cue))).mpr cue_enables_note

/-! ## Counterexample to identifying parallel interaction with evidence addition -/

theorem composed_enabled : Answers enabledQuery (par performer cue) := by
  apply (canObserve_equiv
    ((par_comm_equiv closedNil (par performer cue)).trans (par_nil_equiv _)) .any).mpr
  exact ⟨note, performer_cue_step, trivial⟩

theorem isolated_performer_disabled : ¬ Answers enabledQuery performer := by decide +kernel

theorem isolated_cue_disabled : ¬ Answers enabledQuery cue := by decide +kernel

/-- An interacting pair has positive evidence where the separately sampled
components have none. Thus operational parallel composition cannot be
substituted for the additive revision of this evidence reading. -/
theorem parallel_evidence_not_additive :
    evidence {par performer cue} enabledQuery ≠
      evidence {performer} enabledQuery + evidence {cue} enabledQuery := by
  rw [evidence_singleton_yes _ _ composed_enabled,
    evidence_singleton_no _ _ isolated_performer_disabled,
    evidence_singleton_no _ _ isolated_cue_disabled]
  intro same
  have positive := congrArg BinaryEvidence.pos same
  simp [BinaryEvidence.hplus_def] at positive

/-! ## Counterexample to forgetting the environment's interaction affordances -/

/-- Looking only at autonomous reduction, the cue and silence are bisimilar:
both are stuck. That view omits interactions with an incoming agent. -/
theorem cue_reduction_bisimilar_silence :
    (rhoSystem PEmpty.{1} (fun atom => atom.elim)).Bisimilar cue closedNil := by
  refine ⟨fun first second => first = cue ∧ second = closedNil, ⟨?_, ?_, ?_⟩, rfl, rfl⟩
  · rintro _ _ ⟨rfl, rfl⟩ _ target step
    exact (cue_alone_inert ⟨target, step, trivial⟩).elim
  · rintro _ _ ⟨rfl, rfl⟩ _ target step
    exact (silence_inert ⟨target, step, trivial⟩).elim
  · rintro _ _ _ atom
    exact atom.elim

theorem interaction_evidence_separates_worlds :
    evidence {cue} noteQuery ≠ evidence {closedNil} noteQuery := by
  rw [cue_evidence, silence_evidence]
  intro same
  have positive := congrArg BinaryEvidence.pos same
  simp at positive

/-- No abstraction merging cue and silence can answer this situated query
exactly. This is a concrete obstruction to a context-insensitive world model. -/
theorem no_exact_prediction_after_forgetting {View : Type}
    (abstract : RhoProcess → View) (forgets : abstract cue = abstract closedNil) :
    ¬ ∃ predicts : View → Prop,
      ∀ environment, predicts (abstract environment) ↔ Answers noteQuery environment := by
  rintro ⟨predicts, exactPrediction⟩
  have predictsCue := (exactPrediction cue).mpr cue_enables_note
  rw [forgets] at predictsCue
  exact silence_does_not_enable_note ((exactPrediction closedNil).mp predictsCue)

end Mettapedia.OSLF.Framework.RhoScoreWorldModel
