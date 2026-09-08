import Mettapedia.GSLT.LanguageDef.OrderedMatchMachineAdequacy
import Mettapedia.GSLT.LanguageDef.IRRunView
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteFusedDecisionProgram

/-!
# The completed-call executor covered by the ordered-match machine

The executor language is a representation: its validated definition with the
relation environment its premises consult.  Its fused decision program,
translated leaf by leaf into the ordered-match machine's plans, is a program
of the machine representation.  One complete run of the machine on an
executor term, from the run state of that program to a result state, is one
step of the executor language, and every executor step is such a run.  The
identity on terms is therefore a semantic cover from the executor language
into the run view of the machine: the first hot pass, the pattern-matrix
decision tree with no rule scan.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteMatchMachinePass

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.IRPass
open Mettapedia.GSLT.LanguageDef.IRRunView
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.CallGuardNativeKernel
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControl
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecutePatternMatrixCompilation
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteFusedDecisionProgram

namespace Machine
export Mettapedia.GSLT.LanguageDef.OrderedMatchMachineLanguage
  (Program MachineState encodeState ir mapProgram toMachinePlan LanguageReaches
    languageReaches_of_reaches reaches_of_languageReaches languageReaches_mapProgram_iff
    language_isEquationFree)
end Machine

/-! ## The two representations -/

/-- The executor representation's step is the least-contextual step. -/
theorem executeStep_iff (source target : Pattern) :
    executeIR.semantics.Step source target ↔
      langReducesUsing relationEnv sourceLanguage source target := by
  change StepModuloEquations (engineBasePremises relationEnv) language source target ↔ _
  rw [stepModuloEquations_iff_step_of_no_generators language_isEquationFree]
  rfl

theorem executeEquiv_iff (left right : Pattern) :
    executeIR.semantics.Equiv left right ↔ left = right :=
  gsltModuloEquations_equiv_iff_eq_of_no_generators language_isEquationFree left right

/-- The ordered-match machine over the executor relation environment. -/
def machineIR : IRLanguage := Machine.ir relationEnv sourceLanguage

theorem machineEquiv_iff (left right : Pattern) :
    machineIR.semantics.Equiv left right ↔ left = right :=
  gsltModuloEquations_equiv_iff_eq_of_no_generators Machine.language_isEquationFree left right

/-- The fused executor decision program as a machine program. -/
def machineProgram : Machine.Program :=
  Machine.mapProgram (fun occurrence : SourceOccurrence => occurrence.val) Machine.toMachinePlan
    fusedProgram

/-- Result states of the machine. -/
def exit? : Pattern → Option Pattern
  | .apply "mm-done" [result] => some result
  | _ => none

theorem exit?_encodeState (state : Machine.MachineState) (result : Pattern) :
    exit? (Machine.encodeState state) = some result ↔ state = .done result := by
  cases state <;> simp [Machine.encodeState, exit?]

/-- Run the fused program on the term, starting with the term as the whole
cursor. -/
def protocol : RunProtocol where
  entry := fun source => Machine.encodeState (.run machineProgram source [source])
  exit := exit?

/-- One machine run as one step. -/
abbrev machineRuns : GSLT := runView machineIR protocol

theorem machineRuns_step_iff (source target : Pattern) :
    machineRuns.Step source target ↔ target ∈ fusedReducts 0 source := by
  rw [runView_step_iff_raw_of_equiv_eq machineIR protocol
    (fun equal => (machineEquiv_iff _ _).mp equal)]
  constructor
  · rintro ⟨final, run, exit⟩
    change Machine.LanguageReaches relationEnv sourceLanguage
      (Machine.encodeState (.run machineProgram source [source])) final at run
    obtain ⟨state, rfl, machineRun⟩ :=
      Machine.reaches_of_languageReaches relationEnv sourceLanguage run
    change exit? (Machine.encodeState state) = some target at exit
    rw [exit?_encodeState] at exit
    subst exit
    exact (Machine.languageReaches_mapProgram_iff relationEnv sourceLanguage fusedProgram
      (fun occurrence : SourceOccurrence => occurrence.val) source target).mp
      (Machine.languageReaches_of_reaches relationEnv sourceLanguage machineRun)
  · intro member
    refine ⟨Machine.encodeState (.done target), ?_, rfl⟩
    exact (Machine.languageReaches_mapProgram_iff relationEnv sourceLanguage fusedProgram
      (fun occurrence : SourceOccurrence => occurrence.val) source target).mpr member

/-! ## The pass -/

theorem machineRun_of_executeStep {source target : Pattern}
    (step : executeIR.semantics.Step source target) : machineRuns.Step source target := by
  rw [machineRuns_step_iff]
  obtain ⟨fuel, member⟩ := language_step_covered ((executeStep_iff source target).mp step)
  rw [← fusedReducts_eq_compiledReducts] at member
  exact member

theorem executeStep_of_machineRun {source target : Pattern}
    (run : machineRuns.Step source target) : executeIR.semantics.Step source target := by
  rw [machineRuns_step_iff] at run
  exact (executeStep_iff source target).mpr (fusedReducts_no_invention 0 run)

/-- The identity on terms is a semantic cover from the executor language
into the run view of the ordered-match machine. -/
def executeToMachinePass : SemanticCoveredTranslation executeIR.semantics machineRuns :=
  coverOfRuns executeIR machineIR protocol id
    (fun equal => (machineEquiv_iff _ _).mpr ((executeEquiv_iff _ _).mp equal))
    (fun step => machineRun_of_executeStep step)
    (fun run => ⟨_, executeStep_of_machineRun run, machineIR.semantics.equations.iseqv.refl _⟩)

@[simp] theorem executeToMachinePass_mapTerm : executeToMachinePass.mapTerm = id := rfl

/-! ## Canaries -/

/-- A plans state with nothing remaining halts executed, and the machine runs
to exactly that halt. -/
theorem positive_canary (snapshot : Snapshot) (call : Call) (accepted : List ArrowDeclaration)
    (events : List ControlEvent) :
    machineRuns.Step (encodeExecuteControl (.plans snapshot call [] accepted events))
      (encodeExecuteControl (.halted ⟨.executed accepted, events⟩)) := by
  rw [machineRuns_step_iff]
  apply List.mem_of_mem_head?
  rw [fused_first_eq_executeStep]
  rfl

/-- A halted state has no machine run. -/
theorem stuck_canary (observation : ControlObservation) (target : Pattern) :
    ¬ machineRuns.Step (encodeExecuteControl (.halted observation)) target := by
  rw [machineRuns_step_iff]
  intro member
  have first := fused_first_eq_executeStep (.halted observation)
  simp only [executeStep?, Option.map_none, List.head?_eq_none_iff] at first
  rw [first] at member
  simp at member

/-- The run view with one invented transition from a halted state to
itself. -/
def inventingRuns (observation : ControlObservation) : GSLT where
  Term := Pattern
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target =>
    machineRuns.Step source target ∨
      (source = encodeExecuteControl (.halted observation) ∧ target = source)
  rewrites_resp_left := by
    intro source source' target equal step
    subst equal
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst equal
    exact step

/-- One invented transition breaks the cover. -/
theorem negative_canary (observation : ControlObservation) :
    ¬ ∃ translation : SemanticCoveredTranslation executeIR.semantics (inventingRuns observation),
      translation.mapTerm = id := by
  rintro ⟨translation, equal⟩
  have invented : (inventingRuns observation).Step
      (translation.mapTerm (encodeExecuteControl (.halted observation)))
      (encodeExecuteControl (.halted observation)) := by
    rw [equal]
    exact Or.inr ⟨rfl, rfl⟩
  obtain ⟨target, step, _⟩ := translation.liftStep invented
  exact stuck_canary observation target (machineRun_of_executeStep step)

#print axioms executeToMachinePass
#print axioms machineRuns_step_iff
#print axioms positive_canary
#print axioms negative_canary

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteMatchMachinePass
