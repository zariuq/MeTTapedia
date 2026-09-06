import Mettapedia.GSLT.LanguageDef.OrderedMatchMachineAdequacy
import Mettapedia.GSLT.LanguageDef.IRRunView
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardFusedDecisionProgram

/-!
# The cold call-guard language covered by the ordered-match machine

The cold call-guard language is a representation: its validated definition
with the relation environment its premises consult.  Its fused decision
program, translated leaf by leaf into the ordered-match machine's plans, is a
program of the machine representation.  One complete run of the machine on
a cold term, from the run state of that program to a result state, is one
step of the cold language, and every cold step is such a run.  The identity
on terms is therefore a semantic cover from the cold language into the run
view of the machine: the first pass of the lowering, with the leaf evaluator
now the machine's own operational semantics.

Two canaries fix the sense of the cover.  A running control state with no
remaining declarations steps to its compiled halt, and the machine runs to
exactly that result.  A control state with no successor has no run, and a
run view with one invented transition from such a state allows no cover
with the identity term map.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardMatchMachinePass

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
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection (SpaceOwner)
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan (GuardPlan)
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPatternMatrixCompilation
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardFusedDecisionProgram

namespace Machine

export Mettapedia.GSLT.LanguageDef.OrderedMatchMachineLanguage
  (Program MachineState encodeState ir mapProgram toMachinePlan LanguageReaches
    languageReaches_of_reaches reaches_of_languageReaches languageReaches_mapProgram_iff
    language_isEquationFree)

end Machine

/-! ## The two representations -/

/-- The cold call-guard language as a representation. -/
def coldIR : IRLanguage := ⟨coldSource, relationEnv⟩

theorem cold_isEquationFree : coldSource.language.isEquationFree = true := by decide

/-- The cold representation's step is the authored least-contextual step. -/
theorem coldStep_iff (source target : Pattern) :
    coldIR.semantics.Step source target ↔ langReducesUsing relationEnv sourceLanguage source target := by
  change StepModuloEquations (engineBasePremises relationEnv) coldSource.language source target ↔ _
  rw [stepModuloEquations_iff_step_of_no_generators cold_isEquationFree]
  rfl

theorem coldEquiv_iff (left right : Pattern) : coldIR.semantics.Equiv left right ↔ left = right :=
  gsltModuloEquations_equiv_iff_eq_of_no_generators cold_isEquationFree left right

/-- The ordered-match machine over the cold relation environment. -/
def machineIR : IRLanguage := Machine.ir relationEnv sourceLanguage

theorem machineEquiv_iff (left right : Pattern) :
    machineIR.semantics.Equiv left right ↔ left = right :=
  gsltModuloEquations_equiv_iff_eq_of_no_generators
    Machine.language_isEquationFree left right

/-- The fused cold decision program as a machine program. -/
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

/-- A machine run from a term to a result is membership in the fused
evaluator's output. -/
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
    have listed := (Machine.languageReaches_mapProgram_iff relationEnv sourceLanguage fusedProgram
      (fun occurrence : SourceOccurrence => occurrence.val) source target).mp
      (Machine.languageReaches_of_reaches relationEnv sourceLanguage machineRun)
    exact listed
  · intro member
    refine ⟨Machine.encodeState (.done target), ?_, rfl⟩
    exact (Machine.languageReaches_mapProgram_iff relationEnv sourceLanguage fusedProgram
      (fun occurrence : SourceOccurrence => occurrence.val) source target).mpr member

/-! ## The pass -/

/-- Every cold step is a machine run: the first cover direction. -/
theorem machineRun_of_coldStep {source target : Pattern}
    (step : coldIR.semantics.Step source target) : machineRuns.Step source target := by
  rw [machineRuns_step_iff]
  obtain ⟨fuel, member⟩ := language_step_covered ((coldStep_iff source target).mp step)
  rw [← fusedReducts_eq_compiledReducts] at member
  exact member

/-- Every machine run is a cold step: the second cover direction. -/
theorem coldStep_of_machineRun {source target : Pattern}
    (run : machineRuns.Step source target) : coldIR.semantics.Step source target := by
  rw [machineRuns_step_iff] at run
  exact (coldStep_iff source target).mpr (fusedReducts_no_invention 0 run)

/-- The identity on terms is a semantic cover from the cold call-guard
language into the run view of the ordered-match machine. -/
def coldToMachinePass : SemanticCoveredTranslation coldIR.semantics machineRuns :=
  coverOfRuns coldIR machineIR protocol id
    (fun equal =>
      (machineEquiv_iff _ _).mpr ((coldEquiv_iff _ _).mp equal))
    (fun step => machineRun_of_coldStep step)
    (fun run => ⟨_, coldStep_of_machineRun run,
      machineIR.semantics.equations.iseqv.refl _⟩)

@[simp]
theorem coldToMachinePass_mapTerm : coldToMachinePass.mapTerm = id := rfl

/-! ## Canaries -/

/-- A running control with no remaining declaration halts compiled, and the
machine runs to exactly that halt. -/
theorem positive_canary (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) :
    machineRuns.Step
      (encodeCompileLanguageControl (.running owner revision head arity [] accepted))
      (encodeCompileLanguageControl
        (.halted (.compiled ⟨owner, revision, head, arity, accepted⟩))) := by
  rw [machineRuns_step_iff]
  apply List.mem_of_mem_head?
  rw [fused_first_eq_compileLanguageStep]
  rfl

/-- A control with no successor has no machine run. -/
theorem stuck_canary (control : CompileLanguageControl)
    (stuck : compileLanguageStep? control = none) (target : Pattern) :
    ¬ machineRuns.Step (encodeCompileLanguageControl control) target := by
  rw [machineRuns_step_iff]
  intro member
  have first := fused_first_eq_compileLanguageStep control
  rw [stuck, Option.map_none, List.head?_eq_none_iff] at first
  rw [first] at member
  simp at member

example : compileLanguageStep? (.halted .outsideFragment) = none := rfl

/-- The run view with one invented transition from a stuck control to
itself. -/
def inventingRuns (stuckControl : CompileLanguageControl) : GSLT where
  Term := Pattern
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target =>
    machineRuns.Step source target ∨
      (source = encodeCompileLanguageControl stuckControl ∧ target = source)
  rewrites_resp_left := by
    intro source source' target equal step
    subst equal
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst equal
    exact step

/-- One invented transition breaks the cover: no semantic cover with the
identity term map exists into the inventing run view. -/
theorem negative_canary (control : CompileLanguageControl)
    (stuck : compileLanguageStep? control = none) :
    ¬ ∃ translation : SemanticCoveredTranslation coldIR.semantics (inventingRuns control),
      translation.mapTerm = id := by
  rintro ⟨translation, equal⟩
  have invented : (inventingRuns control).Step
      (translation.mapTerm (encodeCompileLanguageControl control))
      (encodeCompileLanguageControl control) := by
    rw [equal]
    exact Or.inr ⟨rfl, rfl⟩
  obtain ⟨target, step, _⟩ := translation.liftStep invented
  exact stuck_canary control stuck target (machineRun_of_coldStep step)

#print axioms coldToMachinePass
#print axioms machineRuns_step_iff
#print axioms positive_canary
#print axioms negative_canary

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardMatchMachinePass
