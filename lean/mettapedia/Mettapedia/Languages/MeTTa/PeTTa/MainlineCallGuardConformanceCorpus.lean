import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardComposedInvocationRealization
import Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender

/-!
# Conformance corpus for the generated call-guard bodies

For each of the fifteen cold rows and twenty-one hot rows, one loaded state
with the exit configuration the reference runtime produces from it, and the
reference next state; and whole-run fixtures on a small snapshot with the
expected compilation and execution results.  Every expected exit is computed
here by the reference runtime, and every fixture's next state is tied to the
exactness theorems: the exit's state slot is the reference step, and the
whole runs are chains of invocations reaching the reference results.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardConformanceCorpus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender
open Mettapedia.GSLT.LanguageDef.StructuredCStraightLine
open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.CallGuardNativeKernel
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControl
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCOneStepSimulation
  (coldRelations)
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCTotalRealization
  (normalized_observation_iff_of_step)
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCSemantics (handler)
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardComposedRealization
  (invoke? invoke?_runControl)
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardComposedInvocationRealization
  (hotInvoke? hotInvoke?_runControl)

namespace Cold
export Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics (runControl)
export Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFinishSemantics
  (terminalControl?)
end Cold

namespace Hot
export Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCTotalRealization
  (runControl terminalControl? runBudget observation_exact)
end Hot

/-! ## Fixtures -/

/-- One row fixture: the loaded state, the exit configuration the reference
runtime produces, and the reference next state. -/
structure RowFixture where
  name : String
  loaded : Pattern
  exit : Pattern
  next : Pattern

def noExit : Pattern := .apply "structured-c:no-exit" []
def noStep : Pattern := .apply "petta-call-guard:no-step" []

/-- The cold reference exit: the first-reduct normalization of the loaded
state under the cold catalogs. -/
def coldExit (control : CompileLanguageControl) : Pattern :=
  normalizeFirstUsing coldRelations StructuredC.language 1 64 (Cold.runControl control)

def coldFixture (name : String) (control : CompileLanguageControl) : RowFixture :=
  ⟨name, Cold.runControl control, coldExit control,
    match compileLanguageStep? control with
    | some next => encodeCompileLanguageControl next
    | none => noStep⟩

/-- The hot reference exit: the straight-line run of the loaded state under
the hot handler. -/
def hotExit (control : ExecuteControl) : Pattern :=
  (runSteps? handler Hot.runBudget (Hot.runControl control)).getD noExit

def hotFixture (name : String) (control : ExecuteControl) : RowFixture :=
  ⟨name, Hot.runControl control, hotExit control,
    match executeStep? control with
    | some next => encodeExecuteControl next
    | none => noStep⟩

/-! ### Cold rows -/

def owner : SpaceOwner := ⟨0⟩
def declA : ArrowDeclaration := ⟨1, "f", [.atom "A"], .atom "R"⟩
def declG : ArrowDeclaration := ⟨2, "g", [], .atom "R"⟩
def declUndefinedOut : ArrowDeclaration := ⟨3, "f", [], undefinedType⟩
def declHoleOut : ArrowDeclaration := ⟨4, "f", [], holeType⟩
def declAtomOut : ArrowDeclaration := ⟨5, "f", [], atomType⟩
def declOpenOut : ArrowDeclaration := ⟨6, "f", [], .variable "x"⟩

def coldRowControls : List (String × CompileLanguageControl) := [
  ("finish", .running owner 0 "f" 0 [] []),
  ("skip-head", .running owner 0 "f" 0 [declG] []),
  ("skip-arity", .running owner 0 "f" 0 [declA] []),
  ("begin-declaration", .running owner 0 "f" 1 [declA] []),
  ("arguments-finished", .arguments owner 0 "f" 1 declA [] [] [] []),
  ("raw-input", .arguments owner 0 "f" 1 declA [] [atomType] [] []),
  ("undefined-input", .arguments owner 0 "f" 1 declA [] [undefinedType] [] []),
  ("hole-input", .arguments owner 0 "f" 1 declA [] [holeType] [] []),
  ("checked-input", .arguments owner 0 "f" 1 declA [] [.atom "A"] [] []),
  ("open-input", .arguments owner 0 "f" 1 declA [] [.variable "x"] [] []),
  ("undefined-result", .result owner 0 "f" 0 declUndefinedOut [] [] []),
  ("hole-result", .result owner 0 "f" 0 declHoleOut [] [] []),
  ("atom-result", .result owner 0 "f" 0 declAtomOut [] [] []),
  ("checked-result", .result owner 0 "f" 1 declA [] [.evalSoftcutType (.atom "A")] []),
  ("open-result", .result owner 0 "f" 0 declOpenOut [] [] [])]

/-- The reference next state of every cold row, in row order. -/
def coldRowTargets : List CompileLanguageControl := [
  .halted (.compiled ⟨owner, 0, "f", 0, []⟩),
  .running owner 0 "f" 0 [] [],
  .running owner 0 "f" 0 [] [],
  .arguments owner 0 "f" 1 declA [] [.atom "A"] [] [],
  .result owner 0 "f" 1 declA [] [] [],
  .arguments owner 0 "f" 1 declA [] [] [.rawAtom] [],
  .arguments owner 0 "f" 1 declA [] [] [.evalUnchecked] [],
  .arguments owner 0 "f" 1 declA [] [] [.evalUnchecked] [],
  .arguments owner 0 "f" 1 declA [] [] [.evalSoftcutType (.atom "A")] [],
  .halted .outsideFragment,
  .running owner 0 "f" 0 [] [⟨3, [], .resultUnchecked, declUndefinedOut⟩],
  .running owner 0 "f" 0 [] [⟨4, [], .resultUnchecked, declHoleOut⟩],
  .running owner 0 "f" 0 [] [⟨5, [], .resultUnchecked, declAtomOut⟩],
  .running owner 0 "f" 1 [] [⟨1, [.evalSoftcutType (.atom "A")], .resultSoftcutType (.atom "R"),
    declA⟩],
  .halted .outsideFragment]

/-- Every cold row fixture steps to its listed target: the fixtures exercise
the rows they name. -/
theorem coldRows_step :
    coldRowControls.map (fun row => compileLanguageStep? row.2) = coldRowTargets.map some := by
  decide

/-! ### Hot rows -/

def snapshot : Snapshot :=
  ⟨0, [declA], [⟨1, .atom "a", .atom "A"⟩, ⟨2, .atom "r", .atom "R"⟩], ["f"]⟩
def owned : OwnedSnapshot := ⟨owner, snapshot⟩
def call : Call := ⟨"f", [.atom "a"], [.atom "a"], .atom "r"⟩
def callNumber : Call := ⟨"f", [.atom "a"], [.atom "a"], .number "1"⟩
def plan : GuardPlan := ⟨1, [.evalSoftcutType (.atom "A")], .resultSoftcutType (.atom "R"), declA⟩
def family : CompiledGuardFamily := ⟨owner, 0, "f", 1, [plan]⟩

def hotRowControls : List (String × ExecuteControl) := [
  ("request-outside-fragment", .request owned call .outsideFragment),
  ("request-foreign-owner", .request owned call (.compiled { family with owner := ⟨1⟩ })),
  ("request-stale-revision", .request owned call (.compiled { family with revision := 1 })),
  ("request-wrong-head", .request owned call (.compiled { family with head := "g" })),
  ("request-wrong-arity", .request owned call (.compiled { family with arity := 0 })),
  ("request-current", .request owned call (.compiled family)),
  ("plans-finished", .plans snapshot call [] [] []),
  ("plan-head-mismatch", .plans snapshot call [{ plan with declaration := declG }] [] []),
  ("plan-head-matches", .plans snapshot call [plan] [] []),
  ("arguments-finished", .arguments snapshot call plan [] 1 [] [] [] [] []),
  ("argument-raw-accepted",
    .arguments snapshot call plan [] 0 [.rawAtom] [.atom "a"] [.atom "a"] [] []),
  ("argument-raw-rejected",
    .arguments snapshot call plan [] 0 [.rawAtom] [.atom "a"] [.atom "b"] [] []),
  ("argument-unchecked",
    .arguments snapshot call plan [] 0 [.evalUnchecked] [.atom "a"] [.atom "a"] [] []),
  ("argument-checked-exact",
    .arguments snapshot call plan [] 0 [.evalSoftcutType (.atom "A")] [.atom "a"] [.atom "a"]
      [] []),
  ("argument-checked-metatype-accepted",
    .arguments snapshot call plan [] 0 [.evalSoftcutType groundedMetaType] [.atom "a"]
      [.number "1"] [] []),
  ("argument-checked-metatype-rejected",
    .arguments snapshot call plan [] 0 [.evalSoftcutType (.atom "Foo")] [.atom "a"]
      [.number "1"] [] []),
  ("argument-shape-mismatch", .arguments snapshot call plan [] 0 [] [.atom "a"] [] [] []),
  ("result-unchecked",
    .result snapshot call { plan with resultMode := .resultUnchecked } [] [] []),
  ("result-checked-exact", .result snapshot call plan [] [] []),
  ("result-checked-metatype-accepted",
    .result snapshot callNumber { plan with resultMode := .resultSoftcutType groundedMetaType }
      [] [] []),
  ("result-checked-metatype-rejected",
    .result snapshot callNumber { plan with resultMode := .resultSoftcutType (.atom "Foo") }
      [] [] [])]

/-- The reference next state of every hot row, in row order. -/
def hotRowTargets : List ExecuteControl := [
  .halted ⟨.fallback .outsideFragment, [.fallback .outsideFragment]⟩,
  .halted ⟨.fallback .foreignOwner, [.fallback .foreignOwner]⟩,
  .halted ⟨.fallback .staleRevision, [.fallback .staleRevision]⟩,
  .halted ⟨.fallback .wrongHead, [.fallback .wrongHead]⟩,
  .halted ⟨.fallback .wrongArity, [.fallback .wrongArity]⟩,
  .plans snapshot call [plan] [] [],
  .halted ⟨.executed [], []⟩,
  .plans snapshot call [] [] [.beginPlan 1, .rejectOccurrence 1],
  .arguments snapshot call plan [] 0 [.evalSoftcutType (.atom "A")] [.atom "a"] [.atom "a"] []
    [.beginPlan 1],
  .result snapshot call plan [] [] [.evaluateCall 1],
  .arguments snapshot call plan [] 1 [] [] [] [] [.useRawArgument 0],
  .plans snapshot call [] [] [.useRawArgument 0, .rejectOccurrence 1],
  .arguments snapshot call plan [] 1 [] [] [] [] [.evaluateArgument 0],
  .arguments snapshot call plan [] 1 [] [] [] []
    [.evaluateArgument 0, .queryExactType 0 (.atom "A") true],
  .arguments snapshot call plan [] 1 [] [] [] []
    [.evaluateArgument 0, .queryExactType 0 groundedMetaType false,
      .queryMetatype 0 groundedMetaType true],
  .plans snapshot call [] []
    [.evaluateArgument 0, .queryExactType 0 (.atom "Foo") false,
      .queryMetatype 0 (.atom "Foo") false, .rejectOccurrence 1],
  .plans snapshot call [] [] [.argumentShapeMismatch 0, .rejectOccurrence 1],
  .plans snapshot call [] [declA] [.installOccurrence 1],
  .plans snapshot call [] [declA] [.queryResultType (.atom "R") true, .installOccurrence 1],
  .plans snapshot callNumber [] [declA]
    [.queryResultType groundedMetaType false, .queryResultMetatype groundedMetaType true,
      .installOccurrence 1],
  .plans snapshot callNumber [] []
    [.queryResultType (.atom "Foo") false, .queryResultMetatype (.atom "Foo") false,
      .rejectOccurrence 1]]

/-- Every hot row fixture steps to its listed target. -/
theorem hotRows_step :
    hotRowControls.map (fun row => executeStep? row.2) = hotRowTargets.map some := by
  decide

/-! ## Ties to the exactness theorems -/

/-- The state slot of every cold exit is the reference step. -/
theorem coldExit_exact (control target : CompileLanguageControl)
    (step : compileLanguageStep? control = some target) :
    Cold.terminalControl? (coldExit control) = some target :=
  (normalized_observation_iff_of_step (step : compileLanguageGSLT.Step control target) target).2
    rfl

/-- The state slot of every hot exit is the reference step. -/
theorem hotExit_exact (control target : ExecuteControl)
    (step : executeStep? control = some target) :
    Hot.terminalControl? (hotExit control) = some target := by
  have observed := Hot.observation_exact control target step
  unfold Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCTotalRealization.observation
    at observed
  obtain ⟨final, ran, terminal⟩ := Option.bind_eq_some_iff.mp observed
  simp [hotExit, ran, terminal]

/-! ## Whole runs -/

/-- Iterated cold invocations. -/
def invokeN : Nat → Pattern → Option Pattern
  | 0, config => some config
  | n + 1, config => (invoke? config).bind (invokeN n)

def coldStepN : Nat → CompileLanguageControl → Option CompileLanguageControl
  | 0, control => some control
  | n + 1, control => (compileLanguageStep? control).bind (coldStepN n)

theorem invokeN_runControl (n : Nat) (control : CompileLanguageControl) :
    invokeN n (Cold.runControl control) = (coldStepN n control).map Cold.runControl := by
  induction n generalizing control with
  | zero => rfl
  | succ n inductionHypothesis =>
      simp only [invokeN, coldStepN, invoke?_runControl]
      cases compileLanguageStep? control with
      | none => rfl
      | some next => simp [inductionHypothesis]

/-- Iterated hot invocations. -/
def hotInvokeN : Nat → Pattern → Option Pattern
  | 0, config => some config
  | n + 1, config => (hotInvoke? config).bind (hotInvokeN n)

def hotStepN : Nat → ExecuteControl → Option ExecuteControl
  | 0, control => some control
  | n + 1, control => (executeStep? control).bind (hotStepN n)

theorem hotInvokeN_runControl (n : Nat) (control : ExecuteControl) :
    hotInvokeN n (Hot.runControl control) = (hotStepN n control).map Hot.runControl := by
  induction n generalizing control with
  | zero => rfl
  | succ n inductionHypothesis =>
      simp only [hotInvokeN, hotStepN, hotInvoke?_runControl]
      cases executeStep? control with
      | none => rfl
      | some next => simp [inductionHypothesis]

/-- The whole-run snapshot: one relevant and one irrelevant declaration. -/
def wholeSnapshot : Snapshot :=
  ⟨0, [declA, declG], [⟨1, .atom "a", .atom "A"⟩, ⟨2, .atom "r", .atom "R"⟩], ["f", "g"]⟩
def wholeOwned : OwnedSnapshot := ⟨owner, wholeSnapshot⟩
def wholeStart : CompileLanguageControl := compileLanguageStart wholeOwned "f" 1
def wholeCompilation : CompilationResult := compileGuards wholeOwned "f" 1
def wholeExpectedFamily : CompiledGuardFamily := ⟨owner, 0, "f", 1, [plan]⟩

theorem wholeCompilation_value : wholeCompilation = .compiled wholeExpectedFamily := by
  decide

set_option maxRecDepth 10000 in
/-- Six cold invocations from the loaded start reach the loaded halted
compilation. -/
theorem cold_whole_run :
    invokeN 6 (Cold.runControl wholeStart) =
      some (Cold.runControl (.halted wholeCompilation)) := by
  rw [invokeN_runControl, wholeCompilation_value]
  decide

def wholeRequest : ExecuteControl := .request wholeOwned call wholeCompilation
def wholeObservation : ControlObservation := executeControl wholeOwned call wholeCompilation

theorem wholeObservation_value :
    wholeObservation = ⟨.executed [declA],
      [.beginPlan 1, .evaluateArgument 0, .queryExactType 0 (.atom "A") true, .evaluateCall 1,
        .queryResultType (.atom "R") true, .installOccurrence 1]⟩ := by
  decide

set_option maxRecDepth 10000 in
/-- Six hot invocations from the loaded request reach the loaded halted
observation. -/
theorem hot_whole_run :
    hotInvokeN 6 (Hot.runControl wholeRequest) =
      some (Hot.runControl (.halted wholeObservation)) := by
  rw [hotInvokeN_runControl, wholeObservation_value]
  decide

/-! ## The wire -/

def fixturePattern (fixture : RowFixture) : Pattern :=
  .apply "petta-call-guard:fixture"
    [.apply fixture.name [], fixture.loaded, fixture.exit, fixture.next]

def fixtures (rows : List Pattern) : Pattern :=
  rows.foldr (fun row rest => .apply "petta-call-guard:fixtures-cons" [row, rest])
    (.apply "petta-call-guard:fixtures-nil" [])

def coldFixtures : List RowFixture := coldRowControls.map fun row => coldFixture row.1 row.2
def hotFixtures : List RowFixture := hotRowControls.map fun row => hotFixture row.1 row.2

def wholeRunPattern (name : String) (start final expected : Pattern) : Pattern :=
  .apply "petta-call-guard:whole-run" [.apply name [], start, final, expected]

def corpusPattern : Pattern :=
  .apply "petta-call-guard:conformance-corpus" [
    fixtures (coldFixtures.map fixturePattern),
    fixtures (hotFixtures.map fixturePattern),
    fixtures [
      wholeRunPattern "cold-compile-guards" (Cold.runControl wholeStart)
        ((invokeN 6 (Cold.runControl wholeStart)).getD noExit)
        (encodeCompileLanguageControl (.halted wholeCompilation)),
      wholeRunPattern "hot-execute-control" (Hot.runControl wholeRequest)
        ((hotInvokeN 6 (Hot.runControl wholeRequest)).getD noExit)
        (encodeExecuteControl (.halted wholeObservation))]]

def corpusWire : String := renderPattern corpusPattern ++ "\n"

theorem corpus_counts : coldFixtures.length = 15 ∧ hotFixtures.length = 21 := by
  decide

#print axioms coldRows_step
#print axioms hotRows_step
#print axioms coldExit_exact
#print axioms hotExit_exact
#print axioms cold_whole_run
#print axioms hot_whole_run

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardConformanceCorpus
