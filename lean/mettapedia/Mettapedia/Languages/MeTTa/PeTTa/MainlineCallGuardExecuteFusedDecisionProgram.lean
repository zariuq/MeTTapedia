import Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteRulePlanCompilation

/-!
# Fused source-derived decision program for the completed-call executor

The constructor decision tree and the first-order plans of the twenty-one
executor rows are fused into one residual program: each successful leaf
carries its exact source index and its compiled matcher, ordered-premise, and
reconstruction plan.  Evaluation is proved equal to the executor language's
contextual semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteFusedDecisionProgram

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.OSLF.Framework
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControl
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecutePatternMatrixCompilation
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteRulePlanCompilation

namespace Fusion
export Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion
  (CompiledRule Program compile? compile?_exists evalAll_eq_of_compile?)
end Fusion

def fusedProgramOption :
    Option (Fusion.Program SourceCompiler.Head SourceOccurrence FirstOrder.RulePlan) :=
  Fusion.compile? planOptionAt decisionTree

theorem fusedProgramOption_isSome : fusedProgramOption.isSome = true := by
  obtain ⟨program, compiled⟩ :=
    Fusion.compile?_exists planOptionAt (fun occurrence =>
      ⟨planAt occurrence, by simpa [planOptionAt] using planAt_compilation_exact occurrence⟩)
      decisionTree
  simp [fusedProgramOption, compiled]

/-- The unique residual program produced by successful fusion. -/
def fusedProgram : Fusion.Program SourceCompiler.Head SourceOccurrence FirstOrder.RulePlan :=
  fusedProgramOption.get fusedProgramOption_isSome

theorem fusedProgram_compilation_exact :
    Fusion.compile? planOptionAt decisionTree = some fusedProgram :=
  (Option.some_get fusedProgramOption_isSome).symm

/-- Execute the rule plan stored at one decision leaf. -/
def runCompiledOccurrence (source : Pattern)
    (compiled : Fusion.CompiledRule SourceOccurrence FirstOrder.RulePlan) : List Pattern :=
  compiled.plan.run relationEnv sourceLanguage source

theorem runCompiledOccurrence_exact (recursiveStep : Pattern → List Pattern) (source : Pattern)
    (occurrence : SourceOccurrence) (plan : FirstOrder.RulePlan)
    (compiled : planOptionAt occurrence = some plan) :
    runCompiledOccurrence source ⟨occurrence, plan⟩ =
      SourceCompiler.syntacticOccurrenceAttempt premiseBase sourceLanguage
        recursiveStep source occurrence := by
  unfold runCompiledOccurrence
  exact FirstOrder.run_compileRule?_eq_applyRuleUsing relationEnv sourceLanguage recursiveStep
    (SourceCompiler.ruleAt sourceLanguage occurrence) plan source
    (by simpa [planOptionAt] using compiled)

/-- Execute the complete fused residual program at one contextual depth. -/
def fusedReducts (_recursiveFuel : Nat) (source : Pattern) : List Pattern :=
  fusedProgram.evalAll (runCompiledOccurrence source) [SourceCompiler.lowerSubject source]

theorem fusedReducts_eq_compiledReducts (recursiveFuel : Nat) (source : Pattern) :
    fusedReducts recursiveFuel source = compiledReducts recursiveFuel source := by
  unfold fusedReducts compiledReducts
  exact Fusion.evalAll_eq_of_compile? planOptionAt
    (SourceCompiler.syntacticOccurrenceAttempt premiseBase sourceLanguage
      (Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.rewriteAt
        .syntactic premiseBase sourceLanguage recursiveFuel)
      source)
    (runCompiledOccurrence source)
    (runCompiledOccurrence_exact
      (Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.rewriteAt
        .syntactic premiseBase sourceLanguage recursiveFuel)
      source)
    decisionTree fusedProgram fusedProgram_compilation_exact
    [SourceCompiler.lowerSubject source]

theorem fusedReducts_eq_contextualRewriteAt (recursiveFuel : Nat) (source : Pattern) :
    fusedReducts recursiveFuel source =
      Mettapedia.OSLF.MeTTaIL.ContextualStep.rewriteAt
        premiseBase sourceLanguage (recursiveFuel + 1) source := by
  rw [fusedReducts_eq_compiledReducts, compiledReducts_eq_contextualRewriteAt]

theorem fusedReducts_no_invention (recursiveFuel : Nat) {source target : Pattern}
    (member : target ∈ fusedReducts recursiveFuel source) :
    TypeSynthesis.langReducesUsing relationEnv sourceLanguage source target := by
  rw [fusedReducts_eq_compiledReducts] at member
  exact compiledReducts_no_invention recursiveFuel member

/-- On the executor-state image, the first fused result is the executor's
successor. -/
theorem fused_first_eq_executeStep (source : ExecuteControl) :
    (fusedReducts 0 (encodeExecuteControl source)).head? =
      (executeStep? source).map encodeExecuteControl := by
  rw [fusedReducts_eq_compiledReducts, compiled_first_eq_executeStep]

#print axioms fusedProgram_compilation_exact
#print axioms fusedReducts_eq_contextualRewriteAt
#print axioms fusedReducts_no_invention
#print axioms fused_first_eq_executeStep

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteFusedDecisionProgram
