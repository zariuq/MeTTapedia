import Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardRulePlanCompilation

/-!
# Fused source-derived decision program for the PeTTa call guard

The constructor decision tree and the first-order plans for the fifteen
authored rewrite occurrences are fused into one inspectable residual program.
No host callback retrieves or interprets an occurrence after fusion: each
successful leaf carries its exact source index and its compiled matcher,
ordered-premise, and reconstruction plan.

Evaluation is proved equal to the independently defined call-guard source
semantics.  The generic compiler remains partial and its independent transfer
canary checks fail-closed behavior when a reachable plan is omitted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardFusedDecisionProgram

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.OSLF.Framework
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPatternMatrixCompilation
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardRulePlanCompilation

namespace Fusion

export Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion
  (CompiledRule Program compile? compile?_exists evalAll_eq_of_compile?)

end Fusion

/-- Fuse the structural decision program with the independently compiled
first-order plan at every exact source occurrence. -/
def fusedProgramOption :
    Option (Fusion.Program SourceCompiler.Head SourceOccurrence
      FirstOrder.RulePlan) :=
  Fusion.compile? planOptionAt decisionTree

/-- Every occurrence reachable in the source-derived decision tree has a
first-order plan, so complete fusion succeeds. -/
theorem fusedProgramOption_isSome : fusedProgramOption.isSome = true := by
  obtain ⟨program, compiled⟩ :=
    Fusion.compile?_exists planOptionAt (fun occurrence =>
      ⟨planAt occurrence, by
        simpa [planOptionAt] using planAt_compilation_exact occurrence⟩)
      decisionTree
  simp [fusedProgramOption, compiled]

/-- The unique residual program produced by successful fusion. -/
def fusedProgram :
    Fusion.Program SourceCompiler.Head SourceOccurrence FirstOrder.RulePlan :=
  fusedProgramOption.get fusedProgramOption_isSome

/-- `fusedProgram` is the actual output of the partial compiler. -/
theorem fusedProgram_compilation_exact :
    Fusion.compile? planOptionAt decisionTree = some fusedProgram := by
  exact (Option.some_get fusedProgramOption_isSome).symm

/-- Execute the rule plan stored at one decision leaf. -/
def runCompiledOccurrence (source : Pattern)
    (compiled : Fusion.CompiledRule SourceOccurrence FirstOrder.RulePlan) :
    List Pattern :=
  compiled.plan.run relationEnv sourceLanguage source

/-- A leaf compiled from an exact source occurrence retains the full
syntactic matcher, ordered premise, and RHS reconstruction semantics of that
occurrence. -/
theorem runCompiledOccurrence_exact
    (recursiveStep : Pattern → List Pattern) (source : Pattern)
    (occurrence : SourceOccurrence) (plan : FirstOrder.RulePlan)
    (compiled : planOptionAt occurrence = some plan) :
    runCompiledOccurrence source ⟨occurrence, plan⟩ =
      SourceCompiler.syntacticOccurrenceAttempt premiseBase sourceLanguage
        recursiveStep source occurrence := by
  unfold runCompiledOccurrence
  exact FirstOrder.run_compileRule?_eq_applyRuleUsing
    relationEnv sourceLanguage recursiveStep
    (SourceCompiler.ruleAt sourceLanguage occurrence) plan source
    (by simpa [planOptionAt] using compiled)

/-- Execute the complete fused residual program at one contextual depth. -/
def fusedReducts (_recursiveFuel : Nat) (source : Pattern) : List Pattern :=
  fusedProgram.evalAll (runCompiledOccurrence source)
    [SourceCompiler.lowerSubject source]

/-- Fusing occurrence plans into decision leaves preserves every result,
order, and duplicate of the independent source-derived decision semantics. -/
theorem fusedReducts_eq_compiledReducts
    (recursiveFuel : Nat) (source : Pattern) :
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

/-- The fused residual program is exactly the authored least-contextual
call-guard semantics. -/
theorem fusedReducts_eq_contextualRewriteAt
    (recursiveFuel : Nat) (source : Pattern) :
    fusedReducts recursiveFuel source =
      Mettapedia.OSLF.MeTTaIL.ContextualStep.rewriteAt
        premiseBase sourceLanguage (recursiveFuel + 1) source := by
  rw [fusedReducts_eq_compiledReducts,
    compiledReducts_eq_contextualRewriteAt]

/-- Reverse adequacy: the fused program cannot invent a source transition. -/
theorem fusedReducts_no_invention
    (recursiveFuel : Nat) {source target : Pattern}
    (member : target ∈ fusedReducts recursiveFuel source) :
    TypeSynthesis.langReducesUsing relationEnv sourceLanguage source target := by
  rw [fusedReducts_eq_compiledReducts] at member
  exact compiledReducts_no_invention recursiveFuel member

/-- On the exact cold-control image, the first fused result remains the
independent compiler micro-machine successor. -/
theorem fused_first_eq_compileLanguageStep (source : CompileLanguageControl) :
    (fusedReducts 0 (encodeCompileLanguageControl source)).head? =
      (compileLanguageStep? source).map encodeCompileLanguageControl := by
  rw [fusedReducts_eq_compiledReducts,
    compiled_first_eq_compileLanguageStep]

#print axioms fusedProgram_compilation_exact
#print axioms runCompiledOccurrence_exact
#print axioms fusedReducts_eq_contextualRewriteAt
#print axioms fusedReducts_no_invention
#print axioms fused_first_eq_compileLanguageStep

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardFusedDecisionProgram
