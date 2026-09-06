import Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecutePatternMatrixCompilation

/-!
# First-order residual rule program for the completed-call executor

Every executor rewrite row is compiled by the generic first-order rule
compiler.  The program retains exact source occurrences, constructor
patterns, repeated-variable checks, ordered premises, and right-hand-side
reconstruction; unsupported source syntax makes compilation fail.  The
source-derived decision tree invokes these plans, and its complete ordered
reduct list is proved equal to the canonical contextual semantics; on the
encoded executor-state image its first result is the executor's successor.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteRulePlanCompilation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.OSLF.Framework
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControl
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecutePatternMatrixCompilation

namespace FirstOrder
export Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation
  (PatternPlan RulePlan compileRule? erase_of_compileRule?
    run_eq_syntactic run_compileRule?_eq_applyRuleUsing)
end FirstOrder

/-- Compile the row at one exact source occurrence. -/
def planOptionAt (occurrence : SourceOccurrence) : Option FirstOrder.RulePlan :=
  FirstOrder.compileRule? (SourceCompiler.ruleAt sourceLanguage occurrence)

/-- Every one of the twenty-one rows belongs to the first-order fragment. -/
theorem planOptionAt_isSome (occurrence : SourceOccurrence) :
    (planOptionAt occurrence).isSome = true := by
  fin_cases occurrence <;> decide +kernel

/-- The compiled plan of an exact source occurrence. -/
def planAt (occurrence : SourceOccurrence) : FirstOrder.RulePlan :=
  (planOptionAt occurrence).get (planOptionAt_isSome occurrence)

theorem planAt_compilation_exact (occurrence : SourceOccurrence) :
    FirstOrder.compileRule? (SourceCompiler.ruleAt sourceLanguage occurrence) =
      some (planAt occurrence) :=
  (Option.some_get (planOptionAt_isSome occurrence)).symm

theorem planAt_erase (occurrence : SourceOccurrence) :
    (planAt occurrence).erase = SourceCompiler.ruleAt sourceLanguage occurrence :=
  FirstOrder.erase_of_compileRule? (SourceCompiler.ruleAt sourceLanguage occurrence)
    (planAt occurrence) (planAt_compilation_exact occurrence)

/-- Interpret one compiled occurrence without consulting the original row. -/
def plannedOccurrenceAttempt (subject : Pattern) (occurrence : SourceOccurrence) : List Pattern :=
  (planAt occurrence).run relationEnv sourceLanguage subject

theorem plannedOccurrenceAttempt_eq_syntactic (recursiveStep : Pattern → List Pattern)
    (subject : Pattern) (occurrence : SourceOccurrence) :
    plannedOccurrenceAttempt subject occurrence =
      SourceCompiler.syntacticOccurrenceAttempt premiseBase sourceLanguage
        recursiveStep subject occurrence := by
  unfold plannedOccurrenceAttempt
  exact FirstOrder.run_compileRule?_eq_applyRuleUsing relationEnv sourceLanguage
    recursiveStep (SourceCompiler.ruleAt sourceLanguage occurrence)
    (planAt occurrence) subject (planAt_compilation_exact occurrence)

/-- The decision tree with the compiled plans at one contextual depth. -/
def plannedReducts (_recursiveFuel : Nat) (source : Pattern) : List Pattern :=
  decisionTree.evalAll (plannedOccurrenceAttempt source) [SourceCompiler.lowerSubject source]

theorem plannedReducts_eq_compiledReducts (recursiveFuel : Nat) (source : Pattern) :
    plannedReducts recursiveFuel source = compiledReducts recursiveFuel source := by
  unfold plannedReducts compiledReducts
  congr 1
  funext occurrence
  exact plannedOccurrenceAttempt_eq_syntactic
    (Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.rewriteAt
      .syntactic premiseBase sourceLanguage recursiveFuel)
    source occurrence

theorem plannedReducts_eq_contextualRewriteAt (recursiveFuel : Nat) (source : Pattern) :
    plannedReducts recursiveFuel source =
      Mettapedia.OSLF.MeTTaIL.ContextualStep.rewriteAt
        premiseBase sourceLanguage (recursiveFuel + 1) source := by
  rw [plannedReducts_eq_compiledReducts, compiledReducts_eq_contextualRewriteAt]

theorem plannedReducts_no_invention (recursiveFuel : Nat) {source target : Pattern}
    (member : target ∈ plannedReducts recursiveFuel source) :
    TypeSynthesis.langReducesUsing relationEnv sourceLanguage source target := by
  rw [plannedReducts_eq_compiledReducts] at member
  exact compiledReducts_no_invention recursiveFuel member

theorem planned_first_eq_executeStep (source : ExecuteControl) :
    (plannedReducts 0 (encodeExecuteControl source)).head? =
      (executeStep? source).map encodeExecuteControl := by
  rw [plannedReducts_eq_compiledReducts, compiled_first_eq_executeStep]

/-- Source-row count is retained. -/
example : sourceLanguage.rewrites.length = 21 := by decide +kernel

#print axioms planOptionAt_isSome
#print axioms plannedReducts_eq_contextualRewriteAt
#print axioms planned_first_eq_executeStep

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteRulePlanCompilation
