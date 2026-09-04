import Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPatternMatrixCompilation

/-!
# First-order residual rule program for the PeTTa call guard

Every authored cold call-guard rewrite row is compiled by the generic
first-order rule compiler.  The resulting program retains exact source
occurrences, constructor patterns, repeated-variable checks, ordered premises,
and right-hand-side reconstruction.  Unsupported source syntax makes program
compilation fail; there is no per-rule matching, premise, or reconstruction
callback.

The source-derived pattern decision tree invokes these compiled plans.  Its
complete ordered reduct list is proved equal to the canonical contextual
semantics and, on the encoded cold-control image, its first result is proved
equal to the independent compiler micro-machine.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardRulePlanCompilation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.OSLF.Framework
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileCodec
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPatternMatrixCompilation

namespace FirstOrder

export Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation
  (PatternPlan RulePlan compileRule? erase_of_compileRule?
    run_eq_syntactic run_compileRule?_eq_applyRuleUsing)

end FirstOrder

/-! ## Exact source-derived rule program -/

/-- Compile the row at one exact authored occurrence. -/
def planOptionAt (occurrence : SourceOccurrence) : Option FirstOrder.RulePlan :=
  FirstOrder.compileRule? (SourceCompiler.ruleAt sourceLanguage occurrence)

/-- Every one of the fifteen source rows belongs to the explicit first-order
fragment.  The occurrence-indexed proof keeps kernel reduction local: a future
unsupported row fails exactly its own branch. -/
theorem planOptionAt_isSome (occurrence : SourceOccurrence) :
    (planOptionAt occurrence).isSome = true := by
  fin_cases occurrence <;> decide +kernel

/-- Retrieve the independently compiled plan for an exact source occurrence. -/
def planAt (occurrence : SourceOccurrence) : FirstOrder.RulePlan :=
  (planOptionAt occurrence).get (planOptionAt_isSome occurrence)

/-- Each retained plan is the actual result of the generic row compiler. -/
theorem planAt_compilation_exact (occurrence : SourceOccurrence) :
    FirstOrder.compileRule? (SourceCompiler.ruleAt sourceLanguage occurrence) =
      some (planAt occurrence) := by
  exact (Option.some_get (planOptionAt_isSome occurrence)).symm

/-- Every retrieved plan erases to the authored row at the same source index. -/
theorem planAt_erase (occurrence : SourceOccurrence) :
    (planAt occurrence).erase = SourceCompiler.ruleAt sourceLanguage occurrence :=
  FirstOrder.erase_of_compileRule?
    (SourceCompiler.ruleAt sourceLanguage occurrence) (planAt occurrence)
    (planAt_compilation_exact occurrence)

/-! ## Composition with the source-derived decision tree -/

/-- Interpret one compiled source occurrence without consulting the original
row for matching, premise sequencing, or reconstruction. -/
def plannedOccurrenceAttempt
    (subject : Pattern) (occurrence : SourceOccurrence) : List Pattern :=
  (planAt occurrence).run relationEnv sourceLanguage subject

/-- One compiled plan has exactly the canonical meaning of its indexed source
row, including premise order and recursive congruence. -/
theorem plannedOccurrenceAttempt_eq_syntactic
    (recursiveStep : Pattern -> List Pattern)
    (subject : Pattern) (occurrence : SourceOccurrence) :
    plannedOccurrenceAttempt subject occurrence =
      SourceCompiler.syntacticOccurrenceAttempt premiseBase sourceLanguage
        recursiveStep subject occurrence := by
  unfold plannedOccurrenceAttempt
  exact FirstOrder.run_compileRule?_eq_applyRuleUsing relationEnv sourceLanguage
    recursiveStep (SourceCompiler.ruleAt sourceLanguage occurrence)
    (planAt occurrence) subject (planAt_compilation_exact occurrence)

/-- Execute the source-derived decision tree with the source-derived rule
plans at one contextual depth. -/
def plannedReducts (_recursiveFuel : Nat) (source : Pattern) : List Pattern :=
  decisionTree.evalAll
    (plannedOccurrenceAttempt source)
    [SourceCompiler.lowerSubject source]

/-- Replacing the canonical per-row callback by compiled plans changes no
result, order, or multiplicity. -/
theorem plannedReducts_eq_compiledReducts
    (recursiveFuel : Nat) (source : Pattern) :
    plannedReducts recursiveFuel source = compiledReducts recursiveFuel source := by
  unfold plannedReducts compiledReducts
  congr 1
  funext occurrence
  exact plannedOccurrenceAttempt_eq_syntactic
    (Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.rewriteAt
      .syntactic premiseBase sourceLanguage recursiveFuel)
    source occurrence

/-- The complete residual program is exactly the authored least contextual
semantics. -/
theorem plannedReducts_eq_contextualRewriteAt
    (recursiveFuel : Nat) (source : Pattern) :
    plannedReducts recursiveFuel source =
      Mettapedia.OSLF.MeTTaIL.ContextualStep.rewriteAt
        premiseBase sourceLanguage (recursiveFuel + 1) source := by
  rw [plannedReducts_eq_compiledReducts,
    compiledReducts_eq_contextualRewriteAt]

/-- Reverse adequacy: the fully compiled residual program cannot invent a
source transition. -/
theorem plannedReducts_no_invention
    (recursiveFuel : Nat) {source target : Pattern}
    (member : target ∈ plannedReducts recursiveFuel source) :
    TypeSynthesis.langReducesUsing relationEnv sourceLanguage source target := by
  rw [plannedReducts_eq_compiledReducts] at member
  exact compiledReducts_no_invention recursiveFuel member

/-- On the cold-control image, the first fully compiled result is exactly the
independent compiler micro-machine successor. -/
theorem planned_first_eq_compileLanguageStep
    (source : CompileLanguageControl) :
    (plannedReducts 0 (encodeCompileLanguageControl source)).head? =
      (compileLanguageStep? source).map encodeCompileLanguageControl := by
  rw [plannedReducts_eq_compiledReducts,
    compiled_first_eq_compileLanguageStep]

/-! ## Discriminating controls -/

/-- Source-row count is retained rather than collapsed to one phase case. -/
example : sourceLanguage.rewrites.length = 15 := by
  decide +kernel

/-- An invented target rejected by the source remains rejected by the fully
compiled program. -/
example (recursiveFuel : Nat) (source target : Pattern)
    (rejected : Not
      (TypeSynthesis.langReducesUsing relationEnv sourceLanguage source target)) :
    target ∉ plannedReducts recursiveFuel source := by
  intro member
  exact rejected (plannedReducts_no_invention recursiveFuel member)

#print axioms planOptionAt_isSome
#print axioms planAt_compilation_exact
#print axioms planAt_erase
#print axioms plannedOccurrenceAttempt_eq_syntactic
#print axioms plannedReducts_eq_contextualRewriteAt
#print axioms plannedReducts_no_invention
#print axioms planned_first_eq_compileLanguageStep

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardRulePlanCompilation
