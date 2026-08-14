import Mettapedia.GSLT.LanguageDef.FiniteRuleIndexCompilation
import Mettapedia.GSLT.LanguageDef.InferenceChecker

/-!
# Deriving rule-index admission from inference-presentation validity

`FiniteRuleIndexCompilation` deliberately knows nothing about inference
syntax.  This module supplies the small, checked bridge from a validated
inference presentation: contextual V2 validity already proves that every
rule conclusion has a declared outer judgment head and arity, so every stored
rule is admitted by the generic index compiler.

The optimization therefore follows from an authored local property.  A
runtime need not recognize particular judgment names, and an unvalidated
headless rule receives no fallback meaning.
-/

namespace Mettapedia.GSLT.LanguageDef.InferenceRuleIndexCompilation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.FiniteRuleIndexCompilation

/-- The generic dispatch key induced by a declared outer judgment shape. -/
abbrev JudgmentKey := String × Nat

/-- Recover a rule's outer constructor signature when it is syntactically
available. -/
def conclusionKey? (rule : RuleSchema) : Option JudgmentKey :=
  match rule.conclusion with
  | .apply head arguments => some (head, arguments.length)
  | _ => none

/-- A declared judgment shape exposes exactly the key required by the generic
index compiler. -/
theorem conclusionKey?_isSome_of_hasJudgmentShape
    (presentation : Presentation) (rule : RuleSchema)
    (valid : presentation.hasJudgmentShape rule.conclusion = true) :
    (conclusionKey? rule).isSome = true := by
  cases conclusionEq : rule.conclusion <;>
    simp_all [conclusionKey?, Presentation.hasJudgmentShape]

/-- Every rule of a validated presentation passes the local indexability
recognizer. -/
theorem supported_of_validated (presentation : ValidatedPresentation) :
    supported? conclusionKey? presentation.1.rules = true := by
  apply List.all_eq_true.mpr
  intro rule member
  have validIn := rule_isValidIn_of_mem presentation member
  have validShape :=
    RuleSchema.conclusion_hasJudgmentShape_of_validIn validIn
  exact conclusionKey?_isSome_of_hasJudgmentShape
    presentation.1 rule validShape

/-- The generic partial compiler is total on any V2-validated presentation. -/
theorem compile_isSome_of_validated (presentation : ValidatedPresentation) :
    (FiniteRuleIndexCompilation.compile?
      conclusionKey? presentation.1.rules).isSome = true := by
  rw [compile?_isSome_eq_supported?]
  exact supported_of_validated presentation

/-- Run the generic admission boundary on a validated inference
presentation. -/
def admitValidated (presentation : ValidatedPresentation) :
    Option (AdmittedProgram JudgmentKey RuleSchema conclusionKey?) :=
  admitProgram conclusionKey? presentation.1.rules

/-- Validated inference presentations cannot fail the generic admission
boundary. -/
theorem admitValidated_isSome (presentation : ValidatedPresentation) :
    (admitValidated presentation).isSome = true := by
  unfold admitValidated
  rw [admitProgram_isSome_eq_compile?]
  exact compile_isSome_of_validated presentation

/-- Candidate lookup in an admitted validated presentation is exactly the
ordered full-scan semantics. -/
theorem admitted_lookup_eq_full_scan
    (presentation : ValidatedPresentation)
    (admitted : AdmittedProgram JudgmentKey RuleSchema conclusionKey?)
    (sameSource : admitted.source = presentation.1.rules)
    (query : JudgmentKey) :
    lookup query admitted.compiled =
      sourceCandidates conclusionKey? presentation.1.rules query := by
  rw [← sameSource]
  exact lookup_compile?_eq_sourceCandidates
    conclusionKey? admitted.source admitted.compiled
      admitted.compile_eq query

end Mettapedia.GSLT.LanguageDef.InferenceRuleIndexCompilation
