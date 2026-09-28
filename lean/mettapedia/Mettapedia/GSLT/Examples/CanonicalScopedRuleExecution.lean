import Mettapedia.OSLF.Syntax.CanonicalScopedRuleExecution
import Mettapedia.GSLT.Examples.ScopedLamCongExecution

/-!
# The authored lambda rule through checked canonical execution

The actual LamCong declaration elaborates to one explicitly scoped premise.
Its full open-variable firing survives the canonical executor. A premise
whose target escapes its local binder is rejected before execution.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Examples.CanonicalScopedRuleExecution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.Binding.CanonicalScopedRuleExecution
open Mettapedia.GSLT.Examples.ScopedLamCongExecution
open Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise

/-- The checked canonical route returns the exact authored LamCong firing
list, including the selected beta-child ordinal and contextual assignments. -/
theorem lamCong_compiled_firings :
    applyCompiledRule? betaOracle RelationEnv.empty language
      lamCongRule wrappedRedex =
      some (applyRuleWithOracle betaOracle RelationEnv.empty language
        0 lamCongRule wrappedRedex) := by
  exact applyCompiledRule?_eq betaOracle RelationEnv.empty language
    lamCongRule wrappedRedex [.step localStep] lamCong_premise_compiles

/-- The resulting open beta reduct retains the lambda-bound variable. -/
theorem lamCong_compiled_open_result :
    ∃ firings firing,
      applyCompiledRule? betaOracle RelationEnv.empty language
        lamCongRule wrappedRedex = some firings ∧
      firing ∈ firings ∧ firing.target = wrappedTarget ∧
      firing.history.length = 1 := by
  obtain ⟨firing, selected, targetEq, historyLength⟩ :=
    lamCong_executes_open
  exact ⟨_, firing, lamCong_compiled_firings,
    selected, targetEq, historyLength⟩

/-- The same authored local-binder premise compiles in a context with an
additional ambient term variable. The equality holds for every source and
every supplied oracle, including oracles with repeated equal outcomes. -/
theorem lamCong_compiled_in_ambient
    {Evidence : Type} (oracle : StepOracle Evidence)
    (source : Pattern) :
    applyCompiledRuleAt? oracle RelationEnv.empty language lamCongRule
      [.base "Term"] source =
      some (applyRuleWithOracle oracle RelationEnv.empty language
        1 lamCongRule source) := by
  have compiled :
      compileRulePremisesAt? language lamCongRule [.base "Term"] =
        some [.step localStep] := by
    decide +kernel
  exact applyCompiledRuleAt?_eq oracle RelationEnv.empty language
    lamCongRule [.base "Term"] source [.step localStep] compiled

private def escapingRule : RewriteRule :=
  { lamCongRule with
    premises := [.scopedStep { localStep with target := .bvar 1 }] }

/-- At the rule root, index one escapes the premise's sole local binder.
Rejection is distinct from an empty firing. -/
theorem escaping_premise_rejected :
    compileRulePremises? language escapingRule = none := by
  decide +kernel

theorem escaping_premise_has_no_compiled_execution :
    applyCompiledRule? betaOracle RelationEnv.empty language
      escapingRule wrappedRedex = none := by
  exact applyCompiledRule?_rejected betaOracle RelationEnv.empty language
    escapingRule wrappedRedex escaping_premise_rejected

/-- In a one-variable ambient context, that same index now refers to the
ambient variable and is admitted. Scope is relative to the stated context. -/
theorem ambient_variable_admitted :
    compileRulePremisesAt? language escapingRule [.base "Term"] =
      some [.step { localStep with target := .bvar 1 }] := by
  decide +kernel

/-- Both declarations of the actual authored lambda language compile in
their original order, with beta nullary and LamCong carrying its binder. -/
theorem lambda_rules_compile :
    compileRuleListAt? language [] language.rewrites.zipIdx =
      some [(betaRule, 0, []),
        (lamCongRule, 1, [.step localStep])] := by
  have betaCompiled :
      compileRulePremisesAt? language betaRule [] = some [] := by
    decide +kernel
  have lamCompiled :
      compileRulePremisesAt? language lamCongRule [] =
        some [.step localStep] := lamCong_premise_compiles
  have listed : language.rewrites.zipIdx =
      [(betaRule, 0), (lamCongRule, 1)] := rfl
  rw [listed]
  simp [compileRuleListAt?, betaCompiled, lamCompiled]

/-- The whole authored language, not just an isolated LamCong declaration,
has an exactly corresponding canonical one-layer execution list. -/
theorem lambda_language_compiled_firings
    {Evidence : Type} (oracle : StepOracle Evidence)
    (source : Pattern) :
    applyCompiledLanguageAt? oracle RelationEnv.empty language [] source =
      some (language.rewrites.zipIdx.flatMap fun (rule, index) =>
        (applyRuleWithOracle oracle RelationEnv.empty language 0 rule
          source).map fun firing => (index, firing)) := by
  exact applyCompiledLanguageAt?_eq oracle RelationEnv.empty language []
    source _ lambda_rules_compile

private def rejectedLanguage : LanguageDef :=
  { language with «rewrites» := [betaRule, escapingRule] }

/-- One bad scoped declaration rejects the entire canonical rule list; it
does not erase the good beta rule and return an apparently valid empty run. -/
theorem rejected_language_compile :
    compileRuleListAt? rejectedLanguage []
      rejectedLanguage.rewrites.zipIdx = none := by
  decide +kernel

theorem rejected_language_execution :
    applyCompiledLanguageAt? betaOracle RelationEnv.empty
      rejectedLanguage [] wrappedRedex = none := by
  simp [applyCompiledLanguageAt?, rejected_language_compile]

#print axioms lamCong_compiled_firings
#print axioms lamCong_compiled_open_result
#print axioms lamCong_compiled_in_ambient
#print axioms escaping_premise_rejected
#print axioms escaping_premise_has_no_compiled_execution
#print axioms ambient_variable_admitted
#print axioms lambda_rules_compile
#print axioms lambda_language_compiled_firings
#print axioms rejected_language_execution

end Mettapedia.GSLT.Examples.CanonicalScopedRuleExecution
