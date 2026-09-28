import Mettapedia.OSLF.MeTTaIL.ScopedRuleExecution
import Mettapedia.OSLF.MeTTaIL.RuleBindingRegression
import Mettapedia.OSLF.MeTTaIL.Canonical
import Mettapedia.OSLF.Syntax.ContextualValueComparison

/-!
# Scoped conditional-rule controls

These authored-rule instances execute the same raw premises and output
patterns as the historical regression, with explicit dependency declarations.
They exercise ambient open values, repeated occurrences at different binder
depths, and a bag rest carrying repeated elements.
-/

namespace Mettapedia.OSLF.MeTTaIL.ScopedRuleRegression

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ScopedRuleExecution
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.Binding.PatternPresentation
open Mettapedia.OSLF.MeTTaIL.RuleBindingRegression

set_option autoImplicit false

def premiseRule : RewriteRule :=
  { premiseOutputRule with
    typeContext := [("X", .term), ("Y", .term)]
    bindings := some { dependencies := [("X", []), ("Y", [])] } }

def premiseLanguage : LanguageDef :=
  { premiseOutputLanguage with rewrites := [premiseRule] }

/-- Declare the constructors and sort used by the same conditional rule. -/
def declaredPremiseLanguage : LanguageDef :=
  { premiseLanguage with
    types := [TypeDecl.plain "Term"]
    terms :=
      [{ label := "f", category := "Term",
         params := [.simple "x" .term],
         syntaxPattern := [.terminal "f", .nonTerminal "x"] },
       { label := "a", category := "Term", params := [],
         syntaxPattern := [.terminal "a"] }] }

#guard declaredPremiseLanguage.validate.isEmpty
#guard bindingDeclarationsValid declaredPremiseLanguage
#guard scopedRewritesExecutable declaredPremiseLanguage

/-- The query produces the ambient variable, and the RHS binder weakens it. -/
theorem open_premise_output_keeps_ambient_variable :
    applyRuleAt RelationEnv.empty premiseLanguage 1 premiseRule
      (.apply "f" [.bvar 0]) = [.lambda none (.bvar 1)] := by
  decide +kernel

/-- The language-level scoped step uses the actual authored rewrite list. -/
theorem open_language_step_keeps_ambient_variable :
    rewriteStepAt RelationEnv.empty premiseLanguage 1 (.apply "f" [.bvar 0]) =
      [.lambda none (.bvar 1)] := by
  decide +kernel

theorem declared_language_step_keeps_ambient_variable :
    rewriteStepAt RelationEnv.empty declaredPremiseLanguage 1
      (.apply "f" [.bvar 0]) = [.lambda none (.bvar 1)] := by
  decide +kernel

/-- The concrete authored conditional step agrees with the typed occurrence
calculation at its premise-produced output. The general comparison is
`instantiateValue?_erase_bind`; this instance also exercises the actual
language rewrite list and premise producer. -/
theorem declared_step_has_typed_open_output :
    ∃ output : Pattern,
      instantiateValue?
        (erasedValue [] 1
          (Mettapedia.OSLF.Binding.Term.var
            (varOfFin (⟨0, by decide⟩ : Fin 1))))
        1 1 [] = some output ∧
      rewriteStepAt RelationEnv.empty declaredPremiseLanguage 1
        (.apply "f" [.bvar 0]) = [.lambda none output] := by
  exact ⟨.bvar 1, open_ambient_value_below_binder,
    declared_language_step_keeps_ambient_variable⟩

/-- Closed output follows the same path and keeps its exact constructor. -/
theorem closed_premise_output_stays_closed :
    applyRuleAt RelationEnv.empty premiseLanguage 0 premiseRule
      (.apply "f" [.apply "a" []]) =
        [.lambda none (.apply "a" [])] := by
  decide +kernel

/-- The old rule path is retained as a concrete record of the capture bug. -/
theorem legacy_output_differs_from_scoped_output :
    applyRuleWithPremisesUsing RelationEnv.empty premiseOutputLanguage
      premiseOutputRule (.apply "f" [.bvar 0]) ≠
    applyRuleAt RelationEnv.empty premiseLanguage 1 premiseRule
      (.apply "f" [.bvar 0]) := by
  rw [open_premise_output_is_captured, open_premise_output_keeps_ambient_variable]
  decide

def missingOutputDependency : RewriteRule :=
  { premiseRule with bindings := some { dependencies := [("X", [])] } }

/-- A premise result with no declared dependency context cannot be inserted. -/
theorem undeclared_output_declines :
    applyRuleAt RelationEnv.empty premiseLanguage 1 missingOutputDependency
      (.apply "f" [.bvar 0]) = [] := by
  decide +kernel

def staleOutputAddress : RewriteRule :=
  { premiseRule with
    bindings := some {
      dependencies := [("X", []), ("Y", [])]
      occurrences := [{ name := "Y", site := .right, path := [1], arguments := [] }] } }

#guard !bindingDeclarationsValid
  { declaredPremiseLanguage with rewrites := [staleOutputAddress] }

def unknownDependencySort : RewriteRule :=
  { premiseRule with
    bindings := some {
      dependencies := [("X", [.base "Undeclared"]), ("Y", [])] } }

-- Structural site checks alone do not authorize an undeclared dependency
-- sort in an authored language.
#guard !bindingDeclarationsValid
  { declaredPremiseLanguage with rewrites := [unknownDependencySort] }

def binderPremiseRule : RewriteRule :=
  { premiseRule with
    premises := [.congruence (.lambda none (.fvar "X")) (.fvar "Y")] }

def binderPremiseLanguage : LanguageDef :=
  { declaredPremiseLanguage with rewrites := [binderPremiseRule] }

-- Structural binding declarations can be valid while a premise opens a local
-- binder that the present root-context premise adapter cannot interpret.
#guard bindingDeclarationsValid binderPremiseLanguage
#guard !scopedRewritesExecutable binderPremiseLanguage

-- Binding declarations enter both canonical renderers. This executable
-- control compares two concrete authored presentations.
#guard Mettapedia.OSLF.MeTTaIL.Canonical.verboseCanonical premiseLanguage !=
  Mettapedia.OSLF.MeTTaIL.Canonical.verboseCanonical
    { premiseLanguage with rewrites := [staleOutputAddress] }
#guard Mettapedia.OSLF.MeTTaIL.Canonical.zone1SharedCore premiseLanguage !=
  Mettapedia.OSLF.MeTTaIL.Canonical.zone1SharedCore
    { premiseLanguage with rewrites := [staleOutputAddress] }

/-- A stale explicit address cannot silently select the root metavariable. -/
theorem stale_address_declines :
    applyRuleAt RelationEnv.empty premiseLanguage 1 staleOutputAddress
      (.apply "f" [.bvar 0]) = [] := by
  decide +kernel

def repeatedRule : RewriteRule where
  name := "repeated-contextual-meta"
  typeContext := [("X", .term)]
  premises := []
  left := .apply "pair"
    [.lambda none (.fvar "X"), .multiLambda 2 [] (.fvar "X")]
  right := .lambda none (.fvar "X")
  bindings := some {
    dependencies := [("X", [.term])]
    occurrences :=
      [{ name := "X", site := .left, path := [0, 0], arguments := [.bvar 0] },
       { name := "X", site := .left, path := [1, 0], arguments := [.bvar 1] },
       { name := "X", site := .right, path := [0], arguments := [.bvar 0] }] }

def repeatedLanguage : LanguageDef :=
  { premiseOutputLanguage with rewrites := [repeatedRule] }

/-- Two captures at different binder depths recover one declared body. -/
theorem repeated_contextual_occurrences_agree :
    applyRuleAt RelationEnv.empty repeatedLanguage 0 repeatedRule
      (.apply "pair" [.lambda none (.bvar 0), .multiLambda 2 [] (.bvar 1)]) =
        [.lambda none (.bvar 0)] := by
  decide +kernel

/-- A second occurrence that uses an unselected local binder is rejected. -/
theorem repeated_occurrence_wrong_binder_declines :
    applyRuleAt RelationEnv.empty repeatedLanguage 0 repeatedRule
      (.apply "pair" [.lambda none (.bvar 0), .multiLambda 2 [] (.bvar 0)]) =
        [] := by
  decide +kernel

def nonvariableOutputRule : RewriteRule :=
  { repeatedRule with
    bindings := some {
      dependencies := [("X", [.term])]
      occurrences :=
        [{ name := "X", site := .left, path := [0, 0], arguments := [.bvar 0] },
         { name := "X", site := .left, path := [1, 0], arguments := [.bvar 1] },
         { name := "X", site := .right, path := [0],
           arguments := [.apply "zero" []] }] } }

/-- An output occurrence may supply a general term as its substitution. -/
theorem nonvariable_output_occurrence_substitutes :
    applyRuleAt RelationEnv.empty repeatedLanguage 0 nonvariableOutputRule
      (.apply "pair" [.lambda none (.bvar 0), .multiLambda 2 [] (.bvar 1)]) =
        [.lambda none (.apply "zero" [])] := by
  decide +kernel

def outOfScopeOutputArgument : RewriteRule :=
  { nonvariableOutputRule with
    bindings := some {
      dependencies := [("X", [.term])]
      occurrences :=
        [{ name := "X", site := .left, path := [0, 0], arguments := [.bvar 0] },
         { name := "X", site := .left, path := [1, 0], arguments := [.bvar 1] },
         { name := "X", site := .right, path := [0], arguments := [.bvar 1] }] } }

/-- The RHS is only one binder deep; its argument cannot name binder one. -/
theorem out_of_scope_occurrence_argument_declines :
    applyRuleAt RelationEnv.empty repeatedLanguage 0 outOfScopeOutputArgument
      (.apply "pair" [.lambda none (.bvar 0), .multiLambda 2 [] (.bvar 1)]) =
        [] := by
  decide +kernel

def unresolvedOutputArgument : RewriteRule :=
  { nonvariableOutputRule with
    bindings := some {
      dependencies := [("X", [.term])]
      occurrences :=
        [{ name := "X", site := .left, path := [0, 0], arguments := [.bvar 0] },
         { name := "X", site := .left, path := [1, 0], arguments := [.bvar 1] },
         { name := "X", site := .right, path := [0], arguments := [.fvar "X"] }] } }

/-- Recursive metavariable substitution in occurrence arguments awaits the
general rule interpreter; the current executable profile declines it. -/
theorem unresolved_occurrence_argument_declines :
    applyRuleAt RelationEnv.empty repeatedLanguage 0 unresolvedOutputArgument
      (.apply "pair" [.lambda none (.bvar 0), .multiLambda 2 [] (.bvar 1)]) =
        [] := by
  decide +kernel

def restRule : RewriteRule where
  name := "rest-under-two-binders"
  typeContext := [("rest", .bag .term)]
  premises := []
  left := .lambda none (.collection .hashBag [] (some "rest"))
  right := .lambda none (.lambda none (.collection .hashBag [] (some "rest")))
  bindings := some {
    dependencies := [("rest", [.term])]
    occurrences :=
      [{ name := "rest", site := .left, path := [0, 0], arguments := [.bvar 0] },
       { name := "rest", site := .right, path := [0, 0, 0],
         arguments := [.bvar 1] }] }

def restLanguage : LanguageDef :=
  { premiseOutputLanguage with rewrites := [restRule] }

/-- Every residual bag occurrence is transported, including duplicates. -/
theorem bag_rest_keeps_both_occurrences :
    applyRuleAt RelationEnv.empty restLanguage 0 restRule
      (.lambda none (.collection .hashBag [.bvar 0, .bvar 0] none)) =
        [.lambda none (.lambda none
          (.collection .hashBag [.bvar 1, .bvar 1] none))] := by
  decide +kernel

/-- A symbolic target rest is not an enumerated collection residual. -/
theorem symbolic_target_rest_declines :
    applyRuleAt RelationEnv.empty restLanguage 0 restRule
      (.lambda none (.collection .hashBag [.bvar 0] (some "unknown"))) = [] := by
  decide +kernel

end Mettapedia.OSLF.MeTTaIL.ScopedRuleRegression
