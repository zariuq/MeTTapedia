import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationRulePayloads

/-! # Authored construction routes for rules and occurrence data

All constructor positions belong to the `Tcalc.Syntax` compilation. The generic
grammar algebra supplies tokens and source derivations; independent codecs
recover the existing calculus records from the resulting syntax trees.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Payloads

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework
open Mettapedia.GSLT.Parsing.LanguageDefGrammarAlgebra
open Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted

def listRoute {α : Type} {elementSort listSort : String}
    (nilOp : Operation rules [] listSort)
    (consOp : Operation rules [elementSort, listSort] listSort)
    (element : α → Route elementSort) : List α → Route listSort
  | [] => .apply nilOp .nil
  | first :: rest => .apply consOp (.cons (element first) (.cons (listRoute nilOp consOp element rest) .nil))

theorem listRoute_tree {α : Type} {elementSort listSort : String}
    (nilOp : Operation rules [] listSort)
    (consOp : Operation rules [elementSort, listSort] listSort)
    (element : α → Route elementSort) (encode : α → Pattern) (nilTag consTag : String)
    (nilTree : ((syntaxAlgebra rules).evaluate (.apply nilOp .nil)).tree = .apply nilTag [])
    (consTree : ∀ head tail, ((syntaxAlgebra rules).evaluate
      (.apply consOp (.cons head (.cons tail .nil)))).tree =
        .apply consTag [((syntaxAlgebra rules).evaluate head).tree,
          ((syntaxAlgebra rules).evaluate tail).tree])
    (elementTree : ∀ value, ((syntaxAlgebra rules).evaluate (element value)).tree = encode value)
    (values : List α) : ((syntaxAlgebra rules).evaluate (listRoute nilOp consOp element values)).tree =
      listPattern nilTag consTag encode values := by
  induction values with
  | nil => exact nilTree
  | cons first rest ih =>
    rw [listRoute, consTree, elementTree, ih]
    rfl

def termsRoute : List Term → Route "TcTerms" :=
  listRoute (.at ⟨10, by decide +kernel⟩) (.at ⟨11, by decide +kernel⟩) termRoute

theorem termsRoute_tree (values : List Term) :
    ((syntaxAlgebra rules).evaluate (termsRoute values)).tree = termsPattern values :=
  listRoute_tree _ _ termRoute termPattern _ _ rfl (fun _ _ => rfl) termRoute_tree values

def equationRoute (equation : Equation Term) : Route "TcEquation" :=
  .apply (.at ⟨12, by decide +kernel⟩)
    (.cons (termRoute equation.1) (.cons (termRoute equation.2) .nil))

theorem equationRoute_tree (equation : Equation Term) :
    ((syntaxAlgebra rules).evaluate (equationRoute equation)).tree = equationPattern equation := by
  change Pattern.apply "TcEquationData" [((syntaxAlgebra rules).evaluate (termRoute equation.1)).tree,
    ((syntaxAlgebra rules).evaluate (termRoute equation.2)).tree] = _
  rw [termRoute_tree, termRoute_tree]
  rfl

def equationsRoute : EquationStore Term → Route "TcEquations" :=
  listRoute (.at ⟨13, by decide +kernel⟩) (.at ⟨14, by decide +kernel⟩) equationRoute

theorem equationsRoute_tree (values : EquationStore Term) :
    ((syntaxAlgebra rules).evaluate (equationsRoute values)).tree = equationsPattern values :=
  listRoute_tree _ _ equationRoute equationPattern _ _ rfl (fun _ _ => rfl) equationRoute_tree values

def checkRoute : Check Term → Route "TcCheck"
  | .equal left right => .apply (.at ⟨15, by decide +kernel⟩)
      (.cons (termRoute left) (.cons (termRoute right) .nil))
  | .absent term => .apply (.at ⟨16, by decide +kernel⟩) (.cons (termRoute term) .nil)
  | .count term count => .apply (.at ⟨17, by decide +kernel⟩)
      (.cons (termRoute term) (.cons (indexRoute count) .nil))

theorem checkRoute_tree (check : Check Term) :
    ((syntaxAlgebra rules).evaluate (checkRoute check)).tree = checkPattern check := by
  cases check with
  | equal left right =>
    change Pattern.apply "TcEqual" [((syntaxAlgebra rules).evaluate (termRoute left)).tree,
      ((syntaxAlgebra rules).evaluate (termRoute right)).tree] = _
    rw [termRoute_tree, termRoute_tree]
    rfl
  | absent term =>
    change Pattern.apply "TcAbsent" [((syntaxAlgebra rules).evaluate (termRoute term)).tree] = _
    rw [termRoute_tree]
    rfl
  | count term count =>
    change Pattern.apply "TcCount" [((syntaxAlgebra rules).evaluate (termRoute term)).tree,
      ((syntaxAlgebra rules).evaluate (indexRoute count)).tree] = _
    rw [termRoute_tree, indexRoute_tree]
    rfl

def checksRoute : List (Check Term) → Route "TcChecks" :=
  listRoute (.at ⟨18, by decide +kernel⟩) (.at ⟨19, by decide +kernel⟩) checkRoute

theorem checksRoute_tree (values : List (Check Term)) :
    ((syntaxAlgebra rules).evaluate (checksRoute values)).tree = checksPattern values :=
  listRoute_tree _ _ checkRoute checkPattern _ _ rfl (fun _ _ => rfl) checkRoute_tree values

def ruleRoute (rule : RuleInstance Term) : Route "TcRule" :=
  .apply (.at ⟨20, by decide +kernel⟩)
    (.cons (termsRoute rule.take) (.cons (termsRoute rule.read) (.cons (equationsRoute rule.tell)
      (.cons (checksRoute rule.checks) (.cons (termsRoute rule.produce) .nil)))))

theorem ruleRoute_tree (rule : RuleInstance Term) :
    ((syntaxAlgebra rules).evaluate (ruleRoute rule)).tree = rulePattern rule := by
  change Pattern.apply "TcRuleData" [((syntaxAlgebra rules).evaluate (termsRoute rule.take)).tree,
    ((syntaxAlgebra rules).evaluate (termsRoute rule.read)).tree,
    ((syntaxAlgebra rules).evaluate (equationsRoute rule.tell)).tree,
    ((syntaxAlgebra rules).evaluate (checksRoute rule.checks)).tree,
    ((syntaxAlgebra rules).evaluate (termsRoute rule.produce)).tree] = _
  rw [termsRoute_tree, termsRoute_tree, equationsRoute_tree, checksRoute_tree, termsRoute_tree]
  rfl

def indicesRoute : List Nat → Route "TcIndices" :=
  listRoute (.at ⟨21, by decide +kernel⟩) (.at ⟨22, by decide +kernel⟩) indexRoute

theorem indicesRoute_tree (values : List Nat) :
    ((syntaxAlgebra rules).evaluate (indicesRoute values)).tree = indicesPattern values :=
  listRoute_tree _ _ indexRoute indexPattern _ _ rfl (fun _ _ => rfl) indexRoute_tree values

def selectionRoute (selection : Selection Nat) : Route "TcSelection" :=
  .apply (.at ⟨23, by decide +kernel⟩) (.cons (indicesRoute selection.taken)
    (.cons (indicesRoute selection.read) (.cons (indicesRoute selection.made) .nil)))

theorem selectionRoute_tree (selection : Selection Nat) :
    ((syntaxAlgebra rules).evaluate (selectionRoute selection)).tree = selectionPattern selection := by
  change Pattern.apply "TcSelectionData" [((syntaxAlgebra rules).evaluate (indicesRoute selection.taken)).tree,
    ((syntaxAlgebra rules).evaluate (indicesRoute selection.read)).tree,
    ((syntaxAlgebra rules).evaluate (indicesRoute selection.made)).tree] = _
  rw [indicesRoute_tree, indicesRoute_tree, indicesRoute_tree]
  rfl

def configurationRoute (configuration : Configuration Term Nat) : Route "TcConfiguration" :=
  .apply (.at ⟨24, by decide +kernel⟩) (.cons (equationsRoute configuration.equations)
    (.cons (indicesRoute (configuration.present.sort (· ≤ ·))) .nil))

theorem configurationRoute_tree (configuration : Configuration Term Nat) :
    ((syntaxAlgebra rules).evaluate (configurationRoute configuration)).tree =
      configurationPattern configuration := by
  change Pattern.apply "TcConfigurationData" [
    ((syntaxAlgebra rules).evaluate (equationsRoute configuration.equations)).tree,
    ((syntaxAlgebra rules).evaluate (indicesRoute (configuration.present.sort (· ≤ ·)))).tree] = _
  rw [equationsRoute_tree, indicesRoute_tree]
  rfl

theorem rule_printed_derivation (rule : RuleInstance Term) :
    GrammarDerives.Derives dataLanguage "TcRule"
      ((syntaxAlgebra rules).evaluate (ruleRoute rule)).tokens (rulePattern rule) := by
  simpa only [ruleRoute_tree] using evaluate_source_derives data_compiles (ruleRoute rule)

theorem selection_printed_derivation (selection : Selection Nat) :
    GrammarDerives.Derives dataLanguage "TcSelection"
      ((syntaxAlgebra rules).evaluate (selectionRoute selection)).tokens (selectionPattern selection) := by
  simpa only [selectionRoute_tree] using evaluate_source_derives data_compiles (selectionRoute selection)

theorem configuration_printed_derivation (configuration : Configuration Term Nat) :
    GrammarDerives.Derives dataLanguage "TcConfiguration"
      ((syntaxAlgebra rules).evaluate (configurationRoute configuration)).tokens
      (configurationPattern configuration) := by
  simpa only [configurationRoute_tree] using evaluate_source_derives data_compiles (configurationRoute configuration)

theorem rule_printed_readback (rule : RuleInstance Term) :
    readRule ((syntaxAlgebra rules).evaluate (ruleRoute rule)).tree = some rule := by
  rw [ruleRoute_tree, readRule_pattern]

theorem selection_printed_readback (selection : Selection Nat) :
    readSelection ((syntaxAlgebra rules).evaluate (selectionRoute selection)).tree = some selection := by
  rw [selectionRoute_tree, readSelection_pattern]

theorem configuration_printed_readback (configuration : Configuration Term Nat) :
    readConfiguration ((syntaxAlgebra rules).evaluate (configurationRoute configuration)).tree =
      some configuration := by
  rw [configurationRoute_tree, readConfiguration_pattern]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Payloads
