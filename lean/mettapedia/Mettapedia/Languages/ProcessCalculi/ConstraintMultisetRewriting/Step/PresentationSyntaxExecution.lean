import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationSyntaxSource
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationRuleExecution

/-! # Scalar rule documents executing through the occurrence calculus

The source profile parses rules and explicit occurrence selections. A frame's
occurrence labels and source configuration are interpretation parameters.
Erased source trees feed the existing structural execution interpreter; its
admission obligation is the actual occurrence calculus's obligation. Parsed
syntax alone never issues permission. State-document and whole-language
assembly are separate from this rule/selection source interpretation.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.SyntaxExecution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing
open PresentationExprSemantics LanguageDefGrammarAlgebra
open Payloads SyntaxSource

/-- Apply the existing structural execution interpretation to two retained
source trees. Configuration encoding remains the exact existing codec. -/
def Executes (label : Nat → Term) (before after : Execution.State)
    (ruleTree selectionTree : CST) : Prop :=
  ∃ ruleData selectionData,
    LanguageDefScalarStructural.tree? ruleTree = some ruleData ∧
    LanguageDefScalarStructural.tree? selectionTree = some selectionData ∧
    Execution.Executes label ruleData selectionData
      (configurationPattern before) (configurationPattern after)

theorem executes_iff_decoded (label : Nat → Term) (before after : Execution.State)
    (ruleTree selectionTree : CST) :
    Executes label before after ruleTree selectionTree ↔
      ∃ (rule : RuleInstance Term) (selection : Selection Nat),
        readParsed "TcRule" ruleTree = some rule ∧
        readParsed "TcSelection" selectionTree = some selection ∧
        selection.Valid BindingTrees.action label rule before ∧
        selection.result label rule before = after := by
  constructor
  · rintro ⟨ruleData, selectionData, erasedRule, erasedSelection,
      rule, selection, before', after', decodedRule, decodedSelection, decodedBefore, decodedAfter,
      admitted, result⟩
    have sameBefore : before = before' := Option.some.inj
      ((readConfiguration_pattern before).symm.trans decodedBefore)
    have sameAfter : after = after' := Option.some.inj
      ((readConfiguration_pattern after).symm.trans decodedAfter)
    subst before'
    subst after'
    refine ⟨rule, selection, ?_, ?_, (Execution.admits_iff label rule selection before).mp admitted, result⟩
    · change (LanguageDefScalarStructural.tree? ruleTree).bind readRule = some rule
      rw [erasedRule]
      exact decodedRule
    · change (LanguageDefScalarStructural.tree? selectionTree).bind readSelection = some selection
      rw [erasedSelection]
      exact decodedSelection
  · rintro ⟨rule, selection, decodedRule, decodedSelection, admitted, result⟩
    cases erasedRule : LanguageDefScalarStructural.tree? ruleTree with
    | none => simp [readParsed, erasedRule] at decodedRule
    | some ruleData =>
        cases erasedSelection : LanguageDefScalarStructural.tree? selectionTree with
        | none => simp [readParsed, erasedSelection] at decodedSelection
        | some selectionData =>
            refine ⟨ruleData, selectionData, erasedRule, erasedSelection, rule, selection,
              before, after, ?_, ?_, readConfiguration_pattern before, readConfiguration_pattern after,
              (Execution.admits_iff label rule selection before).mpr admitted, result⟩
            · change (LanguageDefScalarStructural.tree? ruleTree).bind readRule = some rule at decodedRule
              rw [erasedRule] at decodedRule
              exact decodedRule
            · change (LanguageDefScalarStructural.tree? selectionTree).bind readSelection = some selection at decodedSelection
              rw [erasedSelection] at decodedSelection
              exact decodedSelection

/-- Whole-input source admission is kept separate from step admission. -/
def Fires (label : Nat → Term) (before after : Execution.State)
    (ruleInput selectionInput : List Nat) (ruleTree selectionTree : CST) : Prop :=
  Nonempty (Source "TcRule" ruleInput ruleTree) ∧
  Nonempty (Source "TcSelection" selectionInput selectionTree) ∧
  Executes label before after ruleTree selectionTree

/-- Once actual source trees decode, both directions of execution are governed
by the original occurrence rule's validity and result, with all guards intact. -/
theorem fires_iff (label : Nat → Term) (before after : Execution.State)
    {ruleInput selectionInput : List Nat} {ruleTree selectionTree : CST}
    (ruleSource : Source "TcRule" ruleInput ruleTree)
    (selectionSource : Source "TcSelection" selectionInput selectionTree)
    (rule : RuleInstance Term) (selection : Selection Nat)
    (decodedRule : readParsed "TcRule" ruleTree = some rule)
    (decodedSelection : readParsed "TcSelection" selectionTree = some selection) :
    Fires label before after ruleInput selectionInput ruleTree selectionTree ↔
      selection.Valid BindingTrees.action label rule before ∧
      selection.result label rule before = after := by
  constructor
  · rintro ⟨_, _, executed⟩
    obtain ⟨otherRule, otherSelection, otherRuleDecoded, otherSelectionDecoded, admitted, result⟩ :=
      (executes_iff_decoded label before after ruleTree selectionTree).mp executed
    have sameRule : otherRule = rule := Option.some.inj (otherRuleDecoded.symm.trans decodedRule)
    have sameSelection : otherSelection = selection := Option.some.inj
      (otherSelectionDecoded.symm.trans decodedSelection)
    subst otherRule
    subst otherSelection
    exact ⟨admitted, result⟩
  · rintro ⟨admitted, result⟩
    exact ⟨⟨ruleSource⟩, ⟨selectionSource⟩,
      (executes_iff_decoded label before after ruleTree selectionTree).mpr
        ⟨rule, selection, decodedRule, decodedSelection, admitted, result⟩⟩


/-- Parser selection is explicit and cannot be bypassed by step admission. -/
def SelectedFires (keepRule keepSelection : CST → Bool)
    (ruleForest selectionForest : ClassAwarePackedForest.Forest)
    (label : Nat → Term) (before after : Execution.State)
    (ruleInput selectionInput : List Nat) (ruleTree selectionTree : CST) : Prop :=
  Selected keepRule ruleForest "TcRule" ruleInput ruleTree ∧
  Selected keepSelection selectionForest "TcSelection" selectionInput selectionTree ∧
  Executes label before after ruleTree selectionTree

theorem selected_fires_iff (keepRule keepSelection : CST → Bool)
    (ruleForest selectionForest : ClassAwarePackedForest.Forest)
    (label : Nat → Term) (before after : Execution.State)
    {ruleInput selectionInput : List Nat} {ruleTree selectionTree : CST}
    (selectedRule : Selected keepRule ruleForest "TcRule" ruleInput ruleTree)
    (selectedSelection : Selected keepSelection selectionForest "TcSelection" selectionInput selectionTree)
    (rule : RuleInstance Term) (selection : Selection Nat)
    (decodedRule : readParsed "TcRule" ruleTree = some rule)
    (decodedSelection : readParsed "TcSelection" selectionTree = some selection) :
    SelectedFires keepRule keepSelection ruleForest selectionForest label before after
      ruleInput selectionInput ruleTree selectionTree ↔
      selection.Valid BindingTrees.action label rule before ∧
      selection.result label rule before = after := by
  obtain ⟨ruleSource⟩ := packed_reflects_source ruleForest "TcRule" ruleInput ruleTree selectedRule.1
  obtain ⟨selectionSource⟩ := packed_reflects_source selectionForest "TcSelection"
    selectionInput selectionTree selectedSelection.1
  have bridge := fires_iff label before after ruleSource selectionSource rule selection
    decodedRule decodedSelection
  constructor
  · rintro ⟨_, _, executed⟩
    exact bridge.mp ⟨⟨ruleSource⟩, ⟨selectionSource⟩, executed⟩
  · intro valid
    exact ⟨selectedRule, selectedSelection, (bridge.mpr valid).2.2⟩

def ruleInput (rule : RuleInstance Term) : List Nat :=
  printTokens ((syntaxAlgebra Payloads.rules).evaluate (ruleRoute rule)).tokens

def selectionInput (selection : Selection Nat) : List Nat :=
  printTokens ((syntaxAlgebra Payloads.rules).evaluate (selectionRoute selection)).tokens

theorem printed_rule_source (rule : RuleInstance Term) :
    ∃ tree, Nonempty (Source "TcRule" (ruleInput rule) tree) ∧
      readParsed "TcRule" tree = some rule := by
  obtain ⟨tree, source, decoded⟩ := printed_route_source (ruleRoute rule)
  have interpreted := decode_route (ruleRoute rule)
  rw [ruleRoute_tree] at interpreted
  change readRule (rulePattern rule) = some (interpret interpretation (ruleRoute rule)) at interpreted
  rw [readRule_pattern] at interpreted
  exact ⟨tree, source, decoded.trans (congrArg some (Option.some.inj interpreted).symm)⟩

theorem printed_selection_source (selection : Selection Nat) :
    ∃ tree, Nonempty (Source "TcSelection" (selectionInput selection) tree) ∧
      readParsed "TcSelection" tree = some selection := by
  obtain ⟨tree, source, decoded⟩ := printed_route_source (selectionRoute selection)
  have interpreted := decode_route (selectionRoute selection)
  rw [selectionRoute_tree] at interpreted
  change readSelection (selectionPattern selection) =
    some (interpret interpretation (selectionRoute selection)) at interpreted
  rw [readSelection_pattern] at interpreted
  exact ⟨tree, source, decoded.trans (congrArg some (Option.some.inj interpreted).symm)⟩

/-- Every authorized occurrence transition has actual scalar source witnesses.
This law does not equate source parsing with admission or assert parser uniqueness. -/
theorem authorized_has_source (label : Nat → Term) (before after : Execution.State)
    (rule : RuleInstance Term) (selection : Selection Nat)
    (admitted : selection.Valid BindingTrees.action label rule before)
    (result : selection.result label rule before = after) :
    ∃ ruleTree selectionTree,
      Fires label before after (ruleInput rule) (selectionInput selection) ruleTree selectionTree := by
  obtain ⟨ruleTree, ⟨ruleSource⟩, decodedRule⟩ := printed_rule_source rule
  obtain ⟨selectionTree, ⟨selectionSource⟩, decodedSelection⟩ := printed_selection_source selection
  exact ⟨ruleTree, selectionTree,
    (fires_iff label before after ruleSource selectionSource rule selection decodedRule decodedSelection).mpr
      ⟨admitted, result⟩⟩

namespace Controls
open Execution.Controls

theorem source_linear_firing : ∃ ruleTree selectionTree,
    Fires label before after (ruleInput rule) (selectionInput selection) ruleTree selectionTree :=
  authorized_has_source label before after rule selection valid rfl

/-- A refused rule still has valid syntax. For every retained parse decoding
to it, the language's absence guard prevents execution to every target. -/
theorem parsed_refusal (target : Execution.State) {ruleTree selectionTree : CST}
    (decodedRule : readParsed "TcRule" ruleTree = some refusedRule)
    (decodedSelection : readParsed "TcSelection" selectionTree = some selection) :
    ¬ Executes label before target ruleTree selectionTree := by
  intro executed
  obtain ⟨otherRule, otherSelection, readRule, readSelection, admitted, _⟩ :=
    (executes_iff_decoded label before target ruleTree selectionTree).mp executed
  have sameRule : otherRule = refusedRule := Option.some.inj (readRule.symm.trans decodedRule)
  have sameSelection : otherSelection = selection := Option.some.inj
    (readSelection.symm.trans decodedSelection)
  subst otherRule
  subst otherSelection
  exact refused_rule_not_admitted ((Execution.admits_iff label refusedRule selection before).mpr admitted)

end Controls

#print axioms executes_iff_decoded
#print axioms fires_iff
#print axioms selected_fires_iff
#print axioms authorized_has_source
#print axioms Controls.source_linear_firing
#print axioms Controls.parsed_refusal

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.SyntaxExecution
