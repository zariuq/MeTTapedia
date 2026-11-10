import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationPayloadGrammar
import Mathlib.Data.Finset.Sort

/-! # Exact rule, selection and configuration payloads

The payloads decode into the existing occurrence calculus representations.
Rule ports, equations and checks keep list order and duplicates. Selections
also retain duplicate identities so ordinary preparation can reject illegal
linear reuse. A configuration's occurrence set has a canonical sorted view;
its reader rejects repeated identities instead of silently coalescing them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Payloads

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing

def listPattern {α : Type} (nilTag consTag : String) (element : α → Pattern) : List α → Pattern
  | [] => .apply nilTag []
  | first :: rest => .apply consTag [element first, listPattern nilTag consTag element rest]

def readList {α : Type} (nilTag consTag : String) (element : Pattern → Option α) :
    Pattern → Option (List α)
  | .apply tag [] => if tag = nilTag then some [] else none
  | .apply tag [first, rest] => if tag = consTag then do
      return (← element first) :: (← readList nilTag consTag element rest)
    else none
  | _ => none

theorem readList_pattern {α : Type} (nilTag consTag : String)
    (encode : α → Pattern) (decode : Pattern → Option α)
    (roundtrip : ∀ value, decode (encode value) = some value) (values : List α) :
    readList nilTag consTag decode (listPattern nilTag consTag encode values) = some values := by
  induction values with
  | nil => simp [listPattern, readList]
  | cons first rest ih => simp [listPattern, readList, roundtrip, ih]

def termsPattern := listPattern "TcTermsNil" "TcTermsCons" termPattern
def readTerms := readList "TcTermsNil" "TcTermsCons" readTerm

theorem readTerms_pattern (terms : List Term) : readTerms (termsPattern terms) = some terms :=
  readList_pattern _ _ _ _ readTerm_pattern terms

def equationPattern (equation : Equation Term) : Pattern :=
  .apply "TcEquationData" [termPattern equation.1, termPattern equation.2]

def readEquation : Pattern → Option (Equation Term)
  | .apply "TcEquationData" [left, right] => do return (← readTerm left, ← readTerm right)
  | _ => none

theorem readEquation_pattern (equation : Equation Term) :
    readEquation (equationPattern equation) = some equation := by
  rcases equation with ⟨left, right⟩
  simp [readEquation, equationPattern, readTerm_pattern]

def equationsPattern := listPattern "TcEquationsNil" "TcEquationsCons" equationPattern
def readEquations := readList "TcEquationsNil" "TcEquationsCons" readEquation

theorem readEquations_pattern (equations : EquationStore Term) :
    readEquations (equationsPattern equations) = some equations :=
  readList_pattern _ _ _ _ readEquation_pattern equations

def checkPattern : Check Term → Pattern
  | .equal left right => .apply "TcEqual" [termPattern left, termPattern right]
  | .absent term => .apply "TcAbsent" [termPattern term]
  | .count term count => .apply "TcCount" [termPattern term, indexPattern count]

def readCheck : Pattern → Option (Check Term)
  | .apply "TcEqual" [left, right] => do return .equal (← readTerm left) (← readTerm right)
  | .apply "TcAbsent" [term] => Check.absent <$> readTerm term
  | .apply "TcCount" [term, count] => do return .count (← readTerm term) (← readIndex count)
  | _ => none

theorem readCheck_pattern (check : Check Term) : readCheck (checkPattern check) = some check := by
  cases check <;> simp [checkPattern, readCheck, readTerm_pattern, readIndex_pattern]

def checksPattern := listPattern "TcChecksNil" "TcChecksCons" checkPattern
def readChecks := readList "TcChecksNil" "TcChecksCons" readCheck

theorem readChecks_pattern (checks : List (Check Term)) : readChecks (checksPattern checks) = some checks :=
  readList_pattern _ _ _ _ readCheck_pattern checks

def rulePattern (rule : RuleInstance Term) : Pattern := .apply "TcRuleData"
  [termsPattern rule.take, termsPattern rule.read, equationsPattern rule.tell,
    checksPattern rule.checks, termsPattern rule.produce]

def readRule : Pattern → Option (RuleInstance Term)
  | .apply "TcRuleData" [take, read, tell, checks, make] => do
      return ⟨← readTerms take, ← readTerms read, ← readEquations tell,
        ← readChecks checks, ← readTerms make⟩
  | _ => none

theorem readRule_pattern (rule : RuleInstance Term) : readRule (rulePattern rule) = some rule := by
  cases rule
  simp [rulePattern, readRule, readTerms_pattern, readEquations_pattern, readChecks_pattern]

def indicesPattern := listPattern "TcIndicesNil" "TcIndicesCons" indexPattern
def readIndices := readList "TcIndicesNil" "TcIndicesCons" readIndex

theorem readIndices_pattern (indices : List Nat) : readIndices (indicesPattern indices) = some indices :=
  readList_pattern _ _ _ _ readIndex_pattern indices

def selectionPattern (selection : Selection Nat) : Pattern := .apply "TcSelectionData"
  [indicesPattern selection.taken, indicesPattern selection.read, indicesPattern selection.made]

def readSelection : Pattern → Option (Selection Nat)
  | .apply "TcSelectionData" [take, read, make] => do
      return ⟨← readIndices take, ← readIndices read, ← readIndices make⟩
  | _ => none

theorem readSelection_pattern (selection : Selection Nat) :
    readSelection (selectionPattern selection) = some selection := by
  cases selection
  simp [readSelection, selectionPattern, readIndices_pattern]

def configurationPattern (configuration : Configuration Term Nat) : Pattern :=
  .apply "TcConfigurationData" [equationsPattern configuration.equations,
    indicesPattern (configuration.present.sort (· ≤ ·))]

def readConfiguration : Pattern → Option (Configuration Term Nat)
  | .apply "TcConfigurationData" [knowledge, occurrences] => do
      let equations ← readEquations knowledge
      let present ← readIndices occurrences
      if present.Nodup then some ⟨equations, present.toFinset⟩ else none
  | _ => none

theorem readConfiguration_pattern (configuration : Configuration Term Nat) :
    readConfiguration (configurationPattern configuration) = some configuration := by
  cases configuration
  simp [readConfiguration, configurationPattern, readEquations_pattern, readIndices_pattern]

def rulePresentation : ExactPresentation.Presentation
    (fun _ : Unit => RuleInstance Term) (fun _ => Pattern) where
  key := ⟨"tcalc.rule-instance", 1⟩
  view := rulePattern
  expand := readRule
  expand_view := readRule_pattern

def selectionPresentation : ExactPresentation.Presentation
    (fun _ : Unit => Selection Nat) (fun _ => Pattern) where
  key := ⟨"tcalc.occurrence-selection", 1⟩
  view := selectionPattern
  expand := readSelection
  expand_view := readSelection_pattern

def configurationPresentation : ExactPresentation.Presentation
    (fun _ : Unit => Configuration Term Nat) (fun _ => Pattern) where
  key := ⟨"tcalc.occurrence-configuration", 1⟩
  view := configurationPattern
  expand := readConfiguration
  expand_view := readConfiguration_pattern

theorem duplicate_selection_is_preserved :
    readSelection (selectionPattern ⟨[4, 4], [8, 8], [9]⟩) =
      some ⟨[4, 4], [8, 8], [9]⟩ := readSelection_pattern _

theorem repeated_present_identity_refused : readConfiguration
    (.apply "TcConfigurationData" [equationsPattern [], indicesPattern [4, 4]]) = none := by
  simp [readConfiguration, readEquations_pattern, readIndices_pattern]

theorem occurrence_order_normalizes : readConfiguration
    (.apply "TcConfigurationData" [equationsPattern [], indicesPattern [9, 4]]) =
      readConfiguration (.apply "TcConfigurationData" [equationsPattern [], indicesPattern [4, 9]]) := by
  simp [readConfiguration, readEquations_pattern, readIndices_pattern, Finset.pair_comm]

theorem duplicate_equations_are_preserved (equation : Equation Term) :
    readEquations (equationsPattern [equation, equation]) = some [equation, equation] :=
  readEquations_pattern _

theorem unknown_guard_refused : readCheck (.apply "TcUnknownGuard" [termPattern (.idx 0)]) = none := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Payloads
