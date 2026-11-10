import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationComposition
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationRuleExecution
import Mettapedia.GSLT.Parsing.ConstructorArgumentRouting

/-! # Same-sort argument order can change a valid resource effect

A selection notation that writes its read field before its take field needs
argument routing. Skipping that routing swaps two same-sort arguments; both
resulting firings can pass admission while consuming different occurrence
identities. A correct step checker cannot repair the source lowering error.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.ArgumentControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing.ConstructorArgumentRouting
open Payloads

def readFirstSelection : GrammarRule :=
  { Payloads.dataLanguage.terms[23] with
    syntaxPattern := [.terminal "(", .terminal "selection", .nonTerminal "read",
      .nonTerminal "take", .nonTerminal "make", .terminal ")"] }

theorem read_first_is_not_direct : ¬ DirectOrder readFirstSelection := by decide +kernel

def correct : Selection Nat := ⟨[0], [1], [2]⟩
def swapped : Selection Nat := ⟨[1], [0], [2]⟩
def sourceChildren : List Pattern := [indicesPattern [1], indicesPattern [0], indicesPattern [2]]

theorem routing_restores_declared_order :
    routeRule readFirstSelection sourceChildren =
      some [indicesPattern [0], indicesPattern [1], indicesPattern [2]] := by decide +kernel

theorem routed_selection :
    (routeRule readFirstSelection sourceChildren).bind (fun arguments =>
      readSelection (.apply "TcSelectionData" arguments)) = some correct := by
  rw [routing_restores_declared_order]
  exact readSelection_pattern correct

theorem skipping_routing_changes_selection :
    readSelection (.apply "TcSelectionData" sourceChildren) = some swapped :=
  readSelection_pattern swapped

def atom : Term := .node (.name 7) .nil
def output : Term := .node (.name 8) .nil
def label (index : Nat) : Term := if index = 2 then output else atom

def before : Execution.State := ⟨[], {0, 1}⟩
def rule : RuleInstance Term := ⟨[atom], [atom], [], [], [output]⟩

theorem both_admitted : correct.Valid BindingTrees.action label rule before ∧
    swapped.Valid BindingTrees.action label rule before := by
  constructor
  all_goals
    refine {
      take_distinct := by simp [correct, swapped]
      output_distinct := by simp [correct, swapped]
      take_length := rfl
      read_length := rfl
      outputs := by simp [correct, swapped, label, rule]
      occurrences := ?_
      consistent := ?_
      checks := by simp [rule] }
    · constructor
      all_goals simp [correct, swapped, before, Selection.commit]
    · refine ⟨Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Term.idx, ?_⟩
      intro equation member
      have reflexive : equation = (atom, atom) := by
        simpa [Selection.problem, Selection.equations, correct, swapped, rule, before, label] using member
      subst equation
      rfl

theorem admitted_effects_differ :
    (correct.result label rule before).present = {1, 2} ∧
    (swapped.result label rule before).present = {0, 2} ∧
    (correct.result label rule before).present ≠ (swapped.result label rule before).present := by
  decide +kernel

#print axioms routing_restores_declared_order
#print axioms both_admitted
#print axioms admitted_effects_differ

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.ArgumentControls
