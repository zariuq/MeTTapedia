import Mettapedia.Languages.OCaml.ExpressionOperationalCorrespondence
import Mettapedia.Languages.OCaml.MachineCompleteness

/-! Separating controls for capture, recursive scope, ordered nested patterns,
fault order and function comparison. Tree derivations are written directly. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml.TreeEvaluationControls

def capture : ExpressionTree :=
  .letValue .bind (.integer 7)
    (.letValue .bind (.lambda .bind (.primitive .add [.variableRef 1, .variableRef 0]))
      (.letValue .bind (.integer 99) (.apply (.variableRef 1) (.integer 3))))

theorem capture_evaluates : TreeEvaluates [] [] capture (.ok (.literal (.integer 10))) := by
  exact .letBody .literal rfl (.letBody .lambda rfl (.letBody .literal rfl
    (.application .literal (.variable rfl) (.lambda rfl
      (.primitive (.cons (.cons .nil (.variable rfl)) (.variable rfl)) (.literal (by cbv)))))))

def recursiveIdentity : ExpressionTree :=
  .letRecursive [.lambda .bind (.variableRef 0)] (.apply (.variableRef 0) (.integer 5))

theorem recursive_evaluates : TreeEvaluates [] [] recursiveIdentity (.ok (.literal (.integer 5))) := by
  exact .recursive (.application .literal (.variable rfl) (.recursive rfl rfl (.variable rfl)))

def nestedFallthrough : ExpressionTree :=
  .matchValue (.tuple [.integer 0, .integer 5])
    [(.tuple [.literal (.integer 1), .wildcard], .integer 99), (.tuple [.bind, .bind], .variableRef 0), (.wildcard, .integer 77)]

theorem nested_fallthrough : TreeEvaluates [] [] nestedFallthrough (.ok (.literal (.integer 5))) := by
  exact .matchBody (.tuple (.cons (.cons .nil .literal) .literal) (by cbv)) rfl (.variable rfl)

def failure : ExpressionTree := .matchValue (.integer 0) []

theorem match_fault : TreeEvaluates [] [] failure (.error .matchFailure) :=
  .matchFailure .literal rfl

def rightToLeft : ExpressionTree :=
  .letRecursive [.lambda .bind (.apply (.variableRef 1) (.variableRef 0))]
    (.tuple [.apply (.variableRef 0) (.integer 0), .primitive .divide [.integer 1, .integer 0]])

theorem right_to_left_fault : TreeEvaluates [] [] rightToLeft (.error .divisionByZero) := by
  exact .recursive (.tupleFault (.tailFault (.headFault .nil
    (.primitive (.cons (.cons .nil .literal) .literal) (.fault (by cbv))))))

def shortCircuit : ExpressionTree := .andThen (.boolean false) (.primitive .divide [.integer 1, .integer 0])

theorem short_circuit : TreeEvaluates [] [] shortCircuit (.ok (.literal (.boolean false))) :=
  .andFalse .literal

def functionComparison : ExpressionTree :=
  .primitive .equal [.lambda .bind (.variableRef 0), .lambda .bind (.integer 0)]

theorem function_comparison_fault : TreeEvaluates [] [] functionComparison (.error .functionalComparison) := by
  exact .primitive (.cons (.cons .nil .lambda) .lambda) (.fault (by cbv))

theorem capture_refuses_shadowed_value : ¬ TreeEvaluates [] [] capture (.ok (.literal (.integer 102))) := by
  intro invented
  have first := (ExpressionTree.assembled_literal_iff capture [] (.integer 10)).mpr capture_evaluates
  have second := (ExpressionTree.assembled_literal_iff capture [] (.integer 102)).mpr invented
  cases evaluates_deterministic first second

theorem fallthrough_refuses_failed_clause : ¬ TreeEvaluates [] [] nestedFallthrough (.ok (.literal (.integer 99))) := by
  intro invented
  have first := (ExpressionTree.assembled_literal_iff nestedFallthrough [] (.integer 5)).mpr nested_fallthrough
  have second := (ExpressionTree.assembled_literal_iff nestedFallthrough [] (.integer 99)).mpr invented
  cases evaluates_deterministic first second

theorem first_match_refuses_later_clause : ¬ TreeEvaluates [] [] nestedFallthrough (.ok (.literal (.integer 77))) := by
  intro invented
  have first := (ExpressionTree.assembled_literal_iff nestedFallthrough [] (.integer 5)).mpr nested_fallthrough
  have second := (ExpressionTree.assembled_literal_iff nestedFallthrough [] (.integer 77)).mpr invented
  cases evaluates_deterministic first second

def mutuallyRecursive : ExpressionTree :=
  .letRecursive [.lambda .bind (.apply (.variableRef 1) (.variableRef 0)), .lambda .bind (.variableRef 0)]
    (.apply (.variableRef 1) (.integer 5))

theorem mutual_group_evaluates : TreeEvaluates [] [] mutuallyRecursive (.ok (.literal (.integer 5))) := by
  exact .recursive (.application .literal (.variable rfl) (.recursive rfl rfl
    (.application (.variable rfl) (.variable rfl) (.recursive rfl rfl (.variable rfl)))))

theorem right_to_left_refuses_value (literal : Literal) : ¬ TreeEvaluates [] [] rightToLeft (.ok (.literal literal)) := by
  intro invented
  have first := (ExpressionTree.assembled_fault_iff rightToLeft [] .divisionByZero).mpr right_to_left_fault
  have second := (ExpressionTree.assembled_literal_iff rightToLeft [] literal).mpr invented
  cases evaluates_deterministic first second

#print axioms capture_evaluates
#print axioms recursive_evaluates
#print axioms nested_fallthrough
#print axioms right_to_left_fault
#print axioms function_comparison_fault
#print axioms capture_refuses_shadowed_value
#print axioms fallthrough_refuses_failed_clause
#print axioms first_match_refuses_later_clause
#print axioms mutual_group_evaluates
#print axioms right_to_left_refuses_value

end Mettapedia.Languages.OCaml.TreeEvaluationControls
