import Mettapedia.Algorithms.Compression.SourceFrame

/-!
# A source-admission counterexample and an abstraction break-even check

`plainPorts` models the existing `source-library:ports?` test. It rejects a
constructor pattern even when that pattern binds an ordinary consecutive
variable inventory. This is a restriction on the supplied source region, not
a one-feature restriction in the incremental search algorithm.

The structural cost is the atom/expression score used by the source POC.
Four occurrences of the empty-list predicate do not pay for its definition.
These are algorithm-level statements; native controls exercise the same
examples separately, without identifying C execution with Lean reduction.
-/

namespace Mettapedia.Algorithms.Compression.SourceAdmissionCounterexample

open SourceFrame

def plainPorts : List (Term Nat) → Nat → Bool
  | [], _ => true
  | .var actual :: rest, expected => actual == expected && plainPorts rest (expected + 1)
  | _ :: _, _ => false

def bits (text : String) : List Bool :=
  text.toUTF8.data.toList.flatMap fun byte =>
    List.ofFn fun index : Fin 8 => byte.toNat.testBit (7 - index.val)

def symbol (text : String) : Term Nat := .literal (bits "Symbol") (bits text)

def truthArguments : List (Term Nat) :=
  [.expr [symbol "stv", .var 0, .var 1],
   .expr [symbol "stv", .var 2, .var 3]]

theorem plain_variables_admitted : plainPorts [.var 0, .var 1] 0 = true := rfl

theorem constructor_formal_rejected (children : List (Term Nat))
    (rest : List (Term Nat)) (expected : Nat) :
    plainPorts (.expr children :: rest) expected = false := rfl

/-- The head shape used by `Truth_ModusPonens` binds four ordinary variables,
but the old plain-port test rejects it before examining its body. -/
theorem pln_head_counterexample :
    occurrencesList truthArguments = [0, 1, 2, 3] ∧
    plainPorts truthArguments 0 = false := by
  constructor <;> rfl

def nodes : Term Nat → Nat
  | .var _ => 1
  | .literal _ _ => 1
  | .expr children => 1 + (children.map nodes).sum

def emptyTest (argument : Term Nat) : Term Nat :=
  .expr [symbol "==", argument, .expr []]

def call (name : String) (argument : Term Nat) : Term Nat :=
  .expr [symbol name, argument]

def definition (name : String) : Term Nat :=
  .expr [symbol "=", call name (.var 0), emptyTest (.var 0)]

theorem empty_test_nodes : nodes (emptyTest (.var 0)) = 4 := by
  simp [nodes, emptyTest, symbol]
theorem helper_call_nodes (name : String) : nodes (call name (.var 0)) = 3 := by
  simp [nodes, call, symbol]
theorem helper_definition_nodes (name : String) : nodes (definition name) = 9 := by
  simp [nodes, definition, call, emptyTest, symbol]

theorem name_spelling_irrelevant (first second : String) :
    nodes (definition first) = nodes (definition second) ∧
    nodes (call first (.var 0)) = nodes (call second (.var 0)) := by
  simp [helper_definition_nodes, helper_call_nodes]

/-- The four-use candidate measured in PLN grows by five structural nodes,
even when the helper name is free of spelling-length penalties. -/
theorem four_uses_grow_by_five (name : String) :
    nodes (definition name) + 4 * nodes (call name (.var 0)) =
      4 * nodes (emptyTest (.var 0)) + 5 := by
  simp [helper_definition_nodes, helper_call_nodes, empty_test_nodes]

theorem empty_test_break_even (name : String) (uses : Nat) :
    nodes (definition name) + uses * nodes (call name (.var 0)) <
      uses * nodes (emptyTest (.var 0)) ↔ 9 < uses := by
  rw [helper_definition_nodes, helper_call_nodes, empty_test_nodes]
  omega

#print axioms pln_head_counterexample
#print axioms four_uses_grow_by_five
#print axioms empty_test_break_even

end Mettapedia.Algorithms.Compression.SourceAdmissionCounterexample
