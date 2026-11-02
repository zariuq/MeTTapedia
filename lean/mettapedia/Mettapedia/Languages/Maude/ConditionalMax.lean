import Mettapedia.Languages.Maude.Examples
import Mettapedia.Languages.Maude.EquationReduction

/-! Exact source equality evidence for the conditional max equations.
Comparison of Peano numerals uses the authored recursive <= equations;
max's guard is justified by that complete equality derivation.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.Maude.ConditionalMax

def numeral := Examples.numeral "max"
def truth : Term := .app "max.true" []
def falsehood : Term := .app "max.false" []
def le (left right : Term) : Term := .app "max.le" [left, right]
def maximum (left right : Term) : Term := .app "max.max" [left, right]
def successor (source : Term) : Term := .app "max.succ" [source]

def zeroOperator : Operator := ⟨"max.zero", "0", [], "Nat", {constructor := true}⟩
def successorOperator : Operator := ⟨"max.succ", "s", ["Nat"], "Nat", {constructor := true}⟩
def trueOperator : Operator := ⟨"max.true", "true", [], "Bool", {constructor := true}⟩
def falseOperator : Operator := ⟨"max.false", "false", [], "Bool", {constructor := true}⟩
def leOperator : Operator := ⟨"max.le", "_<=_", ["Nat", "Nat"], "Bool", {}⟩
def maxOperator : Operator := ⟨"max.max", "max", ["Nat", "Nat"], "Nat", {}⟩

theorem zero_member : zeroOperator ∈ Examples.conditional.signature.operators := by simp [Examples.conditional, Examples.natData, zeroOperator]
theorem successor_member : successorOperator ∈ Examples.conditional.signature.operators := by simp [Examples.conditional, Examples.natData, successorOperator]
theorem true_member : trueOperator ∈ Examples.conditional.signature.operators := by simp [Examples.conditional, trueOperator]
theorem false_member : falseOperator ∈ Examples.conditional.signature.operators := by simp [Examples.conditional, falseOperator]
theorem le_member : leOperator ∈ Examples.conditional.signature.operators := by simp [Examples.conditional, leOperator]
theorem max_member : maxOperator ∈ Examples.conditional.signature.operators := by simp [Examples.conditional, maxOperator]

theorem numeral_sorted (context : VariableContext) (value : Nat) :
    HasSort Examples.conditional.signature context (numeral value) "Nat" := by
  induction value with
  | zero => exact .app zero_member .nil
  | succ value ih => exact .app successor_member (.cons ih .nil)

theorem truth_sorted (context : VariableContext) : HasSort Examples.conditional.signature context truth "Bool" :=
  .app true_member .nil
theorem falsehood_sorted (context : VariableContext) : HasSort Examples.conditional.signature context falsehood "Bool" :=
  .app false_member .nil

theorem le_sorted {context : VariableContext} {left right : Term}
    (first : HasSort Examples.conditional.signature context left "Nat")
    (second : HasSort Examples.conditional.signature context right "Nat") :
    HasSort Examples.conditional.signature context (le left right) "Bool" := .app le_member (.cons first (.cons second .nil))

theorem max_sorted {context : VariableContext} {left right : Term}
    (first : HasSort Examples.conditional.signature context left "Nat")
    (second : HasSort Examples.conditional.signature context right "Nat") :
    HasSort Examples.conditional.signature context (maximum left right) "Nat" := .app max_member (.cons first (.cons second .nil))

def valuation (left right : Nat) : Valuation := fun name =>
  if name = "N" then numeral left else numeral right

def zeroRow : Row := ⟨"le-zero", [("N", "Nat")], [], le (numeral 0) (.var "N"), truth⟩
def falseRow : Row := ⟨"le-succ-zero", [("N", "Nat")], [], le (successor (.var "N")) (numeral 0), falsehood⟩
def recursiveRow : Row := ⟨"le-succ-succ", [("N", "Nat"), ("M", "Nat")], [],
  le (successor (.var "N")) (successor (.var "M")), le (.var "N") (.var "M")⟩

theorem zeroRow_member : zeroRow ∈ Examples.conditional.equations := by
  simp [zeroRow, Examples.conditional, le, numeral, Examples.numeral, Examples.constant, truth, Examples.binary, Examples.n]
theorem falseRow_member : falseRow ∈ Examples.conditional.equations := by
  simp [falseRow, Examples.conditional, le, successor, numeral, Examples.numeral, Examples.constant, falsehood, Examples.binary, Examples.n]
theorem recursiveRow_member : recursiveRow ∈ Examples.conditional.equations := by
  simp [recursiveRow, Examples.conditional, le, successor, Examples.binary, Examples.n, Examples.m]

private theorem nat_valuation (row : Row) (left right : Nat)
    (sorts : ∀ entry ∈ row.usedContext, entry.2 = "Nat") :
    TypedValuation Examples.conditional.signature [] row.usedContext (valuation left right) := by
  intro name sort found
  obtain ⟨before, after, shape, _⟩ := List.lookup_eq_some_iff.mp found
  have member : (name, sort) ∈ row.usedContext := by simp [shape]
  have sortSame := sorts (name, sort) member
  change sort = "Nat" at sortSame
  subst sort
  unfold valuation
  split <;> exact numeral_sorted [] _

theorem le_zero_step (right : Nat) :
    EquationReduction Examples.conditional [] "Bool" (le (numeral 0) (numeral right)) truth := by
  have used : zeroRow.usedContext = [("N", "Nat")] := by
    simp [zeroRow, Row.usedContext, le, numeral, Examples.numeral, Examples.constant, truth, Term.variables]
  have variableTyped : HasSort Examples.conditional.signature zeroRow.usedContext (.var "N") "Nat" :=
    .var (by simp [used])
  have left : HasSort Examples.conditional.signature zeroRow.usedContext zeroRow.left "Bool" :=
    le_sorted (numeral_sorted _ 0) variableTyped
  have equation := EquationReduction.root (valuation right right) zeroRow_member (by decide_cbv)
    left (truth_sorted _) (nat_valuation zeroRow right right (by simp [used])) (.nil _)
  simpa only [zeroRow, le, numeral, Examples.numeral, Examples.constant, truth, String.reduceAppend,
    Term.substitute, List.map_cons, List.map_nil, valuation, if_true] using equation

theorem le_zero (right : Nat) :
    Equivalent Examples.conditional [] "Bool" (le (numeral 0) (numeral right)) truth :=
  (le_zero_step right).equivalent

theorem le_succ_zero_step (left : Nat) :
    EquationReduction Examples.conditional [] "Bool" (le (numeral (left + 1)) (numeral 0)) falsehood := by
  have used : falseRow.usedContext = [("N", "Nat")] := by
    simp [falseRow, Row.usedContext, le, successor, numeral, Examples.numeral, Examples.constant, falsehood, Term.variables]
  have variableTyped : HasSort Examples.conditional.signature falseRow.usedContext (.var "N") "Nat" :=
    .var (by simp [used])
  have leftTyped : HasSort Examples.conditional.signature falseRow.usedContext falseRow.left "Bool" :=
    le_sorted (.app successor_member (.cons variableTyped .nil)) (numeral_sorted _ 0)
  have equation := EquationReduction.root (valuation left left) falseRow_member (by decide_cbv)
    leftTyped (falsehood_sorted _) (nat_valuation falseRow left left (by simp [used])) (.nil _)
  simpa only [falseRow, le, successor, numeral, Examples.numeral, Examples.constant, falsehood, String.reduceAppend,
    Term.substitute, List.map_cons, List.map_nil, valuation, if_true, String.reduceEq, if_false] using equation

theorem le_succ_zero (left : Nat) :
    Equivalent Examples.conditional [] "Bool" (le (numeral (left + 1)) (numeral 0)) falsehood :=
  (le_succ_zero_step left).equivalent

theorem le_succ_succ_step (left right : Nat) : EquationReduction Examples.conditional [] "Bool"
    (le (numeral (left + 1)) (numeral (right + 1))) (le (numeral left) (numeral right)) := by
  have used : recursiveRow.usedContext = [("N", "Nat"), ("M", "Nat")] := by
    simp [recursiveRow, Row.usedContext, le, successor, Term.variables]
  have nTyped : HasSort Examples.conditional.signature recursiveRow.usedContext (.var "N") "Nat" :=
    .var (by simp [used])
  have mTyped : HasSort Examples.conditional.signature recursiveRow.usedContext (.var "M") "Nat" :=
    .var (by simp [used, List.lookup])
  have leftTyped : HasSort Examples.conditional.signature recursiveRow.usedContext recursiveRow.left "Bool" :=
    le_sorted (.app successor_member (.cons nTyped .nil)) (.app successor_member (.cons mTyped .nil))
  have equation := EquationReduction.root (valuation left right) recursiveRow_member (by decide_cbv)
    leftTyped (le_sorted nTyped mTyped) (nat_valuation recursiveRow left right (by simp [used])) (.nil _)
  simpa only [recursiveRow, le, successor, numeral, Examples.numeral, String.reduceAppend,
    Term.substitute, List.map_cons, List.map_nil, valuation, if_true, String.reduceEq, if_false] using equation

theorem le_succ_succ (left right : Nat) :
    Equivalent Examples.conditional [] "Bool" (le (numeral (left + 1)) (numeral (right + 1))) (le (numeral left) (numeral right)) :=
  (le_succ_succ_step left right).equivalent

theorem comparison_equivalent (left right : Nat) : Equivalent Examples.conditional [] "Bool"
    (le (numeral left) (numeral right)) (if left ≤ right then truth else falsehood) := by
  induction left generalizing right with
  | zero => simpa only [Nat.zero_le, if_true] using le_zero right
  | succ left ih =>
    cases right with
    | zero =>
      have positive : ¬left + 1 ≤ 0 := by omega
      simpa only [if_neg positive] using le_succ_zero left
    | succ right =>
      simpa only [Nat.succ_le_succ_iff] using (le_succ_succ left right).trans (ih right)

def leftRow : Row := ⟨"max-left", [("N", "Nat"), ("M", "Nat")],
  [⟨le (.var "M") (.var "N"), truth⟩], maximum (.var "N") (.var "M"), .var "N"⟩
def rightRow : Row := ⟨"max-right", [("N", "Nat"), ("M", "Nat")],
  [⟨le (.var "N") (.var "M"), truth⟩], maximum (.var "N") (.var "M"), .var "M"⟩

theorem leftRow_member : leftRow ∈ Examples.conditional.equations := by
  simp [leftRow, Examples.conditional, maximum, le, truth, Examples.binary, Examples.constant, Examples.n, Examples.m]
theorem rightRow_member : rightRow ∈ Examples.conditional.equations := by
  simp [rightRow, Examples.conditional, maximum, le, truth, Examples.binary, Examples.constant, Examples.n, Examples.m]

theorem maximum_left_step (left right : Nat) (ordered : right ≤ left) :
    EquationReduction Examples.conditional [] "Nat" (maximum (numeral left) (numeral right)) (numeral left) := by
  have used : leftRow.usedContext = [("N", "Nat"), ("M", "Nat")] := by
    simp [leftRow, Row.usedContext, maximum, le, truth, Term.variables]
  have nTyped : HasSort Examples.conditional.signature leftRow.usedContext (.var "N") "Nat" := .var (by simp [used])
  have mTyped : HasSort Examples.conditional.signature leftRow.usedContext (.var "M") "Nat" := .var (by simp [used, List.lookup])
  have comparison : Equivalent Examples.conditional [] "Bool" (le (numeral right) (numeral left)) truth := by
    simpa only [if_pos ordered] using comparison_equivalent right left
  have conditions : Conditions Examples.conditional [] (valuation left right) leftRow.conditions := by
    apply Conditions.cons (sort := "Bool")
    · simpa only [leftRow, le, truth, Term.substitute, List.map_cons, List.map_nil, valuation,
        String.reduceEq, if_true, if_false] using comparison
    · exact .nil _
  have equation := EquationReduction.root (valuation left right) leftRow_member (by decide_cbv)
    (max_sorted nTyped mTyped) nTyped (nat_valuation leftRow left right (by simp [used])) conditions
  simpa only [leftRow, maximum, Term.substitute, List.map_cons, List.map_nil, valuation,
    String.reduceEq, if_true, if_false] using equation

theorem maximum_left (left right : Nat) (ordered : right ≤ left) :
    Equivalent Examples.conditional [] "Nat" (maximum (numeral left) (numeral right)) (numeral left) :=
  (maximum_left_step left right ordered).equivalent

theorem maximum_right_step (left right : Nat) (ordered : left ≤ right) :
    EquationReduction Examples.conditional [] "Nat" (maximum (numeral left) (numeral right)) (numeral right) := by
  have used : rightRow.usedContext = [("N", "Nat"), ("M", "Nat")] := by
    simp [rightRow, Row.usedContext, maximum, le, truth, Term.variables]
  have nTyped : HasSort Examples.conditional.signature rightRow.usedContext (.var "N") "Nat" := .var (by simp [used])
  have mTyped : HasSort Examples.conditional.signature rightRow.usedContext (.var "M") "Nat" := .var (by simp [used, List.lookup])
  have comparison : Equivalent Examples.conditional [] "Bool" (le (numeral left) (numeral right)) truth := by
    simpa only [if_pos ordered] using comparison_equivalent left right
  have conditions : Conditions Examples.conditional [] (valuation left right) rightRow.conditions := by
    apply Conditions.cons (sort := "Bool")
    · simpa only [rightRow, le, truth, Term.substitute, List.map_cons, List.map_nil, valuation,
        String.reduceEq, if_true, if_false] using comparison
    · exact .nil _
  have equation := EquationReduction.root (valuation left right) rightRow_member (by decide_cbv)
    (max_sorted nTyped mTyped) mTyped (nat_valuation rightRow left right (by simp [used])) conditions
  simpa only [rightRow, maximum, Term.substitute, List.map_cons, List.map_nil, valuation,
    String.reduceEq, if_true, if_false] using equation

theorem maximum_right (left right : Nat) (ordered : left ≤ right) :
    Equivalent Examples.conditional [] "Nat" (maximum (numeral left) (numeral right)) (numeral right) :=
  (maximum_right_step left right ordered).equivalent

theorem maximum_equivalent (left right : Nat) :
    Equivalent Examples.conditional [] "Nat" (maximum (numeral left) (numeral right)) (numeral (max left right)) := by
  by_cases ordered : right ≤ left
  · simpa only [Nat.max_eq_left ordered] using maximum_left left right ordered
  · have other : left ≤ right := by omega
    simpa only [Nat.max_eq_right other] using maximum_right left right other

#print axioms comparison_equivalent
#print axioms maximum_equivalent

end Mettapedia.Languages.Maude.ConditionalMax
