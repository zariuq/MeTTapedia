import Mettapedia.Languages.Maude.EquationReduction
import Mettapedia.Languages.Maude.Examples

/-! Typed constructors, contexts and forward instances of the four authored
Peano equations. These witnesses use the source theory's actual rows. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.Languages.Maude.PeanoEquationRules

def zeroOperator : Operator := ⟨"peano.zero", "0", [], "Nat", {constructor := true}⟩
def successorOperator : Operator := ⟨"peano.succ", "s", ["Nat"], "Nat", {constructor := true}⟩
def additionOperator : Operator := ⟨"peano.add", "_+_", ["Nat", "Nat"], "Nat", {}⟩
def multiplicationOperator : Operator := ⟨"peano.mul", "_*_", ["Nat", "Nat"], "Nat", {}⟩

theorem operators {declaration : Operator} (member : declaration ∈ Examples.peano.signature.operators) :
    declaration = zeroOperator ∨ declaration = successorOperator ∨ declaration = additionOperator ∨
      declaration = multiplicationOperator := by
  simpa [Examples.peano, Examples.natData, String.reduceAppend, zeroOperator, successorOperator,
    additionOperator, multiplicationOperator] using member

theorem zero_member : zeroOperator ∈ Examples.peano.signature.operators := by
  simp [Examples.peano, Examples.natData, zeroOperator]
theorem successor_member : successorOperator ∈ Examples.peano.signature.operators := by
  simp [Examples.peano, Examples.natData, successorOperator]
theorem addition_member : additionOperator ∈ Examples.peano.signature.operators := by
  simp [Examples.peano, additionOperator]
theorem multiplication_member : multiplicationOperator ∈ Examples.peano.signature.operators := by
  simp [Examples.peano, multiplicationOperator]

theorem zero_typed (context : VariableContext) : HasSort Examples.peano.signature context (.app "peano.zero" []) "Nat" :=
  .app zero_member .nil
theorem successor_typed {context : VariableContext} {term : Term}
    (typed : HasSort Examples.peano.signature context term "Nat") :
    HasSort Examples.peano.signature context (.app "peano.succ" [term]) "Nat" :=
  .app successor_member (.cons typed .nil)
theorem addition_typed {context : VariableContext} {left right : Term}
    (leftTyped : HasSort Examples.peano.signature context left "Nat")
    (rightTyped : HasSort Examples.peano.signature context right "Nat") :
    HasSort Examples.peano.signature context (.app "peano.add" [left, right]) "Nat" :=
  .app addition_member (.cons leftTyped (.cons rightTyped .nil))
theorem multiplication_typed {context : VariableContext} {left right : Term}
    (leftTyped : HasSort Examples.peano.signature context left "Nat")
    (rightTyped : HasSort Examples.peano.signature context right "Nat") :
    HasSort Examples.peano.signature context (.app "peano.mul" [left, right]) "Nat" :=
  .app multiplication_member (.cons leftTyped (.cons rightTyped .nil))

theorem successor_argument_typed {context : VariableContext} {term : Term}
    (typed : HasSort Examples.peano.signature context (.app "peano.succ" [term]) "Nat") :
    HasSort Examples.peano.signature context term "Nat" := by
  obtain ⟨declaration, member, label, _, arguments⟩ := HasSort.operator_arguments typed rfl
  rcases operators member with rfl | rfl | rfl | rfl
  · simp [zeroOperator] at label
  · cases arguments with
    | cons first rest => exact first
  · simp [additionOperator] at label
  · simp [multiplicationOperator] at label

def successorFrame (context : VariableContext) : ArgumentContext Examples.peano.signature context "Nat" "Nat" :=
  ⟨successorOperator, successor_member, [], [], [], [], rfl, rfl, .nil, .nil⟩

private def binaryLeftFrame {context : VariableContext} (declaration : Operator)
    (declared : declaration ∈ Examples.peano.signature.operators)
    (arguments : declaration.arguments = ["Nat", "Nat"]) (result : declaration.result = "Nat")
    {right : Term} (typed : HasSort Examples.peano.signature context right "Nat") :
    ArgumentContext Examples.peano.signature context "Nat" "Nat" :=
  ⟨declaration, declared, [], ["Nat"], [], [right], arguments, result, .nil, .cons typed .nil⟩

private def binaryRightFrame {context : VariableContext} (declaration : Operator)
    (declared : declaration ∈ Examples.peano.signature.operators)
    (arguments : declaration.arguments = ["Nat", "Nat"]) (result : declaration.result = "Nat")
    {left : Term} (typed : HasSort Examples.peano.signature context left "Nat") :
    ArgumentContext Examples.peano.signature context "Nat" "Nat" :=
  ⟨declaration, declared, ["Nat"], [], [left], [], arguments, result, .cons typed .nil, .nil⟩

def additionLeftFrame {context : VariableContext} {right : Term}
    (typed : HasSort Examples.peano.signature context right "Nat") :=
  binaryLeftFrame additionOperator addition_member rfl rfl typed
def additionRightFrame {context : VariableContext} {left : Term}
    (typed : HasSort Examples.peano.signature context left "Nat") :=
  binaryRightFrame additionOperator addition_member rfl rfl typed
def multiplicationLeftFrame {context : VariableContext} {right : Term}
    (typed : HasSort Examples.peano.signature context right "Nat") :=
  binaryLeftFrame multiplicationOperator multiplication_member rfl rfl typed
def multiplicationRightFrame {context : VariableContext} {left : Term}
    (typed : HasSort Examples.peano.signature context left "Nat") :=
  binaryRightFrame multiplicationOperator multiplication_member rfl rfl typed

@[simp] theorem successorFrame_plug (context : VariableContext) (term : Term) :
    (successorFrame context).plug term = .app "peano.succ" [term] := rfl
@[simp] theorem additionLeftFrame_plug {context : VariableContext} {right : Term}
    (typed : HasSort Examples.peano.signature context right "Nat") (term : Term) :
    (additionLeftFrame typed).plug term = .app "peano.add" [term, right] := rfl
@[simp] theorem additionRightFrame_plug {context : VariableContext} {left : Term}
    (typed : HasSort Examples.peano.signature context left "Nat") (term : Term) :
    (additionRightFrame typed).plug term = .app "peano.add" [left, term] := rfl
@[simp] theorem multiplicationLeftFrame_plug {context : VariableContext} {right : Term}
    (typed : HasSort Examples.peano.signature context right "Nat") (term : Term) :
    (multiplicationLeftFrame typed).plug term = .app "peano.mul" [term, right] := rfl
@[simp] theorem multiplicationRightFrame_plug {context : VariableContext} {left : Term}
    (typed : HasSort Examples.peano.signature context left "Nat") (term : Term) :
    (multiplicationRightFrame typed).plug term = .app "peano.mul" [left, term] := rfl

private def assignment (left right : Term) : Valuation := fun name => if name == "N" then left else right

theorem schemas_typed {row : Row} (declared : row ∈ Examples.peano.equations) :
    HasSort Examples.peano.signature row.usedContext row.left "Nat" ∧
      HasSort Examples.peano.signature row.usedContext row.right "Nat" := by
  simp only [Examples.peano, List.mem_cons, List.not_mem_nil, or_false] at declared
  rcases declared with rfl | rfl | rfl | rfl
  · exact ⟨addition_typed (zero_typed _) (.var (by decide_cbv)), .var (by decide_cbv)⟩
  · exact ⟨addition_typed (successor_typed (.var (by decide_cbv))) (.var (by decide_cbv)),
      successor_typed (addition_typed (.var (by decide_cbv)) (.var (by decide_cbv)))⟩
  · exact ⟨multiplication_typed (zero_typed _) (.var (by decide_cbv)), zero_typed _⟩
  · exact ⟨multiplication_typed (successor_typed (.var (by decide_cbv))) (.var (by decide_cbv)),
      addition_typed (.var (by decide_cbv)) (multiplication_typed (.var (by decide_cbv)) (.var (by decide_cbv)))⟩

private theorem valuation_typed {context : VariableContext} {row : Row}
    (declared : row ∈ Examples.peano.equations) {left right : Term}
    (leftTyped : HasSort Examples.peano.signature context left "Nat")
    (rightTyped : HasSort Examples.peano.signature context right "Nat") :
    TypedValuation Examples.peano.signature context row.usedContext (assignment left right) := by
  have allFormals : Examples.peano.equations.all (fun row => row.formals.all (fun entry => entry.2 == "Nat")) = true := by
    decide_cbv
  intro name sort found
  obtain ⟨before, after, shape, _⟩ := List.lookup_eq_some_iff.mp found
  have member : (name, sort) ∈ row.usedContext := by simp [shape]
  unfold Row.usedContext at member
  have formal := (List.mem_filter.mp member).1
  have same : sort = "Nat" := beq_iff_eq.mp
    (List.all_eq_true.mp (List.all_eq_true.mp allFormals row declared) (name, sort) formal)
  rw [same]
  unfold assignment
  split <;> assumption

private theorem equation_at {context : VariableContext} {row : Row}
    (declared : row ∈ Examples.peano.equations) {left right : Term}
    (leftTyped : HasSort Examples.peano.signature context left "Nat")
    (rightTyped : HasSort Examples.peano.signature context right "Nat") :
    EquationReduction Examples.peano context "Nat"
      (row.left.substitute (assignment left right)) (row.right.substitute (assignment left right)) := by
  have checked : Examples.peano.equations.all (Row.check Examples.peano.signature) = true := by decide_cbv
  have empty : row.conditions = [] := by
    simp only [Examples.peano, List.mem_cons, List.not_mem_nil, or_false] at declared
    rcases declared with rfl | rfl | rfl | rfl <;> rfl
  exact .root (assignment left right) declared (List.all_eq_true.mp checked row declared)
    (schemas_typed declared).1 (schemas_typed declared).2 (valuation_typed declared leftTyped rightTyped)
    (empty ▸ .nil _)

theorem add_zero_step {context : VariableContext} {right : Term}
    (typed : HasSort Examples.peano.signature context right "Nat") :
    EquationReduction Examples.peano context "Nat" (.app "peano.add" [.app "peano.zero" [], right]) right := by
  have step := equation_at (row := Examples.peano.equations[0]) (by simp [Examples.peano]) typed typed
  simpa [Examples.peano, Examples.binary, Examples.constant, Examples.numeral, Examples.m,
    Term.substitute, assignment] using step

theorem add_succ_step {context : VariableContext} {left right : Term}
    (leftTyped : HasSort Examples.peano.signature context left "Nat")
    (rightTyped : HasSort Examples.peano.signature context right "Nat") :
    EquationReduction Examples.peano context "Nat"
      (.app "peano.add" [.app "peano.succ" [left], right]) (.app "peano.succ" [.app "peano.add" [left, right]]) := by
  have step := equation_at (row := Examples.peano.equations[1]) (by simp [Examples.peano]) leftTyped rightTyped
  simpa [Examples.peano, Examples.binary, Examples.n, Examples.m, Term.substitute, assignment] using step

theorem multiply_zero_step {context : VariableContext} {right : Term}
    (typed : HasSort Examples.peano.signature context right "Nat") :
    EquationReduction Examples.peano context "Nat"
      (.app "peano.mul" [.app "peano.zero" [], right]) (.app "peano.zero" []) := by
  have step := equation_at (row := Examples.peano.equations[2]) (by simp [Examples.peano]) typed typed
  simpa [Examples.peano, Examples.binary, Examples.constant, Examples.numeral, Examples.m, Term.substitute,
    assignment] using step

theorem multiply_succ_step {context : VariableContext} {left right : Term}
    (leftTyped : HasSort Examples.peano.signature context left "Nat")
    (rightTyped : HasSort Examples.peano.signature context right "Nat") :
    EquationReduction Examples.peano context "Nat"
      (.app "peano.mul" [.app "peano.succ" [left], right]) (.app "peano.add" [right, .app "peano.mul" [left, right]]) := by
  have step := equation_at (row := Examples.peano.equations[3]) (by simp [Examples.peano]) leftTyped rightTyped
  simpa [Examples.peano, Examples.binary, Examples.n, Examples.m, Term.substitute, assignment] using step

end Mettapedia.Languages.Maude.PeanoEquationRules
