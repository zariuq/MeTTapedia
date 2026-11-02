import Mettapedia.Languages.Maude.Examples

/-! A compositional reducer for the authored Peano equation module. Unknown
constructors and open variables remain syntax. The equation invariant below
does not by itself establish normalization-path coverage or termination of
every oriented rewrite strategy. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.Languages.Maude.PeanoNormalization

def add : Term → Term → Term
  | .app "peano.zero" [], right => right
  | .app "peano.succ" [left], right => .app "peano.succ" [add left right]
  | left, right => .app "peano.add" [left, right]

def multiply : Term → Term → Term
  | .app "peano.zero" [], _ => .app "peano.zero" []
  | .app "peano.succ" [left], right => add right (multiply left right)
  | left, right => .app "peano.mul" [left, right]

def finish (id : String) (arguments : List Term) : Term :=
  match id, arguments with
  | "peano.add", [left, right] => add left right
  | "peano.mul", [left, right] => multiply left right
  | _, _ => .app id arguments

def reduce : Term → Term
  | .var name => .var name
  | .app id arguments => finish id (arguments.map reduce)

def numeralValue? : Term → Option Nat
  | .app "peano.zero" [] => some 0
  | .app "peano.succ" [term] => Nat.succ <$> numeralValue? term
  | _ => none

theorem numeralValue?_numeral (value : Nat) : numeralValue? (Examples.numeral "peano" value) = some value := by
  induction value with
  | zero => simp only [Examples.numeral, Examples.constant, String.reduceAppend, numeralValue?]
  | succ value ih =>
      simp only [Examples.numeral, String.reduceAppend, numeralValue?, ih]
      rfl

theorem add_zero (right : Term) : add (.app "peano.zero" []) right = right := by rw [add]
theorem add_succ (left right : Term) :
    add (.app "peano.succ" [left]) right = .app "peano.succ" [add left right] := by rw [add]
theorem multiply_zero (right : Term) : multiply (.app "peano.zero" []) right = .app "peano.zero" [] := by rw [multiply]
theorem multiply_succ (left right : Term) :
    multiply (.app "peano.succ" [left]) right = add right (multiply left right) := by rw [multiply]

theorem reduce_zero : reduce (.app "peano.zero" []) = .app "peano.zero" [] := by
  rw [reduce]
  rfl

theorem reduce_succ (term : Term) : reduce (.app "peano.succ" [term]) = .app "peano.succ" [reduce term] := by
  rw [reduce]
  rfl

theorem reduce_add (left right : Term) :
    reduce (.app "peano.add" [left, right]) = add (reduce left) (reduce right) := by
  rw [reduce]
  rfl

theorem reduce_multiply (left right : Term) :
    reduce (.app "peano.mul" [left, right]) = multiply (reduce left) (reduce right) := by
  rw [reduce]
  rfl

theorem frame_invariant {signature : Signature} {context : VariableContext} {hole sort : String}
    (frame : ArgumentContext signature context hole sort) {source target : Term}
    (same : reduce source = reduce target) : reduce (frame.plug source) = reduce (frame.plug target) := by
  simp only [ArgumentContext.plug, reduce, List.map_append, List.map_cons, same]

theorem row_invariant {row : Row} (declared : row ∈ Examples.peano.equations) (assignment : Valuation) :
    reduce (row.left.substitute assignment) = reduce (row.right.substitute assignment) := by
  simp only [Examples.peano, List.mem_cons, List.not_mem_nil, or_false] at declared
  rcases declared with rfl | rfl | rfl | rfl
  all_goals
    simp only [Examples.binary, Examples.constant, Examples.n, Examples.m, Examples.numeral,
      Term.substitute, List.map_cons, List.map_nil, String.reduceAppend, reduce_zero, reduce_succ, reduce_add, reduce_multiply,
      add_zero, add_succ, multiply_zero, multiply_succ]

theorem algebra_impossible {source target : Term} : ¬ AlgebraSchema Examples.peano.signature source target := by
  intro step
  have attributes : ∀ declaration ∈ Examples.peano.signature.operators,
      declaration.attributes.associative = false ∧ declaration.attributes.commutative = false ∧
        declaration.attributes.identity = none := by
    intro declaration member
    simp [Examples.peano, Examples.natData] at member
    rcases member with rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl, rfl⟩
  cases step with
  | associative declared active => simp [(attributes _ declared).1] at active
  | commutative declared active => simp [(attributes _ declared).2.1] at active
  | leftUnit declared selected => simp [(attributes _ declared).2.2] at selected
  | rightUnit declared selected => simp [(attributes _ declared).2.2] at selected

theorem equivalent_same_reduce {context : VariableContext} {sort : String} {source target : Term}
    (equivalent : Equivalent Examples.peano context sort source target) : reduce source = reduce target := by
  refine Equivalent.rec
    (motive_1 := fun _ source target _ => reduce source = reduce target)
    (motive_2 := fun assignment conditions _ => ∀ condition ∈ conditions,
      reduce (condition.left.substitute assignment) = reduce (condition.right.substitute assignment))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ equivalent
  · intro _ _ _
    rfl
  · intro _ _ _ _ ih
    exact ih.symm
  · intro _ _ _ _ _ _ first last
    exact first.trans last
  · intro _ _ frame _ _ _ ih
    exact frame_invariant frame ih
  · intro _ _ _ step
    exact (algebra_impossible step.schema).elim
  · intro row _ assignment declared _ _ _ _ _ _
    exact row_invariant declared assignment
  · intro assignment condition impossible
    cases impossible
  · intro assignment condition rest sort _ _ first restIH actual member
    rcases List.mem_cons.mp member with rfl | member
    · exact first
    · exact restIH actual member

#guard reduce (Examples.binary "peano.mul" (Examples.numeral "peano" 2) (Examples.numeral "peano" 3)) ==
  Examples.numeral "peano" 6
#guard reduce (Examples.binary "peano.add" (.var "N") (Examples.numeral "peano" 0)) ==
  Examples.binary "peano.add" (.var "N") (Examples.numeral "peano" 0)
#guard reduce (.app "uninterpreted" [.var "N"]) == .app "uninterpreted" [.var "N"]

end Mettapedia.Languages.Maude.PeanoNormalization
