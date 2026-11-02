import Mettapedia.Languages.OCaml.Assembly
import Mettapedia.Languages.OCaml.Machine
import Mettapedia.Languages.OCaml.Scope

/-! Prepared indexed programs corresponding to the six ordinary OCaml
examples. Expected data values are independent fixtures, also observed in
OCaml. Reading their ordinary source and proving lowering remain separate. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.OCaml.Examples

open Assembly

private def v := Assembly.variableRef
private def n := Assembly.integer
private def b := Assembly.boolean
private def app := Assembly.apply
private def lam (body : Expression) := Assembly.lambda .bind body
private def bin (operator : Primitive) (left right : Expression) := primitive operator [left, right]
private def add := bin .add
private def sub := bin .subtract
private def mul := bin .multiply
private def eq := bin .equal
private def lt := bin .less
private def le := bin .lessEqual
private def lst := Assembly.integers
private def matchList (scrutinee empty nonempty : Expression) :=
  matchValue scrutinee [(.literal .nil, empty), (.cons .bind .bind, nonempty)]

def recursion : Program := assemble <|
  letRecursive [lam (branch (eq (v 0) (n 0)) (n 1)
    (mul (v 0) (app (v 1) (sub (v 0) (n 1)))))] <|
  letRecursive [lam (branch (lt (v 0) (n 2)) (v 0)
    (add (app (v 1) (sub (v 0) (n 1))) (app (v 1) (sub (v 0) (n 2)))))] <|
  tuple [app (v 1) (n 6), app (v 0) (n 10)]

private def mapFunction : Expression := lam <| lam <|
  matchList (v 0) nil <|
    cons (app (v 3) (v 1)) (app (app (v 4) (v 3)) (v 0))

private def foldFunction : Expression := lam <| lam <| lam <|
  matchList (v 0) (v 1) <|
    app (app (app (v 5) (v 4)) (app (app (v 4) (v 3)) (v 1))) (v 0)

private def appendFunction : Expression := lam <| lam <|
  matchList (v 1) (v 0) <|
    cons (v 1) (app (app (v 4) (v 0)) (v 2))

private def reverseFunction : Expression := lam <| lam <|
  matchList (v 0) (v 1) <|
    app (app (v 4) (cons (v 1) (v 3))) (v 0)

def lists : Program := assemble <|
  letRecursive [mapFunction] <|
  letRecursive [foldFunction] <|
  letRecursive [appendFunction] <|
  letRecursive [reverseFunction] <|
  tuple [app (app (v 3) (lam (add (v 0) (n 1)))) (lst [1, 2, 3]),
    app (app (app (v 2) (lam (lam (add (v 1) (v 0))))) (n 0)) (lst [1, 2, 3]),
    app (app (v 1) (lst [1, 2])) (lst [3, 4]), app (app (v 0) nil) (lst [1, 2, 3])]

def mutualRecursion : Program := assemble <|
  letRecursive [lam (branch (eq (v 0) (n 0)) (b true) (app (v 1) (sub (v 0) (n 1)))),
    lam (branch (eq (v 0) (n 0)) (b false) (app (v 2) (sub (v 0) (n 1))))] <|
  tuple [app (v 1) (n 8), app (v 0) (n 7), app (v 1) (n 7)]

def exprConstructors : List Constructor := [⟨0, 0, 1⟩, ⟨0, 1, 2⟩, ⟨0, 2, 2⟩, ⟨0, 3, 1⟩]

private def evaluationFunction : Expression := lam <| matchValue (v 0)
  [(.variant 0 0 [.bind], v 0),
   (.variant 0 1 [.bind, .bind], add (app (v 3) (v 1)) (app (v 3) (v 0))),
   (.variant 0 2 [.bind, .bind], mul (app (v 3) (v 1)) (app (v 3) (v 0))),
   (.variant 0 3 [.bind], sub (n 0) (app (v 2) (v 0)))]

private def simplifyFunction : Expression := lam <| matchValue (v 0)
  [(.variant 0 1 [.variant 0 0 [.literal (.integer 0)], .bind], v 0),
   (.variant 0 1 [.bind, .variant 0 0 [.literal (.integer 0)]], v 0), (.bind, v 0)]

def variants : Program := assemble
  (letRecursive [evaluationFunction] <|
    letValue .bind simplifyFunction <|
    tuple [app (v 1) (variant 0 2 [variant 0 0 [n 6], variant 0 0 [n 7]]),
      app (v 1) (app (v 0) (variant 0 1 [variant 0 0 [n 0], variant 0 0 [n 9]]))])
  exprConstructors

def closures : Program := assemble <|
  letValue .bind (lam (lam (add (v 0) (v 1)))) <|
  letValue .bind (lam (lam (lam (app (v 2) (app (v 1) (v 0)))))) <|
  letValue .bind (n 3) <|
  letValue .bind (lam (add (v 0) (v 1))) <|
  letValue .bind (n 100) <|
  letValue .bind (app (v 4) (n 2)) <|
  tuple [app (v 2) (n 4), app (v 0) (n 5),
    app (app (app (v 4) (v 0)) (app (v 5) (n 10))) (n 1)]

private def insertFunction : Expression := lam <| lam <|
  matchList (v 0) (cons (v 1) nil) <|
    branch (le (v 3) (v 1)) (cons (v 3) (v 2))
      (cons (v 1) (app (app (v 4) (v 3)) (v 0)))

private def sortFunction : Expression := lam <|
  matchList (v 0) nil (app (app (v 4) (v 1)) (app (v 3) (v 0)))

def sorting : Program := assemble <|
  letRecursive [insertFunction] <| letRecursive [sortFunction] <| app (v 0) (lst [3, 1, 2, 1])

def priority : Program := assemble <|
  matchValue (tuple [n 1, n 2])
    [(.tuple [.literal (.integer 1), .bind], v 0),
     (.tuple [.bind, .literal (.integer 2)], v 0), (.wildcard, n 0)]

def matchFailure : Program := assemble <| matchValue nil [(.cons .bind .bind, n 1)]

private def loopFunction : Expression := lam (app (v 1) (v 0))

def looping : Program := assemble <| letRecursive [loopFunction] <| app (v 0) (n 0)

def rightToLeftFault : Program := assemble <| letRecursive [loopFunction] <|
  tuple [app (v 0) (n 0), bin .divide (n 1) (n 0)]

def shortCircuit : Program := assemble <| letRecursive [loopFunction] <|
  tuple [andThen (b false) (app (v 0) (n 0)), orElse (b true) (app (v 0) (n 0))]

def integer (value : Int) : Value := .literal (.integer value)
def boolean (value : Bool) : Value := .literal (.boolean value)
def list : List Int → Value
  | [] => .literal .nil
  | head :: tail => .cons (integer head) (list tail)

structure Example where
  name : String
  program : Program
  expected : Result
  deriving Repr

def examples : List Example := [
  ⟨"core_recursion", recursion, .ok (.tuple [integer 720, integer 55])⟩,
  ⟨"core_lists", lists, .ok (.tuple [list [2, 3, 4], integer 6, list [1, 2, 3, 4], list [3, 2, 1]])⟩,
  ⟨"core_mutual", mutualRecursion, .ok (.tuple [boolean true, boolean true, boolean false])⟩,
  ⟨"core_variants", variants, .ok (.tuple [integer 42, integer 9])⟩,
  ⟨"core_closures", closures, .ok (.tuple [integer 7, integer 7, integer 13])⟩,
  ⟨"core_sort", sorting, .ok (list [1, 1, 2, 3])⟩,
  ⟨"pattern_priority", priority, .ok (integer 2)⟩,
  ⟨"match_failure", matchFailure, .error .matchFailure⟩,
  ⟨"right_to_left_fault", rightToLeftFault, .error .divisionByZero⟩,
  ⟨"short_circuit", shortCircuit, .ok (.tuple [boolean false, boolean true])⟩]

def structuralExamples : List Example := [
  ⟨"literal", assemble (n 42), .ok (integer 42)⟩,
  ⟨"capture", assemble (letValue .bind (n 7) <|
      letValue .bind (lam (v 1)) <| letValue .bind (n 99) <| app (v 1) (n 0)), .ok (integer 7)⟩,
  ⟨"higher_order", assemble (app (lam (app (v 0) (n 42))) (lam (v 0))), .ok (integer 42)⟩,
  ⟨"tuple_parameter", assemble (app (Assembly.lambda (.tuple [.bind, .bind])
      (tuple [v 0, v 1])) (tuple [n 3, n 4])), .ok (.tuple [integer 4, integer 3])⟩,
  ⟨"ordered_pattern", priority, .ok (integer 2)⟩,
  ⟨"unselected_loop", assemble (letRecursive [loopFunction] <|
      branch (b false) (app (v 0) (n 0)) (n 9)), .ok (integer 9)⟩]

#guard examples.all fun sample => run sample.program 20000 (begin sample.program) == .complete sample.expected
#guard match run looping 2000 (begin looping) with | .pending _ => true | _ => false
#guard examples.all fun sample =>
  resume sample.program 19983 (run sample.program 17 (begin sample.program)) ==
    run sample.program 20000 (begin sample.program)
#guard examples.all fun sample => sample.program.checkScope
#guard looping.checkScope
#guard !(assemble (variableRef 0)).checkScope
#guard !(assemble (Assembly.integer integerHalf)).checkScope
#guard !(assemble (Assembly.variant 0 99 []) exprConstructors).checkScope
#guard !({code := #[.apply 0 0], entry := 0} : Program).checkScope
#guard structuralExamples.all fun sample => sample.program.checkScope &&
  run sample.program 20000 (begin sample.program) == .complete sample.expected

end Mettapedia.Languages.OCaml.Examples
