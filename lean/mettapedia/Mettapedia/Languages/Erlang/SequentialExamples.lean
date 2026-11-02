import Mettapedia.Languages.Erlang.Assembly
import Mettapedia.Languages.Erlang.Machine

/-! Independently assembled sequential acceptance controls. The comparison
driver runs the corresponding separately authored Erlang source. These
programs do not establish the source-grammar lowering or emitted backend.
In particular, multi-values, guard fall-through, lexical capture and fault
escape have separating controls. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.Erlang.SequentialExamples

open Assembly

private def v := variableRef
private def n := integer
private def a := atom
private def yes := atom "true"
private def no := atom "false"
private def op := primitive
private def call := apply

def number (value : Int) : Value := .literal (.integer value)
def symbol (name : String) : Value := .literal (.atom name)
def list : List Value → Value
  | [] => .literal .nil
  | head :: tail => .cons head (list tail)
def numbers (values : List Int) : Value := list (values.map number)

private def factorialBody (selfSlot : Nat) : Expression :=
  caseValues (v 0) [
    ([.literal (.integer 0)], yes, n 1),
    ([.bind], op .andBool [op .isInteger [v 0], op .greater [v 0, n 0]],
      op .multiply [v 0, call (v (selfSlot + 2)) [op .subtract [v 0, n 1]]])]

private def reverseBody (selfSlot : Nat) : Expression :=
  caseValues (values [v 1, v 0]) [
    ([.literal .nil, .bind], yes, v 0),
    ([.cons .bind .bind, .bind], yes,
      call (v (selfSlot + 5)) [v 1, cons (v 2) (v 0)])]

private def appendBody (selfSlot : Nat) : Expression :=
  caseValues (values [v 1, v 0]) [
    ([.literal .nil, .bind], yes, v 0),
    ([.cons .bind .bind, .bind], yes,
      cons (v 2) (call (v (selfSlot + 5)) [v 1, v 0]))]

private def mapBody (selfSlot : Nat) : Expression :=
  caseValues (v 0) [
    ([.literal .nil], yes, nil),
    ([.cons .bind .bind], yes,
      cons (call (v 3) [v 1]) (call (v (selfSlot + 4)) [v 3, v 0]))]

def standardSequential : Program := assemble <|
  letRecursive [(1, factorialBody 3), (2, reverseBody 2), (2, appendBody 1), (2, mapBody 0)] <|
    tuple [call (v 3) [n 5], call (v 2) [integers [1, 2, 3], nil],
      call (v 1) [integers [1, 2], integers [3]],
      call (v 0) [lambda 1 (op .add [v 0, n 1]), integers [1, 2]]]

def lexicalCapture : Program := assemble <|
  letValues 1 (n 10) <|
    letValues 1 (lambda 1 (op .add [v 1, v 0])) <|
      letValues 1 (n 99) (call (v 1) [n 5])

private def guardedFallback (guard : Expression) : Program := assemble <|
  letValues 1 (n 7) <|
    caseValues (n 9) [([.bind], guard, v 0), ([.wildcard], yes, v 0)]

def failedGuard : Program := guardedFallback no
def faultyGuard : Program := guardedFallback (op .divide [n 1, n 0])
def nonBooleanGuard : Program := guardedFallback (v 0)

def bodyFault : Program := assemble <|
  caseValues (n 9) [([.bind], yes, op .divide [n 1, n 0]), ([.wildcard], yes, n 42)]

def patternPriority : Program := assemble <|
  caseValues (tuple [a "tag", n 3]) [
    ([.tuple [.literal (.atom "tag"), .bind]], yes, v 0),
    ([.bind], yes, n 99)]

def pinned (argument : Int) : Program := assemble <|
  letValues 1 (n 2) <|
    caseValues (n argument) [([.pinned 0], yes, a "equal"), ([.wildcard], yes, a "different")]

def aliasPattern : Program := assemble <|
  caseValues (integers [4, 5]) [([.alias (.cons .bind .bind)], yes, tuple [v 2, v 1, v 0])]

def multiValue : Program := assemble <|
  letValues 2 (values [n 1, n 2]) (tuple [v 1, v 0])

def tupleIsNotMultiValue : Program := assemble <|
  letValues 2 (tuple [n 1, n 2]) (tuple [v 1, v 0])

def bigInteger : Program := assemble <|
  tuple [op .add [n (2 ^ 100), n 5], op .multiply [n (2 ^ 100), n 3]]

def signedDivision : Program := assemble <| tuple [op .divide [n (-7), n 3], op .remainder [n (-7), n 3]]

def pidEquality : Program :=
  {code := #[.variable 0, .primitive .equal [0, 0]], entry := 1}

def dataOrder : Program := assemble <| tuple [op .less [n 1, a "a"],
  op .less [tuple [], tuple [n (-100)]], op .less [nil, integers [0]], op .less [a "a", a "b"]]

def functionArity : Program := assemble <|
  letValues 1 (lambda 2 (v 0)) <| tuple [op .isFunctionArity [v 0, n 2], op .isFunctionArity [v 0, n 1]]

def nonFunction : Program := assemble (call (n 3) [])
def wrongArity : Program := assemble (call (lambda 2 (v 0)) [n 1])

def selfRequest : Program := assemble (actor .self [])
def sendRequest : Program := {code := #[.variable 0, .literal (.atom "hello"), .actor .send [0, 1]], entry := 2}

def looping : Program := assemble <| letRecursive [(0, call (v 0) [])] (call (v 0) [])
def unselectedLoop : Program := assemble <| letRecursive [(0, call (v 0) [])] <|
  caseValues (n 0) [([.literal (.integer 0)], yes, n 7), ([.wildcard], yes, call (v 0) [])]

def faultBeforeLoop : Program := assemble <| letRecursive [(0, call (v 0) [])] <|
  sequence (op .divide [n 1, n 0]) (call (v 0) [])

structure Example where
  name : String
  program : Program
  expected : Result

def examples : List Example := [
  ⟨"standard-sequential", standardSequential, .ok [.tuple [number 120, numbers [3, 2, 1], numbers [1, 2, 3], numbers [2, 3]]]⟩,
  ⟨"lexical-capture", lexicalCapture, .ok [number 15]⟩,
  ⟨"failed-guard-no-binding-leak", failedGuard, .ok [number 7]⟩,
  ⟨"faulty-guard-falls-through", faultyGuard, .ok [number 7]⟩,
  ⟨"nonboolean-guard-falls-through", nonBooleanGuard, .ok [number 7]⟩,
  ⟨"body-fault-does-not-fall-through", bodyFault, .error .badarith⟩,
  ⟨"pattern-priority", patternPriority, .ok [number 3]⟩,
  ⟨"pinned-positive", pinned 2, .ok [symbol "equal"]⟩,
  ⟨"pinned-negative", pinned 3, .ok [symbol "different"]⟩,
  ⟨"alias-pattern", aliasPattern, .ok [.tuple [numbers [4, 5], number 4, numbers [5]]]⟩,
  ⟨"multiple-return-values", multiValue, .ok [.tuple [number 1, number 2]]⟩,
  ⟨"unbounded-integers", bigInteger, .ok [.tuple [number (2 ^ 100 + 5), number (2 ^ 100 * 3)]]⟩,
  ⟨"signed-quotient-remainder", signedDivision, .ok [.tuple [number (-2), number (-1)]]⟩,
  ⟨"erlang-data-order", dataOrder, .ok [.tuple (List.replicate 4 (boolean true))]⟩,
  ⟨"uncurried-function-arity", functionArity, .ok [.tuple [boolean true, boolean false]]⟩,
  ⟨"nonfunction-fault", nonFunction, .error (.badfun (number 3))⟩]

def check (sample : Example) : Bool :=
  let direct := advance sample.program 5000 (begin sample.program)
  let resumed := (advance sample.program 13 (begin sample.program)).bind (advance sample.program 4987)
  match direct, resumed with
  | .ok (.halted result), .ok resumed => result == sample.expected && resumed == .halted result
  | _, _ => false

#eval examples.map fun sample => (sample.name, check sample)
#guard examples.length == 16
#guard examples.all check
#guard match advance tupleIsNotMultiValue 100 (begin tupleIsNotMultiValue) with
  | .error (.returnArity 2 1) => true
  | _ => false
#guard match advance wrongArity 100 (begin wrongArity) with
  | .ok (.halted (.error (.badarity _ _))) => true
  | _ => false
#guard match advance selfRequest 100 (begin selfRequest) with
  | .ok (.request .self []) => true
  | _ => false
#guard match advance sendRequest 100 (.evaluate sendRequest.entry [.pid 7] []) with
  | .ok (.request (.send 7 (.literal (.atom "hello"))) []) => true
  | _ => false
#guard match advance pidEquality 100 (.evaluate pidEquality.entry [.pid 7] []) with
  | .ok (.halted (.ok [.literal (.atom "true")])) => true
  | _ => false
#guard match advance lexicalCapture 0 (begin lexicalCapture) with
  | .ok (.evaluate _ [] []) => true
  | _ => false
#guard match advance looping 500 (begin looping) with
  | .ok (.halted _) | .ok (.request _ _) | .error _ => false
  | .ok _ => true
#guard match advance unselectedLoop 500 (begin unselectedLoop) with
  | .ok (.halted (.ok [.literal (.integer 7)])) => true
  | _ => false
#guard match advance faultBeforeLoop 500 (begin faultBeforeLoop) with
  | .ok (.halted (.error .badarith)) => true
  | _ => false

end Mettapedia.Languages.Erlang.SequentialExamples
