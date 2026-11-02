import Mettapedia.Languages.Erlang.ActorExamples

/-! Standard actor fixtures assembled into the independent indexed IR.
Receive branches see their pattern bindings, then message, flag and receive
loop, then their captured environment. No host actor implementation is used.
The corresponding Erlang programs are independently authored fixtures. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

namespace Mettapedia.Languages.Erlang.StandardActorExamples

open Assembly

private def v := variableRef
private def yes := atom "true"
private def tag (name : String) : MatchPattern := .literal (.atom name)

/-- Failed patterns and guards advance the scan without consuming a message.
Only a selected branch removes its message, before executing its body. -/
def receiveCases (clauses : List (MatchPattern × Expression × Expression)) : Expression :=
  letRecursive [(0, letValues 2 (actor .peekMessage []) <|
    caseValues (v 1)
      [([tag "true"], yes,
        caseValues (v 0)
          (clauses.map (fun (pattern, guard, body) =>
            ([pattern], guard, sequence (actor .removeMessage []) body)) ++
            [([.wildcard], yes, sequence (actor .nextMessage []) (apply (v 2) []))])),
       ([.wildcard], yes, sequence (actor .waitInfinity []) (apply (v 2) []))])]
    (apply (v 0) [])

private def pongServer : Expression :=
  letRecursive [(0, receiveCases [
    (.tuple [tag "ping", .bind], yes,
      sequence (actor .send [v 0, tuple [atom "pong", actor .self []]]) (apply (v 4) [])),
    (tag "stop", yes, atom "done")])] (apply (v 0) [])

def pingPong (rounds : Nat) : Program := assemble <|
  letValues 1 (actor .self []) <|
    letValues 1 (actor .spawn [lambda 0 pongServer]) <|
      letRecursive [(1, caseValues (v 0) [
        ([.literal (.integer 0)], yes,
          sequence (actor .send [v 2, atom "stop"]) (atom "done")),
        ([.wildcard], yes,
          sequence (actor .send [v 2, tuple [atom "ping", v 3]]) <|
            sequence (receiveCases [(.tuple [tag "pong", .bind],
              primitive .equal [v 0, v 6], atom "ok")]) <|
              apply (v 1) [primitive .subtract [v 0, integer 1]])])]
        (apply (v 0) [integer rounds])

private def counterServer : Expression :=
  letRecursive [(1, receiveCases [
    (.tuple [tag "inc"], yes, apply (v 4) [primitive .add [v 3, integer 1]]),
    (.tuple [tag "get", .bind], yes,
      sequence (actor .send [v 0, tuple [atom "value", v 4]]) (apply (v 5) [v 4])),
    (tag "stop", yes, atom "done")])] (apply (v 0) [integer 0])

def counter : Program := assemble <|
  letValues 1 (actor .self []) <|
    letValues 1 (actor .spawn [lambda 0 counterServer]) <|
      sequence (actor .send [v 0, tuple [atom "inc"]]) <|
      sequence (actor .send [v 0, tuple [atom "inc"]]) <|
      sequence (actor .send [v 0, tuple [atom "get", v 1]]) <|
        letValues 1 (receiveCases [(.tuple [tag "value", .bind],
          primitive .isInteger [v 0], v 0)]) <|
          sequence (actor .send [v 1, atom "stop"]) (v 0)

#guard (pingPong 0).checkScope
#guard (pingPong 2).checkScope
#guard counter.checkScope

def pingPongResult := ActorExamples.runFair 3000 (ActorSystem.begin (pingPong 2))
def counterResult := ActorExamples.runFair 3000 (ActorSystem.begin counter)

private def childDone (system : ActorSystem) : Bool :=
  match system.process? 1 with
  | some process => match process.machine with
    | .halted (.ok [.literal (.atom "done")]) => true
    | _ => false
  | none => false

#guard match pingPongResult with
  | .ok system => match system.observe with
    | .returned (.ok [.literal (.atom "done")]) =>
        childDone system && system.network.isEmpty && system.nextPid == 2
    | _ => false
  | _ => false

#guard match counterResult with
  | .ok system => match system.observe with
    | .returned (.ok [.literal (.integer 2)]) =>
        childDone system && system.network.isEmpty && system.nextPid == 2
    | _ => false
  | _ => false

end Mettapedia.Languages.Erlang.StandardActorExamples
