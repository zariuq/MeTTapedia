import Mettapedia.Languages.Erlang.Actors
import Mettapedia.Languages.Erlang.Assembly
import Mettapedia.Languages.Erlang.Scope

/-! Closed actor programs over the independent IR. The fair reference driver
executes one local step of each existing process, then one eligible delivery.
It witnesses this schedule, not every possible scheduling outcome. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
namespace Mettapedia.Languages.Erlang.ActorExamples
open Assembly

def receiveLiteral (literal : Literal) : Expression :=
  letRecursive [(0, letValues 2 (actor .peekMessage []) <|
    caseValues (variableRef 1)
      [([.literal (.atom "true")], atom "true",
        caseValues (variableRef 0)
          [([.literal literal], atom "true", sequence (actor .removeMessage []) (variableRef 0)),
           ([.literal (.atom "b")], atom "false", atom "wrong"),
           ([.wildcard], atom "true", sequence (actor .nextMessage []) (apply (variableRef 2) []))]),
       ([.wildcard], atom "true", sequence (actor .waitInfinity []) (apply (variableRef 2) []))])]
    (apply (variableRef 0) [])

def spawnSend : Program := assemble <|
  letValues 1 (actor .self []) <|
    sequence (actor .spawn [lambda 0 (actor .send [variableRef 0, integer 42])])
      (receiveLiteral (.integer 42))

def selfSelective : Program := assemble <|
  letValues 1 (actor .self []) <|
    sequence (actor .send [variableRef 0, atom "b"]) <|
    sequence (actor .send [variableRef 0, atom "a"]) <|
    sequence (actor .send [variableRef 0, atom "b"]) <|
      tuple [receiveLiteral (.atom "a"), receiveLiteral (.atom "b")]

#guard spawnSend.checkScope
#guard selfSelective.checkScope

def fairRound (system : ActorSystem) : Except ActorError ActorSystem :=
  ActorSystem.runChoices
    ((List.range system.processes.length).map ActorChoice.execute ++ [.deliver 0]) system

def runFair : Nat → ActorSystem → Except ActorError ActorSystem
  | 0, system => .ok system
  | cycles + 1, system => do runFair cycles (← fairRound system)

def spawnSendResult := runFair 500 (ActorSystem.begin spawnSend)
def selfSelectiveResult := runFair 800 (ActorSystem.begin selfSelective)

#guard match spawnSendResult with
  | .ok system => match system.observe with
    | .returned (.ok [.literal (.integer 42)]) => true
    | _ => false
  | _ => false

#guard match selfSelectiveResult with
  | .ok system => match system.observe, system.process? 0 with
    | .returned (.ok [.tuple [.literal (.atom "a"), .literal (.atom "b")]]), some process =>
        match process.mailbox.contents with
        | [.literal (.atom "b")] => true
        | _ => false
    | _, _ => false
  | _ => false

end Mettapedia.Languages.Erlang.ActorExamples
