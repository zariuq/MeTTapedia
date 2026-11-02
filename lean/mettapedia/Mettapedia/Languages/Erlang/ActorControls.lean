import Mettapedia.Languages.Erlang.Actors
import Mettapedia.Languages.Erlang.Assembly
import Mettapedia.Languages.Erlang.Scope

/-! Whole reference-machine controls for local processes and selective
receive. These run the independent model; emitted actor execution and the
source/compiler correspondence are separate qualification obligations. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace Mettapedia.Languages.Erlang.ActorControls

open Assembly

def ticks (process count : Nat) : List ActorChoice := List.replicate count (.execute process)

def selfProgram : Program := assemble (actor .self [])
#guard selfProgram.checkScope

def selfResult := ActorSystem.runChoices (ticks 0 8) (ActorSystem.begin selfProgram)
#guard match selfResult with
  | .ok system => match system.observe with
    | .returned (.ok [.pid 0]) => true
    | _ => false
  | _ => false

def emptyPeekProgram : Program := assemble (actor .peekMessage [])
#guard emptyPeekProgram.checkScope

def emptyPeekResult := ActorSystem.runChoices (ticks 0 8) (ActorSystem.begin emptyPeekProgram)
#guard match emptyPeekResult with
  | .ok system => match system.observe with
    | .returned (.ok [.literal (.atom "false"), .literal (.atom "undefined")]) => true
    | _ => false
  | _ => false

def spawnProgram : Program := assemble (actor .spawn [lambda 0 (integer 42)])
#guard spawnProgram.checkScope

def spawnResult := ActorSystem.runChoices (ticks 0 16 ++ ticks 1 8) (ActorSystem.begin spawnProgram)
#guard match spawnResult with
  | .ok system => match system.observe, system.process? 1 with
    | .returned (.ok [.pid 1]), some ⟨1, .halted (.ok [.literal (.integer 42)]), _⟩ =>
        system.nextPid == 2 && system.processes.length == 2
    | _, _ => false
  | _ => false

/-- The compiler's receive loop is an ordinary recursive function. Peeking
returns two values, and rejected messages advance only the mailbox cursor. -/
def receiveProgram : Program := assemble <|
  letRecursive [(0, letValues 2 (actor .peekMessage []) <|
    caseValues (variableRef 1)
      [([.literal (.atom "true")], atom "true",
        caseValues (variableRef 0)
          [([.literal (.atom "a")], atom "true", sequence (actor .removeMessage []) (atom "a")),
           ([.literal (.atom "b")], atom "false", atom "wrong"),
           ([.wildcard], atom "true", sequence (actor .nextMessage []) (apply (variableRef 2) []))]),
       ([.wildcard], atom "true", sequence (actor .waitInfinity []) (apply (variableRef 2) []))])]
    (apply (variableRef 0) [])

#guard receiveProgram.checkScope

def withMailbox (messages : List Value) : ActorSystem :=
  {ActorSystem.begin receiveProgram with
    processes := [⟨0, Erlang.begin receiveProgram, ⟨[], messages, []⟩⟩]}

def receiveResult := ActorSystem.runChoices (ticks 0 300)
  (withMailbox [.literal (.atom "b"), .literal (.atom "a"), .literal (.atom "b")])

#guard match receiveResult with
  | .ok system => match system.observe, system.process? 0 with
    | .returned (.ok [.literal (.atom "a")]), some process =>
        match process.mailbox.contents with
        | [.literal (.atom "b"), .literal (.atom "b")] => true
        | _ => false
    | _, _ => false
  | _ => false

def waitingResult := ActorSystem.runChoices (ticks 0 200) (withMailbox [.literal (.atom "b")])
#guard match waitingResult with
  | .ok system => match system.observe, system.process? 0 with
    | .blocked, some process => match process.mailbox.contents with
      | [.literal (.atom "b")] => true
      | _ => false
    | _, _ => false
  | _ => false

def pendingSystem : Except ActorError ActorSystem := do
  let waiting ← waitingResult
  pure {waiting with network := [⟨⟨1, 0⟩, .literal (.atom "a")⟩]}
#guard match pendingSystem with
  | .ok system => match system.observe with | .pending => true | _ => false
  | _ => false

def awakenedResult : Except ActorError ActorSystem := do
  let pending ← pendingSystem
  ActorSystem.runChoices (.deliver 0 :: ticks 0 200) pending
#guard match awakenedResult with
  | .ok system => match system.observe, system.process? 0 with
    | .returned (.ok [.literal (.atom "a")]), some process =>
        match process.mailbox.contents with | [.literal (.atom "b")] => true | _ => false
    | _, _ => false
  | _ => false

/-- The same complete configuration, including saved prefixes and pending
network work, is obtained when the supplied schedule is interrupted. -/
example : ActorSystem.runChoices (ticks 0 13 ++ ticks 0 187) (withMailbox [.literal (.atom "b")]) =
    (ActorSystem.runChoices (ticks 0 13) (withMailbox [.literal (.atom "b")])).bind
      (ActorSystem.runChoices (ticks 0 187)) :=
  ActorSystem.runChoices_append _ _ _

def overtakeControl : Bool :=
  let system := {withMailbox [] with network :=
    [⟨⟨1, 0⟩, .literal (.atom "first")⟩, ⟨⟨1, 0⟩, .literal (.atom "second")⟩]}
  (system.deliver? 1).isNone
#guard overtakeControl

def collisionControl : Bool :=
  let system := {ActorSystem.begin spawnProgram with nextPid := 0}
  match ActorSystem.runChoices (ticks 0 16) system with
  | .error (.pidCollision 0) => true
  | _ => false
#guard collisionControl

end Mettapedia.Languages.Erlang.ActorControls
