import Mettapedia.Languages.Erlang.StandardActorExamples

/-! Worker identity selection and independent-channel scheduling fixtures.
The two causal schedules differ only in permitted delivery choices. They are
witnesses of outcomes, not a proof of complete schedule exploration. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace Mettapedia.Languages.Erlang.ParallelActorExamples

open Assembly StandardActorExamples

private def v := variableRef
private def yes := atom "true"

private def worker (parentSlot : Nat) (input : Int) : Expression :=
  letValues 1 (actor .self []) <|
    actor .send [v (parentSlot + 1), tuple [v 0, primitive .multiply [integer input, integer 2]]]

private def collectWorker (pidSlot : Nat) : Expression :=
  receiveCases [(.tuple [.bind, .bind], primitive .equal [v 1, v (pidSlot + 5)], v 0)]

def parallelMap (first second : Int) : Program := assemble <|
  letValues 1 (actor .self []) <|
    letValues 1 (actor .spawn [lambda 0 (worker 0 first)]) <|
      letValues 1 (actor .spawn [lambda 0 (worker 1 second)]) <|
        letValues 1 (collectWorker 1) <|
          cons (v 0) (cons (collectWorker 1) nil)

private def receiveAny : Expression := receiveCases [(.bind, yes, v 0)]

def twoSenders : Program := assemble <|
  letValues 1 (actor .self []) <|
    letValues 1 (actor .spawn [lambda 0 <|
      sequence (ActorExamples.receiveLiteral (.atom "go")) (actor .send [v 0, atom "b"])]) <|
      sequence (actor .spawn [lambda 0 <|
        sequence (actor .send [v 1, atom "a"]) (actor .send [v 0, atom "go"])]) <|
        letValues 1 receiveAny (tuple [v 0, receiveAny])

def localRound (system : ActorSystem) : Except ActorError ActorSystem :=
  ActorSystem.runChoices ((List.range system.processes.length).map ActorChoice.execute) system

def localRounds : Nat → ActorSystem → Except ActorError ActorSystem
  | 0, system => .ok system
  | count + 1, system => do localRounds count (← localRound system)

def parallelMapResult := ActorExamples.runFair 3000 (ActorSystem.begin (parallelMap 2 3))
def duplicateMapResult := ActorExamples.runFair 3000 (ActorSystem.begin (parallelMap 2 2))
def causalForwardResult := ActorExamples.runFair 3000 (ActorSystem.begin twoSenders)

def reverseWorkerDelivery (program : Program) : Except ActorError ActorSystem := do
  let sent ← localRounds 300 (ActorSystem.begin program)
  let delivered ← ActorSystem.runChoices [.deliver 1, .deliver 0] sent
  localRounds 300 delivered

def parallelMapReverseResult := reverseWorkerDelivery (parallelMap 2 3)
def duplicateMapReverseResult := reverseWorkerDelivery (parallelMap 2 2)

def causalReverseResult : Except ActorError ActorSystem := do
  let sent ← localRounds 300 (ActorSystem.begin twoSenders)
  let triggered ← ActorSystem.runChoices [.deliver 1] sent
  let replied ← localRounds 300 triggered
  let delivered ← ActorSystem.runChoices [.deliver 1, .deliver 0] replied
  localRounds 300 delivered

#guard (parallelMap 2 3).checkScope
#guard (parallelMap 2 2).checkScope
#guard twoSenders.checkScope

private def mapped (result : Except ActorError ActorSystem) (first second : Int) : Bool :=
  match result with
  | .ok system => match system.observe with
    | .returned (.ok [.cons (.literal (.integer a))
        (.cons (.literal (.integer b)) (.literal .nil))]) =>
        a == first && b == second && system.nextPid == 3 && system.network.isEmpty &&
          system.processes.length == 3
    | _ => false
  | _ => false

#guard mapped parallelMapResult 4 6
#guard mapped duplicateMapResult 4 4
#guard mapped parallelMapReverseResult 4 6
#guard mapped duplicateMapReverseResult 4 4

private def ordered (result : Except ActorError ActorSystem) (first second : String) : Bool :=
  match result with
  | .ok system => match system.observe with
    | .returned (.ok [.tuple [.literal (.atom a), .literal (.atom b)]]) =>
        a == first && b == second && system.nextPid == 3 && system.network.isEmpty
    | _ => false
  | _ => false

#guard ordered causalForwardResult "a" "b"
#guard ordered causalReverseResult "b" "a"

end Mettapedia.Languages.Erlang.ParallelActorExamples
