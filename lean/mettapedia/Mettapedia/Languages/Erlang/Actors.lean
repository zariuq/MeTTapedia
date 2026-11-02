import Mettapedia.Languages.Erlang.Machine
import Mettapedia.Languages.Erlang.Network

/-! Local processes over the independent sequential machine and FIFO channels.
Execution and delivery are separate choices. Unavailable choices retain the
configuration; only the explicit quiescence test reports blocked. The emitted
actor controller and its source correspondence are separate obligations. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Erlang

structure LocalProcess where
  identity : Nat
  machine : MachineState
  mailbox : Mailbox Value := {}
  deriving Repr

inductive ActorError where
  | sequential (error : InternalError)
  | mailboxCursor (identity : Nat) (operation : ActorOperation)
  | pidCollision (identity : Nat)
  | invalidSpawn
  deriving Repr

structure ActorSystem where
  program : Program
  processes : List LocalProcess
  network : List (Envelope Value) := []
  nextPid : Nat := 1
  deriving Repr

inductive ActorChoice where
  | execute (processIndex : Nat)
  | deliver (envelopeIndex : Nat)
  deriving Repr, DecidableEq

namespace ActorSystem

def begin (program : Program) : ActorSystem :=
  ⟨program, [⟨0, Erlang.begin program, {}⟩], [], 1⟩

def process? (system : ActorSystem) (identity : Nat) : Option LocalProcess :=
  system.processes.find? fun process => process.identity == identity

def stopped : MachineState → Bool
  | .halted _ => true
  | _ => false

def resume (process : LocalProcess) (values : List Value) (continuation : Continuation) : LocalProcess :=
  {process with machine := .returned values continuation}

def replace (system : ActorSystem) (index : Nat) (process : LocalProcess) : ActorSystem :=
  {system with processes := system.processes.set index process}

/-- Only a request from the selected process is handled. Mailbox scans keep
unmatched occurrences; removing a selected message restores the saved prefix. -/
def request? (system : ActorSystem) (index : Nat) (process : LocalProcess)
    (request : ActorRequest) (continuation : Continuation) : Except ActorError (Option ActorSystem) := do
  let finish := fun values => some (system.replace index (resume process values continuation))
  match request with
  | .self => pure (finish [.pid process.identity])
  | .send receiver message =>
      let next := system.replace index (resume process [message] continuation)
      pure (some {next with network := Network.send ⟨⟨process.identity, receiver⟩, message⟩ next.network})
  | .spawn function =>
      match function with
      | .closure 0 _ _ =>
          if (system.processes.any fun process => process.identity == system.nextPid) then
            throw (.pidCollision system.nextPid)
          let child ← (applyClosure system.program function [] []).mapError ActorError.sequential
          let parent := resume process [.pid system.nextPid] continuation
          pure (some {system with
            processes := system.processes.set index parent ++ [⟨system.nextPid, child, {}⟩]
            nextPid := system.nextPid + 1})
      | _ => throw .invalidSpawn
  | .peekMessage =>
      let box := process.mailbox.normalize
      let values := match box.peek with
        | some message => [boolean true, message]
        | none => [boolean false, .literal (.atom "undefined")]
      pure (some (system.replace index (resume {process with mailbox := box} values continuation)))
  | .nextMessage =>
      match process.mailbox.normalize.next? with
      | none => throw (.mailboxCursor process.identity .nextMessage)
      | some box => pure (some (system.replace index
          (resume {process with mailbox := box} [boolean true] continuation)))
  | .removeMessage =>
      match process.mailbox.normalize.remove? with
      | none => throw (.mailboxCursor process.identity .removeMessage)
      | some box => pure (some (system.replace index
          (resume {process with mailbox := box} [boolean true] continuation)))
  | .waitInfinity =>
      if process.mailbox.unread.isEmpty then pure none
      else pure (finish [boolean false])

def execute? (system : ActorSystem) (index : Nat) : Except ActorError (Option ActorSystem) := do
  let some process := system.processes[index]? | return none
  match process.machine with
  | .request request continuation => system.request? index process request continuation
  | _ =>
      match ← (process.machine.step? system.program).mapError ActorError.sequential with
      | none => pure none
      | some next => pure (some (system.replace index {process with machine := next}))

/-- Delivery uses the independently specified per-channel ordering. Messages
to terminated or absent receivers are discarded; the sender has already returned. -/
def deliver? (system : ActorSystem) (index : Nat) : Option ActorSystem := do
  let (message, pending) ← Network.deliverAt? index system.network
  let processes := system.processes.map fun process =>
    if process.identity = message.key.receiver && !stopped process.machine then
      {process with mailbox := process.mailbox.deliver message.payload}
    else process
  pure {system with network := pending, processes := processes}

def step? (system : ActorSystem) : ActorChoice → Except ActorError (Option ActorSystem)
  | .execute index => system.execute? index
  | .deliver index => .ok (system.deliver? index)

def locallyWaiting (process : LocalProcess) : Bool := match process.machine with
  | .halted _ => true
  | .request .waitInfinity _ => process.mailbox.unread.isEmpty
  | _ => false

/-- Outstanding deliveries prevent a global blocked verdict. -/
def blocked (system : ActorSystem) : Bool :=
  system.network.isEmpty && system.processes.all locallyWaiting

/-- The observation is the initial process's result, independently of whether
other processes have finished. A blocked result still requires global quiescence. -/
inductive Observation where
  | returned (result : Result)
  | blocked
  | pending
  deriving Repr

def observe (system : ActorSystem) : Observation :=
  match system.process? 0 with
  | some ⟨_, .halted result, _⟩ => .returned result
  | some _ => if system.blocked then .blocked else .pending
  | none => .pending

/-- A supplied finite schedule denotes only its prefix, with every pending
process, message and mailbox retained for resumption. -/
def runChoices : List ActorChoice → ActorSystem → Except ActorError ActorSystem
  | [], system => .ok system
  | choice :: choices, system => do
      let next ← system.step? choice
      runChoices choices (next.getD system)

theorem runChoices_append (first second : List ActorChoice) (system : ActorSystem) :
    runChoices (first ++ second) system =
      (runChoices first system).bind (runChoices second) := by
  induction first generalizing system with
  | nil => rfl
  | cons choice choices ih =>
      simp only [List.cons_append, runChoices]
      cases step : system.step? choice with
      | error error => rfl
      | ok next => exact ih (next.getD system)

theorem pending_delivery_not_blocked (system : ActorSystem) (pending : system.network ≠ []) :
    system.blocked = false := by
  cases network : system.network with
  | nil => exact (pending network).elim
  | cons message rest => simp [blocked, network]

/-- A scheduled delivery removes exactly one FIFO-authorized occurrence. -/
theorem delivery_network (system next : ActorSystem) (index : Nat)
    (selected : system.deliver? index = some next) :
    ∃ message, Network.Delivers system.network message next.network := by
  unfold deliver? at selected
  cases result : Network.deliverAt? index system.network with
  | none => simp [result] at selected
  | some pair =>
      rcases pair with ⟨message, pending⟩
      simp only [result] at selected
      dsimp at selected
      cases selected
      exact ⟨message, Network.deliverAt_sound result⟩

/-- A blocked verdict rules out every selected source action, not merely
an outgoing step from one selected process. -/
theorem blocked_no_step (system : ActorSystem) (quiescent : system.blocked = true)
    (choice : ActorChoice) : system.step? choice = .ok none := by
  have parts : system.network = [] ∧ system.processes.all locallyWaiting = true := by
    simpa only [blocked, Bool.and_eq_true, List.isEmpty_iff] using quiescent
  cases choice with
  | deliver index => simp [step?, deliver?, parts.1, Network.deliverAt?]
  | execute index =>
      change system.execute? index = .ok none
      unfold execute?
      cases found : system.processes[index]? with
      | none => rfl
      | some process =>
          dsimp only
          have member : process ∈ system.processes := by
            obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp found
            rw [← same]
            exact List.getElem_mem bound
          have waiting := List.all_eq_true.mp parts.2 process member
          cases machine : process.machine with
          | halted result => rfl
          | evaluate reference environment continuation => simp [locallyWaiting, machine] at waiting
          | returned values continuation => simp [locallyWaiting, machine] at waiting
          | choose arguments clauses environment continuation => simp [locallyWaiting, machine] at waiting
          | request request continuation =>
              cases request <;> simp [locallyWaiting, machine] at waiting
              simp only [request?, waiting, List.isEmpty_nil, if_true]
              rfl

/-- Successful spawning cannot reuse any recorded process identity,
including identities of terminated processes. -/
theorem spawn_fresh (system next : ActorSystem) (index : Nat) (parent : LocalProcess)
    (function : FunctionRef) (captured : Environment) (continuation : Continuation)
    (spawned : system.request? index parent (.spawn (.closure 0 function captured)) continuation = .ok (some next)) :
    ∀ process ∈ system.processes, process.identity ≠ system.nextPid := by
  have fresh : ¬(system.processes.any fun process => process.identity == system.nextPid) = true := by
    intro collided
    simp only [request?, collided, if_true] at spawned
    contradiction
  intro process member same
  apply fresh
  apply List.any_eq_true.mpr
  exact ⟨process, member, by simp [same]⟩

end ActorSystem
end Mettapedia.Languages.Erlang
