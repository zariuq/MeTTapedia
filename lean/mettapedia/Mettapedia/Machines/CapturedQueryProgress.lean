import Mettapedia.Machines.ArenaHeldResources

/-!
# Captured queries, host reads, and semantic progress

A captured query enumerates a fixed sequence of occurrence identities while its
body may change the live world.  This module separates the capture, the remaining
program, an outstanding host read, its completed result, committed effect
receipts, ordered answer publication, and work accounting.

The reference interpreter has no suspension or host protocol.  The host machine
has the same three instruction kinds, but a read takes a request, a checked host
completion, and a result-consuming transition.  Thus a pause cannot replay an
effect: an effect instruction is removed when its receipt is appended.  A new
read is evaluated in the reached world, not in the original capture.

Two capture policies model a concrete continuation-capture defect.  The old
policy rejects a live, shareable, lifetime-tracked fresh space and reports the
rejection as retryable suspension.  Work increases while the outstanding request
stays unchanged.  The repaired semantic policy retains the completed result;
`captureComplete` separately composes that transition with a successful arena
capture receipt and actual resource holds.  If a resource is genuinely
unavailable or unshareable, refusal is terminal and explicit rather than a
promise that retrying the identical state is progress.  External changes before
completion carry different revision tokens and require host revalidation; an
own effect is committed before its subsequent request is made.  This control
does not model every possible callback or publication race.

Answer order is contractual in this sequential fragment, so answers and captured
occurrences are lists.  Effects retain their causal order as well.  A parallel
implementation may relax answer order only with a separate multiset contract.

The progress theorem concerns only finite instruction lists, an available
shareable resource, current dependency tokens, and a scheduler that resumes with
one unit whenever necessary.  It says nothing about arbitrary MeTTa programs,
permanent outages, or exhausted hosts.  `ArenaHeldResources` supplies the
independent lifetime theorem used at the resource-correspondence boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CapturedQueryProgress

universe u
variable {Payload : Type u}

/-- Identity is not payload equality. -/
structure Occurrence (Payload : Type u) where
  id : Nat
  payload : Payload
  deriving DecidableEq

inductive Effect (Payload : Type u) where
  | append (occurrence : Occurrence Payload)
  | remove (captureId : Nat)
  deriving DecidableEq

inductive Answer (Payload : Type u) where
  | atom (payload : Payload)
  | pair (left right : Payload)
  deriving DecidableEq

structure World (Payload : Type u) where
  rows : List (Occurrence Payload)
  revision : Nat
  deriving DecidableEq

/-- Append preserves old occurrences and their order; removal addresses identity. -/
def applyEffect (effect : Effect Payload) (world : World Payload) : World Payload :=
  match effect with
  | .append occurrence => ⟨world.rows ++ [occurrence], world.revision + 1⟩
  | .remove captureId =>
      ⟨world.rows.filter fun row => row.id != captureId, world.revision + 1⟩

inductive Instruction (Payload : Type u) where
  | effect (effect : Effect Payload)
  | answer (answer : Answer Payload)
  | read (source : Occurrence Payload) (pattern : Payload → Bool)

structure ReadRequest (Payload : Type u) where
  source : Occurrence Payload
  pattern : Payload → Bool
  revision : Nat

structure ReadResult (Payload : Type u) where
  revision : Nat
  answers : List (Answer Payload)
  deriving DecidableEq

/-- The independent host-read contract: every currently matching occurrence,
in world order, including equal payloads at distinct identities. -/
def readAnswers (request : ReadRequest Payload) (world : World Payload) :
    List (Answer Payload) :=
  (world.rows.filter fun row => request.pattern row.payload).map fun row =>
    .pair request.source.payload row.payload

/-- The reference has no host state, budget, or suspension. -/
structure Reference (Payload : Type u) where
  world : World Payload
  effects : List (Effect Payload)
  answers : List (Answer Payload)
  deriving DecidableEq

def Reference.initial (world : World Payload) : Reference Payload := ⟨world, [], []⟩

def execute : List (Instruction Payload) → Reference Payload → Reference Payload
  | [], reference => reference
  | .effect effect :: rest, reference =>
      execute rest { reference with
        world := applyEffect effect reference.world
        effects := reference.effects ++ [effect] }
  | .answer answer :: rest, reference =>
      execute rest { reference with answers := reference.answers ++ [answer] }
  | .read source pattern :: rest, reference =>
      let request : ReadRequest Payload := ⟨source, pattern, reference.world.revision⟩
      execute rest { reference with
        answers := reference.answers ++ readAnswers request reference.world }

inductive CapturePolicy where
  | old
  | repaired
  deriving DecidableEq

inductive ResourceKind where
  | arena
  | root
  | trackedFresh
  | foreign
  deriving DecidableEq

structure Resource where
  kind : ResourceKind
  live : Bool
  shareable : Bool
  deriving DecidableEq

/-- The old admission family omitted malloc-backed, lifetime-tracked spaces. -/
def admits (policy : CapturePolicy) (resource : Resource) : Bool :=
  resource.live && resource.shareable &&
    match policy, resource.kind with
    | .old, .arena | .old, .root | .repaired, _ => true
    | _, _ => false

inductive Status where
  | running
  | suspended
  | finished
  | captureRefused
  deriving DecidableEq

structure Machine (Payload : Type u) where
  world : World Payload
  captured : List (Occurrence Payload)
  remaining : List (Instruction Payload)
  outstanding : Option (ReadRequest Payload)
  completed : Option (ReadResult Payload)
  effects : List (Effect Payload)
  answers : List (Answer Payload)
  resource : Resource
  /-- A completed host result is retained, not a resource-lifetime receipt. -/
  resultHeld : Bool
  work : Nat
  budget : Nat
  status : Status

/-- The outstanding request, not merely the ordinary remaining list, is part of
the program position. -/
def continuation (machine : Machine Payload) : List (Instruction Payload) :=
  match machine.outstanding with
  | none => machine.remaining
  | some request => .read request.source request.pattern :: machine.remaining

def semantic (machine : Machine Payload) : Reference Payload :=
  ⟨machine.world, machine.effects, machine.answers⟩

def initial (captured : List (Occurrence Payload)) (program : List (Instruction Payload))
    (resource : Resource) : Machine Payload :=
  { world := ⟨captured, 0⟩
    captured := captured
    remaining := program
    outstanding := none
    completed := none
    effects := []
    answers := []
    resource := resource
    resultHeld := false
    work := 0
    budget := 0
    status := .running }

/-- A completed result belongs to the current reached world.  `resultHeld`
tracks this host-result buffer only; it is not an arena ownership receipt. -/
def HostValid (machine : Machine Payload) : Prop :=
  machine.resultHeld = machine.completed.isSome ∧
    match machine.outstanding, machine.completed with
    | none, none => True
    | some _, none => True
    | some request, some result =>
        result.revision = machine.world.revision ∧
        result.answers = readAnswers request machine.world
    | none, some _ => False

/-- Conditions for the finite, no-external-interference progress fragment. -/
def Supported (machine : Machine Payload) : Prop :=
  admits .repaired machine.resource = true ∧
    match machine.outstanding with
    | none => True
    | some request => request.revision = machine.world.revision

private def charge (machine : Machine Payload) : Machine Payload :=
  let charged := { machine with work := machine.work + 1, budget := machine.budget - 1 }
  if (continuation charged).isEmpty then { charged with status := .finished }
  else if charged.budget = 0 then { charged with status := .suspended }
  else charged

private def consumeResult (machine : Machine Payload) (result : ReadResult Payload) :
    Machine Payload :=
  charge { machine with
    answers := machine.answers ++ result.answers
    outstanding := none
    completed := none
    resultHeld := false }

private def refreshRequest (machine : Machine Payload) (request : ReadRequest Payload) :
    Machine Payload :=
  charge { machine with
    outstanding := some { request with revision := machine.world.revision } }

private def completeRequest (policy : CapturePolicy) (machine : Machine Payload)
    (request : ReadRequest Payload) : Machine Payload :=
  if admits policy machine.resource then
    charge { machine with
      completed := some ⟨machine.world.revision, readAnswers request machine.world⟩
      resultHeld := true }
  else
    let refused := charge machine
    match policy with
    | .old => { refused with status := .suspended }
    | .repaired => { refused with status := .captureRefused }

private def perform (machine : Machine Payload) (instruction : Instruction Payload)
    (rest : List (Instruction Payload)) : Machine Payload :=
  match instruction with
  | .effect effect =>
      charge { machine with
        world := applyEffect effect machine.world
        remaining := rest
        effects := machine.effects ++ [effect] }
  | .answer answer =>
      charge { machine with
        remaining := rest
        answers := machine.answers ++ [answer] }
  | .read source pattern =>
      charge { machine with
        remaining := rest
        outstanding := some ⟨source, pattern, machine.world.revision⟩ }

/-- Execute one charged host-machine transition.  Suspension from budget exhaustion
performs no semantic work. -/
def work (policy : CapturePolicy) (machine : Machine Payload) : Machine Payload :=
  match machine.status with
  | .suspended | .finished | .captureRefused => machine
  | .running =>
      if (continuation machine).isEmpty then { machine with status := .finished }
      else if machine.budget = 0 then { machine with status := .suspended }
      else
        match machine.outstanding with
        | some request =>
            match machine.completed with
            | some result => consumeResult machine result
            | none =>
                if request.revision != machine.world.revision then
                  refreshRequest machine request
                else completeRequest policy machine request
        | none =>
            match machine.remaining with
            | [] => { machine with status := .finished }
            | instruction :: rest => perform machine instruction rest

/-- An observation resume supplies budget only; it cannot change the world,
capture, continuation, effects, answers, resource hold, or work counter. -/
def resume (allowance : Nat) (machine : Machine Payload) : Machine Payload :=
  match machine.status with
  | .suspended => { machine with budget := allowance, status := .running }
  | _ => machine

private def activate (machine : Machine Payload) : Machine Payload :=
  match machine.status with
  | .suspended => resume 1 machine
  | .running => if machine.budget = 0 then { machine with budget := 1 } else machine
  | _ => machine

/-- One fair scheduler step: resume if needed, then offer one unit of work. -/
def autoStep (policy : CapturePolicy) (machine : Machine Payload) : Machine Payload :=
  work policy (activate machine)

def drive (policy : CapturePolicy) : Nat → Machine Payload → Machine Payload
  | 0, machine => machine
  | fuel + 1, machine => drive policy fuel (autoStep policy machine)

/-- Number of charged transitions left in the finite supported fragment. -/
def instructionCost : Instruction Payload → Nat
  | .read _ _ => 3
  | _ => 1

def programCost (program : List (Instruction Payload)) : Nat :=
  (program.map instructionCost).sum

def remainingWork (machine : Machine Payload) : Nat :=
  match machine.outstanding with
  | none => programCost machine.remaining
  | some _ => (if machine.completed.isSome then 1 else 2) + programCost machine.remaining

/-! ## General reachable-state invariants -/

/-- The machine is an exact reference-execution prefix followed by its retained
continuation.  This is proved from the transitions, not assumed as a definition
of successful completion. -/
def PrefixInvariant (machine : Machine Payload) (program : List (Instruction Payload))
    (start : Reference Payload) : Prop :=
  HostValid machine ∧
    ∃ executed, program = executed ++ continuation machine ∧
      semantic machine = execute executed start

theorem initial_prefix (captured : List (Occurrence Payload))
    (program : List (Instruction Payload)) (resource : Resource) :
    PrefixInvariant (initial captured program resource) program
      (Reference.initial ⟨captured, 0⟩) := by
  constructor
  · exact ⟨rfl, trivial⟩
  · exact ⟨[], rfl, rfl⟩

theorem resume_prefix {machine : Machine Payload} {program : List (Instruction Payload)}
    {start : Reference Payload} (allowance : Nat)
    (invariant : PrefixInvariant machine program start) :
    PrefixInvariant (resume allowance machine) program start := by
  obtain ⟨valid, executed, split, current⟩ := invariant
  unfold resume
  split <;> exact ⟨valid, executed, split, current⟩

theorem execute_append (first second : List (Instruction Payload))
    (reference : Reference Payload) :
    execute (first ++ second) reference = execute second (execute first reference) := by
  induction first generalizing reference with
  | nil => rfl
  | cons instruction rest ih =>
      cases instruction <;> simp only [List.cons_append, execute] <;> apply ih

private theorem charge_continuation (machine : Machine Payload) :
    continuation (charge machine) = continuation machine := by
  unfold charge
  dsimp only
  split
  · rfl
  · split <;> rfl

private theorem charge_semantic (machine : Machine Payload) :
    semantic (charge machine) = semantic machine := by
  unfold charge
  dsimp only
  split
  · rfl
  · split <;> rfl

private theorem charge_valid {machine : Machine Payload} (valid : HostValid machine) :
    HostValid (charge machine) := by
  unfold charge
  dsimp only
  split
  · exact valid
  · split <;> exact valid

private theorem charge_prefix {machine : Machine Payload} {program : List (Instruction Payload)}
    {start : Reference Payload} (invariant : PrefixInvariant machine program start) :
    PrefixInvariant (charge machine) program start := by
  obtain ⟨valid, executed, split, current⟩ := invariant
  refine ⟨charge_valid valid, executed, ?_, ?_⟩
  · simpa only [charge_continuation] using split
  · simpa only [charge_semantic] using current

private theorem refreshRequest_prefix {machine : Machine Payload} {request : ReadRequest Payload}
    {program : List (Instruction Payload)} {start : Reference Payload}
    (outstanding : machine.outstanding = some request)
    (invariant : PrefixInvariant machine program start) :
    PrefixInvariant (refreshRequest machine request) program start := by
  apply charge_prefix
  obtain ⟨valid, executed, split, current⟩ := invariant
  refine ⟨?_, executed, ?_, current⟩
  · cases completed : machine.completed <;>
      simp [HostValid, outstanding, completed, readAnswers] at valid ⊢ <;> assumption
  · simpa [continuation, outstanding] using split

private theorem completeRequest_prefix {machine : Machine Payload}
    {request : ReadRequest Payload} {program : List (Instruction Payload)}
    {start : Reference Payload} (policy : CapturePolicy)
    (outstanding : machine.outstanding = some request) (_completed : machine.completed = none)
    (invariant : PrefixInvariant machine program start) :
    PrefixInvariant (completeRequest policy machine request) program start := by
  obtain ⟨valid, executed, split, current⟩ := invariant
  unfold completeRequest
  split
  · apply charge_prefix
    refine ⟨?_, executed, ?_, current⟩
    · simp [HostValid, outstanding]
    · simpa [continuation, outstanding] using split
  · split <;> exact charge_prefix ⟨valid, executed, split, current⟩

private theorem consumeResult_prefix {machine : Machine Payload} {request : ReadRequest Payload}
    {result : ReadResult Payload} {program : List (Instruction Payload)}
    {start : Reference Payload} (outstanding : machine.outstanding = some request)
    (completed : machine.completed = some result)
    (invariant : PrefixInvariant machine program start) :
    PrefixInvariant (consumeResult machine result) program start := by
  obtain ⟨valid, executed, split, current⟩ := invariant
  have valid' := valid
  simp [HostValid, outstanding, completed] at valid'
  apply charge_prefix
  refine ⟨?_, executed ++ [.read request.source request.pattern], ?_, ?_⟩
  · simp [HostValid]
  · rw [List.append_assoc]
    simpa [continuation, outstanding] using split
  · rw [execute_append, ← current]
    simp [execute, semantic, readAnswers, valid'.2.2]

private theorem perform_prefix {machine : Machine Payload}
    (instruction : Instruction Payload) (rest : List (Instruction Payload))
    {program : List (Instruction Payload)} {start : Reference Payload}
    (outstanding : machine.outstanding = none)
    (remaining : machine.remaining = instruction :: rest)
    (invariant : PrefixInvariant machine program start) :
    PrefixInvariant (perform machine instruction rest) program start := by
  have completed : machine.completed = none := by
    cases result : machine.completed with
    | none => rfl
    | some result =>
        obtain ⟨valid, _⟩ := invariant
        simp [HostValid, outstanding, result] at valid
  cases instruction with
  | effect effect =>
      apply charge_prefix
      obtain ⟨valid, executed, split, current⟩ := invariant
      refine ⟨?_, executed ++ [.effect effect], ?_, ?_⟩
      · simpa [HostValid, outstanding, completed] using valid
      · rw [List.append_assoc]
        simpa [continuation, outstanding, remaining] using split
      · rw [execute_append, ← current]
        rfl
  | answer answer =>
      apply charge_prefix
      obtain ⟨valid, executed, split, current⟩ := invariant
      refine ⟨?_, executed ++ [.answer answer], ?_, ?_⟩
      · simpa [HostValid, outstanding, completed] using valid
      · rw [List.append_assoc]
        simpa [continuation, outstanding, remaining] using split
      · rw [execute_append, ← current]
        rfl
  | read source pattern =>
      apply charge_prefix
      obtain ⟨valid, executed, split, current⟩ := invariant
      refine ⟨?_, executed, ?_, current⟩
      · simpa [HostValid, outstanding, completed] using valid
      · simpa [continuation, outstanding, remaining] using split

theorem work_prefix {machine : Machine Payload} {program : List (Instruction Payload)}
    {start : Reference Payload} (policy : CapturePolicy)
    (invariant : PrefixInvariant machine program start) :
    PrefixInvariant (work policy machine) program start := by
  cases status : machine.status with
  | running =>
      simp only [work, status]
      split
      · exact invariant
      split
      · exact invariant
      cases outstanding : machine.outstanding with
      | none =>
          simp only
          cases remaining : machine.remaining with
          | nil =>
              simpa only [remaining, outstanding] using
                (show PrefixInvariant { machine with status := .finished } program start from invariant)
          | cons instruction rest =>
              simp only
              exact perform_prefix instruction rest outstanding remaining invariant
      | some request =>
          simp only
          cases completed : machine.completed with
          | none =>
              simp only
              split
              · exact refreshRequest_prefix outstanding invariant
              · exact completeRequest_prefix policy outstanding completed invariant
          | some result =>
              simp only
              exact consumeResult_prefix outstanding completed invariant
  | suspended => simpa [work, status] using invariant
  | finished => simpa [work, status] using invariant
  | captureRefused => simpa [work, status] using invariant

theorem autoStep_prefix {machine : Machine Payload} {program : List (Instruction Payload)}
    {start : Reference Payload} (policy : CapturePolicy)
    (invariant : PrefixInvariant machine program start) :
    PrefixInvariant (autoStep policy machine) program start := by
  apply work_prefix
  cases status : machine.status with
  | running =>
      simp only [activate, status]
      split <;> exact invariant
  | suspended => simpa [activate, status] using resume_prefix 1 invariant
  | finished => simpa [activate, status] using invariant
  | captureRefused => simpa [activate, status] using invariant

theorem drive_prefix {machine : Machine Payload} {program : List (Instruction Payload)}
    {start : Reference Payload} (policy : CapturePolicy) (fuel : Nat)
    (invariant : PrefixInvariant machine program start) :
    PrefixInvariant (drive policy fuel machine) program start := by
  induction fuel generalizing machine with
  | zero => exact invariant
  | succ fuel ih => exact ih (autoStep_prefix policy invariant)

private theorem charge_supported {machine : Machine Payload} (supported : Supported machine) :
    Supported (charge machine) := by
  unfold charge
  dsimp only
  split
  · exact supported
  · split <;> exact supported

private theorem refreshRequest_supported {machine : Machine Payload}
    {request : ReadRequest Payload} (_outstanding : machine.outstanding = some request)
    (supported : Supported machine) : Supported (refreshRequest machine request) := by
  apply charge_supported
  exact ⟨supported.1, by simp⟩

private theorem completeRequest_supported {machine : Machine Payload}
    {request : ReadRequest Payload} (policy : CapturePolicy)
    (supported : Supported machine) : Supported (completeRequest policy machine request) := by
  unfold completeRequest
  split
  · exact charge_supported supported
  · split <;> exact charge_supported supported

private theorem consumeResult_supported {machine : Machine Payload} {result : ReadResult Payload}
    (supported : Supported machine) : Supported (consumeResult machine result) := by
  apply charge_supported
  exact ⟨supported.1, trivial⟩

private theorem perform_supported {machine : Machine Payload}
    (instruction : Instruction Payload) (rest : List (Instruction Payload))
    (outstanding : machine.outstanding = none) (supported : Supported machine) :
    Supported (perform machine instruction rest) := by
  cases instruction <;> apply charge_supported
  · simpa [Supported, outstanding] using supported
  · simpa [Supported, outstanding] using supported
  · exact ⟨supported.1, rfl⟩

theorem work_supported (policy : CapturePolicy) {machine : Machine Payload}
    (supported : Supported machine) : Supported (work policy machine) := by
  cases status : machine.status with
  | running =>
      simp only [work, status]
      split
      · exact supported
      split
      · exact supported
      cases outstanding : machine.outstanding with
      | none =>
          simp only
          cases remaining : machine.remaining with
          | nil =>
              simpa only [remaining, outstanding] using
                (show Supported { machine with status := .finished } from supported)
          | cons instruction rest =>
              simp only
              exact perform_supported instruction rest outstanding supported
      | some request =>
          simp only
          cases completed : machine.completed with
          | none =>
              simp only
              split
              · exact refreshRequest_supported outstanding supported
              · exact completeRequest_supported policy supported
          | some result =>
              simp only
              exact consumeResult_supported supported
  | suspended => simpa [work, status] using supported
  | finished => simpa [work, status] using supported
  | captureRefused => simpa [work, status] using supported

private theorem activate_supported {machine : Machine Payload} (supported : Supported machine) :
    Supported (activate machine) := by
  cases status : machine.status with
  | running =>
      simp only [activate, status]
      split <;> exact supported
  | suspended => simpa [activate, resume, status, Supported] using supported
  | finished => simpa [activate, status] using supported
  | captureRefused => simpa [activate, status] using supported

theorem autoStep_supported (policy : CapturePolicy) {machine : Machine Payload}
    (supported : Supported machine) : Supported (autoStep policy machine) := by
  exact work_supported policy (activate_supported supported)

theorem drive_supported (policy : CapturePolicy) (fuel : Nat) {machine : Machine Payload}
    (supported : Supported machine) : Supported (drive policy fuel machine) := by
  induction fuel generalizing machine with
  | zero => exact supported
  | succ fuel ih => exact ih (autoStep_supported policy supported)

private theorem charge_remainingWork (machine : Machine Payload) :
    remainingWork (charge machine) = remainingWork machine := by
  unfold charge
  dsimp only
  split
  · rfl
  · split <;> rfl

/-- A current, admitted running transition strictly decreases the finite semantic
work measure.  Numeric `work` increases separately; this measure counts host
transitions still needed by the retained program. -/
theorem work_remainingWork_lt {machine : Machine Payload} (supported : Supported machine)
    (running : machine.status = .running) (budget : machine.budget ≠ 0)
    (nonempty : continuation machine ≠ []) :
    remainingWork (work .repaired machine) < remainingWork machine := by
  have notEmpty : ¬(continuation machine).isEmpty = true := by
    intro empty
    apply nonempty
    simpa using empty
  simp only [work, running, notEmpty, budget, Bool.false_eq_true, ↓reduceIte]
  cases outstanding : machine.outstanding with
  | none =>
      simp only
      cases remaining : machine.remaining with
      | nil =>
          simp [continuation, outstanding, remaining] at nonempty
      | cons instruction rest =>
          simp only
          cases instruction with
          | effect effect =>
              simp only [perform, charge_remainingWork]
              simp [remainingWork, outstanding, remaining, programCost, instructionCost]
          | answer answer =>
              simp only [perform, charge_remainingWork]
              simp [remainingWork, outstanding, remaining, programCost, instructionCost]
          | read source pattern =>
              simp only [perform, charge_remainingWork]
              simp [remainingWork, outstanding, remaining, programCost, instructionCost]
              split <;> omega
  | some request =>
      simp only
      cases completed : machine.completed with
      | none =>
          simp only
          have current := supported.2
          simp [outstanding] at current
          split
          · rename_i stale
            simp [current] at stale
          · simp only [completeRequest, supported.1, ↓reduceIte, charge_remainingWork]
            simp [remainingWork, outstanding, completed]
      | some result =>
          simp only
          simp only [consumeResult, charge_remainingWork]
          simp [remainingWork, outstanding, completed]

private theorem activate_running {machine : Machine Payload}
    (live : machine.status = .running ∨ machine.status = .suspended) :
    (activate machine).status = .running := by
  cases status : machine.status with
  | running =>
      simp only [activate, status]
      split
      · rfl
      · exact status
  | suspended => simp [activate, resume, status]
  | finished => simp [status] at live
  | captureRefused => simp [status] at live

private theorem activate_budget {machine : Machine Payload}
    (live : machine.status = .running ∨ machine.status = .suspended) :
    (activate machine).budget ≠ 0 := by
  cases status : machine.status with
  | running =>
      simp only [activate, status]
      split
      · simp
      · assumption
  | suspended => simp [activate, resume, status]
  | finished => simp [status] at live
  | captureRefused => simp [status] at live

private theorem activate_continuation (machine : Machine Payload) :
    continuation (activate machine) = continuation machine := by
  unfold activate resume
  (repeat' split) <;> rfl

private theorem activate_remainingWork (machine : Machine Payload) :
    remainingWork (activate machine) = remainingWork machine := by
  unfold activate resume
  (repeat' split) <;> rfl

/-- Fair activation supplies exactly the missing observation unit and then makes
strict semantic progress in the supported fragment. -/
theorem autoStep_remainingWork_lt {machine : Machine Payload} (supported : Supported machine)
    (live : machine.status = .running ∨ machine.status = .suspended)
    (nonempty : continuation machine ≠ []) :
    remainingWork (autoStep .repaired machine) < remainingWork machine := by
  unfold autoStep
  rw [← activate_remainingWork machine]
  apply work_remainingWork_lt (activate_supported supported) (activate_running live)
    (activate_budget live)
  rw [activate_continuation]
  exact nonempty

theorem programCost_eq_nil {program : List (Instruction Payload)}
    (zero : programCost program = 0) : program = [] := by
  cases program with
  | nil => rfl
  | cons instruction rest =>
      cases instruction <;> simp [programCost, instructionCost] at zero

theorem continuation_empty_of_remainingWork_zero {machine : Machine Payload}
    (zero : remainingWork machine = 0) : continuation machine = [] := by
  cases outstanding : machine.outstanding with
  | none =>
      have cost : programCost machine.remaining = 0 := by
        simpa [remainingWork, outstanding] using zero
      simp [continuation, outstanding, programCost_eq_nil cost]
  | some request =>
      simp [remainingWork, outstanding] at zero
      split at zero <;> simp at zero

private theorem charge_finished_empty {machine : Machine Payload}
    (running : machine.status = .running) (finished : (charge machine).status = .finished) :
    continuation (charge machine) = [] := by
  unfold charge at finished ⊢
  dsimp only at finished ⊢
  split
  · rename_i empty
    change continuation { machine with work := machine.work + 1, budget := machine.budget - 1 } = []
    simpa using empty
  · rename_i notEmpty
    simp only [notEmpty] at finished
    split
    · rename_i exhausted
      simp [exhausted] at finished
    · rename_i notBudget
      simp only [notBudget, ↓reduceIte] at finished
      simp [running] at finished

private theorem charge_not_refused {machine : Machine Payload}
    (running : machine.status = .running) : (charge machine).status ≠ .captureRefused := by
  unfold charge
  dsimp only
  split
  · simp
  · split <;> simp [running]

private theorem consumeResult_finished_empty {machine : Machine Payload} {result : ReadResult Payload}
    (running : machine.status = .running) (finished : (consumeResult machine result).status = .finished) :
    continuation (consumeResult machine result) = [] := by
  exact charge_finished_empty running finished

private theorem refreshRequest_finished_empty {machine : Machine Payload} {request : ReadRequest Payload}
    (running : machine.status = .running)
    (finished : (refreshRequest machine request).status = .finished) :
    continuation (refreshRequest machine request) = [] := by
  exact charge_finished_empty running finished

private theorem completeRequest_finished_empty {machine : Machine Payload}
    {request : ReadRequest Payload} (policy : CapturePolicy) (running : machine.status = .running)
    (finished : (completeRequest policy machine request).status = .finished) :
    continuation (completeRequest policy machine request) = [] := by
  unfold completeRequest at finished ⊢
  split
  · rename_i admitted
    simp only [admitted, ↓reduceIte] at finished
    exact charge_finished_empty running finished
  · rename_i refused
    simp only [refused] at finished
    cases policy <;> simp at finished

private theorem perform_finished_empty {machine : Machine Payload}
    (instruction : Instruction Payload) (rest : List (Instruction Payload))
    (running : machine.status = .running)
    (finished : (perform machine instruction rest).status = .finished) :
    continuation (perform machine instruction rest) = [] := by
  cases instruction <;> exact charge_finished_empty running finished

private theorem work_finished_empty (policy : CapturePolicy) {machine : Machine Payload}
    (running : machine.status = .running) (finished : (work policy machine).status = .finished) :
    continuation (work policy machine) = [] := by
  simp only [work, running] at finished ⊢
  split
  · rename_i empty
    change continuation machine = []
    simpa using empty
  · rename_i notEmpty
    simp only [notEmpty] at finished
    split
    · rename_i exhausted
      simp [exhausted] at finished
    · rename_i notBudget
      simp only [notBudget, ↓reduceIte] at finished
      cases outstanding : machine.outstanding with
      | none =>
          simp only [outstanding] at finished ⊢
          cases remaining : machine.remaining with
          | nil =>
              simp [continuation]
          | cons instruction rest =>
              simp only [remaining] at finished ⊢
              exact perform_finished_empty instruction rest running finished
      | some request =>
          simp only [outstanding] at finished ⊢
          cases completed : machine.completed with
          | none =>
              simp only [completed] at finished ⊢
              split
              · rename_i stale
                simp only [stale, ↓reduceIte] at finished
                exact refreshRequest_finished_empty running finished
              · rename_i current
                simp only [current] at finished
                exact completeRequest_finished_empty policy running finished
          | some result =>
              simp only [completed] at finished ⊢
              exact consumeResult_finished_empty running finished

private theorem consumeResult_not_refused {machine : Machine Payload} {result : ReadResult Payload}
    (running : machine.status = .running) :
    (consumeResult machine result).status ≠ .captureRefused := by
  exact charge_not_refused running

private theorem refreshRequest_not_refused {machine : Machine Payload} {request : ReadRequest Payload}
    (running : machine.status = .running) :
    (refreshRequest machine request).status ≠ .captureRefused := by
  exact charge_not_refused running

private theorem completeRequest_not_refused {machine : Machine Payload}
    {request : ReadRequest Payload} (supported : Supported machine)
    (running : machine.status = .running) :
    (completeRequest .repaired machine request).status ≠ .captureRefused := by
  unfold completeRequest
  rw [if_pos supported.1]
  exact charge_not_refused running

private theorem perform_not_refused {machine : Machine Payload}
    (instruction : Instruction Payload) (rest : List (Instruction Payload))
    (running : machine.status = .running) :
    (perform machine instruction rest).status ≠ .captureRefused := by
  cases instruction <;> exact charge_not_refused running

private theorem work_not_refused {machine : Machine Payload} (supported : Supported machine)
    (running : machine.status = .running) :
    (work .repaired machine).status ≠ .captureRefused := by
  simp only [work, running]
  split
  · simp
  split
  · simp
  cases outstanding : machine.outstanding with
  | none =>
      simp only
      cases remaining : machine.remaining with
      | nil => simp
      | cons instruction rest =>
          simp only
          exact perform_not_refused instruction rest running
  | some request =>
      simp only
      cases completed : machine.completed with
      | none =>
          simp only
          split
          · exact refreshRequest_not_refused running
          · exact completeRequest_not_refused supported running
      | some result =>
          simp only
          exact consumeResult_not_refused running

private theorem autoStep_finished_empty {machine : Machine Payload}
    (live : machine.status = .running ∨ machine.status = .suspended)
    (finished : (autoStep .repaired machine).status = .finished) :
    continuation (autoStep .repaired machine) = [] := by
  exact work_finished_empty .repaired (activate_running live) finished

private theorem autoStep_not_refused {machine : Machine Payload} (supported : Supported machine)
    (live : machine.status = .running ∨ machine.status = .suspended) :
    (autoStep .repaired machine).status ≠ .captureRefused := by
  exact work_not_refused (activate_supported supported) (activate_running live)

private theorem autoStep_live_or_finished {machine : Machine Payload} (supported : Supported machine)
    (live : machine.status = .running ∨ machine.status = .suspended) :
    ((autoStep .repaired machine).status = .running ∨
        (autoStep .repaired machine).status = .suspended) ∨
      ((autoStep .repaired machine).status = .finished ∧
        continuation (autoStep .repaired machine) = []) := by
  cases status : (autoStep .repaired machine).status with
  | running => exact Or.inl (Or.inl rfl)
  | suspended => exact Or.inl (Or.inr rfl)
  | finished => exact Or.inr ⟨rfl, autoStep_finished_empty live status⟩
  | captureRefused => exact absurd status (autoStep_not_refused supported live)

private theorem autoStep_empty_finished {machine : Machine Payload}
    (live : machine.status = .running ∨ machine.status = .suspended)
    (empty : continuation machine = []) :
    (autoStep .repaired machine).status = .finished := by
  have running := activate_running live
  have activatedEmpty : continuation (activate machine) = [] := by
    rw [activate_continuation]
    exact empty
  simp [autoStep, work, running, activatedEmpty]

private theorem autoStep_empty_continuation {machine : Machine Payload}
    (live : machine.status = .running ∨ machine.status = .suspended)
    (empty : continuation machine = []) :
    continuation (autoStep .repaired machine) = [] := by
  exact autoStep_finished_empty live (autoStep_empty_finished live empty)

theorem drive_finished (policy : CapturePolicy) (fuel : Nat) {machine : Machine Payload}
    (finished : machine.status = .finished) : drive policy fuel machine = machine := by
  induction fuel generalizing machine with
  | zero => rfl
  | succ fuel ih =>
      have frozen : autoStep policy machine = machine := by
        simp [autoStep, activate, work, finished]
      rw [drive, frozen]
      exact ih finished

theorem semantic_eq_execute_of_prefix_empty {machine : Machine Payload}
    {program : List (Instruction Payload)} {start : Reference Payload}
    (invariant : PrefixInvariant machine program start) (empty : continuation machine = []) :
    semantic machine = execute program start := by
  obtain ⟨_, executed, split, current⟩ := invariant
  rw [empty, List.append_nil] at split
  rwa [split]

/-- Fair driving of a supported finite prefix finishes within its semantic work
measure plus one observation.  The final state has no retained program and is
exactly the host-free reference execution. -/
theorem drive_composes {machine : Machine Payload} {program : List (Instruction Payload)}
    {start : Reference Payload} (fuel : Nat) (bound : remainingWork machine < fuel)
    (supported : Supported machine) (invariant : PrefixInvariant machine program start)
    (live : machine.status = .running ∨ machine.status = .suspended) :
    let final := drive .repaired fuel machine
    final.status = .finished ∧ continuation final = [] ∧
      semantic final = execute program start := by
  induction fuel generalizing machine with
  | zero => simp at bound
  | succ fuel ih =>
      by_cases empty : continuation machine = []
      · have finished := autoStep_empty_finished live empty
        have continuationEmpty := autoStep_empty_continuation live empty
        rw [drive, drive_finished .repaired fuel finished]
        exact ⟨finished, continuationEmpty,
          semantic_eq_execute_of_prefix_empty (autoStep_prefix .repaired invariant) continuationEmpty⟩
      · have decrease := autoStep_remainingWork_lt supported live empty
        rcases autoStep_live_or_finished supported live with nextLive | ⟨finished, continuationEmpty⟩
        · rw [drive]
          exact ih (machine := autoStep .repaired machine) (by omega)
            (autoStep_supported .repaired supported) (autoStep_prefix .repaired invariant) nextLive
        · rw [drive, drive_finished .repaired fuel finished]
          exact ⟨finished, continuationEmpty,
            semantic_eq_execute_of_prefix_empty (autoStep_prefix .repaired invariant) continuationEmpty⟩

/-- The general composed contract from the initial machine, with fuel computed
from the independent finite program rather than from implementation counters. -/
theorem initial_drive_composes (captured : List (Occurrence Payload))
    (program : List (Instruction Payload)) (resource : Resource)
    (admitted : admits .repaired resource = true) :
    let final := drive .repaired (programCost program + 1) (initial captured program resource)
    final.status = .finished ∧ continuation final = [] ∧
      semantic final = execute program (Reference.initial ⟨captured, 0⟩) := by
  apply drive_composes
  · simp [remainingWork, initial]
  · exact ⟨admitted, trivial⟩
  · exact initial_prefix captured program resource
  · exact Or.inl rfl

private theorem charge_captured (machine : Machine Payload) :
    (charge machine).captured = machine.captured := by
  unfold charge
  dsimp only
  split
  · rfl
  · split <;> rfl

private theorem charge_effects (machine : Machine Payload) :
    (charge machine).effects = machine.effects := by
  unfold charge
  dsimp only
  split
  · rfl
  · split <;> rfl

theorem work_captured (policy : CapturePolicy) (machine : Machine Payload) :
    (work policy machine).captured = machine.captured := by
  unfold work consumeResult refreshRequest completeRequest perform
  (repeat' split) <;> simp only [charge_captured]

theorem resume_captured (allowance : Nat) (machine : Machine Payload) :
    (resume allowance machine).captured = machine.captured := by
  unfold resume
  split <;> rfl

theorem autoStep_captured (policy : CapturePolicy) (machine : Machine Payload) :
    (autoStep policy machine).captured = machine.captured := by
  rw [autoStep, work_captured]
  unfold activate resume
  (repeat' split) <;> rfl

theorem drive_captured (policy : CapturePolicy) (fuel : Nat) (machine : Machine Payload) :
    (drive policy fuel machine).captured = machine.captured := by
  induction fuel generalizing machine with
  | zero => rfl
  | succ fuel ih =>
      rw [drive, ih, autoStep_captured]

/-- Committed receipts can only be retained or extended by one new occurrence;
no transition removes or reorders them. -/
theorem work_effect_prefix (policy : CapturePolicy) (machine : Machine Payload) :
    machine.effects <+: (work policy machine).effects := by
  unfold work consumeResult refreshRequest completeRequest perform
  (repeat' split) <;> simp [charge_effects]

/-! ## Independent finite programs -/

inductive Body (Payload : Type u) where
  | append (fresh : Occurrence Payload)
  | remove
  | writeRead (fresh : Occurrence Payload) (pattern : Payload → Bool)

/-- Compile each captured occurrence independently.  In particular, equal
payloads produce separate visit and effect occurrences. -/
def Body.program (body : Body Payload) (source : Occurrence Payload) :
    List (Instruction Payload) :=
  match body with
  | .append fresh => [.effect (.append fresh), .answer (.atom source.payload)]
  | .remove => [.effect (.remove source.id), .answer (.atom source.payload)]
  | .writeRead fresh pattern => [.effect (.append fresh), .read source pattern]

def compile (bodies : Occurrence Payload → Body Payload) :
    List (Occurrence Payload) → List (Instruction Payload)
  | [] => []
  | source :: rest => (bodies source).program source ++ compile bodies rest

/-! ## Concrete captured-query controls -/

namespace Controls

inductive Fact where | A | B | New deriving DecidableEq

abbrev O := Occurrence Fact
abbrev I := Instruction Fact
abbrev M := Machine Fact

def a0 : O := ⟨0, .A⟩
def a1 : O := ⟨1, .A⟩
def b2 : O := ⟨2, .B⟩
def capturedThree : List O := [a0, a1, b2]
def new3 : O := ⟨3, .New⟩
def new4 : O := ⟨4, .New⟩
def new5 : O := ⟨5, .New⟩

def appendBody (source : O) : Body Fact :=
  match source.id with
  | 0 => .append new3
  | 1 => .append new4
  | _ => .append new5

def appendProgram : List I := compile appendBody capturedThree
def appendMachine : M := initial capturedThree appendProgram ⟨.trackedFresh, true, true⟩

/-- New rows do not extend the capture.  Duplicate A payloads remain distinct
answers and cause exactly three distinct appends. -/
theorem append_capture_and_occurrences_stable :
    (drive .repaired 12 appendMachine).captured = capturedThree ∧
      (drive .repaired 12 appendMachine).answers = [.atom .A, .atom .A, .atom .B] ∧
      (drive .repaired 12 appendMachine).effects =
        [.append new3, .append new4, .append new5] ∧
      (drive .repaired 12 appendMachine).world.rows =
        capturedThree ++ [new3, new4, new5] ∧
      (drive .repaired 12 appendMachine).status = .finished := by
  decide

def removeProgram : List I := compile (fun _ => .remove) capturedThree
def removeMachine : M := initial capturedThree removeProgram ⟨.trackedFresh, true, true⟩

/-- Removing each captured identity once does not collapse equal payloads. -/
theorem remove_capture_and_occurrences_stable :
    (drive .repaired 12 removeMachine).captured = capturedThree ∧
      (drive .repaired 12 removeMachine).answers = [.atom .A, .atom .A, .atom .B] ∧
      (drive .repaired 12 removeMachine).effects =
        [.remove a0.id, .remove a1.id, .remove b2.id] ∧
      (drive .repaired 12 removeMachine).world.rows = [] ∧
      (drive .repaired 12 removeMachine).status = .finished := by
  decide

def b6 : O := ⟨6, .B⟩
def freshProgram : List I := compile (fun _ => .writeRead b6 (fun _ => true)) [a0]
def freshMachine : M := initial [a0] freshProgram ⟨.trackedFresh, true, true⟩

/-- The fresh read sees the reached [A,B] world, and B has one receipt. -/
theorem new_read_observes_reached_world :
    (drive .repaired 8 freshMachine).answers = [.pair .A .A, .pair .A .B] ∧
      (drive .repaired 8 freshMachine).effects = [.append b6] ∧
      (drive .repaired 8 freshMachine).world.rows = [a0, b6] ∧
      (drive .repaired 8 freshMachine).captured = [a0] ∧
      (drive .repaired 8 freshMachine).status = .finished := by
  decide

/-- The same finite programs are exactly their host-free reference executions. -/
theorem append_composes_with_reference :
    semantic (drive .repaired 12 appendMachine) =
      execute appendProgram (Reference.initial ⟨capturedThree, 0⟩) := by
  decide

theorem remove_composes_with_reference :
    semantic (drive .repaired 12 removeMachine) =
      execute removeProgram (Reference.initial ⟨capturedThree, 0⟩) := by
  decide

theorem fresh_composes_with_reference :
    semantic (drive .repaired 8 freshMachine) =
      execute freshProgram (Reference.initial ⟨[a0], 0⟩) := by
  decide

/-- The exact abstract PeTTa failure state: B is committed and the fresh read is
outstanding.  Its numeric work start agrees with the pinned observation. -/
def stalledFresh : M :=
  { world := ⟨[a0, b6], 1⟩
    captured := [a0]
    remaining := []
    outstanding := some ⟨a0, fun _ => true, 1⟩
    completed := none
    effects := [.append b6]
    answers := []
    resource := ⟨.trackedFresh, true, true⟩
    resultHeld := false
    work := 17
    budget := 0
    status := .suspended }

def resumeWork (policy : CapturePolicy) (machine : M) : M :=
  work policy (resume 1 machine)

def oldLoop : Nat → M → M
  | 0, machine => machine
  | count + 1, machine => oldLoop count (resumeWork .old machine)

set_option maxRecDepth 10000 in
/-- One hundred thirty resumed old transitions charge work but retain exactly
the same request, committed effect, world, capture, and empty answer prefix. -/
theorem old_metering_is_not_semantic_progress :
    (oldLoop 130 stalledFresh).work = 147 ∧
      (oldLoop 130 stalledFresh).status = .suspended ∧
      (oldLoop 130 stalledFresh).outstanding.map ReadRequest.revision = some 1 ∧
      (oldLoop 130 stalledFresh).completed = none ∧
      (oldLoop 130 stalledFresh).effects = [.append b6] ∧
      (oldLoop 130 stalledFresh).world.rows = [a0, b6] ∧
      (oldLoop 130 stalledFresh).answers = [] ∧
      (oldLoop 130 stalledFresh).captured = [a0] := by
  decide

/-- The repaired transition uses the identical stalled state, performs no second
B append, and publishes the two reached-world answers before finishing. -/
theorem repaired_resume_preserves_committed_effect :
    semantic (drive .repaired 2 stalledFresh) =
      ⟨stalledFresh.world, [.append b6], [.pair .A .A, .pair .A .B]⟩ ∧
      (drive .repaired 2 stalledFresh).work = 19 ∧
      (drive .repaired 2 stalledFresh).status = .finished := by
  decide

/-- A nonempty miss is a successful empty read, not capture failure. -/
def missMachine : M :=
  initial [a0] [.read a0 (fun payload => payload == .New)] ⟨.trackedFresh, true, true⟩

theorem nonempty_lookup_miss :
    (drive .repaired 3 missMachine).answers = [] ∧
      (drive .repaired 3 missMachine).status = .finished := by
  decide

/-- Empty input is legal and needs no work. -/
theorem empty_input :
    (drive .repaired 0 (initial ([] : List O) ([] : List I) ⟨.trackedFresh, true, true⟩)).status = .running ∧
      (drive .repaired 1 (initial ([] : List O) ([] : List I) ⟨.trackedFresh, true, true⟩)).status = .finished := by
  decide

/-- Zero budget suspends without changing semantic state or charging work;
resuming with exactly the remaining work finishes at the boundary. -/
theorem budget_boundary :
    let paused := work .repaired freshMachine
    paused.work = 0 ∧ semantic paused = semantic freshMachine ∧
      paused.status = .suspended ∧
      (drive .repaired 4 paused).status = .finished := by
  decide

/-- A genuinely unshareable resource is an explicit terminal refusal, not an
old-style forever-resumable observation. -/
theorem unavailable_resource_is_not_false_progress :
    let machine : M := { stalledFresh with resource := ⟨.trackedFresh, true, false⟩ }
    (autoStep .repaired machine).status = .captureRefused ∧
      (autoStep .repaired machine).work = 18 ∧
      semantic (autoStep .repaired machine) = semantic machine := by
  decide

/-- An external append changes the dependency token.  The host first refreshes
that token, then reads the newly reached world; it does not repeat the own B
receipt. -/
def externallyChanged : M :=
  { stalledFresh with
    world := ⟨[a0, b6, ⟨7, .A⟩], 2⟩
    status := .running
    budget := 3 }

theorem external_change_requires_revalidation :
    (drive .repaired 3 externallyChanged).answers =
      [.pair .A .A, .pair .A .B, .pair .A .A] ∧
      (drive .repaired 3 externallyChanged).effects = [.append b6] ∧
      (drive .repaired 3 externallyChanged).status = .finished := by
  decide

end Controls

/-! ## Resource-correspondence bridge -/

/-- A successful arena capture really retains every required resource in its
receiver.  This is the lifetime fact that the repaired host policy must realize;
`admits` alone is deliberately not treated as a C ownership proof. -/
theorem captured_resources_are_held {ArenaId R : Type} [DecidableEq ArenaId]
    [DecidableEq R]
    (state : ArenaHeldResources.State ArenaId R) (sources : Finset ArenaId)
    (receiver : ArenaId) (shareable : R → Bool) (nodes : ArenaHeldResources.Log R)
    (admitted : (ArenaHeldResources.Capture.capture state sources receiver shareable nodes).1 = true)
    {resource : R} (required : resource ∈ nodes.flatten) :
    ArenaHeldResources.Held
      (ArenaHeldResources.Capture.capture state sources receiver shareable nodes).2 resource := by
  obtain ⟨node, inNodes, refers⟩ := List.mem_flatten.mp required
  apply ArenaHeldResources.held_of_mem (a := receiver) (e := node) (r := resource) ?_ refers
  rw [ArenaHeldResources.Capture.admitted_log state sources receiver shareable nodes admitted]
  exact List.mem_append.mpr (Or.inr inNodes)

/-- The capture-backed host keeps the actual arena state and capture inputs
next to the semantic machine. -/
structure CaptureBackedMachine (Payload ArenaId R : Type) [DecidableEq ArenaId]
    [DecidableEq R] where
  machine : Machine Payload
  arenaState : ArenaHeldResources.State ArenaId R
  sources : Finset ArenaId
  receiver : ArenaId
  shareable : R → Bool
  nodes : ArenaHeldResources.Log R

/-- Capture-backed counterpart of the abstract completion transition.  Abstract
support is checked first; then the real capture receipt determines whether the
completed result is retained or the host explicitly refuses. -/
noncomputable def captureComplete {Payload ArenaId R : Type} [DecidableEq ArenaId]
    [DecidableEq R] (hosted : CaptureBackedMachine Payload ArenaId R)
    (request : ReadRequest Payload) : CaptureBackedMachine Payload ArenaId R :=
  if admits .repaired hosted.machine.resource then
    let receipt := ArenaHeldResources.Capture.capture hosted.arenaState hosted.sources
      hosted.receiver hosted.shareable hosted.nodes
    if receipt.1 then
      { hosted with
        arenaState := receipt.2
        machine := charge { hosted.machine with
          completed := some ⟨hosted.machine.world.revision,
            readAnswers request hosted.machine.world⟩
          resultHeld := true } }
    else
      { hosted with
        arenaState := receipt.2
        machine := { (charge hosted.machine) with status := .captureRefused } }
  else
    { hosted with machine := { (charge hosted.machine) with status := .captureRefused } }

/-- On a successful receipt, the machine performs exactly the original semantic
completion transition, while the returned arena state really holds every
resource in the captured nodes.  Thus `resultHeld` is not being used as a
stand-in for the separate lifetime guarantee. -/
theorem captureComplete_composes {Payload ArenaId R : Type} [DecidableEq ArenaId]
    [DecidableEq R] (hosted : CaptureBackedMachine Payload ArenaId R)
    (request : ReadRequest Payload)
    (supported : admits .repaired hosted.machine.resource = true)
    (receipt : (ArenaHeldResources.Capture.capture hosted.arenaState hosted.sources
      hosted.receiver hosted.shareable hosted.nodes).1 = true) :
    let final := captureComplete hosted request
    final.machine = completeRequest .repaired hosted.machine request ∧
      ∀ {resource : R}, resource ∈ hosted.nodes.flatten →
        ArenaHeldResources.Held final.arenaState resource := by
  simp only [captureComplete, completeRequest, supported, receipt, ↓reduceIte]
  exact ⟨trivial, fun required =>
    captured_resources_are_held hosted.arenaState hosted.sources hosted.receiver
      hosted.shareable hosted.nodes receipt required⟩

#print axioms initial_prefix
#print axioms work_prefix
#print axioms autoStep_prefix
#print axioms drive_prefix
#print axioms work_remainingWork_lt
#print axioms autoStep_remainingWork_lt
#print axioms drive_composes
#print axioms initial_drive_composes
#print axioms drive_captured
#print axioms Controls.append_capture_and_occurrences_stable
#print axioms Controls.remove_capture_and_occurrences_stable
#print axioms Controls.new_read_observes_reached_world
#print axioms Controls.old_metering_is_not_semantic_progress
#print axioms Controls.repaired_resume_preserves_committed_effect
#print axioms captured_resources_are_held
#print axioms captureComplete_composes

end Mettapedia.Machines.CapturedQueryProgress
