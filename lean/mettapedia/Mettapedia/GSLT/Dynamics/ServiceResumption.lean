import Mettapedia.TypeTheory.ContextualDependentSequencing

/-!
# Request-indexed resumptions of contextual effect programs

The existing well-founded effect syntax is extended by dependent service
requests. A continuation receives a value in the reply fibre of its actual
request, and may issue further requests. An independently supplied total
invocation callback resolves those requests. This is not an authored-backend
adequacy theorem or a claim that arbitrary external invocations terminate.

Resolution lowers to the existing contextual Program, with chronological
request/reply history in its answer. The existing isolated-world evaluator
therefore determines choice order, branch identity, private state, and deferred
intents. No second state/choice evaluator is introduced. Declines may be
represented by consumer-chosen reply or answer sums; they are not silently
converted to empty result lists.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ServiceResumption

open ContextualEffectHandlers

universe uRequest uReply uState uAnswer uOther uThird uIntent

/-- An inductive resumption permits arbitrary well-founded nesting of
requests, with a request-indexed continuation rather than an erased reply. -/
inductive Resumption (Request : Type uRequest) (Reply : Request → Type uReply)
    (State : Type uState) (Answer : Type uAnswer) (Intent : Type uIntent) where
  | pure (answer : Answer)
  | choose (left right : Resumption Request Reply State Answer Intent)
  | read (next : State → Resumption Request Reply State Answer Intent)
  | write (state : State) (next : Resumption Request Reply State Answer Intent)
  | intent (value : Intent) (next : Resumption Request Reply State Answer Intent)
  | request (input : Request) (next : Reply input → Resumption Request Reply State Answer Intent)

section Generic

variable {Request : Type uRequest} {Reply : Request → Type uReply}
  {State : Type uState} {Answer : Type uAnswer} {Other : Type uOther}
  {Third : Type uThird} {Intent : Type uIntent}

namespace Resumption

def bind (computation : Resumption Request Reply State Answer Intent)
    (next : Answer → Resumption Request Reply State Other Intent) :
    Resumption Request Reply State Other Intent :=
  match computation with
  | .pure answer => next answer
  | .choose left right => .choose (bind left next) (bind right next)
  | .read continuation => .read fun state => bind (continuation state) next
  | .write state continuation => .write state (bind continuation next)
  | .intent value continuation => .intent value (bind continuation next)
  | .request input continuation => .request input fun reply => bind (continuation reply) next

def map (function : Answer → Other) (computation : Resumption Request Reply State Answer Intent) :
    Resumption Request Reply State Other Intent :=
  computation.bind (fun answer => .pure (function answer))

@[simp] theorem pure_bind (answer : Answer)
    (next : Answer → Resumption Request Reply State Other Intent) :
    bind (.pure answer) next = next answer := rfl

@[simp] theorem request_bind (input : Request)
    (continuation : Reply input → Resumption Request Reply State Answer Intent)
    (next : Answer → Resumption Request Reply State Other Intent) :
    bind (.request input continuation) next =
      .request input (fun reply => (continuation reply).bind next) := rfl

@[simp] theorem bind_pure (computation : Resumption Request Reply State Answer Intent) :
    computation.bind .pure = computation := by
  induction computation with
  | pure answer => rfl
  | choose left right leftIH rightIH => simp only [bind, leftIH, rightIH]
  | read next nextIH => exact congrArg Resumption.read (funext nextIH)
  | write state next nextIH => exact congrArg (Resumption.write state) nextIH
  | intent value next nextIH => exact congrArg (Resumption.intent value) nextIH
  | request input next nextIH => exact congrArg (Resumption.request input) (funext nextIH)

theorem bind_assoc (computation : Resumption Request Reply State Answer Intent)
    (next : Answer → Resumption Request Reply State Other Intent)
    (last : Other → Resumption Request Reply State Third Intent) :
    (computation.bind next).bind last = computation.bind (fun answer => (next answer).bind last) := by
  induction computation with
  | pure answer => rfl
  | choose left right leftIH rightIH => simp only [bind, leftIH, rightIH]
  | read continuation continuationIH => exact congrArg Resumption.read (funext continuationIH)
  | write state continuation continuationIH => exact congrArg (Resumption.write state) continuationIH
  | intent value continuation continuationIH => exact congrArg (Resumption.intent value) continuationIH
  | request input continuation continuationIH =>
      exact congrArg (Resumption.request input) (funext continuationIH)

@[simp] theorem map_id (computation : Resumption Request Reply State Answer Intent) :
    map id computation = computation := bind_pure computation

theorem map_comp (first : Answer → Other) (second : Other → Third)
    (computation : Resumption Request Reply State Answer Intent) :
    map second (map first computation) = map (second ∘ first) computation := by
  simp only [map, bind_assoc, pure_bind, Function.comp_def]

theorem map_bind (function : Other → Third)
    (computation : Resumption Request Reply State Answer Intent)
    (next : Answer → Resumption Request Reply State Other Intent) :
    map function (computation.bind next) = computation.bind (fun answer => map function (next answer)) :=
  bind_assoc computation next _

theorem bind_map (function : Answer → Other)
    (computation : Resumption Request Reply State Answer Intent)
    (next : Other → Resumption Request Reply State Third Intent) :
    (map function computation).bind next = computation.bind (next ∘ function) := by
  simp only [map, bind_assoc, pure_bind, Function.comp_def]

end Resumption

/-- Embed the existing effect syntax, without inserting any request. -/
def embed : Program State Answer Intent → Resumption Request Reply State Answer Intent
  | .pure answer => .pure answer
  | .choose left right => .choose (embed left) (embed right)
  | .read next => .read fun state => embed (next state)
  | .write state next => .write state (embed next)
  | .intent value next => .intent value (embed next)

theorem embed_bind (program : Program State Answer Intent)
    (next : Answer → Program State Other Intent) :
    embed (Request := Request) (Reply := Reply) (program.bind next) =
      (embed program).bind (fun answer => embed (next answer)) := by
  induction program with
  | pure answer => rfl
  | choose left right leftIH rightIH => simp only [Program.bind, embed, Resumption.bind, leftIH, rightIH]
  | read continuation continuationIH => exact congrArg Resumption.read (funext continuationIH)
  | write state continuation continuationIH => exact congrArg (Resumption.write state) continuationIH
  | intent value continuation continuationIH => exact congrArg (Resumption.intent value) continuationIH

theorem embed_map (function : Answer → Other) (program : Program State Answer Intent) :
    embed (Request := Request) (Reply := Reply) (Program.map function program) =
      Resumption.map function (embed program) := embed_bind program _

/-- Resolve only the request constructor, retaining the actual input and
dependent reply in the result. All effects still use the existing Program. -/
def lower (invoke : (input : Request) → Reply input) :
    Resumption Request Reply State Answer Intent →
      Program State (Answer × List (Sigma Reply)) Intent
  | .pure answer => .pure (answer, [])
  | .choose left right => .choose (lower invoke left) (lower invoke right)
  | .read next => .read fun state => lower invoke (next state)
  | .write state next => .write state (lower invoke next)
  | .intent value next => .intent value (lower invoke next)
  | .request input next =>
      Program.map (fun result => (result.1, ⟨input, invoke input⟩ :: result.2))
        (lower invoke (next (invoke input)))

theorem lower_embed (invoke : (input : Request) → Reply input) (program : Program State Answer Intent) :
    lower invoke (embed program) = Program.map (fun answer => (answer, [])) program := by
  induction program with
  | pure answer => rfl
  | choose left right leftIH rightIH => simp only [embed, lower, Program.map, Program.bind] at *; rw [leftIH, rightIH]
  | read next nextIH => exact congrArg Program.read (funext nextIH)
  | write state next nextIH => exact congrArg (Program.write state) nextIH
  | intent value next nextIH => exact congrArg (Program.intent value) nextIH

/-- Every result retains the existing full world and its chronological
request/reply history. Branch history keeps the existing newest-first order. -/
structure Result (Request : Type uRequest) (Reply : Request → Type uReply)
    (State : Type uState) (Answer : Type uAnswer) (Intent : Type uIntent) where
  world : WorldResult State Answer Intent
  replies : List (Sigma Reply)

namespace Result

def ofWorld (world : WorldResult State (Answer × List (Sigma Reply)) Intent) :
    Result Request Reply State Answer Intent where
  world := { branch := world.branch, answer := world.answer.1, state := world.state, intents := world.intents }
  replies := world.answer.2

/-- Earlier intents and responses precede the continuation's history. The
continuation already ran in the selected world's state and branch context. -/
def prepend (intents : List Intent) (replies : List (Sigma Reply))
    (result : Result Request Reply State Answer Intent) : Result Request Reply State Answer Intent :=
  { world := { result.world with intents := intents ++ result.world.intents }
    replies := replies ++ result.replies }

def mapAnswer (function : Answer → Other) (result : Result Request Reply State Answer Intent) :
    Result Request Reply State Other Intent :=
  { world := Mettapedia.TypeTheory.ContextualDependentSequencing.WorldResult.mapAnswer function result.world
    replies := result.replies }

@[simp] theorem prepend_nil (result : Result Request Reply State Answer Intent) :
    prepend [] [] result = result := rfl

theorem prepend_comp (firstIntents secondIntents : List Intent)
    (firstReplies secondReplies : List (Sigma Reply)) (result : Result Request Reply State Answer Intent) :
    prepend firstIntents firstReplies (prepend secondIntents secondReplies result) =
      prepend (firstIntents ++ secondIntents) (firstReplies ++ secondReplies) result := by
  simp only [prepend, List.append_assoc]

end Result

/-- The existing isolated-world evaluator, after request resolution. -/
def runWorldsAt (invoke : (input : Request) → Reply input)
    (computation : Resumption Request Reply State Answer Intent) (state : State) (branch : BranchTrace) :
    List (Result Request Reply State Answer Intent) :=
  (ContextualEffectHandlers.runWorldsAt (lower invoke computation) state branch).map Result.ofWorld

def runWorlds (invoke : (input : Request) → Reply input)
    (computation : Resumption Request Reply State Answer Intent) (state : State) :
    List (Result Request Reply State Answer Intent) := runWorldsAt invoke computation state []

@[simp] theorem runWorldsAt_pure (invoke : (input : Request) → Reply input)
    (answer : Answer) (state : State) (branch : BranchTrace) :
    runWorldsAt (Intent := Intent) invoke (.pure answer) state branch =
      [{ world := { branch := branch, answer := answer, state := state, intents := [] }, replies := [] }] := rfl

@[simp] theorem runWorldsAt_choose (invoke : (input : Request) → Reply input)
    (left right : Resumption Request Reply State Answer Intent) (state : State) (branch : BranchTrace) :
    runWorldsAt invoke (.choose left right) state branch =
      runWorldsAt invoke left state (false :: branch) ++ runWorldsAt invoke right state (true :: branch) := by
  simp only [runWorldsAt, lower, ContextualEffectHandlers.runWorldsAt, List.map_append]

@[simp] theorem runWorldsAt_read (invoke : (input : Request) → Reply input)
    (next : State → Resumption Request Reply State Answer Intent) (state : State) (branch : BranchTrace) :
    runWorldsAt invoke (.read next) state branch = runWorldsAt invoke (next state) state branch := rfl

@[simp] theorem runWorldsAt_write (invoke : (input : Request) → Reply input)
    (newState : State) (next : Resumption Request Reply State Answer Intent) (state : State) (branch : BranchTrace) :
    runWorldsAt invoke (.write newState next) state branch = runWorldsAt invoke next newState branch := rfl

@[simp] theorem runWorldsAt_intent (invoke : (input : Request) → Reply input)
    (value : Intent) (next : Resumption Request Reply State Answer Intent) (state : State) (branch : BranchTrace) :
    runWorldsAt invoke (.intent value next) state branch =
      (runWorldsAt invoke next state branch).map (Result.prepend [value] []) := by
  simp only [runWorldsAt, lower, ContextualEffectHandlers.runWorldsAt, List.map_map,
    Function.comp_def, Result.ofWorld, Result.prepend, List.cons_append, List.nil_append]

@[simp] theorem runWorldsAt_request (invoke : (input : Request) → Reply input)
    (input : Request) (next : Reply input → Resumption Request Reply State Answer Intent)
    (state : State) (branch : BranchTrace) :
    runWorldsAt invoke (.request input next) state branch =
      (runWorldsAt invoke (next (invoke input)) state branch).map
        (Result.prepend [] [⟨input, invoke input⟩]) := by
  simp only [runWorldsAt, lower, Mettapedia.TypeTheory.ContextualDependentSequencing.runWorldsAt_map,
    List.map_map, Function.comp_def, Result.ofWorld, Result.prepend,
    Mettapedia.TypeTheory.ContextualDependentSequencing.WorldResult.mapAnswer,
    List.cons_append, List.nil_append]

/-- Exact ordered sequencing, including both chronological traces. Each
continuation starts at its own prefix's private state and branch history. -/
theorem runWorldsAt_bind (invoke : (input : Request) → Reply input)
    (computation : Resumption Request Reply State Answer Intent)
    (next : Answer → Resumption Request Reply State Other Intent) (state : State) (branch : BranchTrace) :
    runWorldsAt invoke (computation.bind next) state branch =
      (runWorldsAt invoke computation state branch).flatMap fun prior =>
        (runWorldsAt invoke (next prior.world.answer) prior.world.state prior.world.branch).map
          (Result.prepend prior.world.intents prior.replies) := by
  induction computation generalizing state branch with
  | pure answer =>
      simp only [Resumption.bind, runWorldsAt_pure, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      exact (List.map_id _).symm
  | choose left right leftIH rightIH =>
      simp only [Resumption.bind, runWorldsAt_choose, leftIH, rightIH, List.flatMap_append]
  | read continuation continuationIH => exact continuationIH state state branch
  | write newState continuation continuationIH => exact continuationIH newState branch
  | intent value continuation continuationIH =>
      simp only [Resumption.bind, runWorldsAt_intent, continuationIH, List.map_flatMap,
        List.flatMap_map, List.map_map, Function.comp_def, Result.prepend,
        List.cons_append, List.nil_append]
      rfl
  | request input continuation continuationIH =>
      simp only [Resumption.bind, runWorldsAt_request, continuationIH, List.map_flatMap,
        List.flatMap_map, List.map_map, Function.comp_def, Result.prepend,
        List.cons_append, List.nil_append]
      rfl

theorem runWorlds_bind (invoke : (input : Request) → Reply input)
    (computation : Resumption Request Reply State Answer Intent)
    (next : Answer → Resumption Request Reply State Other Intent) (state : State) :
    runWorlds invoke (computation.bind next) state =
      (runWorlds invoke computation state).flatMap fun prior =>
        (runWorldsAt invoke (next prior.world.answer) prior.world.state prior.world.branch).map
          (Result.prepend prior.world.intents prior.replies) :=
  runWorldsAt_bind invoke computation next state []

/-- Backward membership recovers the actual selected prefix and suffix,
rather than only an answer that happens to be equal. -/
theorem mem_runWorldsAt_bind_iff (invoke : (input : Request) → Reply input)
    (computation : Resumption Request Reply State Answer Intent)
    (next : Answer → Resumption Request Reply State Other Intent) (state : State) (branch : BranchTrace)
    (result : Result Request Reply State Other Intent) :
    result ∈ runWorldsAt invoke (computation.bind next) state branch ↔
      ∃ prior ∈ runWorldsAt invoke computation state branch,
        ∃ later ∈ runWorldsAt invoke (next prior.world.answer) prior.world.state prior.world.branch,
          Result.prepend prior.world.intents prior.replies later = result := by
  rw [runWorldsAt_bind]
  simp only [List.mem_flatMap, List.mem_map]

theorem runWorldsAt_map (invoke : (input : Request) → Reply input) (function : Answer → Other)
    (computation : Resumption Request Reply State Answer Intent) (state : State) (branch : BranchTrace) :
    runWorldsAt invoke (Resumption.map function computation) state branch =
      (runWorldsAt invoke computation state branch).map (Result.mapAnswer function) := by
  rw [Resumption.map, runWorldsAt_bind]
  simp only [runWorldsAt_pure, List.map_cons, List.map_nil, Result.prepend, List.append_nil]
  exact List.map_eq_flatMap.symm

/-- An old effect program keeps every original world, in order, and adds no
request occurrences. This is equality at the existing evaluator. -/
theorem runWorldsAt_embed (invoke : (input : Request) → Reply input)
    (program : Program State Answer Intent) (state : State) (branch : BranchTrace) :
    runWorldsAt invoke (embed program) state branch =
      (ContextualEffectHandlers.runWorldsAt program state branch).map
        (fun world => { world := world, replies := [] }) := by
  simp only [runWorldsAt, lower_embed,
    Mettapedia.TypeTheory.ContextualDependentSequencing.runWorldsAt_map,
    List.map_map, Function.comp_def, Result.ofWorld,
    Mettapedia.TypeTheory.ContextualDependentSequencing.WorldResult.mapAnswer]

theorem runWorldsAt_embed_worlds (invoke : (input : Request) → Reply input)
    (program : Program State Answer Intent) (state : State) (branch : BranchTrace) :
    (runWorldsAt invoke (embed program) state branch).map Result.world =
      ContextualEffectHandlers.runWorldsAt program state branch := by
  rw [runWorldsAt_embed, List.map_map]
  exact List.map_id _

theorem embed_replies_empty (invoke : (input : Request) → Reply input)
    (program : Program State Answer Intent) (state : State) (branch : BranchTrace)
    {result : Result Request Reply State Answer Intent}
    (member : result ∈ runWorldsAt invoke (embed program) state branch) : result.replies = [] := by
  rw [runWorldsAt_embed] at member
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
  rfl

/-- Total invocation and well-founded syntax produce a nonempty result list.
A declined reply or stopped answer is still data, not implicit branch loss. -/
theorem runWorldsAt_ne_nil (invoke : (input : Request) → Reply input)
    (computation : Resumption Request Reply State Answer Intent) (state : State) (branch : BranchTrace) :
    runWorldsAt invoke computation state branch ≠ [] := by
  induction computation generalizing state branch with
  | pure answer => exact List.cons_ne_nil _ _
  | choose left right leftIH _ =>
      intro empty
      rw [runWorldsAt_choose] at empty
      exact leftIH state (false :: branch) (List.append_eq_nil_iff.mp empty).1
  | read continuation continuationIH => exact continuationIH state state branch
  | write newState continuation continuationIH => exact continuationIH newState branch
  | intent value continuation continuationIH =>
      intro empty
      rw [runWorldsAt_intent] at empty
      exact continuationIH state branch (List.map_eq_nil_iff.mp empty)
  | request input continuation continuationIH =>
      intro empty
      rw [runWorldsAt_request] at empty
      exact continuationIH (invoke input) state branch (List.map_eq_nil_iff.mp empty)

end Generic

/-! ## Dependent nested-call and history controls -/

namespace Examples

/-- The second request has a reply fibre determined by its numeric bound. -/
inductive Request where
  | width
  | bounded (limit : Nat)
  deriving DecidableEq

def Reply : Request → Type
  | .width => Nat
  | .bounded limit => Fin (limit + 1)

/-- A separately authored total callback; the resumption does not define it. -/
def invoke : (input : Request) → Reply input
  | .width => (2 : Nat)
  | .bounded limit => ⟨limit, Nat.lt_succ_self limit⟩

/-- The first reply sets private state. Each branch then issues a different
dependent request using that state's actual value, retaining deferred intents. -/
def nested : Resumption Request Reply Nat Nat Nat :=
  .request .width fun width =>
    .choose
      (.write width (.intent 10 (.read fun seen =>
        .request (.bounded seen) fun reply => .intent reply.val (.pure reply.val))))
      (.write (Nat.succ width) (.read fun seen =>
        .request (.bounded seen) fun reply => .intent 20 (.pure reply.val)))

theorem nested_exact :
    runWorlds invoke nested 0 =
      [{ world := { branch := [false], answer := 2, state := 2, intents := [10, 2] }
         replies := [⟨.width, (2 : Nat)⟩, ⟨.bounded 2, ⟨2, by decide⟩⟩] },
       { world := { branch := [true], answer := 3, state := 3, intents := [20] }
         replies := [⟨.width, (2 : Nat)⟩, ⟨.bounded 3, ⟨3, by decide⟩⟩] }] := rfl

/-- The old effect program has the same final worlds, but has made no calls. -/
def withoutRequests : Program Nat Nat Nat :=
  .choose (.write 2 (.intent 10 (.intent 2 (.pure 2))))
    (.write 3 (.intent 20 (.pure 3)))

theorem same_existing_worlds :
    (runWorlds invoke nested 0).map Result.world =
      (runWorlds invoke (embed withoutRequests) 0).map Result.world := rfl

theorem same_answers :
    (runWorlds invoke nested 0).map (fun result => result.world.answer) =
      (runWorlds invoke (embed withoutRequests) 0).map (fun result => result.world.answer) := rfl

/-- Even retaining the complete old world cannot recover erased call history. -/
theorem different_request_histories :
    runWorlds invoke nested 0 ≠ runWorlds invoke (embed withoutRequests) 0 := by
  intro equal
  have lengths := congrArg (fun results => results.map (fun result => result.replies.length)) equal
  change [2, 2] = [0, 0] at lengths
  cases lengths

theorem no_trace_recovery_from_worlds :
    ¬ ∃ recover : List (WorldResult Nat Nat Nat) → List (Result Request Reply Nat Nat Nat),
      recover ((runWorlds invoke nested 0).map Result.world) = runWorlds invoke nested 0 ∧
      recover ((runWorlds invoke (embed withoutRequests) 0).map Result.world) =
        runWorlds invoke (embed withoutRequests) 0 := by
  rintro ⟨recover, called, uncalled⟩
  exact different_request_histories
    (called.symm.trans ((congrArg recover same_existing_worlds).trans uncalled))

theorem no_trace_recovery_from_answers :
    ¬ ∃ recover : List Nat → List (Result Request Reply Nat Nat Nat),
      recover ((runWorlds invoke nested 0).map (fun result => result.world.answer)) =
        runWorlds invoke nested 0 ∧
      recover ((runWorlds invoke (embed withoutRequests) 0).map (fun result => result.world.answer)) =
        runWorlds invoke (embed withoutRequests) 0 := by
  rintro ⟨recover, called, uncalled⟩
  exact different_request_histories (called.symm.trans ((congrArg recover same_answers).trans uncalled))

/-- A consumer may stop with an answer sum. Its earlier reply stays present,
and the stopped outcome remains one world rather than disappearing. -/
def stopped : Resumption Request Reply Nat (Sum String Nat) Nat :=
  .request .width fun _ => .pure (.inl "declined")

theorem stopped_reply_retained :
    runWorlds invoke stopped 0 =
      [{ world := { branch := [], answer := .inl "declined", state := 0, intents := [] }
         replies := [⟨.width, (2 : Nat)⟩] }] := rfl

end Examples

#print axioms Resumption.bind_assoc
#print axioms Resumption.map_comp
#print axioms embed_bind
#print axioms lower_embed
#print axioms runWorldsAt_request
#print axioms runWorldsAt_bind
#print axioms mem_runWorldsAt_bind_iff
#print axioms runWorldsAt_map
#print axioms runWorldsAt_embed
#print axioms embed_replies_empty
#print axioms runWorldsAt_ne_nil
#print axioms Examples.nested_exact
#print axioms Examples.no_trace_recovery_from_worlds
#print axioms Examples.no_trace_recovery_from_answers
#print axioms Examples.stopped_reply_retained

end Mettapedia.GSLT.Dynamics.ServiceResumption
