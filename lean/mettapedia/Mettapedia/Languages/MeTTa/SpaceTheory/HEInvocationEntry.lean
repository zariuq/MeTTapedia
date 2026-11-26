import Mettapedia.Languages.MeTTa.SpaceTheory.HEFocused

/-!
# HE invocation and retained equation work

The live complete-frontier query and the use of a retained frontier
are different judgments. The first asks the current context. The
second asks only the captured work and its activation. Grounded calls
have a separate host authority and can change the world.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HEInvocationEntry

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationFrontierRel EquationWork)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed
  (Frame Policy Result WorldEnvironment NativeOutcomeRel NativeReplyPlan)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Task Continuation)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (WorldLocalStepWith)
open HEFocused (Focus Leaf Parent)

structure Input where
  live : List Atom
  scope : List String
  value : Entry.Value
  frame : Frame

inductive Mode where
  | typed (expected : Atom)
  | raw (caller : Option Atom)

def Mode.expected : Mode → Option Atom
  | .typed expected => some expected
  | .raw _ => none

def Mode.caller : Mode → Option Atom
  | .typed _ => none
  | .raw caller => caller

def Mode.protect (mode : Mode) (live : List Atom) : List Atom :=
  mode.expected.toList ++ live

def Mode.mayInvoke (mode : Mode) (input : Input) : Prop :=
  ∀ expected, mode.expected = some expected → ¬ IsErrorRel input.value.erase

inductive Request where
  | invoke (input : Input) (mode : Mode)
  | retained (input : Input) (expected : Option Atom) (work : List EquationWork)

def Request.task : Request → Task
  | .invoke q (.typed expected) => .call q.live q.scope q.value expected q.frame
  | .invoke q (.raw caller) => .invocation q.live q.scope caller q.value q.frame
  | .retained q (some expected) work => .equations q.live q.scope q.value expected q.frame work
  | .retained q none work => .invocationEquations q.live q.scope q.value q.frame work

def Request.recognize : Task → Option Request
  | .call live scope value expected frame => some (.invoke ⟨live, scope, value, frame⟩ (.typed expected))
  | .invocation live scope caller value frame => some (.invoke ⟨live, scope, value, frame⟩ (.raw caller))
  | .equations live scope value expected frame work => some (.retained ⟨live, scope, value, frame⟩ (some expected) work)
  | .invocationEquations live scope value frame work => some (.retained ⟨live, scope, value, frame⟩ none work)
  | _ => none

@[simp] theorem Request.recognize_task (r : Request) : recognize r.task = some r := by
  cases r with
  | invoke _ mode => cases mode <;> rfl
  | retained _ expected _ => cases expected <;> rfl

theorem Request.recognize_exact {task : Task} {r : Request} (found : recognize task = some r) : r.task = task := by
  cases task <;> cases found <;> rfl

theorem Request.task_injective : Function.Injective Request.task := by
  intro first second equal
  have recognized := congrArg recognize equal
  simpa only [recognize_task, Option.some.injEq] using recognized

inductive Reply where
  | error
  | embedded
  | query (work : List EquationWork)
  | native (operator : Atom) (arguments : List Atom) (plan : NativeReplyPlan)
  | exhausted
  | use (chosen : EquationWork) (pending : List EquationWork) (reached : Frame)

variable {Context World : Type}

def Licensed (env : WorldEnvironment Context World) (p : Policy) (w : World) (scope : Context)
    (r : Request) (reply : Reply) (next : World) : Prop :=
  match r with
  | .invoke q mode => match reply with
    | .error => match mode with
      | .typed _ => next = w ∧ IsErrorRel q.value.erase
      | .raw _ => False
    | .embedded =>
      next = w ∧ mode.mayInvoke q ∧ ¬ Minimal.HostCall env.dispatch q.value.erase ∧
        Minimal.embeddedInstruction q.value.erase = true
    | .query work =>
      next = w ∧ mode.mayInvoke q ∧ NonGroundedCallRel env.dispatch q.value.erase ∧
        EquationFrontierRel (env.view w scope) (mode.protect q.live) q.value.erase q.frame.bindings work
    | .native operator arguments plan =>
      mode.mayInvoke q ∧ q.value.erase = .expression (operator :: arguments) ∧ env.dispatch.executable operator ∧
        ∃ outcome, env.services.groundedAt scope w q.live q.scope q.frame q.value outcome next ∧
          NativeOutcomeRel p env.dispatch operator arguments q.value mode.expected q.frame outcome plan
    | _ => False
  | .retained q _ work => match reply with
    | .exhausted => next = w ∧ work = []
    | .use chosen pending reached =>
      next = w ∧ work = chosen :: pending ∧ reached.bindings = chosen.bindings ∧
        Entry.Value.UnifyRel p.rebuilding q.frame.environment q.value (Entry.Value.ofAtom chosen.pattern)
          reached.environment
    | _ => False

def continuation (p : Policy) (dispatch : GroundedDispatch) (r : Request) (reply : Reply) :
    Option (Leaf × List Continuation) :=
  match r, reply with
  | .invoke q (.typed _), .error => some (.returning [(q.value, q.frame)], [])
  | .invoke q (.typed expected), .embedded =>
    some (.work (.invocation (expected :: q.live) q.scope none q.value q.frame),
      [.boundaryBatch q.live q.scope none (.returned q.value expected)])
  | .invoke q (.raw caller), .embedded =>
    some (.work (.minimal q.live q.scope caller q.value q.frame), [])
  | .invoke q (.typed _), .query [] => some (.returning [(q.value, q.frame)], [])
  | .invoke q (.raw _), .query [] => some (.returning [(.symbol "NotReducible", q.frame)], [])
  | .invoke q mode, .query (head :: rest) =>
    some (.work (Request.task (.retained q mode.expected (head :: rest))), [])
  | .invoke _ _, .native _ _ (.done results) => some (.returning results, [])
  | .invoke q mode, .native operator arguments (.resume results) =>
    some (.work (.boundaryBatch q.live q.scope mode.caller
      (.native q.value mode.expected (dispatch.valueProvenance operator arguments)) results), [])
  | .retained _ _ _, .exhausted => some (.returning [], [])
  | .retained q (some expected) _, .use chosen pending reached =>
    some (.work (.boundary (expected :: q.live) q.scope (some q.value.erase) .producer
      (reached.read p (Entry.Value.ofAtom chosen.body)) reached),
      [.boundaryBatch q.live q.scope none (.returned q.value expected),
        .append (Request.task (.retained q (some expected) pending))])
  | .retained q none _, .use chosen pending reached =>
    some (.work (.boundary q.live q.scope (some q.value.erase) .producer
      (reached.read p (Entry.Value.ofAtom chosen.body)) reached),
      [.append (Request.task (.retained q none pending))])
  | _, _ => none

private theorem typed_guard {q : Input} {expected : Atom} (safe : Mode.mayInvoke (.typed expected) q) :
    ¬ IsErrorRel q.value.erase := safe _ rfl

private theorem raw_guard (caller : Option Atom) (q : Input) : Mode.mayInvoke (.raw caller) q := by
  intro _ absent
  cases absent

theorem frames_bounded (p : Policy) (dispatch : GroundedDispatch) (request : Request) (reply : Reply)
    (body : Leaf) (frames : List Continuation)
    (planned : continuation p dispatch request reply = some (body, frames)) : frames.length ≤ 2 := by
  cases request with
  | invoke q mode =>
    cases reply with
    | query work => cases mode <;> cases work <;> cases planned <;> simp
    | native operator arguments plan => cases mode <;> cases plan <;> cases planned <;> simp
    | _ => cases mode <;> cases planned <;> simp
  | retained q expected work =>
    cases expected <;> cases reply <;> cases planned <;> simp

theorem step_iff (env : WorldEnvironment Context World) (p : Policy) (request : Request)
    (world : World) (scope : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (published : List Result) (target : Focus Context World) :
    HEFocused.Move env.arguments env.view env.services env.dispatch env.lookup p
      ⟨world, scope, .work request.task, stack, parents, published⟩ target ↔
    ∃ reply next work frames, Licensed env p world scope request reply next ∧
      continuation p env.dispatch request reply = some (work, frames) ∧
      target = ⟨next, scope, work, frames ++ stack, parents, published⟩ := by
  constructor
  · intro move
    cases request with
    | invoke q mode =>
      rcases q with ⟨live, names, value, frame⟩
      cases mode with
      | typed expected =>
        cases move with
        | perform step =>
          change WorldLocalStepWith env.arguments env.view env.services env.dispatch env.lookup p world scope
            (.work (.call live names value expected frame), stack) _ _ at step
          cases step with
          | core incoming _ localStep outgoing =>
            cases incoming
            cases localStep with
            | callError error => cases outgoing; exact ⟨.error, world, _, _, ⟨rfl, error⟩, rfl, rfl⟩
            | callEmbedded safe ordinary embedded =>
              cases outgoing
              exact ⟨.embedded, world, _, _, ⟨rfl, fun _ _ => safe, ordinary, embedded⟩, rfl, rfl⟩
            | callAbsent safe nongrounded frontier =>
              cases outgoing
              exact ⟨.query [], world, _, _, ⟨rfl, fun _ _ => safe, nongrounded, frontier⟩, rfl, rfl⟩
            | callEquations safe nongrounded frontier nonempty =>
              cases outgoing
              rename_i work
              cases work with
              | nil => exact (nonempty rfl).elim
              | cons head rest =>
                exact ⟨.query (head :: rest), world, _, _, ⟨rfl, fun _ _ => safe, nongrounded, frontier⟩, rfl, rfl⟩
          | callGroundedDone shape executable safe invoked planned =>
            exact ⟨.native _ _ (.done _), _, _, _, ⟨fun _ _ => safe, shape, executable, _, invoked, planned⟩, rfl, rfl⟩
          | callGroundedResume shape executable safe invoked planned =>
            exact ⟨.native _ _ (.resume _), _, _, _, ⟨fun _ _ => safe, shape, executable, _, invoked, planned⟩, rfl, rfl⟩
      | raw caller =>
        cases move with
        | perform step =>
          change WorldLocalStepWith env.arguments env.view env.services env.dispatch env.lookup p world scope
            (.work (.invocation live names caller value frame), stack) _ _ at step
          cases step with
          | core incoming _ localStep outgoing =>
            cases incoming
            cases localStep with
            | invocationEmbedded ordinary embedded =>
              cases outgoing
              exact ⟨.embedded, world, _, _, ⟨rfl, raw_guard _ _, ordinary, embedded⟩, rfl, rfl⟩
            | invocationAbsent nongrounded frontier =>
              cases outgoing
              exact ⟨.query [], world, _, _, ⟨rfl, raw_guard _ _, nongrounded, frontier⟩, rfl, rfl⟩
            | invocationEquations nongrounded frontier nonempty =>
              cases outgoing
              rename_i work
              cases work with
              | nil => exact (nonempty rfl).elim
              | cons head rest =>
                exact ⟨.query (head :: rest), world, _, _,
                  ⟨rfl, raw_guard _ _, nongrounded, frontier⟩, rfl, rfl⟩
          | invocationGroundedDone shape executable invoked planned =>
            exact ⟨.native _ _ (.done _), _, _, _, ⟨raw_guard _ _, shape,
              executable, _, invoked, planned⟩, rfl, rfl⟩
          | invocationGroundedResume shape executable invoked planned =>
            exact ⟨.native _ _ (.resume _), _, _, _, ⟨raw_guard _ _, shape,
              executable, _, invoked, planned⟩, rfl, rfl⟩
    | retained q expected work =>
      rcases q with ⟨live, names, value, frame⟩
      cases expected with
      | some demand =>
        cases move with
        | perform step =>
          change WorldLocalStepWith env.arguments env.view env.services env.dispatch env.lookup p world scope
            (.work (.equations live names value demand frame work), stack) _ _ at step
          cases step with
          | core incoming _ localStep outgoing =>
            cases incoming
            cases localStep with
            | equationsNil => cases outgoing; exact ⟨.exhausted, world, _, _, ⟨rfl, rfl⟩, rfl, rfl⟩
            | equationsCons binds unified =>
              cases outgoing
              exact ⟨.use _ _ _, world, _, _, ⟨rfl, rfl, binds, unified⟩, rfl, rfl⟩
      | none =>
        cases move with
        | perform step =>
          change WorldLocalStepWith env.arguments env.view env.services env.dispatch env.lookup p world scope
            (.work (.invocationEquations live names value frame work), stack) _ _ at step
          cases step with
          | core incoming _ localStep outgoing =>
            cases incoming
            cases localStep with
            | invocationEquationsNil => cases outgoing; exact ⟨.exhausted, world, _, _, ⟨rfl, rfl⟩, rfl, rfl⟩
            | invocationEquationsCons binds unified =>
              cases outgoing
              exact ⟨.use _ _ _, world, _, _, ⟨rfl, rfl, binds, unified⟩, rfl, rfl⟩
  · rintro ⟨reply, next, work, frames, allowed, planned, rfl⟩
    let source : Focus Context World := ⟨world, scope, .work request.task, stack, parents, published⟩
    cases request with
    | invoke q mode =>
      cases reply with
      | error =>
        cases mode with
        | raw => cases allowed
        | typed expected =>
          obtain ⟨rfl, error⟩ := allowed
          cases planned
          exact HEFocused.Move.perform (before := source) (.core (.work _) rfl (.callError error) (.returning _))
      | embedded =>
        obtain ⟨rfl, safe, ordinary, instruction⟩ := allowed
        cases mode with
        | typed expected =>
          cases planned
          exact HEFocused.Move.perform (before := source)
            (.core (.work _) rfl (.callEmbedded (typed_guard safe) ordinary instruction) (.work _))
        | raw caller =>
          cases planned
          exact HEFocused.Move.perform (before := source)
            (.core (.work _) rfl (.invocationEmbedded ordinary instruction) (.work _))
      | query queried =>
        obtain ⟨rfl, safe, nongrounded, frontier⟩ := allowed
        cases mode with
        | typed expected =>
          cases queried with
          | nil =>
            cases planned
            exact HEFocused.Move.perform (before := source)
              (.core (.work _) rfl (.callAbsent (typed_guard safe) nongrounded frontier) (.returning _))
          | cons head rest =>
            cases planned
            exact HEFocused.Move.perform (before := source)
              (.core (.work _) rfl (.callEquations (typed_guard safe) nongrounded frontier (by simp)) (.work _))
        | raw caller =>
          cases queried with
          | nil =>
            cases planned
            exact HEFocused.Move.perform (before := source)
              (.core (.work _) rfl (.invocationAbsent nongrounded frontier) (.returning _))
          | cons head rest =>
            cases planned
            exact HEFocused.Move.perform (before := source)
              (.core (.work _) rfl (.invocationEquations nongrounded frontier (by simp)) (.work _))
      | native operator arguments plan =>
        obtain ⟨safe, shape, executable, outcome, ran, finished⟩ := allowed
        cases mode <;> cases plan <;> cases planned
        · exact HEFocused.Move.perform (before := source) (.callGroundedDone shape executable (typed_guard safe) ran finished)
        · exact HEFocused.Move.perform (before := source) (.callGroundedResume shape executable (typed_guard safe) ran finished)
        · exact HEFocused.Move.perform (before := source) (.invocationGroundedDone shape executable ran finished)
        · exact HEFocused.Move.perform (before := source) (.invocationGroundedResume shape executable ran finished)
      | exhausted | use => cases allowed
    | retained q expected items =>
      cases reply with
      | exhausted =>
        obtain ⟨rfl, rfl⟩ := allowed
        cases expected <;> cases planned
        · exact HEFocused.Move.perform (before := source) (.core (.work _) rfl .invocationEquationsNil (.returning _))
        · exact HEFocused.Move.perform (before := source) (.core (.work _) rfl .equationsNil (.returning _))
      | use chosen pending reached =>
        obtain ⟨rfl, rfl, binds, unified⟩ := allowed
        cases expected <;> cases planned
        · exact HEFocused.Move.perform (before := source)
            (.core (.work _) rfl (.invocationEquationsCons binds unified) (.work _))
        · exact HEFocused.Move.perform (before := source)
            (.core (.work _) rfl (.equationsCons binds unified) (.work _))
      | error | embedded | query | native => cases allowed

theorem retained_step_of_another_view (env : WorldEnvironment Context World)
    (other : World → Context → Space) (p : Policy) (q : Input) (demand : Option Atom)
    (work : List EquationWork) (world : World) (scope : Context)
    (stack : List Continuation) (parents : List (Parent Context)) (published : List Result)
    (target : Focus Context World) :
    let source : Focus Context World := ⟨world, scope, .work (Request.task (.retained q demand work)), stack,
      parents, published⟩
    HEFocused.Move env.arguments env.view env.services env.dispatch env.lookup p source target ↔
      HEFocused.Move env.arguments other env.services env.dispatch env.lookup p source target := by
  let otherEnv : WorldEnvironment Context World := { env with view := other }
  change HEFocused.Move env.arguments env.view env.services env.dispatch env.lookup p
    ⟨world, scope, .work (Request.task (.retained q demand work)), stack, parents, published⟩ target ↔
    HEFocused.Move otherEnv.arguments otherEnv.view otherEnv.services otherEnv.dispatch otherEnv.lookup p
    ⟨world, scope, .work (Request.task (.retained q demand work)), stack, parents, published⟩ target
  rw [step_iff env, step_iff otherEnv]
  constructor <;> rintro ⟨reply, next, body, frames, fact, phase, result⟩ <;>
    refine ⟨reply, next, body, frames, ?_, phase, result⟩ <;>
    cases reply <;> exact fact

end Mettapedia.Languages.MeTTa.SpaceTheory.HEInvocationEntry
