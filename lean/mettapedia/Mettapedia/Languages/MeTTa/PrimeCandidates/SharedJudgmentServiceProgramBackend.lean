import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceProgramAdmission
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.ScopedComputationEffectTree
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# An authored composition backend for repeated judgment services

The control machine retains the existing scoped `Code`, its actual native
environment, and syntax-valued continuation frames. Each request has an
explicit submitted and returned state; the crossing carries the existing
`Invocation`. Native leaves execute through the authored effect-tree
LanguageDef, not through the source world evaluator. The ordered work queue
preserves private worlds and chronological per-world request/reply histories.

This is a typed GSLT composition backend. It is not a Pattern codec or parser
for complete service programs, a raw HOL proof-byte checker, or an unrestricted
OSLF decision procedure. Intrinsic HOL proof objects retain their disclosed
guest-calculus boundary. Matching requests retain their existing closed data.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceProgramBackend

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation SharedJudgmentFragment SharedJudgmentServices SharedJudgmentServicePrograms
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.GSLT.Dynamics.ServiceResumption
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

variable {n m k : Nat}

abbrev Output (m : Nat) := Result (Request m) (@Response m) Bool (Outcome m) Nat

/-- Bodies retain their authored scope and environment. The pair frame
records a selected value, rather than erasing dependent sequencing. -/
inductive Frame (m : Nat) where
  | sequence {n : Nat} (environment : Sub Tower.Head n m) (body : Code (n + 1))
  | sequenceSigma {n : Nat} (environment : Sub Tower.Head n m) (body : Code (n + 1))
  | pair (selected : Tower.Tm m)

inductive Control (m : Nat) where
  | evaluate {n : Nat} (environment : Sub Tower.Head n m) (code : Code n)
  | request (input : Request m)
  | response (input : Request m) (reply : Response input)
  | deliver (outcome : Outcome m)

structure Context (m : Nat) where
  frames : List (Frame m)
  state : Bool
  branch : BranchTrace
  intents : List Nat
  replies : List (Sigma (@Response m))

structure Task (m : Nat) where
  control : Control m
  context : Context m

def responseOutcome (input : Request m) (reply : Response input) : Outcome m :=
  match reply.nativePayload? with
  | some payload => .value payload.1
  | none => .stopped ⟨input, reply⟩

def Context.afterWorld (context : Context m) (world : WorldResult Bool (Tower.Tm m) Nat) : Context m :=
  { context with
    state := world.state
    branch := world.branch
    intents := context.intents ++ world.intents }

def Context.afterReply (context : Context m) (input : Request m) (reply : Response input) : Context m :=
  { context with replies := context.replies ++ [⟨input, reply⟩] }

def Context.output (context : Context m) (outcome : Outcome m) : Output m :=
  ⟨⟨context.branch, outcome, context.state, context.intents⟩, context.replies⟩

inductive Transition (m : Nat) where
  | spawn (tasks : List (Task m))
  | finish (output : Output m)

def Transition.children : Transition m → List (Task m)
  | .spawn tasks => tasks
  | .finish _ => []

/-- Independently authored local rules. In particular, no constructor
mentions `Code.worlds` or resolves a whole resumption before execution. -/
inductive LocalStep (assembly : Assembly) : Task m → Transition m → Prop where
  | native {n : Nat} (environment : Sub Tower.Head n m) (body : NativeCode n)
      (context : Context m) {worlds : List (WorldResult Bool (Tower.Tm m) Nat)}
      (backend : ContextualEffectTreeLanguage.theory.Step
        (ScopedComputationEffectTree.request
          (ScopedComputation.Code.interpret (assembly.execution m).handler environment body)
          context.state context.branch)
        (ScopedComputationEffectTree.completion worlds)) :
      LocalStep assembly ⟨.evaluate environment (.native body), context⟩
        (.spawn (worlds.map fun world =>
          ⟨.deliver (.value world.answer), context.afterWorld world⟩))
  | request {n : Nat} (environment : Sub Tower.Head n m) (input : Request n)
      (context : Context m) :
      LocalStep assembly ⟨.evaluate environment (.request input), context⟩
        (.spawn [⟨.request (input.substitute environment), context⟩])
  | invoked (input : Request m) (reply : Response input) (context : Context m)
      (crossing : Invocation assembly input reply) :
      LocalStep assembly ⟨.request input, context⟩ (.spawn [⟨.response input reply, context⟩])
  | returned (input : Request m) (reply : Response input) (context : Context m) :
      LocalStep assembly ⟨.response input reply, context⟩
        (.spawn [⟨.deliver (responseOutcome input reply), context.afterReply input reply⟩])
  | sequence {n : Nat} (environment : Sub Tower.Head n m) (first : Code n)
      (body : Code (n + 1)) (context : Context m) :
      LocalStep assembly ⟨.evaluate environment (.sequence first body), context⟩
        (.spawn [⟨.evaluate environment first,
          { context with frames := .sequence environment body :: context.frames }⟩])
  | sequenceSigma {n : Nat} (environment : Sub Tower.Head n m) (first : Code n)
      (body : Code (n + 1)) (context : Context m) :
      LocalStep assembly ⟨.evaluate environment (.sequenceSigma first body), context⟩
        (.spawn [⟨.evaluate environment first,
          { context with frames := .sequenceSigma environment body :: context.frames }⟩])
  | choose {n : Nat} (environment : Sub Tower.Head n m) (left right : Code n)
      (context : Context m) :
      LocalStep assembly ⟨.evaluate environment (.choose left right), context⟩
        (.spawn [⟨.evaluate environment left, { context with branch := false :: context.branch }⟩,
          ⟨.evaluate environment right, { context with branch := true :: context.branch }⟩])
  | sequenceValue {n : Nat} (environment : Sub Tower.Head n m) (body : Code (n + 1))
      (value : Tower.Tm m) (context : Context m) :
      LocalStep assembly
        ⟨.deliver (.value value), { context with frames := .sequence environment body :: context.frames }⟩
        (.spawn [⟨.evaluate (consSub value environment) body, context⟩])
  | sigmaValue {n : Nat} (environment : Sub Tower.Head n m) (body : Code (n + 1))
      (value : Tower.Tm m) (context : Context m) :
      LocalStep assembly
        ⟨.deliver (.value value), { context with frames := .sequenceSigma environment body :: context.frames }⟩
        (.spawn [⟨.evaluate (consSub value environment) body,
          { context with frames := .pair value :: context.frames }⟩])
  | pairValue (first second : Tower.Tm m) (context : Context m) :
      LocalStep assembly ⟨.deliver (.value second), { context with frames := .pair first :: context.frames }⟩
        (.spawn [⟨.deliver (.value (.pair first second)), context⟩])
  | valueDone (value : Tower.Tm m) (context : Context m) (empty : context.frames = []) :
      LocalStep assembly ⟨.deliver (.value value), context⟩ (.finish (context.output (.value value)))
  | stopped (reply : Sigma (@Response m)) (context : Context m) :
      LocalStep assembly ⟨.deliver (.stopped reply), context⟩ (.finish (context.output (.stopped reply)))

inductive Term (m : Nat) where
  | running (pending : List (Task m)) (completed : List (Output m))
  | completed (outputs : List (Output m))

/-- The queue is authored left-to-right depth-first control. Both native
branch expansion and source choice keep their original order. -/
inductive Step (assembly : Assembly) : Term m → Term m → Prop where
  | spawn {task : Task m} {children : List (Task m)}
      (localStep : LocalStep assembly task (.spawn children))
      (pending : List (Task m)) (completed : List (Output m)) :
      Step assembly (.running (task :: pending) completed) (.running (children ++ pending) completed)
  | finish {task : Task m} {output : Output m}
      (localStep : LocalStep assembly task (.finish output))
      (pending : List (Task m)) (completed : List (Output m)) :
      Step assembly (.running (task :: pending) completed) (.running pending (completed ++ [output]))
  | completed (outputs : List (Output m)) :
      Step assembly (.running [] outputs) (.completed outputs)

def theory (assembly : Assembly) (m : Nat) : Mettapedia.GSLT.GSLT := equalityGSLT (Term m) (Step assembly)

def start (environment : Sub Tower.Head n m) (code : Code n) (state : Bool) (branch : BranchTrace) : Term m :=
  .running [⟨.evaluate environment code, ⟨[], state, branch, [], []⟩⟩] []

def Reaches (assembly : Assembly) (source target : Term m) : Prop :=
  Nonempty ((theory assembly m).RewritePath source target)

theorem Reaches.refl (assembly : Assembly) (term : Term m) : Reaches assembly term term := ⟨.nil _⟩

theorem Reaches.single {assembly : Assembly} {source target : Term m}
    (step : Step assembly source target) : Reaches assembly source target := ⟨.cons step (.nil _)⟩

private def appendPath {assembly : Assembly} {first middle last : Term m} :
    (theory assembly m).RewritePath first middle → (theory assembly m).RewritePath middle last →
      (theory assembly m).RewritePath first last
  | .nil _, later => later
  | .cons step rest, later => .cons step (appendPath rest later)

theorem Reaches.trans {assembly : Assembly} {first middle last : Term m}
    (earlier : Reaches assembly first middle) (later : Reaches assembly middle last) :
    Reaches assembly first last := by
  obtain ⟨earlier⟩ := earlier
  obtain ⟨later⟩ := later
  exact ⟨appendPath earlier later⟩

/-! ## A decreasing control measure, independent of source world evaluation -/

def codeWeight : {n : Nat} → Code n → Nat
  | _, .native _ => 1
  | _, .request _ => 3
  | _, .sequence first body => codeWeight first + codeWeight body + 2
  | _, .sequenceSigma first body => codeWeight first + codeWeight body + 3
  | _, .choose left right => max (codeWeight left) (codeWeight right) + 1

def Frame.weight : Frame m → Nat
  | .sequence _ body => codeWeight body + 1
  | .sequenceSigma _ body => codeWeight body + 2
  | .pair _ => 1

def framesWeight : List (Frame m) → Nat
  | [] => 0
  | frame :: rest => frame.weight + framesWeight rest

def Control.weight : Control m → Nat
  | .evaluate _ code => codeWeight code
  | .request _ => 2
  | .response _ _ => 1
  | .deliver _ => 0

def Task.weight (task : Task m) : Nat := task.control.weight + framesWeight task.context.frames

theorem local_progress (assembly : Assembly) (task : Task m) :
    ∃ transition, LocalStep assembly task transition := by
  obtain ⟨control, context⟩ := task
  cases control with
  | evaluate environment code =>
      cases code with
      | native body =>
          exact ⟨_, .native environment body context
            ((ScopedComputationEffectTree.native_complete_iff _ _ _ _).mpr rfl)⟩
      | request input => exact ⟨_, .request environment input context⟩
      | sequence first body => exact ⟨_, .sequence environment first body context⟩
      | sequenceSigma first body => exact ⟨_, .sequenceSigma environment first body context⟩
      | choose left right => exact ⟨_, .choose environment left right context⟩
  | request input => exact ⟨_, .invoked input (invoke assembly input) context (invoke_crossing assembly input)⟩
  | response input reply => exact ⟨_, .returned input reply context⟩
  | deliver outcome =>
      cases outcome with
      | stopped reply => exact ⟨_, .stopped reply context⟩
      | value value =>
          obtain ⟨frames, state, branch, intents, replies⟩ := context
          cases frames with
          | nil => exact ⟨_, .valueDone value _ rfl⟩
          | cons frame frames =>
              cases frame with
              | sequence environment body =>
                  exact ⟨_, .sequenceValue environment body value ⟨frames, state, branch, intents, replies⟩⟩
              | sequenceSigma environment body =>
                  exact ⟨_, .sigmaValue environment body value ⟨frames, state, branch, intents, replies⟩⟩
              | pair selected =>
                  exact ⟨_, .pairValue selected value ⟨frames, state, branch, intents, replies⟩⟩

/-- Every spawned task decreases, even when a native macrostep produces
many worlds. The measure counts pending control, not proof-search runtime. -/
theorem LocalStep.decreases {assembly : Assembly} {task child : Task m} {transition : Transition m}
    (step : LocalStep assembly task transition) (member : child ∈ transition.children) :
    child.weight < task.weight := by
  cases step with
  | native environment body context backend =>
      obtain ⟨world, _, rfl⟩ := List.mem_map.mp member
      simp [Task.weight, Control.weight, codeWeight, Context.afterWorld]
  | choose environment left right context =>
      simp only [Transition.children, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;>
        simp only [Task.weight, Control.weight, codeWeight] <;> omega
  | valueDone value context empty => exact False.elim (List.not_mem_nil member)
  | stopped reply context => exact False.elim (List.not_mem_nil member)
  | request environment input context
  | invoked input reply context crossing
  | returned input reply context
  | sequence environment first body context
  | sequenceSigma environment first body context
  | sequenceValue environment body value context
  | sigmaValue environment body value context
  | pairValue first second context =>
      have same := List.mem_singleton.mp member
      subst child
      simp only [Task.weight, Control.weight, codeWeight, Frame.weight, framesWeight, Context.afterReply]
      omega

private theorem process_list (assembly : Assembly) (tasks : List (Task m)) :
    (∀ task ∈ tasks, ∀ pending completed, ∃ outputs,
      Reaches assembly (.running (task :: pending) completed) (.running pending (completed ++ outputs))) →
    ∀ pending completed, ∃ outputs,
      Reaches assembly (.running (tasks ++ pending) completed) (.running pending (completed ++ outputs)) := by
  induction tasks with
  | nil =>
      intro _ pending completed
      exact ⟨[], by simpa only [List.nil_append, List.append_nil] using
        Reaches.refl assembly (.running pending completed)⟩
  | cons task tasks ih =>
      intro each pending completed
      obtain ⟨first, firstPath⟩ := each task (by simp) (tasks ++ pending) completed
      obtain ⟨later, laterPath⟩ := ih (fun child member => each child (by simp [member]))
        pending (completed ++ first)
      refine ⟨first ++ later, ?_⟩
      simpa only [List.cons_append, List.append_assoc] using firstPath.trans laterPath

theorem task_finite (assembly : Assembly) (task : Task m) :
    ∀ pending completed, ∃ outputs,
      Reaches assembly (.running (task :: pending) completed) (.running pending (completed ++ outputs)) := by
  have general : ∀ rank, ∀ task : Task m, task.weight = rank →
      ∀ pending completed, ∃ outputs,
        Reaches assembly (.running (task :: pending) completed) (.running pending (completed ++ outputs)) := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
        intro task weight pending completed
        obtain ⟨transition, step⟩ := local_progress assembly task
        cases transition with
        | finish output => exact ⟨[output], Reaches.single (.finish step pending completed)⟩
        | spawn children =>
            obtain ⟨outputs, later⟩ := process_list assembly children (fun child member =>
              ih child.weight (by rw [← weight]; exact step.decreases member) child rfl) pending completed
            exact ⟨outputs, (Reaches.single (.spawn step pending completed)).trans later⟩
  exact general task.weight task rfl

/-- Every finite authored program has a finite backend path. Invocation is
the supplied total operation; this does not assert termination of arbitrary
external proof search. Native leaves use finite authored effect-tree steps. -/
theorem finite_completion (assembly : Assembly) (environment : Sub Tower.Head n m)
    (code : Code n) (state : Bool) (branch : BranchTrace) :
    ∃ outputs, Reaches assembly (start environment code state branch) (.completed outputs) := by
  obtain ⟨outputs, path⟩ := task_finite assembly
    ⟨.evaluate environment code, ⟨[], state, branch, [], []⟩⟩ [] []
  exact ⟨outputs, path.trans (Reaches.single (.completed outputs))⟩

theorem completed_inert (assembly : Assembly) (outputs : List (Output m)) (target : Term m) :
    ¬ Step assembly (.completed outputs) target := by
  intro step
  cases step

/-! ## Source semantics as a proof invariant, never a backend premise -/

private def resume (assembly : Assembly) : List (Frame m) → Outcome m → Execution m
  | [], outcome => .pure outcome
  | frame :: rest, outcome =>
      match outcome with
      | .stopped reply => .pure (.stopped reply)
      | .value value =>
          match frame with
          | .sequence environment body =>
              (Code.interpret assembly (consSub value environment) body).bind (resume assembly rest)
          | .sequenceSigma environment body =>
              ((Code.interpret assembly (consSub value environment) body).map
                (Outcome.map (.pair value))).bind (resume assembly rest)
          | .pair selected => resume assembly rest (.value (.pair selected value))

private theorem resume_stopped (assembly : Assembly) (frames : List (Frame m))
    (reply : Sigma (@Response m)) : resume assembly frames (.stopped reply) = .pure (.stopped reply) := by
  cases frames <;> rfl

private theorem resume_pair (assembly : Assembly) (selected : Tower.Tm m) (frames : List (Frame m)) :
    resume assembly (.pair selected :: frames) = resume assembly frames ∘ Outcome.map (.pair selected) := by
  funext outcome
  cases outcome with
  | value _ => rfl
  | stopped reply => exact (resume_stopped assembly frames reply).symm

private def controlProgram (assembly : Assembly) (frames : List (Frame m)) : Control m → Execution m
  | .evaluate environment code => (Code.interpret assembly environment code).bind (resume assembly frames)
  | .request input => (requestProgram input).bind (resume assembly frames)
  | .response input reply => resume assembly frames (responseOutcome input reply)
  | .deliver outcome => resume assembly frames outcome

private def pendingReplies : Control m → List (Sigma (@Response m))
  | .response input reply => [⟨input, reply⟩]
  | _ => []

private def taskWorlds (assembly : Assembly) (task : Task m) : List (Output m) :=
  (runWorldsAt (invoke assembly) (controlProgram assembly task.context.frames task.control)
    task.context.state task.context.branch).map
      (Result.prepend task.context.intents (task.context.replies ++ pendingReplies task.control))

private def transitionWorlds (assembly : Assembly) : Transition m → List (Output m)
  | .spawn children => children.flatMap (taskWorlds assembly)
  | .finish output => [output]

private def termWorlds (assembly : Assembly) : Term m → List (Output m)
  | .running pending completed => completed ++ pending.flatMap (taskWorlds assembly)
  | .completed outputs => outputs

private theorem controlProgram_sequence (assembly : Assembly) (environment : Sub Tower.Head n m)
    (first : Code n) (body : Code (n + 1)) (frames : List (Frame m)) :
    controlProgram assembly frames (.evaluate environment (.sequence first body)) =
      controlProgram assembly (.sequence environment body :: frames) (.evaluate environment first) := by
  simp only [controlProgram, Code.interpret, Resumption.bind_assoc]
  congr 1
  funext outcome
  cases outcome <;> simp only [resume, Resumption.pure_bind, resume_stopped]

private theorem controlProgram_sequenceSigma (assembly : Assembly) (environment : Sub Tower.Head n m)
    (first : Code n) (body : Code (n + 1)) (frames : List (Frame m)) :
    controlProgram assembly frames (.evaluate environment (.sequenceSigma first body)) =
      controlProgram assembly (.sequenceSigma environment body :: frames) (.evaluate environment first) := by
  simp only [controlProgram, Code.interpret, Resumption.bind_assoc]
  congr 1
  funext outcome
  cases outcome <;> simp only [resume, Resumption.pure_bind, resume_stopped]

private theorem controlProgram_sigmaValue (assembly : Assembly) (environment : Sub Tower.Head n m)
    (body : Code (n + 1)) (value : Tower.Tm m) (frames : List (Frame m)) :
    controlProgram assembly (.sequenceSigma environment body :: frames) (.deliver (.value value)) =
      controlProgram assembly (.pair value :: frames) (.evaluate (consSub value environment) body) := by
  change ((Code.interpret assembly (consSub value environment) body).map
    (Outcome.map (.pair value))).bind (resume assembly frames) =
      (Code.interpret assembly (consSub value environment) body).bind
        (resume assembly (.pair value :: frames))
  rw [Resumption.bind_map, resume_pair]

private theorem localStep_preserves {assembly : Assembly} {task : Task m} {transition : Transition m}
    (step : LocalStep assembly task transition) :
    taskWorlds assembly task = transitionWorlds assembly transition := by
  cases step with
  | native environment body context backend =>
      have exactWorlds := (ScopedComputationEffectTree.native_complete_iff _ _ _ _).mp backend
      rw [exactWorlds]
      simp only [taskWorlds, transitionWorlds, controlProgram, Code.interpret, pendingReplies,
        runWorldsAt_bind, runWorldsAt_map, runWorldsAt_embed, List.flatMap_map, List.map_flatMap,
        List.map_map, Function.comp_def, Result.mapAnswer, Result.prepend, Context.afterWorld,
        Mettapedia.TypeTheory.ContextualDependentSequencing.WorldResult.mapAnswer,
        List.nil_append, List.append_nil]
      congr 1
      funext world
      congr 1
      funext result
      simp only [Result.prepend, List.append_assoc]
  | request environment input context =>
      simp [taskWorlds, transitionWorlds, controlProgram, Code.interpret, pendingReplies]
  | invoked input reply context crossing =>
      have same := (invoke_iff assembly input reply).mpr crossing
      cases same
      simp only [taskWorlds, transitionWorlds, controlProgram, requestProgram, pendingReplies,
        Resumption.bind, runWorldsAt_request, responseOutcome, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.map_map, Function.comp_def, Result.prepend_comp]
      rfl
  | returned input reply context =>
      simp [taskWorlds, transitionWorlds, controlProgram, pendingReplies, Context.afterReply]
  | sequence environment first body context =>
      simp only [taskWorlds, transitionWorlds, controlProgram_sequence, pendingReplies,
        List.flatMap_cons, List.flatMap_nil, List.append_nil]
  | sequenceSigma environment first body context =>
      simp only [taskWorlds, transitionWorlds, controlProgram_sequenceSigma, pendingReplies,
        List.flatMap_cons, List.flatMap_nil, List.append_nil]
  | choose environment left right context =>
      simp only [taskWorlds, transitionWorlds, controlProgram, Code.interpret, Resumption.bind,
        runWorldsAt_choose, pendingReplies, List.flatMap_cons, List.flatMap_nil, List.map_append,
        List.append_nil]
  | sequenceValue environment body value context =>
      simp [taskWorlds, transitionWorlds, controlProgram, resume, pendingReplies]
  | sigmaValue environment body value context =>
      simp only [taskWorlds, transitionWorlds, controlProgram_sigmaValue, pendingReplies,
        List.flatMap_cons, List.flatMap_nil, List.append_nil]
  | pairValue first second context =>
      simp [taskWorlds, transitionWorlds, controlProgram, resume, pendingReplies]
  | valueDone value context empty =>
      simp [taskWorlds, transitionWorlds, controlProgram, empty, resume, pendingReplies,
        runWorldsAt_pure, Result.prepend, Context.output]
  | stopped reply context =>
      simp [taskWorlds, transitionWorlds, controlProgram, resume_stopped, pendingReplies,
        runWorldsAt_pure, Result.prepend, Context.output]

private theorem step_preserves {assembly : Assembly} {source target : Term m}
    (step : Step assembly source target) : termWorlds assembly source = termWorlds assembly target := by
  cases step with
  | spawn localStep pending completed =>
      simpa only [termWorlds, transitionWorlds, List.flatMap_cons, List.flatMap_append] using
        congrArg (fun worlds => completed ++ (worlds ++ pending.flatMap (taskWorlds assembly)))
          (localStep_preserves localStep)
  | finish localStep pending completed =>
      have same := localStep_preserves localStep
      simp only [termWorlds, List.flatMap_cons, same, transitionWorlds, List.append_assoc]
  | completed outputs => simp only [termWorlds, List.flatMap_nil, List.append_nil]

private theorem path_preserves {assembly : Assembly} :
    {source target : (theory assembly m).Term} →
      (theory assembly m).RewritePath source target → termWorlds assembly source = termWorlds assembly target
  | _, _, .nil _ => rfl
  | _, _, .cons step rest => (step_preserves step).trans (path_preserves rest)

private theorem reaches_preserves {assembly : Assembly} {source target : Term m}
    (reaches : Reaches assembly source target) : termWorlds assembly source = termWorlds assembly target := by
  obtain ⟨path⟩ := reaches
  exact path_preserves path

private theorem start_worlds (assembly : Assembly) (environment : Sub Tower.Head n m)
    (code : Code n) (state : Bool) (branch : BranchTrace) :
    termWorlds assembly (start environment code state branch) = Code.run assembly environment code state branch := by
  simp only [termWorlds, start, taskWorlds, controlProgram, resume, Resumption.bind_pure,
    pendingReplies, List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, Code.run]
  exact List.map_id _

/-- Every reachable completion has exactly the source resumption's complete
ordered results. No shape restriction or source admission assumption is used. -/
theorem completion_sound (assembly : Assembly) (environment : Sub Tower.Head n m)
    (code : Code n) (state : Bool) (branch : BranchTrace) {outputs : List (Output m)}
    (completed : Reaches assembly (start environment code state branch) (.completed outputs)) :
    outputs = Code.run assembly environment code state branch := by
  have same := reaches_preserves completed
  rw [start_worlds] at same
  exact same.symm

/-- The converse is a finite path through the independently authored rules,
not a transition whose premise is equality to the source evaluator. -/
theorem completion_run_iff (assembly : Assembly) (environment : Sub Tower.Head n m)
    (code : Code n) (state : Bool) (branch : BranchTrace) (outputs : List (Output m)) :
    Reaches assembly (start environment code state branch) (.completed outputs) ↔
      outputs = Code.run assembly environment code state branch := by
  constructor
  · exact completion_sound assembly environment code state branch
  · intro same
    obtain ⟨actual, path⟩ := finite_completion assembly environment code state branch
    have exactActual := completion_sound assembly environment code state branch path
    have identifies : actual = outputs := exactActual.trans same.symm
    cases identifies
    exact path

/-- Qualification connects the operational backend to the independently
recursive scoped worlds, including stopped outcomes and full reply fibres. -/
theorem completion_worlds_iff (assembly : Assembly) (execution : ExecutionQualified assembly)
    (environment : Sub Tower.Head n m) (code : Code n) (state : Bool) (branch : BranchTrace)
    (outputs : List (Output m)) :
    Reaches assembly (start environment code state branch) (.completed outputs) ↔
      outputs = Code.worlds assembly environment code state branch := by
  rw [completion_run_iff, Code.interpret_worlds assembly execution]

/-! ## Capture-safe environments and independently admitted outputs -/

/-- Source substitution and environment composition license exactly the
same complete backend observations. Both executions use the one handler at
the final target scope; no cross-scope handler naturality is assumed. -/
theorem completion_substitute_iff (assembly : Assembly) (later : Sub Tower.Head m k)
    (earlier : Sub Tower.Head n m) (code : Code n) (state : Bool) (branch : BranchTrace)
    (outputs : List (Output k)) :
    Reaches assembly (start later (code.substitute earlier) state branch) (.completed outputs) ↔
      Reaches assembly (start (subComp later earlier) code state branch) (.completed outputs) := by
  rw [completion_run_iff, completion_run_iff]
  simp only [Code.run, Code.interpret_substitute]

/-- Backend values inherit native admission from the independent source
judgment. In particular, its request rule retains `EnvironmentAdmitted` and
the explicit type contract for every actual successful invocation. A stopped
reply cannot discharge the value-outcome premise. -/
theorem completion_value_admitted {assembly : Assembly}
    (qualified : specification.Satisfies assembly)
    {context : Tower.Ctx n} {targetContext : Tower.Ctx m} {code : Code n} {type : Tower.Tm n}
    (admitted : Admission assembly context code type) {environment : Sub Tower.Head n m}
    (target : FormationSensitive.ContextFormation assembly.rules targetContext)
    (typed : FormationSensitive.CtxMor assembly.rules context targetContext environment)
    {state : Bool} {branch : BranchTrace} {outputs : List (Output m)}
    (completed : Reaches assembly (start environment code state branch) (.completed outputs))
    {output : Output m} {value : Tower.Tm m} (observed : output ∈ outputs)
    (isValue : output.world.answer = .value value) :
    FormationSensitive.Judgment assembly.rules targetContext value (subst environment type) := by
  rw [completion_sound assembly environment code state branch completed] at observed
  exact admitted.run_preserve qualified target typed observed isValue

/-- Two actual formation-sensitive context morphisms transport admission to
the backend executing substituted source. The result type keeps both native
substitutions, including their lifting under dependent binders. -/
theorem completion_substitute_value_admitted {assembly : Assembly}
    (qualified : specification.Satisfies assembly)
    {context : Tower.Ctx n} {middleContext : Tower.Ctx m} {targetContext : Tower.Ctx k}
    {code : Code n} {type : Tower.Tm n} (admitted : Admission assembly context code type)
    {earlier : Sub Tower.Head n m} {later : Sub Tower.Head m k}
    (earlierTyped : FormationSensitive.CtxMor assembly.rules context middleContext earlier)
    (laterTyped : FormationSensitive.CtxMor assembly.rules middleContext targetContext later)
    (target : FormationSensitive.ContextFormation assembly.rules targetContext)
    {state : Bool} {branch : BranchTrace} {outputs : List (Output k)}
    (completed : Reaches assembly (start later (code.substitute earlier) state branch) (.completed outputs))
    {output : Output k} {value : Tower.Tm k} (observed : output ∈ outputs)
    (isValue : output.world.answer = .value value) :
    FormationSensitive.Judgment assembly.rules targetContext value (subst later (subst earlier type)) := by
  have composed : FormationSensitive.CtxMor assembly.rules context targetContext (subComp later earlier) := by
    intro index
    have transported := (earlierTyped index).substitute laterTyped
    change FormationSensitive.Typing assembly.rules targetContext (subst later (earlier index))
      (subst (fun prior => subst later (earlier prior)) (Ctx.lookup context index))
    rw [subst_comp] at transported
    exact transported
  have path := (completion_substitute_iff assembly later earlier code state branch outputs).mp completed
  simpa only [subst_subComp] using
    completion_value_admitted qualified admitted target composed path observed isValue

/-! ## Actual nested services and exact-history controls -/

namespace Controls

open SharedJudgmentServicePrograms.Examples SharedJudgmentServicePrograms.AdmissionExamples

def nestedOutput (state : Bool) (branch : BranchTrace) : Output 2 :=
  ⟨⟨branch, .value nestedValue, state, []⟩,
    [⟨matchingRequest 2, invoke common (matchingRequest 2)⟩,
      ⟨holRequest 2, invoke common (holRequest 2)⟩]⟩

/-- Matching and actual accepted HOL induction both cross the machine before
the innermost native reflexivity body returns its two dependent Sigma pairs. -/
theorem nested_completion_iff (state : Bool) (branch : BranchTrace) (outputs : List (Output 2)) :
    Reaches common (start ids matchingThenHOLIdentity state branch) (.completed outputs) ↔
      outputs = [nestedOutput state branch] := by
  rw [completion_run_iff, nested_worlds]
  rfl

theorem nested_completion_admitted (state : Bool) (branch : BranchTrace) :
    Reaches common (start ids matchingThenHOLIdentity state branch)
        (.completed [nestedOutput state branch]) ∧
      FormationSensitive.Judgment common.rules ScopedComputation.NativeExamples.context nestedValue nestedType := by
  have completed := (nested_completion_iff state branch _).mpr rfl
  refine ⟨completed, ?_⟩
  have typed : FormationSensitive.CtxMor common.rules ScopedComputation.NativeExamples.context
      ScopedComputation.NativeExamples.context ids := by
    intro index
    simpa only [ids, subst_ids] using
      (FormationSensitive.Typing.var (R := common.rules) (Γ := ScopedComputation.NativeExamples.context) index)
  have preserved := completion_value_admitted common_qualified nested_admitted
    nested_admitted.context_formed typed completed (List.mem_singleton_self _) rfl
  simpa only [subst_ids] using preserved

/-- Mutating even only the reply list cannot preserve the declared complete
observation. Full dependent request/reply pairs, not receipt codes, are kept. -/
theorem changed_nested_history_rejected (state : Bool) (branch : BranchTrace)
    (history : List (Sigma (@Response 2)))
    (changed : history ≠ (nestedOutput state branch).replies) :
    ¬ Reaches common (start ids matchingThenHOLIdentity state branch)
      (.completed [{ nestedOutput state branch with replies := history }]) := by
  intro completed
  have same := (nested_completion_iff state branch _).mp completed
  exact changed (congrArg Result.replies (List.cons.inj same).1)

theorem reversed_nested_history_rejected (state : Bool) (branch : BranchTrace) :
    ¬ Reaches common (start ids matchingThenHOLIdentity state branch)
      (.completed [{ nestedOutput state branch with
        replies := (nestedOutput state branch).replies.reverse }]) := by
  apply changed_nested_history_rejected
  intro same
  have first := congrArg Sigma.fst (List.cons.inj same).1
  cases first

theorem dropped_nested_history_rejected (state : Bool) (branch : BranchTrace) :
    ¬ Reaches common (start ids matchingThenHOLIdentity state branch)
      (.completed [{ nestedOutput state branch with
        replies := [⟨holRequest 2, invoke common (holRequest 2)⟩] }]) := by
  apply changed_nested_history_rejected
  intro same
  have lengths := congrArg List.length same
  simp only [nestedOutput, List.length_cons, List.length_nil] at lengths
  omega

def stoppedOutput (state : Bool) (branch : BranchTrace) : Output 2 :=
  ⟨⟨branch, .stopped ⟨changedHOLRequest 2, invoke common (changedHOLRequest 2)⟩, state, []⟩,
    [⟨matchingRequest 2, invoke common (matchingRequest 2)⟩,
      ⟨changedHOLRequest 2, invoke common (changedHOLRequest 2)⟩]⟩

/-- Omitting induction changes the actual second request. Its decline keeps
the earlier success and prevents evaluation of the remaining native body. -/
theorem stopped_completion_iff (state : Bool) (branch : BranchTrace) (outputs : List (Output 2)) :
    Reaches common (start ids matchingThenChangedHOL state branch) (.completed outputs) ↔
      outputs = [stoppedOutput state branch] := by
  rw [completion_run_iff, matching_then_changed_hol_stops]
  rfl

theorem stopped_completion_no_value (state : Bool) (branch : BranchTrace)
    {outputs : List (Output 2)}
    (completed : Reaches common (start ids matchingThenChangedHOL state branch) (.completed outputs))
    {output : Output 2} (observed : output ∈ outputs) (value : Tower.Tm 2) :
    output.world.answer ≠ .value value := by
  rw [(stopped_completion_iff state branch outputs).mp completed] at observed
  have same := List.mem_singleton.mp observed
  subst output
  intro impossible
  cases impossible

theorem stopped_completion_nonempty (state : Bool) (branch : BranchTrace) :
    Reaches common (start ids matchingThenChangedHOL state branch)
        (.completed [stoppedOutput state branch]) ∧
      ¬ Reaches common (start ids matchingThenChangedHOL state branch) (.completed []) := by
  constructor
  · exact (stopped_completion_iff state branch _).mpr rfl
  · rw [stopped_completion_iff]
    intro impossible
    cases impossible

/-- A real native choice/write/read/intent tree is one macrostep of the
composition machine. Its two ordered children still retain distinct private
states, both chronological intent lists, and the caller's pending frames and
service history. No equality of source and target step counts is claimed. -/
theorem native_effect_macrostep (context : Context 2) :
    LocalStep common
      ⟨.evaluate ids (.native ScopedComputation.NativeExamples.source), context⟩
      (.spawn
        [⟨.deliver (.value (.pair ScopedComputation.NativeExamples.older
            (.refl ScopedComputation.NativeExamples.older))),
          { context with
            state := true
            branch := false :: context.branch
            intents := context.intents ++ [10, 30] }⟩,
         ⟨.deliver (.value (.pair ScopedComputation.NativeExamples.newer
            (.refl ScopedComputation.NativeExamples.newer))),
          { context with
            state := false
            branch := true :: context.branch
            intents := context.intents ++ [20, 40] }⟩]) := by
  apply LocalStep.native ids ScopedComputation.NativeExamples.source context
    (worlds :=
      [⟨false :: context.branch,
        .pair ScopedComputation.NativeExamples.older (.refl ScopedComputation.NativeExamples.older),
        true, [10, 30]⟩,
       ⟨true :: context.branch,
        .pair ScopedComputation.NativeExamples.newer (.refl ScopedComputation.NativeExamples.newer),
        false, [20, 40]⟩])
  apply (ScopedComputationEffectTree.native_complete_iff _ _ _ _).mpr
  exact (ScopedComputation.NativeExamples.source_interpretation context.state context.branch).symm

def substitutedOutput (state : Bool) (branch : BranchTrace) : Output 1 :=
  ⟨⟨branch, .value SubstitutionExamples.substitutedResult, state, []⟩,
    [⟨(SubstitutionExamples.source.substitute SubstitutionExamples.squareSubstitution).request,
      invoke common
        (SubstitutionExamples.source.substitute SubstitutionExamples.squareSubstitution).request⟩]⟩

/-- The actual higher-order HOL environment survives the service-success
binder, authored lambda, and replacement lambda in the submitted source. -/
theorem substituted_completion_iff (state : Bool) (branch : BranchTrace) (outputs : List (Output 1)) :
    Reaches common
      (start ids (ofSource (SubstitutionExamples.source.substitute SubstitutionExamples.squareSubstitution))
        state branch) (.completed outputs) ↔
      outputs = [substitutedOutput state branch] := by
  have returned : (invoke common
      (SubstitutionExamples.source.substitute SubstitutionExamples.squareSubstitution).request).nativePayload? =
      some (FormationSensitiveHOLUniformList.rawMapLength, .const `HOLUniformList.prop) := by
    rw [(invoke_iff _ _ _).mpr SubstitutionExamples.substituted_actual_crossing]
    rfl
  have body := Option.some.inj
    ((continuation_success returned).symm.trans SubstitutionExamples.substituted_program)
  rw [completion_run_iff, ofSource_success common _ returned, body]
  rfl

theorem higher_order_environment_completion (state : Bool) (branch : BranchTrace) :
    Reaches common
      (start SubstitutionExamples.squareSubstitution (ofSource SubstitutionExamples.source) state branch)
      (.completed [substitutedOutput state branch]) := by
  have substituted := (substituted_completion_iff state branch _).mpr rfl
  have transported := (completion_substitute_iff common ids SubstitutionExamples.squareSubstitution
    (ofSource SubstitutionExamples.source) state branch [substitutedOutput state branch]).mp substituted
  simpa only [subComp_ids_left] using transported

/-- Supplying the correct request/reply history does not license the old
unsubstituted answer. This is an exact-output rejection, not a HOL refutation
or a judgment about native conversion of the two returned expressions. -/
theorem wrong_environment_completion_rejected (state : Bool) (branch : BranchTrace) :
    ¬ Reaches common
      (start ids (ofSource (SubstitutionExamples.source.substitute SubstitutionExamples.squareSubstitution))
        state branch)
      (.completed [⟨⟨branch, .value SubstitutionExamples.originalResult, state, []⟩,
        (substitutedOutput state branch).replies⟩]) := by
  intro completed
  have same := (substituted_completion_iff state branch _).mp completed
  have answers := congrArg (fun output : Output 1 => output.world.answer) (List.cons.inj same).1
  exact SubstitutionExamples.changed_environment_changes_result (Outcome.value.inj answers).symm

end Controls

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceProgramBackend
