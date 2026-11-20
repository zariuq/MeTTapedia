import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.HEOnTheStep.FramedMachines
import Mettapedia.Languages.MeTTa.HE.RecursiveExecution

/-!
# HE's retained-control machine on the step

HE's evaluator in the tree is a machine whose state is already atoms of three kinds
(`HE.RecursiveMachine.Contextual`): the **pending work** (`Control.work task`: every task carries
its logical activation, the binding frame of HE's plan items), the **continuation stack**
(first-order `Continuation` frames), and the **published answers** (`emitted`). Each transition
enters one request or consumes one continuation (`LocalStepWith`); publication emits an answer when
the stack is empty (`Step.publish`). Two forms are in the tree:

* `Step`: the read-only space, carried in the configuration;
* `WorldStep`: one shared `World`, read through `view` and changed by host services (native calls,
  grounded operations with effects, captured binding snapshots).

## The theorems

* `localStep_framed`, `worldLocalStep_framed`: **every HE transition is local.** It pops the frames
  it consumes, pushes the frames it creates, and the same move is a transition over every other base
  of the stack.
* `he_step_iff`, `he_world_step_iff`: HE's machines are framed machines (`heMachine`,
  `heWorldMachine`), configuration by configuration.
* `he_on_the_step`, `he_world_on_the_step`: **the model of HE's machine is strongly bisimilar to the
  step restricted to its ground rule family.** Placed on the store
  (one occurrence for the world, one for the pending work with the stack's depth, one per
  continuation frame, one per published answer), HE's transitions are exactly the firings of their
  rules, one firing per HE step, as a strong bisimulation through representation. The rules are
  ground and the knowledge stays trivial: matching, casts, equation queries and grounded dispatch are
  premises of the transition a rule is made from, so the step's own unification does none of that
  work.
* Readouts: the possible outcomes (answer bag, world reached) agree (`he_outcomes_eq`,
  `he_world_outcomes_eq`); a completed HE phase (`observe`) is read off the store as its answer bag
  (`he_completed_answers`).
* `he_world_target_prefix` and `he_world_source_prefix` connect finite paths to the retained HE
  source, including its argument admission policy. `he_world_completed_source_iff` connects
  completed firings to the independent recursive source judgment, observing the answer bag and
  reached world. An incomplete prefix is not a completed empty result.
  `he_world_completed_ordered_iff` instead reads the word of actual publications in the
  supplied firing path, retaining the given initial answer history.
* `CollectorCustody.collector_completed_return` uses the physical collapse and capture firings
  to deliver a completed batch with its collector receipt. Label bisimulation alone does not
  establish this: a raw padded opening can re-create an older frame at the same slot.
  `nested_collector_completed_return` composes the actual two-level run: the completed reply
  selects its saved parent, not another frame with the same activation.
* No added divergence: every firing is one HE step (`he_nonZeno`), and the store runs forever exactly
  when HE does (`he_divergence_iff`, `he_world_divergence_iff`).

## Controls

* `HEControls.he_fires_example`: pending work on the empty tuple returns the empty expression; from
  every store representing it the step fires to the result. `HEControls.he_completed_stuck`: a
  completed phase is stuck on the step as in HE.
* `HEControls.he_native_is_write`: a native call that changes the world is a writing rule, taking the
  world occurrence. `HEControls.he_read_only_no_write`: no writing rule belongs to the read-only
  machine.

## What the fragment is, and what it is not

The fragment is the whole of HE's retained-control machine as it stands in the tree: its first-order
Atom profile (the module's own scope note), with matching, casts, equation queries and grounded
dispatch as the primitive premises of single transitions. Inside one firing those premises are the
machine's: a transition's dependence on the space is its read of the world occurrence. The coarse
interface relation `HE.HESmallStep` and the LeaTTa-based state-free machine are not this machine and
are not covered here; the LeaTTa package is not on the default build path.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.HEOnTheStep

open Mettapedia.Languages.MeTTa.HE (Space)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith LocalStep
  WorldLocalStepWith WorldLocalStep WorldStep WorldSteps observe observe_eq_some)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation WorldConfiguration
  UnscopedControl managedContextControl)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval (GroundedDispatch)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result WorldServices ArgumentService
  CastLookup WorldEnvironment)
open FragmentsOfTheStep.TransitionMaps

/-- HE's read-only configurations. -/
abbrev HEConfig := Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual.Configuration

/-- HE's read-only machine step. -/
abbrev HEReadStep (dispatch : GroundedDispatch) (lookup : CastLookup) (policy : Policy) :
    HEConfig → HEConfig → Prop :=
  Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual.Step dispatch lookup policy

/-! ## Locality of HE's transitions -/

/-- **Every transition of HE's read-only machine is local**: it pops the frames it consumes, pushes
the frames it makes, and is the same move over every base of the stack. -/
theorem localStep_framed {admission : ArgumentService} {space : Space}
    {dispatch : GroundedDispatch} {lookup : CastLookup} {policy : Policy}
    {c c' : Control} {s s' : List Continuation}
    (step : LocalStepWith admission space dispatch lookup policy (c, s) (c', s')) :
    ∃ pop push base, s = pop ++ base ∧ s' = push ++ base ∧
      ∀ base', LocalStepWith admission space dispatch lookup policy (c, pop ++ base')
        (c', push ++ base') := by
  cases step
  case delivered => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.delivered; all_goals assumption⟩
  case cast => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.cast; all_goals assumption⟩
  case atomTuple => exact ⟨[], [_, _], _, rfl, rfl, fun _ => by apply LocalStepWith.atomTuple; all_goals assumption⟩
  case atomFunction => exact ⟨[], [_], _, rfl, rfl, fun _ => by apply LocalStepWith.atomFunction; all_goals assumption⟩
  case atomFallback => exact ⟨[], [_, _, _], _, rfl, rfl, fun _ => by apply LocalStepWith.atomFallback; all_goals assumption⟩
  case atomSelectionFailed => exact ⟨[], [_], _, rfl, rfl, fun _ => by apply LocalStepWith.atomSelectionFailed; all_goals assumption⟩
  case tupleNil => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.tupleNil⟩
  case tupleSingleton => exact ⟨[], [_], _, rfl, rfl, fun _ => by apply LocalStepWith.tupleSingleton⟩
  case tupleCons => exact ⟨[], [_], _, rfl, rfl, fun _ => by apply LocalStepWith.tupleCons⟩
  case branchesNil => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.branchesNil⟩
  case branchesStopped => exact ⟨[], [_], _, rfl, rfl, fun _ => by apply LocalStepWith.branchesStopped; all_goals assumption⟩
  case branchesContinue => exact ⟨[], [_, _], _, rfl, rfl, fun _ => by apply LocalStepWith.branchesContinue; all_goals assumption⟩
  case argumentsNil => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.argumentsNil⟩
  case argumentsCons => exact ⟨[], [_], _, rfl, rfl, fun _ => by apply LocalStepWith.argumentsCons⟩
  case argumentBranchesNil => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.argumentBranchesNil⟩
  case argumentBranchesStopped => exact ⟨[], [_], _, rfl, rfl, fun _ => by apply LocalStepWith.argumentBranchesStopped; all_goals assumption⟩
  case argumentBranchesContinue => exact ⟨[], [_, _], _, rfl, rfl, fun _ => by apply LocalStepWith.argumentBranchesContinue; all_goals assumption⟩
  case functionStart => exact ⟨[], [_], _, rfl, rfl, fun _ => by apply LocalStepWith.functionStart; all_goals assumption⟩
  case functionBranchesNil => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.functionBranchesNil⟩
  case functionBranchesStopped => exact ⟨[], [_], _, rfl, rfl, fun _ => by apply LocalStepWith.functionBranchesStopped; all_goals assumption⟩
  case functionBranchesContinue => exact ⟨[], [_, _], _, rfl, rfl, fun _ => by apply LocalStepWith.functionBranchesContinue; all_goals assumption⟩
  case invocationsNil => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.invocationsNil⟩
  case invocationsCons => exact ⟨[], [_, _], _, rfl, rfl, fun _ => by apply LocalStepWith.invocationsCons⟩
  case callsNil => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.callsNil⟩
  case callsCons => exact ⟨[], [_], _, rfl, rfl, fun _ => by apply LocalStepWith.callsCons⟩
  case callError => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.callError; all_goals assumption⟩
  case callEmbedded => exact ⟨[], [_], _, rfl, rfl, fun _ => by apply LocalStepWith.callEmbedded; all_goals assumption⟩
  case callAbsent => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.callAbsent; all_goals assumption⟩
  case callEquations => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.callEquations; all_goals assumption⟩
  case equationsNil => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.equationsNil⟩
  case equationsCons => exact ⟨[], [_, _], _, rfl, rfl, fun _ => by apply LocalStepWith.equationsCons; all_goals assumption⟩
  case returnRefused => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.returnRefused; all_goals assumption⟩
  case returnStopped => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.returnStopped; all_goals assumption⟩
  case returnEvaluate => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.returnEvaluate; all_goals assumption⟩
  case minimalData => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.minimalData; all_goals assumption⟩
  case minimalEval => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.minimalEval⟩
  case minimalEvalc => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.minimalEvalc; all_goals assumption⟩
  case minimalChain => exact ⟨[], [_], _, rfl, rfl, fun _ => by apply LocalStepWith.minimalChain⟩
  case minimalUnifyYes => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.minimalUnifyYes; all_goals assumption⟩
  case minimalUnifyNo => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.minimalUnifyNo; all_goals assumption⟩
  case minimalUnifyBadArity => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.minimalUnifyBadArity; all_goals assumption⟩
  case minimalConsAtom => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.minimalConsAtom⟩
  case minimalDeconsAtom => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.minimalDeconsAtom⟩
  case minimalFunction => exact ⟨[], [_], _, rfl, rfl, fun _ => by apply LocalStepWith.minimalFunction; all_goals assumption⟩
  case minimalMetta => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.minimalMetta; all_goals assumption⟩
  case minimalContextSpace => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.minimalContextSpace; all_goals assumption⟩
  case bodyStart => exact ⟨[], [_], _, rfl, rfl, fun _ => by apply LocalStepWith.bodyStart⟩
  case invocationEmbedded => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.invocationEmbedded; all_goals assumption⟩
  case invocationAbsent => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.invocationAbsent; all_goals assumption⟩
  case invocationEquations => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.invocationEquations; all_goals assumption⟩
  case invocationEquationsNil => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.invocationEquationsNil⟩
  case invocationEquationsCons => exact ⟨[], [_], _, rfl, rfl, fun _ => by apply LocalStepWith.invocationEquationsCons; all_goals assumption⟩
  case boundaryChain => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.boundaryChain⟩
  case boundaryBodyTerminal => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.boundaryBodyTerminal; all_goals assumption⟩
  case boundaryBodyResume => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.boundaryBodyResume; all_goals assumption⟩
  case boundaryFunctionReturn => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.boundaryFunctionReturn⟩
  case boundaryFunctionNoReturn => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.boundaryFunctionNoReturn; all_goals assumption⟩
  case boundaryProducerRaw => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.boundaryProducerRaw; all_goals assumption⟩
  case boundaryProducerFunction => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.boundaryProducerFunction; all_goals assumption⟩
  case boundaryReturned => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.boundaryReturned⟩
  case boundaryBatchNil => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.boundaryBatchNil⟩
  case boundaryBatchCons => exact ⟨[], [_], _, rfl, rfl, fun _ => by apply LocalStepWith.boundaryBatchCons⟩
  case boundaryNativeEmittedRaw => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.boundaryNativeEmittedRaw⟩
  case boundaryNativeEmittedReturn => exact ⟨[], [_], _, rfl, rfl, fun _ => by apply LocalStepWith.boundaryNativeEmittedReturn⟩
  case boundaryNativeCompletedRaw => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.boundaryNativeCompletedRaw⟩
  case boundaryNativeCompletedReturn => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.boundaryNativeCompletedReturn; all_goals assumption⟩
  case publish => exact ⟨[_], [], _, rfl, rfl, fun _ => by apply LocalStepWith.publish; all_goals assumption⟩
  case singleton => exact ⟨[_], [], _, rfl, rfl, fun _ => by apply LocalStepWith.singleton⟩
  case branches => exact ⟨[_], [], _, rfl, rfl, fun _ => by apply LocalStepWith.branches⟩
  case tupleTail => exact ⟨[_], [], _, rfl, rfl, fun _ => by apply LocalStepWith.tupleTail⟩
  case arguments => exact ⟨[_], [], _, rfl, rfl, fun _ => by apply LocalStepWith.arguments⟩
  case argumentTail => exact ⟨[_], [], _, rfl, rfl, fun _ => by apply LocalStepWith.argumentTail⟩
  case functionHeads => exact ⟨[_], [], _, rfl, rfl, fun _ => by apply LocalStepWith.functionHeads⟩
  case functionAssemble => exact ⟨[_], [], _, rfl, rfl, fun _ => by apply LocalStepWith.functionAssemble⟩
  case diagnostics => exact ⟨[_], [], _, rfl, rfl, fun _ => by apply LocalStepWith.diagnostics⟩
  case boundaryBatch => exact ⟨[_], [], _, rfl, rfl, fun _ => by apply LocalStepWith.boundaryBatch⟩
  case calls => exact ⟨[_], [], _, rfl, rfl, fun _ => by apply LocalStepWith.calls⟩
  case append => exact ⟨[_], [_], _, rfl, rfl, fun _ => by apply LocalStepWith.append⟩
  case prepend => exact ⟨[_], [], _, rfl, rfl, fun _ => by apply LocalStepWith.prepend⟩
  case contextStep => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.contextStep; all_goals assumption⟩
  case contextReturn => exact ⟨[], [], _, rfl, rfl, fun _ => by apply LocalStepWith.contextReturn⟩

/-- The `core` case of the world machine: an ordinary transition under the reached view. -/
theorem core_framed {admission : ArgumentService} {Context World : Type}
    {view : World → Context → Space} {services : WorldServices Context World}
    {dispatch : GroundedDispatch} {lookup : CastLookup} {policy : Policy}
    {w : World} {label : Context} {before after : Control Context} {flatBefore flatAfter : Control}
    {stack remaining : List Continuation}
    (unscoped : UnscopedControl before flatBefore) (managed : managedContextControl before = false)
    (step : LocalStep (admission := admission) (view w label) dispatch lookup policy
      (flatBefore, stack) (flatAfter, remaining))
    (unscoped' : UnscopedControl after flatAfter) :
    ∃ pop push base, stack = pop ++ base ∧ remaining = push ++ base ∧
      ∀ base', WorldLocalStepWith admission view services dispatch lookup policy w label
        (before, pop ++ base') w (after, push ++ base') := by
  obtain ⟨pop, push, base, hs, hr, framed⟩ := localStep_framed step
  exact ⟨pop, push, base, hs, hr, fun base' => .core unscoped managed (framed base') unscoped'⟩

/-- **Every transition of HE's world machine is local.** -/
theorem worldLocalStep_framed {admission : ArgumentService} {Context World : Type}
    {view : World → Context → Space} {services : WorldServices Context World}
    {dispatch : GroundedDispatch} {lookup : CastLookup} {policy : Policy}
    {w w' : World} {label : Context} {c c' : Control Context} {s s' : List Continuation}
    (step : WorldLocalStepWith admission view services dispatch lookup policy w label (c, s) w' (c', s')) :
    ∃ pop push base, s = pop ++ base ∧ s' = push ++ base ∧
      ∀ base', WorldLocalStepWith admission view services dispatch lookup policy w label
        (c, pop ++ base') w' (c', push ++ base') := by
  cases step
  case core => exact core_framed (by assumption) (by assumption) (by assumption) (by assumption)
  case context => exact ⟨[], [], _, rfl, rfl, fun _ => by apply WorldLocalStepWith.context; all_goals assumption⟩
  case contextReturn => exact ⟨[], [], _, rfl, rfl, fun _ => by apply WorldLocalStepWith.contextReturn⟩
  case evalc => exact ⟨[], [], _, rfl, rfl, fun _ => by apply WorldLocalStepWith.evalc⟩
  case metta => exact ⟨[], [], _, rfl, rfl, fun _ => by apply WorldLocalStepWith.metta⟩
  case contextSpace => exact ⟨[], [], _, rfl, rfl, fun _ => by apply WorldLocalStepWith.contextSpace⟩
  case native => exact ⟨[], [], _, rfl, rfl, fun _ => by apply WorldLocalStepWith.native; all_goals assumption⟩
  case callGroundedDone => exact ⟨[], [], _, rfl, rfl, fun _ => by apply WorldLocalStepWith.callGroundedDone; all_goals assumption⟩
  case callGroundedResume => exact ⟨[], [], _, rfl, rfl, fun _ => by apply WorldLocalStepWith.callGroundedResume; all_goals assumption⟩
  case invocationGroundedDone => exact ⟨[], [], _, rfl, rfl, fun _ => by apply WorldLocalStepWith.invocationGroundedDone; all_goals assumption⟩
  case invocationGroundedResume => exact ⟨[], [], _, rfl, rfl, fun _ => by apply WorldLocalStepWith.invocationGroundedResume; all_goals assumption⟩
  case collapseEnter => exact ⟨[], [_], _, rfl, rfl, fun _ => by apply WorldLocalStepWith.collapseEnter; all_goals assumption⟩
  case collectEnter => exact ⟨[_], [], _, rfl, rfl, fun _ => by apply WorldLocalStepWith.collectEnter; all_goals assumption⟩
  case captureNil => exact ⟨[], [], _, rfl, rfl, fun _ => by apply WorldLocalStepWith.captureNil; all_goals assumption⟩
  case captureEmpty => exact ⟨[], [], _, rfl, rfl, fun _ => by apply WorldLocalStepWith.captureEmpty; all_goals assumption⟩
  case captureOne => exact ⟨[], [], _, rfl, rfl, fun _ => by apply WorldLocalStepWith.captureOne; all_goals assumption⟩
  case superposeEnter => exact ⟨[], [], _, rfl, rfl, fun _ => by apply WorldLocalStepWith.superposeEnter; all_goals assumption⟩
  case restoreNil => exact ⟨[], [], _, rfl, rfl, fun _ => by apply WorldLocalStepWith.restoreNil; all_goals assumption⟩
  case restoreOne => exact ⟨[], [], _, rfl, rfl, fun _ => by apply WorldLocalStepWith.restoreOne; all_goals assumption⟩
  case restoreRejected => exact ⟨[], [], _, rfl, rfl, fun _ => by apply WorldLocalStepWith.restoreRejected; all_goals assumption⟩

/-! ## HE's machines are framed machines -/

/-- Publication of HE's machine: the head of a returning batch at the empty stack. -/
def hePublish {Context : Type} : Control Context → Option (Result × Control Context)
  | .returning (head :: tail) => some (head, .returning tail)
  | _ => none

/-- What publication reads: a returning batch, its head published. -/
theorem hePublish_eq {Context : Type} :
    ∀ {c c' : Control Context} {a : Result}, hePublish c = some (a, c') →
      ∃ tail, c = .returning (a :: tail) ∧ c' = .returning tail
  | .returning (head :: tail), c', a, h => by
      simp only [hePublish, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨tail, rfl, rfl⟩
  | .returning [], _, _, h => by simp [hePublish] at h
  | .work _, _, _, h => by simp [hePublish] at h
  | .context _ _ _, _, _, h => by simp [hePublish] at h

/-- **HE's read-only machine as a framed machine**: the world is the space, which no transition
changes. -/
def heMachine (dispatch : GroundedDispatch) (lookup : CastLookup) (policy : Policy) :
    FramedMachine Space Control Continuation Result where
  transition space before space' after :=
    space' = space ∧ LocalStep space dispatch lookup policy before after
  publish := hePublish

/-- HE's configurations as framed configurations. -/
def toConfig (x : HEConfig) : Config Space Control Continuation Result :=
  ⟨x.space, x.control, x.stack, x.emitted⟩

variable {dispatch : GroundedDispatch} {lookup : CastLookup} {policy : Policy}

/-- **HE's read-only machine is the framed machine**, step for step. -/
theorem he_step_iff (x y : HEConfig) :
    HEReadStep dispatch lookup policy x y ↔
      (heMachine dispatch lookup policy).Step (toConfig x) (toConfig y) := by
  obtain ⟨sp, c, s, e⟩ := x
  obtain ⟨sp', c', s', e'⟩ := y
  constructor
  · intro step
    cases step with
    | internal local' => exact .internal ⟨rfl, local'⟩
    | publish => exact .publish rfl
  · intro step
    cases step with
    | internal transition =>
        obtain ⟨rfl, local'⟩ := transition
        exact .internal local'
    | publish emitted =>
        obtain ⟨tail, rfl, rfl⟩ := hePublish_eq emitted
        exact .publish

/-- **Locality of HE's read-only machine.** -/
theorem he_local : (heMachine dispatch lookup policy).Local := by
  intro w w' c c' s s' transition
  obtain ⟨rfl, step⟩ := transition
  obtain ⟨pop, push, base, hs, hs', framed⟩ := localStep_framed step
  exact ⟨pop, push, base, hs, hs', fun base' => ⟨rfl, framed base'⟩⟩

/-- **HE on the step.** The step restricted to the rules of HE's read-only machine is strongly
bisimilar to the machine, through representation: one HE transition is one firing. -/
theorem he_on_the_step :
    IsBisimulation (StoreStep (heMachine dispatch lookup policy))
      (heMachine dispatch lookup policy).Step Represents :=
  bisimulation he_local

/-- **The observations agree**: from a store representing an HE configuration, the step under HE's
rules and HE have the same possible outcomes, the answer bag and the space reached. -/
theorem he_outcomes_eq {S : Store Space Control Continuation Result} {x : HEConfig}
    (represented : Represents S (toConfig x)) :
    storeOutcomes (heMachine dispatch lookup policy) S =
      {o | ∃ y, Relation.ReflTransGen (HEReadStep dispatch lookup policy) x y ∧
        o = ((y.emitted : Multiset Result), {y.space})} := by
  rw [outcomes_eq he_local represented]
  ext o
  constructor
  · rintro ⟨y', path, rfl⟩
    -- every framed configuration reached is an HE configuration
    have lifted : ∀ {a : Config Space Control Continuation Result},
        Relation.ReflTransGen (heMachine dispatch lookup policy).Step (toConfig x) a →
          ∃ y, Relation.ReflTransGen (HEReadStep dispatch lookup policy) x y ∧
            toConfig y = a := by
      intro a path
      induction path with
      | refl => exact ⟨x, .refl, rfl⟩
      | @tail b a' _ last ih =>
          obtain ⟨y, here, rfl⟩ := ih
          obtain ⟨sp, c, s, e⟩ := a'
          refine ⟨⟨sp, c, s, e⟩, here.tail ((he_step_iff y ⟨sp, c, s, e⟩).mpr last), rfl⟩
    obtain ⟨y, here, rfl⟩ := lifted path
    exact ⟨y, here, rfl⟩
  · rintro ⟨y, path, rfl⟩
    have carried : Relation.ReflTransGen (heMachine dispatch lookup policy).Step (toConfig x) (toConfig y) := by
      induction path with
      | refl => exact .refl
      | tail _ last ih => exact ih.tail ((he_step_iff _ _).mp last)
    exact ⟨toConfig y, carried, rfl⟩

/-- **A completed HE phase is read off the store**: when HE observes the answers of a configuration,
the store representing it holds exactly those answers as its answer bag. -/
theorem he_completed_answers {S : Store Space Control Continuation Result} {x : HEConfig}
    {answers : List Result} (represented : Represents S (toConfig x))
    (observed : observe x = some answers) :
    answersOf (MeTTaCalculus.OccurrenceCommits.labels Prod.fst S.present) = (answers : Multiset Result) := by
  rw [represented.2, answersOf_encode]
  have shape := observe_eq_some observed
  rw [shape]
  rfl

/-- **No administrative firings** under HE's rules. -/
theorem he_nonZeno : Mettapedia.Machines.ProgressObservation.NonZeno (fired (heMachine dispatch lookup policy)) :=
  nonZeno _

/-- **No added and no lost divergence for HE.** -/
theorem he_divergence_iff {S : Store Space Control Continuation Result} {x : HEConfig}
    (represented : Represents S (toConfig x)) :
    (∃ Ss : ℕ → Store Space Control Continuation Result, Ss 0 = S ∧
        ∀ n, StoreStep (heMachine dispatch lookup policy) (Ss n) (Ss (n + 1))) ↔
      ∃ xs : ℕ → Config Space Control Continuation Result, xs 0 = toConfig x ∧
        ∀ n, (heMachine dispatch lookup policy).Step (xs n) (xs (n + 1)) :=
  divergence_iff he_local represented

/-! ## The shared world -/

section World

variable {Context World : Type} {view : World → Context → Space}
  {services : WorldServices Context World}

/-- **HE's world machine as a framed machine**, at the root context. -/
def heWorldMachine (view : World → Context → Space) (services : WorldServices Context World)
    (dispatch : GroundedDispatch) (lookup : CastLookup) (policy : Policy) (label : Context)
    (admission : ArgumentService := .historical) :
    FramedMachine World (Control Context) Continuation Result where
  transition w before w' after :=
    WorldLocalStep (admission := admission) view services dispatch lookup policy w label before w' after
  publish := hePublish

/-- HE's world configurations at a context, as framed configurations. -/
def toWorldConfig (x : WorldConfiguration Context World) :
    Config World (Control Context) Continuation Result :=
  ⟨x.world, x.control, x.stack, x.emitted⟩

/-- **HE's world machine is the framed machine**, step for step; the context never changes. -/
theorem he_world_step_iff (x y : WorldConfiguration Context World)
    (admission : ArgumentService := .historical) :
    WorldStep (admission := admission) view services dispatch lookup policy x y ↔
      y.context = x.context ∧
        (heWorldMachine view services dispatch lookup policy x.context admission).Step (toWorldConfig x)
          (toWorldConfig y) := by
  obtain ⟨w, label, c, s, e⟩ := x
  obtain ⟨w', label', c', s', e'⟩ := y
  constructor
  · intro step
    cases step with
    | internal local' => exact ⟨rfl, .internal local'⟩
    | publish => exact ⟨rfl, .publish rfl⟩
  · rintro ⟨same, step⟩
    simp only at same
    subst same
    cases step with
    | internal transition => exact .internal transition
    | publish emitted =>
        obtain ⟨tail, rfl, rfl⟩ := hePublish_eq emitted
        exact .publish

/-- The same fixed-root interpretation throughout an arbitrary finite
source path. This is the path map shared by bag and ordered readback. -/
theorem he_world_framed_path_iff (x y : WorldConfiguration Context World) (admission : ArgumentService) :
    WorldSteps (admission := admission) view services dispatch lookup policy x y ↔
      y.context = x.context ∧ Relation.ReflTransGen
        (heWorldMachine view services dispatch lookup policy x.context admission).Step
        (toWorldConfig x) (toWorldConfig y) := by
  constructor
  · intro path
    induction path with
    | refl => exact ⟨rfl, .refl⟩
    | tail _ edge ih =>
      have ⟨same, step⟩ := (he_world_step_iff _ _ admission).mp edge
      rw [ih.1] at step
      exact ⟨same.trans ih.1, ih.2.tail step⟩
  · rintro ⟨context, path⟩
    let read (state : Config World (Control Context) Continuation Result) :
        WorldConfiguration Context World := ⟨state.world, x.context, state.control, state.stack, state.emitted⟩
    have atStart : read (toWorldConfig x) = x := by cases x; rfl
    have atEnd : read (toWorldConfig y) = y := by
      cases y with
      | mk world label control stack emitted =>
        change label = x.context at context
        subst label
        rfl
    have source := Relation.ReflTransGen.lift read
      (fun a b step => (he_world_step_iff (read a) (read b) admission).2 ⟨rfl, step⟩) _ _ path
    simpa only [Function.onFun, atStart, atEnd] using source

/-- **Locality of HE's world machine.** -/
theorem he_world_local (label : Context) (admission : ArgumentService := .historical) :
    (heWorldMachine view services dispatch lookup policy label admission).Local := by
  intro w w' c c' s s' transition
  exact worldLocalStep_framed transition

/-- **HE with a shared world on the step.** A transition that keeps the world reads its occurrence;
one that changes it (a native call, a grounded operation with an effect, a captured snapshot) takes
it and makes the new world. -/
theorem he_world_on_the_step (label : Context) (admission : ArgumentService := .historical) :
    IsBisimulation (StoreStep (heWorldMachine view services dispatch lookup policy label admission))
      (heWorldMachine view services dispatch lookup policy label admission).Step Represents :=
  bisimulation (he_world_local label admission)

/-- **The world observations agree**: the possible outcomes on the step (answer bag, world reached)
are those of HE's world machine. -/
theorem he_world_outcomes_eq (label : Context) (admission : ArgumentService := .historical)
    {S : Store World (Control Context) Continuation Result}
    {x : Config World (Control Context) Continuation Result} (represented : Represents S x) :
    storeOutcomes (heWorldMachine view services dispatch lookup policy label admission) S =
      machineOutcomes (heWorldMachine view services dispatch lookup policy label admission) x :=
  outcomes_eq (he_world_local label admission) represented

/-- **No added and no lost divergence for HE with a world.** -/
theorem he_world_divergence_iff (label : Context) (admission : ArgumentService := .historical)
    {S : Store World (Control Context) Continuation Result}
    {x : Config World (Control Context) Continuation Result} (represented : Represents S x) :
    (∃ Ss : ℕ → Store World (Control Context) Continuation Result, Ss 0 = S ∧
        ∀ n, StoreStep (heWorldMachine view services dispatch lookup policy label admission)
          (Ss n) (Ss (n + 1))) ↔
      ∃ xs : ℕ → Config World (Control Context) Continuation Result, xs 0 = x ∧
        ∀ n, (heWorldMachine view services dispatch lookup policy label admission).Step
          (xs n) (xs (n + 1)) :=
  divergence_iff (he_world_local label admission) represented

/-- Every finite prefix of admitted firings reads back to an actual HE world path. The root
context is retained, including when pending work addresses a different context. -/
theorem he_world_target_prefix (admission : ArgumentService)
    {x : WorldConfiguration Context World} {S S' : Store World (Control Context) Continuation Result}
    (represented : Represents S (toWorldConfig x))
    (path : Relation.ReflTransGen
      (StoreStep (heWorldMachine view services dispatch lookup policy x.context admission)) S S') :
    ∃ y, WorldSteps (admission := admission) view services dispatch lookup policy x y ∧
      y.context = x.context ∧ Represents S' (toWorldConfig y) := by
  obtain ⟨final, advanced, here⟩ := store_path_to_machine represented path
  let read (state : Config World (Control Context) Continuation Result) :
      WorldConfiguration Context World :=
    ⟨state.world, x.context, state.control, state.stack, state.emitted⟩
  exact ⟨read final, (he_world_framed_path_iff x (read final) admission).mpr ⟨rfl, advanced⟩, rfl, here⟩

/-- A finite HE world path from a represented configuration lifts to admitted firings and
retains the reached world, pending continuation, and multiplicity of published answers. -/
theorem he_world_source_prefix (admission : ArgumentService)
    {x y : WorldConfiguration Context World}
    {S : Store World (Control Context) Continuation Result}
    (represented : Represents S (toWorldConfig x))
    (path : WorldSteps (admission := admission) view services dispatch lookup policy x y) :
    ∃ S', Relation.ReflTransGen
      (StoreStep (heWorldMachine view services dispatch lookup policy x.context admission)) S S' ∧
      Represents S' (toWorldConfig y) :=
  machine_path_to_store (he_world_local x.context admission) represented
    ((he_world_framed_path_iff x y admission).mp path).2

open Mettapedia.Machines.ProgressObservation (observePath)

/-- The supplied firing path determines the exact newly published
answer word. The already published prefix comes from the starting HE
configuration, never from trying to order an endpoint bag. -/
theorem he_world_firing_path_reads_ordered (admission : ArgumentService)
    {x : WorldConfiguration Context World}
    {S S' : Fired (heWorldMachine view services dispatch lookup policy x.context admission)}
    (represented : Represents S (toWorldConfig x)) (path : Quiver.Path S S') :
    ∃ y, WorldSteps (admission := admission) view services dispatch lookup policy x y ∧
      y.context = x.context ∧ Represents S' (toWorldConfig y) ∧
      y.emitted = x.emitted ++ observePath (publication
        (heWorldMachine view services dispatch lookup policy x.context admission)) path := by
  obtain ⟨z, exactTrace, here⟩ := firing_path_reads_answers represented path
  let y : WorldConfiguration Context World := ⟨z.world, x.context, z.control, z.stack, z.emitted⟩
  exact ⟨y, (he_world_framed_path_iff x y admission).mpr ⟨rfl, FramedMachine.answerTrace_path exactTrace⟩,
    rfl, here, FramedMachine.answerTrace_emitted exactTrace⟩

/-- Lift an actual HE path with a declared world projection. An
unpublished world change is a different observation from empty
publication on an unchanged world. -/
theorem he_world_source_lifts_cuts {View : Type} [DecidableEq View] (project : World → View)
    (admission : ArgumentService) {x y : WorldConfiguration Context World}
    {S : Store World (Control Context) Continuation Result}
    (represented : Represents S (toWorldConfig x))
    (source : WorldSteps (admission := admission) view services dispatch lookup policy x y) :
    let M := heWorldMachine view services dispatch lookup policy x.context admission
    ∃ (last : Fired M) (path : Quiver.Path (show Fired M from S) last),
      Represents last (toWorldConfig y) ∧
      M.CutTrace (FramedMachine.worldCut project) path.length (toWorldConfig x) (toWorldConfig y)
        (observePath (worldPublication M project) path) := by
  intro M
  have moves := ((he_world_framed_path_iff x y admission).mp source).2
  obtain ⟨n, word, exactTrace⟩ := M.path_has_cutTrace (FramedMachine.worldCut project) moves
  obtain ⟨last, path, reached, lengthEq, wordEq⟩ :=
    cut_trace_fires (FramedMachine.worldCut project) (worldPublication M project) (world_cut_agrees project)
      (he_world_local x.context admission) represented exactTrace
  exact ⟨last, path, reached, by rw [lengthEq, wordEq]; exact exactTrace⟩

/-- A physical firing path reads back to the actual HE world relation
with the same observed changes and packets, in the same cut order. -/
theorem he_world_firing_path_reads_cuts {View : Type} [DecidableEq View] (project : World → View)
    (admission : ArgumentService) {x : WorldConfiguration Context World}
    {S S' : Fired (heWorldMachine view services dispatch lookup policy x.context admission)}
    (represented : Represents S (toWorldConfig x)) (path : Quiver.Path S S') :
    let M := heWorldMachine view services dispatch lookup policy x.context admission
    ∃ y : WorldConfiguration Context World,
      WorldSteps (admission := admission) view services dispatch lookup policy x y ∧
      y.context = x.context ∧ Represents S' (toWorldConfig y) ∧
      M.CutTrace (FramedMachine.worldCut project) path.length (toWorldConfig x) (toWorldConfig y)
        (observePath (worldPublication M project) path) := by
  intro M
  obtain ⟨z, exactTrace, here⟩ := firing_path_reads_cuts (FramedMachine.worldCut project)
    (worldPublication M project) (world_cut_agrees project) represented path
  let y : WorldConfiguration Context World := ⟨z.world, x.context, z.control, z.stack, z.emitted⟩
  exact ⟨y, (he_world_framed_path_iff x y admission).mpr ⟨rfl, M.cutTrace_path exactTrace⟩,
    rfl, here, exactTrace⟩

open Mettapedia.Languages.MeTTa.HE.RecursiveExecution.Contextual.Stateful
  (source_to_finished finished_to_source)
open MeTTaCalculus.OccurrenceCommits (labels)

/-- The independent completed HE source judgment and the transform runs agree on the reached
world and answer bag. The final control cell is required: a waiting continuation with no
published answers does not certify an empty result. The store does not observe publication order. -/
theorem he_world_completed_source_iff (environment : WorldEnvironment Context World)
    {x : WorldConfiguration Context World} {S : Store World (Control Context) Continuation Result}
    (represented : Represents S (toWorldConfig x)) (answers : Multiset Result) (world : World) :
    (∃ ordered : List Result, x.SourceRel environment policy ordered world ∧
      (ordered : Multiset Result) = answers) ↔
    ∃ S', Relation.ReflTransGen (StoreStep (heWorldMachine environment.view environment.services
        environment.dispatch environment.lookup policy x.context environment.arguments)) S S' ∧
      Cell.control (.returning []) 0 ∈ labels Prod.fst S'.present ∧
      answersOf (labels Prod.fst S'.present) = answers ∧
      worldsOf (labels Prod.fst S'.present) = {world} := by
  constructor
  · rintro ⟨ordered, evaluated, rfl⟩
    obtain ⟨S', path, here⟩ :=
      he_world_source_prefix environment.arguments represented (source_to_finished evaluated)
    refine ⟨S', path, ?_, ?_, ?_⟩
    · rw [here.2]
      exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self ..)
    · rw [here.2, answersOf_encode]
      rfl
    · rw [here.2, worldsOf_encode]
      rfl
  · rintro ⟨S', path, complete, published, reached⟩
    obtain ⟨y, source, context, here⟩ :=
      he_world_target_prefix environment.arguments represented path
    rw [here.2] at complete published reached
    have ⟨control, depth⟩ := control_mem_encode complete
    rw [answersOf_encode] at published
    rw [worldsOf_encode, Multiset.singleton_inj] at reached
    have stack : y.stack = [] := List.length_eq_zero_iff.mp depth.symm
    have terminal : y = ⟨world,x.context,.returning [],[],y.emitted⟩ := by
      cases y
      simp_all only [toWorldConfig]
    exact ⟨y.emitted, finished_to_source (terminal ▸ source), published⟩

/-- The ordered counterpart of the terminal bag comparison. This asks
for the real sequence of firings, not only the final store. A prefix with
no packets is still not enough: the terminal control is required. -/
theorem he_world_completed_ordered_iff (environment : WorldEnvironment Context World)
    {x : WorldConfiguration Context World} {S : Store World (Control Context) Continuation Result}
    (represented : Represents S (toWorldConfig x)) (answers : List Result) (world : World) :
    let machine := heWorldMachine environment.view environment.services environment.dispatch environment.lookup
      policy x.context environment.arguments
    x.SourceRel environment policy answers world ↔
      ∃ (last : Fired machine) (path : Quiver.Path (show Fired machine from S) last),
        Cell.control (.returning []) 0 ∈ labels Prod.fst last.present ∧
        x.emitted ++ observePath (publication machine) path = answers ∧
        worldsOf (labels Prod.fst last.present) = {world} := by
  intro machine
  constructor
  · intro source
    let final : WorldConfiguration Context World := ⟨world, x.context, .returning [], [], answers⟩
    have framed := ((he_world_framed_path_iff x final environment.arguments).mp (source_to_finished source)).2
    obtain ⟨_, word, trace⟩ := FramedMachine.path_has_answerTrace framed
    obtain ⟨last, path, reached, _, observed⟩ :=
      answerTrace_fires (he_world_local x.context environment.arguments) represented trace
    refine ⟨last, path, ?_, ?_, ?_⟩
    · rw [reached.2]
      exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self ..)
    · rw [observed]
      exact (FramedMachine.answerTrace_emitted trace).symm
    · rw [reached.2, worldsOf_encode]
      rfl
  · rintro ⟨last, path, terminal, observed, worldAt⟩
    obtain ⟨y, source, context, here, emitted⟩ :=
      he_world_firing_path_reads_ordered environment.arguments represented path
    rw [here.2] at terminal worldAt
    obtain ⟨control, depth⟩ := control_mem_encode terminal
    rw [worldsOf_encode, Multiset.singleton_inj] at worldAt
    have stack : y.stack = [] := List.length_eq_zero_iff.mp depth.symm
    have ordered := emitted.trans observed
    have ends : y = ⟨world, x.context, .returning [], [], answers⟩ := by
      cases y
      simp_all only [toWorldConfig]
    exact finished_to_source (ends ▸ source)

open Mettapedia.Languages.MeTTa.HE.RecursiveExecution.Contextual.Stateful.Protocol
open Mettapedia.GSLT.Distinction.ProductiveBlocks (Derivation Outcome)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (worldObserve worldObserve_eq_some)

/-- The terminal answer bag suffices for the runner's error-stop decision, but does not
reconstruct the order in which the evaluator reported those answers. -/
theorem he_file_error_from_terminal_bag
    {x : WorldConfiguration Context World} {S : Store World (Control Context) Continuation Result}
    {batch ordering : List Result} (represented : Represents S (toWorldConfig x))
    (completed : worldObserve x = some batch)
    (reading : answersOf (labels Prod.fst S.present) = (ordering : Multiset Result)) :
    FileCommands.hasError ordering = FileCommands.hasError batch := by
  have actual := congrArg WorldConfiguration.emitted (worldObserve_eq_some completed)
  have bag : answersOf (labels Prod.fst S.present) = (batch : Multiset Result) := by
    rw [represented.2, answersOf_encode]
    exact congrArg (fun values : List Result => (values : Multiset Result)) actual
  exact FileCommands.hasError_perm (Multiset.coe_eq_coe.mp (reading.symm.trans bag))

/-- A genuine file report reads back to a terminal transform store, not merely to a
possibly empty partial answer bag. The remaining file execution starts in the reached
world if the report is clean, and retains its unvisited suffix if the batch has an error. -/
theorem he_file_report_has_store (environment : WorldEnvironment Context World)
    {x : WorldConfiguration Context World} {S : Store World (Control Context) Continuation Result}
    (represented : Represents S (toWorldConfig x))
    {remaining : List Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual.Task}
    {fuel : Nat} {batch : List Result} {later : List (List Result)}
    {outcome : Outcome (FileCommands.Cursor Context World) (FileCommands.Finished Context World) Empty}
    (path : Derivation (FileCommands.Step environment policy) fuel (.active x remaining) (batch :: later) outcome) :
    ∃ reached : Store World (Control Context) Continuation Result, ∃ world : World, ∃ restFuel : Nat,
      Relation.ReflTransGen (StoreStep (heWorldMachine environment.view environment.services
        environment.dispatch environment.lookup policy x.context environment.arguments)) S reached ∧
      Cell.control (.returning []) 0 ∈ labels Prod.fst reached.present ∧
      answersOf (labels Prod.fst reached.present) = (batch : Multiset Result) ∧
      worldsOf (labels Prod.fst reached.present) = {world} ∧
      Derivation (FileCommands.Step environment policy) restFuel
        (FileCommands.afterBatch world x.context remaining batch) later outcome := by
  obtain ⟨world, restFuel, source, following⟩ := FileCommands.first_report_source path rfl
  obtain ⟨reached, firings, terminal, values, store⟩ :=
    (he_world_completed_source_iff environment represented (batch : Multiset Result) world).mp
      ⟨batch, source, rfl⟩
  exact ⟨reached, world, restFuel, firings, terminal, values, store, following⟩

/-- Conversely a terminal transform path warrants the report of one actual source
batch. This recovers source order via the source derivation, not from a bag. -/
theorem he_file_store_can_report (environment : WorldEnvironment Context World)
    {x : WorldConfiguration Context World} {S reached : Store World (Control Context) Continuation Result}
    (represented : Represents S (toWorldConfig x))
    (path : Relation.ReflTransGen (StoreStep (heWorldMachine environment.view environment.services
      environment.dispatch environment.lookup policy x.context environment.arguments)) S reached)
    (terminal : Cell.control (.returning []) 0 ∈ labels Prod.fst reached.present)
    {world : World} (store : worldsOf (labels Prod.fst reached.present) = {world})
    (remaining : List Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual.Task) :
    ∃ batch : List Result, ∃ fuel : Nat,
      answersOf (labels Prod.fst reached.present) = (batch : Multiset Result) ∧
      Derivation (FileCommands.Step environment policy) fuel (.active x remaining) [batch]
        (.exhausted (FileCommands.afterBatch world x.context remaining batch)) := by
  obtain ⟨batch, source, values⟩ :=
    (he_world_completed_source_iff environment represented (answersOf (labels Prod.fst reached.present)) world).mpr
      ⟨reached, path, terminal, rfl, store⟩
  obtain ⟨fuel, report⟩ := FileCommands.report_source source remaining
  exact ⟨batch, fuel, values.symm, report⟩

end World

/-! ## Custody of the actual collector frame -/

namespace CollectorCustody

open LocatedSubstitution.Authority (Ledger Mark Ticket)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Frame SnapshotServices)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Entry (Status Value)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open MeTTaCalculus.OccurrenceCommits (labels)

inductive Phase where
  | onStack
  | capturing
  | completed

abbrev ReceiptId (Context World : Type) := Cell World (Control Context) Continuation Result × ℕ
abbrev Book (Context World : Type) := Ledger (ReceiptId Context World) Phase

variable {Context World : Type}

abbrev machine (environment : WorldEnvironment Context World) (policy : Policy) (label : Context) :=
  heWorldMachine environment.view environment.services environment.dispatch environment.lookup policy label
    environment.arguments

def admitsReturn (book : Book Context World) (selected : Selection (ReceiptId Context World))
    (reply : ReceiptId Context World)
    (ticket : Ticket (ReceiptId Context World)) : Prop :=
  book.mark ticket.key = some (.control ticket .onStack) ∧
    selected.taken = [reply, ticket.key]

theorem return_ticket_unique {book : Book Context World} {selected : Selection (ReceiptId Context World)}
    {firstReply secondReply : ReceiptId Context World}
    {old other : Ticket (ReceiptId Context World)}
    (first : admitsReturn book selected firstReply old) (second : admitsReturn book selected secondReply other) :
    old = other := by
  have sameKey : old.key = other.key := (List.cons.inj (List.cons.inj (first.2.symm.trans second.2)).2).1
  have sameMark := first.1
  rw [sameKey, second.1] at sameMark
  exact (Mark.control.inj (Option.some.inj sameMark)).1.symm

/-- Delivery is selected by the completed reply's saved parent key,
not by its value or activation. The take has exactly two occurrences. -/
def admitsHandoff (book : Book Context World) (selected : Selection (ReceiptId Context World))
    (reply : ReceiptId Context World) (child parent : Ticket (ReceiptId Context World)) : Prop :=
  book.mark reply = some (.control child .completed) ∧ child.parent = some parent.key ∧
    admitsReturn book selected reply parent

/-- Search order or a different admissible selection cannot redirect
the same stamped reply to another parent. -/
theorem handoff_parent_unique {book : Book Context World} {first second : Selection (ReceiptId Context World)}
    {reply : ReceiptId Context World} {child parent otherChild otherParent : Ticket (ReceiptId Context World)}
    (left : admitsHandoff book first reply child parent)
    (right : admitsHandoff book second reply otherChild otherParent) : parent = otherParent := by
  have sameChild := (Mark.control.inj (Option.some.inj (left.1.symm.trans right.1))).1
  have sameKey : parent.key = otherParent.key :=
    Option.some.inj (left.2.1.symm.trans (sameChild ▸ right.2.1))
  have sameMark := left.2.2.1
  rw [sameKey, right.2.2.1] at sameMark
  exact (Mark.control.inj (Option.some.inj sameMark)).1.symm

/-- An opening can be local, or explicitly return to the saved
collector at the top of its current stack. Only that actual marked
frame licenses attaching a parent to the new receipt. -/
inductive Enclosing (book : Book Context World) : List Continuation → Option (ReceiptId Context World) → Prop
  | localReturn (stack : List Continuation) : Enclosing book stack none
  | owned {stack : List Continuation} {activation : Frame} {parent : Ticket (ReceiptId Context World)} :
      book.mark parent.key = some (.control parent .onStack) →
      parent.key.1 = .frame stack.length (.collect activation) →
      Enclosing book (.collect activation :: stack) (some parent.key)

theorem Enclosing.retained {before after : CustodyStore World (Control Context) Continuation Result Phase}
    {stack : List Continuation} {parent : Option (ReceiptId Context World)}
    (origin : Enclosing before.2 stack parent) (covered : before.2.Covers before.1.present)
    (kept : RetainsLowerFrames stack.length before after) : Enclosing after.2 stack parent := by
  cases origin with
  | localReturn => exact .localReturn _
  | owned marked atParent =>
    have live := (covered.2 _).mpr (by rw [marked]; rfl)
    exact .owned ((kept live atParent (Nat.lt_succ_self _)).2.trans marked) atParent

/-- An actual collapse allocates the collector key from the selected
frame occurrence it makes. The original control occurrence identifies
its caller; the older stack is outside the taken footprint. -/
theorem open_collector (environment : WorldEnvironment Context World) (policy : Policy) (label : Context)
    {S : Store World (Control Context) Continuation Result} {book : Book Context World}
    {world : World} {live : List Atom} {scope : List String} {caller : Option Atom}
    {readiness : Status} {operand : Value} {activation : Frame} {stack : List Continuation}
    {emitted : List Result} {snapshots : SnapshotServices Context World}
    {parent : Option (ReceiptId Context World)}
    (provided : environment.services.snapshots = some snapshots)
    (represented : Represents S ⟨world,
      .work (.minimal live scope caller (.expression readiness [.symbol "collapse-bind", operand]) activation),
      stack, emitted⟩)
    (covered : book.Covers S.present) (enclosing : Enclosing book stack parent) :
    ∃ (firing : CustodyFiring (machine environment policy label) S book)
      (owner resumed collector : ReceiptId Context World),
      firing.selected.taken = [owner] ∧ firing.selected.made = [resumed, collector] ∧
      collector.1 = .frame stack.length (.collect activation) ∧
      firing.after.mark collector = some (.control ⟨collector, owner, parent⟩ .onStack) ∧
      Represents firing.result ⟨world, .work (.minimal live scope caller operand activation),
        .collect activation :: stack, emitted⟩ ∧
      RetainsLowerFrames stack.length (S, book) (firing.result, firing.after) ∧
      Enclosing firing.after stack parent := by
  let entry : Control Context :=
    .work (.minimal live scope caller (.expression readiness [.symbol "collapse-bind", operand]) activation)
  let next : Control Context := .work (.minimal live scope caller operand activation)
  let rule := readingRule (A := Result) world entry [] next [Continuation.collect activation] stack.length
  obtain ⟨selected, valid, fresh, reaches⟩ :=
    reading_allocated (S := S) (c := entry) (c' := next) (pop := []) (push := [Continuation.collect activation])
      (base := stack) book.issued covered.1 represented
  rcases selected with ⟨taken, read, made⟩
  have one : taken.length = 1 := valid.take_length.symm
  obtain ⟨owner, rfl⟩ := List.length_eq_one_iff.mp one
  have two : made.length = 2 := by
    have size := congrArg List.length valid.outputs
    simpa only [List.length_map, readingRule, popCells, List.length_cons, List.length_nil] using size
  obtain ⟨resumed, collector, rfl⟩ := List.length_eq_two.mp two
  have makes : [resumed.1, collector.1] =
      [.control next (1 + stack.length), .frame stack.length (.collect activation)] := by
    simpa only [List.map_cons, List.map_nil, readingRule, popCells, List.length_cons, List.length_nil,
      Nat.zero_add] using valid.outputs
  let firing : CustodyFiring (machine environment policy label) S book :=
    ⟨rule, .reading stack.length (fun _ => .collapseEnter provided), ⟨[owner], read, [resumed, collector]⟩,
      valid, fresh, #v[.cell none, .control ⟨collector, owner, parent⟩ .onStack]⟩
  have keeps : RetainsLowerFrames stack.length (S, book) (firing.result, firing.after) := by
    apply firing.keeps_lower_frames
    intro depth frame member
    simp [firing, rule, readingRule, popCells] at member
  refine ⟨firing, owner, resumed, collector, rfl, rfl,
    (List.cons.inj (List.cons.inj makes).2).1, ?_, reaches, keeps, enclosing.retained covered keeps⟩
  apply firing.installed
  exact List.mem_cons_of_mem _ List.mem_cons_self

/-- The real collect-entry rule consumes the precise frame named by the
receipt and transfers that same receipt to its made capture control.
Sharing an activation with a lower frame cannot redirect this return. -/
theorem begin_owned_capture (environment : WorldEnvironment Context World) (policy : Policy) (label : Context)
    {S : Store World (Control Context) Continuation Result} {book : Book Context World}
    {world : World} {rows : List Result} {activation : Frame} {stack : List Continuation}
    {emitted : List Result} {snapshots : SnapshotServices Context World}
    (provided : environment.services.snapshots = some snapshots)
    (represented : Represents S ⟨world, .returning rows, .collect activation :: stack, emitted⟩)
    (covered : book.Covers S.present) (ticket : Ticket (ReceiptId Context World))
    (marked : book.mark ticket.key = some (.control ticket .onStack))
    (top : ticket.key.1 = .frame stack.length (.collect activation)) :
    ∃ (firing : CustodyFiring (machine environment policy label) S book)
      (reply capture : ReceiptId Context World),
      admitsReturn book firing.selected reply ticket ∧
      reply.1 = .control (.returning rows) (1 + stack.length) ∧
      capture.1 = .control (.work (.capture rows [] activation)) stack.length ∧
      firing.after.mark capture = some (.control ticket .capturing) ∧
      ticket.key ∉ firing.result.present ∧
      Represents firing.result ⟨world, .work (.capture rows [] activation), stack, emitted⟩ ∧
      RetainsLowerFrames stack.length (S, book) (firing.result, firing.after) := by
  let captureWork : Control Context := .work (.capture rows [] activation)
  let rule := readingRule (A := Result) world (.returning rows) [Continuation.collect activation] captureWork [] stack.length
  obtain ⟨selected, valid, fresh, reaches⟩ :=
    reading_allocated (S := S) (c := .returning rows) (c' := captureWork) (pop := [Continuation.collect activation])
      (push := []) (base := stack) book.issued covered.1 represented
  rcases selected with ⟨taken, read, made⟩
  have two : taken.length = 2 := valid.take_length.symm
  obtain ⟨control, actual, rfl⟩ := List.length_eq_two.mp two
  have one : made.length = 1 := by
    have size := congrArg List.length valid.outputs
    simpa only [List.length_map, readingRule, popCells, List.length_cons, List.length_nil] using size
  obtain ⟨capture, rfl⟩ := List.length_eq_one_iff.mp one
  have labelsTaken : [control.1, actual.1] = [.control (.returning rows) (1 + stack.length),
      .frame stack.length (.collect activation)] := by
    simpa only [List.map_cons, List.map_nil, readingRule, popCells, List.length_cons, List.length_nil,
      Nat.zero_add] using taken_labels valid
  have old : ticket.key ∈ S.present := (covered.2 _).mpr (by rw [marked]; rfl)
  have chosen : actual ∈ S.present := valid.occurrences.taken_subset (by simp [Selection.commit])
  have owns : actual = ticket.key := same_frame_occurrence represented chosen old
    (List.cons.inj (List.cons.inj labelsTaken).2).1 top
  subst actual
  let firing : CustodyFiring (machine environment policy label) S book :=
    ⟨rule, .reading stack.length (fun _ => .collectEnter provided), ⟨[control, ticket.key], read, [capture]⟩,
      valid, fresh, #v[.control ticket .capturing]⟩
  have outs : [capture.1] = [.control captureWork stack.length] := by
    simpa only [List.map_cons, List.map_nil, readingRule, popCells, List.length_nil, Nat.zero_add] using valid.outputs
  refine ⟨firing, control, capture, ⟨marked, rfl⟩, (List.cons.inj labelsTaken).1,
    (List.cons.inj outs).1, ?_, ?_, reaches, firing.keeps_lower_frames _ ?_⟩
  · exact firing.installed List.mem_cons_self
  · exact firing.retired (List.mem_cons_of_mem _ List.mem_cons_self)
  · intro depth frame member
    change Cell.frame depth frame ∈ rule.take at member
    rcases List.mem_cons.mp member with impossible | takenFrame
    · cases impossible
    · exact popCells_depth_ge takenFrame

/-- Deliver a completed inner reply using the actual collect-entry
firing. It selects exactly the stamped return and the saved parent
frame, retires both, and starts capture with the parent's own ticket. -/
theorem handoff_to_parent (environment : WorldEnvironment Context World) (policy : Policy) (label : Context)
    {S : Store World (Control Context) Continuation Result} {book : Book Context World}
    {world : World} {rows : List Result} {activation : Frame} {stack : List Continuation}
    {emitted : List Result} {snapshots : SnapshotServices Context World}
    {reply : ReceiptId Context World} {child parent : Ticket (ReceiptId Context World)}
    (provided : environment.services.snapshots = some snapshots)
    (represented : Represents S ⟨world, .returning rows, .collect activation :: stack, emitted⟩)
    (covered : book.Covers S.present)
    (returned : book.mark reply = some (.control child .completed))
    (returnSlot : reply.1 = .control (.returning rows) (1 + stack.length))
    (enclosing : child.parent = some parent.key)
    (waiting : book.mark parent.key = some (.control parent .onStack))
    (parentSlot : parent.key.1 = .frame stack.length (.collect activation)) :
    ∃ (firing : CustodyFiring (machine environment policy label) S book)
      (capture : ReceiptId Context World),
      admitsHandoff book firing.selected reply child parent ∧
      capture.1 = .control (.work (.capture rows [] activation)) stack.length ∧
      firing.after.mark capture = some (.control parent .capturing) ∧
      reply ∉ firing.result.present ∧ parent.key ∉ firing.result.present ∧
      Represents firing.result ⟨world, .work (.capture rows [] activation), stack, emitted⟩ ∧
      RetainsLowerFrames stack.length (S, book) (firing.result, firing.after) := by
  obtain ⟨firing, takenReply, capture, selected, selectedSlot, atCapture, stamp, closed, reached, keeps⟩ :=
    begin_owned_capture environment policy label provided represented covered parent waiting parentSlot
  have tookReply : takenReply ∈ firing.selected.taken := by simp [selected.2]
  have takenLive := firing.valid.occurrences.taken_subset
    (List.mem_toFinset.mpr tookReply)
  have replyLive : reply ∈ S.present := (covered.2 _).mpr (by rw [returned]; rfl)
  have same := same_control_occurrence represented takenLive replyLive selectedSlot returnSlot
  subst takenReply
  exact ⟨firing, capture, ⟨returned, enclosing, selected⟩, atCapture, stamp,
    firing.retired tookReply, closed, reached, keeps⟩

/-- Execute the actual completed child beneath its newly issued
collector. All the child's source effects are paid before the matching
frame is consumed. The continuation starts capturing that child's
actual returned rows in its reached world under the same receipt. -/
theorem collector_body_to_capture (environment : WorldEnvironment Context World) (policy : Policy) (label : Context)
    {S : Store World (Control Context) Continuation Result} {book : Book Context World}
    {world reachedWorld : World} {live : List Atom} {scope : List String} {caller : Option Atom}
    {readiness : Status} {operand : Value} {activation : Frame} {stack : List Continuation}
    {rows emitted : List Result} {snapshots : SnapshotServices Context World}
    {parent : Option (ReceiptId Context World)}
    (provided : environment.services.snapshots = some snapshots)
    (body : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Stateful.MinimalRel
      environment label world live scope caller operand activation rows reachedWorld (policy := policy))
    (represented : Represents S ⟨world,
        .work (.minimal live scope caller (.expression readiness [.symbol "collapse-bind", operand]) activation),
        stack, emitted⟩)
    (covered : book.Covers S.present) (enclosing : Enclosing book stack parent) :
    ∃ (after : CustodyStore World (Control Context) Continuation Result Phase)
      (ticket : Ticket (ReceiptId Context World)) (capture : ReceiptId Context World),
      Relation.ReflTransGen (CustodyStep (machine environment policy label)) (S, book) after ∧
      Represents after.1 ⟨reachedWorld, .work (.capture rows [] activation), stack, emitted⟩ ∧
      after.2.Covers after.1.present ∧
      capture.1 = .control (.work (.capture rows [] activation)) stack.length ∧
      after.2.mark capture = some (.control ticket .capturing) ∧
      ticket.parent = parent ∧ ticket.key ∈ after.2.issued ∧ ticket.key ∉ after.1.present ∧
      RetainsLowerFrames stack.length (S, book) after := by
  let inner : Control Context := .work (.minimal live scope caller operand activation)
  let machine' := machine environment policy label
  obtain ⟨opening, owner, _, collector, _, _, slot, marked, ready, keepsOpening, _⟩ :=
    open_collector environment policy label provided represented covered enclosing
  have openingCover := opening.covered covered
  have frameLive : collector ∈ opening.result.present := (openingCover.2 _).mpr (by rw [marked]; rfl)
  have bodyLocal : machine'.Local := he_world_local (view := environment.view) (services := environment.services)
    (dispatch := environment.dispatch) (lookup := environment.lookup) (policy := policy) label environment.arguments
  have bodyPath : Relation.ReflTransGen
      (fun x y : World × (Control Context × List Continuation) => machine'.transition x.1 x.2 y.1 y.2)
      (world, inner, []) (reachedWorld, .returning rows, []) :=
    Mettapedia.Languages.MeTTa.HE.RecursiveExecution.Contextual.Stateful.task_complete
      (environment := environment) (policy := policy) (task := .minimal live scope caller operand activation) body []
  obtain ⟨paused, throughBody, pausedRep, pausedCover, keepsBody⟩ :=
    internal_path_beneath bodyLocal bodyPath (outer := .collect activation :: stack)
      ready openingCover
  have same := (keepsBody frameLive slot (Nat.lt_succ_self _)).2
  let ticket : Ticket (ReceiptId Context World) := ⟨collector, owner, parent⟩
  obtain ⟨closing, _, capture, _, _, labelCapture, finalTag, retired, finalRep, keepsClosing⟩ :=
    begin_owned_capture environment policy label provided pausedRep pausedCover ticket (same.trans marked) slot
  have entry : CustodyStep machine' (S, book) (opening.result, opening.after) := ⟨opening, rfl⟩
  exact ⟨(closing.result, closing.after), ticket, capture,
    ((Relation.ReflTransGen.single entry).trans throughBody).tail ⟨closing, rfl⟩,
    finalRep, closing.covered pausedCover, labelCapture, finalTag, rfl,
    Ledger.issued_mono _ _ _ _ (pausedCover.1
      ((pausedCover.2 ticket.key).mpr (by rw [same.trans marked]; rfl))), retired,
    RetainsLowerFrames.trans keepsOpening
      (RetainsLowerFrames.trans (RetainsLowerFrames.mono keepsBody (Nat.le_succ _)) keepsClosing)⟩

/-- Follow the actual capture traversal, transferring the same receipt
at each skip or snapshot write. The terminal control contains the
packed batch and the original caller frame, not a separately built
summary of the answers. -/
theorem finish_owned_capture (environment : WorldEnvironment Context World) (policy : Policy) (label : Context)
    {S : Store World (Control Context) Continuation Result} {book : Book Context World}
    {world reachedWorld : World} {rows : List Result} {saved : List Value} {packed : Value}
    {activation : Frame} {stack : List Continuation} {emitted : List Result}
    {snapshots : SnapshotServices Context World} {ticket : Ticket (ReceiptId Context World)}
    {active : ReceiptId Context World}
    (provided : environment.services.snapshots = some snapshots)
    (capture : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.CaptureRowsRel
      snapshots label world rows saved packed reachedWorld)
    (represented : Represents S ⟨world, .work (.capture rows saved activation), stack, emitted⟩)
    (covered : book.Covers S.present)
    (atCapture : active.1 = .control (.work (.capture rows saved activation)) stack.length)
    (marked : book.mark active = some (.control ticket .capturing)) :
    ∃ (after : CustodyStore World (Control Context) Continuation Result Phase)
      (receiver : ReceiptId Context World),
      Relation.ReflTransGen (CustodyStep (machine environment policy label)) (S, book) after ∧
      Represents after.1 ⟨reachedWorld, .returning [(packed, activation)], stack, emitted⟩ ∧
      after.2.Covers after.1.present ∧
      receiver.1 = .control (.returning [(packed, activation)]) stack.length ∧
      after.2.mark receiver = some (.control ticket .completed) ∧
      RetainsLowerFrames stack.length (S, book) after := by
  induction capture generalizing S book active with
  | nil =>
    obtain ⟨exit, receiver, _, slot, stamp, finished, keeps⟩ := advance_control
      (M := machine environment policy label) (fun _ => .captureNil provided)
      represented covered marked atCapture (.control ticket .completed)
    exact ⟨(exit.result, exit.after), receiver, .single ⟨exit, rfl⟩, finished,
      exit.covered covered, slot, stamp, keeps⟩
  | empty missing _ ih =>
    obtain ⟨skip, next, _, slot, stamp, reached, keeps⟩ := advance_control
      (M := machine environment policy label) (fun _ => .captureEmpty provided missing)
      represented covered marked atCapture (.control ticket .capturing)
    obtain ⟨after, receiver, rest, finished, finalCover, finalSlot, finalStamp, keepsRest⟩ :=
      ih reached (skip.covered covered) slot stamp
    exact ⟨after, receiver, Relation.ReflTransGen.head ⟨skip, rfl⟩ rest, finished, finalCover,
      finalSlot, finalStamp, RetainsLowerFrames.trans keeps keepsRest⟩
  | cons present savedFrame _ ih =>
    obtain ⟨save, next, _, slot, stamp, reached, keeps⟩ := advance_control
      (M := machine environment policy label) (fun _ => .captureOne provided present savedFrame)
      represented covered marked atCapture (.control ticket .capturing)
    obtain ⟨after, receiver, rest, finished, finalCover, finalSlot, finalStamp, keepsRest⟩ :=
      ih reached (save.covered covered) slot stamp
    exact ⟨after, receiver, Relation.ReflTransGen.head ⟨save, rfl⟩ rest, finished, finalCover,
      finalSlot, finalStamp, RetainsLowerFrames.trans keeps keepsRest⟩

/-- A completed collapse with a real child effects path and capture
judgment has an occurrence-level return receipt. Its original frame ID
has been consumed and is not available for a second return. -/
theorem collector_completed_return (environment : WorldEnvironment Context World) (policy : Policy) (label : Context)
    {S : Store World (Control Context) Continuation Result} {book : Book Context World}
    {world childWorld reachedWorld : World} {live : List Atom} {scope : List String} {caller : Option Atom}
    {readiness : Status} {operand packed : Value} {activation : Frame} {stack : List Continuation}
    {rows emitted : List Result} {snapshots : SnapshotServices Context World}
    {parent : Option (ReceiptId Context World)}
    (provided : environment.services.snapshots = some snapshots)
    (body : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Stateful.MinimalRel
      environment label world live scope caller operand activation rows childWorld (policy := policy))
    (capture : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.CaptureRowsRel
      snapshots label childWorld rows [] packed reachedWorld)
    (represented : Represents S ⟨world,
      .work (.minimal live scope caller (.expression readiness [.symbol "collapse-bind", operand]) activation),
      stack, emitted⟩)
    (covered : book.Covers S.present) (enclosing : Enclosing book stack parent) :
    ∃ (after : CustodyStore World (Control Context) Continuation Result Phase)
      (ticket : Ticket (ReceiptId Context World)) (receiver : ReceiptId Context World),
      Relation.ReflTransGen (CustodyStep (machine environment policy label)) (S, book) after ∧
      Represents after.1 ⟨reachedWorld, .returning [(packed, activation)], stack, emitted⟩ ∧
      after.2.Covers after.1.present ∧
      receiver.1 = .control (.returning [(packed, activation)]) stack.length ∧
      after.2.mark receiver = some (.control ticket .completed) ∧
      ticket.parent = parent ∧ ticket.key ∈ after.2.issued ∧ ticket.key ∉ after.1.present ∧
      RetainsLowerFrames stack.length (S, book) after := by
  obtain ⟨between, ticket, current, collect, reached, currentCover, atCapture, stamp, bound, issued, retired, keepsChild⟩ :=
    collector_body_to_capture environment policy label provided body represented covered enclosing
  obtain ⟨after, receiver, completes, finished, finalCover, finalSlot, finalStamp, keepsCapture⟩ :=
    finish_owned_capture environment policy label provided capture reached currentCover atCapture stamp
  have noReissue := custody_path_no_reissue completes
  exact ⟨after, ticket, receiver, collect.trans completes, finished, finalCover, finalSlot, finalStamp,
    bound, noReissue.1 issued, noReissue.2 ticket.key issued retired,
    RetainsLowerFrames.trans keepsChild keepsCapture⟩

/-- The actual nested collapse returns its inner packed value to the
collector that was waiting at the enclosing cut. This works over an
arbitrary lower stack and leaves all those older physical frames and
marks alone. The two collector activations need not differ. -/
theorem nested_collector_completed_return (environment : WorldEnvironment Context World)
    (policy : Policy) (label : Context)
    {S : Store World (Control Context) Continuation Result} {book : Book Context World}
    {world bodyWorld innerWorld reachedWorld : World}
    {live : List Atom} {scope : List String} {caller : Option Atom}
    {innerStatus outerStatus : Status} {operand innerPacked outerPacked : Value}
    {activation : Frame} {stack : List Continuation} {rows emitted : List Result}
    {snapshots : SnapshotServices Context World} {enclosing : Option (ReceiptId Context World)}
    (provided : environment.services.snapshots = some snapshots)
    (body : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Stateful.MinimalRel
      environment label world live scope caller operand activation rows bodyWorld (policy := policy))
    (innerCapture : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.CaptureRowsRel
      snapshots label bodyWorld rows [] innerPacked innerWorld)
    (outerCapture : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.CaptureRowsRel
      snapshots label innerWorld [(innerPacked, activation)] [] outerPacked reachedWorld)
    (represented : Represents S ⟨world, .work (.minimal live scope caller
      (.expression outerStatus [.symbol "collapse-bind",
        .expression innerStatus [.symbol "collapse-bind", operand]]) activation), stack, emitted⟩)
    (covered : book.Covers S.present) (above : Enclosing book stack enclosing) :
    ∃ (ready : CustodyStore World (Control Context) Continuation Result Phase)
      (child parent : Ticket (ReceiptId Context World)) (reply : ReceiptId Context World),
      Relation.ReflTransGen (CustodyStep (machine environment policy label)) (S, book) ready ∧
      Represents ready.1 ⟨innerWorld, .returning [(innerPacked, activation)], .collect activation :: stack, emitted⟩ ∧
      parent.key.1 = .frame stack.length (.collect activation) ∧ parent.parent = enclosing ∧
      RetainsLowerFrames stack.length (S, book) ready ∧
      ∃ landing : CustodyFiring (machine environment policy label) ready.1 ready.2,
        admitsHandoff ready.2 landing.selected reply child parent ∧
        ∃ (last : CustodyStore World (Control Context) Continuation Result Phase)
          (receiver : ReceiptId Context World),
          Relation.ReflTransGen (CustodyStep (machine environment policy label)) (landing.result, landing.after) last ∧
          Represents last.1 ⟨reachedWorld, .returning [(outerPacked, activation)], stack, emitted⟩ ∧
          last.2.Covers last.1.present ∧ last.2.mark receiver = some (.control parent .completed) ∧
          child.key ∉ last.1.present ∧ parent.key ∉ last.1.present ∧ reply ∉ last.1.present ∧
          RetainsLowerFrames stack.length (S, book) last := by
  let M := machine environment policy label
  obtain ⟨opening, owner, _, outer, _, _, outerSlot, waiting, innerEntry, keepsOpening, _⟩ :=
    open_collector environment policy label provided represented covered above
  let parent : Ticket (ReceiptId Context World) := ⟨outer, owner, enclosing⟩
  have openCover := opening.covered covered
  have entry : Enclosing opening.after (.collect activation :: stack) (some outer) :=
    .owned (parent := parent) waiting outerSlot
  obtain ⟨ready, child, reply, paidInner, readyRep, readyCover, replySlot, stamp,
      link, childIssued, childRetired, keepsInner⟩ :=
    collector_completed_return environment policy label provided body innerCapture innerEntry openCover entry
  have outerLive : outer ∈ opening.result.present := (openCover.2 _).mpr (by rw [waiting]; rfl)
  obtain ⟨parentLive, same⟩ := keepsInner outerLive outerSlot (Nat.lt_succ_self _)
  obtain ⟨landing, capture, licensed, captureSlot, newStamp, replyGone, parentGone, atCapture, keepsLanding⟩ :=
    handoff_to_parent environment policy label (child := child) (parent := parent)
      provided readyRep readyCover stamp
      (by simpa only [List.length_cons, Nat.add_comm stack.length 1] using replySlot) link
      (same.trans waiting) outerSlot
  obtain ⟨last, receiver, tail, reached, lastCover, _, completed, keepsFinish⟩ :=
    finish_owned_capture environment policy label provided outerCapture atCapture
      (landing.covered readyCover) captureSlot newStamp
  have opened : CustodyStep M (S, book) (opening.result, opening.after) := ⟨opening, rfl⟩
  have delivered : CustodyStep M ready (landing.result, landing.after) := ⟨landing, rfl⟩
  have through := Relation.ReflTransGen.head delivered tail
  have stillRetired := (custody_path_no_reissue through).2 child.key childIssued childRetired
  have noReissue := custody_path_no_reissue tail
  have spent (occ : ReceiptId Context World) (live : occ ∈ ready.1.present)
      (notMem : occ ∉ landing.result.present) : occ ∉ last.1.present :=
    noReissue.2 occ (Ledger.issued_mono _ _ _ _ (readyCover.1 live)) notMem
  have replyLive : reply ∈ ready.1.present := (readyCover.2 _).mpr (by rw [stamp]; rfl)
  have keptReady : RetainsLowerFrames stack.length (S, book) ready :=
    RetainsLowerFrames.trans keepsOpening
    (RetainsLowerFrames.mono keepsInner (Nat.le_succ _))
  exact ⟨ready, child, parent, reply, Relation.ReflTransGen.head opened paidInner, readyRep, outerSlot, rfl,
    keptReady, landing, licensed, last, receiver, tail, reached, lastCover, completed,
    stillRetired, spent parent.key parentLive parentGone, spent reply replyLive replyGone,
    RetainsLowerFrames.trans keptReady (RetainsLowerFrames.trans keepsLanding keepsFinish)⟩

/-- The unrestricted framed rule family admits padding the collapse
footprint with a preserved older frame. The resulting encoded source
stack is correct, but the old collector occurrence is gone. This is why
the raw bisimulation alone is not a physical custody theorem. -/
theorem raw_padded_open_can_replace_collector (environment : WorldEnvironment Context World)
    (policy : Policy) (label : Context)
    {S : Store World (Control Context) Continuation Result}
    {world : World} {live : List Atom} {scope : List String} {caller : Option Atom}
    {readiness : Status} {operand : Value} {activation : Frame} {emitted : List Result}
    {snapshots : SnapshotServices Context World} {old : ReceiptId Context World}
    (provided : environment.services.snapshots = some snapshots)
    (represented : Represents S ⟨world,
      .work (.minimal live scope caller (.expression readiness [.symbol "collapse-bind", operand]) activation),
      [.collect activation], emitted⟩)
    (present : old ∈ S.present) (atFrame : old.1 = .frame 0 (.collect activation)) :
    ∃ reached, StoreStep (machine environment policy label) S reached ∧ old ∉ reached.present ∧
      Represents reached ⟨world, .work (.minimal live scope caller operand activation),
        [.collect activation, .collect activation], emitted⟩ := by
  let current : Control Context :=
    .work (.minimal live scope caller (.expression readiness [.symbol "collapse-bind", operand]) activation)
  let next : Control Context := .work (.minimal live scope caller operand activation)
  let outer := Continuation.collect activation
  let rule := readingRule (A := Result) world current [outer] next [outer, outer] 0
  obtain ⟨selected, valid, _, reaches⟩ :=
    reading_allocated (S := S) (c := current) (c' := next) (pop := [outer]) (push := [outer, outer])
      (base := []) S.present (fun _ member => member) represented
  have listed : Cell.frame 0 outer ∈ selected.taken.map Prod.fst := by
    rw [taken_labels valid]
    simp [readingRule, popCells]
  obtain ⟨chosen, taken, atChosen⟩ := List.mem_map.mp listed
  have inBefore := valid.occurrences.taken_subset (List.mem_toFinset.mpr taken)
  have same : chosen = old := same_frame_occurrence represented inBefore present atChosen atFrame
  subst chosen
  refine ⟨selected.result Prod.fst rule S, ⟨rule, .reading 0 (fun _ => .collapseEnter provided),
    selected, valid, rfl⟩, ?_, reaches⟩
  intro existsAfter
  rcases MeTTaCalculus.OccurrenceCommits.mem_fire.mp existsAfter with ⟨_, remained⟩ | produced
  · exact remained (List.mem_toFinset.mpr taken)
  · exact Finset.disjoint_left.mp valid.occurrences.fresh produced present

end CollectorCustody

/-! ## Controls -/

namespace HEControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- **Positive control: an HE transition is a firing.** Pending work on the empty tuple returns the
empty expression under its activation; from every store representing that configuration the step
fires to a store representing the result. -/
theorem he_fires_example (space : Space) (live : List Atom) (scope : List String)
    (activation : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Frame) (emitted : List Result)
    {S : Store Space Control Continuation Result}
    (represented : Represents S (toConfig ⟨space, .work (.tuple live scope [] activation), [], emitted⟩)) :
    ∃ S', StoreStep (heMachine dispatch lookup policy) S S' ∧
      Represents S' (toConfig ⟨space, .returning [(.expression .active [], activation)], [], emitted⟩) := by
  have step : HEReadStep dispatch lookup policy ⟨space, .work (.tuple live scope [] activation), [], emitted⟩
      ⟨space, .returning [(.expression .active [], activation)], [], emitted⟩ := .internal .tupleNil
  exact machine_to_store he_local represented ((he_step_iff _ _).mp step)

/-- **Negative control: a completed HE phase is stuck on the step.** When HE observes the answers of
a configuration (the returning batch is empty and no continuation is left), no firing of HE's rules
applies to a store representing it. -/
theorem he_completed_stuck (space : Space) (answers : List Result)
    {S : Store Space Control Continuation Result}
    (represented : Represents S (toConfig ⟨space, .returning [], [], answers⟩)) :
    ∀ S', ¬ StoreStep (heMachine dispatch lookup policy) S S' := by
  rw [stuck_iff he_local represented]
  intro x' step
  obtain ⟨sp, c, s, e⟩ := x'
  have here := (he_step_iff ⟨space, .returning [], [], answers⟩ ⟨sp, c, s, e⟩).mpr step
  exact Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual.observed_final
    (state := ⟨space, .returning [], [], answers⟩) rfl ⟨_, here⟩

/-- **Positive control for effects: a native call that changes the world is a writing rule.** It
takes the world occurrence and makes the new world, with no frame popped or pushed. -/
theorem he_native_is_write {Context World : Type} {view : World → Context → Space}
    {services : WorldServices Context World} (label : Context) {w w' : World}
    {live : List Atom} {scope : List String} {caller : Option Atom}
    {readiness : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Entry.Status}
    {name function arguments : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Entry.Value}
    {activation : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Frame} {results : List Result}
    (call : services.nativeCall label w name.erase function.erase arguments.erase activation results w')
    (changed : w' ≠ w) (b : ℕ) :
    Rules (heWorldMachine view services dispatch lookup policy label)
      (writingRule w (.work (.minimal live scope caller
        (.expression readiness [.symbol "call-native", name, function, arguments]) activation)) []
        w' (.returning results) [] b) ∧
      Cell.world w ∈ (writingRule (C := Control Context) (A := Result) w (.work (.minimal live scope caller
        (.expression readiness [.symbol "call-native", name, function, arguments]) activation)) []
        w' (.returning results) ([] : List Continuation) b).take :=
  ⟨.writing b changed fun _ => WorldLocalStepWith.native call, by simp [writingRule]⟩

/-- **Negative control for effects: the read-only machine never writes.** No writing rule belongs
to HE's read-only machine. -/
theorem he_read_only_no_write (space space' : Space) (c c' : Control) (pop push : List Continuation)
    (b : ℕ) : ¬ Rules (heMachine dispatch lookup policy) (writingRule (A := Result) space c pop space' c' push b) := by
  intro member
  generalize named : writingRule (A := Result) space c pop space' c' push b = rule at member
  cases member with
  | reading _ _ =>
      have heads := congrArg (fun rule : RuleInstance (Cell Space Control Continuation Result) =>
        rule.take.head?) named
      simp [writingRule, readingRule] at heads
  | writing _ changed framed => exact changed (framed []).1
  | publish _ =>
      have heads := congrArg (fun rule : RuleInstance (Cell Space Control Continuation Result) =>
        rule.take.head?) named
      simp [writingRule, publishRule] at heads

end HEControls

#print axioms localStep_framed
#print axioms worldLocalStep_framed
#print axioms he_step_iff
#print axioms he_local
#print axioms he_on_the_step
#print axioms he_outcomes_eq
#print axioms he_completed_answers
#print axioms he_nonZeno
#print axioms he_divergence_iff
#print axioms he_world_step_iff
#print axioms he_world_local
#print axioms he_world_on_the_step
#print axioms he_world_outcomes_eq
#print axioms he_world_divergence_iff
#print axioms he_world_target_prefix
#print axioms he_world_source_prefix
#print axioms he_world_completed_source_iff
#print axioms he_file_report_has_store
#print axioms he_file_store_can_report
#print axioms he_file_error_from_terminal_bag
#print axioms HEControls.he_fires_example
#print axioms HEControls.he_completed_stuck
#print axioms HEControls.he_native_is_write
#print axioms HEControls.he_read_only_no_write

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.HEOnTheStep
