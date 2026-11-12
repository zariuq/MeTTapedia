import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.HEOnTheStep.FramedMachines
import Mettapedia.Languages.MeTTa.HE.RecursiveMachine

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
  of the stack. All 81 transition rules of the read-only machine and all 20 of the world machine are
  covered.
* `he_step_iff`, `he_world_step_iff`: HE's machines are framed machines (`heMachine`,
  `heWorldMachine`), configuration by configuration.
* `he_on_the_step`, `he_world_on_the_step`: **HE is a fragment of the step.** Placed on the store
  (one occurrence for the world, one for the pending work with the stack's depth, one per
  continuation frame, one per published answer), HE's transitions are exactly the firings of their
  rules, one firing per HE step, as a strong bisimulation through representation.
* Readouts: the possible outcomes (answer bag, world reached) agree (`he_outcomes_eq`,
  `he_world_outcomes_eq`); a completed HE phase (`observe`) is read off the store as its answer bag
  (`he_completed_answers`).
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
  WorldLocalStepWith WorldLocalStep WorldStep observe observe_eq_some)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation WorldConfiguration
  UnscopedControl managedContextControl)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval (GroundedDispatch)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result WorldServices ArgumentService
  CastLookup)
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
    (dispatch : GroundedDispatch) (lookup : CastLookup) (policy : Policy) (label : Context) :
    FramedMachine World (Control Context) Continuation Result where
  transition w before w' after := WorldLocalStep view services dispatch lookup policy w label before w' after
  publish := hePublish

/-- HE's world configurations at a context, as framed configurations. -/
def toWorldConfig (x : WorldConfiguration Context World) :
    Config World (Control Context) Continuation Result :=
  ⟨x.world, x.control, x.stack, x.emitted⟩

/-- **HE's world machine is the framed machine**, step for step; the context never changes. -/
theorem he_world_step_iff (x y : WorldConfiguration Context World) :
    WorldStep view services dispatch lookup policy x y ↔
      y.context = x.context ∧
        (heWorldMachine view services dispatch lookup policy x.context).Step (toWorldConfig x)
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

/-- **Locality of HE's world machine.** -/
theorem he_world_local (label : Context) :
    (heWorldMachine view services dispatch lookup policy label).Local := by
  intro w w' c c' s s' transition
  exact worldLocalStep_framed transition

/-- **HE with a shared world on the step.** A transition that keeps the world reads its occurrence;
one that changes it (a native call, a grounded operation with an effect, a captured snapshot) takes
it and makes the new world. -/
theorem he_world_on_the_step (label : Context) :
    IsBisimulation (StoreStep (heWorldMachine view services dispatch lookup policy label))
      (heWorldMachine view services dispatch lookup policy label).Step Represents :=
  bisimulation (he_world_local label)

/-- **The world observations agree**: the possible outcomes on the step (answer bag, world reached)
are those of HE's world machine. -/
theorem he_world_outcomes_eq (label : Context)
    {S : Store World (Control Context) Continuation Result}
    {x : Config World (Control Context) Continuation Result} (represented : Represents S x) :
    storeOutcomes (heWorldMachine view services dispatch lookup policy label) S =
      machineOutcomes (heWorldMachine view services dispatch lookup policy label) x :=
  outcomes_eq (he_world_local label) represented

/-- **No added and no lost divergence for HE with a world.** -/
theorem he_world_divergence_iff (label : Context)
    {S : Store World (Control Context) Continuation Result}
    {x : Config World (Control Context) Continuation Result} (represented : Represents S x) :
    (∃ Ss : ℕ → Store World (Control Context) Continuation Result, Ss 0 = S ∧
        ∀ n, StoreStep (heWorldMachine view services dispatch lookup policy label) (Ss n) (Ss (n + 1))) ↔
      ∃ xs : ℕ → Config World (Control Context) Continuation Result, xs 0 = x ∧
        ∀ n, (heWorldMachine view services dispatch lookup policy label).Step (xs n) (xs (n + 1)) :=
  divergence_iff (he_world_local label) represented

end World

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
#print axioms HEControls.he_fires_example
#print axioms HEControls.he_completed_stuck
#print axioms HEControls.he_native_is_write
#print axioms HEControls.he_read_only_no_write

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.HEOnTheStep
