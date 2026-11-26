import Mettapedia.Languages.MeTTa.HE.RecursiveMachine
import Mettapedia.GSLT.Core.GSLT

/-!
# HE's theory at a fixed space

Specializing to a space removes its atoms from the changing term, not
from the premises that use them. Local work still uses HE's type demand,
matching, bindings, and grounded dispatch. The second kind of rewrite
publishes an answer. This is the fixed-space fibre of HE's contextual
source relation; an execution that changes worlds is not in that fibre.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HEExecution

open Mettapedia.Languages.MeTTa.HE (Space)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval (GroundedDispatch)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed
  (ArgumentService CastLookup Policy Result WorldServices)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual
  (Control Continuation Configuration WorldConfiguration)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual
  (LocalStep Step Steps observe WorldLocalStepWith WorldStepWith)
open Mettapedia.GSLT (GSLT)

structure Phase where
  control : Control
  stack : List Continuation
  emitted : List Result

def Phase.inSpace (space : Space) (p : Phase) : Configuration :=
  ⟨space, p.control, p.stack, p.emitted⟩

def phaseOf (configuration : Configuration) : Phase :=
  ⟨configuration.control, configuration.stack, configuration.emitted⟩

@[simp] theorem space_inSpace (space : Space) (p : Phase) : (p.inSpace space).space = space :=
  rfl

@[simp] theorem phaseOf_inSpace (space : Space) (p : Phase) : phaseOf (p.inSpace space) = p := by
  cases p
  rfl

inductive Rewrites (space : Space) (dispatch : GroundedDispatch) (lookup : CastLookup)
    (policy : Policy) : Phase → Phase → Prop where
  | evaluate {source target : Control} {stack remaining : List Continuation} {answers : List Result} :
      LocalStep space dispatch lookup policy (source, stack) (target, remaining) →
      Rewrites space dispatch lookup policy ⟨source, stack, answers⟩ ⟨target, remaining, answers⟩
  | emit {first : Result} {tail answers : List Result} :
      Rewrites space dispatch lookup policy
        ⟨.returning (first :: tail), [], answers⟩ ⟨.returning tail, [], answers ++ [first]⟩

def theoryAt (space : Space) (dispatch : GroundedDispatch) (lookup : CastLookup) (policy : Policy) :
    GSLT where
  Term := Phase
  equations := ⟨Eq, Eq.refl, Eq.symm, Eq.trans⟩
  rewrites := Rewrites space dispatch lookup policy
  rewrites_resp_left := by rintro x _ y rfl edge; exact ⟨y, edge, rfl⟩
  rewrites_resp_right := by rintro x y _ edge rfl; exact edge

theorem source_space_preserved {dispatch : GroundedDispatch} {lookup : CastLookup} {policy : Policy}
    {before after : Configuration} (step : Step dispatch lookup policy before after) :
    before.space = after.space := by
  cases step <;> rfl

private theorem forget_step {dispatch : GroundedDispatch} {lookup : CastLookup} {policy : Policy}
    {before after : Configuration} (step : Step dispatch lookup policy before after) :
    (theoryAt before.space dispatch lookup policy).Step (phaseOf before) (phaseOf after) := by
  cases step with
  | internal advance => exact Rewrites.evaluate advance
  | publish => exact Rewrites.emit

/-- Every source step in the fibre is one rewrite, and no rewrites are
introduced by specializing to a space. A held atom's status and a
pending continuation are both still part of the term. -/
theorem rewrite_iff (space : Space) (dispatch : GroundedDispatch) (lookup : CastLookup)
    (policy : Policy) (before after : Phase) :
    (theoryAt space dispatch lookup policy).Step before after ↔
      Step dispatch lookup policy (before.inSpace space) (after.inSpace space) := by
  constructor
  · intro rewrite
    change Rewrites _ _ _ _ _ _ at rewrite
    cases rewrite with
    | evaluate localStep => exact .internal localStep
    | emit => exact .publish
  · intro source
    simpa using forget_step source

private theorem snoc (system : GSLT) :
    {x y z : system.Term} → system.MultiStep x y → system.Step y z → system.MultiStep x z
  | _, _, z, .refl _, step => .step step (.refl z)
  | _, _, _, .step first rest, step => .step first (snoc system rest step)

theorem finite_execution_iff (space : Space) (dispatch : GroundedDispatch) (lookup : CastLookup)
    (policy : Policy) (before after : Phase) :
    (theoryAt space dispatch lookup policy).MultiStep before after ↔
      Steps dispatch lookup policy (before.inSpace space) (after.inSpace space) := by
  constructor
  · exact embedPath space dispatch lookup policy
  · intro path
    have preserved : (before.inSpace space).space = space := rfl
    simpa using projectPath space dispatch lookup policy path preserved
where
  embedPath (s : Space) (d : GroundedDispatch) (l : CastLookup) (p : Policy) :
      {x y : Phase} → (theoryAt s d l p).MultiStep x y →
      Steps d l p (x.inSpace s) (y.inSpace s)
    | _, _, .refl _ => .refl
    | _, _, .step edge rest =>
      (Relation.ReflTransGen.single ((rewrite_iff s d l p _ _).mp edge)).trans
        (embedPath s d l p rest)
  projectPath (s : Space) (d : GroundedDispatch) (l : CastLookup) (p : Policy)
      {x y : Configuration} (path : Steps d l p x y) (initial : x.space = s) :
      (theoryAt s d l p).MultiStep (phaseOf x) (phaseOf y) := by
    induction path with
    | refl => exact .refl _
    | @tail middle next _ edge earlier =>
      have same : s = middle.space := by
        suffices h : ∀ {a b : Configuration}, Steps d l p a b → a.space = b.space from
          initial.symm.trans (h ‹Steps d l p x middle›)
        intro a b steps
        induction steps with
        | refl => rfl
        | tail _ last ih => exact ih.trans (source_space_preserved last)
      have newest := forget_step edge
      rw [← same] at newest
      exact snoc _ earlier newest

/-- A queued answer is not yet an observation. The only change in this
rewrite is semantic publication of that answer, with multiplicity intact. -/
theorem publication_changes_observation (space : Space) (dispatch : GroundedDispatch)
    (lookup : CastLookup) (policy : Policy) (first : Result) (prefixAnswers : List Result) :
    let pending : Phase := ⟨.returning [first], [], prefixAnswers⟩
    let complete : Phase := ⟨.returning [], [], prefixAnswers ++ [first]⟩
    observe (pending.inSpace space) = none ∧ (theoryAt space dispatch lookup policy).Step pending complete ∧
      observe (complete.inSpace space) = some (prefixAnswers ++ [first]) :=
  ⟨rfl, Rewrites.emit, rfl⟩

section Live

variable {Context World : Type} {first second : World → Context → Space}
  {services : WorldServices Context World} {dispatch : GroundedDispatch}
  {lookup : CastLookup} {policy : Policy} {admission : ArgumentService}

/-- A local HE step only uses the effective spaces of the initial
context and its retained child contexts. Native and grounded effects still
use their actual world, including any updates they perform. -/
theorem local_rewrite_of_same_snapshot
    {initial final : World} {ctx : Context}
    {source target : Control Context × List Continuation}
    (step : WorldLocalStepWith admission first services dispatch lookup policy initial ctx source final target)
    (same : ∀ name ∈ ctx :: source.1.contexts, first initial name = second initial name) :
    WorldLocalStepWith admission second services dispatch lookup policy initial ctx source final target := by
  induction step with
  | core incoming ordinary localStep outgoing =>
    exact .core incoming ordinary (by simpa only [same _ List.mem_cons_self] using localStep) outgoing
  | context child ih =>
    apply WorldLocalStepWith.context
    apply ih
    intro name within
    exact same name (List.mem_cons_of_mem _ within)
  | contextReturn => exact .contextReturn
  | evalc => exact .evalc
  | metta => exact .metta
  | contextSpace => exact .contextSpace
  | native called => exact .native called
  | callGroundedDone shape executable notError ran returned =>
    exact .callGroundedDone shape executable notError ran returned
  | callGroundedResume shape executable notError ran returned =>
    exact .callGroundedResume shape executable notError ran returned
  | invocationGroundedDone shape executable ran returned =>
    exact .invocationGroundedDone shape executable ran returned
  | invocationGroundedResume shape executable ran returned =>
    exact .invocationGroundedResume shape executable ran returned
  | collapseEnter provided => exact .collapseEnter provided
  | collectEnter provided => exact .collectEnter provided
  | captureNil provided => exact .captureNil provided
  | captureEmpty provided empty => exact .captureEmpty provided empty
  | captureOne provided notEmpty captured => exact .captureOne provided notEmpty captured
  | superposeEnter provided => exact .superposeEnter provided
  | restoreNil provided => exact .restoreNil provided
  | restoreOne provided restored merged => exact .restoreOne provided restored merged
  | restoreRejected provided restored incompatible => exact .restoreRejected provided restored incompatible

theorem world_rewrite_iff_of_same_snapshot {source target : WorldConfiguration Context World}
    (same : ∀ name ∈ source.context :: source.control.contexts,
      first source.world name = second source.world name) :
    WorldStepWith admission first services dispatch lookup policy source target ↔
      WorldStepWith admission second services dispatch lookup policy source target := by
  have one :
      ∀ (a b : World → Context → Space),
        (∀ name ∈ source.context :: source.control.contexts, a source.world name = b source.world name) →
        WorldStepWith admission a services dispatch lookup policy source target →
        WorldStepWith admission b services dispatch lookup policy source target := by
    intro a b agrees step
    cases step with
    | internal localStep =>
      exact .internal (local_rewrite_of_same_snapshot localStep agrees)
    | publish => exact .publish
  exact ⟨one first second same, one second first (fun name member => (same name member).symm)⟩

/-- Pin the definition view for this step alone. The original transition
may change the world; the next step takes its own snapshot. -/
theorem live_world_step_at_snapshot (view : World → Context → Space)
    (source target : WorldConfiguration Context World) :
    WorldStepWith admission view services dispatch lookup policy source target ↔
      WorldStepWith admission (fun _ => view source.world) services dispatch lookup policy source target :=
  world_rewrite_iff_of_same_snapshot (fun _ _ => rfl)

end Live

end Mettapedia.Languages.MeTTa.SpaceTheory.HEExecution
