import Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintRefusal
import Mettapedia.Languages.MeTTa.PeTTa.OutputPlanGate

/-!
# The actual result gate and destination-source constraint admission

Successful unification preserves exactly the source equation's models.
The source retains its equation record while the target retains its solved
substitution. A local source step and the actual four-transition target gate
share that model relation and retain their reached worlds and continuations.
This does not yet prove simulation of all producer/control transitions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.OutputPlan.ConstraintAdmission

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open EagerDFS
open UnifyingConstraintPresentation

def Represents (constraints : Destination.Equations) (bindings : Subst) : Prop :=
  ∀ model, Destination.Solves model constraints ↔ Destination.Solves model (presentation bindings)

theorem solves_append_one (model : Destination.Environment) (before : Destination.Equations) (left right : Atom) :
    Destination.Solves model (before ++ [(left,right)]) ↔
      Destination.Solves model before ∧ Destination.read model left = Destination.read model right := by
  constructor
  · intro solved
    exact ⟨fun pair present => solved pair (List.mem_append_left _ present),
      solved (left,right) (List.mem_append_right _ (List.mem_singleton_self _))⟩
  · rintro ⟨old,equal⟩ pair present
    rcases List.mem_append.mp present with earlier | current
    · exact old pair earlier
    · have same := List.mem_singleton.mp current
      subst pair
      exact equal

theorem gate_models_iff (bindings bound : Subst) (left right : Atom)
    (valid : Unifying.Idempotent bindings)
    (unified : Unifying.unify bindings left (Unifying.resolve bindings right) = .ok bound)
    (model : Destination.Environment) :
    Destination.Solves model (presentation bound) ↔
      Destination.Solves model (presentation bindings) ∧ Destination.read model left = Destination.read model right := by
  have exactModels := successful_models_iff _ bindings bound left (Unifying.resolve bindings right) valid unified model
  constructor
  · intro current
    obtain ⟨old,equal⟩ := exactModels.mp current
    exact ⟨old,equal.trans (absorbs_of_solves model bindings old right)⟩
  · rintro ⟨old,equal⟩
    exact exactModels.mpr ⟨old,equal.trans (absorbs_of_solves model bindings old right).symm⟩

theorem represents_after_gate (before : Destination.Equations) (bindings bound : Subst) (left right : Atom)
    (represented : Represents before bindings) (valid : Unifying.Idempotent bindings)
    (unified : Unifying.unify bindings left (Unifying.resolve bindings right) = .ok bound) :
    Represents (before ++ [(left,right)]) bound := by
  intro model
  rw [solves_append_one,gate_models_iff bindings bound left right valid unified model]
  exact and_congr (represented model) Iff.rfl

theorem gate_has_source_refinement (before : Destination.Equations) (bindings bound : Subst) (left right : Atom)
    (represented : Represents before bindings) (valid : Unifying.Idempotent bindings)
    (unified : Unifying.unify bindings left (Unifying.resolve bindings right) = .ok bound) :
    Destination.Refinement before left right (some (before ++ [(left,right)])) := by
  have boundValid := (Unifying.unifyTerms_sound _ bindings bound left (Unifying.resolve bindings right) valid unified).1
  have current := environment_models_presentation bound boundValid
  obtain ⟨old,equal⟩ := (gate_models_iff bindings bound left right valid unified (environment bound)).mp current
  exact .accepted (environment bound) ((represented _).mpr old) equal

theorem actual_source_refine (before : Destination.Equations) (bindings bound : Subst) (left right : Atom)
    (represented : Represents before bindings) (valid : Unifying.Idempotent bindings)
    (unified : Unifying.unify bindings left (Unifying.resolve bindings right) = .ok bound) :
    Destination.refine before left right = some (before ++ [(left,right)]) :=
  (Destination.refinement_iff _ _ _ _).mp
    (gate_has_source_refinement before bindings bound left right represented valid unified)

theorem source_gate_step {Context : Type} (policy : Destination.Policy) (program : SpaceSemantics.Program)
    (cursor : Destination.Cursor Context) (bindings bound : Subst) (left right : Atom) (older : List Destination.Goal)
    (represented : Represents cursor.control.bindings bindings)
    (atGoal : cursor.control.goals = .equate left right :: older)
    (valid : Unifying.Idempotent bindings)
    (unified : Unifying.unify bindings left (Unifying.resolve bindings right) = .ok bound) :
    Destination.Source.Step policy program cursor
      (.silent {cursor with control := {cursor.control with
        bindings := cursor.control.bindings ++ [(left,right)],goals := older}}) :=
  .accepted left right older _ atGoal
    (gate_has_source_refinement cursor.control.bindings bindings bound left right represented valid unified)

theorem successful_gate_square {Context : Type} (policy : Destination.Policy) (program : SpaceSemantics.Program)
    (cursor : Destination.Cursor Context) (base : Streaming.State)
    (bindings bound : Subst) (left right continuation : Atom)
    (olderGoals : List Destination.Goal) (caller : List Streaming.Frame) (olderJobs : List Streaming.Job)
    (represented : Represents cursor.control.bindings bindings)
    (atGoal : cursor.control.goals = .equate left right :: olderGoals)
    (valid : Unifying.Idempotent bindings)
    (unified : Unifying.unify bindings left (Unifying.resolve bindings right) = .ok bound) :
    Destination.Source.Step policy program cursor
        (.silent {cursor with control := {cursor.control with
          bindings := cursor.control.bindings ++ [(left,right)],goals := olderGoals}}) ∧
      Represents (cursor.control.bindings ++ [(left,right)]) bound ∧
      Streaming.advance program 4 (focused base bindings (equate left right continuation) caller olderJobs) =
        focused base bound continuation caller olderJobs :=
  ⟨source_gate_step policy program cursor bindings bound left right olderGoals represented atGoal valid unified,
   represents_after_gate cursor.control.bindings bindings bound left right represented valid unified,
   gate_success program base bindings bound left right continuation caller olderJobs unified⟩

theorem clashed_gate_has_source_refusal (before : Destination.Equations) (bindings : Subst) (left right : Atom)
    (represented : Represents before bindings) (valid : Unifying.Idempotent bindings)
    (clashed : Unifying.unify bindings left (Unifying.resolve bindings right) = .clash) :
    Destination.Refinement before left right none := by
  apply Destination.Refinement.refused
  rintro ⟨model,sourceModel,equal⟩
  have old := (represented model).mp sourceModel
  have actualEqual := equal.trans (absorbs_of_solves model bindings old right).symm
  exact unifyTerms_refutes_model _ bindings left (Unifying.resolve bindings right) valid clashed model old actualEqual

theorem actual_source_refusal (before : Destination.Equations) (bindings : Subst) (left right : Atom)
    (represented : Represents before bindings) (valid : Unifying.Idempotent bindings)
    (clashed : Unifying.unify bindings left (Unifying.resolve bindings right) = .clash) :
    Destination.refine before left right = none :=
  (Destination.refinement_iff _ _ _ _).mp
    (clashed_gate_has_source_refusal before bindings left right represented valid clashed)

theorem refused_gate_square {Context : Type} (policy : Destination.Policy) (program : SpaceSemantics.Program)
    (cursor : Destination.Cursor Context) (base : Streaming.State)
    (bindings : Subst) (left right continuation : Atom)
    (olderGoals : List Destination.Goal) (caller : List Streaming.Frame) (olderJobs : List Streaming.Job)
    (represented : Represents cursor.control.bindings bindings)
    (atGoal : cursor.control.goals = .equate left right :: olderGoals)
    (valid : Unifying.Idempotent bindings)
    (clashed : Unifying.unify bindings left (Unifying.resolve bindings right) = .clash) :
    Destination.Source.Step policy program cursor (.finish (.noValue cursor.control.bindings,cursor)) ∧
      Streaming.advance program 4 (focused base bindings (equate left right continuation) caller olderJobs) =
        {base with agenda := olderJobs} :=
  ⟨.refused left right olderGoals atGoal
      (clashed_gate_has_source_refusal cursor.control.bindings bindings left right represented valid clashed),
   gate_refusal program base bindings left right continuation caller olderJobs clashed⟩

/-- The target retains extra allocation/private-code fields as well. This
projection relates exactly the three fields observed by this source world. -/
def sourceWorld (world : Streaming.World) : EagerDFS.World := ⟨world.state,world.input,world.output⟩

theorem successful_gate_retains_worlds {Context : Type} (program : SpaceSemantics.Program)
    (cursor : Destination.Cursor Context) (base : Streaming.State)
    (bindings bound : Subst) (left right continuation : Atom)
    (caller : List Streaming.Frame) (olderJobs : List Streaming.Job)
    (worlds : cursor.world = sourceWorld base.world)
    (unified : Unifying.unify bindings left (Unifying.resolve bindings right) = .ok bound) :
    cursor.world = sourceWorld
      (Streaming.advance program 4 (focused base bindings (equate left right continuation) caller olderJobs)).world := by
  rw [gate_success program base bindings bound left right continuation caller olderJobs unified]
  exact worlds

theorem refused_gate_retains_worlds {Context : Type} (program : SpaceSemantics.Program)
    (cursor : Destination.Cursor Context) (base : Streaming.State)
    (bindings : Subst) (left right continuation : Atom)
    (caller : List Streaming.Frame) (olderJobs : List Streaming.Job)
    (worlds : cursor.world = sourceWorld base.world)
    (clashed : Unifying.unify bindings left (Unifying.resolve bindings right) = .clash) :
    cursor.world = sourceWorld
      (Streaming.advance program 4 (focused base bindings (equate left right continuation) caller olderJobs)).world := by
  rw [gate_refusal program base bindings left right continuation caller olderJobs clashed]
  exact worlds

theorem interrupted_gate_keeps_work (program : SpaceSemantics.Program) (base : Streaming.State)
    (bindings : Subst) (left right continuation : Atom) (caller : List Streaming.Frame)
    (olderJobs : List Streaming.Job)
    (unserved : Unifying.unify bindings left (Unifying.resolve bindings right) = .exhausted) :
    (Streaming.advance program 4 (focused base bindings (equate left right continuation) caller olderJobs)).world = base.world ∧
      (Streaming.advance program 4 (focused base bindings (equate left right continuation) caller olderJobs)).agenda ≠ [] := by
  rw [gate_interruption program base bindings left right continuation caller olderJobs unserved]
  exact ⟨rfl,List.cons_ne_nil _ _⟩

end Mettapedia.Languages.MeTTa.PeTTa.OutputPlan.ConstraintAdmission
