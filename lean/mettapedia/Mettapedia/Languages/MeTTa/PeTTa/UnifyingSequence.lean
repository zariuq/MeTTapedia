import Mettapedia.Languages.MeTTa.PeTTa.UnifyingRetainedFrames
import Mettapedia.Machines.OrderedProtocol

/-!
# Ordered completed controls in the actual source machine

Each child is justified by its own source path and returns its own binding
packets. The next child starts in the world actually reached by the previous
one. These laws do not assume termination of arbitrary source computations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Unifying

open Mettapedia.Machines.OrderedProtocol.Completion (OrderedStateFlatMapRel)

def CompletedControl (registry : SpaceSemantics.Program) (control : Control)
    (before : Configuration) (answers : List Answer) (after : Configuration) : Prop :=
  Relation.ReflTransGen (Transition registry)
    {before with control,frames := []}
    {after with control := .returned answers,frames := []}

/-- Every actual finite path supplies an administrative allowance after which
the existing runner continues from its full endpoint. No terminal or
terminating continuation is assumed. -/
theorem steps_run_suffix {registry : SpaceSemantics.Program} {before after : Configuration}
    (path : Relation.ReflTransGen (Transition registry) before after) :
    ∃ spent, ∀ remaining, run registry (spent + remaining) before = run registry remaining after := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0,fun _ => by simp only [Nat.zero_add]⟩
  | @head first middle taken tail ih =>
      obtain ⟨spent,continues⟩ := ih
      refine ⟨spent + 1,?_⟩
      intro remaining
      have firstStep := run_succ_of_step registry (spent + remaining) first middle
        (transition_step taken)
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        firstStep.trans (continues remaining)

theorem ordered_controls_steps {registry : SpaceSemantics.Program}
    {controls : List Control} {before after : Configuration} {answers : List Answer}
    (ordered : OrderedStateFlatMapRel (CompletedControl registry) controls before answers after) :
    ∀ frames collected,
    Relation.ReflTransGen (Transition registry)
      {before with control := .sequence controls collected,frames}
      {after with control := .returned (collected ++ answers),frames} := by
  induction ordered with
  | nil initial =>
      intro frames collected
      simpa only [List.append_nil] using
        Relation.ReflTransGen.single (Transition.sequence_done
          (registry := registry)
          (source := {initial with control := .sequence [] collected,frames}) rfl)
  | @cons head tail initial middle final firstResults tailResults first rest ih =>
      intro frames collected
      have entered : Transition registry
          {initial with control := .sequence (head :: tail) collected,frames}
          {initial with control := head,frames := .sequence tail collected :: frames} :=
        .sequence_enter rfl
      have child := steps_append_frames first (.sequence tail collected :: frames)
      have childPath : Relation.ReflTransGen (Transition registry)
          {initial with control := head,frames := .sequence tail collected :: frames}
          {middle with control := .returned firstResults,frames := .sequence tail collected :: frames} := by
        simpa only [CompletedControl,appendFrames,List.nil_append] using child
      have returned : Transition registry
          {middle with control := .returned firstResults,frames := .sequence tail collected :: frames}
          {middle with control := .sequence tail (collected ++ firstResults),frames} :=
        .sequence_return rfl rfl
      simpa only [List.append_assoc] using
        ((Relation.ReflTransGen.head entered childPath).tail returned).trans
          (ih frames (collected ++ firstResults))

theorem completed_operand_bindings_valid {registry : SpaceSemantics.Program}
    {before after : Configuration} {bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst}
    {expression : Mettapedia.Languages.MeTTa.OSLFCore.Atom} {answers : List Answer}
    (valid : Idempotent bindings)
    (completed : CompletedControl registry (.evaluate bindings expression) before answers after) :
    ∀ answer ∈ answers, Idempotent answer.bindings := by
  have initial : ConfigurationRefines bindings
      {before with control := .evaluate bindings expression,frames := []} := by
    simp only [ConfigurationRefines,ControlRefines,List.not_mem_nil,false_implies,implies_true,and_true]
    exact ⟨valid,Refines.refl valid⟩
  have preserved := reached_answers_refine completed initial answers rfl
  exact fun answer member => (preserved answer member).1

end Mettapedia.Languages.MeTTa.PeTTa.Unifying
