import Mettapedia.Languages.MeTTa.PeTTa.ConstructorDirect
import Mettapedia.Languages.MeTTa.PeTTa.ConstructorAssembly

/-!
# The same completed schedules realized by native-cons expansion

The expansion and direct data construction reach identical return packets and
the same world above arbitrary saved caller frames. The hypotheses contain
actual operand paths and source-valid substitutions, not a promised equality
between evaluators. Escaping faults and full prefix reflection are separate
obligations from these completed-schedule realizations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.ConstructorEvaluation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Machines.OrderedProtocol.Completion (OrderedStateFlatMapRel)
open Unifying

theorem Items.spine {registry : SpaceSemantics.Program} {before after : Configuration}
    {bindings : Subst} {expressions : List Atom} {values : List Values}
    (source : Items registry before bindings expressions after values) :
    Idempotent bindings → ∀ frames,
    Relation.ReflTransGen (Transition registry)
      {before with control := .evaluate bindings (ConstructorSpine.build expressions),frames}
      {after with control := .returned (values.map Values.toAnswer),frames} := by
  refine Items.rec
    (motive_1 := fun before bindings expressions after values _ => Idempotent bindings → ∀ frames,
      Relation.ReflTransGen (Transition registry)
        {before with control := .evaluate bindings (ConstructorSpine.build expressions),frames}
        {after with control := .returned (values.map Values.toAnswer),frames})
    (motive_2 := fun expressions answers before after values _ =>
      (∀ answer ∈ answers, Idempotent answer.bindings) →
      OrderedStateFlatMapRel (CompletedControl registry)
        (answers.map fun answer => .arguments answer.bindings (.function "cons-atom")
          [ConstructorSpine.build expressions] [answer.value] 1)
        before (values.map Values.toAnswer) after)
    ?_ ?_ ?_ ?_ source
  · intro before bindings _ frames
    exact Relation.ReflTransGen.single (step_transition (ConstructorSpine.empty_step registry {before with frames} bindings))
  · intro before middle after bindings first rest answers values operand branches ih valid frames
    have entry : Transition registry
        {before with control := .evaluate bindings (ConstructorSpine.build (first :: rest)),frames}
        {before with
          control := .arguments bindings (.function "cons-atom") [first,ConstructorSpine.build rest] [] 0
          frames} :=
      step_transition (ConstructorSpine.cons_enter_step registry {before with frames} bindings first (ConstructorSpine.build rest))
    have demanded : Transition registry
        {before with
          control := .arguments bindings (.function "cons-atom") [first,ConstructorSpine.build rest] [] 0
          frames}
        {before with
          control := .evaluate bindings first
          frames := .argument (.function "cons-atom") [ConstructorSpine.build rest] [] 0 :: frames} :=
      step_transition (ConstructorSpine.cons_head_step registry {before with frames} bindings first (ConstructorSpine.build rest))
    have child : Relation.ReflTransGen (Transition registry)
        {before with
          control := .evaluate bindings first
          frames := .argument (.function "cons-atom") [ConstructorSpine.build rest] [] 0 :: frames}
        {middle with
          control := .returned answers
          frames := .argument (.function "cons-atom") [ConstructorSpine.build rest] [] 0 :: frames} := by
      simpa only [CompletedControl,appendFrames,List.nil_append] using
        steps_append_frames operand (.argument (.function "cons-atom") [ConstructorSpine.build rest] [] 0 :: frames)
    have returned : Transition registry
        {middle with
          control := .returned answers
          frames := .argument (.function "cons-atom") [ConstructorSpine.build rest] [] 0 :: frames}
        {middle with
          control := .sequence (answers.map fun answer =>
            .arguments answer.bindings (.function "cons-atom") [ConstructorSpine.build rest] [answer.value] 1) []
          frames} := Transition.argument_return
            (source := {middle with
              control := .returned answers
              frames := .argument (.function "cons-atom") [ConstructorSpine.build rest] [] 0 :: frames})
            (values := []) (index := 0) rfl rfl
    have suffix := ordered_controls_steps (ih (completed_operand_bindings_valid valid operand)) frames []
    exact ((Relation.ReflTransGen.single entry).tail demanded |>.trans child |>.tail returned).trans suffix
  · intro expressions before _
    exact OrderedStateFlatMapRel.nil before
  · intro expressions head more before middle after firstValues laterValues first later firstIH laterIH valid
    have headValid := valid head (by simp)
    have child : CompletedControl registry
        (.arguments head.bindings (.function "cons-atom") [ConstructorSpine.build expressions] [head.value] 1)
        before ((firstValues.map (Values.prepend head.value)).map Values.toAnswer) middle :=
      tail_completed head.bindings head.value (ConstructorSpine.build expressions) firstValues
        (firstIH headValid []) (first.normal headValid) []
    have ordered := OrderedStateFlatMapRel.cons child
      (laterIH (fun answer member => valid answer (List.mem_cons_of_mem head member)))
    simpa only [List.map_cons,List.map_append] using ordered

theorem Items.exact_return_boundaries {registry : SpaceSemantics.Program} {before after : Configuration}
    {bindings : Subst} {expressions : List Atom} {values : List Values}
    (source : Items registry before bindings expressions after values) (valid : Idempotent bindings)
    (frames : List Frame) :
    Relation.ReflTransGen (Transition registry)
        {before with control := .arguments bindings .data expressions [] 0,frames}
        {after with control := .returned (values.map Values.toAnswer),frames} ∧
      Relation.ReflTransGen (Transition registry)
        {before with control := .evaluate bindings (ConstructorSpine.build expressions),frames}
        {after with control := .returned (values.map Values.toAnswer),frames} := by
  have nilFunction : Values.withHeld [] = Values.toAnswer := by funext value; rfl
  exact ⟨by simpa only [nilFunction] using source.direct [] 0 frames,source.spine valid frames⟩

end Mettapedia.Languages.MeTTa.PeTTa.ConstructorEvaluation
