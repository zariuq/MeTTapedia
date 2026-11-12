import Mettapedia.Languages.MeTTa.PeTTa.ConstructorEvaluation

/-!
# Completed operand schedules realized by direct data construction

The schedule's operand derivations are executed by the existing source rules.
Each alternative keeps its own binding packet. Held earlier values are only
resolved under the branch that finishes their suffix.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.ConstructorEvaluation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Machines.OrderedProtocol.Completion (OrderedStateFlatMapRel)
open Unifying

theorem Items.direct {registry : SpaceSemantics.Program} {before after : Configuration}
    {bindings : Subst} {expressions : List Atom} {values : List Values}
    (source : Items registry before bindings expressions after values) :
    ∀ held index frames,
    Relation.ReflTransGen (Transition registry)
      {before with control := .arguments bindings .data expressions held index,frames}
      {after with control := .returned (values.map (Values.withHeld held)),frames} := by
  refine Items.rec
    (motive_1 := fun before bindings expressions after values _ => ∀ held index frames,
      Relation.ReflTransGen (Transition registry)
        {before with control := .arguments bindings .data expressions held index,frames}
        {after with control := .returned (values.map (Values.withHeld held)),frames})
    (motive_2 := fun expressions answers before after values _ => ∀ held index,
      OrderedStateFlatMapRel (CompletedControl registry)
        (answers.map fun answer => .arguments answer.bindings .data expressions
          (held ++ [answer.value]) (index + 1))
        before (values.map (Values.withHeld held)) after)
    ?_ ?_ ?_ ?_ source
  · intro before bindings held index frames
    simp only [List.map_cons,List.map_nil,Values.withHeld,List.map_nil,List.append_nil]
    exact .single (step_transition rfl)
  · intro before middle after bindings first rest answers values operand branches ih held index frames
    have entry : Transition registry
        {before with control := .arguments bindings .data (first :: rest) held index,frames}
        {before with
          control := .evaluate bindings first
          frames := .argument .data rest held index :: frames} := .evaluated_argument rfl rfl
    have child : Relation.ReflTransGen (Transition registry)
        {before with control := .evaluate bindings first,frames := .argument .data rest held index :: frames}
        {middle with control := .returned answers,frames := .argument .data rest held index :: frames} := by
      simpa only [CompletedControl,appendFrames,List.nil_append] using
        steps_append_frames operand (.argument .data rest held index :: frames)
    have returned : Transition registry
        {middle with control := .returned answers,frames := .argument .data rest held index :: frames}
        {middle with
          control := .sequence (answers.map fun answer =>
            .arguments answer.bindings .data rest (held ++ [answer.value]) (index + 1)) []
          frames} :=
      .argument_return rfl rfl
    have suffix := ordered_controls_steps (ih held index) frames []
    exact ((Relation.ReflTransGen.head entry child).tail returned).trans suffix
  · intro expressions before held index
    exact OrderedStateFlatMapRel.nil before
  · intro expressions head more before middle after firstValues laterValues first later firstIH laterIH held index
    have child : CompletedControl registry
        (.arguments head.bindings .data expressions (held ++ [head.value]) (index + 1))
        before (firstValues.map (Values.withHeld (held ++ [head.value]))) middle :=
      firstIH (held ++ [head.value]) (index + 1) []
    have ordered := OrderedStateFlatMapRel.cons child (laterIH held index)
    simpa only [List.map_cons,List.map_append,List.map_map,Function.comp_def,Values.withHeld_prepend] using ordered

theorem Branches.direct_ordered {registry : SpaceSemantics.Program} {before after : Configuration}
    {expressions : List Atom} {answers : List Answer} {values : List Values}
    (source : Branches registry expressions answers before after values) :
    ∀ held index,
    OrderedStateFlatMapRel (CompletedControl registry)
      (answers.map fun answer => .arguments answer.bindings .data expressions
        (held ++ [answer.value]) (index + 1))
      before (values.map (Values.withHeld held)) after := by
  induction answers generalizing before after values with
  | nil => cases source; intro held index; exact OrderedStateFlatMapRel.nil _
  | cons head more ih =>
      cases source with
      | cons first later =>
          intro held index
          have child := first.direct (held ++ [head.value]) (index + 1) []
          have ordered := OrderedStateFlatMapRel.cons child (ih later held index)
          simpa only [List.map_cons,List.map_append,List.map_map,Function.comp_def,Values.withHeld_prepend] using ordered

end Mettapedia.Languages.MeTTa.PeTTa.ConstructorEvaluation
