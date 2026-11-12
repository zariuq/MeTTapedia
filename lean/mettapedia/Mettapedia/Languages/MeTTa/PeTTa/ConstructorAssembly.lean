import Mettapedia.Languages.MeTTa.PeTTa.ConstructorEvaluation

/-!
# Native assembly after actual constructor-tail evaluation

The tail packets already have resolved values under their own substitutions.
Native cons therefore assembles each result without changing those bindings,
the reached world or the logical identity supply.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.ConstructorEvaluation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Machines.OrderedProtocol.Completion (OrderedStateFlatMapRel)
open Unifying

def finishControl (head : Atom) (value : Values) : Control :=
  .arguments value.bindings (.function "cons-atom") [] [head,.expression value.items] 2

theorem finish_completed (registry : SpaceSemantics.Program) (base : Configuration)
    (head : Atom) (value : Values) (normal : value.Normal) :
    CompletedControl registry (finishControl head value) base [(value.prepend head).toAnswer] base := by
  apply Relation.ReflTransGen.single
  apply step_transition
  exact ConstructorSpine.cons_finish_normal registry {base with frames := []}
    value.bindings head value.items normal.2

theorem finish_ordered (registry : SpaceSemantics.Program) (base : Configuration)
    (head : Atom) (values : List Values) (normal : ∀ value ∈ values, value.Normal) :
    OrderedStateFlatMapRel (CompletedControl registry) (values.map (finishControl head)) base
      ((values.map (Values.prepend head)).map Values.toAnswer) base := by
  induction values with
  | nil => exact OrderedStateFlatMapRel.nil base
  | cons value rest ih =>
      have first := finish_completed registry base head value (normal value (by simp))
      have later := ih (fun tail member => normal tail (List.mem_cons_of_mem value member))
      simpa only [List.map_cons,List.singleton_append] using OrderedStateFlatMapRel.cons first later

theorem finish_packets (registry : SpaceSemantics.Program) (base : Configuration)
    (head : Atom) (values : List Values) (normal : ∀ value ∈ values, value.Normal) (frames : List Frame) :
    Relation.ReflTransGen (Transition registry)
      {base with
        control := .returned (values.map Values.toAnswer)
        frames := .argument (.function "cons-atom") [] [head] 1 :: frames}
      {base with control := .returned ((values.map (Values.prepend head)).map Values.toAnswer),frames} := by
  have returned : Transition registry
      {base with
        control := .returned (values.map Values.toAnswer)
        frames := .argument (.function "cons-atom") [] [head] 1 :: frames}
      {base with control := .sequence (values.map (finishControl head)) [],frames} := by
    change Transition registry _
      {base with control := .sequence (values.map fun value =>
        .arguments value.bindings (.function "cons-atom") [] [head,.expression value.items] 2) [],frames}
    simpa only [List.map_map,Function.comp_def,Values.toAnswer,finishControl,List.singleton_append] using
      Transition.argument_return (registry := registry)
        (source := {base with
          control := .returned (values.map Values.toAnswer)
          frames := .argument (.function "cons-atom") [] [head] 1 :: frames}) rfl rfl
  exact (Relation.ReflTransGen.single returned).trans
    (ordered_controls_steps (finish_ordered registry base head values normal) frames [])

theorem tail_completed {registry : SpaceSemantics.Program} {before after : Configuration}
    (bindings : Subst) (head expression : Atom) (values : List Values)
    (evaluated : CompletedControl registry (.evaluate bindings expression) before
      (values.map Values.toAnswer) after)
    (normal : ∀ value ∈ values, value.Normal) (frames : List Frame) :
    Relation.ReflTransGen (Transition registry)
      {before with control := .arguments bindings (.function "cons-atom") [expression] [head] 1,frames}
      {after with control := .returned ((values.map (Values.prepend head)).map Values.toAnswer),frames} := by
  have entry : Transition registry
      {before with control := .arguments bindings (.function "cons-atom") [expression] [head] 1,frames}
      {before with
        control := .evaluate bindings expression
        frames := .argument (.function "cons-atom") [] [head] 1 :: frames} :=
    step_transition (ConstructorSpine.cons_tail_step registry {before with frames} bindings head expression)
  have child : Relation.ReflTransGen (Transition registry)
      {before with
        control := .evaluate bindings expression
        frames := .argument (.function "cons-atom") [] [head] 1 :: frames}
      {after with
        control := .returned (values.map Values.toAnswer)
        frames := .argument (.function "cons-atom") [] [head] 1 :: frames} := by
    simpa only [CompletedControl,appendFrames,List.nil_append] using
      steps_append_frames evaluated (.argument (.function "cons-atom") [] [head] 1 :: frames)
  exact (Relation.ReflTransGen.head entry child).trans (finish_packets registry after head values normal frames)

end Mettapedia.Languages.MeTTa.PeTTa.ConstructorEvaluation
