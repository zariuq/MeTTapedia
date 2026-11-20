import Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPatternCode
import Mettapedia.Languages.MeTTa.PeTTa.ConstructorAssembly

/-!
# Finite native execution of the structural data-pattern code

The code runs in the existing source machine. Every finite template returns
exactly its instantiated value, with the same world, bindings, identity
supply, private code and I/O. Actual source paths provide a finite allowance
after which the runner is complete. No termination hypothesis about an
arbitrary operand, or interpretation supplied by an answer oracle, is used.

Text readback, computed-let selection and clause activation are separate
connections. This establishes the finite constructor-execution component.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPattern

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Machines.OrderedProtocol.Completion (OrderedStateFlatMapRel)
open Unifying
open ConstructorEvaluation (Values)

private theorem cons_completed (registry : SpaceSemantics.Program) (base : Configuration)
    (bindings : Subst) (valid : Idempotent bindings) (first rest head : Atom) (tail : List Atom)
    (headNormal : Unbound bindings head) (tailNormal : Unbound bindings (.expression tail))
    (headPath : CompletedControl registry (.evaluate bindings first) base [⟨head, bindings⟩] base)
    (tailPath : CompletedControl registry (.evaluate bindings rest) base [⟨.expression tail, bindings⟩] base) :
    CompletedControl registry (.evaluate bindings (ConstructorSpine.cons first rest)) base
      [⟨.expression (head :: tail), bindings⟩] base := by
  let packet : Values := ⟨tail, bindings⟩
  have tailPackets : CompletedControl registry (.evaluate bindings rest) base
      ([packet].map Values.toAnswer) base := tailPath
  have normal : ∀ value ∈ [packet], value.Normal := by
    intro value member
    have same : value = packet := List.mem_singleton.mp member
    subst value
    exact ⟨valid, tailNormal⟩
  have tailRun := ConstructorEvaluation.tail_completed bindings head rest [packet] tailPackets normal []
  have headFixed := resolve_of_unbound head headNormal
  have tailDone : CompletedControl registry
      (.arguments bindings (.function "cons-atom") [rest] [head] 1) base
      [⟨.expression (head :: tail), bindings⟩] base := by
    simpa only [CompletedControl, List.map_cons, List.map_nil, Values.toAnswer,
      Values.prepend, packet, headFixed] using tailRun
  have ordered : OrderedStateFlatMapRel (CompletedControl registry)
      [.arguments bindings (.function "cons-atom") [rest] [head] 1] base
      [⟨.expression (head :: tail), bindings⟩] base :=
    .cons tailDone (.nil base)
  have suffix := ordered_controls_steps ordered [] []
  have entry := step_transition (ConstructorSpine.cons_enter_step registry {base with frames := []}
    bindings first rest)
  have demand := step_transition (ConstructorSpine.cons_head_step registry {base with frames := []}
    bindings first rest)
  have child : Relation.ReflTransGen (Transition registry)
      {base with
        control := .evaluate bindings first
        frames := [.argument (.function "cons-atom") [rest] [] 0]}
      {base with
        control := .returned [⟨head, bindings⟩]
        frames := [.argument (.function "cons-atom") [rest] [] 0]} := by
    simpa only [CompletedControl, appendFrames, List.nil_append] using
      steps_append_frames headPath [.argument (.function "cons-atom") [rest] [] 0]
  have returned : Transition registry
      {base with
        control := .returned [⟨head, bindings⟩]
        frames := [.argument (.function "cons-atom") [rest] [] 0]}
      {base with
        control := .sequence [.arguments bindings (.function "cons-atom") [rest] [head] 1] []
        frames := []} :=
    .argument_return
      (source := {base with
        control := .returned [⟨head, bindings⟩]
        frames := [.argument (.function "cons-atom") [rest] [] 0]})
      (values := []) (index := 0) rfl rfl
  exact ((Relation.ReflTransGen.single entry).tail demand |>.trans child |>.tail returned).trans suffix

mutual
  theorem atomCode_completes (registry : SpaceSemantics.Program) (base : Configuration)
      (bindings : Subst) (valid : Idempotent bindings) (template : Atom) :
      CompletedControl registry (.evaluate bindings (atomCode template)) base
        [⟨resolve bindings template, bindings⟩] base := by
    cases template with
    | var name => exact .single (step_transition rfl)
    | symbol name => exact .single (step_transition rfl)
    | grounded value => exact .single (step_transition rfl)
    | expression items => exact listCode_completes registry base bindings valid items
  termination_by sizeOf template

  theorem listCode_completes (registry : SpaceSemantics.Program) (base : Configuration)
      (bindings : Subst) (valid : Idempotent bindings) (templates : List Atom) :
      CompletedControl registry (.evaluate bindings (listCode templates)) base
        [⟨.expression (applySubst.applySubstList bindings templates), bindings⟩] base := by
    cases templates with
    | nil =>
        have entry : Transition registry
            {base with control := .evaluate bindings (.expression []), frames := []}
            {base with control := .arguments bindings .data [] [] 0, frames := []} :=
          step_transition rfl
        have returned : Transition registry
            {base with control := .arguments bindings .data [] [] 0, frames := []}
            {base with control := .returned [⟨.expression [], bindings⟩], frames := []} :=
          step_transition rfl
        exact (Relation.ReflTransGen.single entry).tail returned
    | cons first rest =>
        have headPath := atomCode_completes registry base bindings valid first
        have tailPath := listCode_completes registry base bindings valid rest
        have normal := unbound_resolve valid (.expression rest)
        exact cons_completed registry base bindings valid (atomCode first) (listCode rest)
          (resolve bindings first) (applySubst.applySubstList bindings rest)
          (unbound_resolve valid first) normal headPath tailPath
  termination_by sizeOf templates
end

/-- The component executes above arbitrary saved caller frames, which are
left untouched at its return boundary. -/
theorem atomCode_under_frames (registry : SpaceSemantics.Program) (base : Configuration)
    (bindings : Subst) (valid : Idempotent bindings) (template : Atom) (frames : List Frame) :
    Relation.ReflTransGen (Transition registry)
      {base with control := .evaluate bindings (atomCode template), frames}
      {base with control := .returned [⟨resolve bindings template, bindings⟩], frames} := by
  simpa only [CompletedControl, appendFrames, List.nil_append] using
    steps_append_frames (atomCode_completes registry base bindings valid template) frames

/-- A finite administrative allowance is constructed from the actual path.
Every larger allowance gives the same singleton answer and world. -/
theorem atomCode_run (registry : SpaceSemantics.Program) (base : Configuration)
    (bindings : Subst) (valid : Idempotent bindings) (template : Atom) :
    ∃ spent, ∀ remaining,
      run registry (spent + remaining)
        {base with control := .evaluate bindings (atomCode template), frames := []} =
      .complete base.state [resolve bindings template] base.input base.output := by
  obtain ⟨spent, continues⟩ := steps_run_suffix
    (atomCode_completes registry base bindings valid template)
  refine ⟨spent, ?_⟩
  intro remaining
  rw [continues remaining]
  cases remaining <;> simp only [run, List.map_cons, List.map_nil, resolve_idem valid template]

#print axioms atomCode_completes
#print axioms atomCode_under_frames
#print axioms atomCode_run

end Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPattern
