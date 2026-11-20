import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RootRewrites
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ContextTraversal

/-! # Every actual directed native step executes in the finite source program -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.StepRewrites

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing
open RuleBuilder RuleInstances

variable {dev : Definitions.Development} (built : Compiled dev)

theorem traversal_member {rule : ProgramBinders.Equation MSig [] ()} (member : rule ∈ ContextRules.traversal) :
    rule ∈ built.rules := RootRewrites.fixed_member built (by simp [ContextRules.fixed, member])

theorem routing_member {rule : ProgramBinders.Equation MSig [] ()} (member : rule ∈ ContextRules.routing) :
    rule ∈ built.rules := traversal_member built (by simp [ContextRules.traversal, member])

theorem route_root (term context continuation : MClosed) :
    ProgramBinders.Rewrites built.rules.get (seekC term context continuation)
      (rootC term (nodeC "hd-main-plug" [context, continuation])) := by
  have step := RuleInstances.template
    (ContextRules.active (n := 3) "hd-seek" [slot 0, slot 1, slot 2])
    (ContextRules.active "hd-root" [slot 0, node "hd-main-plug" [slot 1, slot 2]])
    (routing_member built (by simp [ContextRules.routing])) ![term, context, continuation]
  simpa [seekC, rootC, activeC, ContextRules.active] using step

theorem route_plug (term context continuation : MClosed) :
    ProgramBinders.Rewrites built.rules.get (resumeC term (nodeC "hd-main-plug" [context, continuation]))
      (plugC term context continuation) := by
  have step := RuleInstances.template
    (ContextRules.active (n := 3) "hd-resume" [slot 0, node "hd-main-plug" [slot 1, slot 2]])
    (ContextRules.active "hd-plug" [slot 0, slot 1, slot 2])
    (routing_member built (by simp [ContextRules.routing])) ![term, context, continuation]
  simpa [resumeC, plugC, activeC, ContextRules.active] using step

theorem plug_empty (term continuation : MClosed) :
    ProgramBinders.Rewrites built.rules.get (plugC term emptyContext continuation) (resumeC term continuation) := by
  have step := RuleInstances.template
    (ContextRules.active (n := 2) "hd-plug" [slot 0, node "hd-context-empty" [], slot 1])
    (ContextRules.active "hd-resume" [slot 0, slot 1])
    (routing_member built (by simp [ContextRules.routing])) ![term, continuation]
  simpa [plugC, emptyContext, resumeC, activeC, ContextRules.active] using step

theorem directed_step {n : Nat} {before after : Tower.Tm n}
    (reduction : StrongNormalization.Reduces (Definitions.devPackage dev built.nativeRows) before after)
    (continuation : MClosed) :
    Steps built.rules (seekC (encodeTm before) emptyContext continuation) (resumeC (encodeTm after) continuation) := by
  obtain ⟨event, allowed, starts, ends⟩ := DirectedSyntax.complete (RootRewrites.presentation built) reduction
  rw [← starts, ← ends]
  have descend := ContextTraversal.seek (fun rule member => traversal_member built member)
    event.context event.action.source emptyContext continuation
  have enter := route_root built (encodeTm event.action.source) (contextCode event.context emptyContext) continuation
  have compute := RootRewrites.action built event.action allowed
    (nodeC "hd-main-plug" [contextCode event.context emptyContext, continuation])
  have leave := route_plug built (encodeTm event.action.target) (contextCode event.context emptyContext) continuation
  have ascend := ContextTraversal.plug (fun rule member => traversal_member built member)
    event.context event.action.target emptyContext continuation
  exact descend.trans ((Relation.ReflTransGen.single enter).trans (compute.trans ((Relation.ReflTransGen.single leave).trans
    (ascend.trans (Relation.ReflTransGen.single (plug_empty built (encodeTm event.target) continuation))))))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.StepRewrites
