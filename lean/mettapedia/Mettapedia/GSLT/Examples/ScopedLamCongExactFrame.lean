import Mettapedia.GSLT.Examples.ScopedLamCongConstructorFrame
import Mettapedia.OSLF.Syntax.ScopedOperationalPresentation

/-!
# The authored LamCong frame has the exact open beta child

The selected contextual capture fixes the child's source. The beta oracle
fixes its target and occurrence. The comparison below follows the actual
ordered constructor frame, retaining the authored parent rule position.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Examples.ScopedLamCongExactFrame

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.Binding.ScopedRuleConstructorFrame
open Mettapedia.OSLF.Binding.ScopedOperationalPresentation
open Mettapedia.OSLF.Binding.ScopedPremiseSkeleton
open Mettapedia.OSLF.Binding.ScopedPremiseFrameLists
open Mettapedia.GSLT.Examples.ScopedLamCongExecution
open Mettapedia.GSLT.Examples.ScopedLamCongConstructorFrame

private theorem listed : (lamCongRule, 1) ∈ language.rewrites.zipIdx := by
  simp [language]

/-- Every selected constructor frame whose oracle has only the authored
open beta target requests the same exact binder-local judgment. -/
theorem frame_exact_child_of_unique_target {Evidence : Type}
    (oracle : StepOracle Evidence)
    (outcome : ∀ evidence target,
      (evidence, target) ∈ oracle 1 openRedex →
        target = Pattern.bvar 0)
    (firing : RuleFiring Evidence)
    (frame : RuleConstructorFrame oracle RelationEnv.empty language
      0 lamCongRule wrappedRedex firing) :
    (RuleConstructorFrame.toSkeleton 1 listed frame).children =
      [(1, openRedex, Pattern.bvar 0)] := by
  suffices general : ∀ (spec : RuleBindingSpec)
      (captured completed : Assignment)
      (history : List (PremiseEvent Evidence)),
      lamCongRule.bindings = some spec →
      captured ∈ matchRuleAt lamCongRule spec 0 wrappedRedex →
      (run : RunFrame oracle RelationEnv.empty language lamCongRule
        spec 0 0 [.scopedStep localStep] captured completed history) →
      (RunFrame.toSkeleton run).children =
        [(1, openRedex, Pattern.bvar 0)] by
    exact general frame.spec frame.captured frame.completed frame.history
      frame.declared frame.selected frame.premises
  intro spec captured completed history declared selected run
  cases run with
  | cons head tail =>
      cases tail
      cases head with
      | scopedStep wellScoped child admitted =>
          have exact := selected_lamCong_child_exact_of_unique_target
            oracle outcome spec captured completed _ child
              declared selected admitted
          have ambient : child.ambient = 1 := by
            simpa [localStep] using admitted.1
          have requested := RunFrame.toSkeleton_children_eq_requests
            (relEnv := RelationEnv.empty) (lang := language)
            (RunFrame.cons (PremiseFrame.scopedStep wellScoped child admitted)
              RunFrame.nil)
          simpa [RunFrame.childRequests,
            PremiseFrame.childRequest?, ambient, exact.1, exact.2]
            using requested

/-- The executable one-result beta oracle is a concrete instance of the
general exact-child frame theorem. -/
theorem frame_exact_child (firing : RuleFiring Unit)
    (frame : RuleConstructorFrame betaOracle RelationEnv.empty language
      0 lamCongRule wrappedRedex firing) :
    (RuleConstructorFrame.toSkeleton 1 listed frame).children =
      [(1, openRedex, Pattern.bvar 0)] := by
  apply frame_exact_child_of_unique_target betaOracle
  · intro evidence target selected
    rw [inner_beta_open] at selected
    have pair : evidence = () ∧ target = Pattern.bvar 0 := by
      simpa only [List.mem_singleton, Prod.mk.injEq] using selected
    exact pair.2

/-- The recursive beta executor retains histories, while every result at
the authored open redex has the bound variable as target. -/
theorem history_target_unique (evidence : RuleHistory) (target : Pattern)
    (selected : (evidence, target) ∈
      rewriteAt RelationEnv.empty language 1 1 openRedex) :
    target = .bvar 0 := by
  have mapped : target ∈
      (rewriteAt RelationEnv.empty language 1 1 openRedex).map
        Prod.snd :=
    List.mem_map.mpr ⟨(evidence, target), selected, rfl⟩
  rw [inner_beta_targets] at mapped
  simpa using mapped

/-- The actual one-fuel beta history oracle gives the precise recursive
child judgment of any selected LamCong frame. -/
theorem history_frame_exact_child (firing : RuleFiring RuleHistory)
    (frame : RuleConstructorFrame
      (rewriteAt RelationEnv.empty language 1)
      RelationEnv.empty language 0 lamCongRule wrappedRedex firing) :
    (RuleConstructorFrame.toSkeleton 1 listed frame).children =
      [(1, openRedex, Pattern.bvar 0)] :=
  frame_exact_child_of_unique_target
    (rewriteAt RelationEnv.empty language 1)
    history_target_unique firing frame

private theorem history_of_indicator (history : RuleHistory)
    (indicated : lamCongBetaHistory history = true) :
    history = .fire 1 [.step 0 0 (.fire 0 [])] := by
  unfold lamCongBetaHistory at indicated
  split at indicated
  · rfl
  · cases indicated

/-- The actual two-layer authored execution yields a raw constructor
whose sole recursive child is exactly the open beta judgment. This uses
the selected history frame, so no different equal-endpoint occurrence is
substituted for the running child. -/
theorem raw_exact_shape :
    ∃ shape : RuleSkeleton RuleHistory RelationEnv.empty language
        0 wrappedRedex wrappedTarget,
      shape.ruleIndex = 1 ∧
      shape.children = [(1, openRedex, .bvar 0)] := by
  obtain ⟨⟨history, target⟩, executed, targetEq⟩ :=
    List.mem_map.mp lamCong_requires_two_layers.2
  dsimp at targetEq
  subst target
  have mapped :
      (lamCongBetaHistory history, wrappedTarget == wrappedTarget) ∈
        (rewriteAt RelationEnv.empty language 2 0 wrappedRedex).map
          (fun (event, result) =>
            (lamCongBetaHistory event, result == wrappedTarget)) :=
    List.mem_map.mpr ⟨(history, wrappedTarget), executed, rfl⟩
  rw [lamCong_tree_shape] at mapped
  have indicated : lamCongBetaHistory history = true :=
    congrArg Prod.fst (List.mem_singleton.mp mapped)
  have exactHistory := history_of_indicator history indicated
  obtain ⟨rule, ruleIndex, listedRule, firing, ⟨frame⟩,
      historyEq, targetEq⟩ :=
    (mem_rewriteAt_succ_iff_frames RelationEnv.empty language 1 0
      wrappedRedex wrappedTarget history).mp executed
  have indexEq : ruleIndex = 1 := by
    have projected := congrArg
      (fun observed : RuleHistory =>
        match observed with
        | .fire index _ => index) historyEq
    rw [exactHistory] at projected
    simpa using projected.symm
  have ruleEq : rule = lamCongRule := by
    have listed := listedRule
    simp [language, indexEq] at listed
    exact listed
  subst rule
  subst ruleIndex
  let shape := RuleConstructorFrame.toSkeleton 1 listedRule frame
  have exactChild := history_frame_exact_child firing frame
  have targetEq' : firing.target = wrappedTarget := targetEq.symm
  cases firing with
  | mk captured completed premiseHistory target =>
      dsimp at targetEq'
      subst target
      exact ⟨shape, rfl, exactChild⟩

#print axioms frame_exact_child_of_unique_target
#print axioms frame_exact_child
#print axioms history_frame_exact_child
#print axioms raw_exact_shape

end Mettapedia.GSLT.Examples.ScopedLamCongExactFrame
