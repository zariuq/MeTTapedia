import Mettapedia.OSLF.Syntax.ScopedRuleConstructorFrame
import Mettapedia.GSLT.Examples.ScopedLamCongExecution

/-!
# Authored lambda instance of the complete scoped rule frame

The actual two-layer LamCong firing passes through the general ordered
constructor-list comparison. An out-of-context oracle result cannot produce
a frame, matching the executable rejection control.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Examples.ScopedRuleConstructorFrame

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.Binding.ScopedRuleConstructorFrame
open Mettapedia.GSLT.Examples.ScopedLamCongExecution

/-- The open LamCong result has a complete retained rule frame: source
capture, the local recursive premise, and the checked final reduct. -/
theorem lamCong_has_rule_frame :
    ∃ firing : RuleFiring Unit,
      Nonempty (RuleConstructorFrame betaOracle RelationEnv.empty
        language 0 lamCongRule wrappedRedex firing) ∧
      firing.target = wrappedTarget := by
  obtain ⟨firing, selected, targetEq, _⟩ := lamCong_executes_open
  exact ⟨firing,
    (frame_nonempty_iff betaOracle RelationEnv.empty language 0
      lamCongRule wrappedRedex firing).mpr selected, targetEq⟩

/-- The generic bounded comparison classifies the same authored two-layer
event whose premise child runs beneath the lambda binder. -/
theorem authored_two_layer_frame :
    ∃ (history : RuleHistory) (rule : RewriteRule) (ruleIndex : Nat)
      (firing : RuleFiring RuleHistory),
      (rule, ruleIndex) ∈ language.rewrites.zipIdx ∧
      Nonempty (RuleConstructorFrame
        (rewriteAt RelationEnv.empty language 1)
        RelationEnv.empty language 0 rule wrappedRedex firing) ∧
      history = .fire ruleIndex firing.history ∧
      wrappedTarget = firing.target := by
  obtain ⟨pair, selected, targetEq⟩ :=
    List.mem_map.mp lamCong_requires_two_layers.2
  rcases pair with ⟨history, target⟩
  dsimp at targetEq
  subst target
  obtain ⟨rule, ruleIndex, declared, firing, frame,
    historyEq, targetEq⟩ :=
    (mem_rewriteAt_succ_iff_frames RelationEnv.empty language 1 0
      wrappedRedex wrappedTarget history).mp selected
  exact ⟨history, rule, ruleIndex, firing, declared, frame,
    historyEq, targetEq⟩

/-- An oracle answer using an unavailable variable cannot be upgraded to
a constructor frame of the authored rule. -/
theorem escaping_answer_has_no_frame (firing : RuleFiring Unit) :
    ¬ Nonempty (RuleConstructorFrame escapingOracle RelationEnv.empty
      language 0 lamCongRule wrappedRedex firing) := by
  intro frame
  have selected :=
    (frame_nonempty_iff escapingOracle RelationEnv.empty language 0
      lamCongRule wrappedRedex firing).mp frame
  rw [escaping_output_rejected] at selected
  cases selected

end Mettapedia.GSLT.Examples.ScopedRuleConstructorFrame
