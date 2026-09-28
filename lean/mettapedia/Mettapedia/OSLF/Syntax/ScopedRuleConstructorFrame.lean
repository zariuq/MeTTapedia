import Mettapedia.OSLF.Syntax.ScopedPremiseFrameLists

/-!
# Constructor frames for complete conditional rule firings

An admitted authored rule selects a scoped capture, runs its ordered premise
frames, and finishes with a reduct. The constructor frame retains all three
stages and their evidence. Its comparison with the executable rule applier
is exact at each finite recursion depth.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedRuleConstructorFrame

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.Binding.ScopedPremiseFrameLists

/-- A whole firing retains the admitted binding declaration, the selected
initial capture, an ordered premise derivation, and the checked reduct. -/
structure RuleConstructorFrame {Evidence : Type}
    (oracle : StepOracle Evidence) (relEnv : RelationEnv)
    (lang : LanguageDef) (ambient : Nat)
    (rule : RewriteRule) (source : Pattern)
    (firing : RuleFiring Evidence) where
  spec : RuleBindingSpec
  declared : rule.bindings = some spec
  admitted : admittedFor rule spec = true
  captured : Assignment
  selected : captured ∈ matchRuleAt rule spec ambient source
  completed : Assignment
  history : List (PremiseEvent Evidence)
  premises : RunFrame oracle relEnv lang rule spec ambient 0
    rule.premises captured completed history
  finished : finish? rule spec ambient captured completed history =
    some firing

/-- Complete executable firing is equivalent to a retained constructor
frame. In particular the list proof cannot omit or reorder a premise. -/
theorem frame_nonempty_iff {Evidence : Type}
    (oracle : StepOracle Evidence) (relEnv : RelationEnv)
    (lang : LanguageDef) (ambient : Nat)
    (rule : RewriteRule) (source : Pattern)
    (firing : RuleFiring Evidence) :
    Nonempty (RuleConstructorFrame oracle relEnv lang ambient
      rule source firing) ↔
      firing ∈ applyRuleWithOracle oracle relEnv lang ambient rule source := by
  constructor
  · rintro ⟨frame⟩
    exact (mem_applyRuleWithOracle_iff oracle relEnv lang ambient
      rule source firing).mpr
      ⟨frame.spec, frame.captured, frame.completed, frame.history,
        frame.declared, frame.admitted, frame.selected,
        (runFrame_nonempty_iff oracle relEnv lang rule frame.spec
          ambient 0 rule.premises frame.captured frame.completed
          frame.history).mp ⟨frame.premises⟩, frame.finished⟩
  · intro selected
    obtain ⟨spec, captured, completed, history, declared,
      admitted, capturedSelected, premiseRun, finished⟩ :=
      (mem_applyRuleWithOracle_iff oracle relEnv lang ambient
        rule source firing).mp selected
    obtain ⟨premises⟩ :=
      (runFrame_nonempty_iff oracle relEnv lang rule spec
        ambient 0 rule.premises captured completed history).mpr premiseRun
    exact ⟨RuleConstructorFrame.mk spec declared admitted captured
      capturedSelected completed history premises finished⟩

/-- The bounded executor has exactly the recursively indexed rule frames
selected from the authored rule list. Recursive child evidence is supplied
at the preceding fuel depth in each premise's local context. -/
theorem mem_rewriteAt_succ_iff_frames
    (relEnv : RelationEnv) (lang : LanguageDef)
    (fuel ambient : Nat) (source target : Pattern)
    (history : RuleHistory) :
    (history, target) ∈ rewriteAt relEnv lang (fuel + 1) ambient source ↔
      ∃ rule ruleIndex,
        (rule, ruleIndex) ∈ lang.rewrites.zipIdx ∧
        ∃ firing,
          Nonempty (RuleConstructorFrame (rewriteAt relEnv lang fuel)
            relEnv lang ambient rule source firing) ∧
          history = .fire ruleIndex firing.history ∧
          target = firing.target := by
  rw [mem_rewriteAt_succ_iff]
  constructor
  · rintro ⟨rule, ruleIndex, declared, firing, selected,
      historyEq, targetEq⟩
    exact ⟨rule, ruleIndex, declared, firing,
      (frame_nonempty_iff (rewriteAt relEnv lang fuel) relEnv lang ambient
        rule source firing).mpr selected, historyEq, targetEq⟩
  · rintro ⟨rule, ruleIndex, declared, firing, frame,
      historyEq, targetEq⟩
    exact ⟨rule, ruleIndex, declared, firing,
      (frame_nonempty_iff (rewriteAt relEnv lang fuel) relEnv lang ambient
        rule source firing).mp frame, historyEq, targetEq⟩

end Mettapedia.OSLF.Binding.ScopedRuleConstructorFrame
