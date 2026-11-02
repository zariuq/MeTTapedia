import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox
import Mettapedia.OSLF.MeTTaIL.ReferenceStepAgreement

/-! Exact one-step readback for the authored mailbox kernel. The projected
schema table is checked against the loaded module. It is used to prove
exhaustive successors, not as an independent Erlang semantics. Payloads are
arbitrary patterns; source queue operations are joined in MailboxExecution. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Execution

open Mettapedia.OSLF.MeTTaIL Syntax Match ContextualStep
open ReflectiveCanonical ReflectiveSubstitution

def schemata : List (Pattern × Pattern) := [
    ((node "ErPeek" [(node "ErMailbox" [.fvar "saved", (node "ErValuesCons" [.fvar "head", .fvar "tail"]), .fvar "rear"])]), (node "ErPeekValue" [.fvar "head", (node "ErMailbox" [.fvar "saved", (node "ErValuesCons" [.fvar "head", .fvar "tail"]), .fvar "rear"])])),
    ((node "ErPeek" [(node "ErMailbox" [.fvar "saved", (node "ErValuesNil" []), (node "ErValuesNil" [])])]), (node "ErPeekEmpty" [(node "ErMailbox" [.fvar "saved", (node "ErValuesNil" []), (node "ErValuesNil" [])])])),
    ((node "ErPeek" [(node "ErMailbox" [.fvar "saved", (node "ErValuesNil" []), (node "ErValuesCons" [.fvar "head", .fvar "tail"])])]), (node "ErRotate" [.fvar "saved", (node "ErValuesCons" [.fvar "head", (node "ErValuesNil" [])]), .fvar "tail"])),
    ((node "ErRotate" [.fvar "saved", .fvar "front", (node "ErValuesCons" [.fvar "head", .fvar "tail"])]), (node "ErRotate" [.fvar "saved", (node "ErValuesCons" [.fvar "head", .fvar "front"]), .fvar "tail"])),
    ((node "ErRotate" [.fvar "saved", .fvar "front", (node "ErValuesNil" [])]), (node "ErPeek" [(node "ErMailbox" [.fvar "saved", .fvar "front", (node "ErValuesNil" [])])])),
    ((node "ErNext" [(node "ErMailbox" [.fvar "saved", (node "ErValuesCons" [.fvar "head", .fvar "tail"]), .fvar "rear"])]), (node "ErAdvanced" [(node "ErMailbox" [(node "ErValuesCons" [.fvar "head", .fvar "saved"]), .fvar "tail", .fvar "rear"])])),
    ((node "ErRemove" [(node "ErMailbox" [.fvar "saved", (node "ErValuesCons" [.fvar "head", .fvar "tail"]), .fvar "rear"])]), (node "ErRestore" [.fvar "saved", .fvar "tail", .fvar "rear"])),
    ((node "ErRestore" [(node "ErValuesCons" [.fvar "head", .fvar "tail"]), .fvar "front", .fvar "rear"]), (node "ErRestore" [.fvar "tail", (node "ErValuesCons" [.fvar "head", .fvar "front"]), .fvar "rear"])),
    ((node "ErRestore" [(node "ErValuesNil" []), .fvar "front", .fvar "rear"]), (node "ErRemoved" [(node "ErMailbox" [(node "ErValuesNil" []), .fvar "front", .fvar "rear"])])),
    ((node "ErDeliver" [.fvar "value", (node "ErMailbox" [.fvar "saved", .fvar "front", .fvar "rear"])]), (node "ErDelivered" [(node "ErMailbox" [.fvar "saved", .fvar "front", (node "ErValuesCons" [.fvar "value", .fvar "rear"])])])),
    ((node "ErWait" [(node "ErMailbox" [.fvar "saved", (node "ErValuesCons" [.fvar "head", .fvar "tail"]), .fvar "rear"])]), (node "ErReady" [(node "ErMailbox" [.fvar "saved", (node "ErValuesCons" [.fvar "head", .fvar "tail"]), .fvar "rear"])])),
    ((node "ErWait" [(node "ErMailbox" [.fvar "saved", (node "ErValuesNil" []), (node "ErValuesCons" [.fvar "head", .fvar "tail"])])]), (node "ErReady" [(node "ErMailbox" [.fvar "saved", (node "ErValuesNil" []), (node "ErValuesCons" [.fvar "head", .fvar "tail"])])])),
    ((node "ErWait" [(node "ErMailbox" [.fvar "saved", (node "ErValuesNil" []), (node "ErValuesNil" [])])]), (node "ErWaiting" [(node "ErMailbox" [.fvar "saved", (node "ErValuesNil" []), (node "ErValuesNil" [])])])),
    ((node "ErWake" [.fvar "value", (node "ErMailbox" [.fvar "saved", (node "ErValuesNil" []), (node "ErValuesNil" [])])]), (node "ErReady" [(node "ErMailbox" [.fvar "saved", (node "ErValuesNil" []), (node "ErValuesCons" [.fvar "value", (node "ErValuesNil" [])])])]))]

theorem schemata_exact : language.rewrites.map (fun rule => (rule.left, rule.right)) = schemata := rfl

theorem premises_empty {rule : RewriteRule} (member : rule ∈ language.rewrites) : rule.premises = [] := by
  have all : language.rewrites.all (fun rule => rule.premises.isEmpty) = true := by decide_cbv
  exact List.isEmpty_iff.mp (List.all_eq_true.mp all rule member)

theorem depth_aligned {rule : RewriteRule} (member : rule ∈ language.rewrites) : ruleDepthAligned rule = true := by
  have all : language.rewrites.all ruleDepthAligned = true := by decide_cbv
  exact List.all_eq_true.mp all rule member

def reducts (source : Pattern) : List Pattern :=
  schemata.flatMap fun schema => (matchPattern schema.1 source).map fun bindings => applyBindings bindings schema.2

theorem rewriteAt_succ (base : BasePremiseEvaluator) (fuel : Nat) (source : Pattern) :
    ContextualStep.rewriteAt base language (fuel + 1) source = reducts source := by
  unfold ContextualStep.rewriteAt
  have same : ∀ rule ∈ language.rewrites,
      applyRuleUsing base language (ContextualStep.rewriteAt base language fuel) rule source =
        (matchPattern rule.left source).map (fun bindings => applyBindings bindings rule.right) := by
    intro rule member
    simp only [applyRuleUsing, matchPatternForRule_eq_syntactic, premises_empty member,
      premisesUsing, List.map_singleton]
    simp only [applyBindingsForRule_eq_syntactic, applyRuleBindings_eq_applyBindings _ _ (depth_aligned member)]
    exact List.map_eq_flatMap.symm
  calc
    language.rewrites.flatMap (fun rule => applyRuleUsing base language
        (ContextualStep.rewriteAt base language fuel) rule source) =
      language.rewrites.flatMap (fun rule =>
        (matchPattern rule.left source).map fun bindings => applyBindings bindings rule.right) :=
      by
        apply List.flatMap_congr
        intro rule member
        exact same rule member
    _ = reducts source := by
      unfold reducts
      rw [← schemata_exact, List.flatMap_map]

theorem step_iff_mem (base : BasePremiseEvaluator) (source target : Pattern) :
    ContextualStep.Step base language source target ↔ target ∈ reducts source := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, found⟩
    cases fuel with
    | zero => cases found
    | succ fuel => simpa only [rewriteAt_succ] using found
  · intro found
    exact ⟨1, by simpa only [rewriteAt_succ] using found⟩

theorem peek_value_iff (base : BasePremiseEvaluator) (saved head tail rear target : Pattern) :
    ContextualStep.Step base language
      (node "ErPeek" [node "ErMailbox" [saved, node "ErValuesCons" [head, tail], rear]]) target ↔
      target = node "ErPeekValue" [head, node "ErMailbox" [saved, node "ErValuesCons" [head, tail], rear]] := by
  rw [step_iff_mem]
  simp [reducts, schemata, node, matchPattern, matchArgs, mergeBindings, applyBindings]

theorem peek_empty_iff (base : BasePremiseEvaluator) (saved target : Pattern) :
    ContextualStep.Step base language
      (node "ErPeek" [(node "ErMailbox" [saved, (node "ErValuesNil" []), (node "ErValuesNil" [])])]) target ↔
      target = (node "ErPeekEmpty" [(node "ErMailbox" [saved, (node "ErValuesNil" []), (node "ErValuesNil" [])])]) := by
  rw [step_iff_mem]
  simp [reducts, schemata, node, matchPattern, matchArgs, mergeBindings, applyBindings]

theorem peek_rotate_iff (base : BasePremiseEvaluator) (saved head tail target : Pattern) :
    ContextualStep.Step base language
      (node "ErPeek" [(node "ErMailbox" [saved, (node "ErValuesNil" []), (node "ErValuesCons" [head, tail])])]) target ↔
      target = (node "ErRotate" [saved, (node "ErValuesCons" [head, (node "ErValuesNil" [])]), tail]) := by
  rw [step_iff_mem]
  simp [reducts, schemata, node, matchPattern, matchArgs, mergeBindings, applyBindings]

theorem rotate_more_iff (base : BasePremiseEvaluator) (saved front head tail target : Pattern) :
    ContextualStep.Step base language
      (node "ErRotate" [saved, front, (node "ErValuesCons" [head, tail])]) target ↔
      target = (node "ErRotate" [saved, (node "ErValuesCons" [head, front]), tail]) := by
  rw [step_iff_mem]
  simp [reducts, schemata, node, matchPattern, matchArgs, mergeBindings, applyBindings]

theorem rotate_done_iff (base : BasePremiseEvaluator) (saved front target : Pattern) :
    ContextualStep.Step base language
      (node "ErRotate" [saved, front, (node "ErValuesNil" [])]) target ↔
      target = (node "ErPeek" [(node "ErMailbox" [saved, front, (node "ErValuesNil" [])])]) := by
  rw [step_iff_mem]
  simp [reducts, schemata, node, matchPattern, matchArgs, mergeBindings, applyBindings]

theorem next_iff (base : BasePremiseEvaluator) (saved head tail rear target : Pattern) :
    ContextualStep.Step base language
      (node "ErNext" [(node "ErMailbox" [saved, (node "ErValuesCons" [head, tail]), rear])]) target ↔
      target = (node "ErAdvanced" [(node "ErMailbox" [(node "ErValuesCons" [head, saved]), tail, rear])]) := by
  rw [step_iff_mem]
  simp [reducts, schemata, node, matchPattern, matchArgs, mergeBindings, applyBindings]

theorem remove_iff (base : BasePremiseEvaluator) (saved head tail rear target : Pattern) :
    ContextualStep.Step base language
      (node "ErRemove" [(node "ErMailbox" [saved, (node "ErValuesCons" [head, tail]), rear])]) target ↔
      target = (node "ErRestore" [saved, tail, rear]) := by
  rw [step_iff_mem]
  simp [reducts, schemata, node, matchPattern, matchArgs, mergeBindings, applyBindings]

theorem restore_more_iff (base : BasePremiseEvaluator) (head tail front rear target : Pattern) :
    ContextualStep.Step base language
      (node "ErRestore" [(node "ErValuesCons" [head, tail]), front, rear]) target ↔
      target = (node "ErRestore" [tail, (node "ErValuesCons" [head, front]), rear]) := by
  rw [step_iff_mem]
  simp [reducts, schemata, node, matchPattern, matchArgs, mergeBindings, applyBindings]

theorem restore_done_iff (base : BasePremiseEvaluator) (front rear target : Pattern) :
    ContextualStep.Step base language
      (node "ErRestore" [(node "ErValuesNil" []), front, rear]) target ↔
      target = (node "ErRemoved" [(node "ErMailbox" [(node "ErValuesNil" []), front, rear])]) := by
  rw [step_iff_mem]
  simp [reducts, schemata, node, matchPattern, matchArgs, mergeBindings, applyBindings]

theorem deliver_iff (base : BasePremiseEvaluator) (value saved front rear target : Pattern) :
    ContextualStep.Step base language
      (node "ErDeliver" [value, (node "ErMailbox" [saved, front, rear])]) target ↔
      target = (node "ErDelivered" [(node "ErMailbox" [saved, front, (node "ErValuesCons" [value, rear])])]) := by
  rw [step_iff_mem]
  simp [reducts, schemata, node, matchPattern, matchArgs, mergeBindings, applyBindings]

theorem wait_front_iff (base : BasePremiseEvaluator) (saved head tail rear target : Pattern) :
    ContextualStep.Step base language
      (node "ErWait" [(node "ErMailbox" [saved, (node "ErValuesCons" [head, tail]), rear])]) target ↔
      target = (node "ErReady" [(node "ErMailbox" [saved, (node "ErValuesCons" [head, tail]), rear])]) := by
  rw [step_iff_mem]
  simp [reducts, schemata, node, matchPattern, matchArgs, mergeBindings, applyBindings]

theorem wait_rear_iff (base : BasePremiseEvaluator) (saved head tail target : Pattern) :
    ContextualStep.Step base language
      (node "ErWait" [(node "ErMailbox" [saved, (node "ErValuesNil" []), (node "ErValuesCons" [head, tail])])]) target ↔
      target = (node "ErReady" [(node "ErMailbox" [saved, (node "ErValuesNil" []), (node "ErValuesCons" [head, tail])])]) := by
  rw [step_iff_mem]
  simp [reducts, schemata, node, matchPattern, matchArgs, mergeBindings, applyBindings]

theorem wait_empty_iff (base : BasePremiseEvaluator) (saved target : Pattern) :
    ContextualStep.Step base language
      (node "ErWait" [(node "ErMailbox" [saved, (node "ErValuesNil" []), (node "ErValuesNil" [])])]) target ↔
      target = (node "ErWaiting" [(node "ErMailbox" [saved, (node "ErValuesNil" []), (node "ErValuesNil" [])])]) := by
  rw [step_iff_mem]
  simp [reducts, schemata, node, matchPattern, matchArgs, mergeBindings, applyBindings]

theorem wake_iff (base : BasePremiseEvaluator) (value saved target : Pattern) :
    ContextualStep.Step base language
      (node "ErWake" [value, (node "ErMailbox" [saved, (node "ErValuesNil" []), (node "ErValuesNil" [])])]) target ↔
      target = (node "ErReady" [(node "ErMailbox" [saved, (node "ErValuesNil" []), (node "ErValuesCons" [value, (node "ErValuesNil" [])])])]) := by
  rw [step_iff_mem]
  simp [reducts, schemata, node, matchPattern, matchArgs, mergeBindings, applyBindings]

/-- Completed mailbox answers have no autonomous rule, even when a payload
itself has the syntax of a command. There is no implicit payload descent. -/
theorem answer_no_step (base : BasePremiseEvaluator) (label : String) (arguments : List Pattern)
    (answer : label ∈ ["ErPeekValue", "ErPeekEmpty", "ErAdvanced", "ErRemoved", "ErDelivered", "ErReady", "ErWaiting"])
    (target : Pattern) : ¬ ContextualStep.Step base language (node label arguments) target := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at answer
  rcases answer with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [step_iff_mem, reducts, schemata, node, matchPattern]

theorem empty_next_no_step (base : BasePremiseEvaluator) (saved rear target : Pattern) :
    ¬ ContextualStep.Step base language
      (node "ErNext" [node "ErMailbox" [saved, node "ErValuesNil", rear]]) target := by
  simp [step_iff_mem, reducts, schemata, node, matchPattern, matchArgs, mergeBindings]

theorem empty_remove_no_step (base : BasePremiseEvaluator) (saved rear target : Pattern) :
    ¬ ContextualStep.Step base language
      (node "ErRemove" [node "ErMailbox" [saved, node "ErValuesNil", rear]]) target := by
  simp [step_iff_mem, reducts, schemata, node, matchPattern, matchArgs, mergeBindings]

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Execution
