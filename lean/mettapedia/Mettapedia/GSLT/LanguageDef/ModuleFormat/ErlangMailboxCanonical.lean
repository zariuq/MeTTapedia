import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailboxSteps
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.OSLF.MeTTaIL.CanonicalBags

/-! The mailbox kernel only rearranges constructor fields. Canonicalizing
unordered collections in a payload cannot change an already canonical
mailbox step. No queue order or duplicate occurrence is identified. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Execution

open Mettapedia.OSLF.MeTTaIL Syntax Match MatchSpec ContextualStep
open ReflectiveCanonical ReflectiveSubstitution CanonicalBags

private theorem schema_canonical (schema : Pattern × Pattern) (member : schema ∈ schemata)
    (bindings : Bindings) :
    canon (applyBindings bindings schema.1) = applyBindings bindings schema.1 →
      canon (applyBindings bindings schema.2) = applyBindings bindings schema.2 := by
  simp only [schemata, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [node, applyBindings, List.map_cons, List.map_nil, canon_apply,
      Pattern.apply.injEq, List.cons.injEq, and_true, true_and] <;>
    aesop

theorem step_preserves_canonical (base : BasePremiseEvaluator) {source target : Pattern}
    (canonical : canon source = source) (step : ContextualStep.Step base language source target) :
    canon target = target := by
  obtain ⟨_, firing⟩ := step
  cases firing with
  | @rule _ _ _ rule initial final member matched premises applied =>
      rw [premises_empty member] at premises
      cases premises
      rw [matchPatternForRule_eq_syntactic] at matched
      have all : language.rewrites.all (fun rule => isMatchCorrectAux rule.left) = true := by decide_cbv
      have reconstructed := matchPattern_correct matched (List.all_eq_true.mp all rule member)
      rw [applyBindingsForRule_eq_syntactic,
        applyRuleBindings_eq_applyBindings _ _ (depth_aligned member)] at applied
      have schema : (rule.left, rule.right) ∈ schemata := by
        rw [← schemata_exact]
        exact List.mem_map_of_mem member
      have preserved := schema_canonical (rule.left, rule.right) schema initial
        (by simpa only [reconstructed] using canonical)
      simpa only [applied] using preserved

theorem canon_values (elements : List Pattern)
    (canonical : ∀ element ∈ elements, canon element = element) : canon (values elements) = values elements := by
  induction elements with
  | nil => simp [values, node, canon_apply]
  | cons head tail ih =>
      simp only [values, node, canon_apply, List.map_cons, List.map_nil,
        canonical head (List.mem_cons_self ..), ih (fun _ member => canonical _ (List.mem_cons_of_mem _ member))]

theorem canon_mailbox {α : Type*} (encode : α → Pattern)
    (canonical : ∀ value, canon (encode value) = encode value)
    (box : Mettapedia.Languages.Erlang.Mailbox α) : canon (mailbox encode box) = mailbox encode box := by
  have each (items : List α) : canon (values (items.map encode)) = values (items.map encode) := by
    apply canon_values
    intro element member
    obtain ⟨value, _, rfl⟩ := List.mem_map.mp member
    exact canonical value
  simp only [mailbox, node, canon_apply, List.map_cons, List.map_nil, each]

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Execution
