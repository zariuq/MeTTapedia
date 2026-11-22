import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierNativeControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierNativeEffects

/-!
# A native failed leaf retires only after complete refutation

The compiled `fail` query has no enabled name. A total refuting probe builds
an empty expansion, which retires the actual native leaf. Any independent
context is carried unchanged, without a premise on its knowledge.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative.FailureControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage Hosting Hosting.Alternatives
open SourceLanguage.Elaboration SourceLanguage.Toolkit
open Hosting.Answers.Bags (D N P1 sp W0)

abbrev query := FrontierControls.failQuery
abbrev leaf := initialLeaf (D := D) N P1 query

theorem origin_related : HostedEvents.Related (D := D) N P1 query (W0, initialBranch query) [] :=
  HostedEvents.initial (D := D) (N := N) (P := P1) (q := query) sp (by trivial) FrontierControls.fail_unopened

theorem leaf_related : Related (D := D) N P1 query [] leaf := ⟨⟨_, origin_related⟩, .nil _ _⟩

theorem disabled (name : RuleName) : ¬ Enabled (D := D) N P1 leaf name := by
  intro enabled
  have historyEnabled := (FrontierNative.enabled_iff (D := D) N P1 query FrontierControls.plain_one leaf_related name).mpr enabled
  have sourceEnabled := (HostedEvents.enabled_iff FrontierControls.plain_one origin_related name).mpr historyEnabled
  exact Bridges.Controls.HostedEventsAudit.failure_has_no_named_child.false ⟨name, sourceEnabled⟩

def probe (name : RuleName) : ProbeResult (D := D) Nat N P1 leaf name := .ok (.inr ⟨disabled name⟩)

theorem ready : Ready (D := D) N P1 probe := fun _ _ => rfl

def chosen : Expansion (D := D) N P1 leaf := fromProbes (D := D) N P1 probe ready

theorem names_empty : chosen.names = ∅ := by
  ext name
  rw [chosen.complete]
  exact ⟨fun enabled => (disabled name enabled).elim, fun absent => by simp at absent⟩

theorem children_empty : chosen.children = 0 := by
  apply Multiset.card_eq_zero.mp
  rw [chosen.children_card, names_empty]
  rfl

theorem unfinished : ¬ StateFinished N leaf.state leaf.active := by
  intro finished
  have historyFinished := (FrontierNative.finished_iff (D := D) N P1 query leaf_related).mpr finished
  exact not_finished_of_fail rfl ((HostedEvents.finished_iff origin_related).mpr historyFinished)

theorem retires : Step (D := D) N P1 ⟨{leaf}, 0⟩ ⟨0, {leaf}⟩ := by
  have moved := Step.expand (D := D) (N := N) (P := P1) leaf 0 0 (valid_of_related (D := D) N P1 query leaf_related) unfinished chosen
  simpa [children_empty, Expansion.retire, names_empty] using moved

theorem retires_beside_any_context (context : Multiset (Leaf MSig)) :
    Step (D := D) N P1 ⟨{leaf} + context, 0⟩ ⟨context, {leaf}⟩ := by
  simpa only [zero_add] using Step.frame (D := D) N P1 retires context

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative.FailureControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative.FailureControls.disabled
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative.FailureControls.retires
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative.FailureControls.retires_beside_any_context
