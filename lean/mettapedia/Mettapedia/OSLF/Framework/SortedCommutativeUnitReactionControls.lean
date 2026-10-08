import Mettapedia.OSLF.Framework.SortedCommutativeUnitReactionCompetition
import Mettapedia.OSLF.Framework.SortedCommutativeProbeReconstructionControls

/-!+# A proper unit reaction gives a second actual get result

An independently authored original binary Cut rule is added to the whole
administrative observer family. Both firings use the same complete input
and literal get label. The original firing retains the entire assay and
its supplied source reactum, whereas the administrative firing returns
the selected child. Support distinguishes the actual target classes.

The context category still has every origin-based RPO, and its literal
IPO bisimulation is a congruence for the combined family. Thus get-result
uniqueness needs a reaction exclusion beyond these category conditions.
This does not assert a failure of complete observer reconstruction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeUnitReactionControls

open _root_.CategoryTheory
open Mettapedia.GSLT.RelativePushout Mettapedia.GSLT.RedexRelativeCongruence
open Mettapedia.OSLF.SortedCommutative
open SortedCommutativeInstruments Support
open SortedCommutativeInstrumentControls (Symbol arity)
open SortedCommutativeSourceControls (low)
open SortedCommutativeProbeSourceControls (ordered)
open SortedCommutativeProbeReconstructionControls (lowTarget)
open scoped BigOperators

def originalDeclarations (_ : Nat) : ReactionRule (.origin : ContextCategory arity) :=
  Source.mapReactionRule (unitSourceRule low)

def combinedRules (rule : ReactionRule (.origin : ContextCategory arity)) : Prop :=
  rules arity Nat rule ∨ ∃ origin : Nat, originalDeclarations origin = rule

def originalFiring (origin : Nat) :=
  unitGetFiring origin low (.ordinary Symbol.pair) ordered 0

def originalResult : (.origin : ContextCategory arity) ⟶ .interface .base :=
  RawArrow.value (classOf (.cut (signature := signature arity) (Parallel := Parallel arity)
    rfl (Source.embed low) (getAssay (.ordinary Symbol.pair) ordered 0)))

theorem the_original_redex_is_a_literal_binary_cut :
    (unitSourceRule low).redex = RawArrow.value
      (classOf (.cut rfl (.zero rfl) (.zero rfl) : Source.Value arity)) := rfl

theorem original_firing_keeps_the_full_result (origin : Nat) :
    (originalFiring origin).result = originalResult :=
  unitGetFiring_complete_result origin low (.ordinary Symbol.pair) ordered 0

theorem the_original_rule_really_fires (origin : Nat) :
    ActIPO combinedRules (getLabel (.ordinary Symbol.pair) 0)
      (RawArrow.value (sourceBundle (.ordinary Symbol.pair) ordered)) originalResult := by
  obtain ⟨rule, admitted, reaction, square, minimal, output⟩ := (originalFiring origin).step
  exact ⟨rule, Or.inr admitted, reaction, square, minimal, output⟩

theorem the_administrative_rule_still_fires :
    ActIPO combinedRules (getLabel (.ordinary Symbol.pair) 0)
      (RawArrow.value (sourceBundle (.ordinary Symbol.pair) ordered)) lowTarget := by
  obtain ⟨rule, admitted, reaction, square, minimal, output⟩ :=
    ((get_source_step_iff (arity := arity) (Origins := Nat) (.ordinary Symbol.pair)
      ordered 0 lowTarget).mpr ⟨⟨7⟩, rfl⟩)
  exact ⟨rule, Or.inl admitted, reaction, square, minimal, output⟩

theorem original_result_retains_three_fresh_heads : arrowObserverCount originalResult = 3 := by
  rw [← original_firing_keeps_the_full_result 7]
  exact unitGetFiring_observerCount 7 low (.ordinary Symbol.pair) ordered 0

theorem administrative_result_has_no_fresh_head : arrowObserverCount lowTarget = 0 :=
  observerCount_embed low

theorem the_two_actual_results_are_distinct : originalResult ≠ lowTarget := by
  intro same
  have support := congrArg arrowObserverCount same
  rw [original_result_retains_three_fresh_heads, administrative_result_has_no_fresh_head] at support
  cases support

theorem actual_get_result_is_not_unique :
    ActIPO combinedRules (getLabel (.ordinary Symbol.pair) 0)
        (RawArrow.value (sourceBundle (.ordinary Symbol.pair) ordered)) lowTarget ∧
      ActIPO combinedRules (getLabel (.ordinary Symbol.pair) 0)
        (RawArrow.value (sourceBundle (.ordinary Symbol.pair) ordered)) originalResult ∧
      lowTarget ≠ originalResult :=
  ⟨the_administrative_rule_still_fires, the_original_rule_really_fires 11,
    Ne.symm the_two_actual_results_are_distinct⟩

theorem identical_result_does_not_merge_original_origins :
    (originalFiring 7).result = (originalFiring 8).result ∧ originalFiring 7 ≠ originalFiring 8 :=
  ⟨(original_firing_keeps_the_full_result 7).trans (original_firing_keeps_the_full_result 8).symm,
    unitGetFiring_distinct_origins 7 8 (by decide) low (.ordinary Symbol.pair) ordered 0⟩

theorem no_original_receipt_has_an_empty_origin :
    ¬Nonempty (Source.FiringEvidence (.origin : ContextCategory arity) Empty
      (fun _ => Source.mapReactionRule (unitSourceRule low))) := by
  rintro ⟨receipt⟩
  exact Empty.elim receipt.occurrence

theorem every_origin_span_still_has_relative_pushouts
    {first second : ContextCategory arity}
    (agent : (.origin : ContextCategory arity) ⟶ first)
    (redex : (.origin : ContextCategory arity) ⟶ second) :
    HasRelativePushouts agent redex := raw_redex_relativePushouts agent redex

theorem combined_literal_bisimulation_is_a_context_congruence
    {source target : ContextCategory arity}
    {first second : (.origin : ContextCategory arity) ⟶ source}
    (related : IPOBisimilar combinedRules first second) (context : source ⟶ target) :
    IPOBisimilar combinedRules (first ≫ context) (second ≫ context) :=
  raw_bisimulation_congruence combinedRules related context

end Mettapedia.OSLF.Framework.SortedCommutativeUnitReactionControls
