import Mettapedia.OSLF.Framework.SortedTypedInstrumentUnitReactionCompetition
import Mettapedia.OSLF.Framework.SortedTypedInstrumentProbeControls

/-!
# Genuine typed unit competition and exact original-ask exclusion

An independently authored binary Cut unit rule competes with the process
get of a heterogeneous send bundle. Both are actual IPO firings at the same
input and label. The original result retains its entire assay and changed
process reactum; the administrative result is the selected pure child.
Origin data, zero-support conditional recovery and empty administrative
origin boundaries are checked independently of get-result uniqueness.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstrumentOriginalProbeControls

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence
open SortedTypedInstruments SortedTypedInstrumentControls SortedTypedInstrumentProbeControls

def originalRule : ReactionRule (.origin : SourceCategory sourceSignature sourceParallel) :=
  unitSourceRule (source := sourceSignature) (Parallel := sourceParallel) rfl (sourcePayload 11)

def originalRules (rule : ReactionRule (.origin : SourceCategory sourceSignature sourceParallel)) : Prop :=
  rule = originalRule

def originalFiring (origin : Nat) :=
  unitGetFiring origin sendHead (sendArguments 7 (sourcePayload 9)) 1 rfl (sourcePayload 11)

def originalResult : (.origin : ContextCategory sourceSignature sourceParallel) ⟶ .interface (.original .process) :=
  RawArrow.value (classOf (Term.cut (signature := signature sourceSignature sourceParallel)
    (Parallel := NativeParallel) (sort := .original .process) rfl (embed (sourcePayload 11))
      (getAssay sendHead (sendArguments 7 (sourcePayload 9)) 1)))

theorem original_redex_is_an_authored_proper_binary_cut :
    originalRule.redex = RawArrow.value
      (classOf (Term.cut (signature := sourceSignature) (Parallel := sourceParallel)
        (sort := .process) rfl (.zero rfl) (.zero rfl))) := rfl

theorem original_complete_result (origin : Nat) : (originalFiring origin).result = originalResult :=
  unitGetFiring_complete_result origin sendHead (sendArguments 7 (sourcePayload 9)) 1 rfl (sourcePayload 11)

theorem the_original_unit_rule_really_fires (origin : Nat) :
    ActIPO (Source.mappedRules originalRules) (probeLabel (.get sendHead 1))
      (RawArrow.value (classOf (bundle sendHead (sendArguments 7 (sourcePayload 9))))) originalResult := by
  refine ⟨Source.mapReactionRule originalRule, ⟨originalRule, rfl, rfl⟩,
    (originalFiring origin).reaction, (originalFiring origin).square, (originalFiring origin).minimal, ?_⟩
  exact (original_complete_result origin).symm

theorem original_result_has_three_observer_heads : arrowObserverCount originalResult = 3 := by
  have complete := unitGetFiring_observerCount 43 sendHead (sendArguments 7 (sourcePayload 9)) 1
    (show sourceParallel .process from rfl) (sourcePayload 11)
  calc
    arrowObserverCount originalResult = arrowObserverCount (originalFiring 43).result :=
      congrArg arrowObserverCount (original_complete_result 43).symm
    _ = 3 + ∑ other, observerCount (sendArguments 7 (sourcePayload 9) other) := complete
    _ = 3 := by
      rw [Fin.sum_univ_two]
      change 3 + (observerCount (embed (sourceName 7)) + observerCount (embed (sourcePayload 9))) = 3
      rw [observerCount_embed, observerCount_embed]

theorem the_selected_administrative_child_is_pure :
    arrowObserverCount (RawArrow.value (classOf (embed (sourcePayload 9))) :
      (.origin : ContextCategory sourceSignature sourceParallel) ⟶ .interface (.original .process)) = 0 :=
  observerCount_embed (sourcePayload 9)

theorem original_and_administrative_results_are_distinct :
    originalResult ≠ RawArrow.value (classOf (embed (sourcePayload 9))) := by
  intro same
  have counts := congrArg arrowObserverCount same
  rw [original_result_has_three_observer_heads, the_selected_administrative_child_is_pure] at counts
  omega

theorem actual_combined_get_result_is_not_unique :
    ActIPO (combinedSourceRules originalRules Nat) (probeLabel (.get sendHead 1))
        (RawArrow.value (classOf (bundle sendHead (sendArguments 7 (sourcePayload 9)))))
        (RawArrow.value (classOf (embed (sourcePayload 9)))) ∧
      ActIPO (combinedSourceRules originalRules Nat) (probeLabel (.get sendHead 1))
        (RawArrow.value (classOf (bundle sendHead (sendArguments 7 (sourcePayload 9))))) originalResult ∧
      originalResult ≠ RawArrow.value (classOf (embed (sourcePayload 9))) := by
  refine ⟨?_, ?_, original_and_administrative_results_are_distinct⟩
  · obtain ⟨rule, admitted, reaction, square, minimal, output⟩ :=
      (processGet 24 7 (sourcePayload 9)).direct_step
    exact ⟨rule, Or.inl admitted, reaction, square, minimal, output⟩
  · obtain ⟨rule, admitted, reaction, square, minimal, output⟩ := the_original_unit_rule_really_fires 43
    exact ⟨rule, Or.inr admitted, reaction, square, minimal, output⟩

theorem original_source_unit_cannot_supply_send_ask
    (observed : ValueClass (source := sourceSignature) (Parallel := sourceParallel) (.arguments sendHead)) :
    ¬ActIPO (Source.mappedRules originalRules) (probeLabel (.ask sendHead))
      (RawArrow.value (classOf (sourceNode sendHead (sendArguments 7 (sourcePayload 9)))))
      (RawArrow.value observed) :=
  source_rules_do_not_fire_under_ask originalRules sendHead _ _

theorem pure_matched_get_recovers_the_exact_nested_payload
    (observed : ValueClass (source := sourceSignature) (Parallel := sourceParallel) (.original .process))
    (pure : classObserverCount observed = 0)
    (step : ActIPO (combinedSourceRules originalRules Nat) (probeLabel (.get sendHead 1))
      (RawArrow.value (classOf (bundle sendHead (sendArguments 7 (sourcePayload 9))))) (RawArrow.value observed)) :
    observed = classOf (embed (sourcePayload 9)) :=
  (combined_get_pure_result_readout originalRules sendHead (sendArguments 7 (sourcePayload 9)) 1
    observed pure step).2

theorem same_full_original_target_does_not_merge_origins :
    (originalFiring 43).result = (originalFiring 44).result ∧ originalFiring 43 ≠ originalFiring 44 :=
  ⟨(original_complete_result 43).trans (original_complete_result 44).symm,
    unitGetFiring_distinct_origins 43 44 (by omega) sendHead (sendArguments 7 (sourcePayload 9)) 1 rfl
      (sourcePayload 11)⟩

theorem empty_administrative_origins_do_not_remove_original_firings :
    ActIPO (combinedSourceRules originalRules Empty) (probeLabel (.get sendHead 1))
      (RawArrow.value (classOf (bundle sendHead (sendArguments 7 (sourcePayload 9))))) originalResult := by
  obtain ⟨rule, admitted, reaction, square, minimal, output⟩ := the_original_unit_rule_really_fires 43
  exact ⟨rule, Or.inr admitted, reaction, square, minimal, output⟩

theorem empty_administrative_origins_cannot_supply_the_pure_child :
    ¬ActIPO (combinedSourceRules originalRules Empty) (probeLabel (.get sendHead 1))
      (RawArrow.value (classOf (bundle sendHead (sendArguments 7 (sourcePayload 9)))))
      (RawArrow.value (classOf (embed (sourcePayload 9)))) := by
  intro step
  have pure : classObserverCount (classOf (embed (sourcePayload 9))) = 0 :=
    observerCount_embed (sourcePayload 9)
  have origin := (combined_get_pure_result_readout originalRules sendHead (sendArguments 7 (sourcePayload 9)) 1
    (classOf (embed (sourcePayload 9))) pure step).1
  exact origin.elim Empty.elim

end Mettapedia.OSLF.Framework.SortedTypedInstrumentOriginalProbeControls
