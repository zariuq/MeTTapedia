import Mettapedia.OSLF.Framework.SortedTypedInstrumentCombinedReconstruction
import Mettapedia.OSLF.Framework.SortedTypedInstrumentOriginalProbeControls

/-!
# Actual typed observer separation with unit-rule competition

Complete administrative probes separate one process occurrence from two,
and different channel values nested inside the same process constructor.
These statements concern actual IPO bisimilarity, rather than membership
in a selected witness relation. AC1 commutativity remains respected.

The original binary unit rule still has a genuine competing get firing.
Its observer-bearing result cannot match any pure source process. The
nonidentity source context retains both its changed input and complete
channel sibling. All reconstruction claims here use literal categorical
labels and explicitly inhabited administrative origins.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstrumentCombinedReconstructionControls

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence
open SortedTypedInstruments SortedTypedInstrumentControls
open SortedTypedInstrumentProbeControls SortedTypedInstrumentOriginalProbeControls

def combinedRules := combinedSourceRules originalRules Nat

theorem actual_observer_bisimilarity_separates_process_multiplicity :
    ¬IPOBisimilar combinedRules
      (RawArrow.value (classOf (embed (sourcePayload 9))))
      (RawArrow.value (classOf (embed (.cut rfl (sourcePayload 9) (sourcePayload 9))))) := by
  intro related
  have sourceSame := (combined_observer_bisimilar_iff_source_equal_all_rules
    originalRules (Origins := Nat) ⟨24⟩ (classOf (sourcePayload 9))
      (classOf (.cut rfl (sourcePayload 9) (sourcePayload 9)))).mp related
  have counts := congrArg (fun supplied => (inventoryQ supplied).card) sourceSame
  change 1 = 1 + 1 at counts
  omega

theorem actual_observer_bisimilarity_separates_complete_nested_channels :
    ¬IPOBisimilar combinedRules
      (RawArrow.value (classOf (embed (sourcePayload 7))))
      (RawArrow.value (classOf (embed (sourcePayload 11)))) := by
  intro related
  have nativeSame := (combined_observer_bisimilar_iff_embedded_equal
    originalRules (Origins := Nat) ⟨24⟩ (classOf (sourcePayload 7))
      (classOf (embed (sourcePayload 11)))).mp related
  have coordinates := (node_class_eq_iff (signature := signature sourceSignature sourceParallel)
    (Parallel := NativeParallel) (Constructor.original Symbol.send) _ _).mp nativeSame
  exact different_channel_indices_remain_distinct 7 11 (by omega) (coordinates 0)

theorem actual_observer_bisimilarity_respects_the_proper_cut_equation :
    IPOBisimilar combinedRules
      (RawArrow.value (classOf (embed (.cut rfl (sourcePayload 7) (sourcePayload 9)))))
      (RawArrow.value (classOf (embed (.cut rfl (sourcePayload 9) (sourcePayload 7))))) :=
  (combined_observer_raw_bisimilar_iff_source_equation_all_rules
      originalRules (Origins := Nat) ⟨24⟩ _ _).mpr
        (Equation.comm (signature := sourceSignature) (Parallel := sourceParallel)
          (sort := .process) rfl (sourcePayload 7) (sourcePayload 9))

theorem no_pure_source_can_match_the_actual_competing_original_result
    (supplied : Class sourceSignature sourceParallel .process) :
    ¬IPOBisimilar combinedRules (RawArrow.value (classEmbedding supplied)) originalResult := by
  intro related
  have recovered := (combined_observer_bisimilar_iff_embedded_equal
    originalRules (Origins := Nat) ⟨24⟩ supplied
      (classOf (.cut (signature := signature sourceSignature sourceParallel)
        (Parallel := NativeParallel) (sort := .original .process)
        rfl (embed (sourcePayload 11))
          (getAssay sendHead (sendArguments 7 (sourcePayload 9)) 1)))).mp related
  have supports := congrArg (fun value => arrowObserverCount
    (RawArrow.value value : (.origin : ContextCategory sourceSignature sourceParallel) ⟶
      .interface (.original .process))) recovered
  have pure : arrowObserverCount (RawArrow.value (classEmbedding supplied) :
      (.origin : ContextCategory sourceSignature sourceParallel) ⟶ .interface (.original .process)) = 0 :=
    classObserverCount_embedding supplied
  rw [pure] at supports
  change 0 = arrowObserverCount originalResult at supports
  rw [original_result_has_three_observer_heads] at supports
  omega

theorem genuine_unit_get_competition_and_complete_future_separation :
    ActIPO combinedRules (probeLabel (.get sendHead 1))
        (RawArrow.value (classOf (bundle sendHead (sendArguments 7 (sourcePayload 9)))))
        originalResult ∧
      ¬IPOBisimilar combinedRules (RawArrow.value (classOf (embed (sourcePayload 9)))) originalResult := by
  exact ⟨actual_combined_get_result_is_not_unique.2.1,
    no_pure_source_can_match_the_actual_competing_original_result (classOf (sourcePayload 9))⟩

def processContext : RawContext sourceSignature sourceParallel .process .process :=
  RawContext.frame (signature := sourceSignature) (Parallel := sourceParallel) Symbol.send 1
    (Fin.cases (motive := fun other => other ≠ 1 → SourceValue (sourceSignature.input Symbol.send other))
      (fun _ => sourceName 11) (fun other absent => by
        have zero : other = 0 := Subsingleton.elim other 0
        subst other
        exact (absent rfl).elim)) .hole

theorem complete_nonidentity_context_preserves_observer_equivalence :
    IPOBisimilar combinedRules
      (RawArrow.value (classEmbedding ((contextClassOf processContext).fill
        (classOf (.cut rfl (sourcePayload 7) (sourcePayload 9))))))
      (RawArrow.value (classEmbedding ((contextClassOf processContext).fill
        (classOf (.cut rfl (sourcePayload 9) (sourcePayload 7)))))) :=
  combined_source_context_congruence originalRules (Origins := Nat) ⟨24⟩
    (contextClassOf processContext) actual_observer_bisimilarity_respects_the_proper_cut_equation

theorem the_context_retains_its_whole_channel_and_process_input (supplied : SourceValue .process) :
    processContext.fill supplied =
      Term.node (signature := sourceSignature) (Parallel := sourceParallel) Symbol.send
        (Fin.cases (motive := fun position => SourceValue (sourceSignature.input Symbol.send position))
          (sourceName 11) (fun _ => supplied)) := by
  change Term.node (signature := sourceSignature) (Parallel := sourceParallel) Symbol.send _ = _
  apply congrArg (Term.node (signature := sourceSignature) (Parallel := sourceParallel) Symbol.send)
  funext position
  fin_cases position <;> rfl

theorem the_actual_context_is_not_identity :
    contextClassOf processContext ≠ ContextClass.identity (signature := sourceSignature)
      (Parallel := sourceParallel) .process := by
  intro same
  have filled := congrArg (fun context : ContextClass sourceSignature sourceParallel .process .process =>
    (inventoryQ (context.fill (classOf (.zero rfl)))).card) same
  change 1 = 0 at filled
  omega

end Mettapedia.OSLF.Framework.SortedTypedInstrumentCombinedReconstructionControls
