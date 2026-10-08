import Mettapedia.OSLF.Framework.SortedTypedInstrumentSourceFiringComparison
import Mettapedia.OSLF.Framework.SortedTypedInstrumentRPOControls

/-!
# Complete channel rewrites, typed reaction frames and retained origins

An original channel rule changes its name inside a genuinely heterogeneous
send frame. The process sibling is retained whole, including its own nested
channel. Native firing receipts preserve the exact reaction frame, result
and independently supplied declaration occurrence; duplicate declarations
therefore still give distinct receipts.

An observer-bearing process value has positive support and cannot be an
original-rule result at an original agent and label. Empty occurrence types
have no firing receipts. These boundaries do not assert total source-sort
inhabitation or uniqueness of a context from its ground action.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstrumentSourceFiringControls

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RelativePushout Mettapedia.GSLT.RedexRelativeCongruence
open SortedTypedInstruments SortedTypedInstruments.Source
open SortedTypedInstrumentControls SortedTypedInstrumentSourceControls

private theorem left_identity_isIPO
    {first second : SourceCategory sourceSignature sourceParallel}
    {agent : (.origin : SourceCategory sourceSignature sourceParallel) ⟶ first}
    {redex : (.origin : SourceCategory sourceSignature sourceParallel) ⟶ second}
    (reaction : second ⟶ first) (square : agent = redex ≫ reaction) :
    IsIdemPushout agent redex (𝟙 first) reaction
      ((Category.comp_id agent).trans square) := by
  intro candidate
  refine ⟨candidate.inl, ?_, ?_⟩
  · refine ⟨Category.id_comp _, ?_, candidate.fac_left⟩
    change reaction ≫ candidate.inl = candidate.inr
    apply (cancel_mono candidate.down).mp
    rw [Category.assoc, candidate.fac_left, Category.comp_id, candidate.fac_right]
  · intro other laws
    exact (cancel_mono candidate.down).mp (laws.2.2.trans candidate.fac_left.symm)

def channelRule (before after : Nat) :
    ReactionRule (.origin : SourceCategory sourceSignature sourceParallel) where
  codomain := .interface .channel
  redex := RawArrow.value (classOf (sourceName before))
  reactum := RawArrow.value (classOf (sourceName after))

def declarations (before after : Nat) (_occurrence : Nat) :
    ReactionRule (.origin : SourceCategory sourceSignature sourceParallel) := channelRule before after

def completeAgent (name : Nat) (payload : SourceValue .process) :
    (.origin : SourceCategory sourceSignature sourceParallel) ⟶ .interface .process :=
  RawArrow.value (classOf ((sendContext payload).fill (sourceName name)))

def completeReaction (payload : SourceValue .process) :
    (.interface .channel : SourceCategory sourceSignature sourceParallel) ⟶ .interface .process :=
  RawArrow.context (contextClassOf (sendContext payload))

def originalReceipt (occurrence before after : Nat) (payload : SourceValue .process) :
    FiringAt Nat (declarations before after) (completeAgent before payload) (𝟙 _) where
  occurrence := occurrence
  reaction := completeReaction payload
  square := Category.comp_id _
  minimal := left_identity_isIPO (completeReaction payload) rfl

theorem actual_original_channel_firing (occurrence before after : Nat) (payload : SourceValue .process) :
    ActIPO (fun rule => ∃ position, declarations before after position = rule)
      (𝟙 (.interface .process)) (completeAgent before payload)
      (RawArrow.value (classOf ((sendContext payload).fill (sourceName after)))) :=
  (originalReceipt occurrence before after payload).step

theorem full_native_reaction_frame_is_retained (occurrence before after : Nat)
    (payload : SourceValue .process) :
    (mapFiring (declarations before after) (originalReceipt occurrence before after payload)).reaction =
      RawArrow.context (contextClassOf (embedContext (sendContext payload))) := rfl

theorem native_target_keeps_the_rewritten_channel_and_nested_process :
    (mapFiring (declarations 7 11) (originalReceipt 24 7 11 (sourcePayload 9))).result =
      RawArrow.value (classOf (embed
        (Term.node (signature := sourceSignature) (Parallel := sourceParallel) Symbol.send
          (Fin.cases (motive := fun position => SourceValue (sourceSignature.input Symbol.send position))
            (sourceName 11) (fun _ => sourcePayload 9))))) := by
  rw [mapFiring_result]
  change (inclusion sourceSignature sourceParallel).map
    (RawArrow.value (classOf ((sendContext (sourcePayload 9)).fill (sourceName 11)))) = _
  rw [complete_source_filling]
  rfl

theorem every_native_receipt_at_this_actual_bound_has_unique_whole_source_readback
    (supplied : FiringAt Nat (fun occurrence => mapReactionRule (declarations 7 11 occurrence))
      ((inclusion sourceSignature sourceParallel).map (completeAgent 7 (sourcePayload 9)))
      ((inclusion sourceSignature sourceParallel).map
        (𝟙 (.interface .process : SourceCategory sourceSignature sourceParallel)))) :
    ∃! before : FiringAt Nat (declarations 7 11) (completeAgent 7 (sourcePayload 9)) (𝟙 _),
      mapFiring (declarations 7 11) before = supplied :=
  native_firing_unique_reconstruction (declarations 7 11) supplied

theorem duplicate_declaration_occurrences_have_equal_whole_targets_but_distinct_receipts :
    (mapFiring (declarations 7 11) (originalReceipt 24 7 11 (sourcePayload 9))).result =
      (mapFiring (declarations 7 11) (originalReceipt 25 7 11 (sourcePayload 9))).result ∧
    mapFiring (declarations 7 11) (originalReceipt 24 7 11 (sourcePayload 9)) ≠
      mapFiring (declarations 7 11) (originalReceipt 25 7 11 (sourcePayload 9)) := by
  refine ⟨rfl, distinct_origins_keep_distinct_firings (declarations 7 11) _ _ ?_⟩
  change (24 : Nat) ≠ 25
  omega

theorem forgetting_the_selected_origin_is_not_injective :
    ¬Function.Injective (fun supplied : FiringAt Nat (declarations 7 11)
      (completeAgent 7 (sourcePayload 9)) (𝟙 _) => supplied.result) := by
  intro injective
  have same := injective (show (originalReceipt 24 7 11 (sourcePayload 9)).result =
    (originalReceipt 25 7 11 (sourcePayload 9)).result from rfl)
  have positions := congrArg (fun supplied : FiringAt Nat (declarations 7 11)
    (completeAgent 7 (sourcePayload 9)) (𝟙 _) => supplied.occurrence) same
  change (24 : Nat) = 25 at positions
  omega

def observerProcess : NativeValue (.original .process) :=
  cut (source := sourceSignature) (Parallel := sourceParallel) (.get (.ordinary Symbol.send) 1)
    (probe (source := sourceSignature) (Parallel := sourceParallel) (.get (.ordinary Symbol.send) 1))
    (bundle (source := sourceSignature) (Parallel := sourceParallel) (.ordinary Symbol.send)
      (sendArguments 7 (sourcePayload 9)))

theorem observer_process_has_positive_class_support :
    classObserverCount (classOf observerProcess) ≠ 0 := by
  change observerCount observerProcess ≠ 0
  change 1 + _ ≠ 0
  omega

theorem original_rules_cannot_emit_the_observer_bearing_process_at_this_bound :
    ¬ActIPO (mappedRules (fun rule => ∃ position, declarations 7 11 position = rule))
      ((inclusion sourceSignature sourceParallel).map
        (𝟙 (.interface .process : SourceCategory sourceSignature sourceParallel)))
      ((inclusion sourceSignature sourceParallel).map (completeAgent 7 (sourcePayload 9)))
      (RawArrow.value (classOf observerProcess) :
        (.origin : ContextCategory sourceSignature sourceParallel) ⟶ .interface (.original .process)) := by
  intro step
  have pure := source_step_full_target_support _ (completeAgent 7 (sourcePayload 9)) (𝟙 _) _ step
  change classObserverCount (classOf observerProcess) = 0 at pure
  exact observer_process_has_positive_class_support pure

theorem an_empty_occurrence_type_has_no_receipt
    (emptyDeclarations : Empty → ReactionRule (.origin : SourceCategory sourceSignature sourceParallel)) :
    ¬Nonempty (FiringAt Empty emptyDeclarations (completeAgent 7 (sourcePayload 9)) (𝟙 _)) := by
  rintro ⟨supplied⟩
  exact supplied.occurrence.elim

end Mettapedia.OSLF.Framework.SortedTypedInstrumentSourceFiringControls
