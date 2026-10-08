import Mettapedia.OSLF.Framework.SortedTypedInstrumentKitRPOComparison
import Mettapedia.OSLF.Framework.SortedTypedInstrumentSourceFiringComparison
import Mettapedia.OSLF.Framework.SortedTypedInstrumentControls
import Mettapedia.OSLF.Syntax.SortedCommutativeContextMonomorphisms
import Mettapedia.OSLF.Syntax.SortedCommutativeConstructorReadout

/-!
# Actual typed kit arrows, minimal assays and nonfull expansion

The send kit retains an independently supplied channel and nested process in
the whole administrative bundle. Its actual ask square is an IPO in the kit
category, and the firing retains duplicate authored origins. Opening the kit
adds a genuine probe arrow with no old preimage. Original source terms remain
available and actual unit padding retains their complete equation classes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstrumentKitControls

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RelativePushout Mettapedia.GSLT.RedexRelativeCongruence
open SortedTypedInstruments SortedTypedInstrumentControls

def closedKit : Kit.Policy sourceSignature sourceParallel := fun head => head ≠ head
def sendKit : Kit.Policy sourceSignature sourceParallel := fun head => head = .ordinary Symbol.send

theorem opensSend : ∀ head, closedKit head → sendKit head := fun _head impossible => (impossible rfl).elim

def sendHead : SourceHead sourceSignature sourceParallel := .ordinary Symbol.send
def arguments := sendArguments 7 (sourcePayload 9)

theorem all_complete_arguments_are_supported : ∀ position, Kit.Supported sendKit (arguments position) := by
  intro position
  fin_cases position
  · exact Kit.embed_supported sendKit (sourceName 7)
  · exact Kit.embed_supported sendKit (sourcePayload 9)

theorem whole_body_is_supported : Kit.Supported sendKit (sourceNode sendHead arguments) :=
  .node (Kit.Allowed.original (opened := sendKit) Symbol.send) all_complete_arguments_are_supported

theorem whole_bundle_is_supported : Kit.Supported sendKit (bundle sendHead arguments) :=
  .node (.arguments sendHead rfl) all_complete_arguments_are_supported

theorem whole_probe_context_is_supported : Kit.ContextSupported sendKit (probeContext (.ask sendHead)) := by
  refine .frame (.cut (.ask sendHead) rfl) ?_ (.hole _)
  intro other different
  fin_cases other
  · exact .node (.probe (.ask sendHead) rfl) (fun absent => Fin.elim0 absent)
  · exact (different rfl).elim

def agent : Kit.origin sendKit ⟶ Kit.interface sendKit (.original .process) :=
  Kit.value (classOf (sourceNode sendHead arguments)) ⟨_, whole_body_is_supported, rfl⟩

def label : Kit.interface sendKit (.original .process) ⟶ Kit.interface sendKit (.arguments sendHead) :=
  Kit.context (contextClassOf (probeContext (.ask sendHead))) ⟨_, whole_probe_context_is_supported, rfl⟩

def output : Kit.origin sendKit ⟶ Kit.interface sendKit (.arguments sendHead) :=
  Kit.value (classOf (bundle sendHead arguments)) ⟨_, whole_bundle_is_supported, rfl⟩

def askRule : ReactionRule (Kit.origin sendKit) where
  codomain := Kit.interface sendKit (.arguments sendHead)
  redex := agent ≫ label
  reactum := output

theorem complete_actual_ask_square : agent ≫ label = askRule.redex ≫ 𝟙 _ :=
  (Category.comp_id askRule.redex).symm

theorem complete_actual_ask_is_minimal :
    IsIdemPushout agent askRule.redex label (𝟙 _) complete_actual_ask_square := by
  apply (Kit.idemPushout_iff complete_actual_ask_square).mpr
  exact raw_right_identity_isIPO label.val rfl

def firing (origin : Nat) : Source.FiringAt Nat (fun _ => askRule) agent label where
  occurrence := origin
  reaction := 𝟙 _
  square := complete_actual_ask_square
  minimal := complete_actual_ask_is_minimal

theorem complete_firing_result : (firing 24).result = output := Category.comp_id output

theorem the_whole_channel_and_nested_process_are_retained :
    (Kit.inclusion sendKit).map (firing 24).result =
      RawArrow.value (classOf (bundle sendHead (sendArguments 7 (sourcePayload 9)))) := by
  rw [complete_firing_result]
  rfl

theorem the_original_probe_redex_is_recovered :
    (Kit.inclusion sendKit).map askRule.redex =
      (sendAsk 24 7 (sourcePayload 9)).rule.redex :=
  (sendAsk 24 7 (sourcePayload 9)).complete_probe_square

theorem erasing_the_nested_process_changes_the_complete_firing_result :
    (Kit.inclusion sendKit).map (firing 24).result ≠
      RawArrow.value (classOf (bundle sendHead (sendArguments 7 (.zero rfl)))) := by
  intro same
  rw [the_whole_channel_and_nested_process_are_retained] at same
  have coordinates := (node_class_eq_iff (signature := signature sourceSignature sourceParallel)
    (Parallel := NativeParallel) (Constructor.arguments sendHead) _ _).mp (RawArrow.value.inj same)
  have processRead : classEmbedding (classOf (sourcePayload 9)) =
      classEmbedding (classOf (.zero rfl : SourceValue .process)) := by
    change classOf (embed (sourcePayload 9)) = classOf (embed (.zero rfl : SourceValue .process))
    simpa only [sendArguments, Fin.cases_succ] using coordinates (Fin.succ (0 : Fin 1))
  have counts := congrArg (fun supplied => (inventoryQ supplied).card) (classEmbedding_injective processRead)
  change 1 = 0 at counts
  omega

theorem duplicate_authored_origins_remain_distinct : firing 24 ≠ firing 25 := by
  intro same
  have origins : 24 = 25 := congrArg Source.FiringAt.occurrence same
  omega

theorem every_competing_candidate_and_mediator_has_the_actual_kit_readout
    (candidate : Candidate agent askRule.redex label (𝟙 _)) :
    IsRelativePushout candidate ↔
      IsRelativePushout (mapCandidate (Kit.inclusion sendKit) candidate) :=
  Kit.relativePushout_iff candidate

theorem actual_redex_relative_pushouts_exist : HasRelativePushouts agent askRule.redex :=
  Kit.redex_relativePushouts agent askRule.redex

theorem the_actual_all_label_context_congruence (rules : ReactionRule (Kit.origin sendKit) → Prop)
    {first second : Kit.Object sendKit} {before after : Kit.origin sendKit ⟶ first}
    (related : IPOBisimilar rules before after) (context : first ⟶ second) :
    IPOBisimilar rules (before ≫ context) (after ≫ context) :=
  Kit.bisimulation_context_congruence rules related context

theorem a_missing_probe_is_not_supported :
    ¬Kit.ArrowSupported closedKit (RawArrow.value
      (classOf (probe (.ask sendHead))) : (.origin : ContextCategory sourceSignature sourceParallel) ⟶
        .interface (.probe (.ask sendHead))) := by
  intro supported
  have zero := (Kit.arrow_supported_iff_weight_zero closedKit _).mp supported
  change HereditaryWeight.term (Kit.constructorWeight closedKit) (probe (.ask sendHead)) = 0 at zero
  unfold probe at zero
  rw [HereditaryWeight.term_node] at zero
  simp only [Finset.univ_eq_empty, Finset.sum_empty, Nat.add_zero] at zero
  exact (Kit.permissionWeight_zero_iff closedKit sendHead).mp zero rfl

def freshProbe : Kit.origin sendKit ⟶ Kit.interface sendKit (.probe (.ask sendHead)) :=
  Kit.value (classOf (probe (.ask sendHead)))
    ⟨_, Kit.Supported.node (opened := sendKit) (.probe (.ask sendHead) rfl) (fun absent => Fin.elim0 absent), rfl⟩

theorem opening_the_kit_adds_an_actual_arrow : ¬(Kit.expand opensSend).Full := by
  intro full
  obtain ⟨before, read⟩ := full.map_surjective freshProbe
  have complete : before.val = freshProbe.val :=
    congrArg (fun arrow : Kit.origin sendKit ⟶ Kit.interface sendKit (.probe (.ask sendHead)) => arrow.val) read
  have supported : Kit.ArrowSupported closedKit freshProbe.val := by
    rw [← complete]
    exact before.property
  exact a_missing_probe_is_not_supported supported

theorem an_unopened_original_source_still_has_its_complete_value :
    ((Kit.sourceInclusion closedKit).map
      (RawArrow.value (classOf (sourcePayload 9)))).val =
        RawArrow.value (classOf (embed (sourcePayload 9))) := rfl

theorem source_unit_padding_preserves_the_supported_complete_arrow :
    (Kit.sourceInclusion closedKit).map (RawArrow.value
      (classOf (.cut (signature := sourceSignature) (Parallel := sourceParallel)
        (sort := .process) rfl (sourcePayload 9) (.zero rfl)))) =
      (Kit.sourceInclusion closedKit).map (RawArrow.value (classOf (sourcePayload 9))) := by
  exact congrArg (Kit.sourceInclusion closedKit).map (congrArg RawArrow.value
    (Quotient.sound (Equation.unit (signature := sourceSignature) (Parallel := sourceParallel) rfl (sourcePayload 9))))

end Mettapedia.OSLF.Framework.SortedTypedInstrumentKitControls
