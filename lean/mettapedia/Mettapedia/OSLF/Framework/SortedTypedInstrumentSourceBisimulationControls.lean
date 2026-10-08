import Mettapedia.OSLF.Framework.SortedTypedInstrumentSourceBisimulation
import Mettapedia.OSLF.Framework.SortedTypedInstrumentRPOControls

/-!
# Proper many-sorted behavior and complete source-context congruence

An independently authored echo rule is available at each complete source
agent, including arbitrary sorted interfaces. Its actual IPO firings keep
the filled source value. Equality of source AC1 inventory multiplicity is
an earned bisimulation: every complete sorted context preserves that
relation. It relates distinct channel values, while separating process
values of different multiplicity.

The actual native relation admits exactly zero-support labels and mapped
original rules. Its source comparison and channel-to-process congruence
are earned from the full firing reconstruction. This is not full
administrative observation equivalence or value equality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstrumentSourceBisimulationControls

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence
open SortedTypedInstruments SortedTypedInstruments.Source
open SortedTypedInstrumentControls SortedTypedInstrumentSourceControls

abbrev Original := SourceCategory sourceSignature sourceParallel

def echoRule {interface : Original} (supplied : (.origin : Original) ⟶ interface) :
    ReactionRule (.origin : Original) where
  codomain := interface
  redex := supplied
  reactum := supplied

def echoRules : ReactionRule (.origin : Original) → Prop :=
  fun rule => ∃ interface : Original, ∃ supplied : (.origin : Original) ⟶ interface,
    echoRule supplied = rule

theorem actual_echo_firing {interface nextInterface : Original}
    (agent : (.origin : Original) ⟶ interface) (label : interface ⟶ nextInterface) :
    ActIPO echoRules label agent (agent ≫ label) :=
  ⟨echoRule (agent ≫ label), ⟨nextInterface, agent ≫ label, rfl⟩, 𝟙 _,
    (Category.comp_id _).symm, raw_right_identity_isIPO label rfl, (Category.comp_id _).symm⟩

theorem echo_step_complete_readout {interface nextInterface : Original}
    (agent : (.origin : Original) ⟶ interface) (label : interface ⟶ nextInterface)
    (result : (.origin : Original) ⟶ nextInterface) (step : ActIPO echoRules label agent result) :
    result = agent ≫ label := by
  obtain ⟨rule, ⟨_, supplied, rfl⟩, reaction, square, _, output⟩ := step
  exact output.trans square.symm

def multiplicity : {interface : Original} → ((.origin : Original) ⟶ interface) → Nat
  | _, .identity => 0
  | _, .value supplied => (inventoryQ supplied).card

def sameMultiplicity (interface : Original)
    (before after : (.origin : Original) ⟶ interface) : Prop :=
  multiplicity before = multiplicity after

private theorem raw_fill_preserves_multiplicity {first second : DataSort}
    (context : RawContext sourceSignature sourceParallel first second) :
    ∀ before after : SourceValue first,
      (inventory before).card = (inventory after).card →
        (inventory (context.fill before)).card = (inventory (context.fill after)).card := by
  apply @RawContext.rec sourceSignature sourceParallel first
    (fun _ context => ∀ before after : SourceValue first,
      (inventory before).card = (inventory after).card →
        (inventory (context.fill before)).card = (inventory (context.fill after)).card) (t := context)
  · intro before after same
    exact same
  · intro constructor position siblings inner _inductionHypothesis before after _same
    simp only [RawContext.fill, inventory, Multiset.card_singleton]
  · intro sort parallel inner sibling inductionHypothesis before after same
    simpa only [RawContext.fill, inventory, Multiset.card_add] using
      congrArg (fun count => count + (inventory sibling).card) (inductionHypothesis before after same)
  · intro sort parallel sibling inner inductionHypothesis before after same
    simpa only [RawContext.fill, inventory, Multiset.card_add] using
      congrArg (fun count => (inventory sibling).card + count) (inductionHypothesis before after same)

theorem all_sorted_source_contexts_preserve_multiplicity {first second : DataSort}
    (context : ContextClass sourceSignature sourceParallel first second)
    (before after : Class sourceSignature sourceParallel first) :
    (inventoryQ before).card = (inventoryQ after).card →
      (inventoryQ (context.fill before)).card = (inventoryQ (context.fill after)).card :=
  Quotient.inductionOn₃ context before after raw_fill_preserves_multiplicity

theorem all_source_labels_preserve_multiplicity {interface nextInterface : Original}
    (before after : (.origin : Original) ⟶ interface)
    (same : sameMultiplicity interface before after) (label : interface ⟶ nextInterface) :
    sameMultiplicity nextInterface (before ≫ label) (after ≫ label) := by
  cases before with
  | identity => cases after; cases label <;> rfl
  | value before =>
    cases after with
    | value after =>
      cases label with
      | context context => exact all_sorted_source_contexts_preserve_multiplicity context before after same

theorem actual_many_sorted_echo_bisimulation : IsIPOBisimulation echoRules sameMultiplicity := by
  intro interface before after same
  refine ⟨?_, ?_⟩
  · intro nextInterface label next step
    refine ⟨after ≫ label, actual_echo_firing after label, ?_⟩
    rw [echo_step_complete_readout before label next step]
    exact all_source_labels_preserve_multiplicity before after same label
  · intro nextInterface label next step
    refine ⟨before ≫ label, actual_echo_firing before label, ?_⟩
    rw [echo_step_complete_readout after label next step]
    exact all_source_labels_preserve_multiplicity before after same label

def nameAgent (index : Nat) : (.origin : Original) ⟶ .interface .channel :=
  RawArrow.value (classOf (sourceName index))

theorem actual_distinct_channel_values_are_bisimilar :
    IPOBisimilar echoRules (nameAgent 7) (nameAgent 11) :=
  ⟨sameMultiplicity, actual_many_sorted_echo_bisimulation, rfl⟩

theorem their_complete_equation_classes_remain_distinct : nameAgent 7 ≠ nameAgent 11 := by
  intro same
  have native := congrArg (inclusion sourceSignature sourceParallel).map same
  exact different_channel_indices_remain_distinct 7 11 (by omega) (RawArrow.value.inj native)

theorem the_source_behavior_relation_is_proper :
    ¬sameMultiplicity (.interface .process)
      (RawArrow.value (classOf (sourcePayload 9)))
      (RawArrow.value (classOf (Term.cut rfl (sourcePayload 9) (sourcePayload 9)))) := by
  change 1 = 1 + 1 → False
  omega

theorem the_actual_typed_native_relation_compares_the_distinct_channel_values :
    ZeroSupportBisimilar echoRules
      ((inclusion sourceSignature sourceParallel).map (nameAgent 7))
      ((inclusion sourceSignature sourceParallel).map (nameAgent 11)) :=
  (bisimilar_iff_zeroSupport echoRules _ _).mp actual_distinct_channel_values_are_bisimilar

theorem heterogeneous_complete_source_context_preserves_the_native_relation :
    ZeroSupportBisimilar echoRules
      ((inclusion sourceSignature sourceParallel).map (nameAgent 7) ≫
        (inclusion sourceSignature sourceParallel).map
          (RawArrow.context (contextClassOf (sendContext (sourcePayload 9)))))
      ((inclusion sourceSignature sourceParallel).map (nameAgent 11) ≫
        (inclusion sourceSignature sourceParallel).map
          (RawArrow.context (contextClassOf (sendContext (sourcePayload 9))))) :=
  zeroSupport_bisimilar_source_context echoRules
    the_actual_typed_native_relation_compares_the_distinct_channel_values _

end Mettapedia.OSLF.Framework.SortedTypedInstrumentSourceBisimulationControls
