import Mettapedia.OSLF.Framework.SortedCommutativeSourceBisimulation
import Mettapedia.OSLF.Framework.SortedCommutativeSourceComparisonControls

/-!
# A nonempty reaction family and genuine pure-label bisimulation controls

The auxiliary echo family contains an actual redex/reactum declaration for
every supplied source value. Every context label fires, with its complete
filled value as target. Independently defined outer-inventory multiplicity
is a proper bisimulation relation for this family: distinct constructor
values are related, while one and two parallel particles are not.

The native comparison and source-context congruence apply to these actual
firings. A genuine administrative observer firing has positive label
support and is excluded. No equality with structural observation, full
administrative bisimulation or the interactive current-view kernel follows.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeSourceBisimulationControls

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence
open SortedCommutativeInstruments Support
open SortedCommutativeInstrumentControls (Symbol arity)
open SortedCommutativeSourceControls (low high sourceCut)
open SortedCommutativeSourceComparisonControls (interactionLabel)

abbrev SourceCategory := Source.SourceCategory (arity := arity)
abbrev sourceInterface : SourceCategory := .interface (ULift.up ())

def echoRule (supplied : Source.ValueClass arity) : ReactionRule (.origin : SourceCategory) where
  codomain := sourceInterface
  redex := RawArrow.value supplied
  reactum := RawArrow.value supplied

def echoRules (rule : ReactionRule (.origin : SourceCategory)) : Prop :=
  ∃ supplied : Source.ValueClass arity, echoRule supplied = rule

theorem actual_nonempty_reaction_family : echoRules (echoRule (classOf low)) :=
  ⟨classOf low, rfl⟩

theorem every_redex_has_a_proper_cut_representative (supplied : Source.ValueClass arity) :
    ∃ raw : Source.Value arity, (echoRule supplied).redex =
      RawArrow.value (classOf (.cut rfl raw (.zero rfl) : Source.Value arity)) := by
  refine Quotient.inductionOn supplied (fun raw => ⟨raw, ?_⟩)
  exact congrArg RawArrow.value (Quotient.sound
    (Equation.unit (signature := Source.signature arity) (Parallel := Source.Parallel arity) rfl raw)).symm

theorem echo_step_readout {interface nextInterface : SourceCategory}
    (agent : (.origin : SourceCategory) ⟶ interface) (label : interface ⟶ nextInterface)
    (next : (.origin : SourceCategory) ⟶ nextInterface)
    (step : ActIPO echoRules label agent next) : next = agent ≫ label := by
  obtain ⟨rule, ⟨supplied, rfl⟩, reaction, square, _minimal, result⟩ := step
  exact result.trans square.symm

theorem echo_context_fires {interface : SourceCategory}
    (agent : (.origin : SourceCategory) ⟶ interface) (label : interface ⟶ sourceInterface) :
    ActIPO echoRules label agent (agent ≫ label) := by
  have valueRead : ∃ supplied : Source.ValueClass arity, agent ≫ label = RawArrow.value supplied := by
    cases agent with
    | identity => cases label with
      | value supplied => exact ⟨supplied, rfl⟩
    | value supplied => cases label with
      | context suppliedContext => exact ⟨suppliedContext.fill supplied, rfl⟩
  obtain ⟨supplied, valueRead⟩ := valueRead
  refine ⟨echoRule supplied, ⟨supplied, rfl⟩, 𝟙 sourceInterface,
    valueRead.trans (Category.comp_id (echoRule supplied).redex).symm,
    raw_right_identity_isIPO label valueRead, ?_⟩
  exact valueRead.trans (Category.comp_id (echoRule supplied).reactum).symm

def multiplicity : {interface : SourceCategory} → ((.origin : SourceCategory) ⟶ interface) → Nat
  | _, .identity => 0
  | _, .value supplied => (inventoryQ supplied).card

def sameMultiplicity (interface : SourceCategory)
    (first second : (.origin : SourceCategory) ⟶ interface) : Prop :=
  multiplicity first = multiplicity second

private theorem raw_fill_preserves_cardinality
    {target : (Source.signature arity).Srt}
    (context : RawContext (Source.signature arity) (Source.Parallel arity) (ULift.up ()) target) :
    ∀ first second : Source.Value arity,
      (inventory first).card = (inventory second).card →
        (inventory (context.fill first)).card = (inventory (context.fill second)).card := by
  apply @RawContext.rec (Source.signature arity) (Source.Parallel arity) (ULift.up ())
    (fun _ context => ∀ first second : Source.Value arity,
      (inventory first).card = (inventory second).card →
        (inventory (context.fill first)).card = (inventory (context.fill second)).card) (t := context)
  · intro first second same
    exact same
  · intro constructor position siblings inner _inductionHypothesis first second _same
    simp only [RawContext.fill, inventory, Multiset.card_singleton]
  · intro sort parallel inner sibling inductionHypothesis first second same
    simpa only [RawContext.fill, inventory, Multiset.card_add] using
      congrArg (fun count => count + (inventory sibling).card) (inductionHypothesis first second same)
  · intro sort parallel sibling inner inductionHypothesis first second same
    simpa only [RawContext.fill, inventory, Multiset.card_add] using
      congrArg (fun count => (inventory sibling).card + count) (inductionHypothesis first second same)

theorem context_preserves_multiplicity
    (context : ContextClass (Source.signature arity) (Source.Parallel arity) (ULift.up ()) (ULift.up ()))
    (first second : Source.ValueClass arity) :
    (inventoryQ first).card = (inventoryQ second).card →
      (inventoryQ (context.fill first)).card = (inventoryQ (context.fill second)).card :=
  Quotient.inductionOn₃ context first second raw_fill_preserves_cardinality

theorem all_source_labels_preserve_multiplicity {interface nextInterface : SourceCategory}
    (first second : (.origin : SourceCategory) ⟶ interface)
    (same : sameMultiplicity interface first second) (label : interface ⟶ nextInterface) :
    sameMultiplicity nextInterface (first ≫ label) (second ≫ label) := by
  cases first with
  | identity => cases second; rfl
  | @value sort supplied =>
    cases second with
    | value other =>
      cases label with
      | @context _ target suppliedContext =>
        cases sort with
        | up source =>
          cases source
          cases target with
          | up target =>
            cases target
            exact context_preserves_multiplicity suppliedContext supplied other same

theorem actual_echo_bisimulation : IsIPOBisimulation echoRules sameMultiplicity := by
  intro interface first second same
  refine ⟨?_, ?_⟩
  · intro nextInterface label next step
    cases nextInterface with
    | origin =>
      obtain ⟨rule, ⟨supplied, rfl⟩, reaction, _⟩ := step
      cases reaction
    | interface sort =>
      cases sort with
      | up sort =>
        cases sort
        refine ⟨second ≫ label, echo_context_fires second label, ?_⟩
        rw [echo_step_readout first label next step]
        exact all_source_labels_preserve_multiplicity first second same label
  · intro nextInterface label next step
    cases nextInterface with
    | origin =>
      obtain ⟨rule, ⟨supplied, rfl⟩, reaction, _⟩ := step
      cases reaction
    | interface sort =>
      cases sort with
      | up sort =>
        cases sort
        refine ⟨first ≫ label, echo_context_fires first label, ?_⟩
        rw [echo_step_readout second label next step]
        exact all_source_labels_preserve_multiplicity first second same label

theorem two_distinct_values_are_actually_bisimilar :
    IPOBisimilar echoRules (RawArrow.value (classOf low)) (RawArrow.value (classOf high)) := by
  refine ⟨sameMultiplicity, actual_echo_bisimulation, ?_⟩
  rfl

theorem multiplicity_relation_is_proper :
    ¬sameMultiplicity sourceInterface (RawArrow.value (classOf low)) (RawArrow.value (classOf sourceCut)) := by
  change 1 = 1 + 1 → False
  omega

theorem native_pure_bisimilarity_does_not_identify_values :
    Source.ZeroSupportBisimilar echoRules (Source.inclusion.map (RawArrow.value (classOf low)))
      (Source.inclusion.map (RawArrow.value (classOf high))) ∧ classOf low ≠ classOf high :=
  ⟨(Source.bisimilar_iff_zeroSupport echoRules _ _).mp two_distinct_values_are_actually_bisimilar,
    SortedCommutativeSourceControls.source_values_are_distinct⟩

theorem actual_nonidentity_label_fires :
    ActIPO echoRules interactionLabel (RawArrow.value (classOf low))
      (RawArrow.value (classOf low) ≫ interactionLabel) := echo_context_fires _ _

theorem constructor_residue_label_is_not_identity : interactionLabel ≠ 𝟙 sourceInterface := by
  intro same
  have counts := congrArg
    (fun context : ContextClass (Source.signature arity) (Source.Parallel arity) (ULift.up ()) (ULift.up ()) =>
      Mettapedia.CategoryTheory.MixedResidue.Context.frameCount (normalizeContext context))
    (RawArrow.context.inj same)
  change 1 = 0 at counts
  cases counts

theorem nonidentity_label_keeps_whole_filled_target :
    RawArrow.value (classOf low) ≫ interactionLabel =
      (RawArrow.value (classOf (SortedCommutativeSourceComparisonControls.interactionContext.fill low)) :
        (.origin : SourceCategory) ⟶ sourceInterface) := rfl

theorem unequal_values_remain_related_under_actual_source_context :
    Source.ZeroSupportBisimilar echoRules
      (Source.inclusion.map (RawArrow.value (classOf low)) ≫ Source.inclusion.map interactionLabel)
      (Source.inclusion.map (RawArrow.value (classOf high)) ≫ Source.inclusion.map interactionLabel) :=
  Source.zeroSupport_bisimilar_source_context echoRules native_pure_bisimilarity_does_not_identify_values.1 interactionLabel

def selectedEchoDeclaration (_origin : Nat) : ReactionRule (.origin : SourceCategory) :=
  echoRule (classOf (SortedCommutativeSourceComparisonControls.interactionContext.fill low))

def retainedEcho (origin : Nat) : Source.FiringEvidence (.origin : SourceCategory) Nat selectedEchoDeclaration where
  occurrence := origin
  sourceInterface := sourceInterface
  targetInterface := sourceInterface
  agent := RawArrow.value (classOf low)
  label := interactionLabel
  reaction := 𝟙 sourceInterface
  square := (Category.comp_id (selectedEchoDeclaration origin).redex).symm
  minimal := raw_right_identity_isIPO interactionLabel rfl

theorem occurrence_comparison_retains_the_whole_nonidentity_result :
    (Source.mapFiring selectedEchoDeclaration (retainedEcho 7)).result =
      Source.inclusion.map (RawArrow.value (classOf low) ≫ interactionLabel) := by
  rw [Source.mapFiring_result]
  exact congrArg Source.inclusion.map (Category.comp_id (selectedEchoDeclaration 7).reactum)

theorem behavioral_comparison_keeps_distinct_supplied_origins :
    Source.mapFiring selectedEchoDeclaration (retainedEcho 7) ≠
      Source.mapFiring selectedEchoDeclaration (retainedEcho 8) :=
  Source.distinct_origins_keep_distinct_firings selectedEchoDeclaration (retainedEcho 7) (retainedEcho 8) (by decide)

theorem genuine_administrative_firing_has_an_excluded_label :
    ActIPO (rules arity Nat) SortedCommutativeInstrumentControls.getSecond.label
      SortedCommutativeInstrumentControls.getSecond.agent SortedCommutativeInstrumentControls.getSecond.target ∧
      arrowObserverCount SortedCommutativeInstrumentControls.getSecond.label ≠ 0 :=
  SortedCommutativeSourceComparisonControls.administrative_firing_is_real_but_not_pure

end Mettapedia.OSLF.Framework.SortedCommutativeSourceBisimulationControls
