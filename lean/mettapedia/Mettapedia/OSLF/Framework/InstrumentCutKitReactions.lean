import Mettapedia.OSLF.Framework.InstrumentCutSourceReactions
import Mettapedia.OSLF.Framework.InstrumentSourceTransitions

/-!
# Actual instrument-kit rule families and complete minimal firing receipts

Permission restricts the categorical reaction family itself. Every permitted
administrative rule retains its authored origin and complete arguments. The
selected probe transition is characterized using its genuine IPO witness;
proper rules cannot supply a different firing behind that label.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentCutContexts

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedConstructors
open Mettapedia.CategoryTheory.GroundPath
open Mettapedia.GSLT.RelativePushout
open Mettapedia.GSLT.RedexRelativeCongruence

universe u w

variable {Symbols : Type u} (arity : Symbols → Nat)

local instance instrumentCutKitReactionsQuiver : Quiver (Srt Symbols arity) :=
  frameQuiver (signature arity)

def instrumentConstructor : Probe Symbols arity → Symbols
  | .ask constructor | .get constructor _ | .build constructor => constructor

def kitAdministrativeRules (Origins : Type w) (opened : InstrumentObservations.Policy Symbols)
    (rule : ReactionRule (.origin : ContextObject (signature arity))) : Prop :=
  ∃ instrument : Probe Symbols arity,
    ∃ occurrence : AdministrativeOccurrence arity Origins instrument,
      opened (instrumentConstructor arity instrument) ∧ rule = occurrence.instance_.rule

def kitRules (Origins : Type w) (opened : InstrumentObservations.Policy Symbols)
    (proper : SourceRule arity → Prop)
    (rule : ReactionRule (.origin : ContextObject (signature arity))) : Prop :=
  kitAdministrativeRules arity Origins opened rule ∨
    ∃ sourceRule, proper sourceRule ∧ rule = sourceRule.reaction

theorem kitRules_extended {Origins : Type w} {opened : InstrumentObservations.Policy Symbols}
    {proper : SourceRule arity → Prop} {rule : ReactionRule (.origin : ContextObject (signature arity))}
    (admitted : kitRules arity Origins opened proper rule) : extendedRules arity Origins proper rule := by
  rcases admitted with ⟨instrument, occurrence, _, rfl⟩ | properAdmission
  · exact Or.inl ⟨instrument, occurrence, rfl⟩
  · exact Or.inr properAdmission

theorem kitRules_monotone {Origins : Type w}
    {first second : InstrumentObservations.Policy Symbols}
    (larger : ∀ constructor, first constructor → second constructor)
    {proper : SourceRule arity → Prop} {rule : ReactionRule (.origin : ContextObject (signature arity))}
    (admitted : kitRules arity Origins first proper rule) : kitRules arity Origins second proper rule := by
  rcases admitted with ⟨instrument, occurrence, permission, rfl⟩ | properAdmission
  · exact Or.inl ⟨instrument, occurrence, larger _ permission, rfl⟩
  · exact Or.inr properAdmission

theorem kit_step_monotone {Origins : Type w}
    {first second : InstrumentObservations.Policy Symbols}
    (larger : ∀ constructor, first constructor → second constructor)
    {proper : SourceRule arity → Prop} {sourceInterface targetInterface : ContextObject (signature arity)}
    {label : sourceInterface ⟶ targetInterface}
    {source : (.origin : ContextObject (signature arity)) ⟶ sourceInterface}
    {target : (.origin : ContextObject (signature arity)) ⟶ targetInterface}
    (step : ActIPO (kitRules arity Origins first proper) label source target) :
    ActIPO (kitRules arity Origins second proper) label source target := by
  obtain ⟨rule, admitted, reaction, square, ipo, targetRead⟩ := step
  exact ⟨rule, kitRules_monotone arity larger admitted, reaction, square, ipo, targetRead⟩

theorem kit_context_congruence (Origins : Type w) (opened : InstrumentObservations.Policy Symbols)
    (proper : SourceRule arity → Prop) {first second : ContextObject (signature arity)}
    (left right : (.origin : ContextObject (signature arity)) ⟶ first)
    (related : IPOBisimilar (kitRules arity Origins opened proper) left right) (context : first ⟶ second) :
    IPOBisimilar (kitRules arity Origins opened proper) (left ≫ context) (right ≫ context) :=
  context_bisimulation_congruence (action (signature arity)) (kitRules arity Origins opened proper)
    left right related context

theorem kit_probe_step_iff (Origins : Type w) (opened : InstrumentObservations.Policy Symbols)
    (proper : SourceRule arity → Prop) (instrument : Probe Symbols arity)
    (source : Value arity (receiver arity instrument)) (target : Value arity (result arity instrument)) :
    ActIPO (kitRules arity Origins opened proper)
      (contextArrow (signature arity) (probeContext arity instrument))
      (termArrow (signature arity) source) (termArrow (signature arity) target) ↔
      ∃ occurrence : AdministrativeOccurrence arity Origins instrument,
        opened (instrumentConstructor arity instrument) ∧
          source = occurrence.instance_.body ∧ target = occurrence.instance_.output := by
  constructor
  · rintro ⟨rule, membership, reaction, square, ipo, targetEq⟩
    rcases membership with ⟨other, occurrence, permission, rfl⟩ | ⟨sourceRule, _, rfl⟩
    · cases reaction with
      | context path =>
        have zero := probe_ipo_reaction_length arity instrument source
          (cut arity other (probe arity other) occurrence.instance_.body)
          (result_ne_probe arity other instrument) path square ipo
        have values := Arrow.value.inj square
        have heads := Term.head_eq (signature := signature arity) _ _ values
        have same : instrument = other := by
          apply Constructor.cut.inj
          exact (show Constructor.cut instrument =
            ((action (signature arity)).path path
              (cut arity other (probe arity other) occurrence.instance_.body)).head from heads).trans
                (zero_path_head arity path _ zero)
        subst other
        have nil := Quiver.Path.eq_nil_of_length_zero path zero
        rw [nil] at square targetEq
        have exposed := Arrow.value.inj square
        rw [probeContext_fill] at exposed
        exact ⟨occurrence, permission, congrFun (Term.node.inj exposed) 1, Arrow.value.inj targetEq⟩
    · cases reaction with
      | context path =>
        have zero := probe_ipo_reaction_length arity instrument source
          (embedSource arity sourceRule.redex) (by intro impossible; cases impossible) path square ipo
        have values := Arrow.value.inj square
        have heads := (Term.head_eq (signature := signature arity) _ _ values).trans
          (zero_path_head arity path (embedSource arity sourceRule.redex) zero)
        cases sourceRead : sourceRule.redex with
        | node constructor arguments =>
          rw [sourceRead] at heads
          change Constructor.cut instrument = Constructor.original constructor at heads
          cases heads
  · rintro ⟨occurrence, permission, rfl, rfl⟩
    let rule := occurrence.instance_.rule
    have square : termArrow (signature arity) occurrence.instance_.body ≫
        contextArrow (signature arity) (probeContext arity instrument) =
        rule.redex ≫ 𝟙 rule.codomain := by
      rw [Category.comp_id, termArrow_comp, probeContext_fill]
      rfl
    exact ⟨rule, Or.inl ⟨instrument, occurrence, permission, rfl⟩, 𝟙 rule.codomain, square,
      ground_identityReactionIPO (action (signature arity)) occurrence.instance_.body
        (cut arity instrument (probe arity instrument) occurrence.instance_.body)
        (probeContext arity instrument) square, rfl⟩

structure KitFiringReceipt (Origins : Type w) (opened : InstrumentObservations.Policy Symbols)
    (instrument : Probe Symbols arity) (source : Value arity (receiver arity instrument))
    (target : Value arity (result arity instrument)) where
  occurrence : AdministrativeOccurrence arity Origins instrument
  permission : opened (instrumentConstructor arity instrument)
  source_readout : source = occurrence.instance_.body
  target_readout : target = occurrence.instance_.output

theorem KitFiringReceipt.step {Origins : Type w} {opened : InstrumentObservations.Policy Symbols}
    (proper : SourceRule arity → Prop) {instrument : Probe Symbols arity}
    {source : Value arity (receiver arity instrument)} {target : Value arity (result arity instrument)}
    (receipt : KitFiringReceipt arity Origins opened instrument source target) :
    ActIPO (kitRules arity Origins opened proper)
      (contextArrow (signature arity) (probeContext arity instrument))
      (termArrow (signature arity) source) (termArrow (signature arity) target) :=
  (kit_probe_step_iff arity Origins opened proper instrument source target).mpr
    ⟨receipt.occurrence, receipt.permission, receipt.source_readout, receipt.target_readout⟩

theorem kitFiringReceipt_support {Origins : Type w} {opened : InstrumentObservations.Policy Symbols}
    (proper : SourceRule arity → Prop) {instrument : Probe Symbols arity}
    {source : Value arity (receiver arity instrument)} {target : Value arity (result arity instrument)} :
    Nonempty (KitFiringReceipt arity Origins opened instrument source target) ↔
      ActIPO (kitRules arity Origins opened proper)
        (contextArrow (signature arity) (probeContext arity instrument))
        (termArrow (signature arity) source) (termArrow (signature arity) target) := by
  constructor
  · rintro ⟨receipt⟩; exact receipt.step arity proper
  · intro step
    obtain ⟨occurrence, permission, sourceRead, targetRead⟩ :=
      (kit_probe_step_iff arity Origins opened proper instrument source target).mp step
    exact ⟨⟨occurrence, permission, sourceRead, targetRead⟩⟩

end Mettapedia.OSLF.Framework.InstrumentCutContexts
