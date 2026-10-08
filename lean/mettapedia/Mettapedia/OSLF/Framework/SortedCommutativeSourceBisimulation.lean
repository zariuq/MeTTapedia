import Mettapedia.OSLF.Framework.SortedCommutativeSourceFiringComparison

/-!
# Native pure-label bisimulation and exact source behavioral comparison

The native relation quantifies over actual extended arrows, interfaces and
IPO firings. Its admitted labels are independently characterized by zero
hereditary auxiliary-head support. Source-object, label, reaction-context
and target reconstruction earn its equivalence with source bisimulation.
Actual source contexts consequently preserve this native restricted relation.

The reaction family consists of mapped source rules. Auxiliary labels and
administrative observer rules are not part of this equivalence; no equality
with full observer bisimulation or current structural views is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments.Source

open _root_.CategoryTheory
open Mettapedia.GSLT.RedexRelativeCongruence
open Support

universe u

variable {Symbols : Type u} {arity : Symbols → Nat}

abbrev NativeRelation := (interface : ContextCategory arity) →
  ((.origin : ContextCategory arity) ⟶ interface) →
    ((.origin : ContextCategory arity) ⟶ interface) → Prop

def IsZeroSupportBisimulation
    (sourceRules : ReactionRule (.origin : SourceCategory (arity := arity)) → Prop)
    (relation : NativeRelation (arity := arity)) : Prop :=
  ∀ {interface : ContextCategory arity} (first second : (.origin : ContextCategory arity) ⟶ interface),
    relation interface first second →
      (∀ {nextInterface : ContextCategory arity} (label : interface ⟶ nextInterface),
        arrowObserverCount label = 0 → ∀ next,
          ActIPO (mappedRules sourceRules) label first next →
            ∃ matched, ActIPO (mappedRules sourceRules) label second matched ∧
              relation nextInterface next matched) ∧
      (∀ {nextInterface : ContextCategory arity} (label : interface ⟶ nextInterface),
        arrowObserverCount label = 0 → ∀ next,
          ActIPO (mappedRules sourceRules) label second next →
            ∃ matched, ActIPO (mappedRules sourceRules) label first matched ∧
              relation nextInterface matched next)

def ZeroSupportBisimilar
    (sourceRules : ReactionRule (.origin : SourceCategory (arity := arity)) → Prop)
    {interface : ContextCategory arity} (first second : (.origin : ContextCategory arity) ⟶ interface) : Prop :=
  ∃ relation, IsZeroSupportBisimulation sourceRules relation ∧ relation interface first second

def nativeRelationImage
    (sourceRelation : (interface : SourceCategory (arity := arity)) →
      ((.origin : SourceCategory (arity := arity)) ⟶ interface) →
        ((.origin : SourceCategory (arity := arity)) ⟶ interface) → Prop) : NativeRelation (arity := arity) :=
  fun interface first second =>
    ∃ sourceInterface : SourceCategory (arity := arity), inclusion.obj sourceInterface = interface ∧
      ∃ sourceFirst sourceSecond, HEq (inclusion.map sourceFirst) first ∧
        HEq (inclusion.map sourceSecond) second ∧ sourceRelation sourceInterface sourceFirst sourceSecond

def sourceRelationRestriction (relation : NativeRelation (arity := arity)) :
    (interface : SourceCategory (arity := arity)) →
      ((.origin : SourceCategory (arity := arity)) ⟶ interface) →
        ((.origin : SourceCategory (arity := arity)) ⟶ interface) → Prop :=
  fun interface first second => relation (inclusion.obj interface) (inclusion.map first) (inclusion.map second)

theorem source_bisimulation_maps
    (sourceRules : ReactionRule (.origin : SourceCategory (arity := arity)) → Prop)
    (sourceRelation : (interface : SourceCategory (arity := arity)) →
      ((.origin : SourceCategory (arity := arity)) ⟶ interface) →
        ((.origin : SourceCategory (arity := arity)) ⟶ interface) → Prop)
    (bisimulation : IsIPOBisimulation sourceRules sourceRelation) :
    IsZeroSupportBisimulation sourceRules (nativeRelationImage sourceRelation) := by
  intro interface first second related
  obtain ⟨sourceInterface, rfl, sourceFirst, sourceSecond, firstRead, secondRead, sourceRelated⟩ := related
  have firstSame : inclusion.map sourceFirst = first := eq_of_heq firstRead
  have secondSame : inclusion.map sourceSecond = second := eq_of_heq secondRead
  subst first
  subst second
  obtain ⟨forward, backward⟩ := bisimulation sourceFirst sourceSecond sourceRelated
  refine ⟨?_, ?_⟩
  · intro nextInterface label pure next step
    obtain ⟨sourceNextInterface, rfl⟩ := arrowObserverCount_zero_target label pure
    obtain ⟨sourceLabel, rfl⟩ := arrowObserverCount_zero_preimage label pure
    obtain ⟨sourceNext, sourceStep, rfl⟩ := source_step_target_reconstruction sourceRules sourceFirst sourceLabel next step
    obtain ⟨sourceMatched, matchedStep, matchedRelated⟩ := forward sourceLabel sourceNext sourceStep
    refine ⟨inclusion.map sourceMatched, source_step_maps sourceRules matchedStep, ?_⟩
    exact ⟨sourceNextInterface, rfl, sourceNext, sourceMatched, HEq.rfl, HEq.rfl, matchedRelated⟩
  · intro nextInterface label pure next step
    obtain ⟨sourceNextInterface, rfl⟩ := arrowObserverCount_zero_target label pure
    obtain ⟨sourceLabel, rfl⟩ := arrowObserverCount_zero_preimage label pure
    obtain ⟨sourceNext, sourceStep, rfl⟩ := source_step_target_reconstruction sourceRules sourceSecond sourceLabel next step
    obtain ⟨sourceMatched, matchedStep, matchedRelated⟩ := backward sourceLabel sourceNext sourceStep
    refine ⟨inclusion.map sourceMatched, source_step_maps sourceRules matchedStep, ?_⟩
    exact ⟨sourceNextInterface, rfl, sourceMatched, sourceNext, HEq.rfl, HEq.rfl, matchedRelated⟩

theorem native_bisimulation_restricts
    (sourceRules : ReactionRule (.origin : SourceCategory (arity := arity)) → Prop)
    (relation : NativeRelation (arity := arity))
    (bisimulation : IsZeroSupportBisimulation sourceRules relation) :
    IsIPOBisimulation sourceRules (sourceRelationRestriction relation) := by
  intro interface first second related
  obtain ⟨forward, backward⟩ := bisimulation (inclusion.map first) (inclusion.map second) related
  refine ⟨?_, ?_⟩
  · intro nextInterface label next step
    obtain ⟨matched, matchedStep, matchedRelated⟩ :=
      forward (inclusion.map label) (arrowObserverCount_embedding label) (inclusion.map next) (source_step_maps sourceRules step)
    obtain ⟨sourceMatched, sourceStep, rfl⟩ := source_step_target_reconstruction sourceRules second label matched matchedStep
    exact ⟨sourceMatched, sourceStep, matchedRelated⟩
  · intro nextInterface label next step
    obtain ⟨matched, matchedStep, matchedRelated⟩ :=
      backward (inclusion.map label) (arrowObserverCount_embedding label) (inclusion.map next) (source_step_maps sourceRules step)
    obtain ⟨sourceMatched, sourceStep, rfl⟩ := source_step_target_reconstruction sourceRules first label matched matchedStep
    exact ⟨sourceMatched, sourceStep, matchedRelated⟩

theorem bisimilar_iff_zeroSupport
    (sourceRules : ReactionRule (.origin : SourceCategory (arity := arity)) → Prop)
    {interface : SourceCategory (arity := arity)}
    (first second : (.origin : SourceCategory (arity := arity)) ⟶ interface) :
    IPOBisimilar sourceRules first second ↔
      ZeroSupportBisimilar sourceRules (inclusion.map first) (inclusion.map second) := by
  constructor
  · rintro ⟨relation, bisimulation, related⟩
    exact ⟨nativeRelationImage relation, source_bisimulation_maps sourceRules relation bisimulation,
      interface, rfl, first, second, HEq.rfl, HEq.rfl, related⟩
  · rintro ⟨relation, bisimulation, related⟩
    exact ⟨sourceRelationRestriction relation, native_bisimulation_restricts sourceRules relation bisimulation, related⟩

theorem zeroSupport_bisimilar_source_context
    (sourceRules : ReactionRule (.origin : SourceCategory (arity := arity)) → Prop)
    {interface nextInterface : SourceCategory (arity := arity)}
    {first second : (.origin : SourceCategory (arity := arity)) ⟶ interface}
    (related : ZeroSupportBisimilar sourceRules (inclusion.map first) (inclusion.map second))
    (context : interface ⟶ nextInterface) :
    ZeroSupportBisimilar sourceRules (inclusion.map first ≫ inclusion.map context)
      (inclusion.map second ≫ inclusion.map context) := by
  have original := (bisimilar_iff_zeroSupport sourceRules first second).mpr related
  have filled := source_bisimulation_congruence sourceRules original context
  simpa only [inclusion.map_comp] using (bisimilar_iff_zeroSupport sourceRules (first ≫ context) (second ≫ context)).mp filled

theorem full_mapped_rule_bisimulation_restricts
    (sourceRules : ReactionRule (.origin : SourceCategory (arity := arity)) → Prop)
    (relation : NativeRelation (arity := arity))
    (bisimulation : IsIPOBisimulation (mappedRules sourceRules) relation) :
    IsZeroSupportBisimulation sourceRules relation := by
  intro interface first second related
  obtain ⟨forward, backward⟩ := bisimulation first second related
  exact ⟨fun label _ next step => forward label next step,
    fun label _ next step => backward label next step⟩

theorem full_mapped_rule_bisimilar_implies_source
    (sourceRules : ReactionRule (.origin : SourceCategory (arity := arity)) → Prop)
    {interface : SourceCategory (arity := arity)}
    (first second : (.origin : SourceCategory (arity := arity)) ⟶ interface)
    (related : IPOBisimilar (mappedRules sourceRules) (inclusion.map first) (inclusion.map second)) :
    IPOBisimilar sourceRules first second := by
  obtain ⟨relation, bisimulation, linked⟩ := related
  exact (bisimilar_iff_zeroSupport sourceRules first second).mpr
    ⟨relation, full_mapped_rule_bisimulation_restricts sourceRules relation bisimulation, linked⟩

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments.Source
