import Mettapedia.OSLF.Framework.SortedTypedInstrumentSourceFiringComparison

/-!
# Native many-sorted pure-label bisimulation and exact source behavioral comparison

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

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments.Source

open _root_.CategoryTheory
open Mettapedia.GSLT.RedexRelativeCongruence

universe u v

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop}

abbrev NativeRelation := (interface : ContextCategory source Parallel) →
  ((.origin : ContextCategory source Parallel) ⟶ interface) →
    ((.origin : ContextCategory source Parallel) ⟶ interface) → Prop

def IsZeroSupportBisimulation
    (sourceRules : ReactionRule (.origin : SourceCategory source Parallel) → Prop)
    (relation : NativeRelation (source := source) (Parallel := Parallel)) : Prop :=
  ∀ {interface : ContextCategory source Parallel} (first second : (.origin : ContextCategory source Parallel) ⟶ interface),
    relation interface first second →
      (∀ {nextInterface : ContextCategory source Parallel} (label : interface ⟶ nextInterface),
        arrowObserverCount label = 0 → ∀ next,
          ActIPO (mappedRules sourceRules) label first next →
            ∃ matched, ActIPO (mappedRules sourceRules) label second matched ∧
              relation nextInterface next matched) ∧
      (∀ {nextInterface : ContextCategory source Parallel} (label : interface ⟶ nextInterface),
        arrowObserverCount label = 0 → ∀ next,
          ActIPO (mappedRules sourceRules) label second next →
            ∃ matched, ActIPO (mappedRules sourceRules) label first matched ∧
              relation nextInterface matched next)

def ZeroSupportBisimilar
    (sourceRules : ReactionRule (.origin : SourceCategory source Parallel) → Prop)
    {interface : ContextCategory source Parallel} (first second : (.origin : ContextCategory source Parallel) ⟶ interface) : Prop :=
  ∃ relation, IsZeroSupportBisimulation sourceRules relation ∧ relation interface first second

def nativeRelationImage
    (sourceRelation : (interface : SourceCategory source Parallel) →
      ((.origin : SourceCategory source Parallel) ⟶ interface) →
        ((.origin : SourceCategory source Parallel) ⟶ interface) → Prop) : NativeRelation (source := source) (Parallel := Parallel) :=
  fun interface first second =>
    ∃ sourceInterface : SourceCategory source Parallel, (inclusion source Parallel).obj sourceInterface = interface ∧
      ∃ sourceFirst sourceSecond, HEq ((inclusion source Parallel).map sourceFirst) first ∧
        HEq ((inclusion source Parallel).map sourceSecond) second ∧ sourceRelation sourceInterface sourceFirst sourceSecond

def sourceRelationRestriction (relation : NativeRelation (source := source) (Parallel := Parallel)) :
    (interface : SourceCategory source Parallel) →
      ((.origin : SourceCategory source Parallel) ⟶ interface) →
        ((.origin : SourceCategory source Parallel) ⟶ interface) → Prop :=
  fun interface first second => relation ((inclusion source Parallel).obj interface) ((inclusion source Parallel).map first) ((inclusion source Parallel).map second)

theorem source_bisimulation_maps
    (sourceRules : ReactionRule (.origin : SourceCategory source Parallel) → Prop)
    (sourceRelation : (interface : SourceCategory source Parallel) →
      ((.origin : SourceCategory source Parallel) ⟶ interface) →
        ((.origin : SourceCategory source Parallel) ⟶ interface) → Prop)
    (bisimulation : IsIPOBisimulation sourceRules sourceRelation) :
    IsZeroSupportBisimulation sourceRules (nativeRelationImage sourceRelation) := by
  intro interface first second related
  obtain ⟨sourceInterface, rfl, sourceFirst, sourceSecond, firstRead, secondRead, sourceRelated⟩ := related
  have firstSame : (inclusion source Parallel).map sourceFirst = first := eq_of_heq firstRead
  have secondSame : (inclusion source Parallel).map sourceSecond = second := eq_of_heq secondRead
  subst first
  subst second
  obtain ⟨forward, backward⟩ := bisimulation sourceFirst sourceSecond sourceRelated
  refine ⟨?_, ?_⟩
  · intro nextInterface label pure next step
    obtain ⟨sourceNextInterface, rfl⟩ := arrowObserverCount_zero_target label pure
    obtain ⟨sourceLabel, rfl⟩ := arrowObserverCount_zero_preimage label pure
    obtain ⟨sourceNext, sourceStep, rfl⟩ := source_step_target_reconstruction sourceRules sourceFirst sourceLabel next step
    obtain ⟨sourceMatched, matchedStep, matchedRelated⟩ := forward sourceLabel sourceNext sourceStep
    refine ⟨(inclusion source Parallel).map sourceMatched, source_step_maps sourceRules matchedStep, ?_⟩
    exact ⟨sourceNextInterface, rfl, sourceNext, sourceMatched, HEq.rfl, HEq.rfl, matchedRelated⟩
  · intro nextInterface label pure next step
    obtain ⟨sourceNextInterface, rfl⟩ := arrowObserverCount_zero_target label pure
    obtain ⟨sourceLabel, rfl⟩ := arrowObserverCount_zero_preimage label pure
    obtain ⟨sourceNext, sourceStep, rfl⟩ := source_step_target_reconstruction sourceRules sourceSecond sourceLabel next step
    obtain ⟨sourceMatched, matchedStep, matchedRelated⟩ := backward sourceLabel sourceNext sourceStep
    refine ⟨(inclusion source Parallel).map sourceMatched, source_step_maps sourceRules matchedStep, ?_⟩
    exact ⟨sourceNextInterface, rfl, sourceMatched, sourceNext, HEq.rfl, HEq.rfl, matchedRelated⟩

theorem native_bisimulation_restricts
    (sourceRules : ReactionRule (.origin : SourceCategory source Parallel) → Prop)
    (relation : NativeRelation (source := source) (Parallel := Parallel))
    (bisimulation : IsZeroSupportBisimulation sourceRules relation) :
    IsIPOBisimulation sourceRules (sourceRelationRestriction relation) := by
  intro interface first second related
  obtain ⟨forward, backward⟩ := bisimulation ((inclusion source Parallel).map first) ((inclusion source Parallel).map second) related
  refine ⟨?_, ?_⟩
  · intro nextInterface label next step
    obtain ⟨matched, matchedStep, matchedRelated⟩ :=
      forward ((inclusion source Parallel).map label) (arrowObserverCount_embedding label) ((inclusion source Parallel).map next) (source_step_maps sourceRules step)
    obtain ⟨sourceMatched, sourceStep, rfl⟩ := source_step_target_reconstruction sourceRules second label matched matchedStep
    exact ⟨sourceMatched, sourceStep, matchedRelated⟩
  · intro nextInterface label next step
    obtain ⟨matched, matchedStep, matchedRelated⟩ :=
      backward ((inclusion source Parallel).map label) (arrowObserverCount_embedding label) ((inclusion source Parallel).map next) (source_step_maps sourceRules step)
    obtain ⟨sourceMatched, sourceStep, rfl⟩ := source_step_target_reconstruction sourceRules first label matched matchedStep
    exact ⟨sourceMatched, sourceStep, matchedRelated⟩

theorem bisimilar_iff_zeroSupport
    (sourceRules : ReactionRule (.origin : SourceCategory source Parallel) → Prop)
    {interface : SourceCategory source Parallel}
    (first second : (.origin : SourceCategory source Parallel) ⟶ interface) :
    IPOBisimilar sourceRules first second ↔
      ZeroSupportBisimilar sourceRules ((inclusion source Parallel).map first) ((inclusion source Parallel).map second) := by
  constructor
  · rintro ⟨relation, bisimulation, related⟩
    exact ⟨nativeRelationImage relation, source_bisimulation_maps sourceRules relation bisimulation,
      interface, rfl, first, second, HEq.rfl, HEq.rfl, related⟩
  · rintro ⟨relation, bisimulation, related⟩
    exact ⟨sourceRelationRestriction relation, native_bisimulation_restricts sourceRules relation bisimulation, related⟩

theorem zeroSupport_bisimilar_source_context
    (sourceRules : ReactionRule (.origin : SourceCategory source Parallel) → Prop)
    {interface nextInterface : SourceCategory source Parallel}
    {first second : (.origin : SourceCategory source Parallel) ⟶ interface}
    (related : ZeroSupportBisimilar sourceRules ((inclusion source Parallel).map first) ((inclusion source Parallel).map second))
    (context : interface ⟶ nextInterface) :
    ZeroSupportBisimilar sourceRules ((inclusion source Parallel).map first ≫ (inclusion source Parallel).map context)
      ((inclusion source Parallel).map second ≫ (inclusion source Parallel).map context) := by
  have original := (bisimilar_iff_zeroSupport sourceRules first second).mpr related
  have filled := source_bisimulation_congruence sourceRules original context
  simpa only [(inclusion source Parallel).map_comp] using (bisimilar_iff_zeroSupport sourceRules (first ≫ context) (second ≫ context)).mp filled

theorem full_mapped_rule_bisimulation_restricts
    (sourceRules : ReactionRule (.origin : SourceCategory source Parallel) → Prop)
    (relation : NativeRelation (source := source) (Parallel := Parallel))
    (bisimulation : IsIPOBisimulation (mappedRules sourceRules) relation) :
    IsZeroSupportBisimulation sourceRules relation := by
  intro interface first second related
  obtain ⟨forward, backward⟩ := bisimulation first second related
  exact ⟨fun label _ next step => forward label next step,
    fun label _ next step => backward label next step⟩

theorem full_mapped_rule_bisimilar_implies_source
    (sourceRules : ReactionRule (.origin : SourceCategory source Parallel) → Prop)
    {interface : SourceCategory source Parallel}
    (first second : (.origin : SourceCategory source Parallel) ⟶ interface)
    (related : IPOBisimilar (mappedRules sourceRules) ((inclusion source Parallel).map first) ((inclusion source Parallel).map second)) :
    IPOBisimilar sourceRules first second := by
  obtain ⟨relation, bisimulation, linked⟩ := related
  exact (bisimilar_iff_zeroSupport sourceRules first second).mpr
    ⟨relation, full_mapped_rule_bisimulation_restricts sourceRules relation bisimulation, linked⟩

end Mettapedia.OSLF.Framework.SortedTypedInstruments.Source
