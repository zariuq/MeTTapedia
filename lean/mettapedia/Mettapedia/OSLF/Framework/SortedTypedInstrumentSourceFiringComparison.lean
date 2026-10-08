import Mettapedia.OSLF.Framework.SortedTypedInstrumentRPOComparison

/-!
# Complete many-sorted source firing and occurrence reconstruction

Original agents and original labels force a matching reaction context to
have zero hereditary observer support. Its complete source preimage and the
earned IPO comparison recover the whole original step and target. This
argument permits arbitrary independently authored original rules; it does
not require the original inclusion to be full.

Firing receipts additionally retain the supplied declaration occurrence.
At original bounds, every native receipt has a unique original receipt with
the same occurrence and complete mapped reaction context and target.
Administrative instrument declarations are a separate reaction family.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments.Source

open _root_.CategoryTheory
open Mettapedia.GSLT.RelativePushout Mettapedia.GSLT.RedexRelativeCongruence

universe u v w u₁ v₁

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop}

def mapReactionRule (supplied : ReactionRule (.origin : SourceCategory source Parallel)) :
    ReactionRule (.origin : ContextCategory source Parallel) where
  codomain := (inclusion source Parallel).obj supplied.codomain
  redex := (inclusion source Parallel).map supplied.redex
  reactum := (inclusion source Parallel).map supplied.reactum

def mappedRules (sourceRules : ReactionRule (.origin : SourceCategory source Parallel) → Prop) :
    ReactionRule (.origin : ContextCategory source Parallel) → Prop :=
  fun supplied => ∃ before, sourceRules before ∧ mapReactionRule before = supplied

theorem source_reaction_context_support
    {first second : SourceCategory source Parallel}
    (agent : (.origin : SourceCategory source Parallel) ⟶ first) (label : first ⟶ second)
    (rule : ReactionRule (.origin : SourceCategory source Parallel))
    (reaction : (inclusion source Parallel).obj rule.codomain ⟶ (inclusion source Parallel).obj second)
    (square : (inclusion source Parallel).map agent ≫ (inclusion source Parallel).map label =
      (inclusion source Parallel).map rule.redex ≫ reaction) :
    arrowObserverCount reaction = 0 := by
  have leftPure : arrowObserverCount ((inclusion source Parallel).map agent ≫
      (inclusion source Parallel).map label) = 0 := by
    rw [arrowCount_comp, arrowObserverCount_embedding, arrowObserverCount_embedding]
  have rightPure : arrowObserverCount ((inclusion source Parallel).map rule.redex ≫ reaction) = 0 :=
    (congrArg arrowObserverCount square).symm.trans leftPure
  exact (composite_zero_support _ _ rightPure).2

theorem source_step_maps
    (sourceRules : ReactionRule (.origin : SourceCategory source Parallel) → Prop)
    {first second : SourceCategory source Parallel}
    {agent : (.origin : SourceCategory source Parallel) ⟶ first} {label : first ⟶ second}
    {result : (.origin : SourceCategory source Parallel) ⟶ second}
    (step : ActIPO sourceRules label agent result) :
    ActIPO (mappedRules sourceRules) ((inclusion source Parallel).map label)
      ((inclusion source Parallel).map agent) ((inclusion source Parallel).map result) := by
  obtain ⟨rule, admitted, reaction, square, minimal, output⟩ := step
  refine ⟨mapReactionRule rule, ⟨rule, admitted, rfl⟩, (inclusion source Parallel).map reaction,
    (by rw [← Functor.map_comp, square, Functor.map_comp]; rfl),
      (RPO.idemPushout_iff_mapped square).mp minimal, ?_⟩
  exact (congrArg (inclusion source Parallel).map output).trans (Functor.map_comp _ _ _)

theorem source_step_target_reconstruction
    (sourceRules : ReactionRule (.origin : SourceCategory source Parallel) → Prop)
    {first second : SourceCategory source Parallel}
    (agent : (.origin : SourceCategory source Parallel) ⟶ first) (label : first ⟶ second)
    (result : (.origin : ContextCategory source Parallel) ⟶ (inclusion source Parallel).obj second)
    (step : ActIPO (mappedRules sourceRules) ((inclusion source Parallel).map label)
      ((inclusion source Parallel).map agent) result) :
    ∃ before : (.origin : SourceCategory source Parallel) ⟶ second,
      ActIPO sourceRules label agent before ∧ (inclusion source Parallel).map before = result := by
  obtain ⟨rule, ⟨sourceRule, admitted, rfl⟩, reaction, square, minimal, output⟩ := step
  have reactionPure := source_reaction_context_support agent label sourceRule reaction square
  obtain ⟨sourceReaction, reactionRead⟩ := arrowObserverCount_zero_preimage reaction reactionPure
  have sourceSquare : agent ≫ label = sourceRule.redex ≫ sourceReaction := by
    apply (inclusion source Parallel).map_injective
    rw [Functor.map_comp, Functor.map_comp, reactionRead]
    exact square
  have sourceMinimal : IsIdemPushout agent sourceRule.redex label sourceReaction sourceSquare := by
    apply (RPO.idemPushout_iff_mapped sourceSquare).mpr
    simpa only [mapReactionRule, reactionRead] using minimal
  refine ⟨sourceRule.reactum ≫ sourceReaction,
    ⟨sourceRule, admitted, sourceReaction, sourceSquare, sourceMinimal, rfl⟩, ?_⟩
  rw [Functor.map_comp, reactionRead]
  exact output.symm

theorem source_step_iff_mapped
    (sourceRules : ReactionRule (.origin : SourceCategory source Parallel) → Prop)
    {first second : SourceCategory source Parallel}
    (agent : (.origin : SourceCategory source Parallel) ⟶ first) (label : first ⟶ second)
    (result : (.origin : SourceCategory source Parallel) ⟶ second) :
    ActIPO sourceRules label agent result ↔
      ActIPO (mappedRules sourceRules) ((inclusion source Parallel).map label)
        ((inclusion source Parallel).map agent) ((inclusion source Parallel).map result) := by
  refine ⟨source_step_maps sourceRules, ?_⟩
  intro step
  obtain ⟨before, sourceStep, same⟩ := source_step_target_reconstruction sourceRules agent label _ step
  have sourceSame : before = result := (inclusion source Parallel).map_injective same
  exact sourceSame ▸ sourceStep

theorem source_step_full_target_support
    (sourceRules : ReactionRule (.origin : SourceCategory source Parallel) → Prop)
    {first second : SourceCategory source Parallel}
    (agent : (.origin : SourceCategory source Parallel) ⟶ first) (label : first ⟶ second)
    (result : (.origin : ContextCategory source Parallel) ⟶ (inclusion source Parallel).obj second)
    (step : ActIPO (mappedRules sourceRules) ((inclusion source Parallel).map label)
      ((inclusion source Parallel).map agent) result) :
    arrowObserverCount result = 0 := by
  obtain ⟨before, _, rfl⟩ := source_step_target_reconstruction sourceRules agent label result step
  exact arrowObserverCount_embedding before

section Occurrences

variable {C : Type u₁} [Category.{v₁} C]

structure FiringAt {origin : C} (Origins : Type w) (declarations : Origins → ReactionRule origin)
    {first second : C} (agent : origin ⟶ first) (label : first ⟶ second) where
  occurrence : Origins
  reaction : (declarations occurrence).codomain ⟶ second
  square : agent ≫ label = (declarations occurrence).redex ≫ reaction
  minimal : IsIdemPushout agent (declarations occurrence).redex label reaction square

def FiringAt.result {origin : C} {Origins : Type w} {declarations : Origins → ReactionRule origin}
    {first second : C} {agent : origin ⟶ first} {label : first ⟶ second}
    (supplied : FiringAt Origins declarations agent label) : origin ⟶ second :=
  (declarations supplied.occurrence).reactum ≫ supplied.reaction

theorem FiringAt.step {origin : C} {Origins : Type w} {declarations : Origins → ReactionRule origin}
    {first second : C} {agent : origin ⟶ first} {label : first ⟶ second}
    (supplied : FiringAt Origins declarations agent label) :
    ActIPO (fun rule => ∃ occurrence, declarations occurrence = rule) label agent supplied.result :=
  ⟨declarations supplied.occurrence, ⟨supplied.occurrence, rfl⟩,
    supplied.reaction, supplied.square, supplied.minimal, rfl⟩

theorem FiringAt.eq_of_readouts {origin : C} {Origins : Type w}
    {declarations : Origins → ReactionRule origin}
    {first second : C} {agent : origin ⟶ first} {label : first ⟶ second}
    (before after : FiringAt Origins declarations agent label)
    (occurrence : before.occurrence = after.occurrence)
    (reaction : HEq before.reaction after.reaction) : before = after := by
  cases before
  cases after
  cases occurrence
  cases eq_of_heq reaction
  rfl

end Occurrences

variable {Origins : Type w}
variable (declarations : Origins → ReactionRule (.origin : SourceCategory source Parallel))

def mapFiring {first second : SourceCategory source Parallel}
    {agent : (.origin : SourceCategory source Parallel) ⟶ first} {label : first ⟶ second}
    (supplied : FiringAt Origins declarations agent label) :
    FiringAt Origins (fun occurrence => mapReactionRule (declarations occurrence))
      ((inclusion source Parallel).map agent) ((inclusion source Parallel).map label) where
  occurrence := supplied.occurrence
  reaction := (inclusion source Parallel).map supplied.reaction
  square := by rw [← Functor.map_comp, supplied.square, Functor.map_comp]; rfl
  minimal := (RPO.idemPushout_iff_mapped supplied.square).mp supplied.minimal

theorem mapFiring_origin {first second : SourceCategory source Parallel}
    {agent : (.origin : SourceCategory source Parallel) ⟶ first} {label : first ⟶ second}
    (supplied : FiringAt Origins declarations agent label) :
    (mapFiring declarations supplied).occurrence = supplied.occurrence := rfl

theorem mapFiring_reaction {first second : SourceCategory source Parallel}
    {agent : (.origin : SourceCategory source Parallel) ⟶ first} {label : first ⟶ second}
    (supplied : FiringAt Origins declarations agent label) :
    (mapFiring declarations supplied).reaction = (inclusion source Parallel).map supplied.reaction := rfl

theorem mapFiring_result {first second : SourceCategory source Parallel}
    {agent : (.origin : SourceCategory source Parallel) ⟶ first} {label : first ⟶ second}
    (supplied : FiringAt Origins declarations agent label) :
    (mapFiring declarations supplied).result = (inclusion source Parallel).map supplied.result := by
  change (inclusion source Parallel).map (declarations supplied.occurrence).reactum ≫
    (inclusion source Parallel).map supplied.reaction =
      (inclusion source Parallel).map ((declarations supplied.occurrence).reactum ≫ supplied.reaction)
  exact ((inclusion source Parallel).map_comp _ _).symm

theorem mapFiring_injective {first second : SourceCategory source Parallel}
    {agent : (.origin : SourceCategory source Parallel) ⟶ first} {label : first ⟶ second} :
    Function.Injective (mapFiring declarations (agent := agent) (label := label)) := by
  intro before after same
  have readings := congrArg (fun supplied : FiringAt Origins
    (fun occurrence => mapReactionRule (declarations occurrence))
      ((inclusion source Parallel).map agent) ((inclusion source Parallel).map label) =>
        (⟨supplied.occurrence, supplied.reaction⟩ :
          Σ occurrence : Origins, (inclusion source Parallel).obj (declarations occurrence).codomain ⟶
            (inclusion source Parallel).obj second)) same
  obtain ⟨occurrence, reaction⟩ := Sigma.mk.inj readings
  cases before with | mk beforeOccurrence beforeReaction beforeSquare beforeMinimal =>
  cases after with | mk afterOccurrence afterReaction afterSquare afterMinimal =>
  cases occurrence
  have sourceReaction : beforeReaction = afterReaction :=
    (inclusion source Parallel).map_injective (eq_of_heq reaction)
  cases sourceReaction
  rfl

theorem native_firing_unique_reconstruction {first second : SourceCategory source Parallel}
    {agent : (.origin : SourceCategory source Parallel) ⟶ first} {label : first ⟶ second}
    (supplied : FiringAt Origins (fun occurrence => mapReactionRule (declarations occurrence))
      ((inclusion source Parallel).map agent) ((inclusion source Parallel).map label)) :
    ∃! before : FiringAt Origins declarations agent label, mapFiring declarations before = supplied := by
  obtain ⟨reaction, reactionRead⟩ := arrowObserverCount_zero_preimage supplied.reaction
    (source_reaction_context_support agent label (declarations supplied.occurrence)
      supplied.reaction supplied.square)
  have sourceSquare : agent ≫ label = (declarations supplied.occurrence).redex ≫ reaction := by
    apply (inclusion source Parallel).map_injective
    rw [Functor.map_comp, Functor.map_comp, reactionRead]
    exact supplied.square
  let before : FiringAt Origins declarations agent label :=
    { occurrence := supplied.occurrence
      reaction := reaction
      square := sourceSquare
      minimal := (RPO.idemPushout_iff_mapped sourceSquare).mpr
        (by simpa only [mapReactionRule, reactionRead] using supplied.minimal) }
  have beforeRead : mapFiring declarations before = supplied :=
    FiringAt.eq_of_readouts _ _ rfl (heq_of_eq reactionRead)
  exact ⟨before, beforeRead, fun after afterRead =>
    mapFiring_injective declarations (afterRead.trans beforeRead.symm)⟩

theorem distinct_origins_keep_distinct_firings {first second : SourceCategory source Parallel}
    {agent : (.origin : SourceCategory source Parallel) ⟶ first} {label : first ⟶ second}
    (before after : FiringAt Origins declarations agent label)
    (different : before.occurrence ≠ after.occurrence) :
    mapFiring declarations before ≠ mapFiring declarations after :=
  fun same => different (congrArg (fun supplied : FiringAt Origins
    (fun occurrence => mapReactionRule (declarations occurrence))
      ((inclusion source Parallel).map agent) ((inclusion source Parallel).map label) => supplied.occurrence) same)

end Mettapedia.OSLF.Framework.SortedTypedInstruments.Source
