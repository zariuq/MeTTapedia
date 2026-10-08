import Mettapedia.OSLF.Framework.SortedCommutativeSourceRPOComparison

/-!
# Source-rule firing with exact reaction-context and target recovery

The rule image is defined independently from actual source declarations.
Pure source agents and source labels force every matching reaction context
to be pure. The earned complete IPO comparison then reconstructs the source
step and its full target. This is a comparison for source rules and labels,
not for the administrative observer reaction family.

Occurrence-indexed evidence separately retains the supplied declaration
origin, agent, label and complete reaction context through the inclusion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments.Source

open _root_.CategoryTheory
open Mettapedia.GSLT.RelativePushout Mettapedia.GSLT.RedexRelativeCongruence
open Support

universe u w

variable {Symbols : Type u} {arity : Symbols → Nat}

def mapReactionRule (supplied : ReactionRule (.origin : SourceCategory (arity := arity))) :
    ReactionRule (.origin : ContextCategory arity) where
  codomain := inclusion.obj supplied.codomain
  redex := inclusion.map supplied.redex
  reactum := inclusion.map supplied.reactum

def mappedRules (sourceRules : ReactionRule (.origin : SourceCategory (arity := arity)) → Prop) :
    ReactionRule (.origin : ContextCategory arity) → Prop :=
  fun supplied => ∃ before, sourceRules before ∧ mapReactionRule before = supplied

theorem source_reaction_context_support
    {source target : SourceCategory (arity := arity)}
    (agent : (.origin : SourceCategory (arity := arity)) ⟶ source) (label : source ⟶ target)
    (rule : ReactionRule (.origin : SourceCategory (arity := arity)))
    (reaction : inclusion.obj rule.codomain ⟶ inclusion.obj target)
    (square : inclusion.map agent ≫ inclusion.map label = inclusion.map rule.redex ≫ reaction) :
    arrowObserverCount reaction = 0 := by
  have leftPure : arrowObserverCount (inclusion.map agent ≫ inclusion.map label) = 0 := by
    rw [arrowCount_comp, arrowObserverCount_embedding, arrowObserverCount_embedding]
  have rightPure : arrowObserverCount (inclusion.map rule.redex ≫ reaction) = 0 :=
    (congrArg arrowObserverCount square).symm.trans leftPure
  exact (composite_zero_support _ _ rightPure).2

theorem source_step_maps
    (sourceRules : ReactionRule (.origin : SourceCategory (arity := arity)) → Prop)
    {source target : SourceCategory (arity := arity)}
    {agent : (.origin : SourceCategory (arity := arity)) ⟶ source} {label : source ⟶ target}
    {result : (.origin : SourceCategory (arity := arity)) ⟶ target}
    (step : ActIPO sourceRules label agent result) :
    ActIPO (mappedRules sourceRules) (inclusion.map label) (inclusion.map agent) (inclusion.map result) := by
  obtain ⟨rule, admitted, reaction, square, minimal, output⟩ := step
  refine ⟨mapReactionRule rule, ⟨rule, admitted, rfl⟩, inclusion.map reaction,
    (by rw [← inclusion.map_comp, square, inclusion.map_comp]; rfl),
      (idemPushout_iff_mapped square).mp minimal, ?_⟩
  exact (congrArg inclusion.map output).trans (inclusion.map_comp _ _)

theorem source_step_target_reconstruction
    (sourceRules : ReactionRule (.origin : SourceCategory (arity := arity)) → Prop)
    {source target : SourceCategory (arity := arity)}
    (agent : (.origin : SourceCategory (arity := arity)) ⟶ source) (label : source ⟶ target)
    (result : (.origin : ContextCategory arity) ⟶ inclusion.obj target)
    (step : ActIPO (mappedRules sourceRules) (inclusion.map label) (inclusion.map agent) result) :
    ∃ before : (.origin : SourceCategory (arity := arity)) ⟶ target,
      ActIPO sourceRules label agent before ∧ inclusion.map before = result := by
  obtain ⟨rule, ⟨sourceRule, admitted, rfl⟩, reaction, square, minimal, output⟩ := step
  have reactionPure := source_reaction_context_support agent label sourceRule reaction square
  obtain ⟨sourceReaction, reactionRead⟩ := arrowObserverCount_zero_preimage reaction reactionPure
  have sourceSquare : agent ≫ label = sourceRule.redex ≫ sourceReaction := by
    apply inclusion.map_injective
    rw [inclusion.map_comp, inclusion.map_comp, reactionRead]
    exact square
  have sourceMinimal : IsIdemPushout agent sourceRule.redex label sourceReaction sourceSquare := by
    apply (idemPushout_iff_mapped sourceSquare).mpr
    simpa only [mapReactionRule, reactionRead] using minimal
  refine ⟨sourceRule.reactum ≫ sourceReaction, ⟨sourceRule, admitted, sourceReaction, sourceSquare, sourceMinimal, rfl⟩, ?_⟩
  rw [inclusion.map_comp, reactionRead]
  exact output.symm

theorem source_step_iff_mapped
    (sourceRules : ReactionRule (.origin : SourceCategory (arity := arity)) → Prop)
    {source target : SourceCategory (arity := arity)}
    (agent : (.origin : SourceCategory (arity := arity)) ⟶ source) (label : source ⟶ target)
    (result : (.origin : SourceCategory (arity := arity)) ⟶ target) :
    ActIPO sourceRules label agent result ↔
      ActIPO (mappedRules sourceRules) (inclusion.map label) (inclusion.map agent) (inclusion.map result) := by
  refine ⟨source_step_maps sourceRules, ?_⟩
  intro step
  obtain ⟨before, sourceStep, same⟩ := source_step_target_reconstruction sourceRules agent label _ step
  have sourceSame : before = result := inclusion.map_injective same
  exact sourceSame ▸ sourceStep

theorem source_step_full_target_support
    (sourceRules : ReactionRule (.origin : SourceCategory (arity := arity)) → Prop)
    {source target : SourceCategory (arity := arity)}
    (agent : (.origin : SourceCategory (arity := arity)) ⟶ source) (label : source ⟶ target)
    (result : (.origin : ContextCategory arity) ⟶ inclusion.obj target)
    (step : ActIPO (mappedRules sourceRules) (inclusion.map label) (inclusion.map agent) result) :
    arrowObserverCount result = 0 := by
  obtain ⟨before, _, rfl⟩ := source_step_target_reconstruction sourceRules agent label result step
  exact arrowObserverCount_embedding before

section Occurrences

variable {C : Type u} [Category.{u} C]

structure FiringEvidence (origin : C) (Origins : Type w) (declarations : Origins → ReactionRule origin) where
  occurrence : Origins
  sourceInterface : C
  targetInterface : C
  agent : origin ⟶ sourceInterface
  label : sourceInterface ⟶ targetInterface
  reaction : (declarations occurrence).codomain ⟶ targetInterface
  square : agent ≫ label = (declarations occurrence).redex ≫ reaction
  minimal : IsIdemPushout agent (declarations occurrence).redex label reaction square

def FiringEvidence.result {origin : C} {Origins : Type w} {declarations : Origins → ReactionRule origin}
    (supplied : FiringEvidence origin Origins declarations) : origin ⟶ supplied.targetInterface :=
  (declarations supplied.occurrence).reactum ≫ supplied.reaction

theorem FiringEvidence.step {origin : C} {Origins : Type w} {declarations : Origins → ReactionRule origin}
    (supplied : FiringEvidence origin Origins declarations) :
    ActIPO (fun rule => ∃ occurrence, declarations occurrence = rule) supplied.label supplied.agent supplied.result :=
  ⟨declarations supplied.occurrence, ⟨supplied.occurrence, rfl⟩,
    supplied.reaction, supplied.square, supplied.minimal, rfl⟩

end Occurrences

variable {Origins : Type w}
variable (declarations : Origins → ReactionRule (.origin : SourceCategory (arity := arity)))

def mapFiring (supplied : FiringEvidence (.origin : SourceCategory (arity := arity)) Origins declarations) :
    FiringEvidence (.origin : ContextCategory arity) Origins (fun occurrence => mapReactionRule (declarations occurrence)) where
  occurrence := supplied.occurrence
  sourceInterface := inclusion.obj supplied.sourceInterface
  targetInterface := inclusion.obj supplied.targetInterface
  agent := inclusion.map supplied.agent
  label := inclusion.map supplied.label
  reaction := inclusion.map supplied.reaction
  square := by rw [← inclusion.map_comp, supplied.square, inclusion.map_comp]; rfl
  minimal := (idemPushout_iff_mapped supplied.square).mp supplied.minimal

theorem mapFiring_origin
    (supplied : FiringEvidence (.origin : SourceCategory (arity := arity)) Origins declarations) :
    (mapFiring declarations supplied).occurrence = supplied.occurrence := rfl

theorem mapFiring_result
    (supplied : FiringEvidence (.origin : SourceCategory (arity := arity)) Origins declarations) :
    (mapFiring declarations supplied).result = inclusion.map supplied.result :=
  (inclusion.map_comp _ _).symm

theorem mapFiring_reaction
    (supplied : FiringEvidence (.origin : SourceCategory (arity := arity)) Origins declarations) :
    (mapFiring declarations supplied).reaction = inclusion.map supplied.reaction := rfl

theorem distinct_origins_keep_distinct_firings
    (first second : FiringEvidence (.origin : SourceCategory (arity := arity)) Origins declarations)
    (origins : first.occurrence ≠ second.occurrence) : mapFiring declarations first ≠ mapFiring declarations second :=
  fun same => origins (congrArg
    (fun firing : FiringEvidence (.origin : ContextCategory arity) Origins
      (fun occurrence => mapReactionRule (declarations occurrence)) => firing.occurrence) same)

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments.Source
