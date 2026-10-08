import Mettapedia.GSLT.Logic.RelativePushoutFunctor
import Mettapedia.GSLT.Logic.RedexRelativeCongruence

/-!
# Complete reactive comparison through a based hom equivalence

Full faithful functors with surjective object actions transport complete IPO
firings in both directions. The result retains the mapped rule, reaction
context and target equation. Bisimulation families are transported at every
interface and arbitrary literal label. No adequacy premise or ground-action
injectivity is supplied.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.RedexRelativeCongruence

open _root_.CategoryTheory
open Mettapedia.GSLT.RelativePushout

universe u v u' v'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (F : C ⥤ D) {origin : C}

def mapReaction (rule : ReactionRule origin) : ReactionRule (F.obj origin) where
  codomain := F.obj rule.codomain
  redex := F.map rule.redex
  reactum := F.map rule.reactum

def mappedRules (rules : ReactionRule origin → Prop) (rule : ReactionRule (F.obj origin)) : Prop :=
  ∃ original, rules original ∧ rule = mapReaction F original

def pullbackRules (rules : ReactionRule (F.obj origin) → Prop) (rule : ReactionRule origin) : Prop :=
  rules (mapReaction F rule)

variable [F.Full] [F.Faithful] (objects : Function.Surjective F.obj)
include objects

omit [F.Faithful] in
theorem mappedRules_pullback (rules : ReactionRule (F.obj origin) → Prop) :
    mappedRules F (pullbackRules F rules) = rules := by
  funext rule
  apply propext
  constructor
  · rintro ⟨original, admitted, rfl⟩
    exact admitted
  · intro admitted
    rcases rule with ⟨interface, redex, reactum⟩
    obtain ⟨originalInterface, rfl⟩ := objects interface
    let original : ReactionRule origin :=
      { codomain := originalInterface, redex := F.preimage redex, reactum := F.preimage reactum }
    have readout : mapReaction F original = ⟨F.obj originalInterface, redex, reactum⟩ := by
      simp only [mapReaction, original, F.map_preimage]
    refine ⟨original, ?_, readout.symm⟩
    change rules (mapReaction F original)
    exact readout.symm ▸ admitted

set_option backward.isDefEq.respectTransparency false in
theorem mapped_step_iff (rules : ReactionRule origin → Prop) {sourceInterface targetInterface : C}
    (label : sourceInterface ⟶ targetInterface) (source : origin ⟶ sourceInterface)
    (target : origin ⟶ targetInterface) :
    ActIPO rules label source target ↔
      ActIPO (mappedRules F rules) (F.map label) (F.map source) (F.map target) := by
  constructor
  · rintro ⟨rule, admitted, reaction, square, ipo, targetReadout⟩
    have mappedSquare : F.map source ≫ F.map label = F.map rule.redex ≫ F.map reaction := by
      rw [← F.map_comp, square, F.map_comp]
    exact ⟨mapReaction F rule, ⟨rule, admitted, rfl⟩, F.map reaction, mappedSquare,
      preserves_idemPushout F objects square ipo,
      by simpa only [mapReaction, F.map_comp] using congrArg F.map targetReadout⟩
  · rintro ⟨rule, ⟨original, admitted, rfl⟩, reaction, square, ipo, targetReadout⟩
    have originalSquare : source ≫ label = original.redex ≫ F.preimage reaction := by
      apply F.map_injective
      simpa only [F.map_comp, F.map_preimage, mapReaction] using square
    refine ⟨original, admitted, F.preimage reaction, originalSquare, ?_, ?_⟩
    · apply reflects_idemPushout F originalSquare
      simpa only [F.map_preimage, mapReaction] using ipo
    · apply F.map_injective
      simpa only [F.map_comp, F.map_preimage, mapReaction] using targetReadout

theorem reflects_mapped_bisimilar (rules : ReactionRule origin → Prop)
    {interface : C} {first second : origin ⟶ interface}
    (related : IPOBisimilar (mappedRules F rules) (F.map first) (F.map second)) :
    IPOBisimilar rules first second := by
  let relation : (interface : C) → (origin ⟶ interface) → (origin ⟶ interface) → Prop :=
    fun _ left right => IPOBisimilar (mappedRules F rules) (F.map left) (F.map right)
  refine ⟨relation, ?_, related⟩
  intro current left right paired
  constructor
  · intro nextInterface label next step
    obtain ⟨matched, matchedStep, successors⟩ := ipoBisimilar_forward paired
      ((mapped_step_iff F objects rules label left next).mp step)
    refine ⟨F.preimage matched, ?_, ?_⟩
    · apply (mapped_step_iff F objects rules label right (F.preimage matched)).mpr
      simpa only [F.map_preimage] using matchedStep
    · change IPOBisimilar (mappedRules F rules) (F.map next) (F.map (F.preimage matched))
      simpa only [F.map_preimage] using successors
  · intro nextInterface label next step
    obtain ⟨matched, matchedStep, successors⟩ := ipoBisimilar_backward paired
      ((mapped_step_iff F objects rules label right next).mp step)
    refine ⟨F.preimage matched, ?_, ?_⟩
    · apply (mapped_step_iff F objects rules label left (F.preimage matched)).mpr
      simpa only [F.map_preimage] using matchedStep
    · change IPOBisimilar (mappedRules F rules) (F.map (F.preimage matched)) (F.map next)
      simpa only [F.map_preimage] using successors

theorem preserves_mapped_bisimilar (rules : ReactionRule origin → Prop)
    {interface : C} {first second : origin ⟶ interface}
    (related : IPOBisimilar rules first second) :
    IPOBisimilar (mappedRules F rules) (F.map first) (F.map second) := by
  let relation : (interface : D) → (F.obj origin ⟶ interface) → (F.obj origin ⟶ interface) → Prop :=
    fun target left right => ∃ current : C, ∃ endpoint : F.obj current = target,
      ∃ before after : origin ⟶ current, IPOBisimilar rules before after ∧
        left = F.map before ≫ eqToHom endpoint ∧ right = F.map after ≫ eqToHom endpoint
  refine ⟨relation, ?_, interface, rfl, first, second, related, by simp, by simp⟩
  intro current left right paired
  obtain ⟨originalInterface, endpoint, before, after, originalRelated, leftReadout, rightReadout⟩ := paired
  cases endpoint
  simp only [eqToHom_refl, Category.comp_id] at leftReadout rightReadout
  cases leftReadout
  cases rightReadout
  constructor
  · intro nextInterface label next step
    obtain ⟨originalNextInterface, rfl⟩ := objects nextInterface
    have originalStep : ActIPO rules (F.preimage label) before (F.preimage next) := by
      apply (mapped_step_iff F objects rules _ _ _).mpr
      simpa only [F.map_preimage] using step
    obtain ⟨matched, matchedStep, successors⟩ := ipoBisimilar_forward originalRelated originalStep
    refine ⟨F.map matched, ?_, originalNextInterface, rfl, F.preimage next, matched, successors, ?_, ?_⟩
    · simpa only [F.map_preimage] using
        (mapped_step_iff F objects rules _ _ _).mp matchedStep
    · simp only [F.map_preimage, eqToHom_refl, Category.comp_id]
    · simp only [eqToHom_refl, Category.comp_id]
  · intro nextInterface label next step
    obtain ⟨originalNextInterface, rfl⟩ := objects nextInterface
    have originalStep : ActIPO rules (F.preimage label) after (F.preimage next) := by
      apply (mapped_step_iff F objects rules _ _ _).mpr
      simpa only [F.map_preimage] using step
    obtain ⟨matched, matchedStep, successors⟩ := ipoBisimilar_backward originalRelated originalStep
    refine ⟨F.map matched, ?_, originalNextInterface, rfl, matched, F.preimage next, successors, ?_, ?_⟩
    · simpa only [F.map_preimage] using
        (mapped_step_iff F objects rules _ _ _).mp matchedStep
    · simp only [eqToHom_refl, Category.comp_id]
    · simp only [F.map_preimage, eqToHom_refl, Category.comp_id]

theorem mapped_bisimilar_iff (rules : ReactionRule origin → Prop)
    {interface : C} (first second : origin ⟶ interface) :
    IPOBisimilar rules first second ↔ IPOBisimilar (mappedRules F rules) (F.map first) (F.map second) :=
  ⟨preserves_mapped_bisimilar F objects rules, reflects_mapped_bisimilar F objects rules⟩

theorem pullback_step_iff (rules : ReactionRule (F.obj origin) → Prop)
    {sourceInterface targetInterface : C} (label : sourceInterface ⟶ targetInterface)
    (source : origin ⟶ sourceInterface) (target : origin ⟶ targetInterface) :
    ActIPO (pullbackRules F rules) label source target ↔ ActIPO rules (F.map label) (F.map source) (F.map target) := by
  have comparison := mapped_step_iff F objects (pullbackRules F rules) label source target
  rw [mappedRules_pullback F objects rules] at comparison
  exact comparison

theorem pullback_bisimilar_iff (rules : ReactionRule (F.obj origin) → Prop)
    {interface : C} (first second : origin ⟶ interface) :
    IPOBisimilar (pullbackRules F rules) first second ↔ IPOBisimilar rules (F.map first) (F.map second) := by
  have comparison := mapped_bisimilar_iff F objects (pullbackRules F rules) first second
  rw [mappedRules_pullback F objects rules] at comparison
  exact comparison

end Mettapedia.GSLT.RedexRelativeCongruence
