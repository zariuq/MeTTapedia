import Mettapedia.OSLF.Framework.InstrumentCutKitCategory

/-!
# Complete transition reflection on the supported context grammar

An old supported source and label force the entire matched redex and reaction
context to remain in the old grammar. Administrative redexes then recover the
old instrument permission, while proper source rules preserve support
independently. The same retained rule, occurrence origin and target witness
therefore give an old transition; no fresh-label or target-closure assumption
is supplied.
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

local instance instrumentCutKitTransitionsQuiver : Quiver (Srt Symbols arity) :=
  frameQuiver (signature arity)

theorem kit_rule_support_recover {Origins : Type w}
    {first second : InstrumentObservations.Policy Symbols}
    {proper : SourceRule arity → Prop}
    {rule : ReactionRule (.origin : ContextObject (signature arity))}
    (membership : kitRules arity Origins second proper rule)
    (redexSupported : KitArrow arity first rule.redex) :
    kitRules arity Origins first proper rule ∧ KitArrow arity first rule.reactum := by
  rcases membership with ⟨instrument, occurrence, _, rfl⟩ | ⟨sourceRule, admitted, rfl⟩
  · cases redexSupported with
    | value supported =>
      obtain ⟨permission, outputSupported⟩ := administrative_support arity occurrence.instance_ supported
      exact ⟨Or.inl ⟨instrument, occurrence, permission, rfl⟩, .value outputSupported⟩
  · exact ⟨Or.inr ⟨sourceRule, admitted, rfl⟩, (proper_rule_support arity first sourceRule).2⟩

/-- Every supplied larger-kit firing is reconstructed with its identical rule,
reaction context, leastness witness and complete target. This theorem does not
require inclusion of the two policies; hereditary support alone forces the
permission needed for this actual firing. -/
theorem kit_step_support_recover {Origins : Type w}
    {first second : InstrumentObservations.Policy Symbols}
    {proper : SourceRule arity → Prop} {sourceInterface targetInterface : ContextObject (signature arity)}
    {label : sourceInterface ⟶ targetInterface}
    {source : (.origin : ContextObject (signature arity)) ⟶ sourceInterface}
    {target : (.origin : ContextObject (signature arity)) ⟶ targetInterface}
    (sourceSupported : KitArrow arity first source) (labelSupported : KitArrow arity first label)
    (step : ActIPO (kitRules arity Origins second proper) label source target) :
    KitArrow arity first target ∧
      ∃ rule, kitRules arity Origins first proper rule ∧
        KitArrow arity first rule.redex ∧ KitArrow arity first rule.reactum ∧
        ∃ reaction : rule.codomain ⟶ targetInterface, KitArrow arity first reaction ∧
          ∃ square : source ≫ label = rule.redex ≫ reaction,
            IsIdemPushout source rule.redex label reaction square ∧ target = rule.reactum ≫ reaction := by
  obtain ⟨rule, membership, reaction, square, ipo, targetReadout⟩ := step
  have filledSupported : KitArrow arity first (rule.redex ≫ reaction) :=
    square ▸ sourceSupported.comp arity labelSupported
  obtain ⟨redexSupported, reactionSupported⟩ := kitArrow_comp_inv arity rule.redex reaction filledSupported
  obtain ⟨oldMembership, reactumSupported⟩ := kit_rule_support_recover arity membership redexSupported
  exact ⟨targetReadout.symm ▸ reactumSupported.comp arity reactionSupported,
    rule, oldMembership, redexSupported, reactumSupported, reaction, reactionSupported,
    square, ipo, targetReadout⟩

theorem kit_step_old_label_target_closure {Origins : Type w}
    {first second : InstrumentObservations.Policy Symbols}
    {proper : SourceRule arity → Prop} {sourceInterface targetInterface : ContextObject (signature arity)}
    {label : sourceInterface ⟶ targetInterface}
    {source : (.origin : ContextObject (signature arity)) ⟶ sourceInterface}
    {target : (.origin : ContextObject (signature arity)) ⟶ targetInterface}
    (sourceSupported : KitArrow arity first source) (labelSupported : KitArrow arity first label)
    (step : ActIPO (kitRules arity Origins second proper) label source target) :
    KitArrow arity first target ∧ ActIPO (kitRules arity Origins first proper) label source target := by
  obtain ⟨targetSupported, rule, admitted, _, _, reaction, _, square, ipo, targetReadout⟩ :=
    kit_step_support_recover arity sourceSupported labelSupported step
  exact ⟨targetSupported, rule, admitted, reaction, square, ipo, targetReadout⟩

def kitRuleImage {opened : InstrumentObservations.Policy Symbols}
    (rule : ReactionRule (kitOrigin arity opened)) :
    ReactionRule (.origin : ContextObject (signature arity)) where
  codomain := rule.codomain.base
  redex := rule.redex.val
  reactum := rule.reactum.val

def kitCategoryRules (Origins : Type w) (opened : InstrumentObservations.Policy Symbols)
    (proper : SourceRule arity → Prop) (rule : ReactionRule (kitOrigin arity opened)) : Prop :=
  kitRules arity Origins opened proper (kitRuleImage arity rule)

theorem kit_category_step_iff (Origins : Type w) (opened : InstrumentObservations.Policy Symbols)
    (proper : SourceRule arity → Prop) {sourceInterface targetInterface : KitObject arity opened}
    (label : sourceInterface ⟶ targetInterface) (source : kitOrigin arity opened ⟶ sourceInterface)
    (target : kitOrigin arity opened ⟶ targetInterface) :
    ActIPO (kitCategoryRules arity Origins opened proper) label source target ↔
      ActIPO (kitRules arity Origins opened proper) label.val source.val target.val := by
  constructor
  · rintro ⟨rule, admitted, reaction, square, ipo, targetReadout⟩
    exact ⟨kitRuleImage arity rule, admitted, reaction.val, congrArg Subtype.val square,
      (kit_idemPushout_iff arity square).mp ipo, congrArg Subtype.val targetReadout⟩
  · intro step
    obtain ⟨_, rule, admitted, redexSupported, reactumSupported, reaction, reactionSupported,
      square, ipo, targetReadout⟩ := kit_step_support_recover arity source.property label.property step
    let lifted : ReactionRule (kitOrigin arity opened) :=
      { codomain := ⟨rule.codomain⟩
        redex := ⟨rule.redex, redexSupported⟩
        reactum := ⟨rule.reactum, reactumSupported⟩ }
    let liftedReaction : lifted.codomain ⟶ targetInterface := ⟨reaction, reactionSupported⟩
    have liftedSquare : source ≫ label = lifted.redex ≫ liftedReaction := Subtype.ext square
    refine ⟨lifted, admitted, liftedReaction, liftedSquare, ?_, Subtype.ext targetReadout⟩
    exact (kit_idemPushout_iff arity liftedSquare).mpr ipo

end Mettapedia.OSLF.Framework.InstrumentCutContexts
