import Mettapedia.OSLF.Framework.SortedTypedInstrumentKitReactions

/-!
# Old typed labels reconstruct full kit firings and targets

The actual square and hereditary factor closure force the matched redex and
reaction context into the old grammar. Redex inversion then recovers the
original declaration or complete administrative occurrence with its authored
origin. Its independently derived reactum support closes the whole target.
No unique-target or ambient-fullness assumption is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RelativePushout Mettapedia.GSLT.RedexRelativeCongruence

universe u v w z

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop} {OriginalOrigins : Type z} {NativeOrigins : Type w}

def ambientRules
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (opened : Policy source Parallel)
    (rule : ReactionRule (.origin : ContextCategory source Parallel)) : Prop :=
  ∃ declaration : Declaration source Parallel OriginalOrigins NativeOrigins opened,
    ruleImage (declaration.rule originalRules) = rule

theorem ambient_step_support_recover {first second : Policy source Parallel}
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    {before after : ContextCategory source Parallel}
    {agent : (.origin : ContextCategory source Parallel) ⟶ before} {label : before ⟶ after}
    {target : (.origin : ContextCategory source Parallel) ⟶ after}
    (agentSupported : ArrowSupported first agent) (labelSupported : ArrowSupported first label)
    (step : ActIPO (ambientRules (NativeOrigins := NativeOrigins) originalRules second) label agent target) :
    ArrowSupported first target ∧
      ∃ declaration : Declaration source Parallel OriginalOrigins NativeOrigins second,
        ∃ oldDeclaration : Declaration source Parallel OriginalOrigins NativeOrigins first,
          oldDeclaration.origin = declaration.origin ∧
          ruleImage (oldDeclaration.rule originalRules) = ruleImage (declaration.rule originalRules) ∧
          ArrowSupported first (ruleImage (declaration.rule originalRules)).redex ∧
          ArrowSupported first (ruleImage (declaration.rule originalRules)).reactum ∧
          ∃ reaction : (ruleImage (declaration.rule originalRules)).codomain ⟶ after,
            ArrowSupported first reaction ∧
            ∃ square : agent ≫ label = (ruleImage (declaration.rule originalRules)).redex ≫ reaction,
              IsIdemPushout agent (ruleImage (declaration.rule originalRules)).redex label reaction square ∧
                target = (ruleImage (declaration.rule originalRules)).reactum ≫ reaction := by
  obtain ⟨_, ⟨declaration, rfl⟩, reaction, square, minimal, resultRead⟩ := step
  have filledSupported : ArrowSupported first ((ruleImage (declaration.rule originalRules)).redex ≫ reaction) :=
    square ▸ agentSupported.comp labelSupported
  obtain ⟨redexSupported, reactionSupported⟩ :=
    (arrow_supported_comp_iff first _ _).mp filledSupported
  have outputSupported := declaration.reactum_support_recover originalRules redexSupported
  exact ⟨resultRead.symm ▸ outputSupported.comp reactionSupported,
    declaration, declaration.recover originalRules redexSupported,
    declaration.recover_origin originalRules redexSupported,
    declaration.recover_ruleImage originalRules redexSupported,
    redexSupported, outputSupported, reaction, reactionSupported, square, minimal, resultRead⟩

theorem ambient_old_label_target_closure {first second : Policy source Parallel}
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    {before after : ContextCategory source Parallel}
    {agent : (.origin : ContextCategory source Parallel) ⟶ before} {label : before ⟶ after}
    {target : (.origin : ContextCategory source Parallel) ⟶ after}
    (agentSupported : ArrowSupported first agent) (labelSupported : ArrowSupported first label)
    (step : ActIPO (ambientRules (NativeOrigins := NativeOrigins) originalRules second) label agent target) :
    ArrowSupported first target ∧
      ActIPO (ambientRules (NativeOrigins := NativeOrigins) originalRules first) label agent target := by
  obtain ⟨targetSupported, declaration, oldDeclaration, _, declarationRead,
    _, _, reaction, _, square, minimal, resultRead⟩ :=
    ambient_step_support_recover originalRules agentSupported labelSupported step
  exact ⟨targetSupported, ruleImage (declaration.rule originalRules),
    ⟨oldDeclaration, declarationRead⟩, reaction, square, minimal, resultRead⟩

theorem category_step_iff (opened : Policy source Parallel)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    {before after : Object opened} (agent : origin opened ⟶ before) (label : before ⟶ after)
    (target : origin opened ⟶ after) :
    ActIPO (categoryRules (NativeOrigins := NativeOrigins) originalRules opened) label agent target ↔
      ActIPO (ambientRules (NativeOrigins := NativeOrigins) originalRules opened) label.val agent.val target.val := by
  constructor
  · rintro ⟨_, ⟨declaration, rfl⟩, reaction, square, minimal, resultRead⟩
    exact ⟨ruleImage (declaration.rule originalRules), ⟨declaration, rfl⟩,
      reaction.val, congrArg Subtype.val square, (idemPushout_iff square).mp minimal,
      congrArg Subtype.val resultRead⟩
  · rintro ⟨_, ⟨declaration, rfl⟩, reaction, square, minimal, resultRead⟩
    have filledSupported : ArrowSupported opened ((ruleImage (declaration.rule originalRules)).redex ≫ reaction) :=
      square ▸ agent.property.comp label.property
    let lifted : (declaration.rule originalRules).codomain ⟶ after :=
      ⟨reaction, ((arrow_supported_comp_iff opened _ _).mp filledSupported).2⟩
    have liftedSquare : agent ≫ label = (declaration.rule originalRules).redex ≫ lifted := Subtype.ext square
    exact ⟨declaration.rule originalRules, ⟨declaration, rfl⟩, lifted, liftedSquare,
      (idemPushout_iff liftedSquare).mpr minimal, Subtype.ext resultRead⟩

theorem ambient_step_maps {first second : Policy source Parallel}
    (subkit : ∀ head, first head → second head)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    {before after : ContextCategory source Parallel}
    {agent : (.origin : ContextCategory source Parallel) ⟶ before} {label : before ⟶ after}
    {target : (.origin : ContextCategory source Parallel) ⟶ after}
    (step : ActIPO (ambientRules (NativeOrigins := NativeOrigins) originalRules first) label agent target) :
    ActIPO (ambientRules (NativeOrigins := NativeOrigins) originalRules second) label agent target := by
  obtain ⟨_, ⟨declaration, rfl⟩, reaction, square, minimal, resultRead⟩ := step
  have same : ruleImage ((declaration.expand subkit).rule originalRules) =
      ruleImage (declaration.rule originalRules) := by
    cases declaration <;> rfl
  exact ⟨ruleImage (declaration.rule originalRules), ⟨declaration.expand subkit, same⟩,
    reaction, square, minimal, resultRead⟩

theorem category_step_maps {first second : Policy source Parallel}
    (subkit : ∀ head, first head → second head)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    {before after : Object first} {agent : origin first ⟶ before} {label : before ⟶ after}
    {target : origin first ⟶ after}
    (step : ActIPO (categoryRules (NativeOrigins := NativeOrigins) originalRules first) label agent target) :
    ActIPO (categoryRules (NativeOrigins := NativeOrigins) originalRules second)
      ((expand subkit).map label) ((expand subkit).map agent) ((expand subkit).map target) :=
  (category_step_iff second originalRules _ _ _).mpr
    (ambient_step_maps subkit originalRules ((category_step_iff first originalRules _ _ _).mp step))

theorem category_step_reflect {first second : Policy source Parallel}
    (subkit : ∀ head, first head → second head)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    {before after : Object first} {agent : origin first ⟶ before} {label : before ⟶ after}
    {target : origin second ⟶ (expand subkit).obj after}
    (step : ActIPO (categoryRules (NativeOrigins := NativeOrigins) originalRules second)
      ((expand subkit).map label) ((expand subkit).map agent) target) :
    ∃ oldTarget : origin first ⟶ after,
      (expand subkit).map oldTarget = target ∧
        ActIPO (categoryRules (NativeOrigins := NativeOrigins) originalRules first) label agent oldTarget := by
  have ambient := (category_step_iff second originalRules _ _ _).mp step
  obtain ⟨targetSupported, oldStep⟩ :=
    ambient_old_label_target_closure originalRules agent.property label.property ambient
  let oldTarget : origin first ⟶ after := ⟨target.val, targetSupported⟩
  exact ⟨oldTarget, Subtype.ext rfl, (category_step_iff first originalRules _ _ _).mpr oldStep⟩

end Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit
