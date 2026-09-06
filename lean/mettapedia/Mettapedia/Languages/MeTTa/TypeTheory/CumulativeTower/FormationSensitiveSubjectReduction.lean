import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveProjection

/-!
# Contextual subject reduction for formation-sensitive typing

Primitive head and declared-root preservation, universe regularity, and
Pi/Sigma conversion qualification suffice for preservation of every existing
contextual step. The proof follows refined typing, including computation in
binder types, dependent arguments, pair components, and identity endpoints.
It reuses checked context conversion and restores formed result types.

Only primitive rule obligations are parameters. No contextual preservation
theorem, normalization claim, or new typing rule is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace FormationSensitive

variable {Head : Type} {n : Nat} {R : Rules Head}

/-- Preservation required only for a primitive universe-head equation at a
primitive head typing, before any cumulative or conversion tail. -/
abbrev HeadPreservation (R : Rules Head) : Prop :=
  ∀ {n : Nat} {Γ : Ctx Head n} {head next u : Head},
    R.headTyping head u → R.headEq head next → Typing R Γ (.head next) (.head u)

/-- Preservation required only for the declared root rules, not their
contextual closure or the built-in beta and projection rules. -/
abbrev RootPreservation (R : Rules Head) : Prop :=
  ∀ {n : Nat} {Γ : Ctx Head n} {source target type : Tm Head n},
    ContextFormation R Γ → Typing R Γ source type →
      R.computation.step source target → Typing R Γ target type

/-- Every contextual computation preserves the actual displayed type of
the refined derivation. This includes reductions beneath dependent binders. -/
theorem Typing.step_preserves
    (universes : UniverseRegularity R) (piBoundary : PiConversionBoundary R)
    (sigmaBoundary : SigmaConversionBoundary R) (heads : HeadPreservation R)
    (roots : RootPreservation R)
    {Γ : Ctx Head n} {term type : Tm Head n} (typing : Typing R Γ term type) :
    ContextFormation R Γ → ∀ {target : Tm Head n},
      Step R.headEq term target R.computation → Typing R Γ target type := by
  induction typing with
  | headType headTyped =>
      intro context target step
      cases step with
      | head equality => exact heads headTyped equality
      | root equation => exact roots context (.headType headTyped) equation
  | var index =>
      intro context target step
      cases step with
      | root equation => exact roots context (.var index) equation
  | const known formed universeWitness _ =>
      intro context target step
      cases step with
      | root equation => exact roots context (.const known formed universeWitness) equation
  | piForm formedA universeA formedB universeB join ihA ihB =>
      intro context target step
      cases step with
      | root equation => exact roots context (.piForm formedA universeA formedB universeB join) equation
      | congPiDom nested =>
          exact .piForm (ihA context nested) universeA
            (formedB.convertNewest formedA universeA (.rel _ _ nested)) universeB join
      | congPiCod nested =>
          exact .piForm formedA universeA (ihB (.snoc context formedA universeA) nested)
            universeB join
  | sigmaForm formedA universeA formedB universeB join ihA ihB =>
      intro context target step
      cases step with
      | root equation => exact roots context (.sigmaForm formedA universeA formedB universeB join) equation
      | congSigmaDom nested =>
          exact .sigmaForm (ihA context nested) universeA
            (formedB.convertNewest formedA universeA (.rel _ _ nested)) universeB join
      | congSigmaCod nested =>
          exact .sigmaForm formedA universeA (ihB (.snoc context formedA universeA) nested)
            universeB join
  | lamIntro formed universeWitness bodyTyped _ ihBody =>
      intro context target step
      cases step with
      | root equation => exact roots context (.lamIntro formed universeWitness bodyTyped) equation
      | congLam nested =>
          obtain ⟨u, v, w, formedA, universeA, formedB, universeB, join⟩ := formed.piFormation
          exact .lamIntro formed universeWitness (ihBody (.snoc context formedA universeA) nested)
  | @appElim n Γ function argument A B functionTyped argumentTyped ihFunction ihArgument =>
      intro context target step
      cases step with
      | root equation => exact roots context (.appElim functionTyped argumentTyped) equation
      | betaPi body argument =>
          exact (Typing.appElim functionTyped argumentTyped).betaPi universes piBoundary context
      | congAppFun nested => exact .appElim (ihFunction context nested) argumentTyped
      | congAppArg nested =>
          have backwards : Conv R.headEq _ _ R.computation := .symm _ _ (.rel _ _ nested)
          exact (Typing.appElim functionTyped (ihArgument context nested)).withResultOf
            (.appElim functionTyped argumentTyped) universes context (backwards.inst0Argument B)
  | @pairIntro n Γ first second A B u formed universeWitness firstTyped secondTyped
      _ ihFirst ihSecond =>
      intro context target step
      cases step with
      | root equation =>
          exact roots context (.pairIntro formed universeWitness firstTyped secondTyped) equation
      | congPairFst nested =>
          have nextFirst := ihFirst context nested
          obtain ⟨v, w, x, formedA, universeA, formedB, universeB, join⟩ := formed.sigmaFormation
          have resultFormed := formedB.instantiate nextFirst
          have argumentConversion : Conv R.headEq _ _ R.computation := .rel _ _ nested
          exact .pairIntro formed universeWitness nextFirst
            (.conv secondTyped resultFormed universeB (argumentConversion.inst0Argument B))
      | congPairSnd nested =>
          exact .pairIntro formed universeWitness firstTyped (ihSecond context nested)
  | fstElim pairTyped ihPair =>
      intro context target step
      cases step with
      | root equation => exact roots context (.fstElim pairTyped) equation
      | betaSigmaFst first second =>
          exact pairTyped.betaSigmaFst universes sigmaBoundary context
      | congFst nested => exact .fstElim (ihPair context nested)
  | @sndElim n Γ pair A B pairTyped ihPair =>
      intro context target step
      cases step with
      | root equation => exact roots context (.sndElim pairTyped) equation
      | betaSigmaSnd first second =>
          exact pairTyped.betaSigmaSnd universes sigmaBoundary context
      | congSnd nested =>
          have backwards : Conv R.headEq _ _ R.computation :=
            .symm _ _ (.rel _ _ (.congFst nested))
          exact (Typing.sndElim (ihPair context nested)).withResultOf
            (.sndElim pairTyped) universes context (backwards.inst0Argument B)
  | idForm formed universeWitness leftTyped rightTyped ihA ihLeft ihRight =>
      intro context target step
      cases step with
      | root equation => exact roots context (.idForm formed universeWitness leftTyped rightTyped) equation
      | congIdTy nested =>
          have nextFormed := ihA context nested
          exact .idForm nextFormed universeWitness
            (.conv leftTyped nextFormed universeWitness (.rel _ _ nested))
            (.conv rightTyped nextFormed universeWitness (.rel _ _ nested))
      | congIdLeft nested => exact .idForm formed universeWitness (ihLeft context nested) rightTyped
      | congIdRight nested => exact .idForm formed universeWitness leftTyped (ihRight context nested)
  | reflIntro termTyped ihTerm =>
      intro context target step
      cases step with
      | root equation => exact roots context (.reflIntro termTyped) equation
      | congRefl nested =>
          have backwards : Conv R.headEq _ _ R.computation := .symm _ _ (.rel _ _ nested)
          exact (Typing.reflIntro (ihTerm context nested)).withResultOf
            (.reflIntro termTyped) universes context
            (Conv.congId (.refl _) backwards backwards)
  | cumul typed order ih =>
      intro context target step
      exact .cumul (ih context step) order
  | conv typed formed universeWitness conversion ih _ =>
      intro context target step
      exact .conv (ih context step) formed universeWitness conversion

theorem Judgment.step_preserves
    (universes : UniverseRegularity R) (piBoundary : PiConversionBoundary R)
    (sigmaBoundary : SigmaConversionBoundary R) (heads : HeadPreservation R)
    (roots : RootPreservation R)
    {Γ : Ctx Head n} {source target type : Tm Head n}
    (judgment : Judgment R Γ source type)
    (step : Step R.headEq source target R.computation) : Judgment R Γ target type :=
  ⟨judgment.context,
    judgment.typing.step_preserves universes piBoundary sigmaBoundary heads roots
      judgment.context step⟩

/-- Finite runs retain the same formed context and displayed result type. -/
theorem Judgment.steps_preserve
    (universes : UniverseRegularity R) (piBoundary : PiConversionBoundary R)
    (sigmaBoundary : SigmaConversionBoundary R) (heads : HeadPreservation R)
    (roots : RootPreservation R)
    {Γ : Ctx Head n} {source target type : Tm Head n}
    (judgment : Judgment R Γ source type)
    (steps : ConversionCoherence.StepStar R source target) : Judgment R Γ target type := by
  induction steps with
  | refl => exact judgment
  | tail previous finalStep ih =>
      exact ih.step_preserves universes piBoundary sigmaBoundary heads roots finalStep

#print axioms Typing.step_preserves
#print axioms Judgment.step_preserves
#print axioms Judgment.steps_preserve

end FormationSensitive
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
