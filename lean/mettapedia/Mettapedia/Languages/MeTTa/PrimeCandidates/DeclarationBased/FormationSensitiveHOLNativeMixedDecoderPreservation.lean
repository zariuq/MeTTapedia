import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveHOLNativeMixedSchemas

/-!
# HOL decoder preservation with native computation available

The decoder's independently formed declarations are included through the
proved rules morphism. Argument recovery and type-adjustment replay use
the actual mixed conversion boundary.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace FormationSensitiveHOLNativeMixedDecoderPreservation

open Presentation Presentation.Declaration Presentation.FormationSensitive
open FormationSensitiveHOLProofFamily
open FormationSensitiveHOLNativeMixedSchemas (universes)
open HOLNativeMixedConversionParallel (mixedPiConversionBoundary)

abbrev jointRules := FormationSensitiveHOLProofListIntegration.rules

theorem pi_zero {n : Nat} {gamma : Tower.Ctx n}
    {a : Tower.Tm n} {b : Tower.Tm (n + 1)}
    (domain : FormationSensitive.Typing jointRules gamma a (sortTm Tower.zero))
    (codomain : FormationSensitive.Typing jointRules (.snoc gamma a) b (sortTm Tower.zero)) :
    FormationSensitive.Typing jointRules gamma (.pi a b) (sortTm Tower.zero) := by
  apply FormationSensitive.Typing.cumul
    (.piForm domain (.sort Tower.zero) codomain (.sort Tower.zero)
      (.sorts Tower.zero Tower.zero))
  intro valuation
  simp [LevelExpr.eval, Tower.zero]

theorem proof_formed {n : Nat} {gamma : Tower.Ctx n} {p : Tower.Tm n}
    (typed : FormationSensitive.Typing jointRules gamma p (.const `HOLUniformList.prop)) :
    FormationSensitive.Typing jointRules gamma (proof p) (sortTm Tower.zero) := by
  have applied := FormationSensitive.Typing.appElim
    (FormationSensitiveHOLProofListIntegration.proof_typed (proofConstant_typed gamma)) typed
  simpa only [proofType, proof, sortTm, liftClosed, Presentation.rename, inst0,
    Presentation.subst] using applied

theorem implication_formed {n : Nat} {gamma : Tower.Ctx n} {p q : Tower.Tm n}
    (hp : FormationSensitive.Typing jointRules gamma p (.const `HOLUniformList.prop))
    (hq : FormationSensitive.Typing jointRules gamma q (.const `HOLUniformList.prop)) :
    FormationSensitive.Typing jointRules gamma (implicationFamily p q) (sortTm Tower.zero) :=
  pi_zero (proof_formed hp) ((proof_formed hq).weaken)

theorem universal_formed {n : Nat} {gamma : Tower.Ctx n} {a f : Tower.Tm n}
    (ha : FormationSensitive.Typing jointRules gamma a (sortTm Tower.zero))
    (hf : FormationSensitive.Typing jointRules gamma f (.pi a (.const `HOLUniformList.prop))) :
    FormationSensitive.Typing jointRules gamma (universalFamily a f) (sortTm Tower.zero) := by
  have applied := FormationSensitive.Typing.appElim (hf.weaken (extension := a))
    (FormationSensitive.Typing.var 0)
  have typed : FormationSensitive.Typing jointRules (.snoc gamma a)
      (.app (Presentation.rename wk f) (.var 0)) (.const `HOLUniformList.prop) := by
    simpa only [Presentation.rename, inst0, Presentation.subst] using applied
  exact pi_zero ha (proof_formed typed)

theorem proofSpine {n : Nat} (gamma : Tower.Ctx n) :
    DeclarationSpine jointRules gamma (.const proofName)
      (.pi (.const `HOLUniformList.prop) (sortTm Tower.zero)) := by
  have spine : DeclarationSpine jointRules gamma (.const proofName) (liftClosed proofType) :=
    .constant (by decide) (FormationSensitiveHOLProofListIntegration.proof_typed proofType_formed) (.sort (.max Tower.zero (.succ Tower.zero)))
  simpa only [proofType, liftClosed, sortTm, rename] using spine

/-- The outer decoder declaration recovers a real proposition argument and
replays the caller's actual type adjustments on any small replacement type. -/
theorem proofArgument {n : Nat} {gamma : Tower.Ctx n} {p displayed : Tower.Tm n}
    (formed : ContextFormation jointRules gamma) (observed : FormationSensitive.Typing jointRules gamma (proof p) displayed) :
    FormationSensitive.Typing jointRules gamma p (.const `HOLUniformList.prop) ∧
      (∀ {replacement}, FormationSensitive.Typing jointRules gamma replacement (sortTm Tower.zero) →
        FormationSensitive.Typing jointRules gamma replacement displayed) := by
  obtain ⟨typed, _, _, replay⟩ :=
    (proofSpine gamma).recoverApplication universes mixedPiConversionBoundary formed observed
  exact ⟨typed, replay⟩

theorem implicationSpine {n : Nat} (gamma : Tower.Ctx n) :
    DeclarationSpine jointRules gamma (.const `HOLUniformList.implication)
      (.pi (.const `HOLUniformList.prop)
        (.pi (.const `HOLUniformList.prop) (.const `HOLUniformList.prop))) := by
  have declared : FormationSensitive.Typing jointRules .nil
      (.pi (.const `HOLUniformList.prop)
        (.pi (.const `HOLUniformList.prop) (.const `HOLUniformList.prop))) (sortTm Tower.zero) :=
    pi_zero
      (FormationSensitiveHOLProofListIntegration.proof_typed (proposition_formed _))
      (pi_zero
        (FormationSensitiveHOLProofListIntegration.proof_typed (proposition_formed _))
        (FormationSensitiveHOLProofListIntegration.proof_typed (proposition_formed _)))
  have spine := DeclarationSpine.constant (R := jointRules) (Γ := gamma)
    (name := `HOLUniformList.implication) (by decide) declared (.sort Tower.zero)
  simpa only [liftClosed, rename] using spine

theorem implicationArguments {n : Nat} {gamma : Tower.Ctx n} {p q : Tower.Tm n}
    (formed : ContextFormation jointRules gamma)
    (observed : FormationSensitive.Typing jointRules gamma (FormationSensitiveHOLUniformList.rawImp p q) (.const `HOLUniformList.prop)) :
    FormationSensitive.Typing jointRules gamma p (.const `HOLUniformList.prop) ∧
      FormationSensitive.Typing jointRules gamma q (.const `HOLUniformList.prop) := by
  obtain ⟨_, _, firstTyping, _, _, _⟩ := observed.appGeneration
  obtain ⟨pTyped, firstSpine, _, _⟩ :=
    (implicationSpine gamma).recoverApplication universes mixedPiConversionBoundary formed firstTyping
  have opened : DeclarationSpine jointRules gamma (.app (.const `HOLUniformList.implication) p)
      (.pi (.const `HOLUniformList.prop) (.const `HOLUniformList.prop)) := firstSpine
  exact ⟨pTyped, (opened.recoverApplication universes mixedPiConversionBoundary formed observed).1⟩

theorem universalSpine {n : Nat} (gamma : Tower.Ctx n) :
    DeclarationSpine jointRules gamma (.const `HOLUniformList.universal)
      (.pi (sortTm Tower.zero)
        (.pi (.pi (.var 0) (.const `HOLUniformList.prop)) (.const `HOLUniformList.prop))) := by
  have spine : DeclarationSpine jointRules gamma (.const `HOLUniformList.universal)
      (liftClosed FormationSensitiveHOLUniformList.universalType) :=
    .constant (by decide) (FormationSensitiveHOLProofListIntegration.proof_typed
      (include_typed FormationSensitiveHOLUniformList.universal_type_formed))
      (.sort (.max (.succ Tower.zero) Tower.zero))
  simpa only [FormationSensitiveHOLUniformList.universalType, liftClosed, sortTm, rename, liftRen,
    Fin.cases_zero] using spine

theorem universalArguments {n : Nat} {gamma : Tower.Ctx n} {a f : Tower.Tm n}
    (formed : ContextFormation jointRules gamma)
    (observed : FormationSensitive.Typing jointRules gamma (universalProposition a f) (.const `HOLUniformList.prop)) :
    FormationSensitive.Typing jointRules gamma a (sortTm Tower.zero) ∧
      FormationSensitive.Typing jointRules gamma f (.pi a (.const `HOLUniformList.prop)) := by
  obtain ⟨_, _, firstTyping, _, _, _⟩ := observed.appGeneration
  obtain ⟨aTyped, firstSpine, _, _⟩ :=
    (universalSpine gamma).recoverApplication universes mixedPiConversionBoundary formed firstTyping
  have opened : DeclarationSpine jointRules gamma (.app (.const `HOLUniformList.universal) a)
      (.pi (.pi a (.const `HOLUniformList.prop)) (.const `HOLUniformList.prop)) := by
    simpa only [inst0, subst, liftSub, subst0, consSub, Fin.cases_zero] using firstSpine
  exact ⟨aTyped, (opened.recoverApplication universes mixedPiConversionBoundary formed observed).1⟩


theorem decoder_preserves {n : Nat} {gamma : Tower.Ctx n}
    {source target displayed : Tower.Tm n}
    (formed : ContextFormation jointRules gamma)
    (observed : FormationSensitive.Typing jointRules gamma source displayed)
    (decoder : DecoderStep source target) :
    FormationSensitive.Typing jointRules gamma target displayed := by
  cases decoder with
  | implication p q =>
      obtain ⟨proposition, replay⟩ := proofArgument formed observed
      obtain ⟨hp, hq⟩ := implicationArguments formed proposition
      exact replay (implication_formed hp hq)
  | universal a f =>
      obtain ⟨proposition, replay⟩ := proofArgument formed observed
      obtain ⟨ha, hf⟩ := universalArguments formed proposition
      exact replay (universal_formed ha hf)

#print axioms proof_formed
#print axioms implication_formed
#print axioms universal_formed
#print axioms proofArgument
#print axioms implicationArguments
#print axioms universalArguments
#print axioms decoder_preserves

end FormationSensitiveHOLNativeMixedDecoderPreservation
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

