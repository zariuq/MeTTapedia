import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeBooleanRelatorPreservation
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeBooleanConversion

/-!
# Preservation for the full native Boolean, List, J and relator package

All seven installed roots are qualified against arbitrary formation-sensitive
source judgments in the same extended calculus. The contextual theorem includes
the inherited lambda, pair and identity congruences. It is finite subject
reduction, not a normalization theorem or a total conversion algorithm.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeBooleanPreservation

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation Presentation.Declaration Presentation.FormationSensitive
open NativeIndexedFamilies
open SharedJudgmentNativeBooleanRootPreservation

abbrev rules := SharedJudgmentNativeBooleanRegion.rules

private theorem emptyOpacity : OpaqueRelatorExtension.Opacity (Signature.empty : Signature Tower.Head) :=
  ⟨fun _ => rfl, fun impossible => impossible.elim⟩

theorem rootPreservationOfPi (boundary : PiConversionBoundary rules) : RootPreservation rules := by
  intro n context source target displayed formed observed root
  cases root with
  | delta lookup =>
      rw [SharedJudgmentNativeBooleanRegion.signature_valueOf_none] at lookup
      cases lookup
  | declared evidence =>
      rcases evidence with ⟨evidence⟩
      exact boolean_preserves boundary formed evidence observed
  | inherited root =>
      have native := (NativeIdentityLevelInstantiation.root_iff theta emptyOpacity).mp root
      cases native with
      | inherited impossible => exact impossible.elim
      | delta lookup =>
          rw [IntrinsicRelator.rawSignature_valueOf_none] at lookup
          cases lookup
      | declared evidence =>
          rcases evidence with ⟨evidence⟩
          cases evidence with
          | list evidence =>
              cases evidence with
              | nil => exact listNil_preserves boundary formed observed
              | cons => exact listCons_preserves boundary formed observed
              | identity => exact identity_preserves boundary formed observed
          | rel evidence =>
              exact SharedJudgmentNativeBooleanRelatorPreservation.iota_preserves
                boundary formed evidence observed

theorem headPreservation : HeadPreservation rules :=
  HeadPreservation.includeSignature
    (HeadPreservation.includeSignature
      (HeadPreservation.includeSignature towerHeadPreservation
        (NativeIdentityLevelInstantiation.nativeInstance theta).signature)
      (NativeIdentityLevelInstantiation.extensionSignature theta Signature.empty))
    SharedJudgmentNativeBooleanRegion.signature

theorem step_preserves_of_boundaries (piBoundary : PiConversionBoundary rules)
    (sigmaBoundary : SigmaConversionBoundary rules)
    {n : Nat} {context : Tower.Ctx n} {source target displayed : Tower.Tm n}
    (judgment : Judgment rules context source displayed)
    (step : Step rules.headEq source target rules.computation) :
    Judgment rules context target displayed :=
  judgment.step_preserves universes piBoundary sigmaBoundary headPreservation
    (rootPreservationOfPi piBoundary) step

theorem steps_preserve_of_boundaries (piBoundary : PiConversionBoundary rules)
    (sigmaBoundary : SigmaConversionBoundary rules)
    {n : Nat} {context : Tower.Ctx n} {source target displayed : Tower.Tm n}
    (judgment : Judgment rules context source displayed)
    (steps : ConversionCoherence.StepStar rules source target) :
    Judgment rules context target displayed :=
  judgment.steps_preserve universes piBoundary sigmaBoundary headPreservation
    (rootPreservationOfPi piBoundary) steps

/-- Every installed root preserves the original displayed type. The actual
extended conversion boundary is proved, not supplied by the caller. -/
theorem rootPreservation : RootPreservation rules :=
  rootPreservationOfPi SharedJudgmentNativeBooleanParallel.nativePiConversionBoundary

/-- Subject reduction for arbitrary admitted terms, including terms with
Boolean elimination inside native List, identity and relator applications. -/
theorem step_preserves {n : Nat} {context : Tower.Ctx n}
    {source target displayed : Tower.Tm n}
    (judgment : Judgment rules context source displayed)
    (step : Step rules.headEq source target rules.computation) :
    Judgment rules context target displayed :=
  step_preserves_of_boundaries SharedJudgmentNativeBooleanParallel.nativePiConversionBoundary
    SharedJudgmentNativeBooleanParallel.nativeSigmaConversionBoundary judgment step

theorem steps_preserve {n : Nat} {context : Tower.Ctx n}
    {source target displayed : Tower.Tm n}
    (judgment : Judgment rules context source displayed)
    (steps : ConversionCoherence.StepStar rules source target) :
    Judgment rules context target displayed :=
  steps_preserve_of_boundaries SharedJudgmentNativeBooleanParallel.nativePiConversionBoundary
    SharedJudgmentNativeBooleanParallel.nativeSigmaConversionBoundary judgment steps

#print axioms rootPreservation
#print axioms step_preserves
#print axioms steps_preserve

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeBooleanPreservation
