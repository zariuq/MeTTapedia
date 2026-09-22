import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveHOLNativeMixedListPreservation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveHOLNativeMixedRelatorPreservation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveHOLNativeMixedDecoderPreservation

/-!
# Contextual subject reduction for the actual joint HOL/native rules

All five native roots and both proof-decoder roots preserve arbitrary
formation-sensitive source judgments. The Pi/Sigma conversion obligations
are discharged by a separately proved conservative auxiliary development.
No auxiliary contraction is installed in the source system.

The result is finite subject reduction. It does not assert normalization,
confluence of authored raw execution, or a complete semantic model.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace FormationSensitiveHOLNativeMixedPreservation

open Presentation Presentation.FormationSensitive
open FormationSensitiveHOLNativeMixedSchemas (universes heads)
open HOLNativeMixedConversionParallel (mixedPiConversionBoundary mixedSigmaConversionBoundary)

abbrev jointRules := FormationSensitiveHOLProofListIntegration.rules

theorem rootPreservation : RootPreservation jointRules := by
  intro n context source target displayed formed observed root
  cases root with
  | inherited native =>
      cases native with
      | inherited impossible => exact impossible.elim
      | delta lookup =>
          rw [HOLNativeMixedConversionCompletion.native_opaque] at lookup
          cases lookup
      | declared evidence =>
          obtain ⟨evidence⟩ := evidence
          cases evidence with
          | list evidence =>
              cases evidence with
              | nil =>
                  exact FormationSensitiveHOLNativeMixedListPreservation.ListElimination.nil_preserves
                    formed observed
              | cons =>
                  exact FormationSensitiveHOLNativeMixedListPreservation.ListElimination.cons_preserves
                    formed observed
              | identity =>
                  exact FormationSensitiveHOLNativeMixedListPreservation.IdentityElimination.identity_preserves
                    formed observed
          | rel evidence =>
              exact FormationSensitiveHOLNativeMixedRelatorPreservation.iota_preserves
                formed evidence observed
  | delta lookup =>
      rw [FormationSensitiveHOLProofConversion.declarations_opaque] at lookup
      cases lookup
  | declared decoder =>
      exact FormationSensitiveHOLNativeMixedDecoderPreservation.decoder_preserves
        formed observed decoder

theorem step_preserves {n : Nat} {context : Tower.Ctx n} {source target displayed : Tower.Tm n}
    (judgment : Judgment jointRules context source displayed)
    (step : Step jointRules.headEq source target jointRules.computation) :
    Judgment jointRules context target displayed :=
  judgment.step_preserves universes mixedPiConversionBoundary mixedSigmaConversionBoundary
    heads rootPreservation step

theorem steps_preserve {n : Nat} {context : Tower.Ctx n} {source target displayed : Tower.Tm n}
    (judgment : Judgment jointRules context source displayed)
    (steps : ConversionCoherence.StepStar jointRules source target) :
    Judgment jointRules context target displayed :=
  judgment.steps_preserve universes mixedPiConversionBoundary mixedSigmaConversionBoundary
    heads rootPreservation steps

/-- The actual GSLT's entire finite derivation preserves the caller's
displayed type, not just its preselected normal-form endpoint. -/
theorem gslt_preserves {n : Nat} {context : Tower.Ctx n} {source target displayed : Tower.Tm n}
    (judgment : Judgment jointRules context source displayed)
    (steps : FormationSensitiveHOLProofListIntegration.Reduces source target) :
    Judgment jointRules context target displayed := by
  refine @Mettapedia.GSLT.GSLT.MultiStep.rec
    (FormationSensitiveHOLProofListIntegration.reduction n)
    (fun source target _ => Judgment jointRules context source displayed →
      Judgment jointRules context target displayed)
    (fun _ checked => checked)
    (fun {_ _ _} edge _ ih checked => ih (step_preserves checked edge))
    source target steps judgment

/-- Admission is transported to every observed finite endpoint of the
actual joint operational presentation. -/
theorem oslf_observation_admitted {n : Nat} {context : Tower.Ctx n}
    {source displayed : Tower.Tm n} {predicate : Tower.Tm n → Prop}
    (judgment : Judgment jointRules context source displayed)
    (observed : Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond
      (FormationSensitiveHOLProofListIntegration.reduction n).closure predicate source) :
    ∃ target, predicate target ∧ Judgment jointRules context target displayed := by
  obtain ⟨target, ⟨middle, path, equal⟩, accepted⟩ :=
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond_spec _ _ _).1 observed
  subst target
  exact ⟨middle, accepted, gslt_preserves judgment path⟩

/-- The existing nonempty native map and translated predicate consumer keep
one environment; every intermediate admitted map state can now be reused. -/
theorem consumer_map_endpoint :
    Judgment jointRules FormationSensitiveHOLProofListIntegration.Consumer.jointContext
      FormationSensitiveHOLProofListIntegration.Consumer.nativeInput
      (NativeIndexedFamilies.Intrinsic.listApp
        FormationSensitiveHOLProofListIntegration.Consumer.elementType) :=
  gslt_preserves
    ⟨FormationSensitiveHOLProofListIntegration.Consumer.joint_context_formed,
      FormationSensitiveHOLProofListIntegration.Consumer.program_typed⟩
    FormationSensitiveHOLProofListIntegration.Consumer.native_computation

#print axioms rootPreservation
#print axioms step_preserves
#print axioms steps_preserve
#print axioms gslt_preserves
#print axioms oslf_observation_admitted
#print axioms consumer_map_endpoint

end FormationSensitiveHOLNativeMixedPreservation
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
