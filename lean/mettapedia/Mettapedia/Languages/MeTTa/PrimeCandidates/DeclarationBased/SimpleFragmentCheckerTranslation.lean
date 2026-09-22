import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.SubstitutionTranslation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FourFaceBetaExperiment
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.DeclarationAwareErasureNaturality

/-! # Typed simple beta cells at the authored first-order checker boundary -/
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

namespace Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.SubstitutionTranslation
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.TowerDTT
open DeclarationAwareSubstitutionCompiler DeclarationAwareSubstitutionLanguage
variable {sourceContext : List Ty} {domain codomain : Ty}
/-! ## Every simple beta cell reaches the first-order checker -/

/-- First-order erasure of every intrinsic newest-variable opening is the
independently defined raw substitution function. -/
@[simp]
theorem rawErase_instantiateNewest
    {targetType : Ty}
    (body : Term (selectedType :: sourceContext) targetType)
    (argument : Term sourceContext selectedType) :
    FourFaceBetaExperiment.DeepGSLT.rawErase
        (body.instantiateNewest argument) =
      substituteRaw 0
        (FourFaceBetaExperiment.DeepGSLT.rawErase argument)
        (FourFaceBetaExperiment.DeepGSLT.rawErase body) := by
  calc
    FourFaceBetaExperiment.DeepGSLT.rawErase
        (body.instantiateNewest argument) =
      DeclarationAwareSubstitutionSemantics.erase
        (eraseTerm (body.instantiateNewest argument)) :=
      FourFaceBetaExperiment.DeepGSLT.rawErase_eq_eraseTower _
    _ = DeclarationAwareSubstitutionSemantics.erase
        (Presentation.inst0 (eraseTerm argument) (eraseTerm body)) := by
      rw [eraseTerm_instantiateNewest]
    _ = DeclarationAwareSubstitutionSemantics.substituteAt 0
        (DeclarationAwareSubstitutionSemantics.erase (eraseTerm argument))
        (DeclarationAwareSubstitutionSemantics.erase (eraseTerm body)) :=
      DeclarationAwareErasureNaturality.erase_inst0
        (eraseTerm argument) (eraseTerm body)
    _ = substituteRaw 0
        (FourFaceBetaExperiment.DeepGSLT.rawErase argument)
        (FourFaceBetaExperiment.DeepGSLT.rawErase body) := by
      rw [FourFaceBetaExperiment.DeepGSLT.rawErase_eq_eraseTower,
        FourFaceBetaExperiment.DeepGSLT.rawErase_eq_eraseTower]
      rfl

/-- The first-order target associated with an arbitrary intrinsic beta cell. -/
def rawTarget (claim : BetaClaim sourceContext domain codomain) : Pattern :=
  encodeRaw (FourFaceBetaExperiment.DeepGSLT.rawErase claim.target)

/-- The declaration-aware root-beta query generated from an arbitrary
intrinsic beta cell. -/
def rawGoal (claim : BetaClaim sourceContext domain codomain) : Pattern :=
  rootBeta
    (tmApp
      (tmLam (encodeRaw
        (FourFaceBetaExperiment.DeepGSLT.rawErase claim.body)))
      (encodeRaw
        (FourFaceBetaExperiment.DeepGSLT.rawErase claim.argument)))
    (rawTarget claim)

/-- The generic proof-producing checker accepts every intrinsic simple beta
cell after first-order erasure. -/
theorem betaClaim_deep_checked
    (claim : BetaClaim sourceContext domain codomain) :
    checkRaw DeclarationAwareSubstitutionLanguage.definition
      (rawGoal claim)
      (betaRawProof
        (FourFaceBetaExperiment.DeepGSLT.rawErase claim.body)
        (FourFaceBetaExperiment.DeepGSLT.rawErase claim.argument)) = true := by
  simp only [rawGoal, rawTarget, BetaClaim.target]
  rw [rawErase_instantiateNewest]
  exact betaRawProof_accepts
    (FourFaceBetaExperiment.DeepGSLT.rawErase claim.body)
    (FourFaceBetaExperiment.DeepGSLT.rawErase claim.argument)

/-- No accepted first-order certificate for the erased source can name a
different target. -/
theorem betaClaim_deep_no_invention
    (claim : BetaClaim sourceContext domain codomain)
    {target : Pattern} {proof : RawProof}
    (accepted :
      checkRaw DeclarationAwareSubstitutionLanguage.definition
        (rootBeta
          (tmApp
            (tmLam (encodeRaw
              (FourFaceBetaExperiment.DeepGSLT.rawErase claim.body)))
            (encodeRaw
              (FourFaceBetaExperiment.DeepGSLT.rawErase claim.argument)))
          target)
        proof = true) :
    target = rawTarget claim := by
  have reflected :=
    DeclarationAwareSubstitutionReflection.checkRaw_beta_reflects
      (FourFaceBetaExperiment.DeepGSLT.rawErase claim.body)
      (FourFaceBetaExperiment.DeepGSLT.rawErase claim.argument) accepted
  calc
    target = encodeRaw
        (substituteRaw 0
          (FourFaceBetaExperiment.DeepGSLT.rawErase claim.argument)
          (FourFaceBetaExperiment.DeepGSLT.rawErase claim.body)) := reflected
    _ = rawTarget claim := by
      simp only [rawTarget, BetaClaim.target]
      rw [rawErase_instantiateNewest]


end Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.SubstitutionTranslation
