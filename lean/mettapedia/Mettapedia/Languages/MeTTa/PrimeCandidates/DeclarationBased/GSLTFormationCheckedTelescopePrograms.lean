import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CheckedTelescopeInstantiation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeJoins

/-! # GSLT certificate adapter for formed telescope programs -/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationCheckedTelescopePrograms
open FormationSensitive
variable {n m : Nat}

/-- The checker fragment preserves refined derivations directly; this is
not an attempted inverse to erasure of arbitrary native typing. -/
theorem structural_regular
    {context : Tower.Ctx n} {body type : Tower.Tm n}
    (proof : DeclarationAwareStructuralTyping.StructuralTyping context body type) :
    Typing Tower.rules context body type := by
  induction proof with
  | legacyGround _ => exact .headType .legacyGround
  | sort _ level => exact .headType (.sort level)
  | reflIntro _ ih => exact .reflIntro ih
  | @piForm n context domain body domainLevel bodyLevel _ _ domainIH bodyIH =>
      exact .piForm domainIH (.sort domainLevel) bodyIH (.sort bodyLevel)
        (.sorts domainLevel bodyLevel)

theorem checkArgument_regular (target : Tower.Ctx m)
    (argument domain : Tower.Tm m) (proof : Mettapedia.GSLT.LanguageDef.InferenceChecker.RawProof)
    (accepted : CheckedTelescopeInstantiation.checkArgument target argument domain proof = true) :
    Typing Tower.rules target argument domain := by
  obtain ⟨evidence⟩ := CheckedTelescopeInstantiation.checkArgument_reflects accepted
  exact structural_regular evidence

#print axioms structural_regular
#print axioms checkArgument_regular

end FormationCheckedTelescopePrograms
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
