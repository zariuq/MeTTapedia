import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRawBoundary
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveSignaturePreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeRegularity
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorConversion
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorAnnotatedChecking

/-! Exact authorization-judgment controls for the selected Nat/Vec policy. -/

set_option autoImplicit false

namespace Mettapedia.Logic.NativeInferenceAuthorizationControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies

def missingDomain : DeclName := `NativeInferenceAuthorizationControls.missingDomain

theorem regularity (enabled : Programs.ComputationProfiles.Selection) :
    FormationSensitive.UniverseRegularity (Programs.ComputationProfiles.rules enabled) :=
  FormationSensitive.towerUniverseRegularity.includeSignature
    (Programs.ComputationProfiles.signature enabled)

theorem missing_lookup (enabled : Programs.ComputationProfiles.Selection) :
    (Programs.ComputationProfiles.rules enabled).constantType missingDomain = none := by
  change (Programs.ComputationProfiles.rules (fun _ => false)).constantType missingDomain = none
  decide +kernel

theorem actual_policy_boundary (enabled : Programs.ComputationProfiles.Selection) :
    HasType (Programs.ComputationProfiles.rules enabled) .nil (.lam (.var 0))
      (.pi (.const missingDomain) (.const missingDomain)) ∧
    ¬ FormationSensitive.Judgment (Programs.ComputationProfiles.rules enabled) .nil
      (.lam (.var 0)) (.pi (.const missingDomain) (.const missingDomain)) :=
  FormationSensitive.raw_identity_missing_domain (regularity enabled) (missing_lookup enabled)

theorem actual_policy_no_uniform_upgrade (enabled : Programs.ComputationProfiles.Selection) :
    ¬ (∀ {n : Nat} {context : Tower.Ctx n} {term type : Tower.Tm n},
      FormationSensitive.ContextFormation (Programs.ComputationProfiles.rules enabled) context →
      HasType (Programs.ComputationProfiles.rules enabled) context term type →
      FormationSensitive.Judgment (Programs.ComputationProfiles.rules enabled) context term type) :=
  FormationSensitive.no_uniform_raw_upgrade (regularity enabled) (missing_lookup enabled)

/-- The original checked program already has the stronger positive judgment. -/
theorem actual_append_raw_view :
    HasType (Programs.ComputationProfiles.rules Programs.ComputationProfiles.naturalOnly)
      .nil Programs.appendTerm Programs.appendType :=
  Programs.ComputationProfiles.append_typed_naturalOnly.toRaw

#check Declaration.Signature.DeclaredPreserves
#check Declaration.IndexedFamily.Authorized
#check FormationSensitive.RootPreservation
#check Programs.ComputationProfiles.NaturalConversion.Preservation.operational_roots
#check Programs.Annotated.root_preserving_of_formerFacts
#print axioms actual_policy_boundary
#print axioms actual_policy_no_uniform_upgrade
#print axioms actual_append_raw_view

end Mettapedia.Logic.NativeInferenceAuthorizationControls
