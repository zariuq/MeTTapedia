import Mettapedia.GSLT.LanguageDef.CertificateGSLTPiVarianceBoundary
import Mettapedia.TypeTheory.PresheafPiIndexedCwfBridge

/-!
# Dependent proof functions under the actual proof-to-goal observation

The general presheaf-context Π law is applied to the authored contextual
proof family. The substitution is the actual natural transformation that
forgets a checked derivation to its goal, and that map is not injective
on duplicate-assumption contexts. The dependent identity function still
transports coherently without identifying those derivations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.TypeTheory.CategoryOfElementsBaseChange
open Mettapedia.TypeTheory.CategoryIndexedFamilyCwf
open Mettapedia.TypeTheory.CategoryIndexedFamilyGeneralPi
open Mettapedia.TypeTheory.PresheafPiIndexedCwfBridge

variable (definition : ValidatedCalculusLanguageDef)

private def observedProofMap :
    derivationTotalFace definition ⟶ goalFace definition :=
  derivationToGoal definition

private def observedProofDomain :
    (goalFace definition).Elements ⥤ Type :=
  derivationFamily definition

private def observedProofCodomain :
    (observedProofDomain definition).Elements ⥤ Type :=
  reindexFamily (observedProofDomain definition)
    (weaken (context := Cat.of (goalFace definition).Elements)
      (observedProofDomain definition))

section
set_option backward.isDefEq.respectTransparency false

/-- The retained-derivation identity function commutes with the actual
proof-to-goal observation, even though that observation forgets which
authored proof was supplied. -/
theorem derivationIdentityPi_transpose_under_observation :
    generalPiTranspose
        (context := Cat.of (derivationTotalFace definition).Elements)
        ((observedProofMap definition).mapElements ⋙
          observedProofDomain definition)
        (Functor.whiskerLeft
          (mapPrecompElements
            (observedProofMap definition).mapElements
            (observedProofDomain definition))
          (identityPiBody (context := Cat.of (goalFace definition).Elements)
            (observedProofDomain definition))) ≫
      (presheafGeneralPi_formation_baseChangeIso
        (observedProofMap definition)
        (observedProofDomain definition)
        (observedProofCodomain definition)).hom =
      Functor.whiskerLeft (observedProofMap definition).mapElements
        (generalPiTranspose
          (context := Cat.of (goalFace definition).Elements)
          (observedProofDomain definition)
          (identityPiBody (context := Cat.of (goalFace definition).Elements)
            (observedProofDomain definition))) := by
  exact presheafGeneralPi_transpose_baseChange
    (source := derivationTotalFace definition)
    (target := goalFace definition)
    (head := unitFamily (Cat.of (goalFace definition).Elements))
    (observedProofMap definition)
    (observedProofDomain definition)
    (observedProofCodomain definition)
    (identityPiBody (context := Cat.of (goalFace definition).Elements)
      (observedProofDomain definition))

end

#check derivationToGoal_not_injective_on_duplicates
#print axioms derivationIdentityPi_transpose_under_observation

end Mettapedia.GSLT.LanguageDef.CertificateGSLT
