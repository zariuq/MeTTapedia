import Mettapedia.GSLT.LanguageDef.CertificateGSLTDisplayedDerivations
import Mettapedia.TypeTheory.CategoryIndexedFamilyTypeFormers
import Mettapedia.TypeTheory.CategoryIndexedFamilyGeneralPi

/-!
# Pointwise dependent-product variance at certificate substitutions

The existing category-indexed families CwF has a pointwise dependent product
when its domain family transports each route by an equivalence. The authored
certificate category has contractions: one target assumption can be used for
two source premise positions. Its proof family therefore has a transport map
that identifies distinct source derivations. The pointwise-product condition
does not hold for that family.

This is a limitation of that particular product construction, not a
nonexistence theorem for dependent products in a presheaf topos or for Prime.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.TypeTheory.CategoryIndexedFamilyCwf
open Mettapedia.TypeTheory.CategoryIndexedFamilyTypeFormers
open Mettapedia.TypeTheory.CategoryIndexedFamilyGeneralPi

variable (definition : ValidatedCalculusLanguageDef) (judgment : Pattern)

private def duplicatePremises : ClassifyingContext definition :=
  ⟨[judgment, judgment]⟩

private def singlePremise : ClassifyingContext definition :=
  ⟨[judgment]⟩

/-- A checked context substitution uses one assumption to fill both premise
positions of a duplicate-judgment context. -/
def contractionSubstitution :
    singlePremise definition judgment ⟶ duplicatePremises definition judgment :=
  .cons (.assumption (context := [judgment]) (0 : Fin 1))
    (.cons (.assumption (context := [judgment]) (0 : Fin 1)) .nil)

private abbrev goalIndexedProofFamily :
    IndexedFamily (Cat.of (goalFace definition).Elements) :=
  derivationFamily definition

/-- The two distinct source assumption occurrences become the same retained
proof after the actual authored contraction substitution. -/
theorem contraction_identifies_assumptions :
    (OpenDerivation.assumption (definition := definition)
      (context := [judgment, judgment]) (0 : Fin 2)).bind
        (contractionSubstitution definition judgment) =
    (OpenDerivation.assumption (definition := definition)
      (context := [judgment, judgment]) (1 : Fin 2)).bind
        (contractionSubstitution definition judgment) := by
  rfl

/-- The proof-relevant goal family has an actual noninjective contextual
action, so its routes cannot all act by fibrewise equivalences. -/
theorem derivationFamily_no_fibrewise_equivalence_action
    (judgment : Pattern) :
    ¬ Nonempty (FibrewiseEquivalenceAction
      (goalIndexedProofFamily definition)) := by
  rintro ⟨action⟩
  let substitution := contractionSubstitution definition judgment
  let route := goalSubstitution definition substitution judgment
  have distinct := ClassifyingContext.duplicate_assumptions_distinct
    definition judgment
  apply distinct
  apply (action.equivalence route).injective
  have collapse : (derivationFamily definition).map route
      (OpenDerivation.assumption (definition := definition)
        (context := [judgment, judgment]) (0 : Fin 2)) =
    (derivationFamily definition).map route
      (OpenDerivation.assumption (definition := definition)
        (context := [judgment, judgment]) (1 : Fin 2)) := by
    change
      (OpenDerivation.assumption (definition := definition)
        (context := [judgment, judgment]) (0 : Fin 2)).bind substitution =
      (OpenDerivation.assumption (definition := definition)
        (context := [judgment, judgment]) (1 : Fin 2)).bind substitution
    exact contraction_identifies_assumptions definition judgment
  calc
    action.equivalence route
        (OpenDerivation.assumption (definition := definition)
          (context := [judgment, judgment]) (0 : Fin 2)) =
      (derivationFamily definition).map route
        (OpenDerivation.assumption (definition := definition)
          (context := [judgment, judgment]) (0 : Fin 2)) :=
        action.apply_eq_map route _
    _ = (derivationFamily definition).map route
        (OpenDerivation.assumption (definition := definition)
          (context := [judgment, judgment]) (1 : Fin 2)) := collapse
    _ = action.equivalence route
        (OpenDerivation.assumption (definition := definition)
          (context := [judgment, judgment]) (1 : Fin 2)) :=
        (action.apply_eq_map route _).symm

/-- The same noninvertible authored proof family nevertheless admits the
general semantic dependent product along its comprehension projection. -/
noncomputable def derivationIdentityPi :
    IndexedFamily (Cat.of (goalFace definition).Elements) :=
  generalPiFamily (goalIndexedProofFamily definition)
    (reindexFamily (goalIndexedProofFamily definition)
      (weaken (goalIndexedProofFamily definition)))

/-- This dependent product has a proof-preserving identity inhabitant; no
inverse is supplied for the contraction of premise occurrences. -/
noncomputable def derivationIdentityPiTerm :
    unitFamily (Cat.of (goalFace definition).Elements) ⟶
      derivationIdentityPi definition :=
  identityPiTranspose (goalIndexedProofFamily definition)

/-- Evaluating the identity inhabitant returns the actual proof variable
uniformly over contextual substitutions, including contraction. -/
theorem derivationIdentityPi_beta :
    Functor.whiskerLeft (weaken (goalIndexedProofFamily definition))
        (derivationIdentityPiTerm definition) ≫
      generalPiEvaluation (goalIndexedProofFamily definition)
        (reindexFamily (goalIndexedProofFamily definition)
          (weaken (goalIndexedProofFamily definition))) =
      identityPiBody (goalIndexedProofFamily definition) :=
  identityPi_beta (goalIndexedProofFamily definition)

#print axioms contraction_identifies_assumptions
#print axioms derivationFamily_no_fibrewise_equivalence_action
#print axioms derivationIdentityPi
#print axioms derivationIdentityPiTerm
#print axioms derivationIdentityPi_beta

end Mettapedia.GSLT.LanguageDef.CertificateGSLT
