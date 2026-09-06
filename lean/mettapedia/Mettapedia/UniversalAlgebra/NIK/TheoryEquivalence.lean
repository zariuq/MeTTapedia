import Mettapedia.GSLT.LanguageDef.NIKTheoryTranslationExt
import Mettapedia.UniversalAlgebra.Instances.MonoidConservativeExtension
import Mettapedia.UniversalAlgebra.NIK.Simulation

/-!
# Equational consequence as semantic NIK theory equivalence

Two occurrence-bearing equation systems may be different source data while
generating the same mathematical theory.  Equality of generated consequence
induces an isomorphism of their semantic NIK theory objects.  Conversely, an
identity-on-equations conservative translation exists only when generated
consequence agrees.

This result concerns semantic theory objects.  It does not identify native
certificate types or supply an exact certificate compiler; those belong to
the stronger category of authority objects.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra.NIK

open CategoryTheory
open Mettapedia.GSLT.LanguageDef.CertifiedTheoryCategory
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory

universe u

variable {S : Signature.{u}} [DecidableEq S.Operation]

/-- Consequence-equivalent systems are isomorphic as semantic NIK theories.
The isomorphism is the identity on equation syntax. -/
def theoryIsoOfSameConsequences
    {left right : EquationSystem S}
    (equivalent : EquationSystem.SameConsequences left right) :
    theoryObject left ≅ theoryObject right where
  hom := identityOnEquationsTranslation equivalent
  inv := identityOnEquationsTranslation equivalent.symm
  hom_inv_id := by
    apply TheoryTranslation.ext_data
    · intro kind
      rfl
    · intro signature
      rfl
    · intro kind equation
      rfl
  inv_hom_id := by
    apply TheoryTranslation.ext_data
    · intro kind
      rfl
    · intro signature
      rfl
    · intro kind equation
      rfl

/-- A conservative semantic route that leaves equation syntax fixed exists
exactly when the two systems have the same generated consequences. -/
theorem sameConsequences_iff_exists_identity_conservative_translation
    {left right : EquationSystem S} :
    EquationSystem.SameConsequences left right ↔
      ∃ translation : TheoryTranslation (theory left) (theory right),
        (∀ equation, translation.mapClaim () equation = equation) ∧
          translation.Conservative := by
  constructor
  · intro equivalent
    exact ⟨identityOnEquationsTranslation equivalent,
      fun _equation => rfl,
      identityOnEquationsTranslation_conservative equivalent⟩
  · rintro ⟨translation, claimFixed, conservative⟩ equation
    constructor
    · intro leftConsequence
      have mapped := translation.scope_preserved () equation leftConsequence
      change EquationalConsequence right
        (translation.mapClaim () equation) at mapped
      simpa only [claimFixed equation] using mapped
    · intro rightConsequence
      apply conservative.scope_reflecting () equation
      change EquationalConsequence right (translation.mapClaim () equation)
      simpa only [claimFixed equation] using rightConsequence

namespace Monoid

open Mettapedia.UniversalAlgebra.Monoid

/-- Positive control: adjoining a derived monoid equation changes the source
list but not the semantic NIK theory object. -/
def derivedExtensionTheoryIso :
    theoryObject derivedExtension ≅ theoryObject equationSystem :=
  theoryIsoOfSameConsequences derivedExtension_sameConsequences

/-- The positive control is non-vacuous: the redundant extension is genuinely
different occurrence-bearing source data. -/
theorem derivedExtension_ne_equationSystem :
    derivedExtension ≠ equationSystem := by
  intro systemsEqual
  have lengthsEqual := congrArg (fun system => system.equations.length)
    systemsEqual
  simp [derivedExtension, EquationSystem.extend, equationSystem] at lengthsEqual

/-- Negative control: a genuinely new equation cannot have a conservative
identity-on-equations route back to the monoid theory. -/
theorem no_identity_conservative_translation_from_collapsingExtension :
    ¬ ∃ translation :
        TheoryTranslation (theory collapsingExtension) (theory equationSystem),
      (∀ equation, translation.mapClaim () equation = equation) ∧
        translation.Conservative := by
  rw [← sameConsequences_iff_exists_identity_conservative_translation]
  exact collapsingExtension_not_sameConsequences

end Monoid

end Mettapedia.UniversalAlgebra.NIK
