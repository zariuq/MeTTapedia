import Mettapedia.GSLT.LanguageDef.CertificateGSLTLedgerDependentFamily
import Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge

/-!
# Exact certificate contexts as indexed-family comprehension

The category of actual proof-bearing answers is equivalent to the category
of elements of the proof-relevant family displayed over exact goal-and-ledger
answers. This composes the existing total-presheaf recovery of authored
proofs with the generic comparison between total-presheaf elements and
indexed-family comprehension. Arrows retain contextual proof substitution.

The result is semantic comprehension of an existing checked calculus. It is
not a new authored Prime dependent former or a completed classifying
lambda-theory.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open CategoryTheory
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge
open Mettapedia.TypeTheory.CategoryIndexedFamilyCwf

/-- The exact goal-and-ledger category is a context of the existing
category-indexed families CwF. -/
abbrev exactGoalLedgerIndexedContext
    (definition : ValidatedCalculusLanguageDef) : Context.{0} :=
  Cat.of (goalLedgerFace definition).Elements

/-- The exact proof fibre is a type of the existing indexed families CwF
over that concrete context. -/
abbrev exactProofIndexedType
    (definition : ValidatedCalculusLanguageDef) :
    IndexedFamily (exactGoalLedgerIndexedContext definition) :=
  exactDerivationDisplayedFamily definition

/-- The actual open-derivation category is equivalent to indexed-family
comprehension of the exact goal-and-ledger proof family. This equivalence
acts on contextual substitutions, not only on closed proof objects. -/
noncomputable def exactProofIndexedComprehensionEquiv
    (definition : ValidatedCalculusLanguageDef) :
    (derivationTotalFace definition).Elements ≌
      (exactDerivationDisplayedFamily definition).Elements :=
  (elementCategoryEquivalence
    (exactDerivationTotalIso definition)).symm.trans
      (totalElementsEquivalence (exactDerivationDisplayedFamily definition))

/-- Actual authored derivation contexts present the indexed CwF's own
comprehension extension of the exact proof family. -/
noncomputable def exactProofCwfComprehensionEquiv
    (definition : ValidatedCalculusLanguageDef) :
    (derivationTotalFace definition).Elements ≌
      (extend (exactGoalLedgerIndexedContext definition)
        (exactProofIndexedType definition) : Type) :=
  exactProofIndexedComprehensionEquiv definition

/-- The exact indexed-comprehension presentation keeps the existing
goal-and-ledger observation as its base projection. -/
theorem exactProofIndexedComprehension_over_base
    (definition : ValidatedCalculusLanguageDef) :
    (exactProofIndexedComprehensionEquiv definition).functor ⋙
        CategoryOfElements.π (exactDerivationDisplayedFamily definition) =
      (derivationToGoalLedger definition).mapElements := by
  let family := exactDerivationDisplayedFamily definition
  let totalIso := exactDerivationTotalIso definition
  have recovery : totalIso.inv ≫ totalProjection family =
      derivationToGoalLedger definition := by
    calc
      totalIso.inv ≫ totalProjection family =
          totalIso.inv ≫
            (totalIso.hom ≫ derivationToGoalLedger definition) := by
              rw [exactDerivationTotalIso_projection definition]
      _ = derivationToGoalLedger definition := by simp
  calc
    (exactProofIndexedComprehensionEquiv definition).functor ⋙
        CategoryOfElements.π family =
      (elementCategoryEquivalence totalIso).symm.functor ⋙
        (totalElementsToDisplayed family ⋙ CategoryOfElements.π family) := by
          rfl
    _ = (elementCategoryEquivalence totalIso).symm.functor ⋙
          (totalProjection family).mapElements := by
            rw [totalElementsEquivalence_over_base family]
    _ = (totalIso.inv ≫ totalProjection family).mapElements := by
          rfl
    _ = (derivationToGoalLedger definition).mapElements := by rw [recovery]

/-- Under the existing CwF's weakening map, the actual derivation context
projects to precisely the already-verified goal-and-ledger observation. -/
theorem exactProofCwfComprehension_weaken
    (definition : ValidatedCalculusLanguageDef) :
    (exactProofCwfComprehensionEquiv definition).functor ⋙
        weaken (exactProofIndexedType definition) =
      (derivationToGoalLedger definition).mapElements :=
  exactProofIndexedComprehension_over_base definition

/-- The actual authored derivation at each proof-bearing context is a
dependent semantic term of the exact goal-and-ledger proof family. It uses
the retained certificate directly, without searching for another one. -/
def exactProofSemanticVariable
    (definition : ValidatedCalculusLanguageDef) :
    IndexedSection (reindexFamily
      (source := Cat.of (derivationTotalFace definition).Elements)
      (exactProofIndexedType definition)
      (derivationToGoalLedger definition).mapElements) :=
  ⟨fun point => ⟨point.2, rfl⟩, by
    intro first second arrow
    apply Subtype.ext
    exact arrow.property⟩

/-- Reading that semantic variable gives the original checked derivation,
not an arbitrary proof of the same goal and ledger. -/
theorem exactProofSemanticVariable_retains
    (definition : ValidatedCalculusLanguageDef)
    (point : (derivationTotalFace definition).Elements) :
    ((exactProofSemanticVariable definition).1 point).val = point.2 := by
  rfl

#print axioms exactProofIndexedComprehensionEquiv
#print axioms exactProofCwfComprehensionEquiv
#print axioms exactProofIndexedComprehension_over_base
#print axioms exactProofCwfComprehension_weaken
#print axioms exactProofSemanticVariable_retains

end Mettapedia.GSLT.LanguageDef.CertificateGSLT
