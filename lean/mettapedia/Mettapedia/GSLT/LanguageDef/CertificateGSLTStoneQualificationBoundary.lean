import Mettapedia.GSLT.LanguageDef.CertificateGSLTDerivabilityQualification
import Mettapedia.GSLT.LanguageDef.CertificateGSLTStoneUltraBasisBridge

/-!
# Semantic qualification at ordinary and free Stone bases

The Stone-gunk CertificateGSLT admits two independent semantic selections over
one unchanged native checker.

* Ordinary Cantor-clopen meaning is exactly matched by the three authored proof
  paths.  Its derivability-to-semantics qualification is conservative.
* The free-ultrafilter selection additionally recognizes a cofinite
  perspective claim which has no native derivation.  Its qualification remains
  sound and natural, but is not conservative.

This is a concrete boundary between semantic extension and proof-system
extension.  Changing semantic perspective does not invent certificates, and
sharing an operational checker does not force selected meanings to coincide.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLTStoneQualificationBoundary

open Mettapedia.GSLT.LanguageDef.NIKDerivabilitySemanticQualification
open Mettapedia.GSLT.LanguageDef.CertificateGSLTDerivabilityQualification
open Mettapedia.GSLT.LanguageDef.CertificateGSLTStoneGunkSemanticAuthority
open Mettapedia.GSLT.LanguageDef.CertificateGSLTStoneUltraBasisBridge

/-! ## Ordinary selected semantics -/

/-- The ordinary selected Stone semantics contains exactly the three claims
with native proof paths, so semantic qualification reflects meaning as well as
preserving it. -/
theorem ordinary_qualification_is_conservative :
    (qualification
      (Mettapedia.GSLT.LanguageDef.CertificateGSLTAuthorityFunctor.contract
        presentation.toSoundPresentation)).toTheoryTranslation.Conservative := by
  apply (generationQualification_conservative_iff
    presentation.toSoundPresentation).mpr
  intro claim meaningful
  exact (meaning_iff_generated_scope claim).mp meaningful

/-- The semantically false atomic claim is absent from both ordinary meaning
and native proof scope. -/
theorem ordinary_atomic_is_neither_meaning_nor_scope :
    ¬ Meaning atomicClaim ∧
      ¬ (Mettapedia.GSLT.LanguageDef.CertificateGSLTHeterogeneousAuthority.theory
        presentation).Scope () atomicClaim :=
  ⟨atomic_lacks_independent_meaning,
    atomic_outside_generated_scope⟩

/-! ## Free-ultrafilter semantic extension -/

/-- The free selected basis is a genuine semantic extension: the cofinite
claim is meaningful but remains outside the unchanged native proof fibre. -/
theorem free_cofinite_semantic_gap :
    freePresentation.Meaning cofinitePerspectiveClaim ∧
      ¬ (Mettapedia.GSLT.LanguageDef.CertificateGSLTHeterogeneousAuthority.theory
        freePresentation).Scope () cofinitePerspectiveClaim :=
  cofinitePerspective_meaning_but_not_scope

/-- Consequently, the natural qualification component for the free selected
presentation is not conservative.  This does not refute its soundness. -/
theorem free_qualification_is_not_conservative :
    ¬ ((generationSemanticQualification freePresentation.Meaning).app
      freePresentation.toSoundPresentation).toTheoryTranslation.Conservative := by
  exact generationQualification_not_conservative_of_semantic_gap
    freePresentation.toSoundPresentation
    cofinitePerspectiveClaim
    cofinitePerspective_free_meaning
    cofinitePerspective_meaning_but_not_scope.2

/-- Ordinary and free semantics can disagree in conservativity while replaying
the very same retained perfect-Stone certificate. -/
theorem checker_invariance_does_not_imply_semantic_conservativity :
    ((Mettapedia.GSLT.LanguageDef.CertificateGSLTHeterogeneousAuthority.contract
        presentation).checker ()).check
          perfectStoneClaim perfectStoneCertificate =
      ((Mettapedia.GSLT.LanguageDef.CertificateGSLTHeterogeneousAuthority.contract
        freePresentation).checker ()).check
          perfectStoneClaim perfectStoneCertificate ∧
      ¬ ((generationSemanticQualification freePresentation.Meaning).app
        freePresentation.toSoundPresentation).toTheoryTranslation.Conservative :=
  ⟨perfectStone_checker_basis_invariant,
    free_qualification_is_not_conservative⟩

#print axioms ordinary_qualification_is_conservative
#print axioms ordinary_atomic_is_neither_meaning_nor_scope
#print axioms free_cofinite_semantic_gap
#print axioms free_qualification_is_not_conservative
#print axioms checker_invariance_does_not_imply_semantic_conservativity

end Mettapedia.GSLT.LanguageDef.CertificateGSLTStoneQualificationBoundary
