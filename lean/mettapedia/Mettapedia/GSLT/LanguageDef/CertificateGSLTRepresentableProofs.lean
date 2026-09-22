import Mettapedia.GSLT.LanguageDef.CertificateGSLTDisplayedDerivations
import Mettapedia.GSLT.Topos.Yoneda

/-!
# Certificate proofs as representable presheaf elements

For one fixed judgment, an open proof in a context is exactly a map from that
context to the one-judgment context. The Yoneda presheaf at the one-judgment
context therefore retains every proof and its substitution action. This is
a semantics-preserving embedding of the existing certificate syntax into
presheaves, not an identification of Prime's judgmental equality with the
extensional internal language of the presheaf topos.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax

private def goalContext (definition : ValidatedCalculusLanguageDef)
    (goal : Pattern) : ClassifyingContext definition := ⟨[goal]⟩

/-- The represented proof at one stage is exactly a one-element derivation
vector: neither the proof nor its rule/assumption occurrences are quotiented. -/
def openProofYonedaEquiv
    (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition)
    (goal : Pattern) :
    OpenDerivation definition context.judgments goal ≃
      ((yoneda (C := ClassifyingContext definition)).obj
        (goalContext definition goal)).obj (Opposite.op context) where
  toFun proof := .cons proof .nil
  invFun
    | .cons proof .nil => proof
  left_inv proof := rfl
  right_inv := by
    intro proofVector
    cases proofVector with
    | cons proof rest =>
        cases rest
        rfl

/-- Yoneda reindexing of a represented proof is exactly the calculus's
proof substitution, preserving its intensional constructor tree. -/
theorem openProofYonedaEquiv_reindex
    (definition : ValidatedCalculusLanguageDef)
    {source target : ClassifyingContext definition}
    (substitution : target ⟶ source)
    (goal : Pattern)
    (proof : OpenDerivation definition source.judgments goal) :
    openProofYonedaEquiv definition target goal
        (proof.bind substitution) =
      ((yoneda (C := ClassifyingContext definition)).obj
        (goalContext definition goal)).map (Quiver.Hom.op substitution)
          (openProofYonedaEquiv definition source goal proof) := by
  rfl

end Mettapedia.GSLT.LanguageDef.CertificateGSLT

#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.openProofYonedaEquiv
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.openProofYonedaEquiv_reindex
