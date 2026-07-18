import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.Erasure
import Mettapedia.GSLT.Meredith.InteractiveGSLT

/-!
# Cost erasure into the pure rho continued carrier

The continued rho presentation exposes only the proved `hashSet`-free carrier
to its computable quotient section.  A cost term enters that carrier after an
explicit signature-name encoding has been shown to stay pure.  Canonical
representatives are then computed by the same rho canonicalizer used by the
continued presentation.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed

open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureCanonicalSection
open Mettapedia.GSLT.Meredith.RhoExample

universe u

namespace CostTerm

/-- Erase a cost term directly into the pure rho section carrier. -/
def erasePure {Ground : Type u}
    (signatureName : SignatureNameEncoding Ground)
    (signaturePure : ∀ signature, HashSetFree (signatureName signature))
    (term : CostTerm Ground) : PurePattern :=
  ⟨term.erase signatureName, term.hashSetFree_erase signaturePure⟩

@[simp]
theorem erasePure_value {Ground : Type u}
    (signatureName : SignatureNameEncoding Ground)
    (signaturePure : ∀ signature, HashSetFree (signatureName signature))
    (term : CostTerm Ground) :
    (term.erasePure signatureName signaturePure).1 = term.erase signatureName :=
  rfl

/-- Compute the representative selected by the continued rho presentation for
an erased cost term. -/
def sectionRepresentative {Ground : Type u}
    (signatureName : SignatureNameEncoding Ground)
    (signaturePure : ∀ signature, HashSetFree (signatureName signature))
    (term : CostTerm Ground) :
    rhoContinuedCutPresentation.SectionCarrier :=
  rhoContinuedCutPresentation.reprSection
    (Quotient.mk pureEquations (term.erasePure signatureName signaturePure))

/-- The continued presentation computes exactly the established rho
canonicalizer on erased cost syntax. -/
@[simp]
theorem sectionRepresentative_value {Ground : Type u}
    (signatureName : SignatureNameEncoding Ground)
    (signaturePure : ∀ signature, HashSetFree (signatureName signature))
    (term : CostTerm Ground) :
    (term.sectionRepresentative signatureName signaturePure).1 =
      Canonical.canonicalize (term.erase signatureName) :=
  rfl

/-- Embedding the computed section representative back into ambient syntax is
the canonicalized cost erasure. -/
@[simp]
theorem sectionEmbedding_sectionRepresentative {Ground : Type u}
    (signatureName : SignatureNameEncoding Ground)
    (signaturePure : ∀ signature, HashSetFree (signatureName signature))
    (term : CostTerm Ground) :
    rhoContinuedCutPresentation.sectionEmbedding
        (term.sectionRepresentative signatureName signaturePure) =
      Canonical.canonicalize (term.erase signatureName) :=
  rfl

/-- The computed section representative remains structurally congruent to the
uncanonicalized cost erasure. -/
theorem erase_structurallyCongruent_sectionRepresentative {Ground : Type u}
    (signatureName : SignatureNameEncoding Ground)
    (signaturePure : ∀ signature, HashSetFree (signatureName signature))
    (term : CostTerm Ground) :
    StructuralCongruence
      (term.erase signatureName)
      (rhoContinuedCutPresentation.sectionEmbedding
        (term.sectionRepresentative signatureName signaturePure)) := by
  simpa using Canonical.canonicalize_sound (term.erase signatureName)

end CostTerm

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed
