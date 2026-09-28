import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueSound
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectPreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Coherence

/-!
# Coherence of annotations for the object package

For every annotation of the object package, that is, annotated declared types
and annotated root steps erasing to the package's, coherence of annotations
needs only injectivity and no-confusion of the annotated type formers
(`object_coherence`):

* normalization of the annotated calculus is the package's strong
  normalization (`objectRules_sn`), through the erasure of derivations;
* the universe laws are the package's level model and cumulativity algebra.

Constructing the annotation of the object package, and proving the injectivity
of its type formers, are not done here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Presentation.TypedEquality.Annotated

namespace CodeModel

/-- The facts coherence needs, for an annotation of the object package, from the
injectivity of its type formers alone. -/
theorem object_coherenceFacts (P : ChurchRules objectRules) (formers : CFormerFacts P) :
    CoherenceFacts P :=
  CoherenceFacts.ofSN formers fun formed typing => (objectRules_sn formed typing).1

/-- **Coherence of annotations for the object package**, from the injectivity
and no-confusion of the annotated type formers. -/
theorem object_coherence (P : ChurchRules objectRules) (formers : CFormerFacts P) {n : Nat}
    {Γ : CCtx Tower.Head n} (formed : CCtxFormed P Γ) {t t' A : CTm Tower.Head n}
    (typing : CTyped P Γ t A) (typing' : CTyped P Γ t' A) (same : t.erase = t'.erase) :
    CEqual P Γ t t' A :=
  coherence (object_coherenceFacts P formers) ConvRules.objectLevels
    ConvRules.objectRules_algebra formed typing typing' same

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
