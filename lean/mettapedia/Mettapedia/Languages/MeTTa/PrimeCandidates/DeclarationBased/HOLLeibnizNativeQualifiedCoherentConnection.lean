import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLLeibnizNativeQualifiedFragmentTheorem
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeHOLProofQualifiedSemanticQuotient

/-!
# One proof-qualified mathematical and operational connection

This module joins the two representation-independent boundaries used by the
current experiment.  The mathematical boundary carries the recursive HOL
proof into formation-sensitive dependent typing, Aczel-trace semantics, a
dependent consumer, and the explicit HOTG universe tower.  The operational
boundary sends proof-qualified execution to equation classes naturally and
then exposes the observation through the canonical OSLF generated from that
GSLT.

The result is a connected construction, not a choice of a definitive Prime
language.  Its negative fields remain part of the package: wrong-target proof
rejection is not refutation, evidence for a different theorem cannot qualify
the optimization, the source erasure is not reflective, finite closure does
not supply the needed list universe, and a same-level code for the full set
carrier is impossible.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace HOLLeibnizNativeQualifiedCoherentConnection

open Mettapedia.Logic
open Mettapedia.Logic.HOL.Embedding
open Mettapedia.Logic.HOL.UniformListInduction
open ZFSetUniverseLift

universe u

/-- The smallest theorem bundle needed to pass from the qualified
mathematical fragment through the semantic quotient to the generated OSLF
observation used by the concrete HOTG map-fusion workload. -/
structure CoherentConnection : Prop where
  mathematical :
    HOLLeibnizNativeQualifiedFragmentTheorem.QualifiedConnectedPackage.{u}

  semanticQuotient :
    NativeHOLProofQualifiedSemanticQuotient.SemanticQuotientLaws.{u}

  generatedOSLF :
    ∀ (level : LevelExpr Nat)
      (lower : ZFSetUniverseClosure.CofinalInaccessibles.{u})
      (x : ZFSetUniformListTraceTypeInterpretation.Value
        carrierCode.{u} element),
      NativeHOLProofQualifiedSemanticQuotient.HOTGMapFusion.GeneratedOSLFClaim
        level lower x

/-- The retained HOL induction proof supplies a nontrivial inhabitant of the
connected boundary.  The native programs on its two branches take different
routes, but their equation-invariant HOTG observation is accepted by the
OSLF generated from the semantic native-list GSLT. -/
theorem current : CoherentConnection.{u} where
  mathematical :=
    HOLLeibnizNativeQualifiedFragmentTheorem.connectedPackage
  semanticQuotient :=
    NativeHOLProofQualifiedSemanticQuotient.semanticQuotientLaws
  generatedOSLF :=
    NativeHOLProofQualifiedSemanticQuotient.HOTGMapFusion.generated_oslf_projection

#print axioms current

end HOLLeibnizNativeQualifiedCoherentConnection
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
