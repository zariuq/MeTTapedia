import Mettapedia.GSLT.Dynamics.ProofRelevantAnswerBag
import Mettapedia.Languages.MeTTa.Experimental.StagedReflective.Presentation

/-! # Staged typing evidence as proof-relevant answer fibres -/

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.RelationalEvidence

open Mettapedia.GSLT.ProofRelevantAnswerBag
open Mettapedia.TypeTheory.Calculi.StagedScopedReflective
open Mettapedia.Languages.MeTTa.Experimental.StagedReflective

/-! ## The native-typing instance of the relation layer -/

/-- Native typing is a relation from the unique query point to claims, with
authored derivation-plus-PLN evidence as its proof fibre. -/
def nativeTypingRel : ProofRel Unit NativeTypingClaim where
  evidence _ claim := NativeEvidenceDerivation claim

/-- The established native derivation bag is exactly a fibrewise bag for the
native typing relation. -/
abbrev NativeRelFibreBag :=
  (claim : NativeTypingClaim) →
    Multiset (nativeTypingRel.evidence () claim)

def nativeDerivationBagEquiv : NativeDerivationBag ≃ NativeRelFibreBag :=
  Equiv.refl _

/-- Truth erasure for the relation instance is the already-proved Galois
connection between unit truth bags and positive multiplicity support. -/
theorem nativeRel_truthSet_galois :
    GaloisConnection NativeDerivationCountBag.ofTruthSet
      NativeDerivationCountBag.truthSet :=
  NativeDerivationCountBag.truthSet_galois

/-- The relation interpretation does not make a PLN strength readout
recoverable from Boolean truth. -/
theorem nativeRel_strength_does_not_factor_through_truth :
    ¬ NativeDerivationBag.StrengthFactorsThroughTruthAt
      primitiveLetTypingClaim :=
  nativeEvidence_strength_does_not_factor_through_truth


#print axioms nativeRel_truthSet_galois
#print axioms nativeRel_strength_does_not_factor_through_truth

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.RelationalEvidence
