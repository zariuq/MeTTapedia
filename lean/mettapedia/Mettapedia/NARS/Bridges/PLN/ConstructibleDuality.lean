import Mettapedia.NARS.Bridges.PLN.EvidenceTranslation
import Mettapedia.NARS.Evidence.EvidenceScopeIncoherence
import Mettapedia.PLN.RuleFamilies.QuantaleSemantics.CDLogic

/-!
# NARS path relevance and PLN constructible-duality evidence

This bridge compares two distinct information dimensions:

* Pei Wang's NARS account retains the inference path and evidence scope of a
  belief;
* the constructible-duality evidence used by PLN retains independent positive
  and negative evidence channels.

For the concrete two-path witness in `EvidenceScopeIncoherence`, both paths
occupy the `both` quadrant, but their evidence values differ.  Thus the
constructible-duality quadrant is a useful local readout, while path identity
and evidence magnitude remain strictly finer information.

The constructible-duality operations are formalized from Ben Goertzel et al.,
*Paraconsistent Foundations for Probabilistic Reasoning, Programming and
Concept Learning* (2020).  The path/scope account is from Pei Wang,
*Formalization of Evidence: A Comparative Study* (2009), pp. 46--47.
-/

namespace Mettapedia.NARS.Bridges.PLN.ConstructibleDuality

open Mettapedia.NARS.TruthFunctions
open Mettapedia.NARS.Evidence.EvidenceScopeIncoherence
open Mettapedia.NARS.Evidence.EvidenceScopeIncoherence.PathWitness
open Mettapedia.PLN.Evidence.EvidenceQuantale

/-- Forget the retained path but keep the two constructive evidence channels
underlying a NARS truth value. -/
noncomputable def evidenceOf
    (belief : PathScopedBelief PathWitness.Statement (Fin 3)) : BinaryEvidence :=
  Mettapedia.NARS.Bridges.PLN.EvidenceTranslation.TV.toEvidence belief.truth

theorem direct_evidence_is_both :
    Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PBit.isBoth
      (evidenceOf directBelief) := by
  constructor <;>
    simp [evidenceOf, directBelief, directTruth,
      Mettapedia.NARS.Bridges.PLN.EvidenceTranslation.TV.toEvidence,
      c2w, ENNReal.ofReal_pos] <;> norm_num

theorem deductive_evidence_is_both :
    Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PBit.isBoth
      (evidenceOf deductiveBelief) := by
  constructor <;>
    simp [evidenceOf, deductiveBelief, deductiveTruth, premiseTruth,
      truthDeduction,
      Mettapedia.NARS.Bridges.PLN.EvidenceTranslation.TV.toEvidence,
      c2w, ENNReal.ofReal_pos] <;> norm_num

theorem direct_evidence_ne_deductive_evidence :
    evidenceOf directBelief ≠ evidenceOf deductiveBelief := by
  intro equality
  have positive := congrArg BinaryEvidence.pos equality
  norm_num [evidenceOf, directBelief, directTruth, deductiveBelief,
    deductiveTruth, premiseTruth, truthDeduction,
    Mettapedia.NARS.Bridges.PLN.EvidenceTranslation.TV.toEvidence,
    c2w] at positive

/-- Path relevance refines the local constructible-duality classification:
both paths contain positive and negative evidence, yet the retained evidence
objects remain distinct. -/
theorem path_relevance_refines_constructible_duality :
    Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PBit.isBoth
        (evidenceOf directBelief) ∧
      Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PBit.isBoth
        (evidenceOf deductiveBelief) ∧
      evidenceOf directBelief ≠ evidenceOf deductiveBelief :=
  ⟨direct_evidence_is_both, deductive_evidence_is_both,
    direct_evidence_ne_deductive_evidence⟩

#print axioms path_relevance_refines_constructible_duality

end Mettapedia.NARS.Bridges.PLN.ConstructibleDuality
