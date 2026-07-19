import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.BeliefState
import Mettapedia.PLN.WorldModel.CertifiedMaskHook

/-!
# Belief slots as additive world-model state

A query-indexed binary-evidence store is both a belief workspace and an
`AdditiveWorldModel`: revision is pointwise evidence addition, and reading a
slot commutes with revision.  A worked residue slot then passes through the
existing proof-carrying world-model hook to a certified hard mask.

The numerical slot does not license pruning on its own.  Authority enters only
through the proved `CertifiedReadout.derive` field.  The zero-evidence fixture
marks the corresponding negative boundary.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric.AdditiveWorldModel
open Mettapedia.PLN.WorldModel.CertifiedMaskHook
open Mettapedia.GSLT.LanguageDef.RefinementInterface
open Mettapedia.GSLT.LanguageDef.CertifiedMask
open Mettapedia.GSLT.LanguageDef.GauthierCertifiedMask
open Mettapedia.GSLT.LanguageDef.GauthierRefinement
open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.OSLF.Framework.GauthierOEISPruningSoundness
open Mettapedia.OSLF.Framework.GauthierOEISModKPruning

/-! ## Generic additive belief-slot world -/

/-- One additive binary-evidence belief slot for each query. -/
abbrev BeliefSlotWorld (Query : Type*) := Query → BinaryEvidence

noncomputable instance beliefSlotWorldEvidenceType (Query : Type*) :
    EvidenceType (BeliefSlotWorld Query) where

/-- Reading a belief slot commutes definitionally with pointwise revision. -/
noncomputable instance beliefSlotAdditiveWorldModel (Query : Type*) :
    AdditiveWorldModel (BeliefSlotWorld Query) Query BinaryEvidence where
  extract := fun world query => world query
  extract_add := by
    intro first second query
    rfl

theorem beliefSlot_extract_add
    {Query : Type*} (first second : BeliefSlotWorld Query) (query : Query) :
    AdditiveWorldModel.extract
        (State := BeliefSlotWorld Query) (Query := Query) (Ev := BinaryEvidence)
        (first + second) query =
      AdditiveWorldModel.extract
          (State := BeliefSlotWorld Query) (Query := Query) (Ev := BinaryEvidence)
          first query +
        AdditiveWorldModel.extract
          (State := BeliefSlotWorld Query) (Query := Query) (Ev := BinaryEvidence)
          second query :=
  rfl

/-! ## Certified residue readout from a binary belief slot -/

/-- A belief packet supporting the distinguished residue query. -/
def positiveResidueBelief : BinaryEvidence where
  pos := 1
  neg := 0

/-- One query-indexed belief state with positive support only at `modThreeOne`. -/
noncomputable def oneResidueBeliefWorld : BeliefSlotWorld ResidueQuery := fun query =>
  if query = modThreeOne then positiveResidueBelief else 0

theorem oneResidueBeliefWorld_extract :
    AdditiveWorldModel.extract
      (State := BeliefSlotWorld ResidueQuery)
      (Query := ResidueQuery) (Ev := BinaryEvidence)
      oneResidueBeliefWorld modThreeOne = positiveResidueBelief := by
  rfl

/-- Positive support in the residue slot is interpreted by the sealed mod-3
program rejector. -/
def oneTargetBeliefReadout :
    CertifiedReadout ResidueQuery BinaryEvidence
      (fun program : Prog => Reproduces program oneTarget) where
  query := modThreeOne
  certifiedEvidence := fun evidence => 0 < evidence.pos
  derive := by
    intro _evidence _hpositive
    exact modKRejector 3 oneTarget

theorem oneTargetBeliefEvidence :
    oneTargetBeliefReadout.certifiedEvidence
      (AdditiveWorldModel.extract
        (State := BeliefSlotWorld ResidueQuery)
        (Query := ResidueQuery) (Ev := BinaryEvidence)
        oneResidueBeliefWorld oneTargetBeliefReadout.query) := by
  change 0 < (positiveResidueBelief.pos)
  norm_num [positiveResidueBelief]

noncomputable def oneTargetBeliefCertificate :
    CertifiedProgramRejector
      (fun program : Prog => Reproduces program oneTarget) :=
  certificateFromWorld oneTargetBeliefReadout oneResidueBeliefWorld
    oneTargetBeliefEvidence

/-- The binary belief slot recovers the sealed modular rejection criterion. -/
theorem oneTargetBeliefCertificate_rejects_iff {program : Prog} :
    oneTargetBeliefCertificate.rejects program ↔
      ModKIncompatible 3 program oneTarget :=
  Iff.rfl

def oneTargetBeliefStatePrune : SearchNode orgMemoRoot → Prop :=
  statePruneFromWorld oneTargetBeliefReadout oneResidueBeliefWorld
    oneTargetBeliefEvidence

/-- T5 crown: an additive belief slot reaches a certified state-space mask
through the generic world-model hook. -/
theorem oneTargetBeliefStatePrune_certified :
    CertifiedHardMask
      (fun program : Prog => Reproduces program oneTarget)
      oneTargetBeliefStatePrune := by
  simpa [oneTargetBeliefStatePrune] using
    (statePruneFromWorld_certified
      (root := orgMemoRoot)
      (property := fun program : Prog => Reproduces program oneTarget)
      oneTargetBeliefReadout oneResidueBeliefWorld oneTargetBeliefEvidence)

/-! ## Negative boundary -/

/-- An empty belief slot does not satisfy this readout's evidence premise. -/
theorem zeroResidueBelief_not_certified :
    ¬oneTargetBeliefReadout.certifiedEvidence
      (AdditiveWorldModel.extract
        (State := BeliefSlotWorld ResidueQuery)
        (Query := ResidueQuery) (Ev := BinaryEvidence)
        (0 : BeliefSlotWorld ResidueQuery) modThreeOne) := by
  change ¬(0 < (0 : BinaryEvidence).pos)
  simp

#print axioms beliefSlot_extract_add
#print axioms oneResidueBeliefWorld_extract
#print axioms oneTargetBeliefCertificate_rejects_iff
#print axioms oneTargetBeliefStatePrune_certified
#print axioms zeroResidueBelief_not_certified

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
