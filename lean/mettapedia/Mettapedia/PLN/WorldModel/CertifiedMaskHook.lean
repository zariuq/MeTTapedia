/-
# World-model extraction to certified hard masks

Extraction never licenses pruning by itself.  A `CertifiedReadout` must turn a
proved proposition about the extracted evidence into an ordinary
`CertifiedProgramRejector`; only then does the generic program-to-state lift
make a hard mask available.
-/

import Mettapedia.PLN.WorldModel.GenericWorldModel
import Mettapedia.GSLT.LanguageDef.Gauthier.CertifiedMask

namespace Mettapedia.PLN.WorldModel.CertifiedMaskHook

open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric.AdditiveWorldModel
open Mettapedia.GSLT.LanguageDef.RefinementInterface
open Mettapedia.GSLT.LanguageDef.CertifiedMask
open Mettapedia.GSLT.LanguageDef.GauthierCertifiedMask
open Mettapedia.GSLT.LanguageDef.GauthierRefinement
open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.OSLF.Framework.GauthierOEISPruningSoundness
open Mettapedia.OSLF.Framework.GauthierOEISModKPruning

universe uQuery uEvidence uProgram

/--
Proof-carrying interpretation of one world-model query.  The `derive` field is
the explicit trust boundary: numerical evidence has no pruning authority
unless this implication is proved.
-/
structure CertifiedReadout (Query : Type uQuery) (Evidence : Type uEvidence)
    {Program : Type uProgram} (property : Program → Prop) where
  query : Query
  certifiedEvidence : Evidence → Prop
  derive : ∀ evidence, certifiedEvidence evidence →
    CertifiedProgramRejector property

/-- Extract one proved program certificate from a world-model state. -/
def certificateFromWorld
    {State Query Evidence Program : Type*}
    [EvidenceType State] [AddCommMonoid Evidence]
    [AdditiveWorldModel State Query Evidence]
    {property : Program → Prop}
    (readout : CertifiedReadout Query Evidence property)
    (world : State)
    (hcertified : readout.certifiedEvidence
      (AdditiveWorldModel.extract (State := State) (Query := Query)
        (Ev := Evidence) world readout.query)) :
    CertifiedProgramRejector property :=
  readout.derive _ hcertified

/-- State predicate licensed by one proof-carrying extracted certificate. -/
def statePruneFromWorld
    {State Query Evidence : Type*}
    [EvidenceType State] [AddCommMonoid Evidence]
    [AdditiveWorldModel State Query Evidence]
    {root : RefinementInterface}
    {property : root.Program → Prop}
    (readout : CertifiedReadout Query Evidence property)
    (world : State)
    (hcertified : readout.certifiedEvidence
      (AdditiveWorldModel.extract (State := State) (Query := Query)
        (Ev := Evidence) world readout.query))
    (node : SearchNode root) : Prop :=
  liftProgramRejector (certificateFromWorld readout world hcertified) node

/-- T5 crown: a proved WM readout licenses the same generic state mask, no more. -/
theorem statePruneFromWorld_certified
    {State Query Evidence : Type*}
    [EvidenceType State] [AddCommMonoid Evidence]
    [AdditiveWorldModel State Query Evidence]
    {root : RefinementInterface}
    {property : root.Program → Prop}
    (readout : CertifiedReadout Query Evidence property)
    (world : State)
    (hcertified : readout.certifiedEvidence
      (AdditiveWorldModel.extract (State := State) (Query := Query)
        (Ev := Evidence) world readout.query)) :
    CertifiedHardMask property
      (statePruneFromWorld readout world hcertified) := by
  intro node hlifted
  change liftProgramRejector
    (certificateFromWorld readout world hcertified) node at hlifted
  exact liftProgramRejector_semanticallyPrunable
    (certificateFromWorld readout world hcertified) hlifted

/-! ## Worked residue extraction -/

structure ResidueQuery where
  modulus : Nat
  residue : Int
  deriving DecidableEq, Repr

abbrev ResidueWorld := ResidueQuery → Nat

local instance residueWorldEvidenceType : EvidenceType ResidueWorld where

local instance residueWorldModel :
    AdditiveWorldModel ResidueWorld ResidueQuery Nat where
  extract := fun world query => world query
  extract_add := by
    intro first second query
    rfl

def modThreeOne : ResidueQuery := ⟨3, 1⟩

/-- A one-fact toy world: it contains precisely the residue query used below. -/
def oneResidueWorld : ResidueWorld := fun query =>
  if query = modThreeOne then 1 else 0

theorem oneResidueWorld_extract :
    AdditiveWorldModel.extract
      (State := ResidueWorld) (Query := ResidueQuery) (Ev := Nat)
      oneResidueWorld modThreeOne = 1 := by
  rfl

/-- Positive extracted support is interpreted by a proved mod-3 rejector. -/
def oneTargetResidueReadout :
    CertifiedReadout ResidueQuery Nat
      (fun program : Prog => Reproduces program oneTarget) where
  query := modThreeOne
  certifiedEvidence := fun evidence => 0 < evidence
  derive := by
    intro _evidence _hpositive
    exact modKRejector 3 oneTarget

theorem oneTargetResidueEvidence :
    oneTargetResidueReadout.certifiedEvidence
      (AdditiveWorldModel.extract
        (State := ResidueWorld) (Query := ResidueQuery) (Ev := Nat)
        oneResidueWorld oneTargetResidueReadout.query) := by
  change 0 < 1
  exact Nat.zero_lt_succ 0

def oneTargetResidueCertificate :
    CertifiedProgramRejector
      (fun program : Prog => Reproduces program oneTarget) :=
  certificateFromWorld oneTargetResidueReadout oneResidueWorld
    oneTargetResidueEvidence

/-- The extracted certificate recovers the sealed mod-3 rejection on the nose. -/
theorem oneTargetResidueCertificate_rejects_iff {program : Prog} :
    oneTargetResidueCertificate.rejects program ↔
      ModKIncompatible 3 program oneTarget :=
  Iff.rfl

def oneTargetResidueStatePrune : SearchNode orgMemoRoot → Prop :=
  statePruneFromWorld oneTargetResidueReadout oneResidueWorld
    oneTargetResidueEvidence

theorem oneTargetResidueStatePrune_certified :
    CertifiedHardMask
      (fun program : Prog => Reproduces program oneTarget)
      oneTargetResidueStatePrune := by
  simpa [oneTargetResidueStatePrune] using
    (statePruneFromWorld_certified
      (root := orgMemoRoot)
      (property := fun program : Prog => Reproduces program oneTarget)
      oneTargetResidueReadout oneResidueWorld oneTargetResidueEvidence)

#print axioms statePruneFromWorld_certified
#print axioms oneResidueWorld_extract
#print axioms oneTargetResidueCertificate_rejects_iff
#print axioms oneTargetResidueStatePrune_certified

end Mettapedia.PLN.WorldModel.CertifiedMaskHook
