import Mettapedia.Logic.HOL.TH0SubstitutionOperationalGSLT
import Mettapedia.TypeTheory.CellHeightObservationHorizonOrthogonality
import Mettapedia.TypeTheory.OperationalIntensionalExtensionalLocalTruncation

/-!
# A locally thin, proof-relevant, open-ended profile

Three independent design axes are often conflated:

* comparison structure between semantic translations;
* occurrence evidence for operational derivations;
* the finite or open-ended horizon of observations.

This module packages the three axes in one profile and constructs a concrete
inhabitant from existing nontrivial models.  Its comparison component is the
actual locally thin operational/intensional/extensional sector.  Its
operational component is intrinsically typed TH0 simultaneous substitution,
with two distinguishable substitutions over the same source and target.  Its
observation component is the Cantor-prefix property that retains an unresolved
tail at every finite horizon.

The resulting counterexamples rule out three tempting global inferences:
local comparison thinness does not make operational evidence irrelevant, does
not impose a uniform finite observation horizon, and does not impose a global
cutoff on future cell dimensions.  Conversely, proof-relevant operational
evidence does not force the selected comparison sector to be thick.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.LocallyThinOpenEndedProofRelevantProfile

open Mettapedia.GSLT.ProofRelevant
open Mettapedia.Logic.HOL
open Mettapedia.Logic.WorldModel.FiniteEvidence
open Mettapedia.Logic.WorldModel.OpenEnded
open Mettapedia.Computability

universe uCell uWorld uSnapshot uOperational

abbrev HorizonProfile :=
  Mettapedia.TypeTheory.CellHeightObservationHorizonOrthogonality.Profile

/-- One independent selection of a comparison layer, an observation problem,
and a proof-relevant operational transition.  The record intentionally adds
no implication between these components. -/
structure Profile where
  architecture : HorizonProfile.{uCell, uWorld, uSnapshot}
  operational : ProofRelevantGSLT.{uOperational}
  source : operational.theory.Term
  target : operational.theory.Term

namespace Profile

/-- The selected comparison fibre is propositionally unique. -/
def ComparisonThin (profile : Profile) : Prop :=
  Mettapedia.TypeTheory.CellHeightObservationHorizonOrthogonality.Profile.CellThin
    profile.architecture

/-- The observation problem retains an unresolved tail at every finite
horizon. -/
def OpenTail (profile : Profile) : Prop :=
  Mettapedia.TypeTheory.CellHeightObservationHorizonOrthogonality.Profile.OpenTail
    profile.architecture

/-- The selected operational transition exists extensionally. -/
def Reachable (profile : Profile) : Prop :=
  profile.operational.theory.Step profile.source profile.target

/-- The selected operational transition has distinguishable occurrence
evidence over its fixed endpoints. -/
def EvidenceRich (profile : Profile) : Prop :=
  ¬ Subsingleton
    (profile.operational.steps.Evidence profile.source profile.target)

end Profile

/-! ## One concrete profile carrying all three properties -/

/-- The actual O/I/E two-cell sector paired with the open-tail Cantor
observation problem. -/
def oieOpenArchitecture : HorizonProfile.{0, 0, 0} where
  tower :=
    Mettapedia.TypeTheory.OperationalIntensionalExtensionalLocalTruncation.tower
  dimension := 1
  World := CantorSpace
  observation := cantorPrefixObservation
  property := someBitTrue

/-- The O/I/E comparison sector, open-tail observations, and TH0 operational
substitution coexist in one concrete profile. -/
def oieOpenTH0 : Profile.{0, 0, 0, 0} where
  architecture := oieOpenArchitecture
  operational :=
    Mettapedia.Logic.HOL.TH0SubstitutionOperationalGSLT.system
      Mettapedia.Logic.HOL.TH0SyntacticUnifierService.Canary.individual
  source :=
    Mettapedia.Logic.HOL.TH0SubstitutionOperationalGSLT.Canary.constantSource
  target :=
    Mettapedia.Logic.HOL.TH0SubstitutionOperationalGSLT.Canary.constantTarget

theorem oieOpenTH0_has_all_three_axes :
    oieOpenTH0.ComparisonThin ∧
      oieOpenTH0.OpenTail ∧
      oieOpenTH0.Reachable ∧
      oieOpenTH0.EvidenceRich := by
  refine ⟨Mettapedia.TypeTheory.OperationalIntensionalExtensionalLocalTruncation.locallyThinAt_twoCells,
    someBitTrue_hasUnresolvedTail, ?_, ?_⟩
  · exact
      Mettapedia.Logic.HOL.TH0SubstitutionOperationalGSLT.Canary.proof_relevant_fibre_over_thin_step.1
  · exact
      Mettapedia.Logic.HOL.TH0SubstitutionOperationalGSLT.Canary.proof_relevant_fibre_over_thin_step.2

/-! ## Non-implication theorems -/

/-- Thin comparisons between translations do not identify operational
derivation evidence. -/
theorem comparisonThin_does_not_imply_evidenceSubsingleton :
    ¬ ∀ profile : Profile.{0, 0, 0, 0},
      profile.ComparisonThin →
        Subsingleton
          (profile.operational.steps.Evidence profile.source profile.target) := by
  intro purported
  have subsingletonEvidence :=
    purported oieOpenTH0 oieOpenTH0_has_all_three_axes.1
  exact oieOpenTH0_has_all_three_axes.2.2.2 subsingletonEvidence

/-- Thin comparisons between translations do not bound observation by one
uniform finite prefix. -/
theorem comparisonThin_does_not_imply_uniformFiniteObservation :
    ¬ ∀ profile : Profile.{0, 0, 0, 0},
      profile.ComparisonThin →
        Mettapedia.TypeTheory.CellHeightObservationHorizonOrthogonality.Profile.UniformFinite
          profile.architecture := by
  intro purported
  have finite := purported oieOpenTH0 oieOpenTH0_has_all_three_axes.1
  exact someBitTrue_not_finitelyDetermined finite

/-- Proof-relevant operational evidence does not force the selected
comparison layer to be thick. -/
theorem evidenceRich_does_not_imply_comparisonThick :
    ¬ ∀ profile : Profile.{0, 0, 0, 0},
      profile.EvidenceRich → ¬ profile.ComparisonThin := by
  intro purported
  have notThin := purported oieOpenTH0 oieOpenTH0_has_all_three_axes.2.2.2
  exact notThin oieOpenTH0_has_all_three_axes.1

/-! ## Local optimization without a global ceiling -/

/-- The same specimen has a local two-cell truncation certificate, raw
comparison history, rich TH0 operational evidence, and an unresolved
observation tail. -/
theorem local_erasure_with_two_histories_and_open_tail :
    Nonempty
        (Mettapedia.TypeTheory.OperationalIntensionalExtensionalLocalTruncation.tower.LocalTruncationCertificate
          1) ∧
      Mettapedia.TypeTheory.OperationalIntensionalExtensionalLocallyThinModeTheory.rawFactorRoundTrip ≠
        Mettapedia.TypeTheory.OperationalIntensionalExtensionalLocallyThinModeTheory.rawFactorIdentity ∧
      oieOpenTH0.EvidenceRich ∧
      oieOpenTH0.OpenTail := by
  exact ⟨⟨Mettapedia.TypeTheory.OperationalIntensionalExtensionalLocalTruncation.twoCellCertificate⟩,
    Mettapedia.TypeTheory.OperationalIntensionalExtensionalLocallyThinModeTheory.raw_factor_history_distinct,
    oieOpenTH0_has_all_three_axes.2.2.2,
    oieOpenTH0_has_all_three_axes.2.1⟩

/-- Optimizing the currently thin O/I/E comparison sector is not a theorem
that every future globular extension stops at any finite dimension. -/
theorem local_certificate_does_not_supply_global_cell_cutoff :
    Nonempty
        (Mettapedia.TypeTheory.OperationalIntensionalExtensionalLocalTruncation.tower.LocalTruncationCertificate
          1) ∧
      ¬ ∃ horizon : Nat, ∀ candidate :
          Mettapedia.CategoryTheory.Higher.GlobularSet.{0},
        candidate.ThinBelow horizon → candidate.LocallyThinAt horizon :=
  Mettapedia.TypeTheory.OperationalIntensionalExtensionalLocalTruncation.local_core_thinness_without_global_cutoff

/-! ## Audited theorem crowns -/

#print axioms oieOpenTH0_has_all_three_axes
#print axioms comparisonThin_does_not_imply_evidenceSubsingleton
#print axioms comparisonThin_does_not_imply_uniformFiniteObservation
#print axioms evidenceRich_does_not_imply_comparisonThick
#print axioms local_erasure_with_two_histories_and_open_tail
#print axioms local_certificate_does_not_supply_global_cell_cutoff

end Mettapedia.TypeTheory.LocallyThinOpenEndedProofRelevantProfile
