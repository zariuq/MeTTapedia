import Mettapedia.TypeTheory.DesignDetermination
import Mettapedia.TypeTheory.MetatheoryChoiceConstraints
import Mettapedia.TypeTheory.IdentityEliminationCapabilities
import Mettapedia.TypeTheory.CwfTarskiUniverse
import Mettapedia.Languages.MeTTa.PrimeCandidates.ScopedIdentityStatus
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeRelatorQualification
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.PolarizedNeedProviderWorkload

/-!
# Evidence for candidate decisions, not a selected language

This entry point collects constraints and discriminating workloads. It does
not define a `Prime` calculus or select a best candidate by import order.

* `MetatheoryChoiceConstraints.provedConstraints` is a bag of proved
  compatibility and separation properties, not one assembled language.
* `DesignDetermination` distinguishes a nonvacuous implication over a stated
  candidate class from a construction satisfying the requirements.
* `FormationSensitiveNativeRelatorQualification` qualifies the cumulative
  presentation's List/J/relator roots. Its J does not select K or global UIP.
* `ScopedIdentityStatus` includes an existing exact-image embedding of the
  native J computation into the conversion-enriched natural model, stable
  under typed substitution. Its joint theorem keeps the artifact layers
  separate rather than presenting them as one settled identity theory.
* `IdentityEliminationCapabilities` names the stronger semantic premises
  needed for a route-family Hedberg theorem. Deciding proof syntax is not a
  decision procedure for inhabitation of arbitrary identity fibres.
* `CwfTarskiUniverse` supplies a common set-family compatibility model, not
  an adequate interpretation of the full object syntax in HOTG.

The executed workload below compares two source programs in the same Need
machine: shared provider selection and fresh provider selection. It proves
that the selected observation distinguishes them. It is not a theorem that
all requirements force call-time choice over every possible evaluator.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

open Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DecisionSurface

open Mettapedia.TypeTheory.DesignDetermination
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

namespace Sharing

open PolarizedNeedProviderWorkload

/-- Retaining just distinct returned values forgets both multiplicity and
the correlation of the selected providers in this concrete workload. -/
theorem same_value_support_different_observations :
    ((observations scope 64 sharedWorkload).map Prod.fst).toFinset =
      ((observations scope 64 freshWorkload).map Prod.fst).toFinset ∧
    observations scope 64 sharedWorkload ≠ observations scope 64 freshWorkload := by
  refine ⟨?_, provider_sharing_changes_observation⟩
  rw [shared_provider_correlates, fresh_provider_selects_independently]
  simp

/-- A consumer of complete observations cannot in general be implemented
from this coarse value-support readout, even on these two programs. -/
theorem no_observation_recovery_from_value_support :
    ¬ ∃ recover : Finset (Option (Tower.Tm 0)) →
        List (Option (Tower.Tm 0) × List Event),
      recover (((observations scope 64 sharedWorkload).map Prod.fst).toFinset) =
        observations scope 64 sharedWorkload ∧
      recover (((observations scope 64 freshWorkload).map Prod.fst).toFinset) =
        observations scope 64 freshWorkload := by
  rintro ⟨recover, shared, fresh⟩
  apply same_value_support_different_observations.2
  exact shared.symm.trans ((congrArg recover
    same_value_support_different_observations.1).trans fresh)

end Sharing

#print axioms Sharing.same_value_support_different_observations
#print axioms Sharing.no_observation_recovery_from_value_support

end Mettapedia.Languages.MeTTa.PrimeCandidates.DecisionSurface
