import Mettapedia.ProbabilityTheory.StochasticInference.Ledger
import Mettapedia.PLN.WorldModel.EvidenceContracts

/-!
# Count evidence

When payloads are observations of the same declared experiment, the count
view reads the active observations of that experiment. The resulting counts
can use the existing PLN and NARS finite evidence interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.StochasticInference.EvidenceLedger

open Mettapedia.PLN.WorldModel.EvidenceSpaces
open Mettapedia.PLN.WorldModel.EvidenceContracts (ledgerEvidence ledgerEvidence_eq_ofSamples)

variable {Id W : Type*}

def activeIds [DecidableEq Id] (ledger : EvidenceLedger Id W) : Finset Id :=
  (ledger.active.map EvidenceEntry.id).toFinset

def counts (ledger : EvidenceLedger Id W) (query : W → Bool) : Evidence ℕ :=
  ofSamples query ((ledger.active.map EvidenceEntry.payload : List W) : Multiset W)

/-- The executable count agrees with the identified-observation semantics
when each active event carries its declared observation. -/
theorem counts_exact [DecidableEq Id] (ledger : EvidenceLedger Id W) (query : W → Bool)
    (world : Id → W) (payloads : ∀ entry ∈ ledger.active, entry.payload = world entry.id) :
    ledger.counts query = ledgerEvidence world query ledger.activeIds := by
  rw [ledgerEvidence_eq_ofSamples]
  simp only [counts, activeIds, List.toFinset_val, List.dedup_eq_self.mpr ledger.active_distinct,
    Multiset.map_coe, List.map_map]
  congr 2
  apply List.map_congr_left
  exact payloads

end Mettapedia.ProbabilityTheory.StochasticInference.EvidenceLedger
