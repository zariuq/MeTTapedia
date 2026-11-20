import Mettapedia.ProbabilityTheory.StochasticInference.Finite

/-!
# History-dependent likelihoods

Use this interface when a report's likelihood depends on which older
reports are available. Retraction edits the raw ledger and takes a fresh
snapshot. The likelihood model supplies the conditional law at the new
history, including histories with missing reports.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.StochasticInference

open Mettapedia.ProbabilityTheory.BayesianNetworks.ExecutableFactorTable (Config)

variable {n : Nat} {domains : Fin n → Nat}

structure HistoryModel (Id Payload : Type*) (domains : Fin n → Nat) where
  base : List (Potential domains)
  likelihood : List (Id × Payload) → Id → Payload → Potential domains

namespace HistoryModel

variable {Id Payload : Type*}

def history (entries : List (EvidenceEntry Id Payload)) : List (Id × Payload) :=
  entries.map fun entry => (entry.id, entry.payload)

private def scoreEntries (model : HistoryModel Id Payload domains) :
    List (EvidenceEntry Id Payload) → List (EvidenceEntry Id (Potential domains))
  | [] => []
  | entry :: older =>
    ⟨entry.id, model.likelihood (history older) entry.id entry.payload, true⟩ ::
      model.scoreEntries older

private theorem scoreEntries_ids (model : HistoryModel Id Payload domains)
    (entries : List (EvidenceEntry Id Payload)) :
    (model.scoreEntries entries).map EvidenceEntry.id = entries.map EvidenceEntry.id := by
  induction entries with
  | nil => rfl
  | cons entry older ih =>
    simp only [scoreEntries, List.map_cons, ih]

private theorem scoreEntries_active (model : HistoryModel Id Payload domains)
    (entries : List (EvidenceEntry Id Payload)) :
    (model.scoreEntries entries).filter EvidenceEntry.active = model.scoreEntries entries := by
  induction entries with
  | nil => rfl
  | cons entry older ih =>
    simp [scoreEntries, ih]

/-- A snapshot is ready for ordinary factor inference and keeps base weights
separate from the likelihood history. Apply later edits to the raw ledger. -/
def snapshot (model : HistoryModel Id Payload domains) (ledger : EvidenceLedger Id Payload) :
    State Id domains :=
  ⟨model.base, ⟨model.scoreEntries ledger.active, by
    rw [scoreEntries_ids]
    exact ledger.active_distinct⟩⟩

theorem snapshot_factors (model : HistoryModel Id Payload domains)
    (ledger : EvidenceLedger Id Payload) :
    (model.snapshot ledger).factors = model.base ++
      (model.scoreEntries ledger.active).map EvidenceEntry.payload := by
  simp [snapshot, State.factors, EvidenceLedger.active, scoreEntries_active]

/-- Scoring a new report uses precisely the older active history. -/
theorem snapshot_observe [DecidableEq Id] [DecidableEq Payload]
    (model : HistoryModel Id Payload domains) (ledger next : EvidenceLedger Id Payload)
    (id : Id) (payload : Payload) (fresh : ledger.lookup id = none)
    (recorded : ledger.observe id payload = .ok (.recorded, next))
    (positive : ∀ v, 0 < domains v) (x : Config domains) :
    (model.snapshot next).unnormalized positive x =
      (model.snapshot ledger).unnormalized positive x *
        (model.likelihood (history ledger.active) id payload).table.value domains positive x := by
  rw [EvidenceLedger.observe_fresh _ _ _ fresh] at recorded
  have same := congrArg Prod.snd (Except.ok.inj recorded)
  change _ = next at same
  subst next
  simp [State.unnormalized, State.tables, snapshot_factors, EvidenceLedger.active,
    scoreEntries, worldWeight, List.prod_append, mul_comm, mul_left_comm]

end HistoryModel

end Mettapedia.ProbabilityTheory.StochasticInference
