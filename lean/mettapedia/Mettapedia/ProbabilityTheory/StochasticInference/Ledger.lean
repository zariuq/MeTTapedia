import Mathlib.Data.List.Nodup

/-!
# Identified evidence with exact withdrawal

A source identity has one immutable payload. Withdrawal changes its activity
and keeps its identity, so replay cannot undo a withdrawal. Restoring a source
is an explicit change of activity. The same carrier can store observations
for either a likelihood model or a count model.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.StochasticInference

structure EvidenceEntry (Id Payload : Type*) where
  id : Id
  payload : Payload
  active : Bool
  deriving DecidableEq

structure EvidenceLedger (Id Payload : Type*) where
  entries : List (EvidenceEntry Id Payload)
  distinct : (entries.map EvidenceEntry.id).Nodup
  deriving DecidableEq

namespace EvidenceLedger

variable {Id Payload : Type*}

def empty : EvidenceLedger Id Payload := ⟨[], List.nodup_nil⟩

def active (ledger : EvidenceLedger Id Payload) : List (EvidenceEntry Id Payload) :=
  ledger.entries.filter EvidenceEntry.active

theorem active_distinct (ledger : EvidenceLedger Id Payload) :
    (ledger.active.map EvidenceEntry.id).Nodup :=
  (List.Sublist.map _ List.filter_sublist).nodup ledger.distinct

def lookup [DecidableEq Id] (ledger : EvidenceLedger Id Payload) (id : Id) :
    Option (EvidenceEntry Id Payload) :=
  ledger.entries.find? (fun entry => decide (entry.id = id))

theorem lookup_none [DecidableEq Id] (ledger : EvidenceLedger Id Payload) (id : Id) :
    ledger.lookup id = none ↔ id ∉ ledger.entries.map EvidenceEntry.id := by
  simp only [lookup, List.find?_eq_none, decide_eq_true_eq, List.mem_map]
  aesop

inductive Arrival where
  | recorded
  | replay
  deriving DecidableEq, Repr

private def insertFresh [DecidableEq Id] (ledger : EvidenceLedger Id Payload) (id : Id)
    (payload : Payload) (fresh : ledger.lookup id = none) : EvidenceLedger Id Payload :=
  ⟨⟨id, payload, true⟩ :: ledger.entries,
    List.nodup_cons.mpr ⟨(lookup_none ledger id).mp fresh, ledger.distinct⟩⟩

/-- An error identifies a conflicting payload for an established source. -/
def observe [DecidableEq Id] [DecidableEq Payload] (ledger : EvidenceLedger Id Payload)
    (id : Id) (payload : Payload) : Except Id (Arrival × EvidenceLedger Id Payload) :=
  match found : ledger.lookup id with
  | some prior =>
    if prior.payload = payload then .ok (.replay, ledger) else .error id
  | none =>
    .ok (.recorded, ledger.insertFresh id payload found)

theorem observe_replay [DecidableEq Id] [DecidableEq Payload] (ledger : EvidenceLedger Id Payload)
    (id : Id) (prior : EvidenceEntry Id Payload) (found : ledger.lookup id = some prior) :
    ledger.observe id prior.payload = .ok (.replay, ledger) := by
  unfold observe
  split <;> simp_all

theorem observe_conflict [DecidableEq Id] [DecidableEq Payload] (ledger : EvidenceLedger Id Payload)
    (id : Id) (prior : EvidenceEntry Id Payload) (found : ledger.lookup id = some prior)
    (payload : Payload) (different : prior.payload ≠ payload) :
    ledger.observe id payload = .error id := by
  unfold observe
  split <;> simp_all

theorem observe_fresh [DecidableEq Id] [DecidableEq Payload] (ledger : EvidenceLedger Id Payload)
    (id : Id) (payload : Payload) (fresh : ledger.lookup id = none) :
    ledger.observe id payload =
      .ok (.recorded, ⟨⟨id, payload, true⟩ :: ledger.entries,
        List.nodup_cons.mpr ⟨(lookup_none ledger id).mp fresh, ledger.distinct⟩⟩) := by
  unfold observe
  split <;> simp_all [insertFresh]

private def setEntry [DecidableEq Id] (id : Id) (on : Bool) (entry : EvidenceEntry Id Payload) :
    EvidenceEntry Id Payload :=
  if entry.id = id then { entry with active := on } else entry

@[simp] private theorem setEntry_id [DecidableEq Id] (id : Id) (on : Bool)
    (entry : EvidenceEntry Id Payload) : (setEntry id on entry).id = entry.id := by
  by_cases same : entry.id = id <;> simp [setEntry, same]

private theorem setEntry_absorbs [DecidableEq Id] (id : Id) (first second : Bool)
    (entry : EvidenceEntry Id Payload) :
    setEntry id second (setEntry id first entry) = setEntry id second entry := by
  by_cases same : entry.id = id <;> simp [setEntry, same]

def setActive [DecidableEq Id] (ledger : EvidenceLedger Id Payload) (id : Id) (on : Bool) :
    EvidenceLedger Id Payload :=
  ⟨ledger.entries.map (setEntry id on), by
    simpa only [List.map_map, Function.comp_def, setEntry_id] using ledger.distinct⟩

abbrev retract [DecidableEq Id] (ledger : EvidenceLedger Id Payload) (id : Id) :=
  ledger.setActive id false

abbrev restore [DecidableEq Id] (ledger : EvidenceLedger Id Payload) (id : Id) :=
  ledger.setActive id true

@[simp] theorem setActive_ids [DecidableEq Id] (ledger : EvidenceLedger Id Payload) (id : Id)
    (on : Bool) : (ledger.setActive id on).entries.map EvidenceEntry.id =
      ledger.entries.map EvidenceEntry.id := by
  simp only [setActive, List.map_map, Function.comp_def, setEntry_id]

theorem setActive_absorbs [DecidableEq Id] (ledger : EvidenceLedger Id Payload) (id : Id)
    (first second : Bool) : (ledger.setActive id first).setActive id second =
      ledger.setActive id second := by
  cases ledger
  simp only [setActive, List.map_map, Function.comp_def, setEntry_absorbs]

theorem distinct_edits_commute [DecidableEq Id] (ledger : EvidenceLedger Id Payload)
    (a b : Id) (different : a ≠ b) (first second : Bool) :
    (ledger.setActive a first).setActive b second =
      (ledger.setActive b second).setActive a first := by
  have swap (entry : EvidenceEntry Id Payload) :
      setEntry b second (setEntry a first entry) = setEntry a first (setEntry b second entry) := by
    by_cases ha : entry.id = a <;> by_cases hb : entry.id = b
    · exact (different (ha.symm.trans hb)).elim
    · simp [setEntry, ha, different]
    · simp [setEntry, hb, Ne.symm different]
    · simp [setEntry, ha, hb]
  cases ledger
  simp only [setActive, List.map_map, Function.comp_def, swap]

theorem active_retract_fresh [DecidableEq Id] (ledger : EvidenceLedger Id Payload)
    (id : Id) (payload : Payload) (fresh : ledger.lookup id = none) :
    ((ledger.insertFresh id payload fresh).retract id).active = ledger.active := by
  have untouched : ∀ entry ∈ ledger.entries, entry.id ≠ id := by
    intro entry member same
    exact (List.find?_eq_none.mp fresh entry member) (by simp [same])
  have rest : ledger.entries.map (setEntry id false) = ledger.entries := by
    calc
      _ = ledger.entries.map _root_.id := by
        apply List.map_congr_left
        intro entry member
        simp [setEntry, untouched entry member]
      _ = _ := List.map_id _
  have head : setEntry id false (⟨id, payload, true⟩ : EvidenceEntry Id Payload) =
      ⟨id, payload, false⟩ := by simp [setEntry]
  simp [active, setActive, insertFresh, head, rest]

end EvidenceLedger

end Mettapedia.ProbabilityTheory.StochasticInference
