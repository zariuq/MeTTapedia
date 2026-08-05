import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.Core

/-!
# Exactly-once causal innovation

The evidence plane of the unified carrier accumulates fresh packets, but
ordinary addition cannot distinguish an independent repeated measurement from
a replay of one causal innovation.  This module adds an explicit innovation
identity and a finite provenance ledger.  A previously unseen identity
contributes its payload once; any later manifestation of that identity is
read-only.  Distinct identities accumulate even when their payloads are equal.

The construction is generic over an additive commutative evidence carrier and
then specializes to `WeightedEvidence`.  At a fresh identity its projection is
exactly the existing `evidenceStep`; at a repeated identity it leaves both the
posterior and innovation planes unchanged.

This formalizes the algebraic core of the causal-idempotence and
independent-evidence contracts proposed in Goertzel's Causal Memory and Credit
Protocol (2026).  Correct assignment of causal identities and conditional
information remain external obligations; the ledger cannot infer causality
from a payload alone.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

open Mettapedia.PLN.Evidence
open scoped ENNReal

universe uId uEvidence

/-- One evidential manifestation together with the identity of the causal
innovation that generated it. -/
structure InnovationPacket (Id : Type uId) (Evidence : Type uEvidence) where
  id : Id
  evidence : Evidence

/-- A finite provenance index and the accepted payload for every identity.
Values outside `seen` are intentionally observationally irrelevant. -/
structure CausalInnovationLedger
    (Id : Type uId) (Evidence : Type uEvidence) where
  seen : Finset Id
  payload : Id → Evidence

namespace CausalInnovationLedger

variable {Id : Type uId} {Evidence : Type uEvidence}

/-- Empty provenance with the neutral payload outside its support. -/
def empty [Zero Evidence] : CausalInnovationLedger Id Evidence where
  seen := ∅
  payload := fun _ => 0

/-- Accepted evidence is derived from the finite provenance support. -/
def total [AddCommMonoid Evidence]
    (ledger : CausalInnovationLedger Id Evidence) : Evidence :=
  ledger.seen.sum ledger.payload

@[simp] private theorem functionUpdate_same [DecidableEq Id]
    (payload : Id → Evidence) (identity : Id) (value : Evidence) :
    Function.update payload identity value identity = value := by
  simp [Function.update]

private theorem functionUpdate_of_ne [DecidableEq Id]
    (payload : Id → Evidence) (updated queried : Id) (value : Evidence)
    (hne : queried ≠ updated) :
    Function.update payload updated value queried = payload queried := by
  simp [Function.update, hne]

/-- Assimilate a packet only when its causal identity is new.  The first
accepted payload is retained for provenance; a conflicting replay is ignored
rather than silently changing the meaning of an existing identity. -/
def assimilate [DecidableEq Id]
    (ledger : CausalInnovationLedger Id Evidence)
    (packet : InnovationPacket Id Evidence) :
    CausalInnovationLedger Id Evidence :=
  if packet.id ∈ ledger.seen then
    ledger
  else
    { seen := insert packet.id ledger.seen
      payload := Function.update ledger.payload packet.id packet.evidence }

@[simp] theorem total_empty [AddCommMonoid Evidence] :
    total (empty : CausalInnovationLedger Id Evidence) = 0 := by
  simp [total, empty]

@[simp] theorem assimilate_of_seen [DecidableEq Id]
    (ledger : CausalInnovationLedger Id Evidence)
    (packet : InnovationPacket Id Evidence)
    (hseen : packet.id ∈ ledger.seen) :
    assimilate ledger packet = ledger := by
  simp [assimilate, hseen]

@[simp] theorem assimilate_seen [DecidableEq Id]
    (ledger : CausalInnovationLedger Id Evidence)
    (packet : InnovationPacket Id Evidence) :
    packet.id ∈ (assimilate ledger packet).seen := by
  by_cases hseen : packet.id ∈ ledger.seen
  · simp [assimilate, hseen]
  · simp [assimilate, hseen]

/-- A fresh causal identity contributes exactly one payload. -/
theorem total_assimilate_of_fresh [DecidableEq Id] [AddCommMonoid Evidence]
    (ledger : CausalInnovationLedger Id Evidence)
    (packet : InnovationPacket Id Evidence)
    (hfresh : packet.id ∉ ledger.seen) :
    total (assimilate ledger packet) =
      total ledger + packet.evidence := by
  unfold total
  rw [assimilate]
  simp only [hfresh, ↓reduceIte]
  rw [Finset.sum_insert hfresh]
  rw [functionUpdate_same]
  have hremaining :
      ∑ identity ∈ ledger.seen,
          Function.update ledger.payload packet.id packet.evidence identity =
        ∑ identity ∈ ledger.seen, ledger.payload identity := by
    apply Finset.sum_congr rfl
    intro identity hidentity
    have hne : identity ≠ packet.id := by
      intro heq
      subst identity
      exact hfresh hidentity
    rw [functionUpdate_of_ne _ _ _ _ hne]
  rw [hremaining]
  exact add_comm packet.evidence _

/-- Replaying an already assimilated identity changes neither provenance nor
accepted evidence. -/
theorem assimilate_idempotent [DecidableEq Id]
    (ledger : CausalInnovationLedger Id Evidence)
    (packet : InnovationPacket Id Evidence) :
    assimilate (assimilate ledger packet) packet =
      assimilate ledger packet := by
  exact assimilate_of_seen _ _ (assimilate_seen ledger packet)

/-- Two distinct fresh identities both contribute, even when their payload
directions or values happen to agree. -/
theorem total_assimilate_two_distinct [DecidableEq Id] [AddCommMonoid Evidence]
    (ledger : CausalInnovationLedger Id Evidence)
    (first second : InnovationPacket Id Evidence)
    (hfirst : first.id ∉ ledger.seen)
    (hsecond : second.id ∉ ledger.seen)
    (hne : second.id ≠ first.id) :
    total (assimilate (assimilate ledger first) second) =
      total ledger + first.evidence + second.evidence := by
  have hsecondFresh :
      second.id ∉ (assimilate ledger first).seen := by
    simp [assimilate, hfirst, hsecond, hne]
  rw [total_assimilate_of_fresh _ _ hsecondFresh]
  rw [total_assimilate_of_fresh _ _ hfirst]

/-- The accepted total of distinct fresh packets is independent of their
arrival order, although the ledger still records both causal identities. -/
theorem total_assimilate_two_distinct_commutes
    [DecidableEq Id] [AddCommMonoid Evidence]
    (ledger : CausalInnovationLedger Id Evidence)
    (first second : InnovationPacket Id Evidence)
    (hfirst : first.id ∉ ledger.seen)
    (hsecond : second.id ∉ ledger.seen)
    (hne : first.id ≠ second.id) :
    total (assimilate (assimilate ledger first) second) =
      total (assimilate (assimilate ledger second) first) := by
  rw [total_assimilate_two_distinct ledger first second hfirst hsecond hne.symm]
  rw [total_assimilate_two_distinct ledger second first hsecond hfirst hne]
  ac_rfl

end CausalInnovationLedger

/-! ## Projection into the unified-carrier evidence plane -/

/-- Posterior evidence paired with a provenance-aware episode ledger. -/
structure CausalEvidenceState (Id : Type uId) where
  posterior : WeightedEvidence
  innovation : CausalInnovationLedger Id WeightedEvidence

namespace CausalEvidenceState

variable {Id : Type uId}

/-- Forget provenance while retaining exactly the state consumed by the
existing unified carrier. -/
noncomputable def toEvidenceLedger
    (state : CausalEvidenceState Id) : EvidenceLedger where
  posterior := state.posterior
  innovation := state.innovation.total

/-- A fresh causal identity performs the existing evidence-plane transition;
a replay is a read-only event. -/
noncomputable def assimilate [DecidableEq Id]
    (retention : ℝ≥0∞) (state : CausalEvidenceState Id)
    (packet : InnovationPacket Id WeightedEvidence) :
    CausalEvidenceState Id :=
  if packet.id ∈ state.innovation.seen then
    state
  else
    { posterior :=
        WeightedEvidence.fadeThenFuse retention state.posterior packet.evidence
      innovation := state.innovation.assimilate packet }

/-- On a new causal identity, provenance-aware assimilation projects exactly
to the existing unified-carrier `evidenceStep`. -/
theorem toEvidenceLedger_assimilate_of_fresh [DecidableEq Id]
    (retention : ℝ≥0∞) (state : CausalEvidenceState Id)
    (packet : InnovationPacket Id WeightedEvidence)
    (hfresh : packet.id ∉ state.innovation.seen) :
    toEvidenceLedger (assimilate retention state packet) =
      evidenceStep retention state.toEvidenceLedger packet.evidence := by
  simp [assimilate, hfresh, toEvidenceLedger, evidenceStep,
    CausalInnovationLedger.total_assimilate_of_fresh]

/-- A repeated causal identity cannot rewrite either evidence plane. -/
theorem assimilate_of_seen [DecidableEq Id]
    (retention : ℝ≥0∞) (state : CausalEvidenceState Id)
    (packet : InnovationPacket Id WeightedEvidence)
    (hseen : packet.id ∈ state.innovation.seen) :
    assimilate retention state packet = state := by
  simp [assimilate, hseen]

end CausalEvidenceState

/-! ## Positive and negative executable boundaries -/

namespace CausalInnovationFixture

def emptyLedger : CausalInnovationLedger (Fin 2) ℕ :=
  CausalInnovationLedger.empty

def first : InnovationPacket (Fin 2) ℕ :=
  ⟨0, 3⟩

def independentSameEvidence : InnovationPacket (Fin 2) ℕ :=
  ⟨1, 3⟩

def conflictingReplay : InnovationPacket (Fin 2) ℕ :=
  ⟨0, 9⟩

/-- Replaying one causal innovation is counted once. -/
theorem duplicate_manifestation_is_idempotent :
    (emptyLedger.assimilate first).assimilate first =
      emptyLedger.assimilate first := by
  exact CausalInnovationLedger.assimilate_idempotent _ _

/-- An independent observation with the same payload still contributes its
own evidence because its causal identity is distinct. -/
theorem independent_same_evidence_accumulates :
    ((emptyLedger.assimilate first).assimilate independentSameEvidence).total =
      6 := by
  decide

/-- A naive additive replay overcounts the first innovation, while the causal
ledger retains its single accepted contribution. -/
theorem naive_duplicate_accumulator_overcounts :
    [first.evidence, first.evidence].sum = 6 ∧
      ((emptyLedger.assimilate first).assimilate first).total = 3 := by
  decide

/-- Reusing one identity for conflicting payloads does not silently revise the
accepted evidence.  The identity assignment must instead be rejected, split,
or versioned by the external causal-responsibility layer. -/
theorem conflicting_replay_is_not_new_evidence :
    ((emptyLedger.assimilate first).assimilate conflictingReplay).total = 3 ∧
      ((emptyLedger.assimilate conflictingReplay).assimilate first).total = 9 := by
  decide

noncomputable def weightedPacket :
    InnovationPacket Bool WeightedEvidence where
  id := false
  evidence := ⟨1, 0⟩

noncomputable def emptyWeightedState : CausalEvidenceState Bool where
  posterior := 0
  innovation := CausalInnovationLedger.empty

/-- The generic causal ledger is genuinely connected to the production
weighted-evidence transition at its fresh-packet boundary. -/
theorem fresh_weighted_packet_recovers_evidenceStep (retention : ℝ≥0∞) :
    (emptyWeightedState.assimilate retention weightedPacket).toEvidenceLedger =
      evidenceStep retention emptyWeightedState.toEvidenceLedger
        weightedPacket.evidence := by
  apply CausalEvidenceState.toEvidenceLedger_assimilate_of_fresh
  simp [emptyWeightedState, CausalInnovationLedger.empty]

end CausalInnovationFixture

#print axioms CausalInnovationLedger.total_assimilate_of_fresh
#print axioms CausalInnovationLedger.assimilate_idempotent
#print axioms CausalInnovationLedger.total_assimilate_two_distinct_commutes
#print axioms CausalEvidenceState.toEvidenceLedger_assimilate_of_fresh
#print axioms CausalInnovationFixture.naive_duplicate_accumulator_overcounts
#print axioms CausalInnovationFixture.conflicting_replay_is_not_new_evidence

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
