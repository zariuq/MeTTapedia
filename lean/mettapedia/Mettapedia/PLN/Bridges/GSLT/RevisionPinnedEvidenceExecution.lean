import Mettapedia.GSLT.LanguageDef.KernelAuthority
import Mettapedia.Machines.RevisionDependencySet
import Mettapedia.PLN.Bridges.KR.RevisionStampedWitnessBridge
import Mettapedia.TypeTheory.ProofRelevantRouteFamilyBridge

/-!
# Revision-pinned evidence execution across Space, PLN, and rho

This module composes three distinct semantic roles.

* A revisioned evidence space stores ordered count-pair occurrences.
* PLN guarded revision combines exact occurrences without reusing provenance.
* A rho communication path records the execution route which carried the
  checked calculation.

The checker resolves every named occurrence against the claimed store
revision, rejects duplicate occurrence use, and recomputes the exact aggregate
counts.  Its meaning is an independently stated resolution relation, not the
Boolean checker equation.

Provenance non-reuse is deliberately not called stochastic independence.
Product, conditional-independence, exchangeability, and calibration claims
require their own authorities (for example a Bayesian-network d-separation
certificate or a credal bound).  The receipt keeps this boundary explicit.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Bridges.GSLT.RevisionPinnedEvidenceExecution

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.KR.ConceptGeometry.AbstractInheritance
open Mettapedia.Machines
open Mettapedia.PLN.Bridges.KR.RevisionStampedWitnessBridge
open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision

abbrev CountPair := Nat × Nat

/-! ## Revisioned evidence spaces -/

/-- A family of ordered evidence stores with one current revision per store. -/
structure RevisionedEvidenceSpace (StoreId Revision : Type) where
  currentRevision : StoreId → Revision
  entries : StoreId → List CountPair

namespace RevisionedEvidenceSpace

variable {StoreId Revision : Type}

/-- The revision-only observer used by the generic dependency-set theory. -/
def revisionEnvironment (space : RevisionedEvidenceSpace StoreId Revision) :
    RevisionEnvironment StoreId Revision :=
  ⟨space.currentRevision⟩

/-- The current ordered view of one store. -/
def view (space : RevisionedEvidenceSpace StoreId Revision)
    (store : StoreId) : RevisionedStoreView StoreId Revision CountPair :=
  ⟨store, space.currentRevision store, space.entries store⟩

/-- Name one logical occurrence in a current store view. -/
def occurrenceId (space : RevisionedEvidenceSpace StoreId Revision)
    (store : StoreId) (logicalIndex : Nat) :
    StoreOccurrenceId StoreId Revision :=
  (space.view store).occurrenceId logicalIndex

/-- Resolve an occurrence only when its store revision and logical position
are both current. -/
def resolve [DecidableEq StoreId] [DecidableEq Revision]
    (space : RevisionedEvidenceSpace StoreId Revision)
    (occurrence : StoreOccurrenceId StoreId Revision) : Option CountPair :=
  (space.view occurrence.read.storeId).resolve occurrence

@[simp] theorem resolve_occurrenceId [DecidableEq StoreId]
    [DecidableEq Revision]
    (space : RevisionedEvidenceSpace StoreId Revision)
    (store : StoreId) (logicalIndex : Nat) :
    space.resolve (space.occurrenceId store logicalIndex) =
      (space.view store).entries[logicalIndex]? := by
  exact RevisionedStoreView.resolve_current (space.view store) logicalIndex

/-- Replace one ordered store and advance it to a caller-selected revision. -/
def updateStore [DecidableEq StoreId]
    (space : RevisionedEvidenceSpace StoreId Revision)
    (store : StoreId) (nextRevision : Revision)
    (nextEntries : List CountPair) :
    RevisionedEvidenceSpace StoreId Revision where
  currentRevision := Function.update space.currentRevision store nextRevision
  entries := Function.update space.entries store nextEntries

@[simp] theorem resolve_updateStore_other [DecidableEq StoreId]
    [DecidableEq Revision]
    (space : RevisionedEvidenceSpace StoreId Revision)
    (store : StoreId) (nextRevision : Revision)
    (nextEntries : List CountPair)
    (occurrence : StoreOccurrenceId StoreId Revision)
    (different : occurrence.read.storeId ≠ store) :
    (space.updateStore store nextRevision nextEntries).resolve occurrence =
      space.resolve occurrence := by
  simp [resolve, view, updateStore, different]

/-- A genuinely different revision rejects an old occurrence from the updated
store, independently of the replacement payload list. -/
theorem resolve_updateStore_same_stale [DecidableEq StoreId]
    [DecidableEq Revision]
    (space : RevisionedEvidenceSpace StoreId Revision)
    (occurrence : StoreOccurrenceId StoreId Revision)
    (nextRevision : Revision) (nextEntries : List CountPair)
    (changed : nextRevision ≠ occurrence.read.revision) :
    (space.updateStore occurrence.read.storeId nextRevision nextEntries).resolve
      occurrence = none := by
  apply RevisionedStoreView.resolve_stale
  simpa [view, updateStore] using changed.symm

/-- Successful resolution implies that the occurrence's captured revision is
the current revision of its store. -/
theorem currentRevision_eq_of_resolve_eq_some [DecidableEq StoreId]
    [DecidableEq Revision]
    (space : RevisionedEvidenceSpace StoreId Revision)
    {occurrence : StoreOccurrenceId StoreId Revision} {counts : CountPair}
    (resolved : space.resolve occurrence = some counts) :
    space.currentRevision occurrence.read.storeId =
      occurrence.read.revision := by
  by_contra different
  have stale : occurrence.read.revision ≠
      space.currentRevision occurrence.read.storeId := by
    exact fun equalRevision => different equalRevision.symm
  have rejected : space.resolve occurrence = none := by
    exact RevisionedStoreView.resolve_stale
      (space.view occurrence.read.storeId) occurrence stale
  rw [rejected] at resolved
  contradiction

end RevisionedEvidenceSpace

/-! ## Independent relational meaning and executable replay -/

variable {StoreId Revision : Type}
variable [DecidableEq StoreId] [DecidableEq Revision]

/-- Resolve a list of exact occurrences in order. -/
def resolveLedger (space : RevisionedEvidenceSpace StoreId Revision) :
    List (StoreOccurrenceId StoreId Revision) →
      Option (List (StoreOccurrenceId StoreId Revision × CountPair))
  | [] => some []
  | occurrence :: rest => do
      let counts ← space.resolve occurrence
      let tail ← resolveLedger space rest
      pure ((occurrence, counts) :: tail)

/-- Declarative ordered resolution of exact occurrences to count pairs. -/
inductive ResolvesLedger (space : RevisionedEvidenceSpace StoreId Revision) :
    List (StoreOccurrenceId StoreId Revision) →
      List (StoreOccurrenceId StoreId Revision × CountPair) → Prop
  | nil : ResolvesLedger space [] []
  | cons {occurrence : StoreOccurrenceId StoreId Revision}
      {counts : CountPair}
      {rest : List (StoreOccurrenceId StoreId Revision)}
      {tail : List (StoreOccurrenceId StoreId Revision × CountPair)} :
      space.resolve occurrence = some counts →
      ResolvesLedger space rest tail →
      ResolvesLedger space (occurrence :: rest) ((occurrence, counts) :: tail)

namespace ResolvesLedger

theorem resolveLedger_eq_some
    {space : RevisionedEvidenceSpace StoreId Revision}
    {occurrences : List (StoreOccurrenceId StoreId Revision)}
    {ledger : List (StoreOccurrenceId StoreId Revision × CountPair)}
    (resolved : ResolvesLedger space occurrences ledger) :
    resolveLedger space occurrences = some ledger := by
  induction resolved with
  | nil => rfl
  | cons headResolved _ tailIH =>
      simp [resolveLedger, headResolved, tailIH]

theorem of_resolveLedger_eq_some
    (space : RevisionedEvidenceSpace StoreId Revision)
    (occurrences : List (StoreOccurrenceId StoreId Revision))
    (ledger : List (StoreOccurrenceId StoreId Revision × CountPair))
    (computed : resolveLedger space occurrences = some ledger) :
    ResolvesLedger space occurrences ledger := by
  induction occurrences generalizing ledger with
  | nil =>
      simp [resolveLedger] at computed
      subst ledger
      exact .nil
  | cons occurrence rest inductionHypothesis =>
      cases headResult : space.resolve occurrence with
      | none =>
          simp [resolveLedger, headResult] at computed
      | some counts =>
          cases tailResult : resolveLedger space rest with
          | none =>
              simp [resolveLedger, headResult, tailResult] at computed
          | some tail =>
              simp [resolveLedger, headResult, tailResult] at computed
              subst ledger
              exact .cons headResult
                (inductionHypothesis tail tailResult)

theorem resolveLedger_eq_some_iff
    (space : RevisionedEvidenceSpace StoreId Revision)
    (occurrences : List (StoreOccurrenceId StoreId Revision))
    (ledger : List (StoreOccurrenceId StoreId Revision × CountPair)) :
    resolveLedger space occurrences = some ledger ↔
      ResolvesLedger space occurrences ledger :=
  ⟨of_resolveLedger_eq_some space occurrences ledger,
    ResolvesLedger.resolveLedger_eq_some⟩

/-- Ordered resolution preserves the exact occurrence list. -/
theorem occurrence_map
    {space : RevisionedEvidenceSpace StoreId Revision}
    {occurrences : List (StoreOccurrenceId StoreId Revision)}
    {ledger : List (StoreOccurrenceId StoreId Revision × CountPair)}
    (resolved : ResolvesLedger space occurrences ledger) :
    ledger.map Prod.fst = occurrences := by
  induction resolved with
  | nil => rfl
  | cons _ _ inductionHypothesis =>
      simp [inductionHypothesis]

/-- Every named occurrence in a resolved ledger has an exact resolved count
pair in that ledger. -/
theorem exists_resolved_of_mem
    {space : RevisionedEvidenceSpace StoreId Revision}
    {occurrences : List (StoreOccurrenceId StoreId Revision)}
    {ledger : List (StoreOccurrenceId StoreId Revision × CountPair)}
    (resolved : ResolvesLedger space occurrences ledger)
    {occurrence : StoreOccurrenceId StoreId Revision}
    (member : occurrence ∈ occurrences) :
    ∃ counts, (occurrence, counts) ∈ ledger ∧
      space.resolve occurrence = some counts := by
  induction resolved with
  | nil => simp at member
  | @cons head counts rest tail headResolved _ inductionHypothesis =>
      simp only [List.mem_cons] at member
      rcases member with equalHead | tailMember
      · subst equalHead
        exact ⟨counts, by simp, headResolved⟩
      · obtain ⟨foundCounts, foundMember, foundResolved⟩ :=
          inductionHypothesis tailMember
        exact ⟨foundCounts, by simp [foundMember], foundResolved⟩

/-- Every resolved occurrence is current in the generic finite dependency-set
sense. -/
theorem dependencies_valid
    {space : RevisionedEvidenceSpace StoreId Revision}
    {occurrences : List (StoreOccurrenceId StoreId Revision)}
    {ledger : List (StoreOccurrenceId StoreId Revision × CountPair)}
    (resolved : ResolvesLedger space occurrences ledger) :
    RevisionDependencySet.ValidAt space.revisionEnvironment
      occurrences.toFinset := by
  intro occurrence member
  have listMember : occurrence ∈ occurrences := by
    simpa using member
  obtain ⟨counts, _, occurrenceResolved⟩ :=
    resolved.exists_resolved_of_mem listMember
  exact space.currentRevision_eq_of_resolve_eq_some occurrenceResolved

end ResolvesLedger

/-- If one occurrence in a proposed batch does not resolve, ordered replay
fails rather than silently dropping it. -/
theorem resolveLedger_eq_none_of_mem_resolve_eq_none
    (space : RevisionedEvidenceSpace StoreId Revision)
    (occurrences : List (StoreOccurrenceId StoreId Revision))
    {occurrence : StoreOccurrenceId StoreId Revision}
    (member : occurrence ∈ occurrences)
    (unresolved : space.resolve occurrence = none) :
    resolveLedger space occurrences = none := by
  cases computed : resolveLedger space occurrences with
  | none => rfl
  | some ledger =>
      have relational :=
        ResolvesLedger.of_resolveLedger_eq_some space occurrences ledger computed
      obtain ⟨counts, _, resolved⟩ :=
        relational.exists_resolved_of_mem member
      rw [unresolved] at resolved
      contradiction

/-- Aggregate positive and negative counts without forgetting which exact
occurrences produced them. -/
def totalCounts
    (ledger : List (StoreOccurrenceId StoreId Revision × CountPair)) :
    CountPair :=
  ((ledger.map fun item => item.2.1).sum,
    (ledger.map fun item => item.2.2).sum)

/-- Resolve a batch and compute its exact sufficient-statistic pair. -/
def resolvedTotal?
    (space : RevisionedEvidenceSpace StoreId Revision)
    (occurrences : List (StoreOccurrenceId StoreId Revision)) :
    Option CountPair :=
  (resolveLedger space occurrences).map totalCounts

theorem resolvedTotal_eq_some_iff
    (space : RevisionedEvidenceSpace StoreId Revision)
    (occurrences : List (StoreOccurrenceId StoreId Revision))
    (expected : CountPair) :
    resolvedTotal? space occurrences = some expected ↔
      ∃ ledger,
        ResolvesLedger space occurrences ledger ∧
        totalCounts ledger = expected := by
  constructor
  · intro computed
    cases ledgerResult : resolveLedger space occurrences with
    | none => simp [resolvedTotal?, ledgerResult] at computed
    | some ledger =>
        have totalEquality : totalCounts ledger = expected := by
          simpa [resolvedTotal?, ledgerResult] using computed
        exact ⟨ledger,
          ResolvesLedger.of_resolveLedger_eq_some
            space occurrences ledger ledgerResult,
          totalEquality⟩
  · rintro ⟨ledger, resolved, totalEquality⟩
    simp [resolvedTotal?, resolved.resolveLedger_eq_some, totalEquality]

/-- A result claim exposes both the revisioned evidence state and the expected
exact sufficient statistic. -/
structure EvidenceClaim (StoreId Revision : Type) where
  space : RevisionedEvidenceSpace StoreId Revision
  expected : CountPair

/-- Untrusted replay evidence is an ordered list of exact occurrence IDs. -/
structure EvidenceCertificate (StoreId Revision : Type) where
  occurrences : List (StoreOccurrenceId StoreId Revision)

/-- Independent meaning: some duplicate-free ordered occurrence list resolves
relationally to the claimed aggregate. -/
def EvidenceMeaning (claim : EvidenceClaim StoreId Revision) : Prop :=
  ∃ occurrences ledger,
    occurrences.Nodup ∧
    ResolvesLedger claim.space occurrences ledger ∧
    totalCounts ledger = claim.expected

/-- Executable trust-boundary replay.  It independently resolves revisions and
logical indices, rejects occurrence reuse, and recomputes both counts. -/
def evidenceChecker :
    Checker (EvidenceClaim StoreId Revision)
      (EvidenceCertificate StoreId Revision) where
  check := fun claim certificate =>
    decide certificate.occurrences.Nodup &&
      decide
        (resolvedTotal? claim.space certificate.occurrences =
          some claim.expected)

theorem evidenceChecker_sound :
    (evidenceChecker (StoreId := StoreId) (Revision := Revision)).Sound
      (EvidenceMeaning (StoreId := StoreId) (Revision := Revision)) := by
  intro claim certificate accepted
  have checked : certificate.occurrences.Nodup ∧
      resolvedTotal? claim.space certificate.occurrences =
        some claim.expected := by
    simpa [evidenceChecker] using accepted
  obtain ⟨ledger, resolved, totalEquality⟩ :=
    (resolvedTotal_eq_some_iff claim.space certificate.occurrences
      claim.expected).mp checked.2
  exact ⟨certificate.occurrences, ledger, checked.1, resolved, totalEquality⟩

theorem evidenceChecker_complete :
    (evidenceChecker (StoreId := StoreId) (Revision := Revision)).CertificateComplete
      (EvidenceMeaning (StoreId := StoreId) (Revision := Revision)) := by
  intro claim meaningful
  obtain ⟨occurrences, ledger, nodup, resolved, totalEquality⟩ := meaningful
  refine ⟨⟨occurrences⟩, ?_⟩
  have computed : resolvedTotal? claim.space occurrences =
      some claim.expected :=
    (resolvedTotal_eq_some_iff claim.space occurrences claim.expected).mpr
      ⟨ledger, resolved, totalEquality⟩
  simp [evidenceChecker, nodup, computed]

/-- The revision-pinned count checker is an exact NIK-style authority for its
independently stated finite meaning. -/
theorem evidenceChecker_authority :
    (evidenceChecker (StoreId := StoreId) (Revision := Revision)).Authority
      (EvidenceMeaning (StoreId := StoreId) (Revision := Revision)) where
  sound := evidenceChecker_sound
  complete := evidenceChecker_complete

/-- Accepted evidence exposes a finite dependency set whose captured
revisions are all current. -/
theorem accepted_dependencies_valid
    {claim : EvidenceClaim StoreId Revision}
    {certificate : EvidenceCertificate StoreId Revision}
    (accepted : evidenceChecker.check claim certificate = true) :
    RevisionDependencySet.ValidAt claim.space.revisionEnvironment
      certificate.occurrences.toFinset := by
  have checked : certificate.occurrences.Nodup ∧
      resolvedTotal? claim.space certificate.occurrences =
        some claim.expected := by
    simpa [evidenceChecker] using accepted
  obtain ⟨ledger, resolved, _⟩ :=
    (resolvedTotal_eq_some_iff claim.space certificate.occurrences
      claim.expected).mp checked.2
  exact resolved.dependencies_valid

/-! ## Exact invalidation and support-local reuse -/

/-- Updating a store not named by a certificate leaves its complete ordered
resolution unchanged. -/
theorem resolveLedger_updateStore_of_all_ne
    (space : RevisionedEvidenceSpace StoreId Revision)
    (occurrences : List (StoreOccurrenceId StoreId Revision))
    (store : StoreId) (nextRevision : Revision)
    (nextEntries : List CountPair)
    (outside : ∀ occurrence ∈ occurrences,
      occurrence.read.storeId ≠ store) :
    resolveLedger (space.updateStore store nextRevision nextEntries)
        occurrences =
      resolveLedger space occurrences := by
  induction occurrences with
  | nil => rfl
  | cons occurrence rest inductionHypothesis =>
      have headOutside : occurrence.read.storeId ≠ store :=
        outside occurrence (by simp)
      have tailOutside : ∀ item ∈ rest, item.read.storeId ≠ store := by
        intro item member
        exact outside item (by simp [member])
      simp [resolveLedger, headOutside,
        inductionHypothesis tailOutside]

/-- A revision and payload update outside the exact occurrence support does
not alter acceptance. -/
theorem checker_updateStore_outside_support
    (claim : EvidenceClaim StoreId Revision)
    (certificate : EvidenceCertificate StoreId Revision)
    (store : StoreId) (nextRevision : Revision)
    (nextEntries : List CountPair)
    (outside : ∀ occurrence ∈ certificate.occurrences,
      occurrence.read.storeId ≠ store) :
    evidenceChecker.check
        ⟨claim.space.updateStore store nextRevision nextEntries,
          claim.expected⟩ certificate =
      evidenceChecker.check claim certificate := by
  simp [evidenceChecker, resolvedTotal?,
    resolveLedger_updateStore_of_all_ne claim.space certificate.occurrences
      store nextRevision nextEntries outside]

/-- Advancing a consulted store rejects the old certificate, even if the
replacement store contains equal count payloads. -/
theorem checker_rejects_consulted_revision_change
    (claim : EvidenceClaim StoreId Revision)
    (certificate : EvidenceCertificate StoreId Revision)
    (occurrence : StoreOccurrenceId StoreId Revision)
    (member : occurrence ∈ certificate.occurrences)
    (nextRevision : Revision) (nextEntries : List CountPair)
    (changed : nextRevision ≠ occurrence.read.revision) :
    evidenceChecker.check
        ⟨claim.space.updateStore occurrence.read.storeId nextRevision
          nextEntries, claim.expected⟩ certificate = false := by
  have unresolved :
      (claim.space.updateStore occurrence.read.storeId nextRevision
        nextEntries).resolve occurrence = none :=
    claim.space.resolve_updateStore_same_stale occurrence nextRevision
      nextEntries changed
  have ledgerRejected := resolveLedger_eq_none_of_mem_resolve_eq_none
    (claim.space.updateStore occurrence.read.storeId nextRevision nextEntries)
    certificate.occurrences member unresolved
  simp [evidenceChecker, resolvedTotal?, ledgerRejected]

/-! ## Connection to guarded PLN revision -/

/-- Convert a resolved occurrence ledger into singleton-stamped count-pair
packets.  Singleton stamps expose exactly which occurrence contributed each
payload. -/
def singletonStampedBatch
    (ledger : List (StoreOccurrenceId StoreId Revision × CountPair)) :
    List (Finset (StoreOccurrenceId StoreId Revision) × CountPair) :=
  ledger.map fun item => ({item.1}, item.2)

omit [DecidableEq StoreId] [DecidableEq Revision] in
private theorem singleton_count_packets_pairwise_of_occurrence_nodup
    (ledger : List (StoreOccurrenceId StoreId Revision × CountPair))
    (nodup : (ledger.map Prod.fst).Nodup) :
    (countPairStampedBatch
      (singletonStampedBatch ledger)).Pairwise
        StampedBinaryEvidence.StampDisjoint := by
  induction ledger with
  | nil => simp [singletonStampedBatch, countPairStampedBatch]
  | cons head tail inductionHypothesis =>
      have nodupCons : (head.1 :: tail.map Prod.fst).Nodup := by
        simpa using nodup
      rw [List.nodup_cons] at nodupCons
      change List.Pairwise StampedBinaryEvidence.StampDisjoint
        (countPairStampedEvidence {head.1} head.2 ::
          countPairStampedBatch (singletonStampedBatch tail))
      rw [List.pairwise_cons]
      constructor
      · intro packet packetMember
        obtain ⟨raw, rawMember, packetEquality⟩ :=
          List.mem_map.mp packetMember
        obtain ⟨item, itemMember, rawEquality⟩ :=
          List.mem_map.mp rawMember
        cases rawEquality
        cases packetEquality
        have different : head.1 ≠ item.1 := by
          intro equalOccurrence
          apply nodupCons.1
          exact List.mem_map.mpr ⟨item, itemMember, equalOccurrence.symm⟩
        simp [countPairStampedEvidence,
          StampedBinaryEvidence.StampDisjoint,
          Mettapedia.Evidence.SourceScoped.Independent,
          Mettapedia.Evidence.SourceScope.Independent, different]
      · exact inductionHypothesis nodupCons.2

omit [DecidableEq StoreId] [DecidableEq Revision] in
@[simp] theorem countPairLedger_singletonStampedBatch
    (ledger : List (StoreOccurrenceId StoreId Revision × CountPair)) :
    countPairLedger (singletonStampedBatch ledger) = ledger.map Prod.snd := by
  simp [countPairLedger, singletonStampedBatch, List.map_map,
    Function.comp_def]

/-- Every accepted Space certificate feeds the existing guarded additive PLN
revision through singleton occurrence stamps. -/
theorem accepted_implies_guarded_pln_revision
    {claim : EvidenceClaim StoreId Revision}
    {certificate : EvidenceCertificate StoreId Revision}
    (accepted : evidenceChecker.check claim certificate = true) :
    ∃ ledger,
      ResolvesLedger claim.space certificate.occurrences ledger ∧
      totalCounts ledger = claim.expected ∧
      guardedRevisionManyEvidence
          (countPairStampedBatch (singletonStampedBatch ledger)) =
        some
          (revisionMany
            ((countPairLedger (singletonStampedBatch ledger)).map
              countPairEvidence)) := by
  have checked : certificate.occurrences.Nodup ∧
      resolvedTotal? claim.space certificate.occurrences =
        some claim.expected := by
    simpa [evidenceChecker] using accepted
  obtain ⟨ledger, resolved, totalEquality⟩ :=
    (resolvedTotal_eq_some_iff claim.space certificate.occurrences
      claim.expected).mp checked.2
  have ledgerNodup : (ledger.map Prod.fst).Nodup := by
    rw [resolved.occurrence_map]
    exact checked.1
  have pairwise :=
    singleton_count_packets_pairwise_of_occurrence_nodup ledger ledgerNodup
  refine ⟨ledger, resolved, totalEquality, ?_⟩
  exact
    (guardedRevisionManyCountPairEvidence_eq_some_iff_pairwise
      (Stamp := StoreOccurrenceId StoreId Revision)
      (singletonStampedBatch ledger)).mpr pairwise

/-- The accepted exact occurrence batch also receives the existing
Beta-Bernoulli sufficient-statistic readout. -/
theorem accepted_implies_beta_parameters
    (prior : ℝ) (priorPositive : 0 < prior)
    {claim : EvidenceClaim StoreId Revision}
    {certificate : EvidenceCertificate StoreId Revision}
    (accepted : evidenceChecker.check claim certificate = true) :
    ∃ ledger,
      ResolvesLedger claim.space certificate.occurrences ledger ∧
      (batchEvidenceBetaParams prior priorPositive
          (countPairLedger (singletonStampedBatch ledger))).alpha =
        prior + claim.expected.1 ∧
      (batchEvidenceBetaParams prior priorPositive
          (countPairLedger (singletonStampedBatch ledger))).beta =
        prior + claim.expected.2 := by
  have checked : certificate.occurrences.Nodup ∧
      resolvedTotal? claim.space certificate.occurrences =
        some claim.expected := by
    simpa [evidenceChecker] using accepted
  obtain ⟨ledger, resolved, totalEquality⟩ :=
    (resolvedTotal_eq_some_iff claim.space certificate.occurrences
      claim.expected).mp checked.2
  refine ⟨ledger, resolved, ?_, ?_⟩
  · rw [batchEvidenceBetaParams_alpha,
      countPairLedger_singletonStampedBatch]
    have positiveEquality :
        (ledger.map fun item => item.2.1).sum = claim.expected.1 := by
      simpa [totalCounts] using congrArg Prod.fst totalEquality
    simpa [List.map_map, Function.comp_def] using
      congrArg (fun count : Nat => prior + (count : ℝ)) positiveEquality
  · rw [batchEvidenceBetaParams_beta,
      countPairLedger_singletonStampedBatch]
    have negativeEquality :
        (ledger.map fun item => item.2.2).sum = claim.expected.2 := by
      simpa [totalCounts] using congrArg Prod.snd totalEquality
    simpa [List.map_map, Function.comp_def] using
      congrArg (fun count : Nat => prior + (count : ℝ)) negativeEquality

/-! ## Proof-relevant rho execution receipts -/

open Mettapedia.TypeTheory.ProofRelevantRouteFamilyBridge
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.TypedCommunicationProtocol

/-- A checked evidence calculation paired with the exact typed rho route that
carried it.  Store revisions and rho route revisions remain separate fields. -/
structure ExecutionReceipt (StoreId Revision : Type)
    [DecidableEq StoreId] [DecidableEq Revision] where
  claim : EvidenceClaim StoreId Revision
  certificate : EvidenceCertificate StoreId Revision
  accepted : evidenceChecker.check claim certificate = true
  route : Rho.CommunicationPath
    closedNilCommData.source closedNilCommData.target

/-- Extensional result observation keeps the exact PLN sufficient statistic
and rho endpoints while forgetting the execution route. -/
def extensionalReadout
    (receipt : ExecutionReceipt StoreId Revision) :
    CountPair × (Rho.CommunicationObject × Rho.CommunicationObject) :=
  (receipt.claim.expected,
    (closedNilCommData.source, closedNilCommData.target))

/-! ## Concrete positive and negative canaries -/

namespace Canary

inductive Store where
  | observations
  | model
  | unrelated
deriving DecidableEq

def space : RevisionedEvidenceSpace Store Nat where
  currentRevision
    | .observations => 7
    | .model => 3
    | .unrelated => 99
  entries
    | .observations => [(2, 0), (0, 1)]
    | .model => [(5, 4)]
    | .unrelated => []

def positiveOccurrence : StoreOccurrenceId Store Nat :=
  space.occurrenceId .observations 0

def negativeOccurrence : StoreOccurrenceId Store Nat :=
  space.occurrenceId .observations 1

def goodCertificate : EvidenceCertificate Store Nat :=
  ⟨[positiveOccurrence, negativeOccurrence]⟩

def goodClaim : EvidenceClaim Store Nat :=
  ⟨space, (2, 1)⟩

theorem goodAccepted :
    evidenceChecker.check goodClaim goodCertificate = true := by
  decide

/-- Changing an unrelated store preserves the accepted result. -/
theorem unrelatedRevisionAccepted :
    evidenceChecker.check
      ⟨space.updateStore .unrelated 100 [(100, 100)], (2, 1)⟩
      goodCertificate = true := by
  change evidenceChecker.check
    ⟨goodClaim.space.updateStore .unrelated 100 [(100, 100)],
      goodClaim.expected⟩ goodCertificate = true
  rw [checker_updateStore_outside_support goodClaim goodCertificate
    .unrelated 100 [(100, 100)]]
  · exact goodAccepted
  · intro occurrence member
    simp [goodCertificate, positiveOccurrence, negativeOccurrence,
      RevisionedEvidenceSpace.occurrenceId,
      RevisionedEvidenceSpace.view, space] at member ⊢
    rcases member with rfl | rfl <;> decide

/-- Advancing the consulted observation store invalidates the old exact
occurrence certificate even when the replacement payloads are byte-for-byte
equal. -/
theorem consultedRevisionRejected :
    evidenceChecker.check
      ⟨space.updateStore .observations 8 [(2, 0), (0, 1)], (2, 1)⟩
      goodCertificate = false := by
  apply checker_rejects_consulted_revision_change goodClaim goodCertificate
    positiveOccurrence
  · simp [goodCertificate]
  · decide

/-- Reusing one exact occurrence is rejected before additive PLN revision. -/
def duplicateCertificate : EvidenceCertificate Store Nat :=
  ⟨[positiveOccurrence, positiveOccurrence]⟩

theorem duplicateRejected :
    evidenceChecker.check goodClaim duplicateCertificate = false := by
  decide

/-- A current revision does not make an out-of-range logical position real. -/
def forgedOccurrence : StoreOccurrenceId Store Nat :=
  space.occurrenceId .observations 2

def forgedCertificate : EvidenceCertificate Store Nat :=
  ⟨[positiveOccurrence, forgedOccurrence]⟩

theorem forgedOccurrenceRejected :
    evidenceChecker.check goodClaim forgedCertificate = false := by
  decide

noncomputable def zeroRouteReceipt : ExecutionReceipt Store Nat where
  claim := goodClaim
  certificate := goodCertificate
  accepted := goodAccepted
  route := Rho.zeroRevisionPath

noncomputable def oneRouteReceipt : ExecutionReceipt Store Nat where
  claim := goodClaim
  certificate := goodCertificate
  accepted := goodAccepted
  route := Rho.oneRevisionPath

/-- The same Space evidence and PLN result can travel through distinct rho
execution histories. -/
theorem routeReceiptsDistinct : zeroRouteReceipt ≠ oneRouteReceipt := by
  intro equalReceipts
  exact Rho.zeroRevisionPath_ne_oneRevisionPath
    (congrArg ExecutionReceipt.route equalReceipts)

@[simp] theorem routeReceiptReadoutsEqual :
    extensionalReadout zeroRouteReceipt =
      extensionalReadout oneRouteReceipt := rfl

/-- Result-and-endpoint observation cannot reconstruct the proof-relevant rho
route. -/
theorem extensionalReadout_not_injective :
    ¬ Function.Injective
      (extensionalReadout : ExecutionReceipt Store Nat →
        CountPair × (Rho.CommunicationObject × Rho.CommunicationObject)) := by
  intro injective
  exact routeReceiptsDistinct (injective routeReceiptReadoutsEqual)

end Canary

#print axioms evidenceChecker_authority
#print axioms accepted_dependencies_valid
#print axioms checker_updateStore_outside_support
#print axioms checker_rejects_consulted_revision_change
#print axioms accepted_implies_guarded_pln_revision
#print axioms accepted_implies_beta_parameters
#print axioms Canary.extensionalReadout_not_injective

end Mettapedia.PLN.Bridges.GSLT.RevisionPinnedEvidenceExecution
