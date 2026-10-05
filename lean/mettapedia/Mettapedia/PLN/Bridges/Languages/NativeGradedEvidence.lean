import Mettapedia.PLN.Bridges.GSLT.EvidenceResolutionAlgebra
import Mettapedia.PLN.Bridges.GSLT.RevisionPinnedEvidenceExecution
import Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedControls

/-!
# Exact evidence grades on native MeTTa continuations

The natural-count profile recognizes actual native `evidence` values. Its
componentwise tensor and alternative addition agree with the existing PLN
binary-evidence algebra. The comparison preserves complete continuations,
physical contributions and unsettled readouts at every finite cut. Declared
positive-evidence admission commutes with that representation change; shared
graded identities retain their argument choices and duplicate occurrences.

Revision-pinned observation certificates are decoded and checked against the
existing relational evidence semantics. Their count readouts and guarded PLN
revision reuse that theory. This comparison does not refine the C space
primitives or their revision ranges.

Count addition alone grants no authority to revise shared sources. This
profile does not identify PLN deduction or abduction with tensor composition,
and does not establish a refinement of the C evaluator or a dependent typing
judgment for weighted contributions.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Bridges.Languages.NativeGradedEvidence

open Mettapedia.Machines.BranchLocalNeed
open NeedReference
open Mettapedia.Languages.MeTTa.PrimeCandidates
open NativeEquationNeed NativeCandidateGrades NativeGradeControls
open NativeWeightedHandler NativeWeightedControls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.GSLT.Dynamics
open Mettapedia.PLN.Evidence (BinEvNat)
open Mettapedia.PLN.Bridges.GSLT.EvidenceResolutionAlgebra
open Mettapedia.PLN.Evidence.EvidenceQuantale (BinaryEvidence)

/-- Negative counts or other values remain outside the declared natural profile. -/
def countCoefficient : Outcome → Option BinEvNat
  | .value (.expression [.symbol "evidence", .grounded (.int positive),
      .grounded (.int negative)]) =>
      if 0 ≤ positive ∧ 0 ≤ negative then
        some ⟨positive.toNat, negative.toNat⟩ else none
  | _ => none

noncomputable def formalCoefficient (outcome : Outcome) :=
  (countCoefficient outcome).map countSemiringHom

/-- The actual nested native adapter agrees at every cut, including its worlds,
caller stack, unsettled grades, order and duplicate physical contributions. -/
theorem native_count_refinement (program : Program) (annotation : Row → Option Atom)
    (fuel : Nat) (before : NestedWork) :
    WeightedBranchingResumption.contributions
      (nestedSource program annotation formalCoefficient) fuel before =
    WeightedResumption.mapCoefficients countSemiringHom
      (WeightedBranchingResumption.contributions
        (nestedSource program annotation countCoefficient) fuel before) :=
  native_nested_change_coefficients countSemiringHom.toMonoidHom
    program annotation countCoefficient fuel before

/-- Authored coefficient/predicate phase changes use the same comparison. -/
theorem authored_count_refinement (program : Program)
    (annotation : Row → Option AuthoredClause) (fuel : Nat) (before : AuthoredWork) :
    WeightedBranchingResumption.contributions
      (authoredSource program annotation formalCoefficient) fuel before =
    WeightedResumption.mapCoefficients countSemiringHom
      (WeightedBranchingResumption.contributions
        (authoredSource program annotation countCoefficient) fuel before) :=
  native_authored_change_coefficients countSemiringHom.toMonoidHom
    program annotation countCoefficient fuel before

/-- Alternative addition needs the separate additive law, supplied here by the
existing count-to-evidence semiring homomorphism. -/
theorem count_total_refinement {Answer : Type}
    (contributions : WeightedResumption.Contributions Answer BinEvNat) :
    WeightedResumption.total (WeightedResumption.mapCoefficients countSemiringHom contributions) =
      countSemiringHom (WeightedResumption.total contributions) :=
  WeightedResumption.total_mapCoefficients countSemiringHom.toAddMonoidHom contributions

def evidenceLiteral (positive negative : Int) : Atom :=
  .expression [.symbol "evidence", integer positive, integer negative]

def tensorRun := orderedIdentityWithGrades
  (evidenceLiteral 2 3) (evidenceLiteral 5 7) countCoefficient

theorem literal_tensor_uses_existing_evidence_coordinates :
    completedValues tensorRun = [(integer 7, (⟨10, 21⟩ : BinEvNat))] := by
  decide +kernel

theorem literal_negative_counts_are_unsettled :
    countCoefficient (.value (evidenceLiteral (-1) 2)) = none ∧
    completedValues (orderedIdentityWithGrades
      (evidenceLiteral (-1) 2) (evidenceLiteral 5 7) countCoefficient) = [] ∧
    (WeightedBranchingResumption.nestedObligations (orderedIdentityWithGrades
      (evidenceLiteral (-1) 2) (evidenceLiteral 5 7) countCoefficient)).length = 1 := by
  decide +kernel

/-- Opposite nonzero polarities multiply to zero; attachment retains the answer
occurrence rather than silently adopting nonzero support as an admission law. -/
theorem literal_tensor_zero_retains_occurrence :
    countCoefficient (.value (evidenceLiteral 1 0)) ≠ some 0 ∧
    countCoefficient (.value (evidenceLiteral 0 1)) ≠ some 0 ∧
    completedValues (orderedIdentityWithGrades
      (evidenceLiteral 1 0) (evidenceLiteral 0 1) countCoefficient) = [(integer 7, 0)] := by
  decide +kernel

def duplicateEvidenceProgram : Program :=
  orderedIdentityProgram ++ [⟨"outer", ["x"], .var "x"⟩]

def duplicateCountRun := WeightedBranchingResumption.contributions
  (nestedSource duplicateEvidenceProgram
    (fun row => if 4 ≤ row.index then some (evidenceLiteral 2 3) else none)
    countCoefficient) 300
  (.inl (WorkOccurrence.root (initial (call "outer" [call "id" [integer 7]]))))

/-- Equal equations retain two contributions. The additive observation doubles
the counts, while the original occurrence list remains available. -/
theorem duplicate_counts_preserve_routes_and_add :
    completedValues duplicateCountRun =
      [(integer 7, (⟨2, 3⟩ : BinEvNat)), (integer 7, (⟨2, 3⟩ : BinEvNat))] ∧
    duplicateCountRun.length = 2 ∧
    WeightedResumption.total (completedValues duplicateCountRun) = (⟨4, 6⟩ : BinEvNat) := by
  decide +kernel

/-- Positive evidence supplies the existing classical support discipline.
A nonzero pair alone does not satisfy its joint-condition law. -/
def countAdmission (value : BinEvNat) : Bool := decide (value.pos ≠ 0)
noncomputable def formalAdmission (value : BinaryEvidence) : Bool := by
  classical
  exact decide (evidenceSupport.Enabled value)

/-- The executable test reads exactly the support declared by the existing
PLN algebra after the count-to-formal-evidence conversion. -/
theorem formal_count_admission (value : BinEvNat) :
    formalAdmission (countSemiringHom value) = countAdmission value := by
  classical
  simp [formalAdmission, evidenceSupport_enabled_iff, countAdmission,
    countSemiringHom, Mettapedia.PLN.Evidence.EvidentialLedger.BinEvNat.toBinaryEvidence]

/-- Admission commutes at every finite cut, preserving native worlds, grade
frames, unsettled comparisons, order and physical duplicate occurrences. -/
theorem native_admitted_count_refinement (program : Program) (annotation : Row → Option Atom)
    (fuel : Nat) (before : NestedWork) :
    WeightedBranchingResumption.contributions
      (nestedAdmittedSource program annotation formalCoefficient formalAdmission) fuel before =
    WeightedResumption.mapCoefficients countSemiringHom
      (WeightedBranchingResumption.contributions
        (nestedAdmittedSource program annotation countCoefficient countAdmission) fuel before) :=
  native_nested_admitted_change_coefficients countSemiringHom.toMonoidHom
    program annotation countCoefficient countAdmission formalAdmission formal_count_admission fuel before

theorem count_admission_zero_and_one :
    countAdmission 0 = false ∧ countAdmission 1 = true := by decide +kernel

theorem count_admission_tensor (left right : BinEvNat) :
    countAdmission (left * right) = (countAdmission left && countAdmission right) := by
  by_cases hl : left.pos = 0
  · simp [countAdmission, hl]
  · by_cases hr : right.pos = 0
    · simp [countAdmission, hr]
    · simp [countAdmission, hl, hr, Nat.mul_ne_zero hl hr]

theorem count_admission_alternative (left right : BinEvNat)
    (accepted : countAdmission left = true) : countAdmission (left + right) = true := by
  have positive : left.pos ≠ 0 := by simpa [countAdmission] using accepted
  change decide (left.pos + right.pos ≠ 0) = true
  simp [positive]

def sharedCountAnnotation (row : Row) : Option Atom :=
  if row.index < 2 then some (evidenceLiteral 3 1)
  else if row.index = 2 then some (evidenceLiteral 7 1)
  else if row.index = 3 then
    some (.expression [.symbol "evidence", .var "x", integer 1])
  else none

def sharedCountRun (guarded : Bool) (fuel : Nat) :=
  WeightedBranchingResumption.contributions
    (nestedAdmittedSource sharedIdentityProgram sharedCountAnnotation countCoefficient
      (fun value => !guarded || countAdmission value)) fuel
    (.inl (WorkOccurrence.root (initial sharedIdentityTerm)))

/-- The grade forces each lazy coin occurrence once. The identity returns
that same cell, and the caller reuses it twice. Equal rows stay distinct. -/
theorem graded_evidence_identity_shares_choice :
    completedValues (sharedCountRun true 300) =
      [(call "Pair" [integer 2, integer 2], (⟨6, 1⟩ : BinEvNat)),
       (call "Pair" [integer 2, integer 2], (⟨6, 1⟩ : BinEvNat)),
       (call "Pair" [integer 5, integer 5], (⟨35, 1⟩ : BinEvNat))] := by
  decide +kernel

theorem graded_evidence_identity_no_mixed_pair :
    ∀ coefficient, (call "Pair" [integer 2, integer 5], coefficient) ∉
      completedValues (sharedCountRun true 300) := by
  intro coefficient
  rw [graded_evidence_identity_shares_choice]
  simp [call, integer]

def polarityRun (admit : BinEvNat → Bool) :=
  WeightedBranchingResumption.contributions
    (nestedAdmittedSource orderedIdentityProgram
      (fun row => if row.index = 2 then some (evidenceLiteral 1 0)
        else if row.index = 4 then some (evidenceLiteral 0 1) else none)
      countCoefficient admit) 300
    (.inl (WorkOccurrence.root (initial (call "outer" [call "id" [integer 7]]))))

/-- Pausing and resuming the actual admitted evidence program preserves the
whole packet, including every body, lazy cell, parent frame and earlier factor. -/
theorem shared_count_resume_exact (first second : Nat) :
    sharedCountRun true (first + second) =
      WeightedResumption.sequence (sharedCountRun true first) (fun leaf => match leaf with
        | .inl answer => [(.inl answer, 1)]
        | .inr pending => WeightedBranchingResumption.contributions
            (nestedAdmittedSource sharedIdentityProgram sharedCountAnnotation countCoefficient
              (fun value => !true || countAdmission value)) second pending) :=
  by
    unfold sharedCountRun
    convert WeightedBranchingResumption.contributions_add (V := BinEvNat)
      (nestedAdmittedSource sharedIdentityProgram sharedCountAnnotation countCoefficient
        (fun value => !true || countAdmission value)) first second
      (.inl (WorkOccurrence.root (initial sharedIdentityTerm))) using 1
    congr 1
    funext leaf
    cases leaf <;> rfl

/-- At a nontrivial cut all three physical coin choices still belong to the
shared continuation; later admission does not reconstruct the query. -/
theorem shared_count_attachment_and_guard_agree :
    completedValues (sharedCountRun false 300) = completedValues (sharedCountRun true 300) ∧
    (sharedCountRun true 30).length = 3 ∧
    completedValues (sharedCountRun true 30) = [] := by
  decide +kernel

/-- Naive nonzero admission accepts both opposite polarities and produces
a zero-weight answer. Positive support refuses the counter-only outer clause. -/
theorem nonzero_packet_admission_breaks_tensor_support :
    completedValues (polarityRun (fun value => value != 0)) = [(integer 7, 0)] ∧
    polarityRun countAdmission = [] := by
  decide +kernel

def unsettledCountRun := WeightedBranchingResumption.contributions
  (nestedAdmittedSource orderedIdentityProgram
    (fun row => if row.index = 2 then some (evidenceLiteral (-1) 2)
      else if row.index = 4 then some (.var "x") else none)
    countCoefficient countAdmission) 300
  (.inl (WorkOccurrence.root (initial (call "outer" [call "id" [integer 7]]))))

/-- An out-of-profile coefficient is an owned unsettled readout. It is neither
a false guard nor a completed answer; the outer grade and body remain attached. -/
theorem unsettled_count_keeps_body_and_parent :
    completedValues unsettledCountRun = [] ∧
    unsettledCountRun.map (fun leaf => match leaf.1 with
      | .inl (.inr (body, score, parents)) =>
          some (score.origin.row.index,
            parents.map (fun (parent : Score) => parent.origin.row.index), isHalted body.state)
      | _ => none) = [some (2, [4], false)] := by
  decide +kernel

/-- Total evidence mass is a useful observation, but it cannot replace the
coefficient during tensor composition. -/
theorem count_mass_is_not_a_tensor_readout :
    (BinEvNat.ess ((⟨2, 3⟩ : BinEvNat) * ⟨5, 7⟩)) = 31 ∧
    (BinEvNat.ess (⟨2, 3⟩ : BinEvNat)) * (BinEvNat.ess (⟨5, 7⟩ : BinEvNat)) = 60 := by
  decide +kernel

/-! ## Revision-pinned native observation certificates -/

open Mettapedia.Machines
open Mettapedia.PLN.Bridges.GSLT.RevisionPinnedEvidenceExecution

def countPairCoefficient (counts : CountPair) : BinEvNat := ⟨counts.1, counts.2⟩

def countPairAtom (counts : CountPair) : Atom :=
  evidenceLiteral counts.1 counts.2

theorem countPairAtom_decodes (counts : CountPair) :
    countCoefficient (.value (countPairAtom counts)) = some (countPairCoefficient counts) := by
  simp [countPairAtom, countCoefficient, evidenceLiteral, integer, countPairCoefficient]

def countAtomEntries {StoreId Revision : Type}
    (space : RevisionedEvidenceSpace StoreId Revision) (store : StoreId) : List Atom :=
  (space.entries store).map countPairAtom

/-- Resolve an observation by its revision and ordered position, then decode
its actual native count payload. Unsupported payloads remain unresolved. -/
def nativeCountAt {StoreId Revision : Type} [DecidableEq Revision]
    (current : StoreId → Revision) (entries : StoreId → List Atom)
    (occurrence : StoreOccurrenceId StoreId Revision) : Option BinEvNat := do
  if occurrence.read.revision = current occurrence.read.storeId then
    let value ← (entries occurrence.read.storeId)[occurrence.logicalIndex]?
    countCoefficient (.value value)
  else none

theorem native_count_at_encoded {StoreId Revision : Type}
    [DecidableEq StoreId] [DecidableEq Revision]
    (space : RevisionedEvidenceSpace StoreId Revision)
    (occurrence : StoreOccurrenceId StoreId Revision) :
    nativeCountAt space.currentRevision (countAtomEntries space) occurrence =
      (space.resolve occurrence).map countPairCoefficient := by
  unfold nativeCountAt countAtomEntries RevisionedEvidenceSpace.resolve
    RevisionedEvidenceSpace.view RevisionedStoreView.resolve
  simp only [true_and]
  by_cases current : occurrence.read.revision = space.currentRevision occurrence.read.storeId
  · simp only [if_pos current]
    rw [List.getElem?_map]
    cases found : (space.entries occurrence.read.storeId)[occurrence.logicalIndex]? with
    | none => rfl
    | some counts => simpa using countPairAtom_decodes counts
  · simp only [if_neg current, Option.map_none]

/-- Independently fold the decoded native payloads in certificate order. -/
def nativeRevisionTotal {StoreId Revision : Type} [DecidableEq Revision]
    (current : StoreId → Revision) (entries : StoreId → List Atom) :
    List (StoreOccurrenceId StoreId Revision) → Option BinEvNat
  | [] => some 0
  | occurrence :: rest => do
      let head ← nativeCountAt current entries occurrence
      let tail ← nativeRevisionTotal current entries rest
      pure (head + tail)

theorem native_revision_total_encoded {StoreId Revision : Type}
    [DecidableEq StoreId] [DecidableEq Revision]
    (space : RevisionedEvidenceSpace StoreId Revision)
    (occurrences : List (StoreOccurrenceId StoreId Revision)) :
    nativeRevisionTotal space.currentRevision (countAtomEntries space) occurrences =
      (resolvedTotal? space occurrences).map countPairCoefficient := by
  induction occurrences with
  | nil => rfl
  | cons occurrence rest ih =>
      simp only [nativeRevisionTotal, native_count_at_encoded, ih, resolvedTotal?, resolveLedger]
      cases head : space.resolve occurrence with
      | none => rfl
      | some counts =>
          cases tail : resolveLedger space rest with
          | none => rfl
          | some ledger =>
              simp only [Option.map_some, Option.pure_def, totalCounts, countPairCoefficient]
              rfl


/-- Closed observation certificates forbid reused identities and require the
claimed count total. Zero counts do not constitute an invalid certificate. -/
def nativeRevisionCheck {StoreId Revision : Type}
    [DecidableEq StoreId] [DecidableEq Revision]
    (current : StoreId → Revision) (entries : StoreId → List Atom)
    (occurrences : List (StoreOccurrenceId StoreId Revision)) (expected : CountPair) : Bool :=
  decide occurrences.Nodup &&
    decide (nativeRevisionTotal current entries occurrences = some (countPairCoefficient expected))

/-- The native decoder and fold agree with the existing revision checker on
encoded count stores; the target is not defined as the image of this fold. -/
theorem native_revision_check_encoded {StoreId Revision : Type}
    [DecidableEq StoreId] [DecidableEq Revision]
    (space : RevisionedEvidenceSpace StoreId Revision)
    (occurrences : List (StoreOccurrenceId StoreId Revision)) (expected : CountPair) :
    nativeRevisionCheck space.currentRevision (countAtomEntries space) occurrences expected =
      evidenceChecker.check ⟨space, expected⟩ ⟨occurrences⟩ := by
  unfold nativeRevisionCheck
  rw [native_revision_total_encoded]
  cases found : resolvedTotal? space occurrences with
  | none => simp [evidenceChecker, found]
  | some counts => simp [evidenceChecker, found, countPairCoefficient, Prod.ext_iff]

/-- Acceptance accounts for this exact ordered certificate, not merely for
some other witness of the same aggregate. -/
theorem native_revision_check_iff {StoreId Revision : Type}
    [DecidableEq StoreId] [DecidableEq Revision]
    (space : RevisionedEvidenceSpace StoreId Revision)
    (occurrences : List (StoreOccurrenceId StoreId Revision)) (expected : CountPair) :
    nativeRevisionCheck space.currentRevision (countAtomEntries space) occurrences expected = true ↔
      occurrences.Nodup ∧ ∃ ledger,
        ResolvesLedger space occurrences ledger ∧ totalCounts ledger = expected := by
  rw [native_revision_check_encoded]
  simp only [evidenceChecker, Bool.and_eq_true, decide_eq_true_eq]
  rw [resolvedTotal_eq_some_iff]

/-- Every independently meaningful finite count claim has an accepted native
certificate on its encoded store. This does not enumerate all query answers. -/
theorem native_revision_certificate_complete {StoreId Revision : Type}
    [DecidableEq StoreId] [DecidableEq Revision]
    (space : RevisionedEvidenceSpace StoreId Revision) (expected : CountPair)
    (meaningful : EvidenceMeaning ⟨space, expected⟩) :
    ∃ occurrences, nativeRevisionCheck space.currentRevision (countAtomEntries space)
      occurrences expected = true := by
  obtain ⟨occurrences, ledger, nodup, resolved, total⟩ := meaningful
  exact ⟨occurrences, (native_revision_check_iff space occurrences expected).mpr
    ⟨nodup, ledger, resolved, total⟩⟩


theorem native_revision_check_sound {StoreId Revision : Type}
    [DecidableEq StoreId] [DecidableEq Revision]
    (space : RevisionedEvidenceSpace StoreId Revision)
    (occurrences : List (StoreOccurrenceId StoreId Revision)) (expected : CountPair)
    (accepted : nativeRevisionCheck space.currentRevision (countAtomEntries space)
      occurrences expected = true) : EvidenceMeaning ⟨space, expected⟩ := by
  apply evidenceChecker_sound ⟨space, expected⟩ ⟨occurrences⟩
  simpa only [native_revision_check_encoded] using accepted

/-- Accepted count certificates determine the existing Beta sufficient
statistics. This readout does not establish stochastic independence. -/
theorem native_revision_beta_readout {StoreId Revision : Type}
    [DecidableEq StoreId] [DecidableEq Revision]
    (prior : ℝ) (priorPositive : 0 < prior)
    (space : RevisionedEvidenceSpace StoreId Revision)
    (occurrences : List (StoreOccurrenceId StoreId Revision)) (expected : CountPair)
    (accepted : nativeRevisionCheck space.currentRevision (countAtomEntries space)
      occurrences expected = true) :
    ∃ ledger,
      ResolvesLedger space occurrences ledger ∧
      (Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.batchEvidenceBetaParams
        prior priorPositive (ledger.map Prod.snd)).alpha = prior + expected.1 ∧
      (Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.batchEvidenceBetaParams
        prior priorPositive (ledger.map Prod.snd)).beta = prior + expected.2 := by
  have checked : evidenceChecker.check ⟨space, expected⟩ ⟨occurrences⟩ = true := by
    simpa only [native_revision_check_encoded] using accepted
  simpa only [countPairLedger_singletonStampedBatch] using
    accepted_implies_beta_parameters prior priorPositive checked

theorem native_revision_rejects_repeated_observation {StoreId Revision : Type}
    [DecidableEq StoreId] [DecidableEq Revision]
    (current : StoreId → Revision) (entries : StoreId → List Atom)
    (occurrence : StoreOccurrenceId StoreId Revision) (expected : CountPair) :
    nativeRevisionCheck current entries [occurrence, occurrence] expected = false := by
  simp [nativeRevisionCheck]

theorem native_revision_untouched_store {StoreId Revision : Type}
    [DecidableEq StoreId] [DecidableEq Revision]
    (space : RevisionedEvidenceSpace StoreId Revision)
    (occurrences : List (StoreOccurrenceId StoreId Revision)) (expected : CountPair)
    (store : StoreId) (nextRevision : Revision) (nextEntries : List CountPair)
    (outside : ∀ occurrence ∈ occurrences, occurrence.read.storeId ≠ store) :
    nativeRevisionCheck (space.updateStore store nextRevision nextEntries).currentRevision
      (countAtomEntries (space.updateStore store nextRevision nextEntries)) occurrences expected =
      nativeRevisionCheck space.currentRevision (countAtomEntries space) occurrences expected := by
  rw [native_revision_check_encoded, native_revision_check_encoded]
  exact checker_updateStore_outside_support ⟨space, expected⟩ ⟨occurrences⟩
    store nextRevision nextEntries outside

theorem native_revision_rejects_stale {StoreId Revision : Type}
    [DecidableEq StoreId] [DecidableEq Revision]
    (space : RevisionedEvidenceSpace StoreId Revision)
    (occurrences : List (StoreOccurrenceId StoreId Revision)) (expected : CountPair)
    (occurrence : StoreOccurrenceId StoreId Revision) (member : occurrence ∈ occurrences)
    (nextRevision : Revision) (nextEntries : List CountPair)
    (changed : nextRevision ≠ occurrence.read.revision) :
    nativeRevisionCheck
      (space.updateStore occurrence.read.storeId nextRevision nextEntries).currentRevision
      (countAtomEntries (space.updateStore occurrence.read.storeId nextRevision nextEntries))
      occurrences expected = false := by
  rw [native_revision_check_encoded]
  exact checker_rejects_consulted_revision_change ⟨space, expected⟩ ⟨occurrences⟩
    occurrence member nextRevision nextEntries changed

open Mettapedia.PLN.Bridges.KR.RevisionStampedWitnessBridge
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision
open Mettapedia.KR.ConceptGeometry.AbstractInheritance

theorem native_revision_guarded_readout {StoreId Revision : Type}
    [DecidableEq StoreId] [DecidableEq Revision]
    (space : RevisionedEvidenceSpace StoreId Revision)
    (occurrences : List (StoreOccurrenceId StoreId Revision)) (expected : CountPair)
    (accepted : nativeRevisionCheck space.currentRevision (countAtomEntries space)
      occurrences expected = true) :
    ∃ ledger,
      ResolvesLedger space occurrences ledger ∧ totalCounts ledger = expected ∧
      guardedRevisionManyEvidence (countPairStampedBatch (singletonStampedBatch ledger)) =
        some (revisionMany ((countPairLedger (singletonStampedBatch ledger)).map
          Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.countPairEvidence)) := by
  apply accepted_implies_guarded_pln_revision
    (claim := ⟨space, expected⟩) (certificate := ⟨occurrences⟩)
  simpa only [native_revision_check_encoded] using accepted

private def revisionExampleSpace : RevisionedEvidenceSpace Nat Nat where
  currentRevision store := if store = 0 then 7 else 10
  entries store := if store = 0 then [(3, 1), (3, 1), (7, 1)] else [(0, 1)]

private def revisionExampleId (position : Nat) : StoreOccurrenceId Nat Nat :=
  ⟨⟨0, 7⟩, position⟩

private def revisionExampleCertificate := [revisionExampleId 0, revisionExampleId 1]

theorem equal_payloads_distinct_observations_validate :
    nativeRevisionCheck revisionExampleSpace.currentRevision
      (countAtomEntries revisionExampleSpace) revisionExampleCertificate (6, 2) = true := by
  decide +kernel

theorem repeated_observation_refused :
    nativeRevisionCheck revisionExampleSpace.currentRevision
      (countAtomEntries revisionExampleSpace) [revisionExampleId 0, revisionExampleId 0]
      (6, 2) = false := by
  decide +kernel

theorem fabricated_position_or_counts_refused :
    nativeRevisionCheck revisionExampleSpace.currentRevision
      (countAtomEntries revisionExampleSpace) [revisionExampleId 3] (7, 1) = false ∧
    nativeRevisionCheck revisionExampleSpace.currentRevision
      (countAtomEntries revisionExampleSpace) revisionExampleCertificate (7, 2) = false := by
  decide +kernel

theorem equal_payload_revision_change_refused :
    let changed := revisionExampleSpace.updateStore 0 8 (revisionExampleSpace.entries 0)
    nativeRevisionCheck changed.currentRevision (countAtomEntries changed)
      revisionExampleCertificate (6, 2) = false := by
  decide +kernel

theorem unrelated_store_change_keeps_native_evidence :
    let changed := revisionExampleSpace.updateStore 1 11 [(100, 100)]
    nativeRevisionCheck changed.currentRevision (countAtomEntries changed)
      revisionExampleCertificate (6, 2) = true := by
  decide +kernel

theorem invalid_count_payload_is_not_repaired :
    nativeCountAt (fun _ : Nat => (7 : Nat)) (fun _ => [evidenceLiteral (-1) 2])
      (revisionExampleId 0) = none ∧
    nativeCountAt (fun _ : Nat => (7 : Nat)) (fun _ => [integer 2])
      (revisionExampleId 0) = none := by
  decide +kernel

theorem empty_observation_certificate_validates_zero :
    nativeRevisionCheck revisionExampleSpace.currentRevision
      (countAtomEntries revisionExampleSpace) [] (0, 0) = true := by
  decide +kernel

theorem real_zero_count_observation_validates :
    nativeRevisionCheck (fun _ : Nat => (7 : Nat))
      (fun _ => [evidenceLiteral 0 0]) [revisionExampleId 0] (0, 0) = true := by
  decide +kernel

theorem reordered_observations_keep_total_and_distinct_certificate :
    let forward := [revisionExampleId 0, revisionExampleId 2]
    let backward := [revisionExampleId 2, revisionExampleId 0]
    nativeRevisionCheck revisionExampleSpace.currentRevision
      (countAtomEntries revisionExampleSpace) forward (10, 2) = true ∧
    nativeRevisionCheck revisionExampleSpace.currentRevision
      (countAtomEntries revisionExampleSpace) backward (10, 2) = true ∧
    forward ≠ backward := by
  decide +kernel


end Mettapedia.PLN.Bridges.Languages.NativeGradedEvidence
