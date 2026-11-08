import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsQuantum
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsAmplitudeControls

/-!
# Records observed at the cut, and the four aggregations on one diamond

## A record is an occurrence observed at the cut

* A configuration class keeps its present occurrences (`presentOf`), so the end of a causal
  history determines which occurrences are present at the cut (`presentOf_classEnd`).
* **Records separate ends** (`injOn_of_records`): if every causal history that ends in `Q` has a
  record, an occurrence present at its end and absent at the end of every other history of the
  region, then no two of them reach the same configuration class.
* **Records destroy interference** (`records_destroy_interference`): then the record-respecting
  readout is the incoherent weight, the classical sum of the branch weights.
* Control (`Superposed.records_found`): R27's superposed alternatives make the answer rows `20`
  and `21`; each is present at the end of its own history and absent at the other's, so they are
  records, and the readout of the amplitudes `1` and `-1` is `2`.
* Control (`Superposed.nominal_interferes`): read with the nominal end, which renames occurrence
  identities, the same two histories have one end and the amplitudes `1` and `-1` read `0`.

## Classical aggregation over interleavings

* `interleavingWeight` adds the Born weights of the terminal words that end in `Q`, once per word.
  It counts each causal history once per interleaving (`interleavingWeight_eq_sum_count`), so it
  is the incoherent weight of the causal histories when every history has one interleaving
  (`interleavingWeight_eq_incoherent_of_single`).
* **The diamond three ways** (`Diamond.diamond_three_ways`): one causal history of amplitude `i`
  reached by two words. Deduplicated, its Born weight is `1`; aggregated classically over the
  interleavings, `2`; summed coherently over the interleavings, `4`.

## Confidence derived from identified measurements

* `ledgerConfidence` is PLN's `n/(n+k)` for the `n` identified observations of R30's ledger
  (`ledgerConfidence_eq_card`). Publishing the same measurements again does not raise it
  (`republication_adds_no_confidence`); disjoint measurements add their counts
  (`disjoint_measurements_add_confidence`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

namespace AmplitudeRuns

open Mettapedia.Algebra.RationalComplexAmplitude (Amplitude born)
open AnnotatedRunUnfolding (CausalClass completed)
open AnnotatedRunBranchCollection (terminalBranches)
open Mettapedia.PLN.WorldModel.EvidenceContracts (ledgerEvidence ledgerEvidence_total)

universe uT uS uO

/-! ## Records observed at the cut -/

section Records

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T) (amp : Firing T S O → Amplitude)
variable {catalogue : List (Firing T S O)} {budget : ℕ} {root : Configuration T O}
  {Q : ConfigurationClass A O → Prop}

/-- The occurrences present at the end of a causal history are those its runs leave. -/
theorem presentOf_classEnd (w : List (Firing T S O)) :
    presentOf A (classEnd A label root (Quot.mk _ w)) = (follow label root w).present := rfl

/-- **Records separate ends.** If every causal history that ends in `Q` has a record, present at
its end and absent at the end of every other history of the region, no two of them reach the same
configuration class. -/
theorem injOn_of_records (record : CausalClass A label root → O)
    (observed : ∀ trace ∈ regionBranches A label catalogue budget root Q,
      record trace ∈ presentOf A (classEnd A label root trace))
    (distinguishes : ∀ trace ∈ regionBranches A label catalogue budget root Q,
      ∀ trace' ∈ regionBranches A label catalogue budget root Q, trace' ≠ trace →
        record trace ∉ presentOf A (classEnd A label root trace')) :
    Set.InjOn (classEnd A label root) (regionBranches A label catalogue budget root Q) := by
  intro trace inTrace trace' inTrace' same
  by_contra different
  exact distinguishes trace inTrace trace' inTrace' (Ne.symm different)
    (same ▸ observed trace inTrace)

/-- **Records destroy interference**: with a record for every causal history that ends in `Q`,
observed at the cut, the record-respecting readout is the classical sum of the branch weights. -/
theorem records_destroy_interference (record : CausalClass A label root → O)
    (observed : ∀ trace ∈ regionBranches A label catalogue budget root Q,
      record trace ∈ presentOf A (classEnd A label root trace))
    (distinguishes : ∀ trace ∈ regionBranches A label catalogue budget root Q,
      ∀ trace' ∈ regionBranches A label catalogue budget root Q, trace' ≠ trace →
        record trace ∉ presentOf A (classEnd A label root trace')) :
    branchReadout A label amp catalogue budget root Q =
      incoherent (branchAmplitudes A label amp catalogue budget root Q) :=
  branchReadout_of_recorded A label amp (injOn_of_records A label record observed distinguishes)

end Records

/-! ## Classical aggregation over interleavings -/

section Interleavings

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T) (amp : Firing T S O → Amplitude)
variable (catalogue : List (Firing T S O)) (budget : ℕ) (root : Configuration T O)
  (Q : ConfigurationClass A O → Prop)

open Classical in
/-- **Classical aggregation over interleavings**: the Born weights of the terminal words that end
in `Q`, once per word. -/
noncomputable def interleavingWeight : ℚ :=
  (((completed A label catalogue budget root).filter fun w =>
      decide (Q (ConfigurationClass.mk A (follow label root w)))).map
    fun w => born (runAmplitude amp w)).sum

open Classical in
/-- **It counts each causal history once per interleaving.** -/
theorem interleavingWeight_eq_sum_count :
    interleavingWeight A label amp catalogue budget root Q =
      ∑ trace ∈ regionBranches A label catalogue budget root Q,
        interleavings A label catalogue budget root Q trace •
          born (classAmplitude A label amp root trace) := by
  unfold interleavingWeight interleavings
  have mapped : ((completed A label catalogue budget root).filter fun w =>
        decide (Q (ConfigurationClass.mk A (follow label root w)))).map
          (fun w => born (runAmplitude amp w)) =
      (((completed A label catalogue budget root).filter fun w =>
        decide (Q (ConfigurationClass.mk A (follow label root w)))).map
          (Quot.mk (RoundEquiv A label root))).map
            (fun trace => born (classAmplitude A label amp root trace)) := by
    rw [List.map_map]
    rfl
  rw [mapped, Finset.sum_list_map_count]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext trace
  rw [mem_regionBranches, List.mem_toFinset, List.mem_map]
  unfold terminalBranches
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨w, member, rfl⟩
    rw [List.mem_filter, decide_eq_true_eq] at member
    exact ⟨⟨w, member.1, rfl⟩, member.2⟩
  · rintro ⟨⟨w, member, rfl⟩, inQ⟩
    exact ⟨w, List.mem_filter.mpr ⟨member, decide_eq_true_eq.mpr inQ⟩, rfl⟩

variable {catalogue budget root Q}

/-- **With one interleaving per history, classical aggregation over interleavings is the
incoherent weight of the causal histories.** -/
theorem interleavingWeight_eq_incoherent_of_single
    (single : ∀ trace ∈ regionBranches A label catalogue budget root Q,
      interleavings A label catalogue budget root Q trace = 1) :
    interleavingWeight A label amp catalogue budget root Q =
      incoherent (branchAmplitudes A label amp catalogue budget root Q) := by
  rw [interleavingWeight_eq_sum_count, incoherent_branchAmplitudes]
  unfold classicalWeight
  refine Finset.sum_congr rfl fun trace member => ?_
  rw [single trace member, one_smul]

end Interleavings

/-! ## Confidence derived from identified measurements -/

section Confidence

variable {Id W : Type*} [DecidableEq Id]

/-- **The confidence of a ledger of identified measurements**: PLN's `n/(n+k)` for its `n`
observations, at prior weight `k`. -/
def ledgerConfidence (world : Id → W) (φ : W → Bool) (k : ℚ) (ledger : Finset Id) : ℚ :=
  ((ledgerEvidence world φ ledger).total : ℚ) / ((ledgerEvidence world φ ledger).total + k)

omit [DecidableEq Id] in
theorem ledgerConfidence_eq_card (world : Id → W) (φ : W → Bool) (k : ℚ) (ledger : Finset Id) :
    ledgerConfidence world φ k ledger = (ledger.card : ℚ) / (ledger.card + k) := by
  unfold ledgerConfidence
  rw [ledgerEvidence_total]

/-- **Publishing the same measurements again does not raise the confidence.** -/
theorem republication_adds_no_confidence (world : Id → W) (φ : W → Bool) (k : ℚ)
    (ledger : Finset Id) :
    ledgerConfidence world φ k (ledger ∪ ledger) = ledgerConfidence world φ k ledger := by
  rw [Finset.union_self]

/-- **Disjoint measurements add their counts.** -/
theorem disjoint_measurements_add_confidence (world : Id → W) (φ : W → Bool) (k : ℚ)
    {first second : Finset Id} (apart : Disjoint first second) :
    ledgerConfidence world φ k (first ∪ second) =
      ((first.card + second.card : ℕ) : ℚ) / ((first.card + second.card : ℕ) + k) := by
  rw [ledgerConfidence_eq_card, Finset.card_union_of_disjoint apart]

end Confidence

/-! ## Controls -/

namespace AggregationControls

open ConstraintMultisetRewriting.Controls (A)
open AnnotatedRuns.Controls (label)
open AmplitudeControls (everything regionBranches_everything)

/-! ### The superposed alternatives carry records -/

namespace Superposed

open AnnotatedRunBranchCollection.Controls.Superpose (root first second alternatives branches
  branches_distinct)
open AmplitudeControls.Superposed (shifted superposed_cancel)

open Classical in
/-- The record of each superposed alternative: the answer row it made. -/
noncomputable def answerRecord (trace : CausalClass A label root) : ℕ :=
  if trace = Quot.mk _ [first] then 20 else 21

theorem answerRecord_first : answerRecord (Quot.mk _ [first]) = 20 := by
  unfold answerRecord
  rw [if_pos rfl]

theorem answerRecord_second : answerRecord (Quot.mk _ [second]) = 21 := by
  unfold answerRecord
  rw [if_neg branches_distinct.symm]

open Classical in
theorem records_observed : ∀ trace ∈ regionBranches A label alternatives 1 root everything,
    answerRecord trace ∈ presentOf A (classEnd A label root trace) := by
  intro trace member
  rw [regionBranches_everything, branches, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl
  · rw [answerRecord_first, presentOf_classEnd]
    decide
  · rw [answerRecord_second, presentOf_classEnd]
    decide

open Classical in
theorem records_distinguish : ∀ trace ∈ regionBranches A label alternatives 1 root everything,
    ∀ trace' ∈ regionBranches A label alternatives 1 root everything, trace' ≠ trace →
      answerRecord trace ∉ presentOf A (classEnd A label root trace') := by
  intro trace member trace' member' apart
  rw [regionBranches_everything, branches, Finset.mem_insert, Finset.mem_singleton] at member
  rw [regionBranches_everything, branches, Finset.mem_insert, Finset.mem_singleton] at member'
  rcases member with rfl | rfl <;> rcases member' with rfl | rfl
  · exact absurd rfl apart
  · rw [answerRecord_first, presentOf_classEnd]
    decide
  · rw [answerRecord_second, presentOf_classEnd]
    decide
  · exact absurd rfl apart

/-- **The answer rows are records, so the superposed amplitudes `1` and `-1` read `2`.** -/
theorem records_found :
    branchReadout A label shifted alternatives 1 root everything = 2 := by
  rw [records_destroy_interference A label shifted answerRecord records_observed
    records_distinguish]
  exact superposed_cancel.2.2.1

/-- **Nominally, the superposed alternatives interfere.** Their ends differ only in the identities
`20` and `21` of two rows with one label, so the nominal end identifies them and the amplitudes `1`
and `-1` read `0`, where the identity end reads `2`. -/
theorem nominal_interferes :
    nominalReadout A label shifted alternatives 1 root everything = 0 ∧
      branchReadout A label shifted alternatives 1 root everything = 2 := by
  refine ⟨?_, records_found⟩
  classical
  have nonempty : (regionBranches A label alternatives 1 root everything).Nonempty := by
    rw [regionBranches_everything, branches]
    exact Finset.insert_nonempty _ _
  have shared : ∀ trace ∈ regionBranches A label alternatives 1 root everything,
      nominalEnd A label (classEnd A label root trace) =
        nominalEnd A label (classEnd A label root (Quot.mk _ [first])) := by
    intro trace member
    rw [regionBranches_everything, branches, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · rfl
    · rfl
  rw [nominalReadout_of_one_end A label shifted nonempty shared, superposed_cancel.2.1]
  exact (Mettapedia.Algebra.RationalComplexAmplitude.born_zero_iff 0).mpr rfl

end Superposed

/-! ### The diamond three ways -/

namespace Diamond

open AnnotatedRuns.Controls (taker reader start)
open AmplitudeControls.Diamond (phase catalogue completed_diamond diamond_in_unfolding
  diamond_counts_twice)

/-- **The diamond three ways.** One causal history of amplitude `i`, reached by two words:
deduplicated, its Born weight is `1`; aggregated classically over the interleavings, `2`; summed
coherently over the interleavings, `4`. -/
theorem diamond_three_ways :
    born (regionalAmplitude A label phase catalogue 2 start everything) = 1 ∧
      interleavingWeight A label phase catalogue 2 start everything = 2 ∧
      born (interleavingAmplitude A label phase catalogue 2 start everything) = 4 := by
  refine ⟨diamond_in_unfolding.2.2.2.2.1, ?_, diamond_in_unfolding.2.2.2.2.2⟩
  classical
  have kept : ∀ w ∈ [[taker, reader], [reader, taker]],
      (fun w => decide (everything (ConfigurationClass.mk A (follow label start w)))) w = true :=
    fun _ _ => decide_eq_true trivial
  unfold interleavingWeight
  rw [completed_diamond, List.filter_eq_self.mpr kept]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [diamond_counts_twice.2.1, diamond_counts_twice.2.2.1, born_unitI]
  norm_num

end Diamond

end AggregationControls

end AmplitudeRuns

open AmplitudeRuns

#print axioms presentOf_classEnd
#print axioms injOn_of_records
#print axioms records_destroy_interference
#print axioms interleavingWeight_eq_sum_count
#print axioms interleavingWeight_eq_incoherent_of_single
#print axioms ledgerConfidence_eq_card
#print axioms republication_adds_no_confidence
#print axioms disjoint_measurements_add_confidence
#print axioms AggregationControls.Superposed.records_observed
#print axioms AggregationControls.Superposed.records_distinguish
#print axioms AggregationControls.Superposed.records_found
#print axioms AggregationControls.Superposed.nominal_interferes
#print axioms AggregationControls.Diamond.diamond_three_ways

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
