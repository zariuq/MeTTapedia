import Mettapedia.Logic.EvidenceKinds.Instances
import Mettapedia.PLN.Bridges.KR.RevisionStampedWitnessBridge
import Mettapedia.PLN.WorldModel.PLNWorldModelAdditiveNoGo

/-!
# Believed results: PLN evidence with the observations it rests on

A believed result carries PLN evidence `(n⁺, n⁻)` together with the finite set of identified
observations it rests on, its stamp (`StampedBinaryEvidence` of the stamped-witness bridge). This
module states where such evidence may be added and where it may not, and how it meets the other
kinds.

## The stamp guard is the ledger contract

For identified observations, a packet's evidence is the ledger evidence of its stamp
(`ledgerPacket`). Then **the stamp guard accepts two packets exactly when additive revision is
exact** (`guarded_ledger_revision_exact_iff`): the guard of `RevisionStampedWitnessBridge` and the
exactness theorem `additive_revision_exact_iff_disjoint` of `EvidenceContracts` are one law. The
dependency sets are exactly what licenses addition.

## Derived beliefs rest on their premises

A conclusion drawn from premise packets rests on the union of their stamps (`derive`), as the
conjunction law of `Dependencies` forces. So:

* **a conclusion is never independent of its own premise** (`derived_with_premise_refused`): the
  guard refuses revising a premise with what was concluded from it. This is the feedback hazard,
  `a ⇐ b ⇐ a`, at the level of packets;
* **two conclusions sharing a premise are refused** (`shared_premise_refused`), and their
  identified-ledger counts would count the shared observations twice (`shared_ledger_double_counts`);
* conclusions from disjoint premises revise by addition (`disjoint_premises_revised`).

Without stamps, revising a packet with its own consequence again and again inflates the counts
without any new observation (`Controls.raw_feedback_inflates`); with stamps the union is constant
and the second round is refused (`Controls.stamped_feedback_refused`).

## A proof is not a count

* **No count reading of an idempotent merge** (`no_count_reading_of_idempotent_merge`): a map from
  results merged idempotently (two copies of one proof are one proof) into counts that turns merge
  into addition is zero. With extended counts the only escape is infinite evidence
  (`PLNWorldModelAdditiveNoGo`), and the repository's strength readout gives the infinite positive
  packet strength `0` (`Controls.infinite_positive_reads_zero`). The lawful readings of a proof as
  evidence are the exhaustive ledger on a finite domain (`Instances`) and, against a failing
  observation, the refutation of one of its dependencies.
* **Strong belief is not proof** (`strong_belief_not_proof`): for every `n`, `n` positive
  observations and none negative coexist with a false universal claim.

## The world-model judgments do not bound use

`WMJudgmentMulti` of the world-model calculus derives `W + W` from the context `{W}`
(`multi_reuses_base`): its context is a permission to use states, not a ledger of uses. The linear
judgment `LinearJudgment` uses each listed state exactly once (`LinearJudgment.eq_sum`,
`LinearJudgment.of_sum`) and refines it (`LinearJudgment.toMulti`); from `{W}` it derives `W` only
(`LinearJudgment.singleton`). Two genuinely distinct observations with equal values are listed
twice and may be added.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.EvidenceKinds

open scoped ENNReal
open Mettapedia.PLN.Evidence
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.WorldModel.EvidenceSpaces
open Mettapedia.PLN.WorldModel.EvidenceContracts
open Mettapedia.KR.ConceptGeometry.AbstractInheritance
open Mettapedia.PLN.Bridges.KR.RevisionStampedWitnessBridge
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision

universe u v w

/-! ## Ledger packets -/

section Ledger

variable {Id : Type u} {W : Type v} [DecidableEq Id]

/-- Natural counts as extended counts. -/
noncomputable def countsToBinary (e : Evidence ℕ) : BinaryEvidence := ⟨e.pos, e.neg⟩

theorem countsToBinary_add (a b : Evidence ℕ) :
    countsToBinary (a + b) = countsToBinary a + countsToBinary b := by
  simp [countsToBinary, BinaryEvidence.hplus_def]

/-- **A ledger packet**: the evidence of identified observations, stamped with their identities. -/
noncomputable def ledgerPacket (world : Id → W) (φ : W → Bool) (ledger : Finset Id) :
    StampedBinaryEvidence Id :=
  ⟨countsToBinary (ledgerEvidence world φ ledger), ledger⟩

/-- **The stamp guard accepts two ledger packets exactly when additive revision is exact.** -/
theorem guarded_ledger_revision_exact_iff (world : Id → W) (φ : W → Bool) (first second : Finset Id) :
    guardedRevisionManyEvidence [ledgerPacket world φ first, ledgerPacket world φ second] =
        some (countsToBinary (ledgerEvidence world φ (first ∪ second))) ↔ Disjoint first second := by
  constructor
  · intro accepted
    have some' : (guardedRevisionManyEvidence
        [ledgerPacket world φ first, ledgerPacket world φ second]).isSome := by
      rw [accepted]; rfl
    have pairwise := (StampedBinaryEvidence.guardedListRevise_isSome_iff_pairwise _).mp
      (by simpa [guardedRevisionManyEvidence] using some')
    have := (List.pairwise_pair.mp pairwise)
    exact this
  · intro disjoint
    have pairwise : [ledgerPacket world φ first, ledgerPacket world φ second].Pairwise
        StampedBinaryEvidence.StampDisjoint := List.pairwise_pair.mpr disjoint
    rw [(guardedRevisionManyEvidence_eq_some_revisionMany_iff_pairwise _).mpr pairwise,
      ledgerEvidence_union_of_disjoint world φ disjoint, countsToBinary_add]
    simp [ledgerPacket, revisionMany, BinaryEvidence.hplus_def]

/-- The counts of two ledgers sharing an observation, added, count it twice. -/
theorem shared_ledger_double_counts (world : Id → W) (φ : W → Bool) {first second : Finset Id}
    {shared : Id} (inFirst : shared ∈ first) (inSecond : shared ∈ second) :
    ledgerEvidence world φ first + ledgerEvidence world φ second ≠
      ledgerEvidence world φ (first ∪ second) := by
  intro exact
  exact Finset.disjoint_left.mp ((additive_revision_exact_iff_disjoint world φ first second).mp exact)
    inFirst inSecond

end Ledger

/-! ## Derived beliefs -/

section Derived

variable {Stamp : Type u} [DecidableEq Stamp]

/-- **A conclusion from premise packets**: its evidence is computed by a rule's formula from the
premises' evidence; it rests on the union of their stamps. -/
noncomputable def derive (formula : List BinaryEvidence → BinaryEvidence)
    (premises : List (StampedBinaryEvidence Stamp)) : StampedBinaryEvidence Stamp :=
  ⟨formula (premises.map fun premise => premise.evidence),
    (StampedBinaryEvidence.listRevise premises).stamp⟩

theorem stamp_le_derive (formula : List BinaryEvidence → BinaryEvidence)
    {premises : List (StampedBinaryEvidence Stamp)} {premise : StampedBinaryEvidence Stamp}
    (member : premise ∈ premises) : premise.stamp ⊆ (derive formula premises).stamp := by
  intro source inPremise
  exact (StampedBinaryEvidence.mem_listRevise_stamp premises).mpr ⟨premise, member, inPremise⟩

/-- **A conclusion is never independent of its own premise.** -/
theorem derived_with_premise_refused (formula : List BinaryEvidence → BinaryEvidence)
    {premises : List (StampedBinaryEvidence Stamp)} {premise : StampedBinaryEvidence Stamp}
    (member : premise ∈ premises) {source : Stamp} (inPremise : source ∈ premise.stamp) :
    guardedRevisionManyEvidence [premise, derive formula premises] = none :=
  guardedRevisionManyEvidence_pair_rejects_shared_stamp inPremise
    (stamp_le_derive formula member inPremise)

/-- **Two conclusions sharing a premise are refused.** -/
theorem shared_premise_refused (first second : List BinaryEvidence → BinaryEvidence)
    {firstPremises secondPremises : List (StampedBinaryEvidence Stamp)}
    {premise : StampedBinaryEvidence Stamp} (inFirst : premise ∈ firstPremises)
    (inSecond : premise ∈ secondPremises) {source : Stamp} (inPremise : source ∈ premise.stamp) :
    guardedRevisionManyEvidence [derive first firstPremises, derive second secondPremises] = none :=
  guardedRevisionManyEvidence_pair_rejects_shared_stamp (stamp_le_derive first inFirst inPremise)
    (stamp_le_derive second inSecond inPremise)

/-- **Conclusions from disjoint premises revise by addition.** -/
theorem disjoint_premises_revised (first second : List BinaryEvidence → BinaryEvidence)
    (firstPremises secondPremises : List (StampedBinaryEvidence Stamp))
    (disjoint : ∀ x ∈ firstPremises, ∀ y ∈ secondPremises, Disjoint x.stamp y.stamp) :
    guardedRevisionManyEvidence [derive first firstPremises, derive second secondPremises] =
      some ((derive first firstPremises).evidence + (derive second secondPremises).evidence) := by
  have stamps : Disjoint (derive first firstPremises).stamp (derive second secondPremises).stamp := by
    rw [Finset.disjoint_left]
    intro source inFirst inSecond
    obtain ⟨x, xIn, sx⟩ := (StampedBinaryEvidence.mem_listRevise_stamp firstPremises).mp inFirst
    obtain ⟨y, yIn, sy⟩ := (StampedBinaryEvidence.mem_listRevise_stamp secondPremises).mp inSecond
    exact Finset.disjoint_left.mp (disjoint x xIn y yIn) sx sy
  have pairwise : [derive first firstPremises, derive second secondPremises].Pairwise
      StampedBinaryEvidence.StampDisjoint := List.pairwise_pair.mpr stamps
  rw [(guardedRevisionManyEvidence_eq_some_revisionMany_iff_pairwise _).mpr pairwise]
  simp [revisionMany, BinaryEvidence.hplus_def]

end Derived

/-! ## A proof is not a count -/

section NoCount

/-- **No count reading of an idempotent merge**: a map into counts that turns an idempotent merge
into addition is zero. -/
theorem no_count_reading_of_idempotent_merge {M : Type u} (merge : M → M → M)
    (idempotent : ∀ x, merge x x = x) (reading : M → Evidence ℕ)
    (additive : ∀ x y, reading (merge x y) = reading x + reading y) (x : M) : reading x = 0 := by
  have twice := additive x x
  rw [idempotent] at twice
  ext
  · have := congrArg Evidence.pos twice
    simp only [Evidence.add_pos] at this
    simp only [Evidence.zero_pos]
    omega
  · have := congrArg Evidence.neg twice
    simp only [Evidence.add_neg] at this
    simp only [Evidence.zero_neg]
    omega

/-- Dependency sets merge by union, so they have no count reading. -/
theorem no_count_reading_of_dependency_sets {Dep : Type u} [DecidableEq Dep]
    (reading : Finset Dep → Evidence ℕ) (additive : ∀ D E, reading (D ∪ E) = reading D + reading E)
    (D : Finset Dep) : reading D = 0 :=
  no_count_reading_of_idempotent_merge (· ∪ ·) Finset.union_idempotent reading additive D

/-- With extended counts the reading is zero wherever it is finite. -/
theorem no_finite_extended_reading {M : Type u} (merge : M → M → M) (idempotent : ∀ x, merge x x = x)
    (reading : M → BinaryEvidence) (additive : ∀ x y, reading (merge x y) = reading x + reading y)
    (x : M) (finite : PLNWorldModelAdditiveNoGo.BinaryEvidence.IsFinite (reading x)) :
    reading x = 0 := by
  have twice := additive x x
  rw [idempotent] at twice
  exact PLNWorldModelAdditiveNoGo.BinaryEvidence.eq_zero_of_hplus_idempotent finite twice.symm

/-- **Strong belief is not proof**: `n` positive observations and no negative one coexist with a
false universal claim. -/
theorem strong_belief_not_proof (n : ℕ) :
    testEvidence (fun k : ℕ => decide (k < n)) (Finset.range n) = ⟨n, 0⟩ ∧
      ¬ Universal Set.univ (fun k : ℕ => k < n) := by
  refine ⟨?_, failing_case_refutes (Set.mem_univ n) (lt_irrefl n)⟩
  rw [testEvidence_of_tested fun k member => by simpa using Finset.mem_range.mp member]
  simp

end NoCount

/-! ## The world-model judgments -/

section Judgments

variable {State : Type u} [EvidenceType State]

/-- **`WMJudgmentMulti` reuses a base state**: `{W}` derives `W + W`. -/
theorem multi_reuses_base (W : State) : WMJudgmentMulti {W} (W + W) :=
  .revise (.base W (Multiset.mem_singleton_self W)) (.base W (Multiset.mem_singleton_self W))



end Judgments

/-! ## Controls -/

namespace Controls

/-- One positive observation. -/
noncomputable def onePositive : BinaryEvidence := ⟨1, 0⟩

/-- **The multiset judgment counts one observation twice; the linear one does not.** -/
theorem one_observation_twice :
    WMJudgmentMulti {onePositive} (onePositive + onePositive) ∧
      onePositive + onePositive ≠ onePositive ∧
      ¬ LinearJudgment {onePositive} (onePositive + onePositive) := by
  have ne : onePositive + onePositive ≠ onePositive := by
    intro same
    have := congrArg BinaryEvidence.pos same
    simp [onePositive, BinaryEvidence.hplus_def] at this
  exact ⟨multi_reuses_base onePositive, ne, fun derivation => ne derivation.singleton⟩

/-- **The infinite positive packet is idempotent, and the strength readout gives it `0`.** So does
the same packet after one counterexample. -/
theorem infinite_positive_reads_zero :
    (⟨⊤, 0⟩ : BinaryEvidence) + ⟨⊤, 0⟩ = ⟨⊤, 0⟩ ∧
      BinaryEvidence.toStrength ⟨⊤, 0⟩ = 0 ∧ BinaryEvidence.toStrength (⟨⊤, 0⟩ + ⟨0, 1⟩) = 0 := by
  refine ⟨by simp [BinaryEvidence.hplus_def], ?_, ?_⟩
  · simp [BinaryEvidence.toStrength, BinaryEvidence.total]
  · simp [BinaryEvidence.toStrength, BinaryEvidence.total, BinaryEvidence.hplus_def]

/-- A packet of one observation, stamped with its identity. -/
noncomputable def observation (id : ℕ) : StampedBinaryEvidence ℕ := ⟨⟨1, 0⟩, {id}⟩

/-- Revise a packet with the current state, ignoring stamps' meaning: raw count addition. -/
noncomputable def rawFeedback (packet state : StampedBinaryEvidence ℕ) : StampedBinaryEvidence ℕ :=
  StampedBinaryEvidence.revise packet state

/-- **Raw feedback inflates the counts without a new observation**: after `n` rounds one
observation counts `n` times, while the stamp stays one observation. -/
theorem raw_feedback_inflates (n : ℕ) :
    ((rawFeedback (observation 0))^[n] StampedBinaryEvidence.empty).evidence.pos = n ∧
      ((rawFeedback (observation 0))^[n + 1] StampedBinaryEvidence.empty).stamp = {0} := by
  constructor
  · induction n with
    | zero => simp [StampedBinaryEvidence.empty]
    | succ n ih =>
        rw [Function.iterate_succ_apply', rawFeedback, StampedBinaryEvidence.revise_evidence,
          BinaryEvidence.hplus_def]
        simp only
        rw [ih]
        simp only [observation]
        push_cast
        ring
  · induction n with
    | zero => simp [rawFeedback, observation, StampedBinaryEvidence.empty]
    | succ n ih =>
        rw [Function.iterate_succ_apply', rawFeedback, StampedBinaryEvidence.revise_stamp, ih]
        simp [observation]

/-- **With stamps, the second round of feedback is refused.** -/
theorem stamped_feedback_refused :
    guardedRevisionManyEvidence [observation 0, rawFeedback (observation 0) StampedBinaryEvidence.empty] =
      none :=
  guardedRevisionManyEvidence_pair_rejects_shared_stamp (a := 0) (by simp [observation])
    (by simp [rawFeedback, observation, StampedBinaryEvidence.empty])

/-- **Shared premise**: deductions through one premise observation are refused; through disjoint
ones they are added. -/
theorem shared_and_disjoint_premises :
    guardedRevisionManyEvidence
        [derive (fun _ => ⟨1, 0⟩) [observation 0, observation 1],
          derive (fun _ => ⟨1, 0⟩) [observation 0, observation 2]] = none ∧
      guardedRevisionManyEvidence
        [derive (fun _ => ⟨1, 0⟩) [observation 0, observation 1],
          derive (fun _ => ⟨1, 0⟩) [observation 2, observation 3]] = some ⟨2, 0⟩ := by
  refine ⟨shared_premise_refused _ _ (premise := observation 0) (by simp) (by simp)
    (source := 0) (by simp [observation]), ?_⟩
  rw [disjoint_premises_revised]
  · simp [derive, BinaryEvidence.hplus_def]
    norm_num
  · simp [observation]

/-- **Linear judgment, positive**: two observations, each used once, revise to their sum.
(`one_observation_twice` is the negative control: one observation cannot be used twice.) -/
theorem two_observations_linear :
    LinearJudgment ({onePositive} + {onePositive}) (onePositive + onePositive) :=
  .revise (.base _) (.base _)

end Controls

end Mettapedia.Logic.EvidenceKinds
