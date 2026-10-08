import Mettapedia.OSLF.Framework.AssayRevisionMetric
import Mettapedia.OSLF.Framework.StructuralInspectionAssayControls

/-!
# Revision agreement does not identify inspection prices

Two independently authored hypothesis sequences ask semantically identical
questions at every stage. Their observation distance is zero, and all their
structural truth certificates agree, while their chosen full inspections
have different prices. The same received tree is confirmed by the affordable
test and left unanswered by the underfunded one.

These are structural observation stages, not an assumed presentation of
greatest-fixed-point unfolding approximants.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.AssayRevision.Controls

open InstrumentObservations AssayControls
open Mettapedia.GSLT.Causality ResourceInteraction ComplementaryAssay

def compact : Hypothesis Bool AssayControls.arity := fun _ => .top
def verbose : Hypothesis Bool AssayControls.arity := fun _ => repeatedTruth 5

theorem same_complete_stage_answers : structuralScheme.Indistinguishable compact verbose := by
  funext stage tree
  exact (repeatedTruth_holds 5 tree).symm

theorem zero_revision_distance : structuralScheme.distance compact verbose = 0 :=
  (structuralScheme.distance_eq_zero_iff compact verbose).2 same_complete_stage_answers

theorem same_truth_certificates_at_every_stage (stage : Nat)
    (branch : Verdict) (tree : Tree Bool AssayControls.arity) :
    TestCertificate (compact stage) branch tree ↔ TestCertificate (verbose stage) branch tree :=
  retained_structural_certificate (depth := stage)
    (by rw [zero_revision_distance]; positivity) (Nat.le_refl stage) branch tree

theorem prices_remain_different :
    (inspect (compact 0) paired).2 = 1 ∧ (inspect (verbose 0) paired).2 = 11 := by decide

theorem exact_agreement_does_not_supply_testing_funds :
    observed (fun tree => (inspect (compact 0) tree).1)
        (fun tree => (inspect (compact 0) tree).2) 20 7 (some paired) 1 =
      { (20, .confirm, 7, paired) } ∧
    observed (fun tree => (inspect (verbose 0) tree).1)
        (fun tree => (inspect (verbose 0) tree).2) 20 7 (some paired) 1 = 0 := by decide

theorem affordable_verbose_test_confirms :
    observed (fun tree => (inspect (verbose 0) tree).1)
        (fun tree => (inspect (verbose 0) tree).2) 20 7 (some paired) 11 =
      { (20, .confirm, 7, paired) } := by decide

def alternating (stage : Nat) : Hypothesis Bool AssayControls.arity :=
  if stage % 2 = 0 then compact else verbose

theorem every_alternating_pair_agrees (first second : Nat) :
    structuralScheme.distance (alternating first) (alternating second) = 0 := by
  apply (structuralScheme.distance_eq_zero_iff _ _).2
  funext stage tree
  unfold alternating
  split_ifs <;> rfl

theorem actual_finite_revision_walk_is_confined (depth count : Nat) :
    structuralScheme.distance (alternating 0) (alternating count) < (1 / 2 : ℝ) ^ depth :=
  finite_walk_confined structuralScheme alternating depth count
    (fun position _ => by rw [every_alternating_pair_agrees]; positivity)

def lateRefutation (position : Nat) : Hypothesis Bool AssayControls.arity :=
  fun stage => if stage = position then .neg .top else .top

theorem late_answer_diff (position : Nat) :
    structuralScheme.satisfies position compact ≠
      structuralScheme.satisfies position (lateRefutation position) := by
  intro same
  have values := congrFun same paired
  simp [structuralScheme, compact, lateRefutation, evaluate] at values

theorem late_refutation_separates (position : Nat) :
    ¬ structuralScheme.Indistinguishable compact (lateRefutation position) := by
  intro same
  exact late_answer_diff position (congrFun same position)

theorem late_first_separation (position : Nat) :
    structuralScheme.separatingRank compact (lateRefutation position) = position := by
  have earlierAnswers : ∀ stage < position,
      structuralScheme.satisfies stage compact =
        structuralScheme.satisfies stage (lateRefutation position) := by
    intro stage earlier
    funext tree
    simp [structuralScheme, compact, lateRefutation, Nat.ne_of_lt earlier]
  apply Nat.le_antisymm
  · by_contra notBounded
    have before : position < structuralScheme.separatingRank compact (lateRefutation position) := by omega
    exact late_answer_diff position (PiNat.apply_eq_of_lt_firstDiff before)
  · by_contra notBounded
    have before : structuralScheme.separatingRank compact (lateRefutation position) < position := by omega
    exact PiNat.apply_firstDiff_ne (late_refutation_separates position)
      (earlierAnswers _ before)

theorem late_revision_distance (position : Nat) :
    structuralScheme.distance compact (lateRefutation position) = (1 / 2 : ℝ) ^ position := by
  rw [structuralScheme.distance_eq compact (lateRefutation position) (late_refutation_separates position),
    late_first_separation]

theorem nonzero_small_revision (depth : Nat) :
    0 < structuralScheme.distance compact (lateRefutation (depth + 1)) ∧
      structuralScheme.distance compact (lateRefutation (depth + 1)) < (1 / 2 : ℝ) ^ depth := by
  rw [late_revision_distance]
  constructor
  · positivity
  · exact pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (Nat.lt_succ_self depth)

end Mettapedia.OSLF.Framework.AssayRevision.Controls
