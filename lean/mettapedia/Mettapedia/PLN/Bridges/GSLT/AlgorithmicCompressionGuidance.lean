import Mettapedia.PLN.Bridges.GSLT.InferenceControl

/-!
# Algorithmic-compression estimators as GSLT guidance

WILLIAM (Arthur Franz, Alexey Gogulya, and Michael Löffler, AGI 2019) searches
for compressive feature graphs.  The `infcontrol` application uses learned
formula features to estimate whether a candidate will occur in a proof.  Such
an estimate can guide proof search, but it is neither PLN evidence nor proof
authority.

This file installs any `(goal, candidate) → score` estimator in the existing
occurrence-preserving controller.  The estimator occupies the independent
estimated-cost/priority channel while the PLN evidence channel remains zero.
Consequently:

* sorting is a permutation of the live frontier;
* an absent candidate cannot be introduced;
* every bounded run remains sound in the underlying branching system; and
* a completed run has the same additive denotation as the unguided roots.

Top-k truncation is intentionally excluded: it is not a permutation and needs
separate pruning authority or a fairness fallback.  This is the formal
correctness boundary for the CeTTa Prime showcase.  No WILLIAM or `infcontrol`
implementation is imported or redistributed here.
-/

namespace Mettapedia.PLN.Bridges.GSLT.AlgorithmicCompressionGuidance

open scoped Classical

open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.InferenceControl.PremiseSelection
open Mettapedia.PLN.Bridges.GSLT.InferenceControl

universe uGoal uNode uAnswer uScore

/-- The neutral PLN evidence channel.  An external compression score is not
silently reinterpreted as observed positive/negative evidence. -/
def noEvidenceScorer (Goal : Type uGoal) (Node : Type uNode) :
    Scorer Goal Node where
  score _ _ := ⟨0, 0⟩

/-- Install an arbitrary estimator as the sole scheduling priority.  Its
comparison may express higher-is-better probability or lower-is-better cost. -/
def estimatorGuidance
    {Goal : Type uGoal} {Node : Type uNode} {Score : Type uScore}
    (estimate : Goal → Node → Score)
    (prefer : Score → Score → Prop) :
    Guidance Goal Node Score Score where
  scorer := noEvidenceScorer Goal Node
  estimate := estimate
  rank := fun _ score => score
  prefer := prefer

@[simp]
theorem estimatorGuidance_evidenceAt
    {Goal : Type uGoal} {Node : Type uNode} {Score : Type uScore}
    (estimate : Goal → Node → Score)
    (prefer : Score → Score → Prop)
    (goal : Goal) (node : Node) :
    (estimatorGuidance estimate prefer).evidenceAt goal node = ⟨0, 0⟩ :=
  rfl

@[simp]
theorem estimatorGuidance_priorityAt
    {Goal : Type uGoal} {Node : Type uNode} {Score : Type uScore}
    (estimate : Goal → Node → Score)
    (prefer : Score → Score → Prop)
    (goal : Goal) (node : Node) :
    (estimatorGuidance estimate prefer).priorityAt goal node =
      estimate goal node :=
  rfl

/-- Estimator-guided sorting preserves every occurrence, including duplicate
occurrences, exactly. -/
theorem estimatorScheduler_reorder_perm
    {Goal : Type uGoal} {Node : Type uNode} {Score : Type uScore}
    (estimate : Goal → Node → Score)
    (prefer : Score → Score → Prop)
    (goal : Goal) (base : Scheduler Node) (frontier : List Node) :
    List.Perm
      (((estimatorGuidance estimate prefer).scheduler goal base).reorder frontier)
      frontier :=
  Guidance.scheduler_reorder_perm _ goal base frontier

/-- A scored but absent candidate remains absent. -/
theorem mem_estimatorScheduler_reorder_iff
    {Goal : Type uGoal} {Node : Type uNode} {Score : Type uScore}
    (estimate : Goal → Node → Score)
    (prefer : Score → Score → Prop)
    (goal : Goal) (base : Scheduler Node) (frontier : List Node) (node : Node) :
    node ∈ (((estimatorGuidance estimate prefer).scheduler goal base).reorder frontier) ↔
      node ∈ frontier :=
  Guidance.mem_scheduler_reorder_iff _ goal base

/-- Estimator guidance cannot weaken reachability soundness: emitted answers
and live occurrences still descend from the original roots. -/
theorem estimator_run_sound
    {Goal : Type uGoal} {Node : Type uNode} {Answer : Type uAnswer}
    {Score : Type uScore}
    (estimate : Goal → Node → Score)
    (prefer : Score → Score → Prop)
    (goal : Goal) (base : Scheduler Node)
    (system : BranchingSystem Node Answer) (roots : List Node) (fuel : Nat) :
    (Snapshot.run system
      ((estimatorGuidance estimate prefer).controller
        (Answer := Answer) goal base)
      fuel
      (Snapshot.initial
        ((estimatorGuidance estimate prefer).controller
          (Answer := Answer) goal base)
        roots)).search.Sound system roots :=
  Guidance.run_sound _ goal base system roots fuel

/-- If estimator-guided exploration completes, the answer bag is the exact
additive denotation of the original roots, independently of score values. -/
theorem estimator_completed_run_denotation
    {Goal : Type uGoal} {Node : Type uNode} {Answer : Type uAnswer}
    {Score : Type uScore}
    (estimate : Goal → Node → Score)
    (prefer : Score → Score → Prop)
    (goal : Goal) (base : Scheduler Node)
    (system : BranchingSystem Node Answer)
    (denotation : AdditiveDenotation system)
    (roots : List Node) (fuel : Nat)
    (complete :
      (Snapshot.run system
        ((estimatorGuidance estimate prefer).controller
          (Answer := Answer) goal base)
        fuel
        (Snapshot.initial
          ((estimatorGuidance estimate prefer).controller
            (Answer := Answer) goal base)
          roots)).search.frontier = []) :
    eventBag
        (Snapshot.run system
          ((estimatorGuidance estimate prefer).controller
            (Answer := Answer) goal base)
          fuel
          (Snapshot.initial
            ((estimatorGuidance estimate prefer).controller
              (Answer := Answer) goal base)
            roots)).search.events =
      foldValues denotation.value roots :=
  Guidance.completed_run_denotation _ goal base system denotation roots fuel
    complete

/-! ## Concrete ordering and truncation boundary -/

def toyEstimate : Unit → Bool → Nat
  | _, true => 9
  | _, false => 1

/-- Higher estimated utility genuinely moves the preferred live occurrence to
the front. -/
theorem higher_estimator_score_selected_first :
    selected
      ((estimatorGuidance toyEstimate (fun first second => second ≤ first)).scheduler
        () Scheduler.breadthFirst)
      [false, true] = some true := by
  simp only [selected, Guidance.scheduler, Scheduler.breadthFirst,
    List.insertionSort_cons, List.insertionSort_nil, List.orderedInsert_nil]
  rw [List.orderedInsert_of_not_le]
  · rfl
  · norm_num [Guidance.priorityAt, Guidance.estimateAt,
      estimatorGuidance, toyEstimate]

/-- Even a maximally scored absent candidate cannot be minted by the
estimator-guided scheduler. -/
theorem scored_absent_candidate_not_introduced :
    true ∉
      ((estimatorGuidance toyEstimate (fun first second => second ≤ first)).scheduler
        () Scheduler.breadthFirst).reorder [false, false] := by
  rw [mem_estimatorScheduler_reorder_iff]
  simp

/-- Top-one truncation is not occurrence-preserving on a two-candidate
frontier.  It therefore cannot be installed through the sound scheduler
interface without separate pruning/fairness evidence. -/
theorem topOne_truncation_is_not_occurrencePreserving :
    ¬ List.Perm ([true, false].take 1) [true, false] := by
  simp

#print axioms estimatorScheduler_reorder_perm
#print axioms mem_estimatorScheduler_reorder_iff
#print axioms estimator_run_sound
#print axioms estimator_completed_run_denotation
#print axioms higher_estimator_score_selected_first
#print axioms scored_absent_candidate_not_introduced
#print axioms topOne_truncation_is_not_occurrencePreserving

end Mettapedia.PLN.Bridges.GSLT.AlgorithmicCompressionGuidance
