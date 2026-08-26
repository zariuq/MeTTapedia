import Mettapedia.GSLT.Core.InferenceControl
import Mettapedia.GSLT.LanguageDef.CertificateGSLTFiniteTraceAuthority
import Mettapedia.Languages.MeTTa.PrimeNeedInferenceControl
import Mettapedia.PLN.InferenceControl.PremiseSelection.Fusion
import Mettapedia.PLN.WorldModel.BinaryWorldModel

/-!
# Evidence-guided, cost-aware inference control

PLN evidence and predicted cost may guide which live inference occurrence is
expanded next.  They do not authorize an inference edge and they do not state
the cost actually incurred.  This module makes that separation executable:

* `Guidance` retains evidence, predicted cost, and their policy projection as
  distinct data;
* `Guidance.scheduler` sorts only the live frontier and proves that the result
  is a permutation;
* generic GSLT soundness and answer-accounting therefore survive every such
  policy;
* a locally complete step authority can serialize the resulting controlled
  run as a finite NIK trace;
* on Prime's Need machine, the semantic work counter remains an exact clock,
  independently of the predicted cost used by the controller.

The controller is deliberately allowed to use an inaccurate estimate.  A bad
estimate may make search slow; it cannot mint a proof or alter a receipt.
-/

namespace Mettapedia.PLN.Bridges.GSLT.InferenceControl

open scoped Classical ENNReal

open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.InferenceControl.PremiseSelection

universe uGoal uNode uAnswer uEstimate uPriority uMemory uAuthority uCertificate
universe uState uQuery

noncomputable section

/-! ## A separated guidance record -/

/-- Evidence and predicted resource use are retained separately.  `rank` is a
policy projection used only for scheduling; neither input is thereby promoted
to semantic authority or an execution receipt. -/
structure Guidance
    (Goal : Type uGoal) (Node : Type uNode)
    (Estimate : Type uEstimate) (Priority : Type uPriority) where
  scorer : Scorer Goal Node
  estimate : Goal → Node → Estimate
  rank : BinaryEvidence → Estimate → Priority
  prefer : Priority → Priority → Prop

namespace Guidance

variable {Goal : Type uGoal} {Node : Type uNode}
variable {Estimate : Type uEstimate} {Priority : Type uPriority}

/-- The evidence retained for one candidate. -/
def evidenceAt (guidance : Guidance Goal Node Estimate Priority)
    (goal : Goal) (node : Node) : BinaryEvidence :=
  guidance.scorer.score goal node

/-- The predicted cost retained for one candidate.  This is not an execution
receipt. -/
def estimateAt (guidance : Guidance Goal Node Estimate Priority)
    (goal : Goal) (node : Node) : Estimate :=
  guidance.estimate goal node

/-- The policy-specific projection used to order candidates. -/
def priorityAt (guidance : Guidance Goal Node Estimate Priority)
    (goal : Goal) (node : Node) : Priority :=
  guidance.rank (guidance.evidenceAt goal node) (guidance.estimateAt goal node)

/-- Refine an existing scheduler by evidence/cost priority.  Only its frontier
reordering changes; its occurrence-preserving integration policy is retained.
The comparison need not be total or transitive for semantic soundness: those
properties affect search quality, while `perm_insertionSort` supplies the
load-bearing occurrence law. -/
def scheduler (guidance : Guidance Goal Node Estimate Priority)
    (goal : Goal) (base : Scheduler Node := Scheduler.breadthFirst) :
    Scheduler Node where
  reorder frontier :=
    List.insertionSort
      (fun first second =>
        guidance.prefer (guidance.priorityAt goal first)
          (guidance.priorityAt goal second))
      (base.reorder frontier)
  reorder_complete frontier :=
    (List.perm_insertionSort _ (base.reorder frontier)).trans
      (base.reorder_complete frontier)
  integrate := base.integrate
  integrate_complete := base.integrate_complete

/-- Evidence-guided ordering preserves every live occurrence exactly. -/
theorem scheduler_reorder_perm
    (guidance : Guidance Goal Node Estimate Priority)
    (goal : Goal) (base : Scheduler Node) (frontier : List Node) :
    List.Perm ((guidance.scheduler goal base).reorder frontier) frontier :=
  (guidance.scheduler goal base).reorder_complete frontier

/-- In particular, no high-scoring absent candidate can be introduced. -/
theorem mem_scheduler_reorder_iff
    (guidance : Guidance Goal Node Estimate Priority)
    (goal : Goal) (base : Scheduler Node)
    {frontier : List Node} {node : Node} :
    node ∈ (guidance.scheduler goal base).reorder frontier ↔
      node ∈ frontier :=
  Scheduler.mem_reorder_iff (guidance.scheduler goal base)

/-- Embed fixed-goal evidence guidance in the open stateful-controller
interface.  A later authored controller may update the goal/world in memory;
the semantic occurrence law remains the same at every state. -/
def controller {Answer : Type uAnswer}
    (guidance : Guidance Goal Node Estimate Priority)
    (goal : Goal) (base : Scheduler Node := Scheduler.breadthFirst) :
    Controller Node Answer Unit :=
  Controller.fixed (guidance.scheduler goal base)

/-- Stateful evidence guidance.  The controller memory may contain a current
world revision, goal, learned policy state, or any combination thereof.  At
each tick it chooses a fresh evidence/cost ordering, while `scheduler` proves
that the chosen ordering remains occurrence-preserving. -/
def statefulController {Answer : Type uAnswer} {Memory : Type uMemory}
    (guidance : Guidance Goal Node Estimate Priority)
    (initialMemory : Memory) (goalAt : Memory → Goal)
    (baseAt : Memory → Scheduler Node)
    (advance : Memory → Node → Option Answer → List Node → Memory) :
    Controller Node Answer Memory where
  initialMemory := initialMemory
  scheduler memory := guidance.scheduler (goalAt memory) (baseAt memory)
  advance := advance

/-- Changing the world/goal and ranking policy through controller memory still
cannot authorize an unreachable occurrence. -/
theorem stateful_run_sound {Answer : Type uAnswer} {Memory : Type uMemory}
    (guidance : Guidance Goal Node Estimate Priority)
    (initialMemory : Memory) (goalAt : Memory → Goal)
    (baseAt : Memory → Scheduler Node)
    (advance : Memory → Node → Option Answer → List Node → Memory)
    (system : BranchingSystem Node Answer) (roots : List Node) (fuel : Nat) :
    (Snapshot.run system
      (guidance.statefulController initialMemory goalAt baseAt advance) fuel
      (Snapshot.initial
        (guidance.statefulController initialMemory goalAt baseAt advance)
        roots)).search.Sound system roots := by
  exact Snapshot.sound_run system _
    (Mettapedia.GSLT.Core.BranchingTemporal.initial_sound system roots) fuel

/-! ## Semantic preservation -/

/-- Evidence and estimated cost can guide exploration without weakening the
branching system's reachability invariant. -/
theorem run_sound
    (guidance : Guidance Goal Node Estimate Priority)
    (goal : Goal) (base : Scheduler Node)
    (system : BranchingSystem Node Answer) (roots : List Node) (fuel : Nat) :
    (Snapshot.run system (guidance.controller (Answer := Answer) goal base) fuel
      (Snapshot.initial (guidance.controller (Answer := Answer) goal base)
        roots)).search.Sound system roots := by
  exact Snapshot.sound_run system _
    (Mettapedia.GSLT.Core.BranchingTemporal.initial_sound system roots) fuel

/-- If guided exploration completes, its answer bag is the denotation of the
initial roots, independently of evidence values, estimates, and policy order. -/
theorem completed_run_denotation
    (guidance : Guidance Goal Node Estimate Priority)
    (goal : Goal) (base : Scheduler Node)
    (system : BranchingSystem Node Answer)
    (denotation : AdditiveDenotation system)
    (roots : List Node) (fuel : Nat)
    (complete :
      (Snapshot.run system
        (guidance.controller (Answer := Answer) goal base) fuel
        (Snapshot.initial (guidance.controller (Answer := Answer) goal base)
          roots)).search.frontier = []) :
    eventBag
        (Snapshot.run system
          (guidance.controller (Answer := Answer) goal base) fuel
          (Snapshot.initial (guidance.controller (Answer := Answer) goal base)
            roots)).search.events =
      foldValues denotation.value roots := by
  exact Snapshot.completed_run_denotation system _ denotation roots fuel complete

/-- Every live bounded guided run is an ordinary derivation in the generated
control GSLT.  This is the semantic input consumed by finite-trace authority. -/
theorem run_multistep
    (guidance : Guidance Goal Node Estimate Priority)
    (goal : Goal) (base : Scheduler Node)
    (system : BranchingSystem Node Answer) (fuel : Nat)
    (snapshot : Snapshot Node Answer Unit)
    (live : Snapshot.LiveThrough system
      (guidance.controller (Answer := Answer) goal base) fuel snapshot) :
    (Snapshot.toGSLT system
      (guidance.controller (Answer := Answer) goal base)).MultiStep snapshot
        (Snapshot.run system
          (guidance.controller (Answer := Answer) goal base) fuel snapshot) :=
  Snapshot.run_multistep system _ fuel snapshot live

/-! ## NIK finite-trace closure -/

/-- If the generated control GSLT has a locally complete step authority, every
live bounded evidence-guided run has an accepted finite NIK trace article.
Evidence guidance discovers the run; the local authority, not the guidance,
justifies each edge. -/
theorem exists_accepted_finite_trace
    [DecidableEq Node] [DecidableEq Answer]
    (guidance : Guidance Goal Node Estimate Priority)
    (goal : Goal) (base : Scheduler Node)
    (system : BranchingSystem Node Answer) (fuel : Nat)
    (snapshot : Snapshot Node Answer Unit)
    (live : Snapshot.LiveThrough system
      (guidance.controller (Answer := Answer) goal base) fuel snapshot)
    (stepAuthority : StepAuthority.{uAuthority, uCertificate} AuthorityId
      (Snapshot.toGSLT system
        (guidance.controller (Answer := Answer) goal base)))
    (stepComplete : stepAuthority.Complete) :
    let claim : TraceClaim
        (Snapshot.toGSLT system
          (guidance.controller (Answer := Answer) goal base)) :=
      { source := snapshot
        target := Snapshot.run system
          (guidance.controller (Answer := Answer) goal base) fuel snapshot }
    ∃ certificate : (finiteTraceAuthority stepAuthority).Certificate,
      (finiteTraceAuthority stepAuthority).check claim certificate = true := by
  intro claim
  apply (finiteTraceAuthority_correspondence stepAuthority stepComplete claim).2
  exact run_multistep guidance goal base system fuel snapshot live

end Guidance

/-! ## Direct world-model evidence guidance -/

namespace WorldModel

open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.WorldModel.PLNWorldModel

variable {State : Type uState} {Query : Type uQuery} {Node : Type uNode}

/-- View a revisable binary world model as a PLN inference-control scorer.
Each live node declares the world-model query whose evidence guides its
priority. -/
def scorer [EvidenceType State] [BinaryWorldModel State Query]
    (queryOf : Node → Query) : Scorer State Node where
  score world node :=
    BinaryWorldModel.evidence (State := State) (Query := Query)
      world (queryOf node)

/-- Search evidence follows the already-admitted PLN revision algebra exactly.
This is the bridge from evolving world content to inference control. -/
theorem scorer_revision
    [EvidenceType State] [BinaryWorldModel State Query]
    (queryOf : Node → Query) (left right : State) (node : Node) :
    (scorer queryOf).score (left + right) node =
      (scorer queryOf).score left node + (scorer queryOf).score right node := by
  exact BinaryWorldModel.evidence_add left right (queryOf node)

/-- Construct guidance whose evidence channel is the formal world-model query
projection.  Estimated cost and policy ranking remain independent parameters. -/
def guidance [EvidenceType State] [BinaryWorldModel State Query]
    {Estimate : Type uEstimate} {Priority : Type uPriority}
    (queryOf : Node → Query) (estimate : State → Node → Estimate)
    (rank : BinaryEvidence → Estimate → Priority)
    (prefer : Priority → Priority → Prop) :
    Guidance State Node Estimate Priority where
  scorer := scorer queryOf
  estimate := estimate
  rank := rank
  prefer := prefer

@[simp] theorem guidance_evidenceAt_revision
    [EvidenceType State] [BinaryWorldModel State Query]
    {Estimate : Type uEstimate} {Priority : Type uPriority}
    (queryOf : Node → Query) (estimate : State → Node → Estimate)
    (rank : BinaryEvidence → Estimate → Priority)
    (prefer : Priority → Priority → Prop)
    (left right : State) (node : Node) :
    (guidance queryOf estimate rank prefer).evidenceAt (left + right) node =
      (guidance queryOf estimate rank prefer).evidenceAt left node +
        (guidance queryOf estimate rank prefer).evidenceAt right node := by
  exact scorer_revision queryOf left right node

end WorldModel

/-! ## Prime specialization: estimate versus receipt -/

namespace Prime

open Mettapedia.Languages.MeTTa.PrimeNeedInferenceControl
open Mettapedia.Languages.MeTTa.PrimeNeedReference

variable {Goal : Type uGoal} {Estimate : Type uEstimate}
variable {Priority : Type uPriority}
variable {Origin Local Resume Rule Value StableFault RetryableFault Effect : Type*}

/-- A PLN/cost-guided Prime emission retains both its exact semantic execution
path and the transition-clock receipt.  The theorem quantifies over arbitrary
predicted-cost carriers and ranking policies, so even a wrong estimate cannot
alter the actual account. -/
theorem controlled_emission_has_proof_and_exact_cost
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (guidance : Guidance Goal
      (WorkOccurrence
        (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect))
      Estimate Priority)
    (goal : Goal)
    (base : Scheduler
      (WorkOccurrence
        (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)))
    (initial :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (fuel : Nat)
    {event : Emission
      (WorkOccurrence
        (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect))
      (Produced Value StableFault RetryableFault × List Nat)}
    (member : event ∈
      (Snapshot.run (Reference.occurrenceSystem spec)
        (guidance.controller
          (Answer := Produced Value StableFault RetryableFault × List Nat)
          goal base)
        fuel
        (Snapshot.initial
          (guidance.controller
            (Answer := Produced Value StableFault RetryableFault × List Nat)
            goal base)
          [WorkOccurrence.root initial])).search.events) :
    Steps spec event.origin.trace.length initial event.origin.state ∧
      event.origin.state.work.transitions =
        initial.work.transitions + event.origin.trace.length ∧
      haltedOutcome event.origin.state = some event.value.1 ∧
      event.value.2 = event.origin.trace := by
  have semantic := Reference.controlled_emission_has_steps spec
    (guidance.controller
      (Answer := Produced Value StableFault RetryableFault × List Nat)
      goal base)
    initial fuel member
  exact ⟨semantic.1, Steps.transitions_eq spec semantic.1,
    semantic.2.1, semantic.2.2⟩

end Prime

/-! ## Separating witnesses -/

namespace Examples

/-- A tiny PLN scorer that gives `true` more positive evidence. -/
def boolScorer : Scorer Unit Bool where
  score _ candidate :=
    if candidate then ⟨2, 0⟩ else ⟨1, 0⟩

/-- Deliberately bad estimates: the evidence-favored candidate is predicted
to be much more expensive.  Soundness must not depend on their accuracy. -/
def badEstimate : Unit → Bool → Nat
  | _, true => 100
  | _, false => 0

def boolGuidance : Guidance Unit Bool Nat ENNReal where
  scorer := boolScorer
  estimate := badEstimate
  rank := fun evidence _ => evidence.pos
  prefer := fun first second => second ≤ first

/-- A second lawful policy prioritizes lower predicted cost.  It retains the
same PLN evidence, demonstrating that evidence and cost projections are not
silently identified. -/
def estimatedCostGuidance : Guidance Unit Bool Nat Nat where
  scorer := boolScorer
  estimate := badEstimate
  rank := fun _ estimate => estimate
  prefer := fun first second => first ≤ second

/-- Positive: the concrete PLN score genuinely controls which live occurrence
is selected first. -/
theorem higher_evidence_selected_first :
    Mettapedia.GSLT.Core.BranchingTemporal.selected
      (boolGuidance.scheduler () Scheduler.breadthFirst) [false, true] =
        some true := by
  simp only [Mettapedia.GSLT.Core.BranchingTemporal.selected,
    Guidance.scheduler, Scheduler.breadthFirst, List.insertionSort_cons,
    List.insertionSort_nil, List.orderedInsert_nil]
  rw [List.orderedInsert_of_not_le]
  · rfl
  · norm_num [Guidance.priorityAt, Guidance.evidenceAt, boolGuidance,
      boolScorer]

/-- Positive: a policy may instead use the independent estimated-cost channel.
Here the deliberately wrong estimate sends `false` first; subsequent semantic
and receipt theorems remain unchanged. -/
theorem lower_estimated_cost_selected_first :
    Mettapedia.GSLT.Core.BranchingTemporal.selected
      (estimatedCostGuidance.scheduler () Scheduler.breadthFirst)
      [true, false] = some false := by
  simp only [Mettapedia.GSLT.Core.BranchingTemporal.selected,
    Guidance.scheduler, Scheduler.breadthFirst, List.insertionSort_cons,
    List.insertionSort_nil, List.orderedInsert_nil]
  rw [List.orderedInsert_of_not_le]
  · rfl
  · norm_num [Guidance.priorityAt, Guidance.estimateAt,
      estimatedCostGuidance, badEstimate]

/-- Positive: evidence-guided ordering retains both duplicate occurrences. -/
theorem duplicate_occurrences_preserved :
    ((boolGuidance.scheduler () Scheduler.breadthFirst).reorder
      [true, false, true]).count true = 2 := by
  have permutation := boolGuidance.scheduler_reorder_perm ()
    Scheduler.breadthFirst [true, false, true]
  exact List.Perm.count_eq permutation true

/-- Negative: even a candidate with defined evidence and estimated cost cannot
appear unless it was a live occurrence. -/
theorem absent_candidate_not_introduced :
    false ∉
      (boolGuidance.scheduler () Scheduler.breadthFirst).reorder [true, true] := by
  rw [boolGuidance.mem_scheduler_reorder_iff () Scheduler.breadthFirst]
  simp

end Examples

#print axioms Guidance.scheduler_reorder_perm
#print axioms Guidance.stateful_run_sound
#print axioms Guidance.run_sound
#print axioms Guidance.completed_run_denotation
#print axioms Guidance.exists_accepted_finite_trace
#print axioms WorldModel.scorer_revision
#print axioms WorldModel.guidance_evidenceAt_revision
#print axioms Prime.controlled_emission_has_proof_and_exact_cost
#print axioms Examples.duplicate_occurrences_preserved
#print axioms Examples.higher_evidence_selected_first
#print axioms Examples.lower_estimated_cost_selected_first
#print axioms Examples.absent_candidate_not_introduced

end

end Mettapedia.PLN.Bridges.GSLT.InferenceControl
