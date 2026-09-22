import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.ProofPlanning
import Mettapedia.Logic.ProofSearch.Planning
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerSemantics
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerUniformListSemantics
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.UniformListChartProofSyntax
import Mettapedia.Logic.HOL.TypeSubstitutionDerivation
import Mettapedia.GSLT.Core.OperationalPathFibration

/-! # HOL compilation and concrete proof-planning developments -/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
set_option autoImplicit false
namespace Mettapedia.Logic.ProofSearch
universe u v w x y z

/-! ## HOL adapter -/


/-! ## A retained List proof-strategy workload

This finite transition system selects retained proof objects; it does not
reconstruct their trees by backward search. BoundedHOLProofPlanning supplies
the separate algorithmic search instance of this same planning interface.
-/

namespace UniformListPlan

open Presentation
open Mettapedia.Logic HOL HOL.UniformListInduction HOL.UniformListInductionChart
open UniformListChartProofSyntax
open HOLNativeGenericProofCompiler

def goal : HOLAdapter.Goal BaseSort Symbol where
  context := []
  hypotheses := theory (Γ := [])
  conclusion := mapLength

abbrev Proof := HOLAdapter.Solution goal

inductive Constraint where
  | repairRejectedCertificate

inductive State where
  | ready
  | directQueued
  | detourPrepared
  | detourQueued
  | directSolved
  | detourSolved
  | needsRepair
  | outOfFuel

inductive Step : State → State → Type where
  | chooseDirect : Step .ready .directQueued
  | prepareDetour : Step .ready .detourPrepared
  | queueDetour : Step .detourPrepared .detourQueued
  | acceptDirect : Step .directQueued .directSolved
  | acceptDetour : Step .detourQueued .detourSolved
  | rejectMalformed : Step .ready .needsRepair
  | exhaustZeroBudget : Step .ready .outOfFuel

def observe : State → Option
    (Outcome HOLAdapter.Solution HOLAdapter.noCounter (fun _ => Constraint) goal)
  | .directSolved => some (.solved (actualProof []))
  | .detourSolved => some (.solved (detouredProof []))
  | .needsRepair => some (.constrained ⟨.repairRejectedCertificate, []⟩)
  | .outOfFuel => some (.exhausted (.budget 0 0 (Nat.le_refl 0)))
  | _ => none

def plan : System HOLAdapter.Solution HOLAdapter.noCounter (fun _ => Constraint) goal where
  State := State
  initial := .ready
  Step := Step
  observe := observe

/-- The concrete cost vector keeps unlike resources in separate components. -/
@[ext] structure WorkCost where
  searchSteps : Nat
  certificateChecks : Nat
  proofNodes : Nat
  compilationSteps : Nat
  executionSteps : Nat
  deriving DecidableEq, Repr

def workZero : WorkCost := ⟨0, 0, 0, 0, 0⟩

def workAdd (left right : WorkCost) : WorkCost :=
  ⟨left.searchSteps + right.searchSteps,
    left.certificateChecks + right.certificateChecks,
    left.proofNodes + right.proofNodes,
    left.compilationSteps + right.compilationSteps,
    left.executionSteps + right.executionSteps⟩

instance workCostZero : Zero WorkCost := ⟨workZero⟩

instance workCostAdd : Add WorkCost := ⟨workAdd⟩

@[simp] theorem workCost_zero_eq : (0 : WorkCost) = workZero := rfl

@[simp] theorem workCost_add_eq (left right : WorkCost) :
    left + right = workAdd left right := rfl

instance : AddMonoid WorkCost where
  zero_add value := by
    change workAdd workZero value = value
    cases value
    simp [workAdd, workZero]
  add_zero value := by
    change workAdd value workZero = value
    cases value
    simp [workAdd, workZero]
  add_assoc first second third := by
    change workAdd (workAdd first second) third =
      workAdd first (workAdd second third)
    cases first
    cases second
    cases third
    simp [workAdd, Nat.add_assoc]
  nsmul := nsmulRec

def cost : @System.CostModel (HOLAdapter.Goal BaseSort Symbol)
    HOLAdapter.Solution HOLAdapter.noCounter (fun _ => Constraint) goal
    plan WorkCost inferInstance where
  charge := fun {_ _} step =>
    match step with
    | .chooseDirect => ⟨1, 0, 0, 0, 0⟩
    | .prepareDetour => ⟨1, 0, 0, 0, 0⟩
    | .queueDetour => ⟨1, 0, 0, 0, 0⟩
    | .acceptDirect => ⟨1, 1, (actualProof []).nodeCount, 0, 0⟩
    | .acceptDetour => ⟨1, 1, (detouredProof []).nodeCount, 0, 0⟩
    | .rejectMalformed => ⟨1, 1, 0, 0, 0⟩
    | .exhaustZeroBudget => 0

def directTrace : plan.Trace plan.initial .directSolved :=
  .cons .chooseDirect (.cons .acceptDirect (.nil _))

def detourTrace : plan.Trace plan.initial .detourSolved :=
  .cons .prepareDetour (.cons .queueDetour (.cons .acceptDetour (.nil _)))

def constrainedTrace : plan.Trace plan.initial .needsRepair :=
  .cons .rejectMalformed (.nil _)

def exhaustedTrace : plan.Trace plan.initial .outOfFuel :=
  .cons .exhaustZeroBudget (.nil _)

theorem direct_certificate_checked :
    produce? [] (UniformListChartNIKService.actualRequest []) = some (actualProof []) :=
  actual_produced []

theorem detoured_certificate_checked :
    produce? [] (detouredRequest []) = some (detouredProof []) :=
  detoured_produced []

theorem malformed_is_constraint_not_refutation : produce? []
    { UniformListChartNIKService.actualRequest [] with
      stepProof := malformedCertificate [] } = none :=
  malformed_rejected []

theorem direct_cost : cost.total directTrace = ⟨2, 1, 50, 0, 0⟩ := by
  apply WorkCost.ext <;>
    simp [System.CostModel.total, directTrace, cost, actual_tree_nodes,
      workAdd, workZero]

theorem detour_cost : cost.total detourTrace = ⟨3, 1, 52, 0, 0⟩ := by
  apply WorkCost.ext <;>
    simp [System.CostModel.total, detourTrace, cost, detoured_tree_nodes,
      workAdd, workZero]

theorem same_goal_different_retained_proofs :
    (actualProof [] : Proof) ≠ detouredProof [] :=
  retained_strategies_distinct

theorem same_admission_different_cost :
    (actualProof []).intrinsicAdmission = (detouredProof []).intrinsicAdmission ∧
      cost.total directTrace ≠ cost.total detourTrace := by
  constructor
  · exact same_intrinsic_admission []
  · rw [direct_cost, detour_cost]
    intro equal
    have := congrArg WorkCost.proofNodes equal
    norm_num at this

theorem constrained_observed :
    plan.observe .needsRepair =
      some (.constrained ⟨.repairRejectedCertificate, []⟩) := rfl

theorem exhausted_observed :
    plan.observe .outOfFuel =
      some (.exhausted (.budget 0 0 (Nat.le_refl 0))) := rfl

def directOutcome :
    Outcome HOLAdapter.Solution HOLAdapter.noCounter (fun _ => Constraint) goal :=
  .solved (actualProof [])

def detourOutcome :
    Outcome HOLAdapter.Solution HOLAdapter.noCounter (fun _ => Constraint) goal :=
  .solved (detouredProof [])

theorem direct_outcome_observed :
    plan.observe .directSolved = some directOutcome := rfl

theorem detour_outcome_observed :
    plan.observe .detourSolved = some detourOutcome := rfl

def directRun : System.Run plan directOutcome where
  final := .directSolved
  trace := directTrace
  observed := direct_outcome_observed

def detourRun : System.Run plan detourOutcome where
  final := .detourSolved
  trace := detourTrace
  observed := detour_outcome_observed

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem direct_compiles :
    (compile FormationSensitiveHOLLeibnizInterface.signature
      UniformList.proofName UniformList.operations (actualProof [])
      (n := 5) Fin.elim0 (fun index => .var index)).isSome = true := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem detour_compiles :
    (compile FormationSensitiveHOLLeibnizInterface.signature
      UniformList.proofName UniformList.operations (detouredProof [])
      (n := 5) Fin.elim0 (fun index => .var index)).isSome = true := by
  decide

def directNative : Tower.Tm 5 :=
  (compile FormationSensitiveHOLLeibnizInterface.signature
    UniformList.proofName UniformList.operations (actualProof [])
    (n := 5) Fin.elim0 (fun index => .var index)).get direct_compiles

def detourNative : Tower.Tm 5 :=
  (compile FormationSensitiveHOLLeibnizInterface.signature
    UniformList.proofName UniformList.operations (detouredProof [])
    (n := 5) Fin.elim0 (fun index => .var index)).get detour_compiles

theorem compiler_emits_direct :
    compile FormationSensitiveHOLLeibnizInterface.signature
      UniformList.proofName UniformList.operations (actualProof [])
      Fin.elim0 (fun index => .var index) = some directNative :=
  (Option.some_get direct_compiles).symm

theorem compiler_emits_detour :
    compile FormationSensitiveHOLLeibnizInterface.signature
      UniformList.proofName UniformList.operations (detouredProof [])
      Fin.elim0 (fun index => .var index) = some detourNative :=
  (Option.some_get detour_compiles).symm

theorem direct_outcome_compiles :
    HOLAdapter.compileOutcome?
      FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
      UniformList.operations directOutcome Fin.elim0 (fun index => .var index) =
        some directNative := by
  exact compiler_emits_direct

theorem detour_outcome_compiles :
    HOLAdapter.compileOutcome?
      FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
      UniformList.operations detourOutcome Fin.elim0 (fun index => .var index) =
        some detourNative := by
  exact compiler_emits_detour

def searchStage : Stage Unit
    (Outcome HOLAdapter.Solution HOLAdapter.noCounter (fun _ => Constraint) goal) :=
  plan.completionStage

def searchCost : Stage.Cost searchStage WorkCost :=
  System.completionCost cost

def compileStage : Stage
    (Outcome HOLAdapter.Solution HOLAdapter.noCounter (fun _ => Constraint) goal)
    (Tower.Tm 5) :=
  HOLAdapter.compilationStage FormationSensitiveHOLLeibnizInterface.signature
    UniformList.proofName UniformList.operations 5 Fin.elim0
      (fun index => .var index)

def compileCost : Stage.Cost compileStage WorkCost where
  charge _ := ⟨0, 0, 0, 1, 0⟩

def pipelineStage : Stage Unit (Tower.Tm 5) :=
  searchStage.comp compileStage

def pipelineCost : Stage.Cost pipelineStage WorkCost :=
  searchCost.comp compileCost

def directPipelineEvidence : pipelineStage.Evidence () directNative :=
  ⟨directOutcome, directRun, ⟨direct_outcome_compiles⟩⟩

def detourPipelineEvidence : pipelineStage.Evidence () detourNative :=
  ⟨detourOutcome, detourRun, ⟨detour_outcome_compiles⟩⟩

theorem direct_pipeline_cost :
    pipelineCost.charge directPipelineEvidence = ⟨2, 1, 50, 1, 0⟩ := by
  rw [show pipelineCost.charge directPipelineEvidence =
      cost.total directTrace + ⟨0, 0, 0, 1, 0⟩ by rfl]
  rw [direct_cost]
  rfl

theorem detour_pipeline_cost :
    pipelineCost.charge detourPipelineEvidence = ⟨3, 1, 52, 1, 0⟩ := by
  rw [show pipelineCost.charge detourPipelineEvidence =
      cost.total detourTrace + ⟨0, 0, 0, 1, 0⟩ by rfl]
  rw [detour_cost]
  rfl

/-- Operational cost extends the same vector only from an actual finite GSLT
execution path. -/
def executionCost (system : Mettapedia.GSLT.GSLT.{0}) :
    Stage.Cost (OperationalAdapter.executionStage system) WorkCost where
  charge path := ⟨0, 0, 0, 0, path.length⟩

@[simp] theorem executionCost_charge
    {system : Mettapedia.GSLT.GSLT.{0}} {source target : system.Term}
    (path : Mettapedia.GSLT.IndexedOperational.ExecutionPath system source target) :
    (executionCost system).charge path = ⟨0, 0, 0, 0, path.length⟩ := rfl

theorem directNative_denotes (a : ZFSet.{u}) :
    UniformListSemantics.Denotes a
      (UniformListSemantics.Controls.assumptionState a (theory (Γ := [])))
      directNative mapLength := by
  exact HOLAdapter.compileOutcome_denotes
    FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
    UniformList.operations (UniformListSemantics.algebra a) directOutcome
    direct_outcome_compiles
    (UniformListSemantics.Controls.assumptionState a (theory (Γ := [])))
    (UniformListSemantics.Controls.assumptionHypotheses a (theory (Γ := [])))

theorem detourNative_denotes (a : ZFSet.{u}) :
    UniformListSemantics.Denotes a
      (UniformListSemantics.Controls.assumptionState a (theory (Γ := [])))
      detourNative mapLength := by
  exact HOLAdapter.compileOutcome_denotes
    FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
    UniformList.operations (UniformListSemantics.algebra a) detourOutcome
    detour_outcome_compiles
    (UniformListSemantics.Controls.assumptionState a (theory (Γ := [])))
    (UniformListSemantics.Controls.assumptionHypotheses a (theory (Γ := [])))

end UniformListPlan

/-! ## A real checked refutation -/

namespace CountermodelPlan

open Mettapedia.Logic HOL HOL.TypeSubstitutionExample

abbrev Goal := Unit
abbrev Solution (_ : Goal) :=
  HOL.ProofSyntax (NoConstants Bool) [] sourceClaim

inductive Certificate where
  | separatingModel

def counter : CounterSystem Goal Solution where
  Certificate := fun _ => Certificate
  check := fun _ => true
  sound := by
    intro goal certificate accepted proof
    exact sourceClaim_not_provable proof.erase

inductive Constraint

inductive State where
  | ready
  | refuted

inductive Step : State → State → Type where
  | checkCountermodel : Step .ready .refuted

def observe : State → Option (Outcome Solution counter (fun _ => Constraint) ())
  | .ready => none
  | .refuted => some (.refuted .separatingModel rfl)

def plan : System Solution counter (fun _ => Constraint) () where
  State := State
  initial := .ready
  Step := Step
  observe := observe

def trace : plan.Trace plan.initial .refuted :=
  .cons .checkCountermodel (.nil _)

theorem checked_refutation_observed :
    plan.observe .refuted = some (.refuted .separatingModel rfl) := rfl

theorem checked_refutation_excludes_solution : ¬ Nonempty (Solution ()) := by
  rintro ⟨proof⟩
  exact counter.sound (certificate := .separatingModel) rfl proof

end CountermodelPlan

#print axioms System.CostModel.total_append
#print axioms HOLAdapter.compileOutcome_denotes
#print axioms UniformListPlan.same_admission_different_cost
#print axioms UniformListPlan.directNative_denotes
#print axioms UniformListPlan.detourNative_denotes
#print axioms UniformListPlan.direct_pipeline_cost
#print axioms UniformListPlan.detour_pipeline_cost
#print axioms CountermodelPlan.checked_refutation_excludes_solution

end Mettapedia.Logic.ProofSearch
