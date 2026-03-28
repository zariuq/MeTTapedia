import Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservationPath
import Mettapedia.Logic.MarkovLogicTrustTriangleExample

/-!
# Concrete Example: Proof-Backed Meta-Goal Shell Preservation

This module instantiates the abstract path theorem from
`MetaGoalShellPreservationPath.lean` with a small concrete example.

On the Gödel-machine side we use a tiny proof system whose provability predicate
is just truth, so proof-backed utility improvements are easy to witness.

On the Markov-logic side we reuse the trust-triangle example:
- the protected WM goal is the query on agent `1`,
- the triangle `{0,1,2}` is the protected semantic core,
- the disconnected chain weight is rewritten twice.

The resulting two-step path shows:
- expected utility strictly improves along the rewrite path, and
- the protected WM goal stays within the cumulative shell bound.

This is deliberately small.  The point is to exercise the bridge honestly,
not to overfit a larger self-modifying agent before the surrounding
Gödel-machine layer is complete.
-/

namespace Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservationExample

open Mettapedia.UniversalAI.BayesianAgents
open Mettapedia.UniversalAI.SelfModification
open Mettapedia.UniversalAI.GodelMachine
open Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservation
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicDynamicTranscendence
open Mettapedia.Logic.MarkovLogicDynamicIndividuation
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteVariableNeighborhoodWorldOfViews
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicOntologyGrowth
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicAbstract.MassState
open Mettapedia.Logic.MarkovLogicTrustTriangleExample
open MeasureTheory

/-- A minimal truth-based formal system.  A statement is provable exactly when
it is true.  This is only for a concrete bridge example. -/
def truthFormalSystem : FormalSystem where
  axioms := ∅
  provable := fun φ => φ
  sound := by
    intro φ hφ
    exact hφ
  axioms_provable := by
    intro φ hφ
    simp at hφ
  modus_ponens := by
    intro φ ψ hφ himp
    exact himp hφ
  provable_true := trivial

/-- A deterministic environment concentrating all mass on one fixed percept. -/
def deterministicEnv : EnvProb := fun _ x =>
  if x = Percept.mk false false then 1 else 0

/-- A constant policy that always stays put and keeps the same policy name. -/
def constantPolicy : SelfModPolicy := fun _ =>
  ⟨Action.stay, 0⟩

/-- The corresponding constant interpreter. -/
def constantPolicyInterp : PolicyInterpreter := fun _ => constantPolicy

/-- Zero discount keeps the example arithmetic simple. -/
def zeroDiscount : DiscountFactor :=
  ⟨0, by norm_num, by norm_num⟩

/-- Constant utility with value `r`. -/
def constantUtility (r : ℝ) : Utility := fun _ => r

/-- A tiny Gödel-machine state with constant utility `r`. -/
def toyMachine (r : ℝ) : GodelMachineState where
  policy := constantPolicy
  utility := constantUtility r
  formalSystem := truthFormalSystem
  envProb := deterministicEnv
  policyInterp := constantPolicyInterp
  γ := zeroDiscount
  horizon := 1

theorem expectedUtilityFromStart_toyMachine (r : ℝ) :
    expectedUtilityFromStart (toyMachine r) = r := by
  simp [expectedUtilityFromStart, expectedUtility, toyMachine,
    GodelMachineState.toRealisticValueData, vValueRealistic, qValueRealistic,
    constantPolicy, constantUtility, deterministicEnv, zeroDiscount,
    History.wellFormed]

theorem toyMachine_validModification_of_lt {r s : ℝ} (hrs : r < s) :
    validModification (toyMachine r) (toyMachine s) := by
  change expectedUtilityFromStart (toyMachine s) >
      expectedUtilityFromStart (toyMachine r)
  simpa [expectedUtilityFromStart_toyMachine r,
    expectedUtilityFromStart_toyMachine s] using hrs

/-- Common protected goal family for the trust triangle: just the agent-1 query. -/
def trustTriangleProtectedGoals : ProtectedWMGoals coreTriangle where
  goals := {agent1Query}
  supported := by
    intro q hq
    simp at hq
    subst hq
    exact agent1Query_supported

/-- The boundary condition used for existence witnesses in the example. -/
def falseBoundary : BoundaryCondition Nat := fun _ => false

/-- Fixed triangle weight for the example. -/
noncomputable def trustWt : ℝ := 1 / 4

/-- Three chain weights along the rewrite path. -/
noncomputable def trustChain₀ : ℝ := 1 / 10
noncomputable def trustChain₁ : ℝ := 1 / 5
noncomputable def trustChain₂ : ℝ := 3 / 10

theorem trustWt_small : |trustWt| < 1 / 2 := by
  norm_num [trustWt]

theorem trustChain₀_small : |trustChain₀| < 1 / 2 := by
  norm_num [trustChain₀]

theorem trustChain₁_small : |trustChain₁| < 1 / 2 := by
  norm_num [trustChain₁]

theorem trustChain₂_small : |trustChain₂| < 1 / 2 := by
  norm_num [trustChain₂]

/-- First semantic shell-preservation step: rewrite the disconnected chain from
`trustChain₀` to `trustChain₁`. -/
noncomputable def trustTriangleSemanticStep₀₁ :
    DynamicTranscendenceStep
      (triangleChainSpec trustWt trustChain₀)
      (triangleChainSpec trustWt trustChain₁) where
  queryRegion := coreTriangle
  shellDepth := 0
  shell_agreement := specs_agree_on_triangle trustWt trustChain₀ trustChain₁
  budget₁ := triangleChainSpec_budget trustWt trustChain₀ trustWt_small trustChain₀_small
  budget₂ := triangleChainSpec_budget trustWt trustChain₁ trustWt_small trustChain₁_small

/-- Second semantic shell-preservation step: rewrite the disconnected chain from
`trustChain₁` to `trustChain₂`. -/
noncomputable def trustTriangleSemanticStep₁₂ :
    DynamicTranscendenceStep
      (triangleChainSpec trustWt trustChain₁)
      (triangleChainSpec trustWt trustChain₂) where
  queryRegion := coreTriangle
  shellDepth := 0
  shell_agreement := specs_agree_on_triangle trustWt trustChain₁ trustChain₂
  budget₁ := triangleChainSpec_budget trustWt trustChain₁ trustWt_small trustChain₁_small
  budget₂ := triangleChainSpec_budget trustWt trustChain₂ trustWt_small trustChain₂_small

/-- First proof-backed rewrite step. -/
noncomputable def trustTriangleMetaStep₀₁ :
    MetaGoalShellPreservationStep (Atom := Nat) (ClauseId := VarNClauseId) where
  oldMachine := toyMachine 0
  newMachine := toyMachine 1
  oldSpec := triangleChainSpec trustWt trustChain₀
  newSpec := triangleChainSpec trustWt trustChain₁
  semanticStep := trustTriangleSemanticStep₀₁
  protectedGoals := trustTriangleProtectedGoals
  proofBacked := toyMachine_validModification_of_lt (by norm_num)

/-- Second proof-backed rewrite step. -/
noncomputable def trustTriangleMetaStep₁₂ :
    MetaGoalShellPreservationStep (Atom := Nat) (ClauseId := VarNClauseId) where
  oldMachine := toyMachine 1
  newMachine := toyMachine 2
  oldSpec := triangleChainSpec trustWt trustChain₁
  newSpec := triangleChainSpec trustWt trustChain₂
  semanticStep := trustTriangleSemanticStep₁₂
  protectedGoals := trustTriangleProtectedGoals
  proofBacked := toyMachine_validModification_of_lt (by norm_num)

/-- Two-step path of proof-backed rewrites with the same protected WM goal. -/
noncomputable def trustTriangleMetaGoalPath :
    MetaGoalShellPreservationPath (Atom := Nat) (ClauseId := VarNClauseId)
      trustTriangleProtectedGoals.goals :=
  .step (.single trustTriangleMetaStep₀₁
      (by
        intro q hq
        simpa [trustTriangleMetaStep₀₁, trustTriangleProtectedGoals] using hq))
    trustTriangleMetaStep₁₂
      (by
        intro q hq
        simpa [trustTriangleMetaStep₁₂, trustTriangleProtectedGoals] using hq)

theorem trustTriangleMetaGoalPath_coherent :
    trustTriangleMetaGoalPath.Coherent := by
  simp [trustTriangleMetaGoalPath, MetaGoalShellPreservationPath.Coherent,
    MetaGoalShellPreservationPath.endMachine, MetaGoalShellPreservationPath.endSpec,
    trustTriangleMetaStep₀₁, trustTriangleMetaStep₁₂]

theorem trustTriangleMetaStep₀₁_errorBound :
    trustTriangleMetaStep₀₁.errorBound = 6 := by
  rw [MetaGoalShellPreservationStep.errorBound]
  simp [trustTriangleMetaStep₀₁, trustTriangleSemanticStep₀₁, coreTriangle]
  norm_num

theorem trustTriangleMetaStep₁₂_errorBound :
    trustTriangleMetaStep₁₂.errorBound = 6 := by
  rw [MetaGoalShellPreservationStep.errorBound]
  simp [trustTriangleMetaStep₁₂, trustTriangleSemanticStep₁₂, coreTriangle]
  norm_num

theorem trustTriangleMetaGoalPath_totalErrorBound :
    trustTriangleMetaGoalPath.totalErrorBound = 12 := by
  simp [trustTriangleMetaGoalPath, MetaGoalShellPreservationPath.totalErrorBound,
    trustTriangleMetaStep₀₁_errorBound, trustTriangleMetaStep₁₂_errorBound]
  norm_num

private theorem exists_triangleChain_dlr (wc : ℝ) :
    ∃ μ : Measure (InfiniteWorld Nat),
      ∃ _ : IsProbabilityMeasure μ,
        FixedRegionCylinderDLR
          (triangleChainSpec trustWt wc).toStrictlyPositiveInfiniteGroundMLNSpec μ := by
  simpa [triangleChainSpec] using
    exists_varNeighborhood_fixedRegionCylinderDLR
      triangleChainNbrs triangleChainNbrs triangleChainNbrs_symm
      (triangleChainTrust trustWt wc) uniformPrior falseBoundary

/-- Concrete protected-goal example: a two-step proof-backed rewrite path on
the trust triangle improves utility and keeps the protected WM goal within the
cumulative shell bound. -/
theorem trustTriangle_metaGoal_path_example :
    ∃ measures :
        MetaGoalShellPreservationPathDLR
          (Atom := Nat) (ClauseId := VarNClauseId) trustTriangleMetaGoalPath,
      expectedUtilityFromStart trustTriangleMetaGoalPath.endMachine >
          expectedUtilityFromStart trustTriangleMetaGoalPath.startMachine ∧
        |(BinaryWorldModel.queryStrength
            ({infiniteMLNMassSemantics trustTriangleMetaGoalPath.startSpec
                measures.startMeasure measures.startDLR} :
              MassState (ConstraintQuery Nat)) agent1Query).toReal -
          (BinaryWorldModel.queryStrength
            ({infiniteMLNMassSemantics trustTriangleMetaGoalPath.endSpec
                measures.endMeasure measures.endDLR} :
              MassState (ConstraintQuery Nat)) agent1Query).toReal| ≤
            12 := by
  classical
  rcases exists_triangleChain_dlr trustChain₀ with ⟨μ₀m, hμ₀prob, hμ₀⟩
  rcases exists_triangleChain_dlr trustChain₁ with ⟨μ₁m, hμ₁prob, hμ₁⟩
  rcases exists_triangleChain_dlr trustChain₂ with ⟨μ₂m, hμ₂prob, hμ₂⟩
  let μ₀ : ProbabilityMeasure (InfiniteWorld Nat) := ⟨μ₀m, hμ₀prob⟩
  let μ₁ : ProbabilityMeasure (InfiniteWorld Nat) := ⟨μ₁m, hμ₁prob⟩
  let μ₂ : ProbabilityMeasure (InfiniteWorld Nat) := ⟨μ₂m, hμ₂prob⟩
  let measures :
      MetaGoalShellPreservationPathDLR
        (Atom := Nat) (ClauseId := VarNClauseId) trustTriangleMetaGoalPath :=
    .step (.single μ₀ μ₁ hμ₀ hμ₁) μ₂ hμ₂
  refine ⟨measures, ?_⟩
  have hmain :=
    measures.utility_improves_and_goal_wmStrength_cumulative_drift
      trustTriangleMetaGoalPath_coherent
      (q := agent1Query) (by simp [trustTriangleProtectedGoals])
  refine ⟨hmain.1, ?_⟩
  have hbound : |(BinaryWorldModel.queryStrength
      ({infiniteMLNMassSemantics trustTriangleMetaGoalPath.startSpec
          measures.startMeasure measures.startDLR} :
        MassState (ConstraintQuery Nat)) agent1Query).toReal -
    (BinaryWorldModel.queryStrength
      ({infiniteMLNMassSemantics trustTriangleMetaGoalPath.endSpec
          measures.endMeasure measures.endDLR} :
        MassState (ConstraintQuery Nat)) agent1Query).toReal| ≤
      trustTriangleMetaGoalPath.totalErrorBound := hmain.2
  simpa [trustTriangleMetaGoalPath_totalErrorBound] using hbound

/-- Concrete exact bridge example via dynamic-individuation closure:
the first proof-backed rewrite improves utility while preserving the protected
trust-triangle WM goal exactly. -/
theorem trustTriangle_exact_metaGoal_closure_example
    (wt wc₁ wc₂ : ℝ)
    (hwt : |wt| < 1 / 2) (hwc₁ : |wc₁| < 1 / 2) (hwc₂ : |wc₂| < 1 / 2)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Nat))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Nat))
    (hμ₁ : FixedRegionCylinderDLR
      (triangleChainSpec wt wc₁).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Nat)))
    (hμ₂ : FixedRegionCylinderDLR
      (triangleChainSpec wt wc₂).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Nat))) :
    expectedUtilityFromStart (toyMachine 1) >
        expectedUtilityFromStart (toyMachine 0) ∧
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics (triangleChainSpec wt wc₁) μ₁ hμ₁} :
          MassState (ConstraintQuery Nat)) agent1Query =
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics (triangleChainSpec wt wc₂) μ₂ hμ₂} :
          MassState (ConstraintQuery Nat)) agent1Query := by
  let closure : DynamicIndividuationClosure (triangleChainSpec wt wc₁) :=
    trustTriangleClosure wt wc₁
  let cross : CrossSpecDLR (triangleChainSpec wt wc₁) (triangleChainSpec wt wc₂) :=
    { oldMeasure := μ₁
      newMeasure := μ₂
      oldDLR := hμ₁
      newDLR := hμ₂ }
  let goals : ProtectedWMGoals closure.proto.seed := by
    simpa [closure, trustTriangleClosure] using trustTriangleProtectedGoals
  have hAgree :
      SpecAgreesOnRegion (triangleChainSpec wt wc₁) (triangleChainSpec wt wc₂)
        ((triangleChainSpec wt wc₁).iterExpandRegion closure.proto.seed closure.closureDepth) := by
    simpa [closure, trustTriangleClosure, ClassicalInfiniteGroundMLNSpec.iterExpandRegion]
      using specs_agree_on_triangle wt wc₁ wc₂
  have hClosed₂ :
      InteractionClosed (triangleChainSpec wt wc₂)
        ((triangleChainSpec wt wc₁).iterExpandRegion closure.proto.seed closure.closureDepth) := by
    simpa [closure, trustTriangleClosure, ClassicalInfiniteGroundMLNSpec.iterExpandRegion]
      using triangleCore_interactionClosed wt wc₂
  simpa [cross] using
    validModification_and_goal_wmStrength_preserved_of_dynamicIndividuationClosure
      (oldMachine := toyMachine 0)
      (newMachine := toyMachine 1)
      (proofBacked := toyMachine_validModification_of_lt (by norm_num))
      (closure := closure)
      (hagree := hAgree)
      (hclosed₂ := hClosed₂)
      (hbudget₁ := triangleChainSpec_budget wt wc₁ hwt hwc₁)
      (hbudget₂ := triangleChainSpec_budget wt wc₂ hwt hwc₂)
      (protectedGoals := goals)
      (measures := cross)
      (q := agent1Query)
      (hq := by
        simp [goals, closure, trustTriangleClosure, trustTriangleProtectedGoals])

end Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservationExample
