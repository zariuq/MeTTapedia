import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Foundation
import Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservationPath

/-!
# GodelClaw Ethics Meta-Stability

This module packages the universal-loving-care safety theorem in one place.

The intended reading is deliberately broader than AI-only safety:

- for an AI system, it says proof-backed self-modification can improve expected
  utility while preserving protected caring goals exactly or approximately;
- for a human agent, it reads as disciplined reflective revision preserving a
  protected caring core while beliefs and plans evolve.

The caring goals are represented extensionally as protected WM queries.  This
lets us reuse the proved shell-preservation machinery without pretending we
already have a fully compiled bridge from every ethics formula into WM space.

**Positive example.**  A protected query encoding operator deference,
non-maleficence, consent, or an epistemic-universal-love obligation can stay
stable under remote rewrites.

**Negative example.**  If a rewrite reaches the protected region itself, or if
the Dobrushin budget fails, these theorems do not apply.
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw.Ethics

open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicOntologyGrowth
open Mettapedia.Logic.MarkovLogicDynamicIndividuation
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicAbstract.MassState
open Mettapedia.UniversalAI.GodelMachine
open Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservation
open MeasureTheory

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

/-- Protected caring goals are just protected WM goals read through an ethics
lens.  Typical examples are queries encoding care, non-maleficence, consent,
or operator deference on a protected region. -/
abbrev ProtectedCaringGoals (Γ : Region Atom) := ProtectedWMGoals (Atom := Atom) Γ

/-- Exact ethics meta-stability:

if a proof-backed rewrite stays outside a dynamically individuated caring core,
then every protected caring query on that core is preserved exactly while
expected utility improves. -/
theorem validModification_preserves_protectedCaringGoal_of_dynamicIndividuationClosure
    {oldSpec newSpec : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (oldMachine newMachine : GodelMachineState)
    (proofBacked : validModification oldMachine newMachine)
    (closure : DynamicIndividuationClosure oldSpec)
    (hagree : SpecAgreesOnRegion oldSpec newSpec
      (oldSpec.iterExpandRegion closure.proto.seed closure.closureDepth))
    (hclosed₂ : InteractionClosed newSpec
      (oldSpec.iterExpandRegion closure.proto.seed closure.closureDepth))
    (hbudget₁ : oldSpec.PaperUniformSmallTotalInfluence)
    (hbudget₂ : newSpec.PaperUniformSmallTotalInfluence)
    (protectedCaringGoals : ProtectedCaringGoals (Atom := Atom) closure.proto.seed)
    (measures : CrossSpecDLR oldSpec newSpec)
    {q : ConstraintQuery Atom}
    (hq : q ∈ protectedCaringGoals.goals) :
    expectedUtilityFromStart newMachine > expectedUtilityFromStart oldMachine ∧
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics oldSpec measures.oldMeasure measures.oldDLR} :
          MassState (ConstraintQuery Atom)) q =
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics newSpec measures.newMeasure measures.newDLR} :
          MassState (ConstraintQuery Atom)) q := by
  exact validModification_and_goal_wmStrength_preserved_of_dynamicIndividuationClosure
    (oldMachine := oldMachine) (newMachine := newMachine)
    (proofBacked := proofBacked)
    (closure := closure)
    (hagree := hagree)
    (hclosed₂ := hclosed₂)
    (hbudget₁ := hbudget₁)
    (hbudget₂ := hbudget₂)
    (protectedGoals := protectedCaringGoals)
    (measures := measures)
    (q := q) hq

/-- Approximate ethics meta-stability along a path:

if a reflective-development path keeps a caring query protected at each step,
then utility improves while the WM truth value of that caring query drifts by
at most the cumulative shell tail. -/
theorem MetaGoalShellPreservationPathDLR.utility_improves_and_protectedCaringGoal_drift_bounded
    {protectedCaringGoals : Finset (ConstraintQuery Atom)}
    {path : MetaGoalShellPreservationPath
      (Atom := Atom) (ClauseId := ClauseId) protectedCaringGoals}
    (measures : MetaGoalShellPreservationPathDLR path)
    (hcoh : path.Coherent)
    {q : ConstraintQuery Atom}
    (hq : q ∈ protectedCaringGoals) :
    expectedUtilityFromStart path.endMachine >
        expectedUtilityFromStart path.startMachine ∧
      |(BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics path.startSpec measures.startMeasure measures.startDLR} :
            MassState (ConstraintQuery Atom)) q).toReal -
        (BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics path.endSpec measures.endMeasure measures.endDLR} :
            MassState (ConstraintQuery Atom)) q).toReal| ≤
          path.totalErrorBound := by
  exact measures.utility_improves_and_goal_wmStrength_cumulative_drift hcoh hq

end Mettapedia.CognitiveArchitecture.GodelClaw.Ethics
