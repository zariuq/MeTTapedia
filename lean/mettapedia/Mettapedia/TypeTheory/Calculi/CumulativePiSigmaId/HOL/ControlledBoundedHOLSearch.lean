import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.ControlledHOLProofSearch
import Mettapedia.Logic.HOL.BoundedLogicalSearch

/-!
# Bounded higher-order search as an evidence-producing inference provider

A request supplies its scoped instantiation inventory and search depth.
Expansion runs the existing bounded logical search and emits only its actual
retained proof. Failed requests emit nothing. The controller may order these
requests, but does not select their premises, proofs, or conversion rules.

This atomic provider model retains the internal search-event receipt on the
same controlled expansion. It is not a microstep model of a C prover or a
claim that arbitrary ATP certificates have already been reconstructed.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Logic.ProofSearch.ControlledHOL.BoundedProvider

open Mettapedia.Logic HOL HOL.BoundedLogicalSearch
open Mettapedia.GSLT.Core Mettapedia.GSLT.Core.BranchingTemporal

universe u v w

/-- The bounded algorithm's choices are supplied data, not global policy. -/
structure Request (Base : Type u) (Const : HOL.Ty Base → Type v) where
  candidates : Candidates Const
  depth : Nat

variable {Base : Type u} {Const : HOL.Ty Base → Type v}
variable [DecidableEq Base] [∀ type, DecidableEq (Const type)]

def result (goal : HOLAdapter.Goal Base Const) (request : Request Base Const) :
    Result goal.hypotheses goal.conclusion :=
  search request.candidates request.depth goal.hypotheses goal.conclusion

/-- Each expansion performs its supplied bounded search; only actual successful
proof syntax is emitted. There are no secretly retained failed answers. -/
def system (goal : HOLAdapter.Goal Base Const) :
    BranchingSystem (Request Base Const) (HOLAdapter.Solution goal) where
  emit request := (result goal request).answer.map (fun found => found.proof)
  successors _ := []

/-- The authored finite portfolio has a literal completed bag denotation. -/
def denotation (goal : HOLAdapter.Goal Base Const) : AdditiveDenotation (system goal) where
  value request := optionBag ((system goal).emit request)
  unfold _ := by simp [system, foldValues]

/-- Internal event costs are charged to the actual selected provider expansion.
The same request computes its answer and its full failed/successful history. -/
def eventCost {Memory : Type (max u v)}
    {counter : CounterSystem (HOLAdapter.Goal Base Const) HOLAdapter.Solution}
    {Constraint : HOLAdapter.Goal Base Const → Type (max u v)}
    (goal : HOLAdapter.Goal Base Const)
    (controller : InferenceControl.Controller (Request Base Const) (HOLAdapter.Solution goal) Memory)
    (roots : List (Request Base Const)) {Grade : Type w} [AddMonoid Grade]
    (charge : Event → Grade) :
    System.CostModel (ControlledSearch.plan counter Constraint goal (system goal) controller roots)
      Grade :=
  ControlledSearch.costModel (fun request => (result goal request).cost charge)

/-- Distinct dimensions: controller expansions and the bounded searches'
actual event counts. This is not elapsed time or C instruction accounting. -/
def workCost {Memory : Type (max u v)}
    {counter : CounterSystem (HOLAdapter.Goal Base Const) HOLAdapter.Solution}
    {Constraint : HOLAdapter.Goal Base Const → Type (max u v)}
    (goal : HOLAdapter.Goal Base Const)
    (controller : InferenceControl.Controller (Request Base Const) (HOLAdapter.Solution goal) Memory)
    (roots : List (Request Base Const)) :
    System.CostModel (ControlledSearch.plan counter Constraint goal (system goal) controller roots)
      (Nat × Nat) :=
  ControlledSearch.costModel (fun request => (1, (result goal request).events.length))

/-- A failed actual search contributes no evidence, regardless of guidance. -/
theorem failed_emits_nothing (goal : HOLAdapter.Goal Base Const) (request : Request Base Const)
    (failed : (result goal request).answer = none) :
    (system goal).emit request = none := by simp [system, failed]

/-- Success retains the searched proof verbatim, including its assumptions. -/
theorem successful_emits_actual (goal : HOLAdapter.Goal Base Const)
    (request : Request Base Const) (found : Found goal.hypotheses goal.conclusion)
    (success : (result goal request).answer = some found) :
    (system goal).emit request = some found.proof := by simp [system, success]

#print axioms denotation
#print axioms failed_emits_nothing
#print axioms successful_emits_actual

end Mettapedia.Logic.ProofSearch.ControlledHOL.BoundedProvider
