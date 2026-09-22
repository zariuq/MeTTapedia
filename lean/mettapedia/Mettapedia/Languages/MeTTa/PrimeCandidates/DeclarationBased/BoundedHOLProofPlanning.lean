import Mettapedia.Logic.HOL.BoundedLogicalSearch
import Mettapedia.Logic.ProofSearch.Planning
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLProofPlanning
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerTyping

/-!
# Actual bounded HOL search feeding native proof planning

The plan's execution step invokes bounded search on its indexed sequent.
Unlike a queue of preselected proofs, its terminal proof is reconstructed by
that algorithm. The internal event history decorates that same execution
step, including failed branches. This is an atomic search-call model with an
inspectable internal history, not a microstep model of the C implementation.

Only an actual searched tree reaches the one native compiler. Its ordinary
typing and displayed semantic theorems apply without another compiler or a
replacement source proof. This proof-only strategy never emits refutation;
exhausting its finite bounded search is not evidence against the theorem.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace BoundedHOLProofPlanning

open Mettapedia.Logic HOL.BoundedLogicalSearch
open ProofSearch ProofSearch.HOLAdapter
open Presentation FormationSensitiveHOLInterface HOLNativeGenericProofCompiler

universe u v w

variable {Base : Type u} {Const : HOL.Ty Base → Type v}

abbrev Constraints (_goal : HOLAdapter.Goal Base Const) := ULift.{max u v} Empty

def outcome {goal : HOLAdapter.Goal Base Const}
    (result : Result goal.hypotheses goal.conclusion) :
    Outcome HOLAdapter.Solution HOLAdapter.noCounter Constraints goal :=
  match result.answer with
  | some found => .solved found.proof
  | none => .exhausted (.searchSpace result.events.length)

inductive State (goal : HOLAdapter.Goal Base Const) where
  | ready
  | finished (result : Result goal.hypotheses goal.conclusion)

variable [DecidableEq Base] [∀ σ, DecidableEq (Const σ)]

/-- The only execution constructor returns the algorithm's actual result. -/
inductive Step (candidates : Candidates Const) (fuel : Nat)
    (goal : HOLAdapter.Goal Base Const) : State goal → State goal → Type (max u v) where
  | execute : Step candidates fuel goal .ready
      (.finished (search candidates fuel goal.hypotheses goal.conclusion))

def plan (candidates : Candidates Const) (fuel : Nat) (goal : HOLAdapter.Goal Base Const) :
    System HOLAdapter.Solution HOLAdapter.noCounter Constraints goal where
  State := State goal
  initial := .ready
  Step := Step candidates fuel goal
  observe := fun state =>
    match state with
    | .ready => none
    | .finished result => some (outcome result)

def run (candidates : Candidates Const) (fuel : Nat) (goal : HOLAdapter.Goal Base Const) :
    System.Run (plan candidates fuel goal)
      (outcome (search candidates fuel goal.hypotheses goal.conclusion)) where
  final := .finished (search candidates fuel goal.hypotheses goal.conclusion)
  trace := .cons .execute (.nil _)
  observed := rfl

/-- Cost interprets the history of the very search step executed by the plan. -/
def cost {Grade : Type (max u v)} [AddMonoid Grade]
    (candidates : Candidates Const) (fuel : Nat) (goal : HOLAdapter.Goal Base Const)
    (charge : Event → Grade) : System.CostModel (plan candidates fuel goal) Grade where
  charge := fun {_source target} _step =>
    match target with
    | .ready => 0
    | .finished result => result.cost charge

theorem run_cost {Grade : Type (max u v)} [AddMonoid Grade]
    (candidates : Candidates Const) (fuel : Nat) (goal : HOLAdapter.Goal Base Const)
    (charge : Event → Grade) :
    (cost candidates fuel goal charge).total (run candidates fuel goal).trace =
      (search candidates fuel goal.hypotheses goal.conclusion).cost charge := by
  simp [cost, run, System.CostModel.total]

/-- Native typing is earned by compiling the actual solved search outcome. -/
theorem compiled_typed (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName)
    (candidates : Candidates Const) (fuel : Nat) (goal : HOLAdapter.Goal Base Const)
    {n : Nat} {target : Tower.Ctx n}
    {objects : Sub Tower.Head goal.context.length n}
    {hypotheses : Fin goal.hypotheses.length → Tower.Tm n}
    (objectTyped : GenericTyping.Objects signature target objects)
    (hypothesisTyped : GenericTyping.Hypotheses signature operations target objects hypotheses)
    {native : Tower.Tm n}
    (success : compileOutcome? signature proofName operations
      (outcome (search candidates fuel goal.hypotheses goal.conclusion)) objects hypotheses =
        some native) :
    ∃ code, represent signature goal.conclusion = some code ∧
      Presentation.FormationSensitive.Typing operations.target target native
        (FormationSensitiveHOLGenericProofFamily.proof proofName (subst objects code)) := by
  cases found : (search candidates fuel goal.hypotheses goal.conclusion).answer with
  | none => simp [outcome, found, compileOutcome?] at success
  | some actual =>
      simp only [outcome, found, compileOutcome?] at success
      exact GenericTyping.compile_typed signature proofName operations actual.proof
        objectTyped hypothesisTyped success

/-- The same compiler term denotes the exact queried conclusion. -/
theorem compiled_denotes (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName)
    (semantics : GenericSemantics.Algebra signature proofName operations)
    (candidates : Candidates Const) (fuel : Nat) (goal : HOLAdapter.Goal Base Const)
    {n : Nat} {objects : Sub Tower.Head goal.context.length n}
    {hypotheses : Fin goal.hypotheses.length → Tower.Tm n} {native : Tower.Tm n}
    (success : compileOutcome? signature proofName operations
      (outcome (search candidates fuel goal.hypotheses goal.conclusion)) objects hypotheses =
        some native)
    (state : semantics.State objects)
    (hypothesesMeaning : GenericSemantics.Hypotheses semantics state hypotheses) :
    semantics.Denotes state native goal.conclusion :=
  compileOutcome_denotes signature proofName operations semantics _ success state hypothesesMeaning

/-- Bounded failure does not enter the native compiler as a proof. -/
theorem exhausted_not_compiled (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName)
    (candidates : Candidates Const) (fuel : Nat) (goal : HOLAdapter.Goal Base Const)
    (failed : (search candidates fuel goal.hypotheses goal.conclusion).answer = none)
    {n : Nat} (objects : Sub Tower.Head goal.context.length n)
    (hypotheses : Fin goal.hypotheses.length → Tower.Tm n) :
    compileOutcome? signature proofName operations
      (outcome (search candidates fuel goal.hypotheses goal.conclusion)) objects hypotheses = none := by
  simp [outcome, failed, compileOutcome?]

#print axioms compiled_typed
#print axioms compiled_denotes
#print axioms exhausted_not_compiled
#print axioms run_cost

end BoundedHOLProofPlanning
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
