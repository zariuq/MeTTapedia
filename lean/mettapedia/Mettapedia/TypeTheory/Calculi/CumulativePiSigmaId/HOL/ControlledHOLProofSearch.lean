import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.ProofPlanning
import Mettapedia.Logic.ProofSearch.ControlledSearch
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerTyping

/-!
# Controlled HOL proof search through the one native compiler

Inference providers emit actual proof syntax at an indexed query. Control
only schedules their authorized occurrences. Compilation consumes the first
retained answer, with its hypotheses and object context unchanged. A native
result therefore has both provider provenance and the generic compiler's
typing and semantic guarantees.

The search stage carries its actual run. Its cost reads that same trace, and
composition with compilation retains both receipts rather than rebuilding a
second search or semantic history. No runtime correspondence is asserted.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Logic.ProofSearch.ControlledHOL

open Mettapedia.Logic HOL
open Mettapedia.GSLT.Core Mettapedia.GSLT.Core.BranchingTemporal
open Presentation FormationSensitiveHOLInterface HOLNativeGenericProofCompiler

universe u v w

variable {Base : Type u} {Const : HOL.Ty Base → Type v}
variable {Node Memory : Type (max u v)}
variable {counter : CounterSystem (HOLAdapter.Goal Base Const) HOLAdapter.Solution}
variable {Constraint : HOLAdapter.Goal Base Const → Type (max u v)}
variable {goal : HOLAdapter.Goal Base Const}
variable {system : BranchingSystem Node (HOLAdapter.Solution goal)}
variable {controller : InferenceControl.Controller Node (HOLAdapter.Solution goal) Memory}
variable {roots : List Node}

/-- Native compilation of the actual observation, not of a separately chosen
proof or a semantically equivalent replacement. -/
def compileState? (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName)
    (state : ControlledSearch.State Node (HOLAdapter.Solution goal) Memory)
    {n : Nat} (objects : Sub Tower.Head goal.context.length n)
    (hypotheses : Fin goal.hypotheses.length → Tower.Tm n) : Option (Tower.Tm n) :=
  (ControlledSearch.observe counter Constraint goal state).bind
    (fun outcome => HOLAdapter.compileOutcome? signature proofName operations
      outcome objects hypotheses)

/-- A compiled result retains the exact generated proof and the successful
equation of the existing compiler. -/
theorem compiled_from_provider
    (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName)
    {state : ControlledSearch.State Node (HOLAdapter.Solution goal) Memory}
    (trace : (ControlledSearch.plan counter Constraint goal system controller roots).Trace
      (ControlledSearch.plan counter Constraint goal system controller roots).initial state)
    {n : Nat} {objects : Sub Tower.Head goal.context.length n}
    {hypotheses : Fin goal.hypotheses.length → Tower.Tm n} {native : Tower.Tm n}
    (success : compileState? (counter := counter) (Constraint := Constraint)
      signature proofName operations state objects hypotheses = some native) :
    ∃ node proof, Generated system roots node ∧ system.emit node = some proof ∧
      compile signature proofName operations proof objects hypotheses = some native := by
  cases events : state.snapshot.search.events with
  | nil =>
      cases frontier : state.snapshot.search.frontier <;>
        simp [compileState?, ControlledSearch.observe, events, frontier,
          HOLAdapter.compileOutcome?] at success
  | cons event pending =>
      have observed : ControlledSearch.observe counter Constraint goal state =
          some (.solved event.value) := by simp [ControlledSearch.observe, events]
      obtain ⟨node, generated, emitted⟩ := ControlledSearch.solved_has_origin trace observed
      exact ⟨node, event.value, generated, emitted,
        by simpa [compileState?, observed, HOLAdapter.compileOutcome?] using success⟩

/-- The retained provider proof produces a native inhabitant of the exact
represented conclusion in the supplied typed context. -/
theorem compiled_typed
    (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName)
    {state : ControlledSearch.State Node (HOLAdapter.Solution goal) Memory}
    (trace : (ControlledSearch.plan counter Constraint goal system controller roots).Trace
      (ControlledSearch.plan counter Constraint goal system controller roots).initial state)
    {n : Nat} {target : Tower.Ctx n} {objects : Sub Tower.Head goal.context.length n}
    {hypotheses : Fin goal.hypotheses.length → Tower.Tm n} {native : Tower.Tm n}
    (objectTyped : GenericTyping.Objects signature target objects)
    (hypothesisTyped : GenericTyping.Hypotheses signature operations target objects hypotheses)
    (success : compileState? (counter := counter) (Constraint := Constraint)
      signature proofName operations state objects hypotheses = some native) :
    ∃ code, represent signature goal.conclusion = some code ∧
      Presentation.FormationSensitive.Typing operations.target target native
        (FormationSensitiveHOLGenericProofFamily.proof proofName (subst objects code)) := by
  obtain ⟨_node, proof, _generated, _emitted, compiled⟩ :=
    compiled_from_provider signature proofName operations trace success
  exact GenericTyping.compile_typed signature proofName operations proof
    objectTyped hypothesisTyped compiled

/-- The same native term and actual source proof cross the model interface. -/
theorem compiled_denotes
    (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName)
    (semantics : GenericSemantics.Algebra signature proofName operations)
    {searchState : ControlledSearch.State Node (HOLAdapter.Solution goal) Memory}
    (trace : (ControlledSearch.plan counter Constraint goal system controller roots).Trace
      (ControlledSearch.plan counter Constraint goal system controller roots).initial searchState)
    {n : Nat} {objects : Sub Tower.Head goal.context.length n}
    {hypotheses : Fin goal.hypotheses.length → Tower.Tm n} {native : Tower.Tm n}
    (success : compileState? (counter := counter) (Constraint := Constraint)
      signature proofName operations searchState objects hypotheses = some native)
    (state : semantics.State objects)
    (hypothesesMeaning : GenericSemantics.Hypotheses semantics state hypotheses) :
    semantics.Denotes state native goal.conclusion := by
  obtain ⟨_node, proof, _generated, _emitted, compiled⟩ :=
    compiled_from_provider signature proofName operations trace success
  exact GenericSemantics.compile_denotes signature proofName operations semantics
    proof compiled state hypothesesMeaning

/-- Open search is not a native proof. -/
theorem open_not_compiled
    (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName)
    (state : ControlledSearch.State Node (HOLAdapter.Solution goal) Memory)
    (opened : ControlledSearch.observe counter Constraint goal state = none)
    {n : Nat} (objects : Sub Tower.Head goal.context.length n)
    (hypotheses : Fin goal.hypotheses.length → Tower.Tm n) :
    compileState? (counter := counter) (Constraint := Constraint)
      signature proofName operations state objects hypotheses = none := by
  simp [compileState?, opened]

/-- Exhaustion, whether a budget or the authored finite space, is not proof. -/
theorem exhausted_not_compiled
    (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName)
    (state : ControlledSearch.State Node (HOLAdapter.Solution goal) Memory)
    (failure : Exhaustion)
    (exhausted : ControlledSearch.observe counter Constraint goal state =
      some (.exhausted failure))
    {n : Nat} (objects : Sub Tower.Head goal.context.length n)
    (hypotheses : Fin goal.hypotheses.length → Tower.Tm n) :
    compileState? (counter := counter) (Constraint := Constraint)
      signature proofName operations state objects hypotheses = none := by
  simp [compileState?, exhausted, HOLAdapter.compileOutcome?]

/-- Compose the existing run and compiler stages, preserving the observed
outcome, actual run, and exact successful compilation equation. -/
def compilationPipeline
    (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName)
    (n : Nat) (objects : Sub Tower.Head goal.context.length n)
    (hypotheses : Fin goal.hypotheses.length → Tower.Tm n) : Stage Unit (Tower.Tm n) :=
  (ControlledSearch.plan counter Constraint goal system controller roots).completionStage.comp
    (HOLAdapter.compilationStage signature proofName operations n objects hypotheses)

/-- The pipeline interprets precisely the search and compiler receipts in
its composed evidence; grades need not share the proof-family universe. -/
def pipelineCost
    (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName)
    (n : Nat) (objects : Sub Tower.Head goal.context.length n)
    (hypotheses : Fin goal.hypotheses.length → Tower.Tm n)
    {Grade : Type w} [AddMonoid Grade]
    (searchCost : System.CostModel
      (ControlledSearch.plan counter Constraint goal system controller roots) Grade)
    (compilerCost : Stage.Cost
      (HOLAdapter.compilationStage (counter := counter) (Constraint := Constraint)
        signature proofName operations n objects hypotheses) Grade) :
    Stage.Cost (compilationPipeline (counter := counter) (Constraint := Constraint)
      (system := system) (controller := controller)
      (roots := roots) signature proofName operations n objects hypotheses) Grade :=
  (System.completionCost searchCost).comp compilerCost

#print axioms compiled_from_provider
#print axioms compiled_typed
#print axioms compiled_denotes
#print axioms open_not_compiled
#print axioms exhausted_not_compiled

end Mettapedia.Logic.ProofSearch.ControlledHOL
