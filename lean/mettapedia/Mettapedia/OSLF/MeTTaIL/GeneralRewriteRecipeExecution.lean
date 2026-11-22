import Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeDAG
import Mettapedia.Machines.ProductiveCoreAdapters
import Mettapedia.GSLT.Distinction.SimulationComposition

/-!
# Retained checking of authored rewrite-recipe DAGs

Each worker call replays one original recipe node and checks its literal
premise addresses. The admitted language, binding context and result sort
remain fixed parameters. Refusal retains the old checked table and the
complete refused suffix. The table carries endpoint judgments; no rewrite
rule or search procedure is supplied by a different language.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeExecution

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission GeneralRewriteRecipeDAG
open Mettapedia.Machines.ProductiveCoreAdapters
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.OSLF.NativeTypes.Certificates
open Mettapedia.OSLF.Framework.PathTypeSynthesis Mettapedia.OSLF.Framework.GSLTTypeSynthesis

abbrev Work := RetainedFold.Work Node (List Claim)

variable (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)

/-- Local recipe choices are checked by their original replay function;
ordered back-references are checked by the original shared-row worker. -/
def consume (table : List Claim) (node : Node) : Option (List Claim) :=
  match node.admit? plan bound type with
  | none => none
  | some row =>
      if (Shared.inspectRow table row).1 then
        some (table ++ [Rule.conclusion plan bound type row.rule])
      else none

theorem reference_eq (table : List Claim) (nodes : List Node) :
    RetainedFold.reference (consume plan bound type) table nodes =
      (prepare? plan bound type nodes).bind (fun rows => (Shared.inspectRows table rows).table) := by
  induction nodes generalizing table with
  | nil => rfl
  | cons node rest ih =>
      cases admitted : node.admit? plan bound type with
      | none => simp [RetainedFold.reference, consume, prepare?, admitted]
      | some row =>
          cases valid : (Shared.inspectRow table row).1 with
          | false =>
              cases prepared : prepare? plan bound type rest <;>
                simp [RetainedFold.reference, consume, prepare?, admitted, valid, prepared,
                  Shared.inspectRows]
          | true =>
              simp only [RetainedFold.reference, consume, admitted, Option.bind_some, valid, ↓reduceIte]
              rw [ih]
              cases prepared : prepare? plan bound type rest <;>
                simp [prepare?, admitted, valid, prepared, Shared.inspectRows]

def start (graph : Graph) : Work := RetainedFold.start graph.nodes []

def advance (budget : Nat) (work : Work) : Work :=
  RetainedFold.advance (consume plan bound type) budget work

def verdict (graph : Graph) (wanted : Claim) (work : Work) : Bool :=
  match work.result with
  | none => false
  | some table => decide (table[graph.root]? = some wanted)

theorem verdict_exact (graph : Graph) (wanted : Claim) :
    verdict graph wanted (advance plan bound type graph.nodes.length (start graph)) =
      graph.check plan bound type wanted := by
  unfold verdict advance start
  rw [RetainedFold.complete_exact, reference_eq]
  unfold Graph.check
  cases prepared : prepare? plan bound type graph.nodes with
  | none => rfl
  | some rows =>
      simp only [Option.bind_some, Shared.checkJudgments, Shared.checkJudgmentsWithWork_eq_inspectRows]
      cases (Shared.inspectRows [] rows).table <;> rfl

theorem verdict_valid (graph : Graph) (wanted : Claim) :
    verdict graph wanted (advance plan bound type graph.nodes.length (start graph)) = true ↔
      graph.Valid plan bound type wanted := by
  rw [verdict_exact, Graph.check_exact]

/-- Coverage refers to the original finite execution modulo the language's
equations, not to a command that merely names a hypothetical fibre step. -/
theorem exists_verdict_iff_semanticPath (source target : Pattern) :
    (∃ graph : Graph, verdict graph (source, target)
      (advance plan bound type graph.nodes.length (start graph)) = true) ↔
      Nonempty (SemanticPath (GeneralOccurrenceSemantics.gslt plan bound type) source target) := by
  simp only [verdict_exact]
  exact GeneralRewriteRecipeDAG.exists_checked_iff_semanticPath plan bound type source target

/-- The completed native checker witnesses the existing reaching native
type. Its target predicate must respect the original equations. -/
theorem exists_verdict_iff_reachingNativeType
    (predicate : EquationPredicate (pathGSLT (GeneralOccurrenceSemantics.gslt plan bound type)))
    (source : Pattern) :
    (∃ target graph, verdict graph (source, target)
      (advance plan bound type graph.nodes.length (start graph)) = true ∧ predicate target) ↔
      (pathOSLF (GeneralOccurrenceSemantics.gslt plan bound type)).satisfies source
        (reachingNativeType (GeneralOccurrenceSemantics.gslt plan bound type) predicate).pred := by
  rw [satisfies_reachingNativeType_iff (GeneralOccurrenceSemantics.gslt plan bound type) predicate source]
  constructor
  · rintro ⟨target, graph, checked, holds⟩
    exact ⟨target, (exists_verdict_iff_semanticPath plan bound type source target).mp ⟨graph, checked⟩, holds⟩
  · rintro ⟨target, path, holds⟩
    obtain ⟨graph, checked⟩ := (exists_verdict_iff_semanticPath plan bound type source target).mpr path
    exact ⟨target, graph, checked, holds⟩

def object : ObservedMachine (Occurrence Work) Work Empty :=
  ObservedMachine.of (answerMachine (RetainedFold.core (consume plan bound type)))

/-- Calls of the authored-node worker and one final observation. Substitution,
premise replay, sorting and term comparison are not constant-time premises. -/
theorem machine_completes (graph : Graph) :
    ∃ fuel events report, fuel ≤ graph.nodes.length + 1 ∧
      (object plan bound type).machine.run fuel (start graph) = (events, .finished report) ∧
      report.result = (prepare? plan bound type graph.nodes).bind
        (fun rows => (Shared.inspectRows [] rows).table) := by
  obtain ⟨fuel, events, report, count, ran, result⟩ :=
    RetainedFold.machine_completes (consume plan bound type) graph.nodes []
  exact ⟨fuel, events, report, count, ran, result.trans (reference_eq plan bound type [] graph.nodes)⟩

/-- Root inspection of any actual finished run agrees with the original
authored DAG checker, including rejection of unused invalid rows. -/
theorem finished_verdict (graph : Graph) (wanted : Claim) {fuel : Nat}
    {events : List (Occurrence Work)} {report : Work}
    (finished : (object plan bound type).machine.run fuel (start graph) = (events, .finished report)) :
    verdict graph wanted report = graph.check plan bound type wanted := by
  have result := RetainedFold.finished_result (consume plan bound type) graph.nodes [] finished
  unfold verdict
  rw [result, reference_eq]
  unfold Graph.check
  cases prepare? plan bound type graph.nodes with
  | none => rfl
  | some rows =>
      simp only [Option.bind_some, Shared.checkJudgments, Shared.checkJudgmentsWithWork_eq_inspectRows]
      cases (Shared.inspectRows [] rows).table <;> rfl

/-- Exact correspondence of actual terminated checking and the existing
equation-respecting reachability native type. -/
theorem exists_finished_iff_reachingNativeType
    (predicate : EquationPredicate (pathGSLT (GeneralOccurrenceSemantics.gslt plan bound type)))
    (source : Pattern) :
    (∃ target graph fuel events report,
      (object plan bound type).machine.run fuel (start graph) = (events, .finished report) ∧
        verdict graph (source, target) report = true ∧ predicate target) ↔
      (pathOSLF (GeneralOccurrenceSemantics.gslt plan bound type)).satisfies source
        (reachingNativeType (GeneralOccurrenceSemantics.gslt plan bound type) predicate).pred := by
  rw [← exists_verdict_iff_reachingNativeType plan bound type predicate source]
  constructor
  · rintro ⟨target, graph, fuel, events, report, finished, accepted, holds⟩
    refine ⟨target, graph, ?_, holds⟩
    rw [verdict_exact, ← finished_verdict plan bound type graph (source, target) finished]
    exact accepted
  · rintro ⟨target, graph, accepted, holds⟩
    obtain ⟨fuel, events, report, _, finished, _⟩ := machine_completes plan bound type graph
    refine ⟨target, graph, fuel, events, report, finished, ?_, holds⟩
    rw [finished_verdict plan bound type graph (source, target) finished, ← verdict_exact]
    exact accepted

end Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeExecution
