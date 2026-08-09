import Mettapedia.Languages.MeTTa.MeTTaZero

/-!
# Staged semantic adequacy for query-first MeTTa Zero

The executable Zero presentation separates request classification, positive
production, and closed observation.  This module gives that stage boundary a
proof-relevant semantic model before choosing a Horn, worklist, chart, or
PathMap realization.

Query evidence retains the matched space atom and bindings.  Equation
evidence additionally retains the public-query witness through which the
equation was discovered.  Ground evidence remains visibly distinct.  Erasing
the evidence after production recovers the query-first kernel exactly; the
observer adds the inert result only after exact completed emptiness.
-/

namespace Mettapedia.Languages.MeTTa.MeTTaZeroStagedAdequacy

open Mettapedia.Languages.MeTTa.MeTTaZero
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

/-- The two public request forms after the authored classification stage. -/
inductive ClassifiedRequest (model : Model) where
  | query (space : model.Space) (pattern template : Pattern)
  | evaluate (space : model.Space) (subject : Pattern)

/-- Evidence emitted by one successful public query occurrence. -/
structure QueryEvidence where
  candidate : Pattern
  bindings : Bindings
deriving Repr, DecidableEq

/-- Positive production evidence.  Equation production contains the public
query evidence that exposed the equation as ordinary space data. -/
inductive ProducerEvidence where
  | query (evidence : QueryEvidence)
  | equation (queryEvidence : QueryEvidence) (left right : Pattern)
      (equationBindings : Bindings)
  | ground (subject result : Pattern)
deriving Repr, DecidableEq

/-- One proof-relevant produced occurrence. -/
structure ProducedOccurrence where
  evidence : ProducerEvidence
  result : Pattern
deriving Repr, DecidableEq

private structure QueryOccurrence where
  evidence : QueryEvidence
  result : Pattern
deriving DecidableEq

/-- Positive occurrences of a public query, before observation erases their
evidence. -/
def queryProduced (model : Model) (space : model.Space)
    (pattern template : Pattern) : Multiset QueryOccurrence :=
  (model.contents space).bind fun candidate =>
    (model.matchAtoms pattern candidate).map fun bindings =>
      { evidence := { candidate, bindings }
        result := applyBindings bindings template }

/-- Equation production starts from the public wildcard query.  There is no
private equation store in this definition. -/
def equationProduced (model : Model) (space : model.Space)
    (subject : Pattern) : Multiset ProducedOccurrence :=
  (queryProduced model space (.fvar allAtomsVariable)
      (.fvar allAtomsVariable)).bind fun queried =>
    match viewEquation? queried.result with
    | none => 0
    | some (left, right) =>
        (model.matchAtoms left subject).map fun bindings =>
          { evidence := .equation queried.evidence left right bindings
            result := applyBindings bindings right }

/-- Grounding is a separate positive producer and retains its provenance kind.
The richer capability result protocol remains an extension of `Model`. -/
def groundProduced (model : Model) (subject : Pattern) :
    Multiset ProducedOccurrence :=
  (model.groundApply subject).map fun result =>
    { evidence := .ground subject result, result }

/-- The authored positive-production stage. -/
def produce (model : Model) : ClassifiedRequest model →
    Multiset ProducedOccurrence
  | .query space pattern template =>
      (queryProduced model space pattern template).map fun occurrence =>
        { evidence := .query occurrence.evidence
          result := occurrence.result }
  | .evaluate space subject =>
      equationProduced model space subject + groundProduced model subject

/-- The closed observer preserves query emptiness, preserves every positive
evaluation occurrence, and applies inertness only to a completed empty
evaluation production. -/
def observe {model : Model} : ClassifiedRequest model →
    Multiset ProducedOccurrence → Multiset Pattern
  | .query .., produced => produced.map ProducedOccurrence.result
  | .evaluate _ subject, produced =>
      if produced = 0 then {subject}
      else produced.map ProducedOccurrence.result

/-- The complete three-stage semantic pipeline after classification. -/
def run (model : Model) (request : ClassifiedRequest model) :
    Multiset Pattern :=
  observe request (produce model request)

@[simp] theorem queryProduced_results (model : Model) (space : model.Space)
    (pattern template : Pattern) :
    (queryProduced model space pattern template).map QueryOccurrence.result =
      query model space pattern template := by
  unfold queryProduced query
  rw [Multiset.map_bind]
  apply Multiset.bind_congr
  intro candidate _
  rw [Multiset.map_map]
  rfl

@[simp] theorem groundProduced_results (model : Model) (subject : Pattern) :
    (groundProduced model subject).map ProducedOccurrence.result =
      model.groundApply subject := by
  unfold groundProduced
  rw [Multiset.map_map]
  rfl

/-- Erasing evidence from equation production recovers the query-derived
equation semantics exactly. -/
theorem equationProduced_results (model : Model) (space : model.Space)
    (subject : Pattern) :
    (equationProduced model space subject).map ProducedOccurrence.result =
      equationResults model space subject := by
  unfold equationProduced equationResults
  rw [Multiset.map_bind]
  calc
    (queryProduced model space (.fvar allAtomsVariable)
          (.fvar allAtomsVariable)).bind
        (fun queried =>
          Multiset.map ProducedOccurrence.result
            (match viewEquation? queried.result with
             | none => 0
             | some (left, right) =>
                 Multiset.map
                   (fun bindings =>
                     { evidence :=
                         ProducerEvidence.equation queried.evidence left right
                           bindings
                       result := applyBindings bindings right })
                   (model.matchAtoms left subject))) =
      (queryProduced model space (.fvar allAtomsVariable)
          (.fvar allAtomsVariable)).bind
        (fun queried =>
          match viewEquation? queried.result with
          | none => 0
          | some (left, right) =>
              (model.matchAtoms left subject).map fun bindings =>
                applyBindings bindings right) := by
          apply Multiset.bind_congr
          intro queried _
          cases equationView : viewEquation? queried.result with
          | none => simp [equationView]
          | some equation =>
              obtain ⟨left, right⟩ := equation
              simp [equationView, Multiset.map_map]
    _ = ((queryProduced model space (.fvar allAtomsVariable)
            (.fvar allAtomsVariable)).map QueryOccurrence.result).bind
          (fun candidate =>
            match viewEquation? candidate with
            | none => 0
            | some (left, right) =>
                (model.matchAtoms left subject).map fun bindings =>
                  applyBindings bindings right) := by
          rw [Multiset.bind_map]
    _ = (queryAll model space).bind
          (fun candidate =>
            match viewEquation? candidate with
            | none => 0
            | some (left, right) =>
                (model.matchAtoms left subject).map fun bindings =>
                  applyBindings bindings right) := by
          rw [queryProduced_results]
          rfl

@[simp] theorem produce_query_results (model : Model) (space : model.Space)
    (pattern template : Pattern) :
    (produce model (.query space pattern template)).map
        ProducedOccurrence.result =
      query model space pattern template := by
  simp [produce]

@[simp] theorem produce_evaluate_results (model : Model)
    (space : model.Space) (subject : Pattern) :
    (produce model (.evaluate space subject)).map ProducedOccurrence.result =
      interpretedResults model space subject := by
  simp [produce, interpretedResults, equationProduced_results,
    groundProduced_results]

/-- Positive query adequacy: classification, production, and observation
recover the public query occurrence bag exactly. -/
@[simp] theorem run_query (model : Model) (space : model.Space)
    (pattern template : Pattern) :
    run model (.query space pattern template) =
      query model space pattern template := by
  simp [run, observe]

/-- Positive evaluation adequacy: the staged pipeline recovers the query-first
one-step evaluator exactly, including its inert default. -/
@[simp] theorem run_evaluate (model : Model) (space : model.Space)
    (subject : Pattern) :
    run model (.evaluate space subject) =
      evaluateOne model space subject := by
  simp [run, observe, evaluateOne, produce_evaluate_results]

/-- Negative boundary: an empty query stays empty; the inert default belongs
only to evaluation observation. -/
theorem empty_query_does_not_become_inert (model : Model)
    (space : model.Space) (pattern template : Pattern)
    (empty : query model space pattern template = 0) :
    run model (.query space pattern template) = 0 := by
  simpa [run_query] using empty

/-- Negative boundary: positive evaluation production cannot acquire an extra
inert occurrence. -/
theorem positive_evaluation_has_no_inert_fallback (model : Model)
    (space : model.Space) (subject : Pattern)
    (positive : interpretedResults model space subject ≠ 0) :
    run model (.evaluate space subject) =
      interpretedResults model space subject := by
  rw [run_evaluate]
  exact evaluateOne_of_interpreted model space subject positive

end Mettapedia.Languages.MeTTa.MeTTaZeroStagedAdequacy
