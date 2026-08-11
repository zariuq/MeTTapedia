import Mettapedia.Languages.MeTTa.MeTTaZero
import Mettapedia.Languages.MeTTa.MeTTaZeroLanguageAdequacy
import Mettapedia.GSLT.Core.ClosureCriteria

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
open Mettapedia.Languages.MeTTa.MeTTaZeroLanguageAdequacy
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT
open Mettapedia.GSLT.Core.ClosureCriteria

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
  simp [groundProduced, Multiset.map_map]

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
          | none => simp
          | some equation =>
              obtain ⟨left, right⟩ := equation
              simp [Multiset.map_map]
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
  have production_empty :
      produce model (.evaluate space subject) = 0 ↔
        interpretedResults model space subject = 0 := by
    rw [← produce_evaluate_results, Multiset.map_eq_zero]
  unfold run evaluateOne
  change
    (if produce model (.evaluate space subject) = 0 then {subject}
     else (produce model (.evaluate space subject)).map
       ProducedOccurrence.result) =
      (if interpretedResults model space subject = 0 then {subject}
       else interpretedResults model space subject)
  simp only [production_empty, produce_evaluate_results]

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

/-! ## The staged pipeline as a control GSLT -/

/-- The complete language-visible state of Zero's semantic pipeline after a
request has been classified.  Produced evidence and the final occurrence bag
remain terms of the control theory rather than private driver state. -/
inductive PipelineControl (model : Model) where
  | classified (request : ClassifiedRequest model)
  | produced (request : ClassifiedRequest model)
      (occurrences : Multiset ProducedOccurrence)
  | observed (request : ClassifiedRequest model)
      (occurrences : Multiset ProducedOccurrence)
      (answers : Multiset Pattern)

/-- The two semantic stage transitions.  Production is positive; observation
is the only stage allowed to add the inert result after completed emptiness. -/
inductive PipelineStep (model : Model) :
    PipelineControl model → PipelineControl model → Prop where
  | produce (request : ClassifiedRequest model) :
      PipelineStep model (.classified request)
        (.produced request (MeTTaZeroStagedAdequacy.produce model request))
  | observe (request : ClassifiedRequest model)
      (occurrences : Multiset ProducedOccurrence) :
      PipelineStep model (.produced request occurrences)
        (.observed request occurrences
          (MeTTaZeroStagedAdequacy.observe request occurrences))

/-- Zero's classified-request pipeline as a genuine GSLT of control terms. -/
def pipelineControlGSLT (model : Model) : GSLT where
  Term := PipelineControl model
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := PipelineStep model
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- The exact answer bag associated with every intermediate control term.
Stage transitions preserve this observer. -/
def PipelineControl.answers {model : Model} :
    PipelineControl model → Multiset Pattern
  | .classified request => run model request
  | .produced request occurrences => observe request occurrences
  | .observed _ _ answers => answers

/-- Production and observation preserve the exact occurrence-bag answer. -/
theorem PipelineStep.answers_preserved {model : Model}
    {source target : PipelineControl model}
    (step : PipelineStep model source target) :
    source.answers = target.answers := by
  cases step <;> rfl

/-! ### Exact bridge to the authored five-field realization -/

/-- Forget only the surface encoding of the space argument and recover the
classified semantic request carried by the staged pipeline. -/
def classifiedRequest {model : Model} :
    KernelRequest model → ClassifiedRequest model
  | .query space _ pattern template => .query space pattern template
  | .evaluate space _ subject => .evaluate space subject

/-- Reapply the public answer constructor selected by a classified request.
The staged pipeline internally carries raw answers; the authored five-field
root exposes these two explicit result forms. -/
def ClassifiedRequest.publicAnswers {model : Model}
    (request : ClassifiedRequest model) (answers : Multiset Pattern) :
    Multiset Pattern :=
  match request with
  | .query .. => answers.map queryAnswerPattern
  | .evaluate .. => answers.map evaluationAnswerPattern

/-- Observe any intermediate pipeline term through the authored root's public
answer constructors. -/
def PipelineControl.publicAnswers {model : Model}
    (control : PipelineControl model) : Multiset Pattern :=
  match control with
  | .classified request => request.publicAnswers (run model request)
  | .produced request occurrences =>
      request.publicAnswers (observe request occurrences)
  | .observed request _ answers => request.publicAnswers answers

/-- Public occurrence-bag observation is invariant across both staged
transitions. -/
theorem PipelineStep.publicAnswers_preserved {model : Model}
    {source target : PipelineControl model}
    (step : PipelineStep model source target) :
    source.publicAnswers = target.publicAnswers := by
  cases step <;> rfl

/-- The completed semantic artifact produced from one authored-root request. -/
def completedPipelineArtifact {model : Model} (request : KernelRequest model) :
    PipelineControl model :=
  let classified := classifiedRequest request
  .observed classified (produce model classified) (run model classified)

/-- The staged control GSLT is a certified realization of the same source
observation as the generic interpreter over Zero's authored five-field root. -/
def stagedRealization (model : Model) :
    SimpleRealization (KernelRequest model) (PipelineControl model)
      (Multiset Pattern) where
  compile := fun _ request => completedPipelineArtifact request
  observeSource := fun _ request => semanticAnswers request
  observeArtifact := fun _ artifact => artifact.publicAnswers
  adequate := by
    intro _ request
    cases request with
    | query space spaceTerm pattern template =>
        simp [completedPipelineArtifact, classifiedRequest,
          PipelineControl.publicAnswers, ClassifiedRequest.publicAnswers,
          semanticAnswers, run_query]
    | evaluate space spaceTerm subject =>
        simp [completedPipelineArtifact, classifiedRequest,
          PipelineControl.publicAnswers, ClassifiedRequest.publicAnswers,
          semanticAnswers, run_evaluate]

/-- The staged control realization and the generic authored-root interpreter
agree exactly for every request, including occurrence multiplicity. -/
theorem stagedRealization_agrees_with_authored (model : Model)
    (request : KernelRequest model) :
    (stagedRealization model).observeArtifact ()
        ((stagedRealization model).compile () request) =
      (authoredRealization model).compile () request := by
  rw [(stagedRealization model).adequate]
  exact ((authoredRealization model).adequate () request).symm

/-- A deterministic driver for the staged semantic pipeline.  Its private
state is `Unit`: every semantically relevant control component is already in
`PipelineControl`. -/
def pipelineDriver (model : Model) : HostedDriver (pipelineControlGSLT model) where
  State := Unit
  step := fun control _ =>
    match control with
    | .classified request =>
        some (.produced request (produce model request), ())
    | .produced request occurrences =>
        some (.observed request occurrences (observe request occurrences), ())
    | .observed _ _ _ => none
  sound := by
    intro control state next state' moved
    cases state
    cases control with
    | classified request =>
        cases moved
        exact PipelineStep.produce request
    | produced request occurrences =>
        cases moved
        exact PipelineStep.observe request occurrences
    | observed request occurrences answers =>
        simp at moved

/-- Removing the vacuous `Unit` component gives an equivalence between whole
driver configurations and Zero's own control terms. -/
def pipelineConfigurationEquiv (model : Model) :
    (PipelineControl model × Unit) ≃ PipelineControl model where
  toFun := Prod.fst
  invFun := fun control => (control, ())
  left_inv := by
    intro configuration
    rcases configuration with ⟨control, ⟨⟩⟩
    rfl
  right_inv := by
    intro control
    rfl

/-- Strong control closure for Zero's semantic pipeline: the language-visible
control GSLT contains exactly every driver configuration and exactly every
driver move. -/
def pipelineControlReification (model : Model) :
    ControlReification (pipelineDriver model) (pipelineControlGSLT model) where
  configuration := pipelineConfigurationEquiv model
  step_iff := by
    intro source target
    rcases source with ⟨source, ⟨⟩⟩
    rcases target with ⟨target, ⟨⟩⟩
    change PipelineStep model source target ↔
      (pipelineDriver model).step source () = some (target, ())
    cases source with
    | classified request =>
        constructor
        · intro step
          cases step
          rfl
        · intro moved
          cases moved
          exact PipelineStep.produce request
    | produced request occurrences =>
        constructor
        · intro step
          cases step
          rfl
        · intro moved
          cases moved
          exact PipelineStep.observe request occurrences
    | observed request occurrences answers =>
        constructor
        · intro step
          cases step
        · intro moved
          simp [pipelineDriver] at moved

/-- The private driver state cannot affect any bounded observation.  This is
the observation-indexed criterion, not an assertion that all possible
schedulers or observers are interchangeable. -/
theorem pipelineDriver_privateStateInvariant (model : Model)
    {Observation : Type*}
    (observer : BoundedRunReport (PipelineControl model) Unit → Observation) :
    PrivateStateObservationInvariant (pipelineDriver model)
      (fun _ _ => True) observer :=
  privateStateObservationInvariant_of_subsingleton
    (pipelineDriver model) (fun first second => by cases first; cases second; rfl)
    (fun _ _ => True) observer

/-! ## Honest bounded execution and resumption -/

@[simp] theorem pipeline_runReport_zero (model : Model)
    (request : ClassifiedRequest model) :
    (pipelineDriver model).runReport (.classified request) () 0 =
      .expired (.classified request) () :=
  rfl

@[simp] theorem pipeline_runReport_one (model : Model)
    (request : ClassifiedRequest model) :
    (pipelineDriver model).runReport (.classified request) () 1 =
      .expired (.produced request (produce model request)) () :=
  rfl

@[simp] theorem pipeline_runReport_two (model : Model)
    (request : ClassifiedRequest model) :
    (pipelineDriver model).runReport (.classified request) () 2 =
      .completed
        (.observed request (produce model request) (run model request)) () :=
  rfl

/-- Expiration and completion are observably different even though the
residual produced term already determines the eventual answer bag. -/
theorem one_step_report_ne_completed (model : Model)
    (request : ClassifiedRequest model) :
    (pipelineDriver model).runReport (.classified request) () 1 ≠
      .completed (.produced request (produce model request)) () := by
  simp

/-- An expired Zero computation resumes from its retained classified control
term and reaches the same completed occurrence bag. -/
theorem pipeline_resume_from_zero (model : Model)
    (request : ClassifiedRequest model) :
    (pipelineDriver model).resume
        ((pipelineDriver model).runReport (.classified request) () 0) 2 =
      .completed
        (.observed request (produce model request) (run model request)) () := by
  simp

/-- Running the reified control pipeline to completion and observing its
public result agrees exactly with the generic interpreter over the authored
five-field Zero root. -/
theorem completed_runReport_agrees_with_authored (model : Model)
    (request : KernelRequest model) :
    let classified := classifiedRequest request
    ((pipelineDriver model).runReport (.classified classified) () 2).term
        |>.publicAnswers =
      (authoredRealization model).compile () request := by
  dsimp only
  rw [pipeline_runReport_two]
  simpa [completedPipelineArtifact, stagedRealization,
    PipelineControl.publicAnswers] using
    stagedRealization_agrees_with_authored model request

end Mettapedia.Languages.MeTTa.MeTTaZeroStagedAdequacy
