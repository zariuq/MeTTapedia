import Mettapedia.GSLT.Distinction.OptionGraph
import Mettapedia.GSLT.Causality.ContextChoicePoints

/-!
# The choice points of the context operators, placed in the option graph

`GSLT.Causality.ContextChoicePoints.records` holds eight choice points of the
context operators. Each pairs a restricted option with a general top, names the
theorems that embed the restricted option in the top with its guarantee and the
theorems of a separating witness, the C fixtures that exhibit the choice, and
the parts recorded as arguments. This module places each record in the option
graph without restating any of that: the embedding becomes an arrow from the
restricted option to the top, and the witness a witness between them. Both
verdicts cite the witness theorems and the record's conjunction theorem; the
record's fixtures support the top's verdict and its arguments qualify the
restricted option's verdict.

What is written here is placement and prose: the question each record answers,
the two options' identifiers and titles, the observer, the concrete case and the
reading of each verdict. The evidence for strategies joins the existing question
on the scope of the demand strategy instead of opening a second one.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeOptions.ContextChoices

open Lean (Name)
open Mettapedia.GSLT.Distinction.OptionGraph
open Mettapedia.GSLT.Causality.ContextChoicePoints (Record records)

/-- The report that records the arguments of the choice points. -/
def report : Document where
  key := "context-choices-report-20261005"
  title := "Causal programs on three faces, the context operators, and the over-limit audit: report"
  date := "2026-10-05"

/-- Where a record goes in the graph, and how its verdicts read. -/
structure Placement where
  number : Nat
  /-- The question, when the record opens one. -/
  question : Option Question
  /-- The options the record adds; empty when both exist already. -/
  options : List Node
  restricted : String
  general : String
  observer : String
  arrowId : String
  witnessId : String
  case : String
  restrictedReading : String
  generalReading : String
  /-- The heading of the report where the record's arguments are made. -/
  argumentAnchor : String := ""
  /-- The conjunction theorem that states the record's guarantee and witness together. -/
  recordTheorem : Name

def placements : List Placement := [
  { number := 0
    recordTheorem := ``Mettapedia.GSLT.Causality.ContextChoicePoints.explicitDo_record
    question := some
      { id := "explicit-do"
        title := "Explicit or derived do"
        summary := "Whether an intervention is one simultaneous assignment or is derived from \
          binding override with the newest binding winning. On values over finitely many keys \
          the two have one ladder; over infinitely many keys one explicit assignment separates \
          stores that no chain of bindings separates; on computations explicit do is eager." }
    options := [
      { id := "explicit-do", question := "explicit-do", title := "Explicit do"
        summary := "One simultaneous assignment of values to keys." },
      { id := "derived-do", question := "explicit-do", title := "Derived do"
        summary := "Do derived from binding override (ctx:bind), the newest binding winning." }]
    restricted := "explicit-do", general := "derived-do", observer := "override-law"
    arrowId := "explicit-do-in-derived", witnessId := "shadowed-intervention"
    case := "An intervention on a key that a newer intervention on the same key shadows."
    restrictedReading := "The shadowed computation still runs: the override law holds only when \
      it has one answer or the newer one has none."
    generalReading := "The override law always holds: the newest binding wins and the shadowed \
      computation is never drawn." },
  { number := 1
    recordTheorem := ``Mettapedia.GSLT.Causality.ContextChoicePoints.strategy_record
    question := none
    options := []
    restricted := "laziness-global", general := "strategy-bubbles"
    observer := "strategy-observations-kept"
    arrowId := "one-strategy-in-bubbles", witnessId := "coin-uses"
    case := "A coin used zero times and twice."
    restrictedReading := "Lost: discarded, the strategies give different outcome bags on the \
      coin, and copied, different outcome sets, so one strategy for every program cannot give \
      the others' answers."
    generalReading := "Kept: the three strategies agree exactly on the discarding and copying \
      lines, and each is a bubble with that guarantee." },
  { number := 2
    recordTheorem := ``Mettapedia.GSLT.Causality.ContextChoicePoints.provenance_record
    question := some
      { id := "provenance"
        title := "Readouts with or without provenance"
        summary := "Whether readouts forget the retained unit and the occurrence, or keep them." }
    options := [
      { id := "forgetful-readouts", question := "provenance", title := "Forgetful readouts"
        summary := "Readouts that forget response types and occurrences." },
      { id := "provenance-readouts", question := "provenance",
        title := "Readouts that keep provenance"
        summary := "Readouts that keep the retained unit and the occurrence." }]
    restricted := "forgetful-readouts", general := "provenance-readouts"
    observer := "option-agreement"
    arrowId := "forgetful-in-provenance", witnessId := "forgotten-mixed-and-fixed"
    case := "The mixed and the fixed populations, read after forgetting their response types."
    restrictedReading := "Identified: forgetting keeps every passive distance and puts the two \
      at counterfactual distance zero."
    generalReading := "Kept apart: one population has a unit for which treatment is necessary \
      and sufficient and the other has none; the twin built from the shared draw tells them \
      apart, the experiment does not." },
  { number := 3
    recordTheorem := ``Mettapedia.GSLT.Causality.ContextChoicePoints.firstClass_record
    question := some
      { id := "first-class-contexts"
        title := "Contexts at the meta level or first-class"
        summary := "Whether interventions are only applied from outside a model, or contexts are \
          values a program can build." }
    options := [
      { id := "meta-contexts", question := "first-class-contexts",
        title := "Contexts only at the meta level"
        summary := "Interventions applied from outside: the constant policies." },
      { id := "first-class-contexts", question := "first-class-contexts",
        title := "First-class contexts"
        summary := "Contexts are values; a policy may build one from what it observes." }]
    restricted := "meta-contexts", general := "first-class-contexts"
    observer := "adaptive-program"
    arrowId := "meta-in-first-class", witnessId := "adaptive-policy"
    case := "A policy that treats each unit of a two-unit population according to its covariate."
    restrictedReading := "Not expressed on the given model: no meta-level intervention on it \
      behaves like the adaptive program, even at rung one, while a re-encoded model does. \
      Whether a meta-only observer can state the adaptive query as a formula is not proved."
    generalReading := "Expressed: the policy is a context built from the observed covariate."
    argumentAnchor := "Choice 3, the precise sense of the separation" },
  { number := 4
    recordTheorem := ``Mettapedia.GSLT.Causality.ContextChoicePoints.region_record
    question := some
      { id := "region-interventions"
        title := "Region-bounded or unrestricted interventions"
        summary := "Whether interventions may bind only the keys of a region, or any key. This \
          concerns interventions on causal models, not the observers of the λ-to-ρ compiler." }
    options := [
      { id := "region-interventions", question := "region-interventions",
        title := "Region-bounded interventions"
        summary := "Contexts that bind only keys of a given region." },
      { id := "unrestricted-interventions", question := "region-interventions",
        title := "Unrestricted interventions"
        summary := "Contexts that may bind any key." }]
    restricted := "region-interventions", general := "unrestricted-interventions"
    observer := "option-agreement"
    arrowId := "region-in-unrestricted", witnessId := "guarded-secret"
    case := "The law 'guard and secret' with the region {open}: environments that differ only in \
      the secret."
    restrictedReading := "Identified at every rung: the region cannot bind the guard."
    generalReading := "Kept apart at rung two: binding the guard, outside the region, separates \
      them." },
  { number := 5
    recordTheorem := ``Mettapedia.GSLT.Causality.ContextChoicePoints.weights_record
    question := some
      { id := "possibility-weights"
        title := "Possibility or weights"
        summary := "Whether causal populations are read by which outcomes are possible or by how \
          much weight each carries." }
    options := [
      { id := "possibility", question := "possibility-weights", title := "Possibility"
        summary := "The support of a population: which outcomes are possible." },
      { id := "weights", question := "possibility-weights", title := "Weights"
        summary := "The weighted population." }]
    restricted := "possibility", general := "weights", observer := "option-agreement"
    arrowId := "possibility-in-weights", witnessId := "equal-supports"
    case := "Two populations with equal supports, mostly helped and mostly always affected."
    restrictedReading := "Identified at every possibilistic rung."
    generalReading := "Kept apart at every weighted rung." },
  { number := 6
    recordTheorem := ``Mettapedia.GSLT.Causality.ContextChoicePoints.structural_record
    question := some
      { id := "causal-calculus"
        title := "One causal calculus or causal theories as bubbles"
        summary := "Whether one causal calculus is fixed in the kernel, or causal theories are \
          bubbles of the GSLT top." }
    options := [
      { id := "one-causal-calculus", question := "causal-calculus",
        title := "One causal calculus in the kernel"
        summary := "Recursive structural models: one solution before and after every \
          intervention." },
      { id := "causal-bubbles", question := "causal-calculus",
        title := "Causal theories as bubbles"
        summary := "Causal theories as bubbles of the GSLT top, which hosts recursive and \
          feedback models alike." }]
    restricted := "one-causal-calculus", general := "causal-bubbles", observer := "solutions"
    arrowId := "recursive-in-bubbles", witnessId := "feedback-loops"
    case := "The copying loop and the negating loop."
    restrictedReading := "Not hosted: neither loop is recursive. A class between the recursive \
      models and all models is not exhibited."
    generalReading := "Hosted: both loops are terms of one GSLT, the copying loop with two \
      solutions and the negating loop with none."
    argumentAnchor := "Choice 6, argument" },
  { number := 7
    recordTheorem := ``Mettapedia.GSLT.Causality.ContextChoicePoints.gradedIdentity_record
    question := some
      { id := "graded-identity"
        title := "One fixed equality or graded identity"
        summary := "Whether one equality is fixed, or the three rung equalities are the zero \
          kernels of three distances." }
    options := [
      { id := "fixed-equality", question := "graded-identity", title := "One fixed equality"
        summary := "One equivalence decides identity." },
      { id := "graded-identity", question := "graded-identity", title := "Graded identity"
        summary := "Three rung equalities and their distances." }]
    restricted := "fixed-equality", general := "graded-identity", observer := "option-agreement"
    arrowId := "fixed-in-graded", witnessId := "graded-gaps"
    case := "A population treatment would help against an inert one, and the mixed against the \
      fixed population."
    restrictedReading := "One verdict per pair: association identifies the first pair and \
      intervention the second."
    generalReading := "Graded: passive distance zero against interventional distance at least \
      the square of the discount, and interventional distance zero against counterfactual \
      distance at least that." }
]

/-- The observers the placements introduce. -/
def observers : List Observer := [
  { id := "override-law", title := "Override law of an intervention"
    reads := "The outcome bags and draws of a shadowed intervention, and whether the newest \
      binding wins."
    kind := .«theorem» },
  { id := "option-agreement", title := "Agreement under the option"
    reads := "Whether the option's equivalence, at each rung, identifies the two cases."
    kind := .«theorem», identifies := true },
  { id := "adaptive-program", title := "An adaptive program"
    reads := "Whether the option expresses a policy that builds its context from the observed \
      covariate."
    kind := .«theorem» },
  { id := "solutions", title := "Solutions of a model"
    reads := "How many solutions a model has, before and after intervention."
    kind := .«theorem» }
]

/-- The record numbered as the placement. -/
def recordOf (placement : Placement) : Option Record :=
  records.find? (·.number == placement.number)

/-- The record's fixtures, cited whole. -/
def fixturesOf (record : Record) : List Evidence :=
  record.fixtures.map fun path => .fixture "c-draft" path []

/-- The record's arguments, at the report's heading. -/
def argumentsOf (placement : Placement) (record : Record) : List Evidence :=
  record.arguments.map fun claim => .argument report.key placement.argumentAnchor claim

def citations (names : List Name) : Evidence :=
  .«theorem» (names.map fun name => { declaration := name })

/-- The embedding of the restricted option in the top. -/
def arrowOf (placement : Placement) (record : Record) : Arrow where
  id := placement.arrowId
  source := placement.restricted
  target := placement.general
  kind := .interpretation
  grades := [.ungraded]
  summary := "The restricted option embedded in the top as a bubble; the cited theorems state \
    its guarantee."
  evidence := citations record.embedding ::
    if record.embeddingEvidence.contains .fixture then fixturesOf record else []

/-- The separating witness. -/
def witnessOf (placement : Placement) (record : Record) : Witness where
  id := placement.witnessId
  observer := placement.observer
  left := placement.restricted
  right := placement.general
  case := placement.case
  leftVerdict := {
    reading := placement.restrictedReading
    evidence := citations (record.witness ++ [placement.recordTheorem]) ::
      if record.witnessEvidence.contains .argument then argumentsOf placement record else [] }
  rightVerdict := {
    reading := placement.generalReading
    evidence := citations (record.witness ++ [placement.recordTheorem]) ::
      if record.witnessEvidence.contains .fixture then fixturesOf record else [] }

def questions : List Question := placements.filterMap (·.question)

def nodes : List Node := placements.flatMap (·.options)

def arrows : List Arrow :=
  placements.filterMap fun placement => (recordOf placement).map (arrowOf placement)

def witnesses : List Witness :=
  placements.filterMap fun placement => (recordOf placement).map (witnessOf placement)

/-- Every record is placed. -/
theorem every_record_placed :
    records.map (·.number) = placements.map (·.number) := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PrimeOptions.ContextChoices
