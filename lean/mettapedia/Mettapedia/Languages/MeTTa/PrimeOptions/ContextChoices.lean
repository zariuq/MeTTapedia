import Mettapedia.GSLT.Distinction.OptionGraph
import Mettapedia.GSLT.Causality.ContextChoicePoints
import Mettapedia.GSLT.Causality.UniqueSolution
import Mettapedia.GSLT.Causality.AdaptiveExpressibility

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

Where theorems now carry a record's argument (`Placement.upgrade`), they replace it as
evidence and the argument stays on the verdict as history. Two arguments are upgraded:
when a meta-level observer can state the adaptive query as a formula, and Halpern's
class of models with one solution under every surgery, which gets an option of its own
between the recursive models and all models, with two restriction arrows and two
witnesses.
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
  /-- The kind of the arrow between the two options. -/
  arrowKind : ArrowKind
  /-- The arrow runs from the top to the restricted option, as a restriction or a
  reading of the top; otherwise from the restricted option into the top. -/
  fromTop : Bool := false
  /-- What the arrow preserves and what it does not. -/
  contract : Contract := {}
  /-- Theorems that now carry the record's arguments. When there are any, they replace the
  arguments as evidence, and the arguments stay on the verdict as history. -/
  upgrade : List Name := []

def placements : List Placement := [
  { number := 0
    recordTheorem := ``Mettapedia.GSLT.Causality.ContextChoicePoints.explicitDo_record
    arrowKind := .unclassified
    contract := {
      entries := [
        .keeps .distinctions
          [``Mettapedia.GSLT.Causality.ContextBindings.OverrideAction.explicit_derived_agree]
          "on values: the same agreement at every rung",
        .loses (.evidence .cost)
          [``Mettapedia.GSLT.Causality.ContextBindings.explicitDraws_doBinding,
           ``Mettapedia.GSLT.Causality.ContextBindings.derivedDraws_doBinding]
          "an unread binding is drawn once explicitly and never when derived"] }
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
    arrowKind := .restriction
    fromTop := true
    contract := {
      entries := [
        .loses .distinctions
          [``Mettapedia.GSLT.Dynamics.DemandAgreement.coin_uses]
          "what the other strategies show on a coin"] }
    question := none
    options := []
    restricted := "laziness-global", general := "strategy-bubbles"
    observer := "strategy-observations-kept"
    arrowId := "bubbles-to-one-strategy", witnessId := "coin-uses"
    case := "A coin used zero times and twice."
    restrictedReading := "Lost: discarded, the strategies give different outcome bags on the \
      coin, and copied, different outcome sets, so one strategy for every program cannot give \
      the others' answers."
    generalReading := "Kept: the three strategies agree exactly on the discarding and copying \
      lines, and each is a bubble with that guarantee." },
  { number := 2
    recordTheorem := ``Mettapedia.GSLT.Causality.ContextChoicePoints.provenance_record
    arrowKind := .observationalQuotient
    fromTop := true
    contract := {
      entries := [
        .keeps .distinctions
          [``Mettapedia.GSLT.Causality.AbstractionControls.Forgetful.passive_isometry]
          "passive distances",
        .loses (.evidence .provenance)
          [``Mettapedia.GSLT.Causality.AbstractionControls.Forgetful.collapses_mixed_fixed,
           ``Mettapedia.GSLT.Causality.Hierarchy.ResponseTypes.not_counterfactual_mixed_fixed]
          "the retained unit: a rung-three answer is lost"] }
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
    arrowId := "provenance-read-forgetfully", witnessId := "forgotten-mixed-and-fixed"
    case := "The mixed and the fixed populations, read after forgetting their response types."
    restrictedReading := "Identified: forgetting keeps every passive distance and puts the two \
      at counterfactual distance zero."
    generalReading := "Kept apart: one population has a unit for which treatment is necessary \
      and sufficient and the other has none; the twin built from the shared draw tells them \
      apart, the experiment does not." },
  { number := 3
    recordTheorem := ``Mettapedia.GSLT.Causality.ContextChoicePoints.firstClass_record
    arrowKind := .restriction
    fromTop := true
    contract := {
      entries := [
        .keeps .verdicts
          [``Mettapedia.GSLT.Causality.AdaptiveContexts.internal_do_eq_external]
          "a meta-level intervention is the constant policy",
        .loses .distinctions
          [``Mettapedia.GSLT.Causality.AdaptiveContexts.adaptive_not_meta]
          "the adaptive program has no meta-level counterpart on the same model"] }
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
    arrowId := "first-class-to-meta", witnessId := "adaptive-policy"
    case := "A policy that treats each unit of a two-unit population according to its covariate."
    restrictedReading := "Not expressed on the given model: no meta-level intervention on it \
      behaves like the adaptive program, even at rung one, while a re-encoded model does. As a \
      formula, relative to the same meta-level contexts (one treatment imposed on every unit) \
      and the observer of quantities, the adaptive query is stated exactly when the formula \
      may read the treatment atom: one formula that reads it states the query, and no formula \
      of effect atoms alone does."
    generalReading := "Expressed: the policy is a context built from the observed covariate."
    argumentAnchor := "Choice 3, the precise sense of the separation"
    upgrade := [``Mettapedia.GSLT.Causality.AdaptiveExpressibility.expressible_exactly_when_covariate,
      ``Mettapedia.GSLT.Causality.AdaptiveExpressibility.effectOnly_cannot_express,
      ``Mettapedia.GSLT.Causality.AdaptiveExpressibility.adaptiveFormula_reads_covariate] },
  { number := 4
    recordTheorem := ``Mettapedia.GSLT.Causality.ContextChoicePoints.region_record
    arrowKind := .restriction
    fromTop := true
    contract := {
      entries := [
        .loses .distinctions
          [``Mettapedia.GSLT.Causality.ContextOperatorsControls.OneShot.region_witness]
          "environments differing in a secret behind a guard outside the region"] }
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
    arrowId := "unrestricted-to-region", witnessId := "guarded-secret"
    case := "The law 'guard and secret' with the region {open}: environments that differ only in \
      the secret."
    restrictedReading := "Identified at every rung: the region cannot bind the guard."
    generalReading := "Kept apart at rung two: binding the guard, outside the region, separates \
      them." },
  { number := 5
    recordTheorem := ``Mettapedia.GSLT.Causality.ContextChoicePoints.weights_record
    arrowKind := .observationalQuotient
    fromTop := true
    contract := {
      entries := [
        .loses .distinctions
          [``Mettapedia.GSLT.Causality.WeightedResponseTypes.erasure_strict]
          "two populations with equal supports"] }
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
    arrowId := "weights-to-possibility", witnessId := "equal-supports"
    case := "Two populations with equal supports, mostly helped and mostly always affected."
    restrictedReading := "Identified at every possibilistic rung."
    generalReading := "Kept apart at every weighted rung." },
  { number := 6
    recordTheorem := ``Mettapedia.GSLT.Causality.ContextChoicePoints.structural_record
    arrowKind := .restriction
    fromTop := true
    contract := {
      entries := [
        .keeps .laws
          [``Mettapedia.GSLT.Causality.StructuralModels.surgery_exists_unique_solution]
          "interventions stay inside: a recursive model has one solution before and after every surgery",
        .loses .verdicts
          [``Mettapedia.GSLT.Causality.StructuralModels.copyLoop_two_solutions,
           ``Mettapedia.GSLT.Causality.StructuralModels.negLoop_no_solution]
          "feedback models have two solutions or none, outside the bubble"] }
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
    arrowId := "causal-bubbles-to-recursive", witnessId := "feedback-loops"
    case := "The copying loop and the negating loop."
    restrictedReading := "Not hosted: neither loop is recursive. Between the recursive models \
      and all models lies the class with one solution under every surgery: a mutual cycle is \
      in it and is not recursive, both loops are outside it, it is closed under surgery, and in \
      it a property of some solution is a property of every solution."
    generalReading := "Hosted: both loops are terms of one GSLT, the copying loop with two \
      solutions and the negating loop with none."
    argumentAnchor := "Choice 6, argument"
    upgrade := [``Mettapedia.GSLT.Causality.UniqueSolution.cycle_strict,
      ``Mettapedia.GSLT.Causality.UniqueSolution.below_every_mechanism,
      ``Mettapedia.GSLT.Causality.UniqueSolution.unique_closed_under_surgery,
      ``Mettapedia.GSLT.Causality.UniqueSolution.some_solution_iff_every] },
  { number := 7
    recordTheorem := ``Mettapedia.GSLT.Causality.ContextChoicePoints.gradedIdentity_record
    arrowKind := .observationalQuotient
    fromTop := true
    contract := {
      entries := [
        .loses .distinctions
          [``Mettapedia.GSLT.Causality.AbstractionControls.ResponseGraded.interventionalDistance_wouldHelp_inert,
           ``Mettapedia.GSLT.Causality.AbstractionControls.ResponseGraded.counterfactualDistance_mixed_fixed]
          "the grades of pairs a coarser rung identifies"] }
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
    arrowId := "graded-to-fixed-equality", witnessId := "graded-gaps"
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

/-- The embedding of the restricted option in the top. -/
def arrowOf (placement : Placement) (record : Record) : Arrow where
  id := placement.arrowId
  source := if placement.fromTop then placement.general else placement.restricted
  target := if placement.fromTop then placement.restricted else placement.general
  kind := placement.arrowKind
  grades := [.ungraded]
  summary := if placement.fromTop then
      "The top restricted to, or read as, the restricted option; the cited theorems state \
      the restricted option's guarantee."
    else
      "The restricted option read inside the top; the cited theorems state its guarantee."
  evidence := cites record.embedding ::
    if record.embeddingEvidence.contains .fixture then fixturesOf record else []
  contract := placement.contract

/-- The separating witness. -/
def witnessOf (placement : Placement) (record : Record) : Witness where
  id := placement.witnessId
  observer := placement.observer
  left := placement.restricted
  right := placement.general
  case := placement.case
  leftVerdict := {
    reading := placement.restrictedReading
    evidence := cites (record.witness ++ [placement.recordTheorem]) ::
      if !record.witnessEvidence.contains .argument then []
      else if placement.upgrade.isEmpty then argumentsOf placement record
      else [cites placement.upgrade]
    superseded :=
      if record.witnessEvidence.contains .argument && !placement.upgrade.isEmpty then
        argumentsOf placement record
      else [] }
  rightVerdict := {
    reading := placement.generalReading
    evidence := cites (record.witness ++ [placement.recordTheorem]) ::
      if record.witnessEvidence.contains .fixture then fixturesOf record else [] }

/-! ## Halpern's class between the recursive models and all models -/

/-- Models with one solution under every surgery. -/
def uniqueSolutionNode : Node where
  id := "unique-solution-models"
  question := "causal-calculus"
  title := "One solution under every surgery"
  summary := "Halpern's class of nonrecursive models: every setting of the endogenous keys has \
    exactly one solution, so the some-solution and every-solution readings agree."
  facts := [cites [``Mettapedia.GSLT.Causality.UniqueSolution.some_solution_iff_every,
    ``Mettapedia.GSLT.Causality.UniqueSolution.counterfactual_exists_unique,
    ``Mettapedia.GSLT.Causality.UniqueSolution.unique_closed_under_surgery]]

/-- The two restrictions: all models to the class, and the class to the recursive models. -/
def uniqueSolutionArrows : List Arrow := [
  { id := "causal-bubbles-to-unique-solution", source := "causal-bubbles"
    target := "unique-solution-models", kind := .restriction, grades := [.ungraded]
    summary := "The models with one solution under every surgery, among all models."
    evidence := [cites [``Mettapedia.GSLT.Causality.UniqueSolution.below_every_mechanism,
      ``Mettapedia.GSLT.Causality.UniqueSolution.unique_closed_under_surgery]]
    contract := {
      entries := [
        .keeps .laws [``Mettapedia.GSLT.Causality.UniqueSolution.unique_closed_under_surgery]
          "interventions stay inside: a surgery of a model in the class is in the class",
        .loses .verdicts [``Mettapedia.GSLT.Causality.UniqueSolution.copyLoop_outside,
          ``Mettapedia.GSLT.Causality.UniqueSolution.negLoop_outside]
          "the copying loop and the negating loop are outside"] } },
  { id := "unique-solution-to-recursive", source := "unique-solution-models"
    target := "one-causal-calculus", kind := .restriction, grades := [.ungraded]
    summary := "The recursive models among those with one solution under every surgery; a \
      recursive model needs a store to seed its solution."
    evidence := [cites [``Mettapedia.GSLT.Causality.UniqueSolution.recursive_unique_under_every_surgery,
      ``Mettapedia.GSLT.Causality.UniqueSolution.empty_recursive_outside,
      ``Mettapedia.GSLT.Causality.UniqueSolution.cycle_strict]]
    contract := {
      entries := [
        .keeps .laws
          [``Mettapedia.GSLT.Causality.UniqueSolution.recursive_unique_under_every_surgery]
          "a recursive model with a store has one solution under every surgery",
        .loses .verdicts [``Mettapedia.GSLT.Causality.UniqueSolution.cycle_strict,
          ``Mettapedia.GSLT.Causality.UniqueSolution.cycle_not_recursive]
          "the mutual cycle: one solution under every surgery, and no rank"]
      hypotheses := [``Nonempty] } }]

/-- The two witnesses that separate the class from its neighbours. -/
def uniqueSolutionWitnesses : List Witness := [
  { id := "mutual-cycle", observer := "solutions"
    left := "one-causal-calculus", right := "unique-solution-models"
    case := "Two cells over three values, each computed from the other: left sends a, b, c to \
      a, a, c and right sends them to a, a, b."
    leftVerdict := {
      reading := "Not hosted: each cell reads the other, so no rank makes the model recursive."
      evidence := [cites [``Mettapedia.GSLT.Causality.UniqueSolution.cycle_not_recursive,
        ``Mettapedia.GSLT.Causality.UniqueSolution.cycle_left_depends_on_right,
        ``Mettapedia.GSLT.Causality.UniqueSolution.cycle_right_depends_on_left]] }
    rightVerdict := {
      reading := "Hosted: every surgery has exactly one solution."
      evidence := [cites [``Mettapedia.GSLT.Causality.UniqueSolution.cycle_unique_under_every_surgery,
        ``Mettapedia.GSLT.Causality.UniqueSolution.cycle_strict]] } },
  { id := "loops-outside-the-class", observer := "solutions"
    left := "unique-solution-models", right := "causal-bubbles"
    case := "The copying loop and the negating loop."
    leftVerdict := {
      reading := "Not hosted: with nothing imposed the copying loop has two solutions and the \
        negating loop none."
      evidence := [cites [``Mettapedia.GSLT.Causality.UniqueSolution.copyLoop_outside,
        ``Mettapedia.GSLT.Causality.UniqueSolution.negLoop_outside,
        ``Mettapedia.GSLT.Causality.UniqueSolution.below_every_mechanism]] }
    rightVerdict := {
      reading := "Hosted: both loops are models, the copying loop with two solutions and the \
        negating loop with none."
      evidence := [cites [``Mettapedia.GSLT.Causality.StructuralModels.copyLoop_two_solutions,
        ``Mettapedia.GSLT.Causality.StructuralModels.negLoop_no_solution]] } }]

def questions : List Question := placements.filterMap (·.question)

def nodes : List Node := placements.flatMap (·.options) ++ [uniqueSolutionNode]

def arrows : List Arrow :=
  placements.filterMap (fun placement => (recordOf placement).map (arrowOf placement)) ++
    uniqueSolutionArrows

def witnesses : List Witness :=
  placements.filterMap (fun placement => (recordOf placement).map (witnessOf placement)) ++
    uniqueSolutionWitnesses

/-- Every record is placed. -/
theorem every_record_placed :
    records.map (·.number) = placements.map (·.number) := by
  decide +kernel

/-- An upgraded verdict cites no argument, and keeps the arguments it replaced as history. -/
theorem upgrades_replace_arguments :
    (placements.filter (!·.upgrade.isEmpty)).map (fun placement =>
      (placement.number, ((recordOf placement).map fun record =>
        let verdict := (witnessOf placement record).leftVerdict
        (verdict.evidence.all (·.kind != .argument), verdict.superseded.length)))) =
      [(3, some (true, 1)), (6, some (true, 1))] := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PrimeOptions.ContextChoices
