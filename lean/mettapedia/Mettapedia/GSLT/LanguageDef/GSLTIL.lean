import Mettapedia.GSLT.Core.IndexedOperational
import Mettapedia.GSLT.LanguageDef.ExtendedLanguageDef
import Mettapedia.GSLT.LanguageDef.LogicExtension
import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# The finite authored core of GSLT-IL

The abstract indexed command calculus has dependent states: a state belongs to
one GSLT fibre, and a route transports it to another fibre.  This module gives
that calculus one small authored `LanguageDef` boundary suitable for finite
execution and compilation.

There are two command forms:

* `at(stage, state)` computes inside one fibre;
* `via(kind, route, source, target, state)` exposes a requested transport.

The route kind is retained as data.  Forward translations, exact covered
translations, theory extensions, world revisions, observer changes, and
physical realizations must therefore be admitted by different catalog
entries; the runtime cannot silently treat them as one untyped arrow.

The three authored reductions are the three constructors of the abstract
indexed command step: compute at a fibre, compute underneath a pending route,
or apply the selected route.  Their premises query a finite catalog.  The
catalog is semantic input, not a host-language case split, and unsupported
commands remain inert.
-/

namespace Mettapedia.GSLT.LanguageDef.GSLTIL

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ExtensionComposition
open Mettapedia.GSLT.LanguageDef.LogicExtension
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.Framework.TypeSynthesis

/-! ## Authored syntax and relations -/

def stageType : TypeDecl := TypeDecl.plain "Stage"
def routeKindType : TypeDecl := TypeDecl.plain "RouteKind"
def routeType : TypeDecl := TypeDecl.plain "Route"
def stateType : TypeDecl := TypeDecl.plain "State"
def commandType : TypeDecl := TypeDecl.plain "Command"

private def constructor (label category : String)
    (parameters : List (String × TypeExpr)) : GrammarRule :=
  { label
    category
    params := parameters.map fun parameter =>
      .simple parameter.1 parameter.2
    syntaxPattern := [] }

/-- A returned state in one explicitly named fibre. -/
def atConstructor : GrammarRule :=
  constructor "at" "Command"
    [("stage", .base "Stage"), ("state", .base "State")]

/-- An outstanding typed transport request. -/
def viaConstructor : GrammarRule :=
  constructor "via" "Command"
    [("kind", .base "RouteKind"), ("route", .base "Route"),
      ("source", .base "Stage"), ("target", .base "Stage"),
      ("state", .base "State")]

def metavariable (name : String) : Pattern := .fvar name

def atPattern (stage state : Pattern) : Pattern :=
  .apply "at" [stage, state]

def viaPattern (kind route source target state : Pattern) : Pattern :=
  .apply "via" [kind, route, source, target, state]

def fibreStepRelation : String := "GSLTILFibreStep"
def transportRelation : String := "GSLTILTransport"

/-- Compute inside a returned fibre. -/
def fibreAtRewrite : RewriteRule :=
  { name := "gslt-il-fibre-at"
    typeContext :=
      [("stage", .base "Stage"), ("state", .base "State"),
        ("next", .base "State")]
    premises :=
      [.relationQuery fibreStepRelation
        [metavariable "stage", metavariable "state", metavariable "next"]]
    left := atPattern (metavariable "stage") (metavariable "state")
    right := atPattern (metavariable "stage") (metavariable "next") }

/-- Compute in the source fibre while transport remains explicit. -/
def fibreUnderViaRewrite : RewriteRule :=
  { name := "gslt-il-fibre-under-via"
    typeContext :=
      [("kind", .base "RouteKind"), ("route", .base "Route"),
        ("source", .base "Stage"), ("target", .base "Stage"),
        ("state", .base "State"), ("next", .base "State")]
    premises :=
      [.relationQuery fibreStepRelation
        [metavariable "source", metavariable "state", metavariable "next"]]
    left := viaPattern (metavariable "kind") (metavariable "route")
      (metavariable "source") (metavariable "target")
      (metavariable "state")
    right := viaPattern (metavariable "kind") (metavariable "route")
      (metavariable "source") (metavariable "target")
      (metavariable "next") }

/-- Apply one catalogued route and return in its target fibre. -/
def applyViaRewrite : RewriteRule :=
  { name := "gslt-il-apply-via"
    typeContext :=
      [("kind", .base "RouteKind"), ("route", .base "Route"),
        ("source", .base "Stage"), ("target", .base "Stage"),
        ("state", .base "State"), ("transported", .base "State")]
    premises :=
      [.relationQuery transportRelation
        [metavariable "kind", metavariable "route", metavariable "source",
          metavariable "target", metavariable "state",
          metavariable "transported"]]
    left := viaPattern (metavariable "kind") (metavariable "route")
      (metavariable "source") (metavariable "target")
      (metavariable "state")
    right := atPattern (metavariable "target")
      (metavariable "transported") }

/-- The catalog interfaces used by the three command rules. -/
def logicDeclarations : LogicProgram :=
  [.relation
      { name := fibreStepRelation
        argTypes := [.base "Stage", .base "State", .base "State"] },
   .relation
      { name := transportRelation
        argTypes :=
          [.base "RouteKind", .base "Route", .base "Stage", .base "Stage",
            .base "State", .base "State"] }]

def logicAuthoringLayer : CompositionalLayer LanguageDef :=
  CompositionalLayer.ofCodec LanguageDef logicCodec

/-- The finite GSLT-IL command language, authored as one compositional object. -/
def definition : ExtendedLanguageDef logicAuthoringLayer :=
  extendedLanguageDef!
    { name := "gslt-il-finite-indexed-command"
      types := [stageType, routeKindType, routeType, stateType, commandType]
      terms := [atConstructor, viaConstructor]
      equations := []
      rewrites := [fibreAtRewrite, fibreUnderViaRewrite, applyViaRewrite] }
    with layer (logicAuthoringLayer) { logicDeclarations }

abbrev language : LanguageDef := definition.toLanguageDef

private theorem rewrites_validate :
    ∀ rewrite ∈ language.rewrites,
      LanguageDef.validateRewrite language rewrite = [] := by
  intro rewrite rewriteMember
  change rewrite ∈
    [fibreAtRewrite, fibreUnderViaRewrite, applyViaRewrite] at rewriteMember
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at rewriteMember
  rcases rewriteMember with rfl | rfl | rfl
  all_goals
    simp [LanguageDef.validateRewrite, language, definition,
      fibreAtRewrite, fibreUnderViaRewrite, applyViaRewrite,
      atPattern, viaPattern, metavariable, fibreStepRelation,
      transportRelation, stageType, routeKindType, routeType, stateType,
      commandType, atConstructor, viaConstructor, constructor,
      LanguageDef.validatePatternConstructors,
      LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premisePatterns,
      LanguageDef.premiseFvarNames,
      LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseForAllParams, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, LanguageDef.typeNames]
  all_goals
    repeat' constructor

/-- The authored definition passes the ordinary structural validator. -/
theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  all_goals try decide
  exact rewrites_validate

def admittedLogic : AdmittedProgram language :=
  ⟨logicDeclarations, by decide⟩

@[simp] theorem authored_logic_roundTrip :
    logicAuthoringLayer.elaborate language definition.authoredSource =
      some logicDeclarations :=
  definition.elaborate_authoredSource

/-! ## A finite, language-visible execution catalog -/

/-- One admitted local transition row.  `occurrence` is proof-relevant
authorship identity.  Execution queries ignore it, but encodings retain it so
two extensionally equal authored rules do not become the same operation. -/
structure FibreRow where
  occurrence : Pattern
  stage : Pattern
  source : Pattern
  target : Pattern
  deriving DecidableEq

/-- One admitted transport row.  The kind remains explicit so that a forward
translation cannot be consumed where exact coverage or realization evidence
is required. -/
structure TransportRow where
  occurrence : Pattern
  kind : Pattern
  route : Pattern
  sourceStage : Pattern
  targetStage : Pattern
  source : Pattern
  target : Pattern
  deriving DecidableEq

/-- A finite executable fragment of an indexed diagram. -/
structure Catalog where
  fibreRows : List FibreRow
  transportRows : List TransportRow

def fibreTargets (catalog : Catalog) (stage source : Pattern) : List Pattern :=
  catalog.fibreRows.filterMap fun row =>
    if row.stage = stage ∧ row.source = source then some row.target else none

def transportTargets (catalog : Catalog) (kind route sourceStage targetStage
    source : Pattern) : List Pattern :=
  catalog.transportRows.filterMap fun row =>
    if row.kind = kind ∧ row.route = route ∧
        row.sourceStage = sourceStage ∧ row.targetStage = targetStage ∧
        row.source = source then
      some row.target
    else
      none

/-- The relation environment generated from a finite catalog. -/
def relationEnv (catalog : Catalog) : RelationEnv where
  tuples relation arguments :=
    match relation, arguments with
    | candidate, [stage, source, .fvar _] =>
        if candidate = fibreStepRelation then
          (fibreTargets catalog stage source).map fun target =>
            [stage, source, target]
        else
          []
    | candidate,
        [kind, route, sourceStage, targetStage, source, .fvar _] =>
        if candidate = transportRelation then
          (transportTargets catalog kind route sourceStage targetStage source).map
            fun target =>
              [kind, route, sourceStage, targetStage, source, target]
        else
          []
    | _, _ => []

/-- The GSLT denoted by the authored command language at one finite catalog. -/
def totalTheory (catalog : Catalog) : GSLT :=
  languageGSLTUsing (relationEnv catalog) language
    (ReductionRespectsEquationsUsing.of_equation_free _ rfl)

private theorem rules_noncontextual :
    ∀ rule, rule ∈ language.rewrites →
      NoncontextualPremises rule.premises := by
  intro rule ruleMember
  change rule ∈
    [fibreAtRewrite, fibreUnderViaRewrite, applyViaRewrite] at ruleMember
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ruleMember
  rcases ruleMember with rfl | rfl | rfl
  all_goals exact .relationQuery .nil

private theorem rootStep_iff_mem_executor (catalog : Catalog)
    (source target : Pattern) :
    RootStep (relationEnv catalog) language source target ↔
      target ∈ rewriteStepWithPremisesUsing
        (relationEnv catalog) language source := by
  simp [RootStep, rewriteStepWithPremisesUsing,
    applyRuleWithPremisesUsing]

/-- The authored total GSLT and the generic root executor expose the same
one-step relation. -/
theorem totalTheory_step_iff_mem_executor (catalog : Catalog)
    (source target : Pattern) :
    (totalTheory catalog).Step source target ↔
      target ∈ rewriteStepWithPremisesUsing
        (relationEnv catalog) language source := by
  unfold totalTheory
  rw [languageGSLTUsing_step]
  unfold langReducesUsing
  rw [step_iff_rootStep_of_noncontextualRules rules_noncontextual]
  exact rootStep_iff_mem_executor catalog source target

@[simp] private theorem match_fibre_tuple
    (stage state target : Pattern) :
    matchRelationArgs [("state", state), ("stage", stage)]
        [metavariable "stage", metavariable "state", metavariable "next"]
        [stage, state, target] =
      [[("next", target)]] := by
  simp [matchRelationArgs, matchRelationArgument, Bindings.lookup,
    mergeBindings, metavariable]

/-- A returned fibre command enumerates exactly the catalogued local
successors of its state. -/
theorem execute_at (catalog : Catalog) (stage state : Pattern) :
    rewriteStepWithPremisesUsing (relationEnv catalog) language
        (atPattern stage state) =
      (fibreTargets catalog stage state).map (atPattern stage) := by
  simp [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, relationEnv, language, definition,
    fibreAtRewrite, fibreUnderViaRewrite, applyViaRewrite,
    fibreStepRelation, transportRelation, atPattern, viaPattern,
    metavariable, matchPatternForRule, matchPatternForRuleUsing,
    applyBindingsForRule, applyBindingsForRuleUsing,
    matchPattern, matchArgs, mergeBindings, applyBindings]
  generalize fibreTargets catalog stage state = targets
  induction targets with
  | nil => rfl
  | cons target targets inductionHypothesis =>
      simp [matchRelationArgs, matchRelationArgument, Bindings.lookup,
        mergeBindings, atPattern, inductionHypothesis]

/-- A pending route exposes both kinds of enabled work without conflating
them: source-fibre steps retain the route, while a catalogued transport
returns an `at` command in the target fibre. -/
theorem execute_via (catalog : Catalog)
    (kind route sourceStage targetStage state : Pattern) :
    rewriteStepWithPremisesUsing (relationEnv catalog) language
        (viaPattern kind route sourceStage targetStage state) =
      (fibreTargets catalog sourceStage state).map
          (viaPattern kind route sourceStage targetStage) ++
        (transportTargets catalog kind route sourceStage targetStage state).map
          (atPattern targetStage) := by
  simp [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, relationEnv, language, definition,
    fibreAtRewrite, fibreUnderViaRewrite, applyViaRewrite,
    fibreStepRelation, transportRelation, atPattern, viaPattern,
    metavariable, matchPatternForRule, matchPatternForRuleUsing,
    applyBindingsForRule, applyBindingsForRuleUsing,
    matchPattern, matchArgs, mergeBindings, applyBindings]
  generalize fibreTargets catalog sourceStage state = fibreRows
  generalize transportTargets catalog kind route sourceStage targetStage state =
    transportRows
  congr 1
  · induction fibreRows with
    | nil => rfl
    | cons target targets inductionHypothesis =>
        simp [matchRelationArgs, matchRelationArgument, Bindings.lookup,
          mergeBindings, viaPattern, inductionHypothesis]
  · induction transportRows with
    | nil => rfl
    | cons target targets inductionHypothesis =>
        simp [matchRelationArgs, matchRelationArgument, Bindings.lookup,
          mergeBindings, atPattern, inductionHypothesis]

theorem mem_fibreTargets_iff (catalog : Catalog)
    (stage source target : Pattern) :
    target ∈ fibreTargets catalog stage source ↔
      ∃ row ∈ catalog.fibreRows,
        row.stage = stage ∧ row.source = source ∧ row.target = target := by
  simp [fibreTargets, and_assoc]

theorem mem_transportTargets_iff (catalog : Catalog)
    (kind route sourceStage targetStage source target : Pattern) :
    target ∈
        transportTargets catalog kind route sourceStage targetStage source ↔
      ∃ row ∈ catalog.transportRows,
        row.kind = kind ∧ row.route = route ∧
        row.sourceStage = sourceStage ∧ row.targetStage = targetStage ∧
        row.source = source ∧ row.target = target := by
  simp [transportTargets, and_assoc]

/-- The three intended wire-level command transitions, stated independently
of the generic language executor. -/
inductive WireStep (catalog : Catalog) : Pattern → Pattern → Prop where
  | fibreAt {row : FibreRow} :
      row ∈ catalog.fibreRows →
      WireStep catalog (atPattern row.stage row.source)
        (atPattern row.stage row.target)
  | fibreUnderVia {row : FibreRow} :
      row ∈ catalog.fibreRows →
      (kind route targetStage : Pattern) →
      WireStep catalog
        (viaPattern kind route row.stage targetStage row.source)
        (viaPattern kind route row.stage targetStage row.target)
  | applyVia {row : TransportRow} :
      row ∈ catalog.transportRows →
      WireStep catalog
        (viaPattern row.kind row.route row.sourceStage row.targetStage row.source)
        (atPattern row.targetStage row.target)

/-- Every direct wire transition is accepted by the authored executor. -/
theorem wireStep_mem_executor (catalog : Catalog) {source target : Pattern}
    (step : WireStep catalog source target) :
    target ∈ rewriteStepWithPremisesUsing
      (relationEnv catalog) language source := by
  cases step with
  | fibreAt rowMember =>
      rw [execute_at]
      simp only [List.mem_map]
      exact ⟨_,
        (mem_fibreTargets_iff catalog _ _ _).mpr
          ⟨_, rowMember, rfl, rfl, rfl⟩,
        rfl⟩
  | fibreUnderVia rowMember kind route targetStage =>
      rw [execute_via, List.mem_append]
      left
      simp only [List.mem_map]
      exact ⟨_,
        (mem_fibreTargets_iff catalog _ _ _).mpr
          ⟨_, rowMember, rfl, rfl, rfl⟩,
        rfl⟩
  | applyVia rowMember =>
      rw [execute_via, List.mem_append]
      right
      simp only [List.mem_map]
      exact ⟨_,
        (mem_transportTargets_iff catalog _ _ _ _ _ _).mpr
          ⟨_, rowMember, rfl, rfl, rfl, rfl, rfl, rfl⟩,
        rfl⟩

/-! ## Refinement from the dependent indexed command calculus -/

universe uTerm uIndex vIndex

/-- The finite catalog data needed to preserve a fragment of one dependent
indexed command diagram.  The two admission fields ensure that serialization
does not omit any abstract edge in the selected fragment.

This is deliberately only a step-preservation interface.  Proving that the
catalog invents no extra behavior is the separate step-reflection obligation
of an exact realization. -/
structure StepPreservingCommandEncoding
    {Index : Type uIndex} [CategoryTheory.Category.{vIndex} Index]
    (diagram : Diagram.{uTerm, uIndex, vIndex} Index) where
  catalog : Catalog
  encodeStage : Index → Pattern
  encodeState : ∀ stage,
    SemanticTerm (diagram.obj stage).theory → Pattern
  encodeRouteKind : ∀ {source target : Index},
    (source ⟶ target) → Pattern
  encodeRoute : ∀ {source target : Index},
    (source ⟶ target) → Pattern
  encodeFibreOccurrence : ∀ {stage : Index}
      {source target : SemanticTerm (diagram.obj stage).theory},
    SemanticStep (diagram.obj stage).theory source target → Pattern
  encodeTransportOccurrence : ∀ {source target : Index}
      (_route : source ⟶ target)
      (_state : SemanticTerm (diagram.obj source).theory), Pattern
  admitFibre : ∀ {stage : Index}
      {source target : SemanticTerm (diagram.obj stage).theory},
    (step : SemanticStep (diagram.obj stage).theory source target) →
      ({ occurrence := encodeFibreOccurrence step
         stage := encodeStage stage
         source := encodeState stage source
         target := encodeState stage target } : FibreRow) ∈ catalog.fibreRows
  admitTransport : ∀ {source target : Index}
      (route : source ⟶ target)
      (state : SemanticTerm (diagram.obj source).theory),
    ({ occurrence := encodeTransportOccurrence route state
       kind := encodeRouteKind route
       route := encodeRoute route
       sourceStage := encodeStage source
       targetStage := encodeStage target
       source := encodeState source state
       target := encodeState target (transportTerm diagram route state) } :
        TransportRow) ∈ catalog.transportRows

namespace StepPreservingCommandEncoding

variable {Index : Type uIndex} [CategoryTheory.Category.{vIndex} Index]
    {diagram : Diagram.{uTerm, uIndex, vIndex} Index}

/-- Serialize a dependent indexed command without erasing its source and
target fibre indices. -/
def encodeCommand (encoding : StepPreservingCommandEncoding diagram) :
    Command diagram → Pattern
  | .at stage state =>
      atPattern (encoding.encodeStage stage)
        (encoding.encodeState stage state)
  | .via (source := source) (target := target) route state =>
      viaPattern (encoding.encodeRouteKind route)
        (encoding.encodeRoute route)
        (encoding.encodeStage source) (encoding.encodeStage target)
        (encoding.encodeState source state)

/-- Every abstract dependent command edge becomes an admitted edge of the
independent finite wire relation. -/
theorem encodeStep_wire (encoding : StepPreservingCommandEncoding diagram)
    {source target : Command diagram}
    (step : Command.Step diagram source target) :
    WireStep encoding.catalog (encoding.encodeCommand source)
      (encoding.encodeCommand target) := by
  cases step with
  | fibre step =>
      simpa [encodeCommand] using
        WireStep.fibreAt (encoding.admitFibre step)
  | underVia route step =>
      simpa [encodeCommand] using
        WireStep.fibreUnderVia (encoding.admitFibre step)
          (encoding.encodeRouteKind route) (encoding.encodeRoute route)
          (encoding.encodeStage _)
  | applyVia route state =>
      simpa [encodeCommand] using
        WireStep.applyVia (encoding.admitTransport route state)

/-- The authored finite GSLT accepts every abstract command step whose
catalog rows were admitted by the encoding. -/
theorem encodeStep_preserved (encoding : StepPreservingCommandEncoding diagram)
    {source target : Command diagram}
    (step : Command.Step diagram source target) :
    (totalTheory encoding.catalog).Step
      (encoding.encodeCommand source) (encoding.encodeCommand target) := by
  rw [totalTheory_step_iff_mem_executor]
  exact wireStep_mem_executor encoding.catalog (encoding.encodeStep_wire step)

end StepPreservingCommandEncoding

/-- The command-shaped domain of the finite metalanguage.  Patterns outside
this domain are data and remain inert. -/
inductive WellFormedCommand : Pattern → Prop where
  | returned (stage state : Pattern) :
      WellFormedCommand (atPattern stage state)
  | pending (kind route sourceStage targetStage state : Pattern) :
      WellFormedCommand
        (viaPattern kind route sourceStage targetStage state)

/-- On every well-formed command, the authored GSLT is exactly the independent
wire relation. -/
theorem totalTheory_step_iff_wireStep (catalog : Catalog)
    {source target : Pattern} (wellFormed : WellFormedCommand source) :
    (totalTheory catalog).Step source target ↔ WireStep catalog source target := by
  cases wellFormed with
  | returned stage state =>
      rw [totalTheory_step_iff_mem_executor, execute_at]
      constructor
      · simp only [List.mem_map]
        rintro ⟨next, nextMember, rfl⟩
        obtain ⟨row, rowMember, rowStage, rowSource, rowTarget⟩ :=
          (mem_fibreTargets_iff catalog stage state next).mp nextMember
        subst rowStage
        subst rowSource
        subst rowTarget
        exact .fibreAt rowMember
      · intro step
        have accepted := wireStep_mem_executor catalog step
        rw [execute_at] at accepted
        exact accepted
  | pending kind route sourceStage targetStage state =>
      rw [totalTheory_step_iff_mem_executor, execute_via]
      constructor
      · rw [List.mem_append]
        rintro (localMember | transportMember)
        · simp only [List.mem_map] at localMember
          obtain ⟨next, nextMember, rfl⟩ := localMember
          obtain ⟨row, rowMember, rowStage, rowSource, rowTarget⟩ :=
            (mem_fibreTargets_iff catalog sourceStage state next).mp nextMember
          subst rowStage
          subst rowSource
          subst rowTarget
          exact .fibreUnderVia rowMember kind route targetStage
        · simp only [List.mem_map] at transportMember
          obtain ⟨transported, transportedMember, rfl⟩ := transportMember
          obtain ⟨row, rowMember, rowKind, rowRoute, rowSourceStage,
              rowTargetStage, rowSource, rowTarget⟩ :=
            (mem_transportTargets_iff catalog kind route sourceStage targetStage
              state transported).mp transportedMember
          subst rowKind
          subst rowRoute
          subst rowSourceStage
          subst rowTargetStage
          subst rowSource
          subst rowTarget
          exact .applyVia rowMember
      · intro step
        have accepted := wireStep_mem_executor catalog step
        rw [execute_via] at accepted
        exact accepted

namespace StepPreservingCommandEncoding

variable {Index : Type uIndex} [CategoryTheory.Category.{vIndex} Index]
    {diagram : Diagram.{uTerm, uIndex, vIndex} Index}

/-- Encoded abstract commands always inhabit the command-shaped fragment of
the authored language. -/
theorem encodeCommand_wellFormed
    (encoding : StepPreservingCommandEncoding diagram)
    (command : Command diagram) :
    WellFormedCommand (encoding.encodeCommand command) := by
  cases command <;> constructor

/-- The separately named no-invention obligation for a finite realization.
Step preservation alone does not provide this direction. -/
def StepReflecting (encoding : StepPreservingCommandEncoding diagram) : Prop :=
  ∀ {source target : Command diagram},
    WireStep encoding.catalog (encoding.encodeCommand source)
        (encoding.encodeCommand target) →
      Nonempty (Command.Step diagram source target)

/-- Once both preservation and reflection are supplied, the authored finite
GSLT is exactly adequate on encoded dependent commands. -/
theorem authored_step_iff_abstract_step
    (encoding : StepPreservingCommandEncoding diagram)
    (reflecting : StepReflecting encoding)
    {source target : Command diagram} :
    (totalTheory encoding.catalog).Step
        (encoding.encodeCommand source) (encoding.encodeCommand target) ↔
      Nonempty (Command.Step diagram source target) := by
  constructor
  · intro authoredStep
    apply reflecting
    exact (totalTheory_step_iff_wireStep encoding.catalog
      (encoding.encodeCommand_wellFormed source)).mp authoredStep
  · rintro ⟨abstractStep⟩
    exact encoding.encodeStep_preserved abstractStep

end StepPreservingCommandEncoding

/-- An unknown top-level form is neither accidentally interpreted nor
reported as a host-language error. -/
theorem unknown_command_inert (catalog : Catalog) (arguments : List Pattern) :
    rewriteStepWithPremisesUsing (relationEnv catalog) language
        (.apply "unknown" arguments) = [] := by
  simp [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    language, definition, fibreAtRewrite, fibreUnderViaRewrite,
    applyViaRewrite, atPattern, viaPattern, metavariable,
    matchPatternForRule, matchPatternForRuleUsing, matchPattern]

/-- The direct finite command relation is itself a GSLT. -/
def wireGSLT (catalog : Catalog) : GSLT where
  Term := Pattern
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := WireStep catalog
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

end Mettapedia.GSLT.LanguageDef.GSLTIL
