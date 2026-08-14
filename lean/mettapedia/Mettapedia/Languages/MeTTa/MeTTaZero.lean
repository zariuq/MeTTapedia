import Mettapedia.GSLT.Core.Composition
import Mettapedia.GSLT.Dynamics.AnswerEffect
import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.GSLT.LanguageDef.ExtensionComposition
import Mettapedia.GSLT.LanguageDef.ExtendedLanguageDef
import Mettapedia.GSLT.LanguageDef.LogicExtension
import Mettapedia.GSLT.LanguageDef.OracleExtension
import Mettapedia.OSLF.MeTTaIL.Match
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Multiset.Bind

/-!
# A query-first MeTTa Zero kernel

This module gives a small MeTTa-family kernel without identifying the kernel
with one backend or one answer quotient.

The primitive symbolic operation is a public query over one reflective space.
Facts, equations, types, and programs are all ordinary `Pattern` values in
that space.  One-step evaluation is derived from the public query: enumerate
the stored atoms, retain equation-shaped atoms, match their left sides against
the subject with the same matcher, and instantiate their right sides.  A
declared grounding portal supplies external alternatives.  If neither route
answers, the subject is retained inertly.

The reference result carrier is a finite multiset.  It retains multiplicity
without making enumeration order semantic.  Consequently list-valued PeTTa
querying can interpret the kernel through its exact occurrence bag, while a
set-valued MM2 realization can interpret the support quotient without
pretending to preserve multiplicity.

There are two complementary presentations here.

* `queryGSLT` and `evaluationGSLT` are semantic GSLTs.  Their disjoint sum is
  `kernelGSLT`, with faithful embeddings of both components.
* `definition` is one `ExtendedLanguageDef`: its five-field term language,
  relation signatures, and grounding portal are authored together.  The
  extension index is the product of the logic and oracle authoring GSLTs, so
  `authoredExtensionGSLT` composes those declaration languages inside
  `(T,E,R)`.

The results below establish the MeTTa-family discriminators exercised by this
kernel.  They do not claim categorical initiality; that requires a chosen
category of answer algebras and dialect interpretations.
-/

namespace Mettapedia.Languages.MeTTa.MeTTaZero

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.ExtensionComposition
open Mettapedia.GSLT.LanguageDef.LogicExtension
open Mettapedia.GSLT.LanguageDef.OracleExtension
open Mettapedia.GSLT.Dynamics.OccurrenceSemantics
open Mettapedia.GSLT.Dynamics.OperationalRegion
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

/-! ## Query and evaluation model -/

/-- The semantic choices a MeTTa dialect supplies to the query-first kernel.

`contents` is the one reflective medium.  `matchAtoms` is used both by public
query and by evaluation.  `groundApply` is a capability boundary: an empty
result means the implementation declines to interpret the subject. -/
structure Model where
  Space : Type
  contents : Space → Multiset Pattern
  matchAtoms : Pattern → Pattern → Multiset Bindings
  groundApply : Pattern → Multiset Pattern

/-- The sole matching law required to recover every stored atom through the
public query operation. -/
structure Lawful (model : Model) : Prop where
  wildcard_match : ∀ name atom,
    model.matchAtoms (.fvar name) atom = {[(name, atom)]}

/-- Public reflective query.  Every successful match contributes one
instantiated template occurrence. -/
def query (model : Model) (space : model.Space)
    (pattern template : Pattern) : Multiset Pattern :=
  (model.contents space).bind fun atom =>
    (model.matchAtoms pattern atom).map fun bindings =>
      applyBindings bindings template

/-- A reserved metavariable used only to enumerate the reflective medium. -/
def allAtomsVariable : String := "__metta_zero_atom"

/-- Query every atom as itself.  This is defined through `query`, not by
reading `contents` directly. -/
def queryAll (model : Model) (space : model.Space) : Multiset Pattern :=
  query model space (.fvar allAtomsVariable) (.fvar allAtomsVariable)

/-- A stored equation is ordinary data with the shape `(= lhs rhs)`. -/
def viewEquation? : Pattern → Option (Pattern × Pattern)
  | .apply "=" [left, right] => some (left, right)
  | _ => none

/-- Derived equation application.  Candidate equations are obtained through
the public query, then their left sides are matched against the subject using
the same matcher as that query. -/
def equationResults (model : Model) (space : model.Space)
    (subject : Pattern) : Multiset Pattern :=
  (queryAll model space).bind fun candidate =>
    match viewEquation? candidate with
    | none => 0
    | some (left, right) =>
        (model.matchAtoms left subject).map fun bindings =>
          applyBindings bindings right

/-- Results known to the kernel before the open-world default is applied. -/
def interpretedResults (model : Model) (space : model.Space)
    (subject : Pattern) : Multiset Pattern :=
  equationResults model space subject + model.groundApply subject

/-- One-step evaluation.  Ignorance is inertness, not absence of an answer. -/
def evaluateOne (model : Model) (space : model.Space)
    (subject : Pattern) : Multiset Pattern :=
  let results := interpretedResults model space subject
  if results = 0 then {subject} else results

@[simp] theorem queryAll_eq_contents (model : Model) (lawful : Lawful model)
    (space : model.Space) :
    queryAll model space = model.contents space := by
  simp only [queryAll, query]
  induction model.contents space using Multiset.induction_on with
  | empty => rfl
  | @cons atom atoms inductionHypothesis =>
      simp [lawful.wildcard_match, applyBindings, allAtomsVariable]
      simpa using
        (Multiset.bind_singleton atoms (fun atom : Pattern => atom))

/-- Exact witness characterization of the derived evaluator.  In particular,
an equation result always factors through a publicly queryable stored atom. -/
theorem mem_equationResults_iff (model : Model) (space : model.Space)
    (subject result : Pattern) :
    result ∈ equationResults model space subject ↔
      ∃ candidate ∈ queryAll model space,
        ∃ left right, viewEquation? candidate = some (left, right) ∧
          ∃ bindings ∈ model.matchAtoms left subject,
            applyBindings bindings right = result := by
  simp only [equationResults, Multiset.mem_bind]
  constructor
  · rintro ⟨candidate, candidateMember, candidateResult⟩
    cases equationView : viewEquation? candidate with
    | none => simp [equationView] at candidateResult
    | some equation =>
        obtain ⟨left, right⟩ := equation
        simp only [equationView, Multiset.mem_map] at candidateResult
        obtain ⟨bindings, bindingsMember, resultEqual⟩ := candidateResult
        exact ⟨candidate, candidateMember, left, right, equationView,
          bindings, bindingsMember, resultEqual⟩
  · rintro ⟨candidate, candidateMember, left, right, equationView,
      bindings, bindingsMember, resultEqual⟩
    refine ⟨candidate, candidateMember, ?_⟩
    simp only [equationView, Multiset.mem_map]
    exact ⟨bindings, bindingsMember, resultEqual⟩

/-- On a lawful model the previous factorization starts from an atom in the
single reflective medium, not a private rule table. -/
theorem mem_equationResults_iff_contents (model : Model)
    (lawful : Lawful model) (space : model.Space) (subject result : Pattern) :
    result ∈ equationResults model space subject ↔
      ∃ candidate ∈ model.contents space,
        ∃ left right, viewEquation? candidate = some (left, right) ∧
          ∃ bindings ∈ model.matchAtoms left subject,
            applyBindings bindings right = result := by
  rw [mem_equationResults_iff, queryAll_eq_contents model lawful]

/-- Open-world ignorance retains the uninterpreted subject. -/
@[simp] theorem evaluateOne_of_uninterpreted (model : Model)
    (space : model.Space) (subject : Pattern)
    (unknown : interpretedResults model space subject = 0) :
    evaluateOne model space subject = {subject} := by
  simp [evaluateOne, unknown]

/-- When some interpretation succeeds, evaluation returns exactly those
occurrences and does not add the inert fallback. -/
theorem evaluateOne_of_interpreted (model : Model) (space : model.Space)
    (subject : Pattern)
    (known : interpretedResults model space subject ≠ 0) :
    evaluateOne model space subject = interpretedResults model space subject := by
  simp [evaluateOne, known]

/-! ## The semantic GSLTs -/

/-- Query requests and multiplicity-labelled answers.  The natural-number
label identifies one of the indistinguishable copies without imposing an
enumeration order. -/
inductive QueryTerm (model : Model) where
  | request (space : model.Space) (pattern template : Pattern)
  | answer (space : model.Space) (pattern template : Pattern)
      (occurrence : Nat) (result : Pattern)

/-- One query rewrite emits exactly one copy from the query multiset. -/
inductive QueryStep (model : Model) : QueryTerm model → QueryTerm model → Prop where
  | found {space pattern template occurrence result}
      (copy : occurrence < Multiset.count result
        (query model space pattern template)) :
      QueryStep model (.request space pattern template)
        (.answer space pattern template occurrence result)

/-- General reflective query as a genuine `(T,E,R)` theory. -/
def queryGSLT (model : Model) : GSLT where
  Term := QueryTerm model
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := QueryStep model
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

@[simp] theorem queryGSLT_step_iff (model : Model) (space : model.Space)
    (pattern template result : Pattern) (occurrence : Nat) :
    (queryGSLT model).Step (.request space pattern template)
      (.answer space pattern template occurrence result) ↔
      occurrence < Multiset.count result
        (query model space pattern template) := by
  constructor
  · intro step
    cases step
    assumption
  · exact QueryStep.found

/-- Query membership and GSLT reachability agree exactly, including occurrence
identity. -/
theorem mem_query_iff_exists_step (model : Model) (space : model.Space)
    (pattern template result : Pattern) :
    result ∈ query model space pattern template ↔
      ∃ occurrence,
        (queryGSLT model).Step (.request space pattern template)
          (.answer space pattern template occurrence result) := by
  constructor
  · intro member
    have positive : 0 < Multiset.count result
        (query model space pattern template) :=
      Multiset.count_pos.mpr member
    exact ⟨0, (queryGSLT_step_iff _ _ _ _ _ _).2 positive⟩
  · rintro ⟨occurrence, step⟩
    exact Multiset.count_pos.mp
      (Nat.zero_lt_of_lt ((queryGSLT_step_iff _ _ _ _ _ _).1 step))

/-- Current Zero evaluation as one point of the generic occurrence-source
specification space. Query derivation and inert fallback are confined to the
function supplying this point's answer bag. -/
def evaluationOccurrenceSource (model : Model) :
    OccurrenceSource model.Space Pattern Pattern where
  occurrences := evaluateOne model

/-- Evaluation requests and occurrence-labelled answers are the canonical
terms generated by the selected occurrence source. -/
abbrev EvaluationTerm (model : Model) :=
  OccurrenceTerm (evaluationOccurrenceSource model)

/-- Zero's evaluation steps are generic occurrence-selection steps. -/
abbrev EvaluationStep (model : Model) :=
  OccurrenceStep (evaluationOccurrenceSource model)

/-- Query-derived one-step evaluation is constructed from its occurrence
source rather than re-authoring the same step relation. -/
def evaluationGSLT (model : Model) : GSLT :=
  occurrenceGSLT (evaluationOccurrenceSource model)

@[simp] theorem evaluationGSLT_step_iff (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat) :
    (evaluationGSLT model).Step (.request space subject)
      (.answer space subject occurrence result) ↔
      occurrence < Multiset.count result
        (evaluateOne model space subject) :=
  occurrenceGSLT_step_iff (evaluationOccurrenceSource model)
    space subject result occurrence

theorem mem_evaluateOne_iff_exists_step (model : Model) (space : model.Space)
    (subject result : Pattern) :
    result ∈ evaluateOne model space subject ↔
      ∃ occurrence,
        (evaluationGSLT model).Step (.request space subject)
          (.answer space subject occurrence result) := by
  constructor
  · intro member
    have positive : 0 < Multiset.count result
        (evaluateOne model space subject) := Multiset.count_pos.mpr member
    exact ⟨0, (evaluationGSLT_step_iff _ _ _ _ _).2 positive⟩
  · rintro ⟨occurrence, step⟩
    exact Multiset.count_pos.mp
      (Nat.zero_lt_of_lt ((evaluationGSLT_step_iff _ _ _ _ _).1 step))

/-- The kernel is composed inside `(T,E,R)`: query and derived evaluation are
the two summands of one GSLT. -/
def kernelGSLT (model : Model) : GSLT :=
  GSLT.disjointSum (queryGSLT model) (evaluationGSLT model)

/-- Public query embeds faithfully into the composed kernel. -/
def queryEmbedding (model : Model) :
    GSLT.Embedding (queryGSLT model) (kernelGSLT model) :=
  GSLT.disjointSumLeft _ _

/-- Derived evaluation embeds faithfully into the composed kernel. -/
def evaluationEmbedding (model : Model) :
    GSLT.Embedding (evaluationGSLT model) (kernelGSLT model) :=
  GSLT.disjointSumRight _ _

/-! ### The common occurrence-bag interpretation

A request and any one of its occurrence-labelled answer states denote the
same complete answer bag.  This turns the operational query/evaluation GSLTs
into elaborations with a nontrivial invariant: taking a rewrite selects an
occurrence but does not change the query denotation. -/

def queryMeaning (model : Model) : QueryTerm model → Multiset Pattern
  | .request space pattern template => query model space pattern template
  | .answer space pattern template _ _ => query model space pattern template

def evaluationMeaning (model : Model) :
    EvaluationTerm model → Multiset Pattern :=
  occurrenceMeaning (evaluationOccurrenceSource model)

/-- Query rewriting preserves the complete occurrence-bag denotation. -/
def queryElaboration (model : Model) :
    GSLT.Elaboration (queryGSLT model) (Multiset Pattern) where
  elaborate := fun term => some (queryMeaning model term)
  equation := by
    intro source target equivalent
    cases equivalent
    rfl
  rewrite := by
    intro source target step
    cases step
    rfl

/-- Query-derived evaluation rewriting preserves the complete answer bag. -/
def evaluationElaboration (model : Model) :
    GSLT.Elaboration (evaluationGSLT model) (Multiset Pattern) :=
  occurrenceElaboration (evaluationOccurrenceSource model)

def kernelMeaning (model : Model) :
    (kernelGSLT model).Term → Multiset Pattern :=
  Sum.elim (queryMeaning model) (evaluationMeaning model)

/-- The composed Zero kernel has one occurrence-bag interpretation whose
restriction to either component is its established meaning. -/
def kernelElaboration (model : Model) :
    GSLT.Elaboration (kernelGSLT model) (Multiset Pattern) where
  elaborate := fun term => some (kernelMeaning model term)
  equation := by
    intro source target equivalent
    cases equivalent with
    | left component => cases component; rfl
    | right component => cases component; rfl
  rewrite := by
    intro source target step
    cases step with
    | left component =>
        exact (queryElaboration model).rewrite component
    | right component =>
        exact (evaluationElaboration model).rewrite component

@[simp] theorem kernelElaboration_query (model : Model)
    (term : QueryTerm model) :
    (kernelElaboration model).elaborate (.inl term) =
      some (queryMeaning model term) :=
  rfl

@[simp] theorem kernelElaboration_evaluation (model : Model)
    (term : EvaluationTerm model) :
    (kernelElaboration model).elaborate (.inr term) =
      some (evaluationMeaning model term) :=
  rfl

/-- Public query embeds into Zero while preserving its exact occurrence-bag
meaning.  This names the invariant that the structural embedding alone does
not express. -/
def queryObservedEmbedding (model : Model) :
    GSLT.Embedding.Observed (queryGSLT model) (kernelGSLT model)
      (Multiset Pattern) where
  toEmbedding := queryEmbedding model
  observeSource := queryMeaning model
  observeTarget := kernelMeaning model
  preserves := fun _ => rfl

/-- Query-derived evaluation embeds into Zero with the same occurrence-bag
observation. -/
def evaluationObservedEmbedding (model : Model) :
    GSLT.Embedding.Observed (evaluationGSLT model) (kernelGSLT model)
      (Multiset Pattern) where
  toEmbedding := evaluationEmbedding model
  observeSource := evaluationMeaning model
  observeTarget := kernelMeaning model
  preserves := fun _ => rfl

/-! ### The current Zero point in the operational specification region -/

/-- Admissible Zero operational points select an occurrence source, a host
theory, and a faithful component embedding.  This is a category of points and
typed commuting-square arrows, not the definition of one branded language. -/
abbrev OperationalRegion := OccurrencePoint Pattern Pattern

/-- Today's query-first Zero kernel is one named point of the operational
region.  Its query derivation and inert fallback remain properties of this
point's selected source, not requirements of every point in the region. -/
def currentOperationalPoint (model : Model) : OperationalRegion where
  Space := model.Space
  source := evaluationOccurrenceSource model
  host := kernelGSLT model
  occurrenceEmbedding := evaluationEmbedding model

/-- The complete answer-bag interpretation is an independent attachment to
the current operational point. -/
def currentBagObservation (model : Model) :
    OccurrencePoint.BagObservation (currentOperationalPoint model) where
  meaning := kernelMeaning model
  elaboration := kernelElaboration model
  elaborates := by intro; rfl
  occurrenceMeaning := by intro; rfl

/-- Positive witness: the selected occurrence component takes exactly the
same embedded steps in the current host. -/
theorem currentOperationalPoint_step_iff (model : Model)
    (source target : (evaluationGSLT model).Term) :
    (currentOperationalPoint model).host.Step
        ((currentOperationalPoint model).occurrenceEmbedding.toFun source)
        ((currentOperationalPoint model).occurrenceEmbedding.toFun target) ↔
      (evaluationGSLT model).Step source target :=
  (currentOperationalPoint model).occurrenceEmbedding.step_iff source target

/-- Negative witness: the current host also contains public query terms, so
hosting does not identify the generated occurrence theory with the host. -/
theorem query_request_not_in_current_occurrence_image (model : Model)
    (space : model.Space) (pattern template : Pattern) :
    ∀ term : (evaluationGSLT model).Term,
      (currentOperationalPoint model).occurrenceEmbedding.toFun term ≠
        Sum.inl (QueryTerm.request space pattern template) := by
  intro term equal
  cases equal

/-- The query inclusion is therefore a certified realization, not merely a
term injection. -/
def queryKernelRealization (model : Model) :
    Mettapedia.GSLT.SimpleRealization (queryGSLT model).Term
      (kernelGSLT model).Term (Multiset Pattern) :=
  (queryObservedEmbedding model).toRealization

/-- The evaluation inclusion is a certified realization at the same exact
occurrence-bag observation. -/
def evaluationKernelRealization (model : Model) :
    Mettapedia.GSLT.SimpleRealization (evaluationGSLT model).Term
      (kernelGSLT model).Term (Multiset Pattern) :=
  (evaluationObservedEmbedding model).toRealization

/-! ## The authored five-field language and its coGSLT extensions -/

def atomType : TypeDecl := TypeDecl.plain "Atom"
def spaceType : TypeDecl := TypeDecl.plain "Space"
def processType : TypeDecl := TypeDecl.plain "Process"
def alternativesType : TypeDecl := TypeDecl.plain "Alternatives"

private def constructor (label category : String)
    (parameters : List (String × TypeExpr)) : GrammarRule :=
  { label
    category
    params := parameters.map fun parameter =>
      .simple parameter.1 parameter.2
    syntaxPattern := [] }

def equationConstructor : GrammarRule :=
  constructor "=" "Atom" [("left", .base "Atom"), ("right", .base "Atom")]

def queryRequestConstructor : GrammarRule :=
  constructor "zero-query" "Process"
    [("space", .base "Space"), ("pattern", .base "Atom"),
      ("template", .base "Atom")]

def queryAnswerConstructor : GrammarRule :=
  constructor "zero-query-answer" "Process" [("answer", .base "Atom")]

def evaluationRequestConstructor : GrammarRule :=
  constructor "zero-evaluate" "Process"
    [("space", .base "Space"), ("subject", .base "Atom")]

def evaluationAnswerConstructor : GrammarRule :=
  constructor "zero-evaluate-answer" "Process" [("answer", .base "Atom")]

/-- A named metavariable used by the authored rewrite schemas. -/
def metavariable (name : String) : Pattern := .fvar name

def queryRequestPattern (space pattern template : Pattern) : Pattern :=
  .apply "zero-query" [space, pattern, template]

def queryAnswerPattern (answer : Pattern) : Pattern :=
  .apply "zero-query-answer" [answer]

def evaluationRequestPattern (space subject : Pattern) : Pattern :=
  .apply "zero-evaluate" [space, subject]

def evaluationAnswerPattern (answer : Pattern) : Pattern :=
  .apply "zero-evaluate-answer" [answer]

def queryRewrite : RewriteRule :=
  { name := "zero-query"
    typeContext :=
      [("space", .base "Space"), ("pattern", .base "Atom"),
       ("template", .base "Atom"), ("answer", .base "Atom")]
    premises :=
      [.relationQuery "ZeroQuery"
        [metavariable "space", metavariable "pattern", metavariable "template",
         metavariable "answer"]]
    left := queryRequestPattern (metavariable "space") (metavariable "pattern")
      (metavariable "template")
    right := queryAnswerPattern (metavariable "answer") }

def evaluationRewrite : RewriteRule :=
  { name := "zero-evaluate"
    typeContext :=
      [("space", .base "Space"), ("subject", .base "Atom"),
       ("answer", .base "Atom")]
    premises :=
      [.relationQuery "ZeroEvaluate"
        [metavariable "space", metavariable "subject", metavariable "answer"]]
    left := evaluationRequestPattern (metavariable "space") (metavariable "subject")
    right := evaluationAnswerPattern (metavariable "answer") }

/-- The two relation signatures are interfaces.  Evaluation has no independent
clause table: its realization is fixed by `evaluateOne`. -/
def logicDeclarations : LogicProgram :=
  [.relation
      { name := "ZeroQuery"
        argTypes := [.base "Space", .base "Atom", .base "Atom", .base "Atom"] },
   .relation
      { name := "ZeroEvaluate"
        argTypes := [.base "Space", .base "Atom", .base "Atom"] }]

/-- Grounding returns an abstract alternative carrier.  Whether it is a bag,
set, counted map, or weighted carrier belongs to a realization/observer, not
to the root language. -/
def groundApplyDeclaration : OracleDecl :=
  { name := "ground-apply"
    argTypes := [.base "Atom"]
    resultType := .base "Alternatives" }

/-- Raw logic authoring as an indexed compositional layer. -/
def logicAuthoringLayer : CompositionalLayer LanguageDef :=
  CompositionalLayer.ofCodec LanguageDef logicCodec

/-- Raw oracle authoring as an indexed compositional layer. -/
def oracleAuthoringLayer : CompositionalLayer LanguageDef :=
  CompositionalLayer.ofCodec LanguageDef oracleCodec

/-- The single compositional authoring system for Zero's logic and grounding
declarations.  Contextual admission is applied only after this product
elaborates. -/
def authoredExtensionComposition : CompositionalLayer LanguageDef :=
  logicAuthoringLayer.product oracleAuthoringLayer

/-- **The complete authored Zero definition.**  The five core fields and both
extension components are written as one definition.  Each `layer` clause names
the authored GSLT responsible for that block; the notation folds them through
`CompositionalLayer.product` in written order. -/
def definition : ExtendedLanguageDef authoredExtensionComposition :=
  extendedLanguageDef!
    { name := "metta-zero-query-kernel"
      types := [atomType, spaceType, processType, alternativesType]
      terms :=
        [equationConstructor, queryRequestConstructor, queryAnswerConstructor,
         evaluationRequestConstructor, evaluationAnswerConstructor]
      equations := []
      rewrites := [queryRewrite, evaluationRewrite] }
    with layer (logicAuthoringLayer) { logicDeclarations }
    and layer (oracleAuthoringLayer) { [groundApplyDeclaration] }

/-- The exact five-field root consumed by ordinary language tooling. -/
abbrev language : LanguageDef := definition.toLanguageDef

/-- The root rewrite inventory remains directly inspectable through the
projection from the combined definition. -/
@[simp] theorem language_rewrites :
    language.rewrites = [queryRewrite, evaluationRewrite] :=
  rfl

private theorem rewrites_validate :
  ∀ rewrite ∈ language.rewrites,
      LanguageDef.validateRewrite language rewrite = [] := by
  intro rewrite rewriteMember
  change rewrite ∈ [queryRewrite, evaluationRewrite] at rewriteMember
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at rewriteMember
  rcases rewriteMember with rfl | rfl
  all_goals
    simp [LanguageDef.validateRewrite, language, definition, queryRewrite,
      evaluationRewrite, queryRequestPattern, queryAnswerPattern,
      evaluationRequestPattern, evaluationAnswerPattern, metavariable,
      atomType, spaceType, processType, alternativesType,
      equationConstructor, queryRequestConstructor, queryAnswerConstructor,
      evaluationRequestConstructor, evaluationAnswerConstructor, constructor,
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
    constructor <;>
      apply LanguageDef.validateTypeExpr_eq_nil_of_baseNames <;>
      simp [TypeDecl.plain, TypeExpr.baseNames]

/-- The authored root passes the ordinary five-field language validator. -/
theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  all_goals try decide
  exact rewrites_validate

def admittedLogic : AdmittedProgram language :=
  ⟨logicDeclarations, by decide⟩

def admittedOracles : AdmittedLibrary language :=
  ⟨[groundApplyDeclaration], by decide⟩

/-- The authored logic and oracle languages compose as an actual GSLT. -/
def authoredExtensionGSLT : GSLT :=
  (authoredExtensionComposition.system language).authoring.theory

/-- Logic declarations retain their own equations and rewrites inside the
composite authoring language. -/
def logicAuthoringEmbedding :
    GSLT.Embedding logicDocumentGSLT authoredExtensionGSLT :=
  GSLT.compositeDocumentsLeft _ _

/-- Oracle declarations retain their own equations and rewrites inside the
composite authoring language. -/
def oracleAuthoringEmbedding :
    GSLT.Embedding oracleDocumentGSLT authoredExtensionGSLT :=
  GSLT.compositeDocumentsRight _ _

/-! ### A certified realization of the composed authoring GSLT -/

/-- Logic declarations lowered from semantic lists to backend arrays. -/
def logicArrayRealization :
    CoGSLTLayer.Realization logicAuthoringLayer.toCoGSLTLayer
      (fun _ => Array LogicDeclaration) (fun _ => LogicProgram) :=
  logicCodec.arrayRealization LanguageDef

/-- Oracle declarations lowered independently to backend arrays. -/
def oracleArrayRealization :
    CoGSLTLayer.Realization oracleAuthoringLayer.toCoGSLTLayer
      (fun _ => Array OracleDecl) (fun _ => List OracleDecl) :=
  oracleCodec.arrayRealization LanguageDef

/-- The two independent lowering certificates compose through the same
product that composes their authored GSLTs. -/
def authoredArrayRealization :
    CoGSLTLayer.Realization authoredExtensionComposition.toCoGSLTLayer
      (fun _ => Array LogicDeclaration × Array OracleDecl)
      (fun _ => LogicProgram × List OracleDecl) :=
  logicAuthoringLayer.productRealization oracleAuthoringLayer
    logicArrayRealization oracleArrayRealization

/-- The raw declarations underlying Zero's admitted logic and oracle fibres. -/
abbrev authoredExtensionDeclarations :
    authoredExtensionComposition.Fiber language :=
  definition.extension

theorem definition_language :
    definition.toLanguageDef = language :=
  rfl

@[simp] theorem definition_logic :
    definition.extension.1 = logicDeclarations :=
  rfl

@[simp] theorem definition_oracles :
    definition.extension.2 = [groundApplyDeclaration] :=
  rfl

/-- The extension part of Zero's combined definition is denoted by one actual
composite authored GSLT. -/
@[simp] theorem definition_authoredGSLT :
    definition.authoredGSLT = authoredExtensionGSLT :=
  rfl

/-- Elaborating that composite GSLT term recovers both extension blocks at
once. -/
@[simp] theorem definition_elaborates :
    authoredExtensionComposition.elaborate language
        definition.authoredSource =
      some authoredExtensionDeclarations :=
  definition.elaborate_authoredSource

/-- A document containing only the logic declarations elaborates with the
oracle layer's authored empty payload.  This is the typed counterpart of
running Zero without a grounding library. -/
def logicOnlySource : authoredExtensionGSLT.Term :=
  [Sum.inl (logicAuthoringLayer.quote language logicDeclarations)]

@[simp] theorem logicOnlySource_elaborates :
    authoredExtensionComposition.elaborate language logicOnlySource =
      some (logicDeclarations, []) := by
  unfold authoredExtensionComposition logicOnlySource
  rw [CompositionalLayer.product_elaborates_left_only,
    CompositionalLayer.elaborate_quote]
  rfl

/-- Adding the grounding declaration changes the typed oracle payload.  It is
therefore a genuine composed library, not behavior smuggled into the core or
an alias for the logic-only definition. -/
theorem grounding_library_changes_extension :
    (authoredExtensionComposition.elaborate language logicOnlySource).map
        Prod.snd ≠
      (authoredExtensionComposition.elaborate language
        definition.authoredSource).map Prod.snd := by
  rw [logicOnlySource_elaborates, definition_elaborates]
  change (some [] : Option (List OracleDecl)) ≠
    some [groundApplyDeclaration]
  intro equal
  have impossible : ([] : List OracleDecl) = [groundApplyDeclaration] :=
    Option.some.inj equal
  cases impossible

/-- End-to-end staging: canonical mixed authoring elaborates and compiles to
the independently lowered logic and oracle artifacts. -/
theorem authoredArrayRealization_compile_quote :
    authoredArrayRealization.compileTerm? language
        (authoredExtensionComposition.toCoGSLTLayer.quote language
          authoredExtensionDeclarations) =
      some (logicDeclarations.toArray, [groundApplyDeclaration].toArray) := by
  rw [CoGSLTLayer.Realization.compileTerm_quote]
  rfl

/-! ### One elaborator for the composed authoring language -/

/-- The concrete term carrier of the mixed authoring GSLT.  Each occurrence
is a logic document or an oracle document; occurrences of the two kinds may be
interleaved freely. -/
abbrev AuthoredExtensionSource :=
  List (DeclarationDocument LogicSyntax ⊕ DeclarationDocument OracleSyntax)

/-- The dependent payload produced by the mixed authoring language. -/
abbrev AdmittedExtensions (base : LanguageDef) :=
  AdmittedProgram base × AdmittedLibrary base

private def elaborateRawExtensions? (base : LanguageDef)
    (source : AuthoredExtensionSource) :
    Option (LogicProgram × List OracleDecl) :=
  authoredExtensionComposition.elaborate base source

private theorem elaborateRawExtensions?_equation (base : LanguageDef)
    {source target : AuthoredExtensionSource}
    (equivalent : (authoredExtensionComposition.system base).authoring.theory.Equiv
      source target) :
    elaborateRawExtensions? base source = elaborateRawExtensions? base target :=
  (authoredExtensionComposition.system base).elaboration.equation equivalent

private theorem elaborateRawExtensions?_rewrite (base : LanguageDef)
    {source target : AuthoredExtensionSource}
    (step : (authoredExtensionComposition.system base).authoring.theory.Step
      source target) :
    elaborateRawExtensions? base source = elaborateRawExtensions? base target :=
  (authoredExtensionComposition.system base).elaboration.rewrite step

@[simp] private theorem elaborateRawExtensions?_quote (base : LanguageDef)
    (program : LogicProgram) (library : List OracleDecl) :
    elaborateRawExtensions? base
        (authoredExtensionComposition.quote base (program, library)) =
      some (program, library) := by
  unfold elaborateRawExtensions?
  exact authoredExtensionComposition.elaborate_quote base (program, library)

private def elaborateExtensions? (base : LanguageDef)
    (source : AuthoredExtensionSource) : Option (AdmittedExtensions base) := do
  let raw ← elaborateRawExtensions? base source
  let program := raw.1
  if programAdmitted : LogicProgram.AdmissibleFor program base = true then
    let library := raw.2
    if libraryAdmitted : LibraryAdmissible base library = true then
      some (⟨program, programAdmitted⟩, ⟨library, libraryAdmitted⟩)
    else
      none
  else
    none

private def quoteExtensions (base : LanguageDef)
    (extensions : AdmittedExtensions base) : AuthoredExtensionSource :=
  authoredExtensionComposition.quote base (extensions.1.1, extensions.2.1)

@[simp] private theorem elaborateExtensions?_quoteExtensions
    (base : LanguageDef) (extensions : AdmittedExtensions base) :
    elaborateExtensions? base (quoteExtensions base extensions) =
      some extensions := by
  rcases extensions with ⟨⟨program, programAdmitted⟩, ⟨library, libraryAdmitted⟩⟩
  unfold elaborateExtensions? quoteExtensions
  rw [elaborateRawExtensions?_quote]
  simp [programAdmitted, libraryAdmitted]

/-- Logic and grounding are authored and elaborated as one compositional
coGSLT layer.  The payload is dependent on the exact five-field base, so this
is a genuine fibre rather than an unvalidated product. -/
def extensionLayer : CoGSLTLayer LanguageDef where
  Fiber := AdmittedExtensions
  sourceGSLT := fun base =>
    (authoredExtensionComposition.system base).authoring.theory
  elaborate := elaborateExtensions?
  quote := quoteExtensions
  elaborate_quote := elaborateExtensions?_quoteExtensions
  elaborate_equation := by
    intro base source target equivalent
    unfold elaborateExtensions?
    rw [elaborateRawExtensions?_equation base equivalent]
  elaborate_rewrite := by
    intro base source target step
    unfold elaborateExtensions?
    rw [elaborateRawExtensions?_rewrite base step]

/-- The real Zero logic and grounding declarations round-trip together through
the mixed authoring GSLT. -/
theorem authored_extensions_roundTrip :
    extensionLayer.elaborate language
        (extensionLayer.quote language (admittedLogic, admittedOracles)) =
      some (admittedLogic, admittedOracles) :=
  extensionLayer.elaborate_quote language (admittedLogic, admittedOracles)

/-- Attaching the fully composed extension preserves the five-field root
definition exactly. -/
@[simp] theorem extension_erases_to_language :
    extensionLayer.erase
        (extensionLayer.attach language (admittedLogic, admittedOracles)) =
      language :=
  rfl

@[simp] theorem logic_erases_to_language :
    ExtensionLayer.erase
        (ExtensionLayer.attach
          Mettapedia.GSLT.LanguageDef.LogicExtension.layer.toExtensionLayer
          language admittedLogic) = language :=
  rfl

@[simp] theorem oracles_erase_to_language :
    ExtensionLayer.erase
        (ExtensionLayer.attach
          Mettapedia.GSLT.LanguageDef.OracleExtension.layer.toExtensionLayer
          language admittedOracles) = language :=
  rfl

/-! ## A concrete occurrence model and discriminator canaries -/

/-- The structural list model used by the exact PeTTa interpretation below. -/
def structuralModel (groundApply : Pattern → Multiset Pattern := fun _ => 0) : Model where
  Space := Multiset Pattern
  contents := id
  matchAtoms := fun pattern atom => (matchPattern pattern atom : List Bindings)
  groundApply := groundApply

theorem structuralModel_lawful (groundApply : Pattern → Multiset Pattern) :
    Lawful (structuralModel groundApply) := by
  constructor
  intro name atom
  simp [structuralModel, matchPattern]

private def knowledgeAtom : Pattern :=
  .apply "knows" [.apply "alice" [], .apply "bob" []]

private def equationAtom : Pattern :=
  .apply "="
    [.apply "f" [.fvar "x"], .apply "g" [.fvar "x"]]

private def subjectAtom : Pattern := .apply "f" [.apply "a" []]
private def resultAtom : Pattern := .apply "g" [.apply "a" []]

/-- Positive: arbitrary non-rule knowledge is publicly queryable. -/
example :
    query (structuralModel fun _ => 0) ({knowledgeAtom} : Multiset Pattern)
      (.fvar "item") (.fvar "item") = {knowledgeAtom} :=
  by simp [query, structuralModel, matchPattern, applyBindings]

/-- Positive: an equation is queryable as ordinary data. -/
example :
    query (structuralModel fun _ => 0) ({equationAtom} : Multiset Pattern)
      (.fvar "item") (.fvar "item") = {equationAtom} :=
  by simp [query, structuralModel, matchPattern, applyBindings]

/-- Positive: evaluation is derived from querying the equation atom. -/
example :
    equationResults (structuralModel fun _ => 0)
      ({equationAtom} : Multiset Pattern) subjectAtom =
      {resultAtom} :=
  by
    simp [equationResults, queryAll, query, structuralModel, matchPattern,
      matchArgs, mergeBindings, viewEquation?, equationAtom, subjectAtom,
      resultAtom, applyBindings]

/-- Positive: duplicate stored equations remain distinct occurrences. -/
example :
    equationResults (structuralModel fun _ => 0)
      ({equationAtom, equationAtom} : Multiset Pattern) subjectAtom =
        ({resultAtom, resultAtom} : Multiset Pattern) :=
  by
    simp [equationResults, queryAll, query, structuralModel, matchPattern,
      matchArgs, mergeBindings, viewEquation?, equationAtom, subjectAtom,
      resultAtom, applyBindings]

/-- Positive: unknown expressions remain inert. -/
example :
    evaluateOne (structuralModel fun _ => 0) (0 : Multiset Pattern)
      subjectAtom = {subjectAtom} :=
  rfl

/-- Negative discriminator: an equation-only private view cannot implement the
general query, because it makes ordinary knowledge invisible. -/
theorem equation_only_view_is_not_general_query :
    (List.filterMap (fun atom => (viewEquation? atom).map fun _ => atom)
        [knowledgeAtom]).isEmpty = true ∧
      query (structuralModel fun _ => 0) ({knowledgeAtom} : Multiset Pattern)
        (.fvar "item") (.fvar "item") = {knowledgeAtom} := by
  simp [viewEquation?, knowledgeAtom, query, structuralModel, matchPattern,
    applyBindings]

/-- The canonical counted observation of one answer value. -/
def multiplicity (answer : Pattern) (answers : Multiset Pattern) : Nat :=
  answers.count answer

/-- The idempotent support quotient used by set-valued realizations. -/
def support (answers : Multiset Pattern) : Finset Pattern :=
  answers.toFinset

/-- Support preserves existence exactly. -/
@[simp] theorem mem_support_iff (answer : Pattern) (answers : Multiset Pattern) :
    answer ∈ support answers ↔ answer ∈ answers := by
  simp [support]

/-- The exact occurrence-bag realization induces a certified support-only
realization by an explicit observation projection.  This is the contract a
set-valued backend may implement without claiming multiplicity preservation. -/
def querySupportRealization (model : Model) :
    Mettapedia.GSLT.SimpleRealization (queryGSLT model).Term
      (kernelGSLT model).Term (Finset Pattern) :=
  (queryKernelRealization model).mapObservation (fun _ => support)

/-- The support realization preserves exactly which answers occur. -/
theorem querySupportRealization_mem_iff (model : Model)
    (term : (queryGSLT model).Term) (answer : Pattern) :
    answer ∈
        (querySupportRealization model).observeArtifact ()
          ((querySupportRealization model).compile () term) ↔
      answer ∈ queryMeaning model term := by
  rw [(querySupportRealization model).observe_compile]
  exact mem_support_iff answer (queryMeaning model term)

/-- Negative observation canary: support cannot recover multiplicity. -/
theorem support_forgets_duplicate (answer : Pattern) :
    support ({answer} : Multiset Pattern) = support {answer, answer} ∧
      multiplicity answer ({answer} : Multiset Pattern) ≠
        multiplicity answer {answer, answer} := by
  constructor
  · ext candidate
    simp [support]
  · simp [multiplicity]

/-- No observer of support alone can reconstruct exact multiplicity for all
answer bags.  Thus support adequacy cannot be silently promoted to occurrence-
bag adequacy. -/
theorem no_multiplicity_observer_from_support (answer : Pattern) :
    ¬ ∃ recover : Finset Pattern → Nat,
        ∀ answers : Multiset Pattern,
          recover (support answers) = multiplicity answer answers := by
  rintro ⟨recover, recovers⟩
  have one := recovers ({answer} : Multiset Pattern)
  have two := recovers ({answer, answer} : Multiset Pattern)
  have distinguished := support_forgets_duplicate answer
  apply distinguished.2
  rw [← one, ← two, distinguished.1]

/-! ## MeTTa Zero as one interpreted theory

Zero's authored rewrites contain relation premises.  They therefore become an
operational GSLT only after a model, a space, and the pattern naming that space
have supplied the relation environment.  The resulting family has the authored
`Pattern` carrier itself; the query/evaluation kernel is its semantic reference,
not a disjoint second carrier.

This is an ordinary dependent family of GSLTs.  Calling it `Ind(GSLT)` would
require reindexing maps and coherence laws that are not asserted here. -/

section TotalTheory

open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.TotalGSLT

/-- Relation rows supplied by one semantic model and one named reflective
space.  Query and evaluation use the same model operations as the semantic
kernel. -/
noncomputable def semanticRelationEnv (model : Model) (space : model.Space)
    (spaceTerm : Pattern) : RelationEnv where
  tuples relation arguments :=
    match relation, arguments with
    | "ZeroQuery", [candidateSpace, pattern, template, .fvar _] =>
        if candidateSpace = spaceTerm then
          (query model space pattern template).toList.map fun answer =>
            [spaceTerm, pattern, template, answer]
        else
          []
    | "ZeroEvaluate", [candidateSpace, subject, .fvar _] =>
        if candidateSpace = spaceTerm then
          (evaluateOne model space subject).toList.map fun answer =>
            [spaceTerm, subject, answer]
        else
          []
    | _, _ => []

/-- Compatibility follows from Zero's authored empty equation list for every
semantic relation environment. -/
abbrev reductionRespectsEquations (model : Model) (space : model.Space)
    (spaceTerm : Pattern) :
    ReductionRespectsEquationsUsing
      (semanticRelationEnv model space spaceTerm) language :=
  ReductionRespectsEquationsUsing.of_no_equations
    (semanticRelationEnv model space spaceTerm) rfl

/-- **MeTTa Zero as one GSLT.**  Its authored requests reduce directly under
the query-first model; no disconnected kernel summand is added. -/
noncomputable def totalTheory (model : Model) (space : model.Space)
    (spaceTerm : Pattern) : GSLT :=
  languageGSLTUsing (semanticRelationEnv model space spaceTerm) language
    (reductionRespectsEquations model space spaceTerm)

/-- **The carrier** is the authored pattern language itself. -/
theorem totalTheory_Term (model : Model) (space : model.Space)
    (spaceTerm : Pattern) :
    (totalTheory model space spaceTerm).Term = Pattern :=
  rfl

/-- **The reduction relation** is exactly the authored rewrite relation under
the model-provided logic environment. -/
theorem totalTheory_rewrites (model : Model) (space : model.Space)
    (spaceTerm : Pattern) :
    (totalTheory model space spaceTerm).rewrites =
      langReducesUsing (semanticRelationEnv model space spaceTerm) language :=
  rfl

/-- The authored root declares no equations. -/
theorem totalTheory_object_equations_empty : language.equations = [] :=
  rfl

/-- Consequently the total theory's equivalence is exactly syntactic equality. -/
theorem totalTheory_equiv (model : Model) (space : model.Space)
    (spaceTerm source target : Pattern) :
    (totalTheory model space spaceTerm).Equiv source target ↔ source = target :=
  equationEquiv_iff_eq_of_no_generators rfl source target

/-- One-step reduction in the total theory is precisely authored reduction
under the semantic relation environment. -/
theorem totalTheory_step (model : Model) (space : model.Space)
    (spaceTerm source target : Pattern) :
    (totalTheory model space spaceTerm).Step source target ↔
      langReducesUsing (semanticRelationEnv model space spaceTerm)
        language source target :=
  Iff.rfl

end TotalTheory

end Mettapedia.Languages.MeTTa.MeTTaZero
