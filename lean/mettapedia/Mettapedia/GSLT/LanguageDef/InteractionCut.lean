import Mettapedia.GSLT.LanguageDef.SemanticCategory
import Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-!
# Interaction cuts selected from an authored language definition

An interaction cut is additional structure on an iGSLT.  It does not supply
an independent contraction callback.  Instead it selects the introductions,
continuation positions, residual constructor, and ordered source
factorization of the interaction rewrite already authored by the retained
`LanguageDef`.  The rewrite schema and its least declarative interpretation
remain the sole authority for contraction.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open StructuralMorphism
open WellSorted

/-- A parameter position in one exact authored constructor. -/
structure ConstructorParameter
    {presentation : ValidatedLanguageDef}
    (constructor : AuthoredConstructor presentation) where
  index : Nat
  inBounds : index < constructor.1.params.length

namespace ConstructorParameter

/-- The parameter declaration selected by a position. -/
def parameter
    {presentation : ValidatedLanguageDef}
    {constructor : AuthoredConstructor presentation}
    (position : ConstructorParameter constructor) : TermParam :=
  constructor.1.params[position.index]'position.inBounds

end ConstructorParameter

/-- The result type of a continuation parameter.  A plain parameter is its
own continuation.  A binder parameter contributes the codomain of its
function type. -/
def continuationResult? (parameter : TermParam) : Option TypeExpr :=
  match parameterType? parameter with
  | some (.arrow _ result) => some result
  | some type => some type
  | none => none

/-- A constructor parameter explicitly designated as a continuation of the
interacting sort. -/
structure ContinuationPosition
    (presentation : InteractivePresentation)
    (constructor : AuthoredConstructor presentation.presentation)
    extends ConstructorParameter constructor where
  hasInteractingResult :
    continuationResult? toConstructorParameter.parameter =
      some (.base presentation.interactingSort.1.name)

/-- Select an ordinary constructor argument as an interaction subject, or
record that the subject is structurally carried by the contact constructor. -/
inductive SubjectSelection
    {presentation : ValidatedLanguageDef}
    (constructor : AuthoredConstructor presentation)
    (schemaTerm : Pattern) where
  | absent
  | argument
      (position : ConstructorParameter constructor)
      (subject : Pattern)
      (selected : match schemaTerm with
        | .apply _ arguments => arguments[position.index]? = some subject
        | _ => False)

namespace SubjectSelection

/-- The selected nominal subject, when one is explicitly present. -/
def pattern
    {presentation : ValidatedLanguageDef}
    {constructor : AuthoredConstructor presentation}
    {schemaTerm : Pattern} :
    SubjectSelection constructor schemaTerm → Option Pattern
  | .absent => none
  | .argument _ subject _ => some subject

end SubjectSelection

/-- The schema variable occupying a continuation slot.  A continuation is
either a plain metavariable or that metavariable under the binder shape
already declared by its constructor parameter.  This is the exact variable
whose type the Cost construction re-sorts; it is not recovered later by a
heuristic traversal. -/
inductive ContinuationSchemaVariable : Pattern → Type where
  | plain (name : String) : ContinuationSchemaVariable (.fvar name)
  | abstraction (binder : Option String) (name : String) :
      ContinuationSchemaVariable (.lambda binder (.fvar name))
  | multiAbstraction (arity : Nat) (binders : List String) (name : String) :
      ContinuationSchemaVariable (.multiLambda arity binders (.fvar name))

namespace ContinuationSchemaVariable

/-- The rewrite-schema metavariable designated by a continuation slot. -/
def name {pattern : Pattern} : ContinuationSchemaVariable pattern → String
  | .plain name => name
  | .abstraction _ name => name
  | .multiAbstraction _ _ name => name

/-- Read the metavariable name from precisely the three continuation shapes.
This is an observation of the existing locally nameless pattern, not a second
representation of continuation syntax. -/
def patternName? : Pattern → Option String
  | .fvar name => some name
  | .lambda _ (.fvar name) => some name
  | .multiLambda _ _ (.fvar name) => some name
  | _ => none

@[simp]
theorem patternName?_eq_name {pattern : Pattern}
    (witness : ContinuationSchemaVariable pattern) :
    patternName? pattern = some witness.name := by
  cases witness <;> rfl

/-- Structural presentation maps leave schema-variable names and binder
metadata unchanged. -/
@[simp]
theorem patternName?_mapPattern {pattern : Pattern}
    (symbols : PresentationSymbols)
    (witness : ContinuationSchemaVariable pattern) :
    patternName? (mapPattern symbols pattern) = some witness.name := by
  cases witness <;>
    simp [patternName?, mapPattern, name]

end ContinuationSchemaVariable

/-- A schema pattern is represented by an exact authored constructor.
Ordinary constructors use their label and arity.  A single collection
parameter uses the shared bare-collection representation already derived by
the typing layer. -/
def RepresentedBy (constructor : GrammarRule) : Pattern → Prop
  | .apply label arguments =>
      ¬ UsesBareCollection constructor ∧
        label = constructor.label ∧
        arguments.length = constructor.params.length
  | .collection collectionType _ _ =>
      ∃ parameterName elementType,
        constructor.params =
          [.simple parameterName (.collection collectionType elementType)]
  | _ => False

/-- How the authored contractum is assembled.  Most process calculi name a
residual constructor such as parallel composition.  Lambda calculus instead
uses the locally nameless substitution form directly, so the degenerate
`K'` case is represented without inventing a constructor. -/
inductive ResidualRepresentation
    {presentation : ValidatedLanguageDef} : Pattern → Type where
  | constructor
      (residual : AuthoredConstructor presentation)
      {contractum : Pattern}
      (represented : RepresentedBy residual.1 contractum) :
      ResidualRepresentation contractum
  | substitution (body replacement : Pattern) :
      ResidualRepresentation (.subst body replacement)

/-- Whether one ordered interaction operand is introduced by its own
constructor or is itself the continuation selected directly from contact.
The latter is the degenerate environment operand of beta reduction. -/
inductive InteractionOperandKind where
  | introduced
  | direct
deriving DecidableEq, Repr

/-- Evidence connecting an interaction operand's schema occurrence to its
selected continuation.  A genuine introduction selects one of its authored
constructor arguments.  A direct operand is exactly the continuation. -/
inductive InteractionOperandForm
    {presentation : InteractivePresentation}
    (constructor : AuthoredConstructor presentation.presentation)
    (continuation : ContinuationPosition presentation constructor)
    (schemaTerm continuationPattern : Pattern) where
  | introduced
      (represented : RepresentedBy constructor.1 schemaTerm)
      (continuationSelected : match schemaTerm with
        | .apply _ arguments =>
            arguments[continuation.index]? = some continuationPattern
        | _ => False) :
      InteractionOperandForm constructor continuation schemaTerm
        continuationPattern
  | direct (same : schemaTerm = continuationPattern) :
      InteractionOperandForm constructor continuation schemaTerm
        continuationPattern

/-- One ordered operand occurring in the selected interaction rule.  Every
operand names the constructor position whose result is its continuation.  For
an ordinary introduction this is a position of that introduction; for a
direct operand it is the corresponding position of the contact constructor. -/
structure InteractionOperandProfile
    (presentation : InteractivePresentation) where
  constructor : AuthoredConstructor presentation.presentation
  schemaTerm : Pattern
  continuation : ContinuationPosition presentation constructor
  continuationPattern : Pattern
  continuationVariable : ContinuationSchemaVariable continuationPattern
  subject : SubjectSelection constructor schemaTerm
  form : InteractionOperandForm constructor continuation schemaTerm
    continuationPattern

namespace InteractionOperandProfile

/-- The two semantically distinct operand cases, with no constructor-shape
heuristic. -/
def kind {presentation : InteractivePresentation}
    (operand : InteractionOperandProfile presentation) :
    InteractionOperandKind :=
  match operand.form with
  | .introduced _ _ => .introduced
  | .direct _ => .direct

end InteractionOperandProfile

/-- Read the ordered binary/collection representation of an interaction core
without requiring its two parameter types to coincide.  The root iGSLT contact
is homogeneous; after Cost retypes a direct continuation position, the
retained inner core is intentionally heterogeneous while keeping the same
ordered representation. -/
def coreContactRepresentation? (sort : TypeDecl) (constructor : GrammarRule) :
    Option ContactRepresentation :=
  if constructor.category = sort.name then
    match constructor.params with
    | [.simple _ _, .simple _ _] => some .binary
    | [.simple _ (.collection collectionType _)] =>
        some (.collection collectionType)
    | _ => none
  else
    none

/-- The exact carrier and constructor of an ordered interaction core.  In an
unmetered theory this normally agrees with the root contact selected by the
interactive presentation.  A derived gated theory may retain a retyped,
heterogeneous copy below an administrative envelope while exposing a
different homogeneous root contact. -/
structure CoreContactPresentation (presentation : ValidatedLanguageDef) where
  sort : AuthoredSort presentation
  constructor : AuthoredConstructor presentation
  representation : ContactRepresentation
  representsCore :
    coreContactRepresentation? sort.1 constructor.1 = some representation

/-- The ordered side of a cut. -/
inductive CutSide where
  | program
  | environment
deriving DecidableEq, Repr

namespace CutSide

/-- The argument index occupied by this side in an ordinary binary contact. -/
def binaryIndex : CutSide → Nat
  | .program => 0
  | .environment => 1

end CutSide

/-- A cut operand is either introduced away from contact, or is a direct
continuation owned by the corresponding binary contact position.  This is the
structural distinction between rho's two genuine introductions and lambda's
degenerate environment operand. -/
inductive InteractionOperandPlacement
    {interactive : InteractivePresentation}
    (contact : CoreContactPresentation interactive.presentation)
    (side : CutSide)
    (operand : InteractionOperandProfile interactive) : Prop where
  | introduced
      (kind : operand.kind = .introduced)
      (different : operand.constructor ≠ contact.constructor) :
      InteractionOperandPlacement contact side operand
  | direct
      (kind : operand.kind = .direct)
      (binary : contact.representation = .binary)
      (ownedByContact : operand.constructor = contact.constructor)
      (atSide : operand.continuation.index = side.binaryIndex) :
      InteractionOperandPlacement contact side operand

/-- The selected interaction core has an ordered program/environment contact.
Collection contact may retain an open surrounding context, but the two
principal introductions remain ordered data. -/
inductive CutSourceShape
    {presentation : ValidatedLanguageDef}
    (contact : CoreContactPresentation presentation)
    (program environment : Pattern) : Pattern → Prop where
  | binary
      (binaryContact : contact.representation = .binary) :
      CutSourceShape contact program environment
        (.apply contact.constructor.1.label [program, environment])
  | collection
      {collectionType : CollType} (context : List Pattern)
      (rest : Option String)
      (collectionContact :
        contact.representation = .collection collectionType) :
      CutSourceShape contact program environment
        (.collection collectionType (program :: environment :: context) rest)

/-- An interaction core may occur beneath one structural envelope in the
authored rewrite source.  The core still contains the ordered program and
environment introductions directly; the envelope records surrounding gates
or resources without turning arbitrary contexts into reduction authority. -/
structure EnvelopedCutSource
    {presentation : ValidatedLanguageDef}
    (contact : CoreContactPresentation presentation)
    (program environment source : Pattern) where
  core : Pattern
  coreShape : CutSourceShape contact program environment core
  envelope : OneHoleContext
  fillsSource : envelope.fill core = source

/-- The contact constructor is free of authored static equations.  This is
the structural-subject alternative to an explicit nominal subject match. -/
def ContactEquationFree (presentation : InteractivePresentation) : Prop :=
  ∀ equation ∈ presentation.presentation.language.equations,
    (presentation.contactConstructor.1.label,
        presentation.contactConstructor.1.params.length) ∉
        equation.left.constructorRefs ∧
      (presentation.contactConstructor.1.label,
        presentation.contactConstructor.1.params.length) ∉
        equation.right.constructorRefs

/-- Subject matching is either nominal, with the same explicit schema term
selected on both ordered introductions, or structural, supplied by a free
binary contact constructor. -/
inductive SubjectAgreement
    {presentation : InteractivePresentation}
    (program environment : InteractionOperandProfile presentation) : Prop where
  | nominal (subject : Pattern)
      (programSubject : program.subject.pattern = some subject)
      (environmentSubject : environment.subject.pattern = some subject) :
      SubjectAgreement program environment
  | structural
      (binaryContact : presentation.contactRepresentation = .binary)
      (equationFree : ContactEquationFree presentation) :
      SubjectAgreement program environment

/-- Ordered interaction-cut data derived from one exact iGSLT presentation.
`K` and the interaction rewrite are already selected by the underlying
iGSLT; this enrichment names `Kp`, `Ke`, `K'`, their continuation slots, and
the exact factorization of that authored rule. -/
structure InteractionCutPresentation (theory : IGSLT) where
  program : InteractionOperandProfile theory.presentation
  environment : InteractionOperandProfile theory.presentation
  coreContact : CoreContactPresentation theory.presentation.presentation
  programPlacement : InteractionOperandPlacement coreContact .program program
  environmentPlacement :
    InteractionOperandPlacement coreContact .environment environment
  sourceShape : EnvelopedCutSource coreContact
    program.schemaTerm environment.schemaTerm
    theory.presentation.interactionRewrite.1.left
  /-- Every administrative frame around the ordered core comes from the
  authored term signature.  This excludes metasyntactic or arbitrary raw
  `Pattern` contexts without granting those frames reduction authority. -/
  sourceEnvelopeInSignature :
    SignatureContext theory.presentation.presentation.language
      coreContact.sort.1.name
      theory.presentation.interactingSort.1.name
      sourceShape.envelope
  /-- This cut presentation internalizes contraction in the selected
  contractum.  An interaction rule with executable premises requires a
  separate, typed transport of its premise environment; silently dropping
  those premises would strengthen the generated Cost reduction. -/
  interactionPremisesEmpty :
    theory.presentation.interactionRewrite.1.premises = []
  residual : ResidualRepresentation
    (presentation := theory.presentation.presentation)
    theory.presentation.interactionRewrite.1.right
  subjectsAgree : SubjectAgreement program environment

namespace InteractionCutPresentation

/-- The contraction schema is not separately authored: it is the right-hand
side of the selected interaction rewrite. -/
def contractumSchema {theory : IGSLT}
    (_cut : InteractionCutPresentation theory) : Pattern :=
  theory.presentation.interactionRewrite.1.right

/-- The cut's reduction authority is exactly the interaction rewrite already
selected from the sole language definition. -/
theorem interactionRewrite_mem {theory : IGSLT}
    (_cut : InteractionCutPresentation theory) :
    theory.presentation.interactionRewrite.1 ∈
      theory.presentation.presentation.language.rewrites :=
  theory.presentation.interactionRewrite.2

end InteractionCutPresentation

/-! ## Continuation-stable source envelopes -/

/-- Does this exact constructor position carry one of the two ordered
continuations selected by the interaction cut? -/
def isSelectedContinuation {theory : IGSLT}
    (cut : InteractionCutPresentation theory)
    (constructor : GrammarRule) (index : Nat) : Bool :=
  (constructor == cut.program.constructor.1 &&
      index == cut.program.continuation.index) ||
    (constructor == cut.environment.constructor.1 &&
      index == cut.environment.continuation.index)

/-- A constructor-derived context whose hole path never enters either
continuation slot selected by the ordered interaction cut.  Sibling terms may
contain continuations; only the path from the root to the hole is constrained.
This is the precise structural condition under which continuation retyping
keeps the whole context in the base fiber. -/
inductive ContinuationStableContext {theory : IGSLT}
    (cut : InteractionCutPresentation theory) :
    String → String → OneHoleContext → Prop where
  | hole (sort : String) :
      ContinuationStableContext cut sort sort .hole
  | simpleArg
      {source parameter : String} {rule : GrammarRule}
      {parameterName : String} {beforeParams afterParams : List TermParam}
      {before after : List Pattern} {inner : OneHoleContext} :
      rule ∈ theory.presentation.presentation.language.terms →
      rule.params = beforeParams ++
        .simple parameterName (.base parameter) :: afterParams →
      before.length = beforeParams.length →
      after.length = afterParams.length →
      isSelectedContinuation cut rule beforeParams.length = false →
      ContinuationStableContext cut source parameter inner →
      ContinuationStableContext cut source rule.category
        (.apply rule.label before inner after)
  | abstractionArg
      {source binderSort bodySort : String} {rule : GrammarRule}
      {declaredBinderName actualBinderName : Option String} {bodyName : String}
      {beforeParams afterParams : List TermParam}
      {before after : List Pattern} {inner : OneHoleContext} :
      rule ∈ theory.presentation.presentation.language.terms →
      rule.params = beforeParams ++
        .abstractionNamed declaredBinderName bodyName
          (.arrow (.base binderSort) (.base bodySort)) :: afterParams →
      before.length = beforeParams.length →
      after.length = afterParams.length →
      isSelectedContinuation cut rule beforeParams.length = false →
      ContinuationStableContext cut source bodySort inner →
      ContinuationStableContext cut source rule.category
        (.apply rule.label before (.lambda actualBinderName inner) after)
  | collectionElement
      {source elementSort : String} {rule : GrammarRule}
      {parameterName : String} {collectionType : CollType}
      {before after : List Pattern} {rest : Option String}
      {inner : OneHoleContext} :
      rule ∈ theory.presentation.presentation.language.terms →
      rule.params =
        [.simple parameterName (.collection collectionType (.base elementSort))] →
      isSelectedContinuation cut rule 0 = false →
      ContinuationStableContext cut source elementSort inner →
      ContinuationStableContext cut source rule.category
        (.collection collectionType before inner after rest)

namespace ContinuationStableContext

/-- Forgetting continuation stability recovers the ordinary context derived
from the exact authored constructor signature. -/
theorem toSignatureContext {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    {source target : String} {context : OneHoleContext}
    (stable : ContinuationStableContext cut source target context) :
    SignatureContext theory.presentation.presentation.language
      source target context := by
  induction stable with
  | hole => exact .hole _
  | simpleArg ruleMembership parameters beforeLength afterLength
      _notSelected _innerStable inductionHypothesis =>
      exact .simpleArg ruleMembership parameters beforeLength afterLength
        inductionHypothesis
  | abstractionArg ruleMembership parameters beforeLength afterLength
      _notSelected _innerStable inductionHypothesis =>
      exact .abstractionArg ruleMembership parameters beforeLength afterLength
        inductionHypothesis
  | collectionElement ruleMembership parameters _notSelected _innerStable
      inductionHypothesis =>
      exact .collectionElement ruleMembership parameters inductionHypothesis

/-- Continuation-stable contexts compose by plugging their hole paths. -/
theorem comp {theory : IGSLT} {cut : InteractionCutPresentation theory}
    {source middle target : String}
    {outerContext innerContext : OneHoleContext}
    (outer : ContinuationStableContext cut middle target outerContext)
    (inner : ContinuationStableContext cut source middle innerContext) :
    ContinuationStableContext cut source target
      (outerContext.comp innerContext) := by
  induction outer generalizing source innerContext with
  | hole => simpa [OneHoleContext.comp] using inner
  | simpleArg ruleMembership parameters beforeLength afterLength notSelected
      _frameStable inductionHypothesis =>
      simpa [OneHoleContext.comp] using
        (ContinuationStableContext.simpleArg ruleMembership parameters
          beforeLength afterLength notSelected (inductionHypothesis inner))
  | abstractionArg ruleMembership parameters beforeLength afterLength
      notSelected _frameStable inductionHypothesis =>
      simpa [OneHoleContext.comp] using
        (ContinuationStableContext.abstractionArg ruleMembership parameters
          beforeLength afterLength notSelected (inductionHypothesis inner))
  | collectionElement ruleMembership parameters notSelected _frameStable
      inductionHypothesis =>
      simpa [OneHoleContext.comp] using
        (ContinuationStableContext.collectionElement ruleMembership parameters
          notSelected (inductionHypothesis inner))

end ContinuationStableContext

/-! ## Rho instance and ordered controls -/

private def rhoInputConstructor :
    AuthoredConstructor rhoValidatedLanguageDef :=
  ⟨rhoCalc.terms[5], List.getElem_mem (by simp [rhoCalc])⟩

private def rhoOutputConstructor :
    AuthoredConstructor rhoValidatedLanguageDef :=
  ⟨rhoCalc.terms[4], List.getElem_mem (by simp [rhoCalc])⟩

/-- The exact parallel constructor selected from `rhoCalc`. -/
def rhoParallelConstructor :
    AuthoredConstructor rhoValidatedLanguageDef :=
  ⟨rhoCalc.terms[3], List.getElem_mem (by simp [rhoCalc])⟩

/-- The exact quotation constructor selected from `rhoCalc`. -/
def rhoQuoteConstructor :
    AuthoredConstructor rhoValidatedLanguageDef :=
  ⟨rhoCalc.terms[2], List.getElem_mem (by simp [rhoCalc])⟩

private def rhoProgramIntroduction :
    InteractionOperandProfile rhoInteractivePresentation where
  constructor := rhoInputConstructor
  schemaTerm :=
    .apply "PInput" [.fvar "n", .lambda none (.fvar "p")]
  continuation :=
    { index := 1
      inBounds := by simp [rhoInputConstructor, rhoCalc]
      hasInteractingResult := by
        rfl }
  continuationPattern := .lambda none (.fvar "p")
  continuationVariable := .abstraction none "p"
  subject := .argument
    { index := 0, inBounds := by simp [rhoInputConstructor, rhoCalc] }
    (.fvar "n") (by rfl)
  form := .introduced (by
      simp [RepresentedBy, UsesBareCollection, rhoInputConstructor, rhoCalc])
    (by rfl)

private def rhoEnvironmentIntroduction :
    InteractionOperandProfile rhoInteractivePresentation where
  constructor := rhoOutputConstructor
  schemaTerm := .apply "POutput" [.fvar "n", .fvar "q"]
  continuation :=
    { index := 1
      inBounds := by simp [rhoOutputConstructor, rhoCalc]
      hasInteractingResult := by
        rfl }
  continuationPattern := .fvar "q"
  continuationVariable := .plain "q"
  subject := .argument
    { index := 0, inBounds := by simp [rhoOutputConstructor, rhoCalc] }
    (.fvar "n") (by rfl)
  form := .introduced (by
      simp [RepresentedBy, UsesBareCollection, rhoOutputConstructor, rhoCalc])
    (by rfl)

/-- The core contact of pure rho is the exact process sort and parallel
collection constructor selected by its interactive presentation. -/
def rhoCoreContact : CoreContactPresentation rhoValidatedLanguageDef where
  sort := rhoInteractivePresentation.interactingSort
  constructor := rhoInteractivePresentation.contactConstructor
  representation := rhoInteractivePresentation.contactRepresentation
  representsCore := by rfl

/-- Pure rho's COMM rule, factored as the ordered input/output interaction
cut selected from `rhoCalc`. -/
def rhoInteractionCut : InteractionCutPresentation rhoIGSLT where
  program := rhoProgramIntroduction
  environment := rhoEnvironmentIntroduction
  coreContact := rhoCoreContact
  programPlacement := .introduced rfl (by
      intro equality
      have labels := congrArg (fun constructor => constructor.1.label) equality
      simp [rhoProgramIntroduction, rhoInputConstructor, rhoCoreContact,
        rhoInteractivePresentation, rhoCalc] at labels)
  environmentPlacement := .introduced rfl (by
      intro equality
      have labels := congrArg (fun constructor => constructor.1.label) equality
      simp [rhoEnvironmentIntroduction, rhoOutputConstructor, rhoCoreContact,
        rhoInteractivePresentation, rhoCalc] at labels)
  sourceShape :=
    { core := rhoCommRewrite.left
      coreShape := by
        change CutSourceShape rhoCoreContact
          rhoProgramIntroduction.schemaTerm
          rhoEnvironmentIntroduction.schemaTerm rhoCommRewrite.left
        simpa [rhoCommRewrite, rhoProgramIntroduction,
          rhoEnvironmentIntroduction] using
          (CutSourceShape.collection [] (some "rest") rfl :
            CutSourceShape rhoCoreContact
              rhoProgramIntroduction.schemaTerm
              rhoEnvironmentIntroduction.schemaTerm
              (.collection .hashBag
                (rhoProgramIntroduction.schemaTerm ::
                  rhoEnvironmentIntroduction.schemaTerm :: [])
                (some "rest")))
      envelope := .hole
      fillsSource := rfl }
  sourceEnvelopeInSignature := .hole "Proc"
  interactionPremisesEmpty := rfl
  residual := .constructor rhoParallelConstructor (by
    change RepresentedBy rhoParallelConstructor.1 rhoCommRewrite.right
    change ∃ parameterName elementType,
      [TermParam.simple "ps" (.collection .hashBag (.base "Proc"))] =
        [TermParam.simple parameterName (.collection .hashBag elementType)]
    exact ⟨"ps", .base "Proc", rfl⟩)
  subjectsAgree := .nominal (.fvar "n") rfl rfl

/-- Positive ordered control: the program side of rho's cut is input. -/
theorem rhoInteractionCut_program_constructor :
    rhoInteractionCut.program.constructor.1.label = "PInput" :=
  rfl

/-- The program introduction is the exact input declaration selected from
the sole rho language definition. -/
@[simp] theorem rhoInteractionCut_program_constructor_value :
    rhoInteractionCut.program.constructor.1 = rhoCalc.terms[5] :=
  rfl

/-- The program continuation is the second input parameter. -/
@[simp] theorem rhoInteractionCut_program_continuation_index :
    rhoInteractionCut.program.continuation.index = 1 :=
  rfl

/-- Positive ordered control: the environment side of rho's cut is output. -/
theorem rhoInteractionCut_environment_constructor :
    rhoInteractionCut.environment.constructor.1.label = "POutput" :=
  rfl

/-- The environment introduction is the exact output declaration selected
from the sole rho language definition. -/
@[simp] theorem rhoInteractionCut_environment_constructor_value :
    rhoInteractionCut.environment.constructor.1 = rhoCalc.terms[4] :=
  rfl

/-- The environment continuation is the second output parameter. -/
@[simp] theorem rhoInteractionCut_environment_continuation_index :
    rhoInteractionCut.environment.continuation.index = 1 :=
  rfl

/-- Negative control: the ordered roles are not definitionally exchanged. -/
theorem rhoInteractionCut_roles_distinct :
    rhoInteractionCut.program.constructor.1.label ≠
      rhoInteractionCut.environment.constructor.1.label := by
  decide

/-- Pure rho is the root-cut special case: COMM has no administrative
envelope around its ordered input/output core. -/
theorem rhoInteractionCut_source_envelope :
    rhoInteractionCut.sourceShape.envelope = .hole :=
  rfl

end Mettapedia.GSLT.LanguageDef
