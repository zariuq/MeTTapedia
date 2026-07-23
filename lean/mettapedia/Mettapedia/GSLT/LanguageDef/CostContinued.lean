import Mettapedia.GSLT.LanguageDef.CostInteractive

/-!
# Continued closure of the generic Cost construction

The funded interaction is factored through the ordered cut retained by the
source continued theory.  Its inner contact and introductions are the tagged
base copies of the source declarations; the signed term and funding stack are
ordinary signature-derived envelopes around that core.  Their exposed fields
have the source-process and token-stack sorts, respectively, so they are not
misclassified as continuation-bearing introductions of the wrapped carrier.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open StructuralMorphism
open WellSorted

/-- Transport a schema pattern into the collision-free Cost base namespace. -/
def costBaseSchemaPattern (pattern : Pattern) : Pattern :=
  mapPatternSchemaNames costSourceSchemaName
    (mapPattern costBasePresentationSymbols pattern)

/-- The designated continuation metavariable survives constructor transport
and receives the same collision-free schema-name action as its term. -/
def ContinuationSchemaVariable.costBase
    {pattern : Pattern} (witness : ContinuationSchemaVariable pattern) :
    ContinuationSchemaVariable (costBaseSchemaPattern pattern) := by
  cases witness with
  | plain name =>
      simpa [costBaseSchemaPattern, mapPatternSchemaNames, mapPattern,
        costBasePresentationSymbols] using
        (ContinuationSchemaVariable.plain (costSourceSchemaName name))
  | abstraction binder name =>
      simpa [costBaseSchemaPattern, mapPatternSchemaNames, mapPattern,
        costBasePresentationSymbols] using
        (ContinuationSchemaVariable.abstraction
          (binder.map costSourceSchemaName) (costSourceSchemaName name))
  | multiAbstraction arity binders name =>
      simpa [costBaseSchemaPattern, mapPatternSchemaNames, mapPattern,
        costBasePresentationSymbols] using
        (ContinuationSchemaVariable.multiAbstraction arity
          (binders.map costSourceSchemaName) (costSourceSchemaName name))

/-- Base transport changes the designated schema name by exactly the
collision-free source-name embedding. -/
@[simp]
theorem ContinuationSchemaVariable.costBase_name
    {pattern : Pattern} (witness : ContinuationSchemaVariable pattern) :
    witness.costBase.name = costSourceSchemaName witness.name := by
  cases witness <;> rfl

/-- Selecting an argument commutes with the constructor/schema transport. -/
theorem costBaseSchemaPattern_selected
    (schemaTerm continuationPattern : Pattern) (index : Nat)
    (selected : match schemaTerm with
      | .apply _ arguments =>
          arguments[index]? = some continuationPattern
      | _ => False) :
    match costBaseSchemaPattern schemaTerm with
    | .apply _ arguments =>
        arguments[index]? = some (costBaseSchemaPattern continuationPattern)
    | _ => False := by
  cases schemaTerm <;>
    simp_all [costBaseSchemaPattern, mapPattern,
      mapPatternSchemaNames, mapPatternListSchemaNames_eq_map,
      List.getElem?_map]

namespace CIGSLT

/-- A source sort selected from the exact generated Cost presentation. -/
def costBaseAuthoredSort (source : CIGSLT)
    (sort : AuthoredSort source.theory.presentation.presentation) :
    AuthoredSort source.costIGSLT.presentation.presentation :=
  ⟨{ sort.1 with name := costBaseSortName sort.1.name }, by
    change List.Mem { sort.1 with name := costBaseSortName sort.1.name }
      source.costCoreLanguage.types
    apply List.mem_append_left
    change List.Mem { sort.1 with name := costBaseSortName sort.1.name }
      source.continuationRetyping.generatedLanguage.types
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨sort.1, sort.2, rfl⟩⟩

/-- A source constructor selected from the exact generated Cost presentation. -/
def costBaseAuthoredConstructor (source : CIGSLT)
    (constructor :
      AuthoredConstructor source.theory.presentation.presentation) :
    AuthoredConstructor source.costIGSLT.presentation.presentation :=
  ⟨costBaseConstructor source.cut constructor.1, by
    change List.Mem (costBaseConstructor source.cut constructor.1)
      source.costCoreLanguage.terms
    apply List.mem_append_left
    exact source.continuationRetyping.costBaseConstructor_mem_generated
      constructor.1 constructor.2⟩

/-- Constructor representation is stable under the Cost base translation.
Only labels and sort annotations change; arity and bare-collection shape do
not. -/
theorem representedBy_costBase
    (source : CIGSLT) (constructor : GrammarRule) (pattern : Pattern)
    (represented : RepresentedBy constructor pattern) :
    RepresentedBy (costBaseConstructor source.cut constructor)
      (costBaseSchemaPattern pattern) := by
  cases pattern with
  | apply label arguments =>
      rcases represented with ⟨notBare, labelEquality, arityEquality⟩
      simp only [costBaseSchemaPattern, mapPattern, mapPatternSchemaNames]
      refine ⟨?_, ?_, ?_⟩
      · exact (usesBareCollection_costBaseConstructor_iff
          source.cut constructor).not.mpr notBare
      · simpa [costBaseSchemaPattern, mapPatternSchemaNames,
          costBaseConstructor, costBasePresentationSymbols] using
            congrArg costBaseConstructorName labelEquality
      · simpa [costBaseSchemaPattern, mapPatternSchemaNames,
          costBaseConstructor] using arityEquality
  | collection collectionType elements rest =>
      rcases represented with ⟨parameterName, elementType, parameterShape⟩
      simp only [costBaseSchemaPattern, mapPattern, mapPatternSchemaNames]
      refine ⟨parameterName,
        if isSelectedContinuation source.cut constructor 0 then
          costWrappedTypeExpr
            source.theory.presentation.interactingSort.1.name elementType
        else costBaseTypeExpr elementType, ?_⟩
      by_cases selected :
        isSelectedContinuation source.cut constructor 0 = true <;>
        simp [costBaseConstructor, parameterShape, costBaseParameter,
          selected, mapParameterType, costWrappedTypeExpr, costBaseTypeExpr]
  | bvar index => simp [RepresentedBy] at represented
  | fvar name => simp [RepresentedBy] at represented
  | lambda binder body => simp [RepresentedBy] at represented
  | multiLambda arity binders body =>
      simp [RepresentedBy] at represented
  | subst body replacement => simp [RepresentedBy] at represented

/-- One selected operand transported into the generated Cost cut.  Genuine
introductions retain their constructor representation; a direct operand
remains exactly its continuation while its owning contact position is
re-sorted by the same declaration-level constructor translation. -/
def costBaseOperand (source : CIGSLT)
    (operand : InteractionOperandProfile source.theory.presentation)
    (selected : isSelectedContinuation source.cut
      operand.constructor.1 operand.continuation.index = true) :
    InteractionOperandProfile source.costIGSLT.presentation := by
  rcases operand with
    ⟨constructor, schemaTerm, continuation, continuationPattern,
      continuationWitness, surface, form⟩
  have selectedContinuation :
      isSelectedContinuation source.cut constructor.1
        continuation.index = true := by
    simpa using selected
  let targetConstructor : AuthoredConstructor
      source.costIGSLT.presentation.presentation :=
    source.costBaseAuthoredConstructor constructor
  let targetContinuation : ContinuationPosition
      source.costIGSLT.presentation targetConstructor :=
    { index := continuation.index
      inBounds := by
        change continuation.index <
          (costBaseConstructor source.cut constructor.1).params.length
        rw [costBaseConstructor_params_length]
        exact continuation.inBounds
      hasInteractingResult := by
        change continuationResult?
          ((costBaseConstructor source.cut constructor.1).params[
            continuation.index]'(by simpa using continuation.inBounds)) =
          some (.base costWrappedSortName)
        rw [costBaseConstructor_parameter source.cut constructor.1
          continuation.index continuation.inBounds]
        simp only [costBaseParameter, selectedContinuation, if_true]
        exact continuationResult?_mapParameterType_costWrapped
          source.theory.presentation.interactingSort.1.name
          continuation.toConstructorParameter.parameter
          continuation.hasInteractingResult }
  cases form with
  | introduced represented selectedArgument =>
      cases schemaTerm with
      | apply label arguments =>
          exact
            { constructor := targetConstructor
              schemaTerm :=
                .apply (costBaseConstructorName label)
                  (mapPatternListSchemaNames costSourceSchemaName
                    (arguments.map
                      (mapPattern costBasePresentationSymbols)))
              continuation := targetContinuation
              continuationPattern := costBaseSchemaPattern continuationPattern
              continuationVariable := continuationWitness.costBase
              surface := .absent
              form := .introduced (by
                  dsimp [targetConstructor, costBaseAuthoredConstructor]
                  simpa [costBaseSchemaPattern, costBasePresentationSymbols,
                    mapPattern, mapPatternSchemaNames, List.map_map] using
                    (representedBy_costBase source constructor.1
                      (.apply label arguments) represented)) (by
                  dsimp [targetContinuation]
                  rw [mapPatternListSchemaNames_eq_map,
                    List.getElem?_map, List.getElem?_map, selectedArgument]
                  rfl) }
      | bvar index => exact False.elim selectedArgument
      | fvar name => exact False.elim selectedArgument
      | lambda binder body => exact False.elim selectedArgument
      | multiLambda arity binders body => exact False.elim selectedArgument
      | subst body replacement => exact False.elim selectedArgument
      | collection collectionType elements rest =>
          exact False.elim selectedArgument
  | direct same =>
      exact
        { constructor := targetConstructor
          schemaTerm := costBaseSchemaPattern schemaTerm
          continuation := targetContinuation
          continuationPattern := costBaseSchemaPattern continuationPattern
          continuationVariable := continuationWitness.costBase
          surface := .absent
          form := .direct (congrArg costBaseSchemaPattern same) }

/-- The transported program introduction retains the exact continuation
selected by the source cut. -/
def costProgramOperand (source : CIGSLT) :
    InteractionOperandProfile source.costIGSLT.presentation :=
  source.costBaseOperand source.cut.program (by
    simp [isSelectedContinuation])

/-- The transported environment introduction retains the exact continuation
selected by the source cut. -/
def costEnvironmentOperand (source : CIGSLT) :
    InteractionOperandProfile source.costIGSLT.presentation :=
  source.costBaseOperand source.cut.environment (by
    simp [isSelectedContinuation])

@[simp]
theorem costBaseOperand_schemaTerm (source : CIGSLT)
    (operand : InteractionOperandProfile source.theory.presentation)
    (selected : isSelectedContinuation source.cut
      operand.constructor.1 operand.continuation.index = true) :
    (source.costBaseOperand operand selected).schemaTerm =
      costBaseSchemaPattern operand.schemaTerm := by
  rcases operand with
    ⟨constructor, schemaTerm, continuation, continuationPattern,
      continuationWitness, surface, form⟩
  cases form with
  | introduced represented selectedArgument =>
      cases schemaTerm with
      | apply label arguments =>
          simp [costBaseOperand, costBaseSchemaPattern,
            costBasePresentationSymbols, mapPattern, mapPatternSchemaNames]
      | bvar index => exact False.elim selectedArgument
      | fvar name => exact False.elim selectedArgument
      | lambda binder body => exact False.elim selectedArgument
      | multiLambda arity binders body => exact False.elim selectedArgument
      | subst body replacement => exact False.elim selectedArgument
      | collection collectionType elements rest =>
          exact False.elim selectedArgument
  | direct same => simp [costBaseOperand]

@[simp]
theorem costBaseOperand_constructor (source : CIGSLT)
    (operand : InteractionOperandProfile source.theory.presentation)
    (selected : isSelectedContinuation source.cut
      operand.constructor.1 operand.continuation.index = true) :
    (source.costBaseOperand operand selected).constructor =
      source.costBaseAuthoredConstructor operand.constructor := by
  rcases operand with
    ⟨constructor, schemaTerm, continuation, continuationPattern,
      continuationWitness, surface, form⟩
  cases form with
  | introduced represented selectedArgument =>
      cases schemaTerm with
      | apply label arguments => simp [costBaseOperand]
      | bvar index => exact False.elim selectedArgument
      | fvar name => exact False.elim selectedArgument
      | lambda binder body => exact False.elim selectedArgument
      | multiLambda arity binders body => exact False.elim selectedArgument
      | subst body replacement => exact False.elim selectedArgument
      | collection collectionType elements rest =>
          exact False.elim selectedArgument
  | direct same => simp [costBaseOperand]

@[simp]
theorem costBaseOperand_continuation_index (source : CIGSLT)
    (operand : InteractionOperandProfile source.theory.presentation)
    (selected : isSelectedContinuation source.cut
      operand.constructor.1 operand.continuation.index = true) :
    (source.costBaseOperand operand selected).continuation.index =
      operand.continuation.index := by
  rcases operand with
    ⟨constructor, schemaTerm, continuation, continuationPattern,
      continuationWitness, surface, form⟩
  cases form with
  | introduced represented selectedArgument =>
      cases schemaTerm with
      | apply label arguments => simp [costBaseOperand]
      | bvar index => exact False.elim selectedArgument
      | fvar name => exact False.elim selectedArgument
      | lambda binder body => exact False.elim selectedArgument
      | multiLambda arity binders body => exact False.elim selectedArgument
      | subst body replacement => exact False.elim selectedArgument
      | collection collectionType elements rest =>
          exact False.elim selectedArgument
  | direct same => simp [costBaseOperand]

@[simp]
theorem costBaseOperand_continuationVariable_name (source : CIGSLT)
    (operand : InteractionOperandProfile source.theory.presentation)
    (selected : isSelectedContinuation source.cut
      operand.constructor.1 operand.continuation.index = true) :
    (source.costBaseOperand operand selected).continuationVariable.name =
      costSourceSchemaName operand.continuationVariable.name := by
  rcases operand with
    ⟨constructor, schemaTerm, continuation, continuationPattern,
      continuationWitness, surface, form⟩
  cases form with
  | introduced represented selectedArgument =>
      cases schemaTerm with
      | apply label arguments => simp [costBaseOperand]
      | bvar index => exact False.elim selectedArgument
      | fvar name => exact False.elim selectedArgument
      | lambda binder body => exact False.elim selectedArgument
      | multiLambda arity binders body => exact False.elim selectedArgument
      | subst body replacement => exact False.elim selectedArgument
      | collection collectionType elements rest =>
          exact False.elim selectedArgument
  | direct same => simp [costBaseOperand]

@[simp]
theorem costBaseOperand_kind (source : CIGSLT)
    (operand : InteractionOperandProfile source.theory.presentation)
    (selected : isSelectedContinuation source.cut
      operand.constructor.1 operand.continuation.index = true) :
    (source.costBaseOperand operand selected).kind = operand.kind := by
  rcases operand with
    ⟨constructor, schemaTerm, continuation, continuationPattern,
      continuationWitness, surface, form⟩
  cases form with
  | introduced represented selectedArgument =>
      cases schemaTerm with
      | apply label arguments =>
          simp [costBaseOperand, InteractionOperandProfile.kind]
      | bvar index => exact False.elim selectedArgument
      | fvar name => exact False.elim selectedArgument
      | lambda binder body => exact False.elim selectedArgument
      | multiLambda arity binders body => exact False.elim selectedArgument
      | subst body replacement => exact False.elim selectedArgument
      | collection collectionType elements rest =>
          exact False.elim selectedArgument
  | direct same =>
      simp [costBaseOperand, InteractionOperandProfile.kind]

/-- Base transport preserves the exact binary/collection representation of
the source interaction core, including when a direct contact argument is
re-sorted to the wrapped carrier. -/
private theorem costBaseParameter_simple_shape
    {theory : IGSLT} (cut : InteractionCutPresentation theory)
    (constructor : GrammarRule) (index : Nat) (name : String)
    (type : TypeExpr) :
    ∃ mappedType,
      costBaseParameter cut constructor (.simple name type, index) =
        .simple name mappedType := by
  unfold costBaseParameter
  split <;> exact ⟨_, rfl⟩

private theorem costBaseParameter_collection_shape
    {theory : IGSLT} (cut : InteractionCutPresentation theory)
    (constructor : GrammarRule) (index : Nat) (name : String)
    (collectionType : CollType) (elementType : TypeExpr) :
    ∃ mappedElementType,
      costBaseParameter cut constructor
          (.simple name (.collection collectionType elementType), index) =
        .simple name (.collection collectionType mappedElementType) := by
  unfold costBaseParameter
  split <;> exact ⟨_, rfl⟩

private theorem coreContactRepresentation_costBaseConstructor
    (source : CIGSLT) (sort : TypeDecl) (constructor : GrammarRule)
    (representation : ContactRepresentation)
    (represented : coreContactRepresentation? sort constructor =
      some representation) :
    coreContactRepresentation?
        { sort with name := costBaseSortName sort.name }
        (costBaseConstructor source.cut constructor) =
      some representation := by
  rcases sort with ⟨sortName, carrier⟩
  rcases constructor with ⟨label, category, parameters, syntaxPattern, policy⟩
  by_cases categoryEquality : category = sortName
  · subst category
    simp only [coreContactRepresentation?] at represented
    simp only [costBaseConstructor, coreContactRepresentation?]
    cases parameters with
    | nil => simp at represented
    | cons first rest =>
      cases rest with
      | nil =>
        cases first with
        | simple parameterName type =>
          cases type with
          | base name => simp at represented
          | arrow domain codomain => simp at represented
          | multiBinder body => simp at represented
          | collection collectionType elementType =>
            rcases costBaseParameter_collection_shape source.cut
              { label := label, category := sortName,
                params := [.simple parameterName
                  (.collection collectionType elementType)],
                syntaxPattern := syntaxPattern, evalPolicy? := policy }
              0 parameterName collectionType elementType with
              ⟨mappedElementType, mappedShape⟩
            simp only [List.zipIdx_cons, List.map_cons]
            rw [mappedShape]
            simpa using represented
        | abstractionNamed binder name type => simp at represented
        | multiAbstractionNamed binders name type => simp at represented
      | cons second tail =>
        cases tail with
        | nil =>
          cases first with
          | simple firstName firstType =>
            cases second with
            | simple secondName secondType =>
              rcases costBaseParameter_simple_shape source.cut
                { label := label, category := sortName,
                  params := [.simple firstName firstType,
                    .simple secondName secondType],
                  syntaxPattern := syntaxPattern, evalPolicy? := policy }
                0 firstName firstType with ⟨mappedFirst, firstShape⟩
              rcases costBaseParameter_simple_shape source.cut
                { label := label, category := sortName,
                  params := [.simple firstName firstType,
                    .simple secondName secondType],
                  syntaxPattern := syntaxPattern, evalPolicy? := policy }
                1 secondName secondType with ⟨mappedSecond, secondShape⟩
              simp only [List.zipIdx_cons, List.map_cons]
              rw [firstShape, secondShape]
              simpa using represented
            | abstractionNamed binder name type => simp at represented
            | multiAbstractionNamed binders name type => simp at represented
          | abstractionNamed binder name type => simp at represented
          | multiAbstractionNamed binders name type => simp at represented
        | cons third tail => simp at represented
  · simp [coreContactRepresentation?, categoryEquality] at represented

theorem costBaseCore_representsCore (source : CIGSLT) :
    coreContactRepresentation?
        (source.costBaseAuthoredSort source.cut.coreContact.sort).1
        (source.costBaseAuthoredConstructor
          source.cut.coreContact.constructor).1 =
      some source.cut.coreContact.representation := by
  exact coreContactRepresentation_costBaseConstructor source
    source.cut.coreContact.sort.1 source.cut.coreContact.constructor.1
    source.cut.coreContact.representation source.cut.coreContact.representsCore

/-- The exact base copy of the source contact selected from the generated
Cost presentation. -/
def costBaseCoreContact (source : CIGSLT) :
    CoreContactPresentation source.costIGSLT.presentation.presentation where
  sort := source.costBaseAuthoredSort source.cut.coreContact.sort
  constructor := source.costBaseAuthoredConstructor
    source.cut.coreContact.constructor
  representation := source.cut.coreContact.representation
  representsCore := source.costBaseCore_representsCore

/-- The ordered source interaction core transports without changing binary
versus collection contact shape. -/
private theorem CutSourceShape.costBase
    (source : CIGSLT) {program environment core : Pattern}
    (shape : CutSourceShape source.cut.coreContact program environment core) :
    CutSourceShape source.costBaseCoreContact
      (costBaseSchemaPattern program) (costBaseSchemaPattern environment)
      (costBaseSchemaPattern core) := by
  cases shape with
  | binary binaryContact =>
      simpa [costBaseCoreContact, costBaseAuthoredConstructor,
        costBaseConstructor, costBaseSchemaPattern,
        costBasePresentationSymbols, mapPattern, mapPatternSchemaNames,
        mapPatternListSchemaNames_eq_map] using
        (CutSourceShape.binary
          (contact := source.costBaseCoreContact)
          (program := costBaseSchemaPattern program)
          (environment := costBaseSchemaPattern environment)
          binaryContact)
  | collection context rest collectionContact =>
      simpa [costBaseCoreContact, costBaseSchemaPattern,
        costBasePresentationSymbols, mapPattern, mapPatternSchemaNames,
        mapPatternListSchemaNames_eq_map, List.map_map] using
        (CutSourceShape.collection
          (contact := source.costBaseCoreContact)
          (program := costBaseSchemaPattern program)
          (environment := costBaseSchemaPattern environment)
          (mapPatternListSchemaNames costSourceSchemaName
            (context.map (mapPattern costBasePresentationSymbols)))
          (rest.map costSourceSchemaName) collectionContact)

theorem costBaseCoreShape (source : CIGSLT) :
    CutSourceShape source.costBaseCoreContact
      source.costProgramOperand.schemaTerm
      source.costEnvironmentOperand.schemaTerm
      source.costBaseInteractionCore := by
  simpa [costProgramOperand, costEnvironmentOperand,
    costBaseInteractionCore, costBaseSchemaPattern] using
    (CutSourceShape.costBase source source.cut.sourceShape.coreShape)

/-- The source cut's envelope remains a constructor-derived context in the
complete generated Cost signature.  Schema alpha-renaming changes local names
but neither constructor positions nor sorts. -/
theorem costBaseSourceEnvelopeInSignature (source : CIGSLT) :
    SignatureContext source.costWholeLanguage
      (costBaseSortName source.cut.coreContact.sort.1.name)
      (costBaseSortName source.theory.presentation.interactingSort.1.name)
      source.costBaseSourceEnvelope := by
  apply SignatureContext.mapSchemaNames costSourceSchemaName
  apply SignatureContext.mono (sourceLanguage :=
    source.continuationRetyping.generatedLanguage)
  · intro rule membership
    change rule ∈ source.costCoreLanguage.terms
    exact List.mem_append_left _ membership
  · exact source.sourceEnvelopeRetypable

/-- The signing and funding apparatus is itself generated by two ordinary
constructor slots: first the signed-body slot, then the left operand of the
wrapped contact. -/
theorem costFundingEnvelopeInSignature (source : CIGSLT) :
    SignatureContext source.costWholeLanguage
      (costBaseSortName source.theory.presentation.interactingSort.1.name)
      costWrappedSortName source.costFundingEnvelope := by
  apply SignatureContext.simpleArg
      (source := costBaseSortName
        source.theory.presentation.interactingSort.1.name)
      (parameter := costWrappedSortName)
      (rule := costContactConstructor)
      (parameterName := "left")
      (beforeParams := [])
      (afterParams :=
        [.simple "right" (.base costWrappedSortName)])
      (before := [])
      (after := [.apply costFundingConstructorName
        [.apply costTokenStackConsConstructorName
          [.fvar source.costSignatureVariable,
            .fvar source.costStackTailVariable]]])
  · change costContactConstructor ∈ source.costCoreLanguage.terms
    apply List.mem_append_right
    simp [costCoreConstructors]
  · rfl
  · rfl
  · rfl
  · apply SignatureContext.simpleArg
        (source := costBaseSortName
          source.theory.presentation.interactingSort.1.name)
        (parameter := costBaseSortName
          source.theory.presentation.interactingSort.1.name)
        (rule := costSignedConstructor
          source.theory.presentation.interactingSort.1.name)
        (parameterName := "body")
        (beforeParams := [])
        (afterParams :=
          [.simple "signature" (.base costSignatureSortName)])
        (before := [])
        (after := [.fvar source.costSignatureVariable])
    · change costSignedConstructor
          source.theory.presentation.interactingSort.1.name ∈
        source.costCoreLanguage.terms
      apply List.mem_append_right
      simp [costCoreConstructors]
    · rfl
    · rfl
    · rfl
    · exact SignatureContext.hole _

/-- The complete whole-redex envelope is a signature-derived context from the
transported interaction core to the generated wrapped carrier. -/
theorem costWholeRedexEnvelopeInSignature (source : CIGSLT) :
    SignatureContext source.costWholeLanguage
      (costBaseSortName source.cut.coreContact.sort.1.name)
      costWrappedSortName source.costWholeRedexEnvelope := by
  exact SignatureContext.comp source.costFundingEnvelopeInSignature
    source.costBaseSourceEnvelopeInSignature

/-- Base transport is injective on authored constructors.  Validation makes
source labels unique, and the reserved Cost base prefix is injective. -/
theorem costBaseAuthoredConstructor_injective (source : CIGSLT) :
    Function.Injective source.costBaseAuthoredConstructor := by
  intro left right equality
  apply ContinuationRetypingPlan.authoredConstructorLabel_injective
    source.theory.presentation.presentation
  apply costBaseConstructorName_injective
  simpa [costBaseAuthoredConstructor, costBaseConstructor] using
    congrArg
      (fun constructor : AuthoredConstructor source.costWholePresentation =>
        constructor.1.label) equality

/-- The generated rule retains the transported ordered interaction core below
its explicit signing/funding envelope. -/
def costWholeCutSource (source : CIGSLT) :
    EnvelopedCutSource source.costBaseCoreContact
      source.costProgramOperand.schemaTerm
      source.costEnvironmentOperand.schemaTerm
      source.costWholeRedexSource where
  core := source.costBaseInteractionCore
  coreShape := source.costBaseCoreShape
  envelope := source.costWholeRedexEnvelope
  fillsSource := rfl

/-- A declaration from the continuation signature cannot be confused with
the administrative contact constructor.  The proof uses the two disjoint
generated constructor namespaces, not a string scan over equation text. -/
theorem generatedTerm_label_ne_costContact (source : CIGSLT)
    (rule : GrammarRule)
    (membership :
      rule ∈ source.continuationRetyping.generatedLanguage.terms) :
    rule.label ≠ costContactConstructorName := by
  simp only [ContinuationRetypingPlan.generatedLanguage,
    List.mem_append, List.mem_map] at membership
  rcases membership with
    ⟨authored, _authoredMembership, rfl⟩ |
      ⟨wrapped, _wrappedMembership, rfl⟩
  · exact costBaseConstructorName_ne_apparatus authored.label "contact"
  · exact costWrappedConstructorName_ne_apparatus
      wrapped.1.label "contact"

/-- A pattern sorted in the declaration-derived continuation signature has
no reference to the later administrative contact constructor. -/
theorem generatedPattern_contactConstructor_absent (source : CIGSLT)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr}
    (typed : HasType source.continuationRetyping.generatedLanguage
      free bound pattern type) (arity : Nat) :
    (costContactConstructorName, arity) ∉ pattern.constructorRefs := by
  intro referenceMembership
  rcases typed.constructorReferencesDeclared
      (costContactConstructorName, arity) referenceMembership with
    ⟨rule, ruleMembership, labelEquality, _arityEquality⟩
  exact source.generatedTerm_label_ne_costContact rule ruleMembership
    labelEquality

/-- The transported static equation theory is genuinely free of the new
contact constructor on both surfaces.  Equations are retained exactly; their
prior sorting in the generated continuation signature supplies the exclusion
witness required by structural surface matching. -/
theorem costStaticEquation_contactFree (source : CIGSLT)
    (equation : Equation) (membership : equation ∈ source.costStaticEquations) :
    (costContactConstructorName, costContactConstructor.params.length) ∉
        equation.left.constructorRefs ∧
      (costContactConstructorName, costContactConstructor.params.length) ∉
        equation.right.constructorRefs := by
  simp only [costStaticEquations, List.mem_append, List.mem_map] at membership
  rcases membership with
    ⟨sourceEquation, sourceMembership, rfl⟩ |
      ⟨sourceEquation, sourceMembership, rfl⟩
  · rcases (source.equationsRetypable sourceEquation sourceMembership).baseWellSorted with
      ⟨type, leftTyped, rightTyped⟩
    constructor
    · simpa [costBaseEquationDecl, mapEquationSchemaNames] using
        source.generatedPattern_contactConstructor_absent leftTyped
          costContactConstructor.params.length
    · simpa [costBaseEquationDecl, mapEquationSchemaNames] using
        source.generatedPattern_contactConstructor_absent rightTyped
          costContactConstructor.params.length
  · rcases (source.equationsRetypable sourceEquation sourceMembership).wrappedWellSorted with
      ⟨type, leftTyped, rightTyped⟩
    constructor
    · simpa [costWrappedEquationDecl, mapEquationSchemaNames] using
        source.generatedPattern_contactConstructor_absent leftTyped
          costContactConstructor.params.length
    · simpa [costWrappedEquationDecl, mapEquationSchemaNames] using
        source.generatedPattern_contactConstructor_absent rightTyped
          costContactConstructor.params.length

/-- The exact funded interaction closes back into the ordered cut interface.
The selected rewrite remains the singleton rewrite of the generated validated
`LanguageDef`; no contraction callback is introduced. -/
def costInteractionCut (source : CIGSLT) :
    InteractionCutPresentation source.costIGSLT where
  program := source.costProgramOperand
  environment := source.costEnvironmentOperand
  coreContact := source.costBaseCoreContact
  programPlacement := by
    cases source.cut.programPlacement with
    | introduced kind different =>
        apply InteractionOperandPlacement.introduced
        · simp only [costProgramOperand]
          rw [costBaseOperand_kind]
          exact kind
        · intro equality
          simp only [costProgramOperand, costBaseCoreContact] at equality
          rw [costBaseOperand_constructor] at equality
          apply different
          apply source.costBaseAuthoredConstructor_injective
          change source.costBaseAuthoredConstructor
              source.cut.program.constructor =
            source.costBaseAuthoredConstructor
              source.cut.coreContact.constructor at equality
          exact equality
    | direct kind binary ownedByContact atSide =>
        apply InteractionOperandPlacement.direct
        · simp only [costProgramOperand]
          rw [costBaseOperand_kind]
          exact kind
        · exact binary
        · simp only [costProgramOperand, costBaseCoreContact]
          rw [costBaseOperand_constructor]
          exact congrArg source.costBaseAuthoredConstructor ownedByContact
        · simp only [costProgramOperand]
          rw [costBaseOperand_continuation_index]
          exact atSide
  environmentPlacement := by
    cases source.cut.environmentPlacement with
    | introduced kind different =>
        apply InteractionOperandPlacement.introduced
        · simp only [costEnvironmentOperand]
          rw [costBaseOperand_kind]
          exact kind
        · intro equality
          simp only [costEnvironmentOperand, costBaseCoreContact] at equality
          rw [costBaseOperand_constructor] at equality
          apply different
          apply source.costBaseAuthoredConstructor_injective
          change source.costBaseAuthoredConstructor
              source.cut.environment.constructor =
            source.costBaseAuthoredConstructor
              source.cut.coreContact.constructor at equality
          exact equality
    | direct kind binary ownedByContact atSide =>
        apply InteractionOperandPlacement.direct
        · simp only [costEnvironmentOperand]
          rw [costBaseOperand_kind]
          exact kind
        · exact binary
        · simp only [costEnvironmentOperand, costBaseCoreContact]
          rw [costBaseOperand_constructor]
          exact congrArg source.costBaseAuthoredConstructor ownedByContact
        · simp only [costEnvironmentOperand]
          rw [costBaseOperand_continuation_index]
          exact atSide
  sourceShape := source.costWholeCutSource
  sourceEnvelopeInSignature := source.costWholeRedexEnvelopeInSignature
  interactionPremisesEmpty := rfl
  residual := .constructor source.costWholeContactConstructor (by
    change RepresentedBy costContactConstructor source.costWholeRedexTarget
    rw [costWholeRedexTarget_funding_tail]
    exact ⟨by simp [UsesBareCollection, costContactConstructor], rfl,
      by simp [costContactConstructor]⟩)
  surfacesAgree := .structural rfl (by
    intro equation membership
    exact source.costStaticEquation_contactFree equation membership)

@[simp]
theorem costInteractionCut_program_constructor (source : CIGSLT) :
    source.costInteractionCut.program.constructor =
      source.costBaseAuthoredConstructor source.cut.program.constructor := by
  simp [costInteractionCut, costProgramOperand]

@[simp]
theorem costInteractionCut_environment_constructor (source : CIGSLT) :
    source.costInteractionCut.environment.constructor =
      source.costBaseAuthoredConstructor source.cut.environment.constructor := by
  simp [costInteractionCut, costEnvironmentOperand]

@[simp]
theorem costInteractionCut_program_continuation_index (source : CIGSLT) :
    source.costInteractionCut.program.continuation.index =
      source.cut.program.continuation.index := by
  simp [costInteractionCut, costProgramOperand]

@[simp]
theorem costInteractionCut_environment_continuation_index (source : CIGSLT) :
    source.costInteractionCut.environment.continuation.index =
      source.cut.environment.continuation.index := by
  simp [costInteractionCut, costEnvironmentOperand]

@[simp]
theorem costInteractionCut_program_continuationVariable_name
    (source : CIGSLT) :
    source.costInteractionCut.program.continuationVariable.name =
      costSourceSchemaName source.cut.program.continuationVariable.name := by
  simp [costInteractionCut, costProgramOperand]

@[simp]
theorem costInteractionCut_environment_continuationVariable_name
    (source : CIGSLT) :
    source.costInteractionCut.environment.continuationVariable.name =
      costSourceSchemaName source.cut.environment.continuationVariable.name := by
  simp [costInteractionCut, costEnvironmentOperand]

theorem costBaseConstructor_eq_program_iff (source : CIGSLT)
    (rule : GrammarRule)
    (membership : rule ∈ source.theory.presentation.presentation.language.terms) :
    costBaseConstructor source.cut rule =
        source.costInteractionCut.program.constructor.1 ↔
      rule = source.cut.program.constructor.1 := by
  constructor
  · intro equality
    rw [costInteractionCut_program_constructor] at equality
    change costBaseConstructor source.cut rule =
      costBaseConstructor source.cut source.cut.program.constructor.1
        at equality
    have mappedEquality :
        source.costBaseAuthoredConstructor ⟨rule, membership⟩ =
          source.costBaseAuthoredConstructor source.cut.program.constructor := by
      exact Subtype.ext equality
    exact congrArg Subtype.val
      (source.costBaseAuthoredConstructor_injective mappedEquality)
  · intro equality
    subst rule
    rw [costInteractionCut_program_constructor]
    rfl

theorem costBaseConstructor_eq_environment_iff (source : CIGSLT)
    (rule : GrammarRule)
    (membership : rule ∈ source.theory.presentation.presentation.language.terms) :
    costBaseConstructor source.cut rule =
        source.costInteractionCut.environment.constructor.1 ↔
      rule = source.cut.environment.constructor.1 := by
  constructor
  · intro equality
    rw [costInteractionCut_environment_constructor] at equality
    change costBaseConstructor source.cut rule =
      costBaseConstructor source.cut source.cut.environment.constructor.1
        at equality
    have mappedEquality :
        source.costBaseAuthoredConstructor ⟨rule, membership⟩ =
          source.costBaseAuthoredConstructor
            source.cut.environment.constructor := by
      exact Subtype.ext equality
    exact congrArg Subtype.val
      (source.costBaseAuthoredConstructor_injective mappedEquality)
  · intro equality
    subst rule
    rw [costInteractionCut_environment_constructor]
    rfl

/-- Base transport preserves exactly which constructor positions are the two
selected continuations of the retained ordered cut. -/
theorem isSelectedContinuation_costBase (source : CIGSLT)
    (rule : GrammarRule)
    (membership : rule ∈ source.theory.presentation.presentation.language.terms)
    (index : Nat) :
    isSelectedContinuation source.costInteractionCut
        (costBaseConstructor source.cut rule) index =
      isSelectedContinuation source.cut rule index := by
  apply Bool.eq_iff_iff.mpr
  simp only [isSelectedContinuation, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq]
  rw [costBaseConstructor_eq_program_iff source rule membership,
    costBaseConstructor_eq_environment_iff source rule membership,
    costInteractionCut_program_continuation_index,
    costInteractionCut_environment_continuation_index]

theorem costContactConstructor_not_selected (source : CIGSLT)
    (index : Nat) :
    isSelectedContinuation source.costInteractionCut costContactConstructor
      index = false := by
  have notProgram : costContactConstructor ≠
      source.costInteractionCut.program.constructor.1 := by
    rw [costInteractionCut_program_constructor]
    intro equality
    have labelEquality := congrArg GrammarRule.label equality
    exact costBaseConstructorName_ne_apparatus
      source.cut.program.constructor.1.label "contact" labelEquality.symm
  have notEnvironment : costContactConstructor ≠
      source.costInteractionCut.environment.constructor.1 := by
    rw [costInteractionCut_environment_constructor]
    intro equality
    have labelEquality := congrArg GrammarRule.label equality
    exact costBaseConstructorName_ne_apparatus
      source.cut.environment.constructor.1.label "contact" labelEquality.symm
  apply Bool.eq_false_iff.mpr
  intro selected
  simp only [isSelectedContinuation, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq] at selected
  rcases selected with selected | selected
  · exact notProgram selected.1
  · exact notEnvironment selected.1

theorem costSignedConstructor_not_selected (source : CIGSLT)
    (index : Nat) :
    isSelectedContinuation source.costInteractionCut
        (costSignedConstructor
          source.theory.presentation.interactingSort.1.name) index = false := by
  have notProgram :
      costSignedConstructor
          source.theory.presentation.interactingSort.1.name ≠
        source.costInteractionCut.program.constructor.1 := by
    rw [costInteractionCut_program_constructor]
    intro equality
    have labelEquality := congrArg GrammarRule.label equality
    exact costBaseConstructorName_ne_apparatus
      source.cut.program.constructor.1.label "signed" labelEquality.symm
  have notEnvironment :
      costSignedConstructor
          source.theory.presentation.interactingSort.1.name ≠
        source.costInteractionCut.environment.constructor.1 := by
    rw [costInteractionCut_environment_constructor]
    intro equality
    have labelEquality := congrArg GrammarRule.label equality
    exact costBaseConstructorName_ne_apparatus
      source.cut.environment.constructor.1.label "signed" labelEquality.symm
  apply Bool.eq_false_iff.mpr
  intro selected
  simp only [isSelectedContinuation, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq] at selected
  rcases selected with selected | selected
  · exact notProgram selected.1
  · exact notEnvironment selected.1

/-- The source cut's stable envelope transports into the base fiber of the
generated cut, with schema variables alpha-renamed into the reserved Cost
namespace. -/
theorem costBaseSourceEnvelopeStable (source : CIGSLT) :
    ContinuationStableContext source.costInteractionCut
      (costBaseSortName source.cut.coreContact.sort.1.name)
      (costBaseSortName source.theory.presentation.interactingSort.1.name)
      source.costBaseSourceEnvelope := by
  apply ContinuationStableContext.mapSchemaNames costSourceSchemaName
  refine ContinuationStableContext.mapCostBase
      (sourceCut := source.cut) source.costInteractionCut ?_ ?_
        source.sourceEnvelopeStable
  · intro rule membership
    change costBaseConstructor source.cut rule ∈ source.costWholeLanguage.terms
    rw [costWholeLanguage_terms]
    apply List.mem_append_left
    exact source.continuationRetyping.costBaseConstructor_mem_generated
      rule membership
  · exact source.isSelectedContinuation_costBase

/-- The generated signing/contact envelope stays outside the two retained
source-continuation slots. -/
theorem costFundingEnvelopeStable (source : CIGSLT) :
    ContinuationStableContext source.costInteractionCut
      (costBaseSortName source.theory.presentation.interactingSort.1.name)
      costWrappedSortName source.costFundingEnvelope := by
  apply ContinuationStableContext.simpleArg
      (rule := costContactConstructor)
      (parameterName := "left")
      (beforeParams := [])
      (afterParams :=
        [.simple "right" (.base costWrappedSortName)])
      (before := [])
      (after := [.apply costFundingConstructorName
        [.apply costTokenStackConsConstructorName
          [.fvar source.costSignatureVariable,
            .fvar source.costStackTailVariable]]])
  · change costContactConstructor ∈ source.costCoreLanguage.terms
    apply List.mem_append_right
    simp [costCoreConstructors]
  · rfl
  · rfl
  · rfl
  · exact source.costContactConstructor_not_selected 0
  · apply ContinuationStableContext.simpleArg
        (rule := costSignedConstructor
          source.theory.presentation.interactingSort.1.name)
        (parameterName := "body")
        (beforeParams := [])
        (afterParams :=
          [.simple "signature" (.base costSignatureSortName)])
        (before := [])
        (after := [.fvar source.costSignatureVariable])
    · change costSignedConstructor
          source.theory.presentation.interactingSort.1.name ∈
        source.costCoreLanguage.terms
      apply List.mem_append_right
      simp [costCoreConstructors]
    · rfl
    · rfl
    · rfl
    · exact source.costSignedConstructor_not_selected 0
    · exact ContinuationStableContext.hole _

/-- The complete generated redex envelope is stable under another Cost
application: the original stable envelope is retained below two generated
apparatus frames, and all three parts avoid the selected continuations. -/
theorem costWholeRedexEnvelopeStable (source : CIGSLT) :
    ContinuationStableContext source.costInteractionCut
      (costBaseSortName source.cut.coreContact.sort.1.name)
      costWrappedSortName source.costWholeRedexEnvelope := by
  exact ContinuationStableContext.comp source.costFundingEnvelopeStable
    source.costBaseSourceEnvelopeStable

/-! ## Continued closure data for another Cost application -/

@[simp]
theorem costProgramOperand_category (source : CIGSLT) :
    source.costProgramOperand.constructor.1.category =
      costBaseSortName source.cut.program.constructor.1.category := by
  rw [costProgramOperand, costBaseOperand_constructor]
  rfl

@[simp]
theorem costEnvironmentOperand_category (source : CIGSLT) :
    source.costEnvironmentOperand.constructor.1.category =
      costBaseSortName source.cut.environment.constructor.1.category := by
  rw [costEnvironmentOperand, costBaseOperand_constructor]
  rfl

/-- The generated interaction has the canonical hereditary continuation plan:
every constructor except the retained program and environment introductions
receives a wrapped copy at the next Cost layer. -/
def costContinuationRetyping (source : CIGSLT) :
    ContinuationRetypingPlan source.costInteractionCut where
  residualCovered := by
    change (show AuthoredConstructor
        source.costIGSLT.presentation.presentation from
      source.costWholeContactConstructor) ∈
        continuationConstructors source.costInteractionCut
    rw [ContinuationRetypingPlan.mem_continuationConstructors_iff]
    constructor
    · intro equality
      have valueEquality := congrArg Subtype.val equality
      have labelEquality := congrArg GrammarRule.label valueEquality
      rw [costInteractionCut_program_constructor] at labelEquality
      apply costBaseConstructorName_ne_apparatus
        source.cut.program.constructor.1.label "contact"
      simpa [costBaseAuthoredConstructor, costBaseConstructor,
        costWholeContactConstructor, costContactConstructor,
        costContactConstructorName] using labelEquality.symm
    · intro equality
      have valueEquality := congrArg Subtype.val equality
      have labelEquality := congrArg GrammarRule.label valueEquality
      rw [costInteractionCut_environment_constructor] at labelEquality
      apply costBaseConstructorName_ne_apparatus
        source.cut.environment.constructor.1.label "contact"
      simpa [costBaseAuthoredConstructor, costBaseConstructor,
        costWholeContactConstructor, costContactConstructor,
        costContactConstructorName] using labelEquality.symm

end CIGSLT

end Mettapedia.GSLT.LanguageDef
