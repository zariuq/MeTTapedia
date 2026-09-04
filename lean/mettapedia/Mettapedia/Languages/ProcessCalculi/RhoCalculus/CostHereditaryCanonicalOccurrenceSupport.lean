import Mettapedia.GSLT.LanguageDef.CostCanonicalOccurrenceInventoryBridge
import Mettapedia.GSLT.LanguageDef.CostReflectiveSupportOccurrenceSubstitutionComposition
import Mettapedia.GSLT.LanguageDef.CostReflectiveSupportTwoAvailabilitySubstitution
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonical
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryOccurrenceSupportProfile

/-!
# Canonical rho occurrences with authored local support

Every free-variable occurrence in the hereditary rho canonical source frame
is traced to one exact authored inventory occurrence.  The corresponding
occurrence-local support certificate and semantic class suffix are then
retained together.  This deliberately does not assert that the authored
availability equals the final canonical occurrence's local availability;
that comparison is the remaining common-lift obligation.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace CostStaticRegionNode

theorem List.suffix_of_eq {left right : List α} (equality : left = right) :
    left <:+ right := by
  subst right
  exact List.suffix_rfl

private theorem rhoCIGSLT_reflection_eq_rhoReflectionProfile :
    rhoCIGSLT.reflection.1 = rhoReflectionProfile :=
  rfl

/-! ## The exact rho static fragment -/

/-- Every authored constructor underlying a selected rho static constructor is
one of the four non-principal declarations: zero, drop, quote, or parallel.
Input and output are excluded by the continuation plan itself.  Keeping this
classification proof-relevant lets later occurrence arguments eliminate
binder-bearing static frames without inspecting generated wire names. -/
theorem rhoStaticPreimage_sourceConstructor_cases
    {color : CostStaticColor}
    {constructor : rhoCIGSLT.DeclaredCostConstructor}
    (preimage : CostStaticConstructorPreimage rhoCIGSLT color constructor) :
    preimage.sourceConstructor.1 = rhoCalc.terms[0] ∨
      preimage.sourceConstructor.1 = rhoCalc.terms[1] ∨
      preimage.sourceConstructor.1 = rhoCalc.terms[2] ∨
      preimage.sourceConstructor.1 = rhoCalc.terms[3] := by
  have membership := preimage.sourceConstructor.2
  change preimage.sourceConstructor.1 ∈
    [rhoCalc.terms[0], rhoCalc.terms[1], rhoCalc.terms[2],
      rhoCalc.terms[3], rhoCalc.terms[4], rhoCalc.terms[5]] at membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with first | second | third | fourth | input | output
  · exact Or.inl first
  · exact Or.inr (Or.inl second)
  · exact Or.inr (Or.inr (Or.inl third))
  · exact Or.inr (Or.inr (Or.inr fourth))
  · have notPrincipal :=
      (rhoContinuationRetyping.mem_wrappedConstructors_iff
        preimage.sourceConstructor).mp preimage.wrapped
    apply (notPrincipal.2 ?_).elim
    apply Subtype.ext
    exact input.trans rhoInteractionCut_environment_constructor_value.symm
  · have notPrincipal :=
      (rhoContinuationRetyping.mem_wrappedConstructors_iff
        preimage.sourceConstructor).mp preimage.wrapped
    apply (notPrincipal.1 ?_).elim
    apply Subtype.ext
    exact output.trans rhoInteractionCut_program_constructor_value.symm

/- Binder-free syntax used by atomized rho static frames.  It deliberately
excludes explicit substitution as well as both binder constructors. -/
mutual
  /-- One binder-free atomized static frame. -/
  def rhoStaticFrameBinderFree : Pattern → Bool
    | .bvar _ | .fvar _ => true
    | .apply _ arguments => rhoStaticFrameListBinderFree arguments
    | .lambda _ _ | .multiLambda _ _ _ | .subst _ _ => false
    | .collection _ elements _ => rhoStaticFrameListBinderFree elements

  /-- A list of binder-free atomized static frames. -/
  def rhoStaticFrameListBinderFree : List Pattern → Bool
    | [] => true
    | pattern :: patterns =>
        rhoStaticFrameBinderFree pattern &&
          rhoStaticFrameListBinderFree patterns
end

/-- Reflective availability at the hole of a binder-free rho static context.
Applications reset availability exactly at quote constructors; collections
leave it unchanged.  Binder and substitution cases are deliberately inert:
every theorem using this function rules them out with
`rhoStaticFrameBinderFree` before interpreting the result. -/
def staticContextReflectiveAvailable (profile : ReflectionProfile)
    (ambient : List TypeExpr) :
    OneHoleContext → List TypeExpr
  | .hole => ambient
  | .apply constructor _ inner _ =>
      staticContextReflectiveAvailable profile
        (if ReflectiveContextSupport.isQuoteConstructor
            profile constructor then [] else ambient) inner
  | .lambda _ inner =>
      staticContextReflectiveAvailable profile ambient inner
  | .multiLambda _ _ inner =>
      staticContextReflectiveAvailable profile ambient inner
  | .substBody inner _ =>
      staticContextReflectiveAvailable profile ambient inner
  | .substReplacement _ inner =>
      staticContextReflectiveAvailable profile ambient inner
  | .collection _ _ inner _ _ =>
      staticContextReflectiveAvailable profile ambient inner

def rhoStaticContextReflectiveAvailable (ambient : List TypeExpr) :
    OneHoleContext → List TypeExpr
  | .hole => ambient
  | .apply constructor _ inner _ =>
      rhoStaticContextReflectiveAvailable
        (if ReflectiveContextSupport.isQuoteConstructor
            rhoCIGSLT.reflection.1 constructor then [] else ambient) inner
  | .lambda _ inner => rhoStaticContextReflectiveAvailable ambient inner
  | .multiLambda _ _ inner =>
      rhoStaticContextReflectiveAvailable ambient inner
  | .substBody inner _ => rhoStaticContextReflectiveAvailable ambient inner
  | .substReplacement _ inner =>
      rhoStaticContextReflectiveAvailable ambient inner
  | .collection _ _ inner _ _ =>
      rhoStaticContextReflectiveAvailable ambient inner

/-- Static presentation mapping preserves the quote boundaries crossed by a
selected occurrence, and hence preserves its exact reflective availability. -/
theorem rhoStaticContextReflectiveAvailable_mapOneHoleContext
    (color : CostStaticColor) (ambient : List TypeExpr) :
    ∀ context : OneHoleContext,
      staticContextReflectiveAvailable rhoCIGSLT.costWholeReflectionProfile
          ambient
          (CIGSLT.mapOneHoleContext (color.symbols rhoCIGSLT) context) =
        rhoStaticContextReflectiveAvailable ambient context
  | .hole => rfl
  | .apply constructor before inner after => by
      simp only [CIGSLT.mapOneHoleContext,
        staticContextReflectiveAvailable,
        rhoStaticContextReflectiveAvailable,
        reflectiveIsQuoteConstructor_mapCostStatic]
      exact rhoStaticContextReflectiveAvailable_mapOneHoleContext color
        (if ReflectiveContextSupport.isQuoteConstructor
            rhoCIGSLT.reflection.1 constructor then [] else ambient) inner
  | .lambda binder inner => by
      simpa only [CIGSLT.mapOneHoleContext,
        staticContextReflectiveAvailable,
        rhoStaticContextReflectiveAvailable] using
        rhoStaticContextReflectiveAvailable_mapOneHoleContext color ambient
          inner
  | .multiLambda arity binders inner => by
      simpa only [CIGSLT.mapOneHoleContext,
        staticContextReflectiveAvailable,
        rhoStaticContextReflectiveAvailable] using
        rhoStaticContextReflectiveAvailable_mapOneHoleContext color ambient
          inner
  | .substBody inner replacement => by
      simpa only [CIGSLT.mapOneHoleContext,
        staticContextReflectiveAvailable,
        rhoStaticContextReflectiveAvailable] using
        rhoStaticContextReflectiveAvailable_mapOneHoleContext color ambient
          inner
  | .substReplacement body inner => by
      simpa only [CIGSLT.mapOneHoleContext,
        staticContextReflectiveAvailable,
        rhoStaticContextReflectiveAvailable] using
        rhoStaticContextReflectiveAvailable_mapOneHoleContext color ambient
          inner
  | .collection collectionType before inner after rest => by
      simpa only [CIGSLT.mapOneHoleContext,
        staticContextReflectiveAvailable,
        rhoStaticContextReflectiveAvailable] using
        rhoStaticContextReflectiveAvailable_mapOneHoleContext color ambient
          inner

/-- Ambient de Bruijn renaming changes indices and accumulated hole depth but
does not change any quote boundary crossed by a selected occurrence. -/
theorem rhoStaticContextReflectiveAvailable_renameAmbientContextAt
    (rename : Nat → Nat) : ∀ (depth : Nat) (ambient : List TypeExpr)
      (context : OneHoleContext),
      rhoStaticContextReflectiveAvailable ambient
          (ContextSubstitution.renameAmbientContextAt rename depth context).1 =
        rhoStaticContextReflectiveAvailable ambient context
  | _, _, .hole => rfl
  | depth, ambient, .apply constructor before inner after => by
      simp only [ContextSubstitution.renameAmbientContextAt,
        rhoStaticContextReflectiveAvailable]
      exact rhoStaticContextReflectiveAvailable_renameAmbientContextAt rename
        depth
          (if ReflectiveContextSupport.isQuoteConstructor
              rhoCIGSLT.reflection.1 constructor then [] else ambient) inner
  | depth, ambient, .lambda binder inner => by
      simpa only [ContextSubstitution.renameAmbientContextAt,
        rhoStaticContextReflectiveAvailable] using
        rhoStaticContextReflectiveAvailable_renameAmbientContextAt rename
          (depth + 1) ambient inner
  | depth, ambient, .multiLambda arity binders inner => by
      simpa only [ContextSubstitution.renameAmbientContextAt,
        rhoStaticContextReflectiveAvailable] using
        rhoStaticContextReflectiveAvailable_renameAmbientContextAt rename
          (depth + arity) ambient inner
  | depth, ambient, .substBody inner replacement => by
      simpa only [ContextSubstitution.renameAmbientContextAt,
        rhoStaticContextReflectiveAvailable] using
        rhoStaticContextReflectiveAvailable_renameAmbientContextAt rename
          (depth + 1) ambient inner
  | depth, ambient, .substReplacement body inner => by
      simpa only [ContextSubstitution.renameAmbientContextAt,
        rhoStaticContextReflectiveAvailable] using
        rhoStaticContextReflectiveAvailable_renameAmbientContextAt rename
          depth ambient inner
  | depth, ambient, .collection collectionType before inner after rest => by
      simpa only [ContextSubstitution.renameAmbientContextAt,
        rhoStaticContextReflectiveAvailable] using
        rhoStaticContextReflectiveAvailable_renameAmbientContextAt rename
          depth ambient inner

/-- An occurrence of a free variable that remains visible in a typed rho
name has the name type.  Every constructor returning `Name` is an authored
quote, so a nonempty local availability rules out descending through such a
constructor.  The remaining free-variable case is therefore the root name
itself. -/
theorem rhoTypedNameOccurrence_lookup_of_available_ne_nil
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {pattern : Pattern}
    (typed : WellSorted.HasType rhoCalc free bound pattern TypeExpr.name)
    (object : WellSorted.isObjectPattern pattern = true)
    (occurrence : CostStaticFVarOccurrence pattern)
    (ambient : List TypeExpr)
    (available_ne_nil :
      rhoStaticContextReflectiveAvailable ambient occurrence.context ≠ []) :
    free occurrence.name = some TypeExpr.name := by
  cases pattern with
  | bvar index =>
      have impossible := occurrence.name_mem_freeFvarNames
      simp [Pattern.freeFvarNames] at impossible
  | fvar name =>
      cases typed with
      | fvar lookup =>
          have nameEquality : occurrence.name = name := by
            simpa [Pattern.freeFvarNames] using
              occurrence.name_mem_freeFvarNames
          simpa [nameEquality] using lookup
  | apply constructor arguments =>
      obtain ⟨rule, membership, labelEquality, _notBare, typeEquality,
          argumentsTyped⟩ := WellSorted.hasType_apply_inversion typed
      have categoryEquality : rule.category = "Name" :=
        (TypeExpr.base.inj typeEquality).symm
      have sealed :=
        EquationSubstitution.rho_reflectiveNameResultSealed
          rhoReflectivePresentation.toReflectivePresentationDecl
          (by simp [rhoReflectionProfile]) rule membership categoryEquality
      let view := Classical.choice
        (CostApplyOccurrenceView.nonempty constructor arguments occurrence)
      have localNil : rhoStaticContextReflectiveAvailable ambient
          occurrence.context = [] := by
        rw [view.context_eq]
        simp [rhoStaticContextReflectiveAvailable,
          rhoCIGSLT_reflection_eq_rhoReflectionProfile, labelEquality,
          sealed.1]
      exact (available_ne_nil localNil).elim
  | lambda binder body =>
      simp [WellSorted.isObjectPattern] at object
  | multiLambda arity binders body =>
      simp [WellSorted.isObjectPattern] at object
  | subst body replacement =>
      simp [WellSorted.isObjectPattern] at object
  | collection collectionType elements rest =>
      rcases WellSorted.hasType_collection_inversion typed with
        ⟨elementType, typeEquality, elementsTyped⟩ |
          ⟨rule, parameterName, elementType, membership, parameterShape,
            typeEquality, elementsTyped⟩
      · simp at typeEquality
      · have categoryEquality : rule.category = "Name" :=
          (TypeExpr.base.inj typeEquality).symm
        have sealed :=
          EquationSubstitution.rho_reflectiveNameResultSealed
            rhoReflectivePresentation.toReflectivePresentationDecl
            (by simp [rhoReflectionProfile]) rule membership categoryEquality
        exact (sealed.2 ⟨parameterName, collectionType, elementType,
          parameterShape⟩).elim

/-- Typing inversion for the authored rho Quote/Drop redex.  The exposed
payload lies in the exact `Name` fibre independently of reflective-support
data. -/
theorem rhoQuoteDrop_inner_typed
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {inner : Pattern} {type : TypeExpr}
    (typed : WellSorted.HasType rhoCalc free bound
      (.apply "NQuote" [.apply "PDrop" [inner]]) type) :
    WellSorted.HasType rhoCalc free bound inner TypeExpr.name := by
  obtain ⟨rule, membership, labelEquality, _notBare, _typeEquality,
      argumentsTyped⟩ := WellSorted.hasType_apply_inversion typed
  simp [rhoCalc] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
  · simp at labelEquality
  · simp at labelEquality
  · cases argumentsTyped with
    | @cons _ argument arguments parameter parameters expected
        representation parameterType argumentTyped tailTyped =>
        cases tailTyped
        have expectedEquality : expected = TypeExpr.proc := by
          simpa [WellSorted.parameterType?, TypeExpr.proc,
            TypeExpr.baseType] using parameterType.symm
        subst expected
        obtain ⟨innerTyped, _innerSafe⟩ :=
          CanonicalSupport.drop_argument_supportSafe argumentTyped
            (argumentTyped.reflectiveSupportSafeAt_empty bound)
        exact innerTyped
  · simp at labelEquality
  · simp at labelEquality
  · simp at labelEquality

/-- Pointwise rho canonicalization preserves a typed constructor-argument
spine at an explicitly supplied quote-visible depth. -/
theorem rhoCanonicalizeListByDepths_argumentsTyped
    {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
    (availableDepth scopeDepth : Nat)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {arguments : List Pattern} {parameters : List TermParam}
    (typed : WellSorted.ArgumentsHaveTypes rhoCalc free bound arguments
      parameters)
    (canonicalizable : CanonicalSupport.ParametersCanonicalizable parameters)
    (object : WellSorted.isObjectPatternList arguments = true) :
    WellSorted.ArgumentsHaveTypes rhoCalc free bound
      (canonicalizeListByDepths key rhoReflectivePresentation availableDepth
        scopeDepth arguments) parameters := by
  cases typed with
  | nil => rfl
  | @cons bound argument arguments parameter parameters expected representation
      parameterType argumentTyped argumentsTyped =>
      have objectParts : WellSorted.isObjectPattern argument = true ∧
          WellSorted.isObjectPatternList arguments = true := by
        simpa [WellSorted.isObjectPatternList] using object
      have argumentCanonicalizable :
          CanonicalSupport.CanonicalizableRhoType expected :=
        canonicalizable parameter (by simp) expected parameterType
      obtain ⟨normalizedArgumentTyped, _normalizedArgumentSafe⟩ :=
        CanonicalSupport.canonicalizeByDepths_supportSafe key scopeDepth
          argumentTyped
          (argumentTyped.reflectiveSupportSafeAt_empty
            (List.replicate availableDepth TypeExpr.name))
          argumentCanonicalizable objectParts.1
      have tailCanonicalizable :
          CanonicalSupport.ParametersCanonicalizable parameters := by
        intro tailParameter membership tailExpected tailType
        exact canonicalizable tailParameter (by simp [membership])
          tailExpected tailType
      have normalizedArgumentsTyped :=
        rhoCanonicalizeListByDepths_argumentsTyped key availableDepth
          scopeDepth argumentsTyped tailCanonicalizable objectParts.2
      have normalizedRepresentation :=
        CanonicalSupport.matchesParameterRepresentation_canonicalizeByDepths
          key availableDepth scopeDepth parameter argument representation
      simpa [canonicalizeListByDepths] using
        WellSorted.ArgumentsHaveTypes.cons normalizedRepresentation
          parameterType normalizedArgumentTyped normalizedArgumentsTyped

/-- Minimal elementwise typing carried by the syntax-directed occurrence
trace.  Constructor parameters and homogeneous collection fibres both forget
to this common interface. -/
def RhoPatternListHasType (free : WellSorted.FreeTypeContext)
    (bound : List TypeExpr) (patterns : List Pattern) : Prop :=
  ∀ pattern ∈ patterns, ∃ type,
    WellSorted.HasType rhoCalc free bound pattern type

theorem RhoPatternListHasType.ofArguments
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {arguments : List Pattern} {parameters : List TermParam}
    (typed : WellSorted.ArgumentsHaveTypes rhoCalc free bound arguments
      parameters) :
    RhoPatternListHasType free bound arguments := by
  cases typed with
  | nil => simp [RhoPatternListHasType]
  | @cons argument arguments parameter parameters expected representation
      parameterType argumentTyped argumentsTyped =>
      intro pattern membership
      simp only [List.mem_cons] at membership
      rcases membership with rfl | membership
      · exact ⟨expected, argumentTyped⟩
      · exact RhoPatternListHasType.ofArguments argumentsTyped pattern
          membership

theorem RhoPatternListHasType.ofElements
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {elements : List Pattern} {elementType : TypeExpr}
    (typed : WellSorted.ElementsHaveType rhoCalc free bound elements
      elementType) :
    RhoPatternListHasType free bound elements := by
  cases typed with
  | nil => simp [RhoPatternListHasType]
  | cons elementTyped elementsTyped =>
      intro pattern membership
      simp only [List.mem_cons] at membership
      rcases membership with rfl | membership
      · exact ⟨_, elementTyped⟩
      · exact RhoPatternListHasType.ofElements elementsTyped pattern membership

/-- At the rho application finisher, availability is either preserved
exactly or the selected occurrence is exposed from a typed `Name` payload.
This is the local typed half of the canonical ancestry dichotomy. -/
theorem rhoStaticContextReflectiveAvailable_finishApplyOccurrenceSource_eq_or_name
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    (constructor : String) (arguments : List Pattern) {type : TypeExpr}
    (typed : WellSorted.HasType rhoCalc free bound
      (.apply constructor arguments) type)
    (object : WellSorted.isObjectPattern
      (.apply constructor arguments) = true)
    (occurrence : CostStaticFVarOccurrence
      (finishNormalizeReflectiveApply rhoReflectivePresentation constructor
        arguments)) (ambient : List TypeExpr) :
    rhoStaticContextReflectiveAvailable
        (if ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.reflection.1
            constructor then [] else ambient)
        (finishApplyOccurrenceSource rhoReflectivePresentation constructor
          arguments occurrence).occurrence.context =
        rhoStaticContextReflectiveAvailable ambient occurrence.context ∨
      (rhoStaticContextReflectiveAvailable
          (if ReflectiveContextSupport.isQuoteConstructor
              rhoCIGSLT.reflection.1 constructor then [] else ambient)
          (finishApplyOccurrenceSource rhoReflectivePresentation constructor
            arguments occurrence).occurrence.context = [] ∧
        free occurrence.name = some TypeExpr.name) := by
  unfold finishApplyOccurrenceSource
  generalize shapeEquality :
    finishApplyShape rhoReflectivePresentation constructor arguments = shape
  cases shape with
  | retained resultEquality =>
      left
      exact
        (rhoStaticContextReflectiveAvailable_applyOccurrenceArgument ambient
          constructor arguments (occurrence.castRoot resultEquality)).trans
        (rhoStaticContextReflectiveAvailable_castRoot resultEquality occurrence
          ambient)
  | exposed name constructorEquality argumentsEquality resultEquality =>
      subst constructor
      subst arguments
      have payloadTyped : WellSorted.HasType rhoCalc free bound name
          TypeExpr.name :=
        rhoQuoteDrop_inner_typed typed
      have payloadObject : WellSorted.isObjectPattern name = true := by
        simpa [WellSorted.isObjectPattern,
          WellSorted.isObjectPatternList] using object
      let exposedOccurrence := occurrence.castRoot resultEquality
      have quoted : ReflectiveContextSupport.isQuoteConstructor
          rhoCIGSLT.reflection.1 "NQuote" = true := by
        simp [rhoReflectionProfile,
          ReflectiveContextSupport.isQuoteConstructor,
          rhoReflectivePresentation]
      by_cases targetNil :
          rhoStaticContextReflectiveAvailable ambient
            occurrence.context = []
      · left
        rw [if_pos quoted]
        rw [rhoStaticContextReflectiveAvailable_nil]
        exact targetNil.symm
      · right
        constructor
        · rw [if_pos quoted]
          exact rhoStaticContextReflectiveAvailable_nil _
        · have exposedAvailableNe :
            rhoStaticContextReflectiveAvailable ambient
              exposedOccurrence.context ≠ [] := by
            intro exposedNil
            apply targetNil
            exact
              (rhoStaticContextReflectiveAvailable_castRoot resultEquality
                occurrence ambient).symm.trans exposedNil
          exact rhoTypedNameOccurrence_lookup_of_available_ne_nil payloadTyped
            payloadObject exposedOccurrence ambient exposedAvailableNe

/-- Application-occurrence inversion retaining the complete zipper equality,
not merely the selected child. -/
theorem planOccurrence_application_split_context
    {source : CIGSLT}
    {sourceBound targetBound sourceAvailable : List TypeExpr}
    {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
    {boundaries : List CostRegionBoundary} {sourceLabel : String}
    {constructor : source.DeclaredCostConstructor}
    {children : List (CostStaticPlanDecoration source)}
    {name : String} {context : OneHoleContext} {available : List TypeExpr}
    (occurrence : CostStaticPlanAbstractOccurrence source name
      (.mk sourceBound targetBound sourceAvailable outer pattern sourceType
        boundaries (.application sourceLabel constructor children))
      context available) :
    ∃ before child after inner,
      children = before ++ child :: after ∧
        context = .apply sourceLabel
          (before.map CostStaticPlanDecoration.abstractPattern) inner
          (after.map CostStaticPlanDecoration.abstractPattern) ∧
        Nonempty (CostStaticPlanAbstractOccurrence source name child inner
          available) := by
  cases occurrence with
  | application nested => exact ⟨_, _, _, _, rfl, rfl, ⟨nested⟩⟩

/-- Collection counterpart of `planOccurrence_application_split_context`. -/
theorem planOccurrence_collection_split_context
    {source : CIGSLT}
    {sourceBound targetBound sourceAvailable : List TypeExpr}
    {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
    {boundaries : List CostRegionBoundary} {collectionType : CollType}
    {sourceRest : Option String} {choice : CostCollectionTypingChoice}
    {children : List (CostStaticPlanDecoration source)}
    {name : String} {context : OneHoleContext} {available : List TypeExpr}
    (occurrence : CostStaticPlanAbstractOccurrence source name
      (.mk sourceBound targetBound sourceAvailable outer pattern sourceType
        boundaries (.collection collectionType sourceRest choice children))
      context available) :
    ∃ before child after inner,
      children = before ++ child :: after ∧
        context = .collection collectionType
          (before.map CostStaticPlanDecoration.abstractPattern) inner
          (after.map CostStaticPlanDecoration.abstractPattern) sourceRest ∧
        Nonempty (CostStaticPlanAbstractOccurrence source name child inner
          available) := by
  cases occurrence with
  | collection nested => exact ⟨_, _, _, _, rfl, rfl, ⟨nested⟩⟩

mutual
  /-- Semantic-atom reification changes only free-variable spellings, so it
  preserves the binder-free static-frame fragment exactly. -/
  theorem rhoStaticFrameBinderFree_reify
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {occurrences : List CostRegionOccurrence}
      {table : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
        occurrences}
      {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
        table}
      {root pattern : Pattern}
      {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
        table values root}
      (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
        inventory) :
      rhoStaticFrameBinderFree (environment.reify pattern) =
        rhoStaticFrameBinderFree pattern := by
    cases pattern with
    | bvar | fvar =>
        simp [Pattern.renameFVars, rhoStaticFrameBinderFree]
    | apply constructor arguments =>
        simp only [CostStaticAtomEnvironment.reify,
          rhoStaticFrameBinderFree]
        exact rhoStaticFrameListBinderFree_reify environment arguments
    | lambda | multiLambda | subst =>
        simp [Pattern.renameFVars, rhoStaticFrameBinderFree]
    | collection collectionType elements rest =>
        simp only [CostStaticAtomEnvironment.reify,
          rhoStaticFrameBinderFree]
        exact rhoStaticFrameListBinderFree_reify environment elements
  termination_by 3 * sizeOf pattern + 2

  /-- List companion to binder-free reification. -/
  theorem rhoStaticFrameListBinderFree_reify
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {occurrences : List CostRegionOccurrence}
      {table : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
        occurrences}
      {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
        table}
      {root : Pattern}
      {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
        table values root}
      (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
        inventory) :
      ∀ patterns,
        rhoStaticFrameListBinderFree (patterns.map environment.reify) =
          rhoStaticFrameListBinderFree patterns
    | [] => rfl
    | pattern :: patterns => by
        simp only [List.map_cons, rhoStaticFrameListBinderFree]
        rw [rhoStaticFrameBinderFree_reify (pattern := pattern) environment,
          rhoStaticFrameListBinderFree_reify environment patterns]
  termination_by patterns => 3 * sizeOf patterns + 1

  decreasing_by
    all_goals simp_wf <;> omega
end

/-- The three non-bare rho static declarations have only base-sorted simple
parameters.  Parallel is represented by a bare collection and therefore
cannot occur in an application plan. -/
theorem rhoStaticPreimage_nonBare_parameters_base
    {color : CostStaticColor}
    {constructor : rhoCIGSLT.DeclaredCostConstructor}
    (preimage : CostStaticConstructorPreimage rhoCIGSLT color constructor)
    (notBare : ¬ WellSorted.UsesBareCollection
      preimage.sourceConstructor.1) :
    ∀ parameter ∈ preimage.sourceConstructor.1.params,
      ∃ category, WellSorted.parameterType? parameter =
        some (.base category) := by
  intro parameter membership
  rcases rhoStaticPreimage_sourceConstructor_cases preimage with
    zero | drop | quote | parallel
  · rw [zero] at membership
    simp [rhoCalc] at membership
  · rw [drop] at membership
    simp [rhoCalc] at membership
    subst parameter
    exact ⟨"Name", rfl⟩
  · rw [quote] at membership
    simp [rhoCalc] at membership
    subst parameter
    exact ⟨"Proc", rfl⟩
  · apply (notBare ?_).elim
    rw [parallel]
    exact ⟨"ps", .hashBag, TypeExpr.proc, by rfl⟩

mutual
  /-- A rho static plan in a base-sort fibre erases to a binder-free atom
  frame.  Non-static subterms have already become boundary variables. -/
  theorem CostStaticRegionPlan.rhoAbstractPattern_binderFree_of_base
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound}
      {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
      (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer pattern sourceType)
      (base : ∃ category, sourceType = .base category) :
      rhoStaticFrameBinderFree plan.abstractPattern = true := by
    cases plan with
    | bvar | fvar | boundaryApplication | boundaryCollection => rfl
    | @application sourceBound targetBound sourceAvailable thinning outer
        wireName arguments constructor rendered current preimage notBare
        children =>
        simpa [CostStaticRegionPlan.abstractPattern,
          rhoStaticFrameBinderFree] using
          CostStaticArgumentPlan.rhoAbstractPatterns_binderFree_of_base
            children
            (rhoStaticPreimage_nonBare_parameters_base preimage notBare)
    | @lambda sourceBound targetBound sourceAvailable thinning outer binder
        body domain codomain bodyPlan =>
        obtain ⟨category, impossible⟩ := base
        cases impossible
    | @multiLambda sourceBound targetBound sourceAvailable thinning outer arity
        binders body domain codomain bodyPlan =>
        obtain ⟨category, impossible⟩ := base
        cases impossible
    | @collection sourceBound targetBound sourceAvailable thinning outer
        collectionType elements rest sourceType choice selected children =>
        obtain ⟨category, sourceTypeEquality⟩ := base
        cases sourceTypeEquality
        rcases mem_costStaticCollectionTypingChoices_sound rhoCIGSLT color
            targetFree targetBound collectionType elements
            (mapTypeExpr (color.symbols rhoCIGSLT) (.base category)) choice
            selected with direct | bare
        · obtain ⟨sourceElementType, choiceEquality, expectedEquality,
              _checked⟩ := direct
          have impossible : (.base category : TypeExpr) =
              .collection collectionType sourceElementType :=
            mapTypeExpr_costStatic_injective rhoCIGSLT color expectedEquality
          cases impossible
        · obtain ⟨rule, sourceElementType, choiceEquality, membership,
              _wrapped, _expectedEquality, parameterName, parameterShape,
              _checked⟩ := bare
          have ruleEquality : rule = rhoCalc.terms[3] :=
            CostCanonicalLaws.rho_rule_eq_parallel_of_bare_shape membership
              parameterShape
          subst rule
          simp [rhoCalc, TypeExpr.bag, TypeExpr.proc,
            TypeExpr.baseType] at parameterShape
          have sourceElementEquality : sourceElementType = TypeExpr.proc := by
            exact parameterShape.2.2.symm
          cases sourceElementEquality
          cases choiceEquality
          simpa [CostStaticRegionPlan.abstractPattern,
            rhoStaticFrameBinderFree] using
            CostStaticElementPlan.rhoAbstractPatterns_binderFree_of_base
              children ⟨"Proc", rfl⟩
  termination_by 3 * sizeOf pattern + 2

  /-- Ordered arguments of a rho static application remain binder-free when
  every authored parameter has a base result type. -/
  theorem CostStaticArgumentPlan.rhoAbstractPatterns_binderFree_of_base
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound}
      {outer : OneHoleContext} {wireName : String}
      {before arguments : List Pattern} {parameters : List TermParam}
      (plan : CostStaticArgumentPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer wireName before arguments
          parameters)
      (parametersBase : ∀ parameter ∈ parameters,
        ∃ category, WellSorted.parameterType? parameter =
          some (.base category)) :
      rhoStaticFrameListBinderFree plan.abstractPatterns = true := by
    cases plan with
    | nil => rfl
    | @cons sourceBound targetBound sourceAvailable thinning outer wireName
        before argument arguments parameter parameters sourceExpected
        representation parameterType head tail =>
        obtain ⟨category, expectedBase⟩ :=
          parametersBase parameter (by simp)
        have sourceExpectedEquality : sourceExpected = .base category :=
          Option.some.inj (parameterType.symm.trans expectedBase)
        subst sourceExpected
        have tailBase : ∀ tailParameter ∈ parameters,
            ∃ tailCategory, WellSorted.parameterType? tailParameter =
              some (.base tailCategory) := by
          intro tailParameter membership
          exact parametersBase tailParameter (by simp [membership])
        simp [CostStaticArgumentPlan.abstractPatterns,
          rhoStaticFrameListBinderFree,
          CostStaticRegionPlan.rhoAbstractPattern_binderFree_of_base head
            ⟨category, rfl⟩,
          CostStaticArgumentPlan.rhoAbstractPatterns_binderFree_of_base tail
            tailBase]
  termination_by 3 * sizeOf arguments + 1

  /-- Homogeneous elements of a rho static parallel frame remain binder-free
  when their authored element type is a base sort. -/
  theorem CostStaticElementPlan.rhoAbstractPatterns_binderFree_of_base
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound}
      {outer : OneHoleContext} {collectionType : CollType}
      {before elements : List Pattern} {rest : Option String}
      {sourceElementType : TypeExpr}
      (plan : CostStaticElementPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer collectionType before
          elements rest sourceElementType)
      (base : ∃ category, sourceElementType = .base category) :
      rhoStaticFrameListBinderFree plan.abstractPatterns = true := by
    cases plan with
    | nil => rfl
    | cons head tail =>
        simp [CostStaticElementPlan.abstractPatterns,
          rhoStaticFrameListBinderFree,
          CostStaticRegionPlan.rhoAbstractPattern_binderFree_of_base head base,
          CostStaticElementPlan.rhoAbstractPatterns_binderFree_of_base tail
            base]
  termination_by 3 * sizeOf elements + 1
  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega
end

/-- The actual source skeleton selected by a rho static node is binder-free.
This is a theorem about the plan authority, not a post-hoc syntax check. -/
theorem skeleton_binderFree
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree) :
    rhoStaticFrameBinderFree node.skeleton.1 = true := by
  rw [node.skeleton_pattern]
  exact CostStaticRegionPlan.rhoAbstractPattern_binderFree_of_base node.plan
    ⟨node.sourceSort.1, rfl⟩

/-- Replacing authored leaves by semantic atom names cannot introduce a
binder into the exact source frame used by hereditary canonicalization. -/
theorem reifiedSourceFrame_binderFree
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory) :
    rhoStaticFrameBinderFree (node.reifiedSourceFrame environment).1 = true := by
  rw [node.reifiedSourceFrame_pattern,
    rhoStaticFrameBinderFree_reify environment]
  exact skeleton_binderFree node

/-! ## Binder-free preservation through keyed canonical phases -/

/-- A binder-free list is equivalently binder-free at each member. -/
theorem rhoStaticFrameListBinderFree_iff_forall_mem :
    ∀ patterns,
      rhoStaticFrameListBinderFree patterns = true ↔
        ∀ pattern ∈ patterns, rhoStaticFrameBinderFree pattern = true
  | [] => by simp [rhoStaticFrameListBinderFree]
  | pattern :: patterns => by
      simp [rhoStaticFrameListBinderFree,
        rhoStaticFrameListBinderFree_iff_forall_mem patterns]

/-- The Quote/Drop finisher can only retain a binder-free application or
expose the binder-free payload already present below its Drop argument. -/
theorem rhoStaticFrameBinderFree_finishApply
    (declaration : ReflectivePresentationDecl) (constructor : String)
    (arguments : List Pattern)
    (argumentsFree : rhoStaticFrameListBinderFree arguments = true) :
    rhoStaticFrameBinderFree
        (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
          declaration constructor arguments) = true := by
  generalize shapeEquality : finishApplyShape declaration constructor
    arguments = shape
  cases shape with
  | retained resultEquality =>
      rw [resultEquality]
      exact argumentsFree
  | exposed name constructorEquality argumentsEquality resultEquality =>
      rw [resultEquality]
      rw [argumentsEquality] at argumentsFree
      simpa [rhoStaticFrameListBinderFree, rhoStaticFrameBinderFree] using
        argumentsFree

/-- Parallel flattening, unit filtering, and stable key sorting retain the
binder-free property of every surviving exact member. -/
theorem rhoStaticFrameListBinderFree_normalizeParallelElementsBy
    {Key : Type} [LinearOrder Key] (key : Pattern → Key)
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern)
    (patternsFree : rhoStaticFrameListBinderFree patterns = true) :
    rhoStaticFrameListBinderFree
        (normalizeParallelElementsBy key declaration patterns) = true := by
  rw [rhoStaticFrameListBinderFree_iff_forall_mem] at patternsFree ⊢
  intro member membership
  have ordinaryMembership :
      member ∈ normalizeParallelElements declaration patterns :=
    (normalizeParallelElementsBy_perm key declaration patterns).mem_iff.mp
      membership
  obtain ⟨source, sourceMembership, memberMembership⟩ :=
    normalizeParallelElements_mem_source ordinaryMembership
  have sourceFree := patternsFree source sourceMembership
  rcases mem_parallelSplice memberMembership with
    ⟨elements, sourceEquality, memberInElements⟩ |
      ⟨memberEquality, _notParallel⟩
  · subst source
    simp only [rhoStaticFrameBinderFree] at sourceFree
    exact (rhoStaticFrameListBinderFree_iff_forall_mem elements).mp sourceFree
      member memberInElements
  · subst member
    exact sourceFree

/-- Empty, singleton, and genuine parallel rebuilding introduce no binders. -/
theorem rhoStaticFrameBinderFree_collapseParallel
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern)
    (patternsFree : rhoStaticFrameListBinderFree patterns = true) :
    rhoStaticFrameBinderFree (collapseParallel declaration patterns) = true := by
  cases patterns with
  | nil => rfl
  | cons pattern patterns =>
      cases patterns with
      | nil =>
          simpa [collapseParallel, rhoStaticFrameListBinderFree] using
            patternsFree
      | cons second rest =>
          simpa [collapseParallel, rhoStaticFrameBinderFree] using patternsFree

mutual
  /-- Two-depth keyed canonicalization preserves binder-freedom.  This is the
  syntactic half of the rho availability dichotomy: canonicalization cannot
  create an intervening binder around an atom occurrence. -/
  theorem rhoStaticFrameBinderFree_canonicalizeByDepths
      {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl)
      (availableDepth scopeDepth : Nat) :
      ∀ pattern,
        rhoStaticFrameBinderFree pattern = true →
          rhoStaticFrameBinderFree
            (canonicalizeByDepths key declaration availableDepth scopeDepth
              pattern) = true
    | .bvar _, _ => rfl
    | .fvar _, _ => rfl
    | .apply constructor arguments, free => by
        simp only [canonicalizeByDepths]
        apply rhoStaticFrameBinderFree_finishApply declaration constructor
        apply rhoStaticFrameListBinderFree_canonicalizeListByDepths key
          declaration
        exact free
    | .lambda _ _, free => by
        simp [rhoStaticFrameBinderFree] at free
    | .multiLambda _ _ _, free => by
        simp [rhoStaticFrameBinderFree] at free
    | .subst _ _, free => by
        simp [rhoStaticFrameBinderFree] at free
    | .collection collectionType elements none, free => by
        simp only [canonicalizeByDepths]
        have normalizedFree :=
          rhoStaticFrameListBinderFree_canonicalizeListByDepths key
            declaration availableDepth scopeDepth elements free
        split
        · apply rhoStaticFrameBinderFree_collapseParallel declaration
          exact rhoStaticFrameListBinderFree_normalizeParallelElementsBy
            (key availableDepth scopeDepth) declaration _ normalizedFree
        · exact normalizedFree
    | .collection collectionType elements (some rest), free => by
        simp only [canonicalizeByDepths, rhoStaticFrameBinderFree]
        exact rhoStaticFrameListBinderFree_canonicalizeListByDepths key
          declaration availableDepth scopeDepth elements free
  termination_by pattern => 3 * sizeOf pattern + 2

  /-- List companion to binder-free keyed canonicalization. -/
  theorem rhoStaticFrameListBinderFree_canonicalizeListByDepths
      {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl)
      (availableDepth scopeDepth : Nat) :
      ∀ patterns,
        rhoStaticFrameListBinderFree patterns = true →
          rhoStaticFrameListBinderFree
            (canonicalizeListByDepths key declaration availableDepth scopeDepth
              patterns) = true
    | [], _ => rfl
    | pattern :: patterns, free => by
        simp only [canonicalizeListByDepths, rhoStaticFrameListBinderFree,
          Bool.and_eq_true] at free ⊢
        exact ⟨
          rhoStaticFrameBinderFree_canonicalizeByDepths key declaration
            availableDepth scopeDepth pattern free.1,
          rhoStaticFrameListBinderFree_canonicalizeListByDepths key declaration
            availableDepth scopeDepth patterns free.2⟩
  termination_by patterns => 3 * sizeOf patterns + 1

  decreasing_by
    all_goals simp_wf <;> omega
end

/-- The exact keyed canonical source representative consumed by hereditary
restoration remains binder-free. -/
theorem semanticCanonicalizedSourcePattern_binderFree
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory) :
    rhoStaticFrameBinderFree
        (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
          rhoReflectivePresentation node.targetBound.length 0
          (node.reifiedSourceFrame environment).1) = true :=
  rhoStaticFrameBinderFree_canonicalizeByDepths
    (sourceSemanticPatternKeyAt node environment) rhoReflectivePresentation
      node.targetBound.length 0 (node.reifiedSourceFrame environment).1
        (reifiedSourceFrame_binderFree node environment)

/-! ## Exact quote-local safety at authored occurrences -/

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
mutual
  /-- In a binder-free rho static frame, the semantic value attached to an
  exact plan occurrence is safe at the availability computed by that same
  occurrence's zipper.  Unlike `semanticLeafWitness`, the result does not
  existentially forget where quote constructors reset availability. -/
  theorem CostStaticRegionPlan.semanticLeafSafeAt_quoteLocal
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
      {pattern : Pattern} {sourceType : TypeExpr}
      (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer pattern sourceType)
      (frameFree : rhoStaticFrameBinderFree plan.abstractPattern = true)
      (collectionDeterministic :
        WellSorted.CollectionChoiceDeterministic
          rhoCIGSLT.costWholeLanguage)
      {globalOccurrences : List CostRegionOccurrence}
      (globalTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
        globalOccurrences)
      (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
        globalTable)
      (entriesSubset : plan.boundaryTable.entries ⊆ globalTable.entries)
      {targetTyped : WellSorted.HasType rhoCIGSLT.costWholeLanguage targetFree
        targetBound pattern (mapTypeExpr (color.symbols rhoCIGSLT) sourceType)}
      {support : ContextSupport.Support} {reflectiveAvailable : List TypeExpr}
      {binderImage : TypeExpr → TypeExpr}
      (targetSafe : targetTyped.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile support reflectiveAvailable
          binderImage)
      {root : Pattern}
      (parameter : CostStaticParameterOccurrence rhoCIGSLT color targetFree
        globalTable values root)
      {name : String} {context : OneHoleContext}
      {planAvailable : List TypeExpr}
      (planOccurrence : CostStaticPlanAbstractOccurrence rhoCIGSLT name
        plan.decoration context planAvailable)
      (nameEquality : parameter.fvarOccurrence.name = name)
      (childrenPreserve : CostStaticBoundaryChildReflectiveSupportPreserving
        globalTable values support binderImage) :
      CostStaticSemanticLeafSafeAt support
        (rhoStaticContextReflectiveAvailable reflectiveAvailable context)
          binderImage parameter := by
    cases plan with
    | bvar sourceIndex lookup correspondence availableScope =>
        cases planOccurrence
    | @fvar sourceBound targetBound sourceAvailable thinning outer sourceName
        sourceType targetLookup =>
        cases planOccurrence with
        | sourceFVar =>
            simpa [rhoStaticContextReflectiveAvailable] using
              sourceLeafSemanticSafeAt targetLookup targetSafe parameter
                nameEquality
    | boundaryApplication constructor rendered outsideCurrent certified
        certifies =>
        cases planOccurrence with
        | boundaryApplication =>
            have localMembership : certified.typed ∈
                [certified.typed] := List.mem_cons_self
            have globalMembership : certified.typed ∈ globalTable.entries :=
              entriesSubset localMembership
            simpa [rhoStaticContextReflectiveAvailable] using
              boundaryLeafSemanticSafeAt certified.typed globalMembership
                certified.content_eq certified.targetType_eq targetSafe
                  childrenPreserve parameter nameEquality
    | application constructor rendered current preimage notBare children =>
        obtain ⟨before, child, after, inner, decomposition, contextEquality,
            ⟨nested⟩⟩ :=
          planOccurrence_application_split_context planOccurrence
        obtain ⟨argumentsTyped, argumentsSafe⟩ :=
          applicationArgumentsSafe constructor rendered preimage targetSafe
        have childrenFree :
            rhoStaticFrameListBinderFree children.abstractPatterns = true := by
          simpa [CostStaticRegionPlan.abstractPattern,
            rhoStaticFrameBinderFree] using frameFree
        have leafSafe :=
          CostStaticArgumentPlan.semanticLeafSafeAt_quoteLocal
            (name := name) (planAvailable := planAvailable)
            children childrenFree collectionDeterministic globalTable values
              entriesSubset argumentsSafe decomposition nested parameter
                nameEquality childrenPreserve
        rw [contextEquality]
        simpa [rhoStaticContextReflectiveAvailable] using leafSafe
    | lambda bodyPlan =>
        simp [CostStaticRegionPlan.abstractPattern,
          rhoStaticFrameBinderFree] at frameFree
    | multiLambda bodyPlan =>
        simp [CostStaticRegionPlan.abstractPattern,
          rhoStaticFrameBinderFree] at frameFree
    | collection choice selected children =>
        obtain ⟨before, child, after, inner, decomposition, contextEquality,
            ⟨nested⟩⟩ :=
          planOccurrence_collection_split_context planOccurrence
        obtain ⟨elementsTyped, elementsSafe⟩ :=
          collectionElementsSafe collectionDeterministic choice selected
            targetSafe
        have childrenFree :
            rhoStaticFrameListBinderFree children.abstractPatterns = true := by
          simpa [CostStaticRegionPlan.abstractPattern,
            rhoStaticFrameBinderFree] using frameFree
        have leafSafe :=
          CostStaticElementPlan.semanticLeafSafeAt_quoteLocal
            (name := name) (planAvailable := planAvailable)
            children childrenFree collectionDeterministic globalTable values
              entriesSubset elementsSafe decomposition nested parameter
                nameEquality childrenPreserve
        rw [contextEquality]
        simpa [rhoStaticContextReflectiveAvailable] using leafSafe
    | boundaryCollection currentRejected oppositeChoice oppositeSelected
        certified certifies =>
        cases planOccurrence with
        | boundaryCollection =>
            have localMembership : certified.typed ∈
                [certified.typed] := List.mem_cons_self
            have globalMembership : certified.typed ∈ globalTable.entries :=
              entriesSubset localMembership
            simpa [rhoStaticContextReflectiveAvailable] using
              boundaryLeafSemanticSafeAt certified.typed globalMembership
                certified.content_eq certified.targetType_eq targetSafe
                  childrenPreserve parameter nameEquality
  termination_by 3 * sizeOf pattern + 2

  /-- Ordered-argument companion to
  `CostStaticRegionPlan.semanticLeafSafeAt_quoteLocal`. -/
  theorem CostStaticArgumentPlan.semanticLeafSafeAt_quoteLocal
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
      {wireName : String} {before arguments : List Pattern}
      {parameters : List TermParam}
      (plan : CostStaticArgumentPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer wireName before arguments
          parameters)
      (frameFree : rhoStaticFrameListBinderFree plan.abstractPatterns = true)
      (collectionDeterministic :
        WellSorted.CollectionChoiceDeterministic
          rhoCIGSLT.costWholeLanguage)
      {globalOccurrences : List CostRegionOccurrence}
      (globalTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
        globalOccurrences)
      (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
        globalTable)
      (entriesSubset : plan.boundaryTable.entries ⊆ globalTable.entries)
      {argumentsTyped : WellSorted.ArgumentsHaveTypes
        rhoCIGSLT.costWholeLanguage targetFree targetBound arguments
          (parameters.map (mapTermParam (color.symbols rhoCIGSLT)))}
      {support : ContextSupport.Support} {reflectiveAvailable : List TypeExpr}
      {binderImage : TypeExpr → TypeExpr}
      (argumentsSafe : argumentsTyped.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile support reflectiveAvailable
          binderImage)
      {selectedBefore selectedAfter : List
        (CostStaticPlanDecoration rhoCIGSLT)}
      {selectedDecoration : CostStaticPlanDecoration rhoCIGSLT}
      {name : String} {inner : OneHoleContext}
      {planAvailable : List TypeExpr}
      (decomposition : plan.decorations =
        selectedBefore ++ selectedDecoration :: selectedAfter)
      (nested : CostStaticPlanAbstractOccurrence rhoCIGSLT name
        selectedDecoration inner planAvailable)
      {root : Pattern}
      (parameter : CostStaticParameterOccurrence rhoCIGSLT color targetFree
        globalTable values root)
      (nameEquality : parameter.fvarOccurrence.name = name)
      (childrenPreserve : CostStaticBoundaryChildReflectiveSupportPreserving
        globalTable values support binderImage) :
      CostStaticSemanticLeafSafeAt support
        (rhoStaticContextReflectiveAvailable reflectiveAvailable inner)
          binderImage parameter := by
    cases plan with
    | nil => simp [CostStaticArgumentPlan.decorations] at decomposition
    | cons representation parameterType head tail =>
        obtain ⟨_, _, headSafe, tailSafe⟩ :=
          argumentsSafeAt_cons_map (source := rhoCIGSLT) (color := color)
            parameterType argumentsSafe
        have freeParts :
            rhoStaticFrameBinderFree head.abstractPattern = true ∧
              rhoStaticFrameListBinderFree tail.abstractPatterns = true := by
          simpa [CostStaticArgumentPlan.abstractPatterns,
            rhoStaticFrameListBinderFree] using frameFree
        cases selectedBefore with
        | nil =>
            simp only [CostStaticArgumentPlan.decorations,
              List.nil_append, List.cons.injEq] at decomposition
            let headOccurrence :=
              CostStaticPlanAbstractOccurrence.reindexDecoration
                decomposition.1.symm nested
            have headSubset : head.boundaryTable.entries ⊆
                globalTable.entries := by
              intro boundary membership
              apply entriesSubset
              change boundary ∈
                (TypedCostRegionBoundaryTable.append head.boundaryTable
                  tail.boundaryTable).entries
              rw [TypedCostRegionBoundaryTable.entries_append]
              exact List.mem_append_left _ membership
            exact CostStaticRegionPlan.semanticLeafSafeAt_quoteLocal
              (name := name) (planAvailable := planAvailable)
              head freeParts.1 collectionDeterministic globalTable values
                headSubset headSafe parameter headOccurrence nameEquality
                  childrenPreserve
        | cons skipped selectedBefore =>
            simp only [CostStaticArgumentPlan.decorations,
              List.cons_append, List.cons.injEq] at decomposition
            have tailSubset : tail.boundaryTable.entries ⊆
                globalTable.entries := by
              intro boundary membership
              apply entriesSubset
              change boundary ∈
                (TypedCostRegionBoundaryTable.append head.boundaryTable
                  tail.boundaryTable).entries
              rw [TypedCostRegionBoundaryTable.entries_append]
              exact List.mem_append_right _ membership
            exact CostStaticArgumentPlan.semanticLeafSafeAt_quoteLocal
              (name := name) (planAvailable := planAvailable)
              tail freeParts.2 collectionDeterministic globalTable values
                tailSubset tailSafe decomposition.2 nested parameter
                  nameEquality childrenPreserve
  termination_by 3 * sizeOf arguments + 1

  /-- Homogeneous-collection companion to
  `CostStaticRegionPlan.semanticLeafSafeAt_quoteLocal`. -/
  theorem CostStaticElementPlan.semanticLeafSafeAt_quoteLocal
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
      {collectionType : CollType} {before elements : List Pattern}
      {rest : Option String} {sourceElementType : TypeExpr}
      (plan : CostStaticElementPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer collectionType before
          elements rest sourceElementType)
      (frameFree : rhoStaticFrameListBinderFree plan.abstractPatterns = true)
      (collectionDeterministic :
        WellSorted.CollectionChoiceDeterministic
          rhoCIGSLT.costWholeLanguage)
      {globalOccurrences : List CostRegionOccurrence}
      (globalTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
        globalOccurrences)
      (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
        globalTable)
      (entriesSubset : plan.boundaryTable.entries ⊆ globalTable.entries)
      {elementsTyped : WellSorted.ElementsHaveType
        rhoCIGSLT.costWholeLanguage targetFree targetBound elements
          (mapTypeExpr (color.symbols rhoCIGSLT) sourceElementType)}
      {support : ContextSupport.Support} {reflectiveAvailable : List TypeExpr}
      {binderImage : TypeExpr → TypeExpr}
      (elementsSafe : elementsTyped.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile support reflectiveAvailable
          binderImage)
      {selectedBefore selectedAfter : List
        (CostStaticPlanDecoration rhoCIGSLT)}
      {selectedDecoration : CostStaticPlanDecoration rhoCIGSLT}
      {name : String} {inner : OneHoleContext}
      {planAvailable : List TypeExpr}
      (decomposition : plan.decorations =
        selectedBefore ++ selectedDecoration :: selectedAfter)
      (nested : CostStaticPlanAbstractOccurrence rhoCIGSLT name
        selectedDecoration inner planAvailable)
      {root : Pattern}
      (parameter : CostStaticParameterOccurrence rhoCIGSLT color targetFree
        globalTable values root)
      (nameEquality : parameter.fvarOccurrence.name = name)
      (childrenPreserve : CostStaticBoundaryChildReflectiveSupportPreserving
        globalTable values support binderImage) :
      CostStaticSemanticLeafSafeAt support
        (rhoStaticContextReflectiveAvailable reflectiveAvailable inner)
          binderImage parameter := by
    cases plan with
    | nil => simp [CostStaticElementPlan.decorations] at decomposition
    | cons head tail =>
        obtain ⟨_, _, headSafe, tailSafe⟩ :=
          elementsSafeAt_cons (source := rhoCIGSLT) elementsSafe
        have freeParts :
            rhoStaticFrameBinderFree head.abstractPattern = true ∧
              rhoStaticFrameListBinderFree tail.abstractPatterns = true := by
          simpa [CostStaticElementPlan.abstractPatterns,
            rhoStaticFrameListBinderFree] using frameFree
        cases selectedBefore with
        | nil =>
            simp only [CostStaticElementPlan.decorations,
              List.nil_append, List.cons.injEq] at decomposition
            let headOccurrence :=
              CostStaticPlanAbstractOccurrence.reindexDecoration
                decomposition.1.symm nested
            have headSubset : head.boundaryTable.entries ⊆
                globalTable.entries := by
              intro boundary membership
              apply entriesSubset
              change boundary ∈
                (TypedCostRegionBoundaryTable.append head.boundaryTable
                  tail.boundaryTable).entries
              rw [TypedCostRegionBoundaryTable.entries_append]
              exact List.mem_append_left _ membership
            exact CostStaticRegionPlan.semanticLeafSafeAt_quoteLocal
              (name := name) (planAvailable := planAvailable)
              head freeParts.1 collectionDeterministic globalTable values
                headSubset headSafe parameter headOccurrence nameEquality
                  childrenPreserve
        | cons skipped selectedBefore =>
            simp only [CostStaticElementPlan.decorations,
              List.cons_append, List.cons.injEq] at decomposition
            have tailSubset : tail.boundaryTable.entries ⊆
                globalTable.entries := by
              intro boundary membership
              apply entriesSubset
              change boundary ∈
                (TypedCostRegionBoundaryTable.append head.boundaryTable
                  tail.boundaryTable).entries
              rw [TypedCostRegionBoundaryTable.entries_append]
              exact List.mem_append_right _ membership
            exact CostStaticElementPlan.semanticLeafSafeAt_quoteLocal
              (name := name) (planAvailable := planAvailable)
              tail freeParts.2 collectionDeterministic globalTable values
                tailSubset tailSafe decomposition.2 nested parameter
                  nameEquality childrenPreserve
  termination_by 3 * sizeOf elements + 1
  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega
end

/-- The normalized semantic atom at an executable inventory position is safe
at the exact quote-local availability of that position's authored zipper.
No availability is selected by choice in this theorem. -/
theorem occurrenceAtomSafeAt_quoteLocal
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (support : ContextSupport.Support) (available : List TypeExpr)
    (binderImage : TypeExpr → TypeExpr)
    (childrenPreserve : CostStaticBoundaryChildReflectiveSupportPreserving
      node.boundaryTable values support binderImage)
    (inputSafe : node.term.2.1.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support available binderImage)
    (position : inventory.Occurrence) :
    (inventory.occurrenceAtom position).normalTyped.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support
        (rhoStaticContextReflectiveAvailable available
          (planDecorationOccurrenceAt node inventory position).context)
        binderImage := by
  let positional := planDecorationOccurrenceAt node inventory position
  obtain ⟨packed⟩ := nonempty_planOccurrenceAt node inventory position
  rcases packed with ⟨planAvailable, planOccurrence⟩
  let parameter := inventory.occurrenceAt position
  have nameEquality : parameter.fvarOccurrence.name = positional.name :=
    (planDecorationOccurrenceAt_name node inventory position).symm
  have planFree : rhoStaticFrameBinderFree node.plan.abstractPattern = true :=
    CostStaticRegionPlan.rhoAbstractPattern_binderFree_of_base node.plan
      ⟨node.sourceSort.1, rfl⟩
  have semanticSafe :=
    CostStaticRegionPlan.semanticLeafSafeAt_quoteLocal node.plan planFree
      rho_costWholeLanguage_collectionChoiceDeterministic node.boundaryTable
        values (fun _ membership => membership) inputSafe parameter
          planOccurrence.1 nameEquality childrenPreserve
  exact semanticSafe.atomSafe

/-- The finite support quotient whose occurrence availability is definitionally
the authored zipper's quote-local availability.  This is the exact profile
consumed by the canonical ancestry bridge. -/
noncomputable def quoteLocalOccurrenceSupportProfile
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (support : ContextSupport.Support) (available : List TypeExpr)
    (binderImage : TypeExpr → TypeExpr)
    (childrenPreserve : CostStaticBoundaryChildReflectiveSupportPreserving
      node.boundaryTable values support binderImage)
    (inputSafe : node.term.2.1.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support available binderImage) :
    CostStaticOccurrenceSupportProfile
      (CostStaticAtomEnvironment.ofInventory inventory) support binderImage := by
  let occurrenceAvailable : inventory.Occurrence → List TypeExpr :=
    fun position => rhoStaticContextReflectiveAvailable available
      (planDecorationOccurrenceAt node inventory position).context
  let classSupport : OccurrenceClassSupport
      (CostStaticAtomEnvironment.ofInventory inventory).occurrenceSlot :=
    OccurrenceClassSupport.ofSurjective occurrenceAvailable
      (CostStaticAtomEnvironment.ofInventory_occurrenceSlot_surjective
        inventory)
  exact
    { classSupport := classSupport
      occurrenceSafe := by
        intro position
        exact occurrenceAtomSafeAt_quoteLocal node values inventory support
          available binderImage childrenPreserve inputSafe position }

@[simp]
theorem quoteLocalOccurrenceSupportProfile_occurrenceAvailable
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (support : ContextSupport.Support) (available : List TypeExpr)
    (binderImage : TypeExpr → TypeExpr)
    (childrenPreserve : CostStaticBoundaryChildReflectiveSupportPreserving
      node.boundaryTable values support binderImage)
    (inputSafe : node.term.2.1.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support available binderImage)
    (position : inventory.Occurrence) :
    (quoteLocalOccurrenceSupportProfile node values inventory support available
      binderImage childrenPreserve inputSafe).classSupport.occurrenceAvailable
        position =
      rhoStaticContextReflectiveAvailable available
        (planDecorationOccurrenceAt node inventory position).context := rfl

/-! ## Reconstructing support safety from exact occurrence bounds -/

/-- Every free-variable occurrence of a pattern has enough quote-local
availability for the support assigned to its spelling. -/
def RhoStaticOccurrenceSupportBounded (support : ContextSupport.Support)
    (available : List TypeExpr) (pattern : Pattern) : Prop :=
  ∀ occurrence : CostStaticFVarOccurrence pattern,
    support occurrence.name <:+
      rhoStaticContextReflectiveAvailable available occurrence.context

/-- List-indexed companion to `RhoStaticOccurrenceSupportBounded`. -/
def RhoStaticListOccurrenceSupportBounded (support : ContextSupport.Support)
    (available : List TypeExpr) (patterns : List Pattern) : Prop :=
  ∀ occurrence : CostStaticFVarListOccurrence patterns,
    support occurrence.occurrence.name <:+
      rhoStaticContextReflectiveAvailable available
        occurrence.occurrence.context

@[simp]
theorem rhoCIGSLT_reflection_eq_rhoReflectionProfile :
    rhoCIGSLT.reflection.1 = rhoReflectionProfile := rfl

theorem rhoStaticListOccurrenceSupportBounded_of_apply
    (support : ContextSupport.Support) (available : List TypeExpr)
    (constructor : String) (arguments : List Pattern)
    (bounded : RhoStaticOccurrenceSupportBounded support available
      (.apply constructor arguments)) :
    RhoStaticListOccurrenceSupportBounded support
      (if ReflectiveContextSupport.isQuoteConstructor rhoReflectionProfile
          constructor then [] else available) arguments := by
  intro occurrence
  have selected := bounded (occurrence.inApply constructor)
  change support occurrence.occurrence.name <:+
    rhoStaticContextReflectiveAvailable
      (if ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.reflection.1
        constructor then [] else available) occurrence.occurrence.context at selected
  rw [rhoCIGSLT_reflection_eq_rhoReflectionProfile] at selected
  exact selected

theorem rhoStaticListOccurrenceSupportBounded_of_collection
    (support : ContextSupport.Support) (available : List TypeExpr)
    (collectionType : CollType) (elements : List Pattern)
    (rest : Option String)
    (bounded : RhoStaticOccurrenceSupportBounded support available
      (.collection collectionType elements rest)) :
    RhoStaticListOccurrenceSupportBounded support available elements := by
  intro occurrence
  have selected := bounded (occurrence.inCollection collectionType rest)
  simpa [RhoStaticOccurrenceSupportBounded,
    RhoStaticListOccurrenceSupportBounded,
    CostStaticFVarListOccurrence.inCollection,
    rhoStaticContextReflectiveAvailable] using selected

theorem rhoStaticOccurrenceSupportBounded_head
    (support : ContextSupport.Support) (available : List TypeExpr)
    (head : Pattern) (tail : List Pattern)
    (bounded : RhoStaticListOccurrenceSupportBounded support available
      (head :: tail)) :
    RhoStaticOccurrenceSupportBounded support available head := by
  intro occurrence
  let selected : CostStaticFVarListOccurrence (head :: tail) :=
    { position := ⟨0, by simp⟩
      occurrence := occurrence }
  exact bounded selected

theorem rhoStaticListOccurrenceSupportBounded_tail
    (support : ContextSupport.Support) (available : List TypeExpr)
    (head : Pattern) (tail : List Pattern)
    (bounded : RhoStaticListOccurrenceSupportBounded support available
      (head :: tail)) :
    RhoStaticListOccurrenceSupportBounded support available tail := by
  intro occurrence
  let selected : CostStaticFVarListOccurrence (head :: tail) :=
    { position := Fin.succ occurrence.position
      occurrence := occurrence.occurrence }
  exact bounded selected

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
mutual
  /-- Binder-free rho syntax is support-safe whenever every exact occurrence
  has the suffix demanded at its own quote-local zipper. -/
  theorem WellSorted.HasType.rhoStaticFrame_supportSafe_of_occurrences
      {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr}
      (typed : WellSorted.HasType rhoCalc free bound pattern type)
      {support : ContextSupport.Support} {available : List TypeExpr}
      {binderImage : TypeExpr → TypeExpr}
      (frameFree : rhoStaticFrameBinderFree pattern = true)
      (bounded : RhoStaticOccurrenceSupportBounded support available pattern) :
      typed.ReflectiveSupportSafeAt rhoReflectionProfile support available
        binderImage := by
    cases typed with
    | bvar lookup => exact .bvar lookup available
    | @fvar bound name type lookup =>
        have suffix := bounded
          ({ name := name
             context := .hole
             selected := Selects.here } : CostStaticFVarOccurrence (.fvar name))
        exact .fvar lookup available (by
          exact List.suffix_iff_exists_eq_append.mp
            (by simpa [rhoStaticContextReflectiveAvailable] using suffix))
    | @constructor bound rule arguments membership notBare argumentsTyped =>
        have argumentsFree : rhoStaticFrameListBinderFree arguments = true := by
          simpa [rhoStaticFrameBinderFree] using frameFree
        by_cases quoted : ReflectiveContextSupport.isQuoteConstructor
            rhoReflectionProfile rule.label = true
        · have argumentsBounded :=
            rhoStaticListOccurrenceSupportBounded_of_apply support available
              rule.label arguments bounded
          have argumentsSafe :=
            WellSorted.ArgumentsHaveTypes.rhoStaticFrame_supportSafe_of_occurrences
              (binderImage := binderImage) argumentsTyped argumentsFree
                (by simpa [quoted] using
                argumentsBounded)
          exact .constructorQuote (membership := membership)
            (notBare := notBare) quoted argumentsSafe
        · have ordinary : ReflectiveContextSupport.isQuoteConstructor
              rhoReflectionProfile rule.label = false :=
            Bool.eq_false_of_not_eq_true quoted
          have argumentsBounded :=
            rhoStaticListOccurrenceSupportBounded_of_apply support available
              rule.label arguments bounded
          have argumentsSafe :=
            WellSorted.ArgumentsHaveTypes.rhoStaticFrame_supportSafe_of_occurrences
              (binderImage := binderImage) argumentsTyped argumentsFree
                (by simpa [ordinary] using
                argumentsBounded)
          exact .constructorOrdinary (membership := membership)
            (notBare := notBare) ordinary argumentsSafe
    | lambda bodyTyped =>
        simp [rhoStaticFrameBinderFree] at frameFree
    | multiLambda bodyTyped =>
        simp [rhoStaticFrameBinderFree] at frameFree
    | subst bodyTyped replacementTyped =>
        simp [rhoStaticFrameBinderFree] at frameFree
    | @collection bound collectionType elements rest elementType elementsTyped =>
        have elementsFree : rhoStaticFrameListBinderFree elements = true := by
          simpa [rhoStaticFrameBinderFree] using frameFree
        have elementsBounded :=
          rhoStaticListOccurrenceSupportBounded_of_collection support available
            collectionType elements rest bounded
        exact .collection
          (WellSorted.ElementsHaveType.rhoStaticFrame_supportSafe_of_occurrences
            elementsTyped elementsFree elementsBounded)
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType membership parameterShape elementsTyped =>
        have elementsFree : rhoStaticFrameListBinderFree elements = true := by
          simpa [rhoStaticFrameBinderFree] using frameFree
        have elementsBounded :=
          rhoStaticListOccurrenceSupportBounded_of_collection support available
            collectionType elements rest bounded
        exact .collectionConstructor (membership := membership)
          (parameterShape := parameterShape)
          (WellSorted.ElementsHaveType.rhoStaticFrame_supportSafe_of_occurrences
            elementsTyped elementsFree elementsBounded)
  termination_by 3 * sizeOf pattern + 2

  /-- Ordered-argument companion to
  `WellSorted.HasType.rhoStaticFrame_supportSafe_of_occurrences`. -/
  theorem WellSorted.ArgumentsHaveTypes.rhoStaticFrame_supportSafe_of_occurrences
      {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      (typed : WellSorted.ArgumentsHaveTypes rhoCalc free bound arguments
        parameters)
      {support : ContextSupport.Support} {available : List TypeExpr}
      {binderImage : TypeExpr → TypeExpr}
      (frameFree : rhoStaticFrameListBinderFree arguments = true)
      (bounded : RhoStaticListOccurrenceSupportBounded support available
        arguments) :
      typed.ReflectiveSupportSafeAt rhoReflectionProfile support available
        binderImage := by
    cases typed with
    | nil => exact .nil bound available
    | @cons bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped =>
        have freeParts : rhoStaticFrameBinderFree argument = true ∧
            rhoStaticFrameListBinderFree arguments = true := by
          simpa [rhoStaticFrameListBinderFree] using frameFree
        exact .cons (representation := representation)
          (parameterType := parameterType)
          (WellSorted.HasType.rhoStaticFrame_supportSafe_of_occurrences
            argumentTyped freeParts.1
              (rhoStaticOccurrenceSupportBounded_head support available
                argument arguments bounded))
          (WellSorted.ArgumentsHaveTypes.rhoStaticFrame_supportSafe_of_occurrences
            argumentsTyped freeParts.2
              (rhoStaticListOccurrenceSupportBounded_tail support available
                argument arguments bounded))
  termination_by 3 * sizeOf arguments + 1
  /-- Homogeneous-element companion to
  `WellSorted.HasType.rhoStaticFrame_supportSafe_of_occurrences`. -/
  theorem WellSorted.ElementsHaveType.rhoStaticFrame_supportSafe_of_occurrences
      {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      (typed : WellSorted.ElementsHaveType rhoCalc free bound elements
        elementType)
      {support : ContextSupport.Support} {available : List TypeExpr}
      {binderImage : TypeExpr → TypeExpr}
      (frameFree : rhoStaticFrameListBinderFree elements = true)
      (bounded : RhoStaticListOccurrenceSupportBounded support available
        elements) :
      typed.ReflectiveSupportSafeAt rhoReflectionProfile support available
        binderImage := by
    cases typed with
    | nil => exact .nil bound elementType available
    | @cons bound element elements elementType elementTyped elementsTyped =>
        have freeParts : rhoStaticFrameBinderFree element = true ∧
            rhoStaticFrameListBinderFree elements = true := by
          simpa [rhoStaticFrameListBinderFree] using frameFree
        exact .cons
          (WellSorted.HasType.rhoStaticFrame_supportSafe_of_occurrences
            elementTyped freeParts.1
              (rhoStaticOccurrenceSupportBounded_head support available
                element elements bounded))
          (WellSorted.ElementsHaveType.rhoStaticFrame_supportSafe_of_occurrences
            elementsTyped freeParts.2
              (rhoStaticListOccurrenceSupportBounded_tail support available
                element elements bounded))
  termination_by 3 * sizeOf elements + 1
  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega
end

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
mutual
  /-- Constructor-facing support safety exposes the exact suffix at every
  positional occurrence of a binder-free rho static frame. -/
  theorem WellSorted.HasType.ReflectiveSupportSafeAt.rhoStaticFrame_supportBounded
      {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr}
      {typed : WellSorted.HasType rhoCalc free bound pattern type}
      {support : ContextSupport.Support} {available : List TypeExpr}
      {binderImage : TypeExpr → TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt rhoReflectionProfile support
        available binderImage)
      (frameFree : rhoStaticFrameBinderFree pattern = true) :
      RhoStaticOccurrenceSupportBounded support available pattern := by
    intro occurrence
    cases safe with
    | bvar => cases occurrence.selected
    | @fvar bound name type lookup currentAvailable binderImage shape =>
        simpa [rhoStaticContextReflectiveAvailable] using
          List.suffix_iff_exists_eq_append.mpr shape
    | @constructorQuote bound rule arguments membership notBare argumentsTyped
        currentAvailable binderImage quoted argumentsSafe =>
        have argumentsFree : rhoStaticFrameListBinderFree arguments = true := by
          simpa [rhoStaticFrameBinderFree] using frameFree
        have argumentsBounded :=
          argumentsSafe.rhoStaticFrame_supportBounded argumentsFree
        let view := Classical.choice
          (CostApplyOccurrenceView.nonempty rule.label arguments occurrence)
        let position : Fin arguments.length := ⟨view.before.length, by
          have lengths := congrArg List.length view.arguments_eq
          simp only [List.length_append, List.length_cons] at lengths
          omega⟩
        have argumentEquality : arguments.get position = view.argument :=
          List.getElem_of_append view.arguments_eq rfl
        let nested : CostStaticFVarListOccurrence arguments :=
          { position := position
            occurrence :=
              { name := occurrence.name
                context := view.inner
                selected := argumentEquality.symm ▸ view.selected } }
        have suffix := argumentsBounded nested
        rw [view.context_eq]
        simpa [rhoStaticContextReflectiveAvailable, quoted] using suffix
    | @constructorOrdinary bound rule arguments membership notBare
        argumentsTyped currentAvailable binderImage ordinary argumentsSafe =>
        have argumentsFree : rhoStaticFrameListBinderFree arguments = true := by
          simpa [rhoStaticFrameBinderFree] using frameFree
        have argumentsBounded :=
          argumentsSafe.rhoStaticFrame_supportBounded argumentsFree
        let view := Classical.choice
          (CostApplyOccurrenceView.nonempty rule.label arguments occurrence)
        let position : Fin arguments.length := ⟨view.before.length, by
          have lengths := congrArg List.length view.arguments_eq
          simp only [List.length_append, List.length_cons] at lengths
          omega⟩
        have argumentEquality : arguments.get position = view.argument :=
          List.getElem_of_append view.arguments_eq rfl
        let nested : CostStaticFVarListOccurrence arguments :=
          { position := position
            occurrence :=
              { name := occurrence.name
                context := view.inner
                selected := argumentEquality.symm ▸ view.selected } }
        have suffix := argumentsBounded nested
        rw [view.context_eq]
        simpa [rhoStaticContextReflectiveAvailable, ordinary] using suffix
    | lambda => simp [rhoStaticFrameBinderFree] at frameFree
    | multiLambda => simp [rhoStaticFrameBinderFree] at frameFree
    | subst => simp [rhoStaticFrameBinderFree] at frameFree
    | @collection bound collectionType elements rest elementType elementsTyped
        currentAvailable binderImage elementsSafe =>
        have elementsFree : rhoStaticFrameListBinderFree elements = true := by
          simpa [rhoStaticFrameBinderFree] using frameFree
        have elementsBounded :=
          elementsSafe.rhoStaticFrame_supportBounded elementsFree
        let view := collectionOccurrenceView collectionType elements rest
          occurrence
        let position : Fin elements.length := ⟨view.before.length, by
          have lengths := congrArg List.length view.patterns_eq
          simp only [List.length_append, List.length_cons] at lengths
          omega⟩
        have elementEquality : elements.get position = view.member :=
          List.getElem_of_append view.patterns_eq rfl
        let nested : CostStaticFVarListOccurrence elements :=
          { position := position
            occurrence :=
              { name := occurrence.name
                context := view.inner
                selected := elementEquality.symm ▸ view.selected } }
        have suffix := elementsBounded nested
        rw [view.context_eq]
        simpa [rhoStaticContextReflectiveAvailable] using suffix
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType membership parameterShape elementsTyped
        currentAvailable binderImage elementsSafe =>
        have elementsFree : rhoStaticFrameListBinderFree elements = true := by
          simpa [rhoStaticFrameBinderFree] using frameFree
        have elementsBounded :=
          elementsSafe.rhoStaticFrame_supportBounded elementsFree
        let view := collectionOccurrenceView collectionType elements rest
          occurrence
        let position : Fin elements.length := ⟨view.before.length, by
          have lengths := congrArg List.length view.patterns_eq
          simp only [List.length_append, List.length_cons] at lengths
          omega⟩
        have elementEquality : elements.get position = view.member :=
          List.getElem_of_append view.patterns_eq rfl
        let nested : CostStaticFVarListOccurrence elements :=
          { position := position
            occurrence :=
              { name := occurrence.name
                context := view.inner
                selected := elementEquality.symm ▸ view.selected } }
        have suffix := elementsBounded nested
        rw [view.context_eq]
        simpa [rhoStaticContextReflectiveAvailable] using suffix
  termination_by 3 * sizeOf pattern + 2

  theorem WellSorted.ArgumentsHaveTypes.ReflectiveSupportSafeAt.rhoStaticFrame_supportBounded
      {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      {typed : WellSorted.ArgumentsHaveTypes rhoCalc free bound arguments
        parameters}
      {support : ContextSupport.Support} {available : List TypeExpr}
      {binderImage : TypeExpr → TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt rhoReflectionProfile support
        available binderImage)
      (frameFree : rhoStaticFrameListBinderFree arguments = true) :
      RhoStaticListOccurrenceSupportBounded support available arguments := by
    intro occurrence
    cases safe with
    | nil => exact Fin.elim0 occurrence.position
    | @cons bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped
        currentAvailable binderImage argumentSafe argumentsSafe =>
        have freeParts : rhoStaticFrameBinderFree argument = true ∧
            rhoStaticFrameListBinderFree arguments = true := by
          simpa [rhoStaticFrameListBinderFree] using frameFree
        have headBounded :=
          argumentSafe.rhoStaticFrame_supportBounded freeParts.1
        have tailBounded :=
          argumentsSafe.rhoStaticFrame_supportBounded freeParts.2
        rcases occurrence with ⟨position, nested⟩
        cases position using Fin.cases with
        | zero => exact headBounded nested
        | succ tailPosition =>
            exact tailBounded ⟨tailPosition, nested⟩
  termination_by 3 * sizeOf arguments + 1

  theorem WellSorted.ElementsHaveType.ReflectiveSupportSafeAt.rhoStaticFrame_supportBounded
      {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      {typed : WellSorted.ElementsHaveType rhoCalc free bound elements
        elementType}
      {support : ContextSupport.Support} {available : List TypeExpr}
      {binderImage : TypeExpr → TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt rhoReflectionProfile support
        available binderImage)
      (frameFree : rhoStaticFrameListBinderFree elements = true) :
      RhoStaticListOccurrenceSupportBounded support available elements := by
    intro occurrence
    cases safe with
    | nil => exact Fin.elim0 occurrence.position
    | @cons bound element elements elementType elementTyped elementsTyped
        currentAvailable binderImage elementSafe elementsSafe =>
        have freeParts : rhoStaticFrameBinderFree element = true ∧
            rhoStaticFrameListBinderFree elements = true := by
          simpa [rhoStaticFrameListBinderFree] using frameFree
        have headBounded :=
          elementSafe.rhoStaticFrame_supportBounded freeParts.1
        have tailBounded :=
          elementsSafe.rhoStaticFrame_supportBounded freeParts.2
        rcases occurrence with ⟨position, nested⟩
        cases position using Fin.cases with
        | zero => exact headBounded nested
        | succ tailPosition =>
            exact tailBounded ⟨tailPosition, nested⟩
  termination_by 3 * sizeOf elements + 1

  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega
end

/-! ## Quote-local availability through canonical occurrence ancestry -/

/-- Computing reflective availability through a composite zipper is the same
as computing it through the outer zipper and then the inner zipper. -/
theorem rhoStaticContextReflectiveAvailable_comp
    (ambient : List TypeExpr) (outer inner : OneHoleContext) :
    rhoStaticContextReflectiveAvailable ambient (outer.comp inner) =
      rhoStaticContextReflectiveAvailable
        (rhoStaticContextReflectiveAvailable ambient outer) inner := by
  induction outer generalizing ambient with
  | hole => rfl
  | apply constructor before outer after inductionHypothesis =>
      exact inductionHypothesis _
  | lambda binder outer inductionHypothesis =>
      exact inductionHypothesis _
  | multiLambda arity binders outer inductionHypothesis =>
      exact inductionHypothesis _
  | substBody outer replacement inductionHypothesis =>
      exact inductionHypothesis _
  | substReplacement body outer inductionHypothesis =>
      exact inductionHypothesis _
  | collection collectionType before outer after rest inductionHypothesis =>
      exact inductionHypothesis _

/-- Once an authored quote has sealed availability, every deeper binder-free
zipper remains sealed. -/
@[simp]
theorem rhoStaticContextReflectiveAvailable_nil
    (context : OneHoleContext) :
    rhoStaticContextReflectiveAvailable [] context = [] := by
  induction context with
  | hole => rfl
  | apply constructor before inner after inductionHypothesis =>
      simpa [rhoStaticContextReflectiveAvailable] using inductionHypothesis
  | lambda binder inner inductionHypothesis =>
      exact inductionHypothesis
  | multiLambda arity binders inner inductionHypothesis =>
      exact inductionHypothesis
  | substBody inner replacement inductionHypothesis =>
      exact inductionHypothesis
  | substReplacement body inner inductionHypothesis =>
      exact inductionHypothesis
  | collection collectionType before inner after rest inductionHypothesis =>
      exact inductionHypothesis

/-- Casting the root pattern of an occurrence does not change its zipper-local
availability. -/
theorem rhoStaticContextReflectiveAvailable_castRoot
    {left right : Pattern} (equal : left = right)
    (occurrence : CostStaticFVarOccurrence left) (ambient : List TypeExpr) :
    rhoStaticContextReflectiveAvailable ambient
        (CostStaticFVarOccurrence.castRoot equal occurrence).context =
      rhoStaticContextReflectiveAvailable ambient occurrence.context := by
  cases equal
  rfl

/-- Casting the surrounding list of an occurrence does not change its nested
zipper-local availability. -/
theorem rhoStaticContextReflectiveAvailable_castPatterns
    {left right : List Pattern} (equal : left = right)
    (occurrence : CostStaticFVarListOccurrence left)
    (ambient : List TypeExpr) :
    rhoStaticContextReflectiveAvailable ambient
        (CostStaticFVarListOccurrence.castPatterns equal occurrence
          ).occurrence.context =
      rhoStaticContextReflectiveAvailable ambient
        occurrence.occurrence.context := by
  cases equal
  rfl

/-- Removing a collection wrapper while retaining its exact member does not
change reflective availability. -/
@[simp]
theorem rhoStaticContextReflectiveAvailable_inCollection
    (ambient : List TypeExpr) (collectionType : CollType)
    (rest : Option String) {patterns : List Pattern}
    (occurrence : CostStaticFVarListOccurrence patterns) :
    rhoStaticContextReflectiveAvailable ambient
        (occurrence.inCollection collectionType rest).context =
      rhoStaticContextReflectiveAvailable ambient
        occurrence.occurrence.context := by
  rfl

/-- Entering an application resets availability exactly when that application
is the rho quote constructor. -/
@[simp]
theorem rhoStaticContextReflectiveAvailable_inApply
    (ambient : List TypeExpr) (constructor : String)
    {patterns : List Pattern}
    (occurrence : CostStaticFVarListOccurrence patterns) :
    rhoStaticContextReflectiveAvailable ambient
        (occurrence.inApply constructor).context =
      rhoStaticContextReflectiveAvailable
        (if ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.reflection.1
            constructor then [] else ambient)
        occurrence.occurrence.context := by
  rfl

/-- Forgetting the sole list position preserves the nested occurrence
availability. -/
theorem rhoStaticContextReflectiveAvailable_singletonListOccurrenceRoot
    {root : Pattern} (occurrence : CostStaticFVarListOccurrence [root])
    (ambient : List TypeExpr) :
    rhoStaticContextReflectiveAvailable ambient
        (singletonListOccurrenceRoot occurrence).context =
      rhoStaticContextReflectiveAvailable ambient
        occurrence.occurrence.context := by
  rcases occurrence with ⟨position, nested⟩
  have positionValue : position.val = 0 := by
    have bound := position.isLt
    change position.val < 1 at bound
    omega
  have positionEquality : position = ⟨0, by simp⟩ :=
    Fin.ext positionValue
  subst position
  rfl

/-- Pulling an occurrence backward through a list permutation changes only
its list position, not the selected pattern's inner zipper. -/
theorem rhoStaticContextReflectiveAvailable_pullbackPerm
    {source target : List Pattern} (permutation : target.Perm source)
    (occurrence : CostStaticFVarListOccurrence target)
    (ambient : List TypeExpr) :
    rhoStaticContextReflectiveAvailable ambient
        (occurrence.pullbackPerm permutation).occurrence.context =
      rhoStaticContextReflectiveAvailable ambient
        occurrence.occurrence.context := by
  unfold CostStaticFVarListOccurrence.pullbackPerm
  dsimp only
  generalize equality :
      source.get (permutation.idxBij occurrence.position) =
        target.get occurrence.position = elementEquality
  cases elementEquality
  rfl

/-- Pulling an occurrence backward through a positional sublist changes only
its list position, not the selected pattern's inner zipper. -/
theorem rhoStaticContextReflectiveAvailable_positionalPullback
    {source target : List Pattern}
    (embedding : CostStaticFVarListOccurrence.CostPositionalSublist target
      source)
    (occurrence : CostStaticFVarListOccurrence target)
    (ambient : List TypeExpr) :
    rhoStaticContextReflectiveAvailable ambient
        (CostStaticFVarListOccurrence.CostPositionalSublist.pullback embedding
          occurrence).occurrence.context =
      rhoStaticContextReflectiveAvailable ambient
        occurrence.occurrence.context := by
  unfold CostStaticFVarListOccurrence.CostPositionalSublist.pullback
  dsimp only
  generalize equality :
      source.get
          (CostStaticFVarListOccurrence.CostPositionalSublist.sourcePosition
            embedding occurrence.position) =
        target.get occurrence.position = elementEquality
  cases elementEquality
  rfl

/-- Filter ancestry preserves the exact inner availability. -/
theorem rhoStaticContextReflectiveAvailable_filterOccurrenceSource
    (keep : Pattern → Bool) (patterns : List Pattern)
    (occurrence : CostStaticFVarListOccurrence (patterns.filter keep))
    (ambient : List TypeExpr) :
    rhoStaticContextReflectiveAvailable ambient
        (filterOccurrenceSource keep patterns occurrence).occurrence.context =
      rhoStaticContextReflectiveAvailable ambient
        occurrence.occurrence.context := by
  exact rhoStaticContextReflectiveAvailable_positionalPullback
    (CostStaticFVarListOccurrence.filterPositionalSublist keep patterns)
      occurrence ambient

/-- Stable-sort ancestry preserves the exact inner availability, including at
tied keys and duplicate values. -/
theorem rhoStaticContextReflectiveAvailable_sortPatternsByOccurrenceSource
    {Key : Type} [LinearOrder Key] (key : Pattern → Key)
    (patterns : List Pattern)
    (occurrence : CostStaticFVarListOccurrence
      (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy key patterns))
    (ambient : List TypeExpr) :
    rhoStaticContextReflectiveAvailable ambient
        (sortPatternsByOccurrenceSource key patterns occurrence
          ).occurrence.context =
      rhoStaticContextReflectiveAvailable ambient
        occurrence.occurrence.context := by
  exact rhoStaticContextReflectiveAvailable_pullbackPerm
    (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_perm key patterns)
      occurrence ambient

/-- Decomposing a position of a flattened list retains the exact inner
zipper-local availability. -/
theorem rhoStaticContextReflectiveAvailable_flatMapOccurrenceSource
    (expand : Pattern → List Pattern) (patterns : List Pattern)
    (occurrence : CostStaticFVarListOccurrence (patterns.flatMap expand))
    (ambient : List TypeExpr) :
    rhoStaticContextReflectiveAvailable ambient
        (CostStaticFVarListOccurrence.flatMapOccurrenceSource expand patterns
          occurrence).expandedOccurrence.occurrence.context =
      rhoStaticContextReflectiveAvailable ambient
        occurrence.occurrence.context := by
  induction patterns with
  | nil => exact Fin.elim0 occurrence.position
  | cons head tail inductionHypothesis =>
      rw [CostStaticFVarListOccurrence.flatMapOccurrenceSource]
      by_cases inHead : occurrence.position.val < (expand head).length
      · rw [dif_pos inHead]
        generalize equality :
            (expand head).get ⟨occurrence.position.val, inHead⟩ =
              ((head :: tail).flatMap expand).get occurrence.position =
            elementEquality
        cases elementEquality
        rfl
      · rw [dif_neg inHead]
        let tailPosition : Fin (tail.flatMap expand).length :=
          ⟨occurrence.position.val - (expand head).length, by
            have bound : occurrence.position.val <
                (expand head).length + (tail.flatMap expand).length := by
              simpa [List.flatMap] using occurrence.position.isLt
            exact Nat.sub_lt_left_of_lt_add (Nat.le_of_not_gt inHead) bound⟩
        have elementEquality :
            (tail.flatMap expand).get tailPosition =
              ((head :: tail).flatMap expand).get occurrence.position := by
          symm
          exact List.getElem_append_right
            (by simpa using Nat.le_of_not_gt inHead)
        let tailOccurrence : CostStaticFVarListOccurrence
            (tail.flatMap expand) :=
          { position := tailPosition
            occurrence := elementEquality ▸ occurrence.occurrence }
        have tailAvailable :
            rhoStaticContextReflectiveAvailable ambient
                tailOccurrence.occurrence.context =
              rhoStaticContextReflectiveAvailable ambient
                occurrence.occurrence.context := by
          unfold tailOccurrence
          dsimp only
          generalize equality :
              (tail.flatMap expand).get tailPosition =
                ((head :: tail).flatMap expand).get occurrence.position =
              castEquality
          cases castEquality
          rfl
        exact (inductionHypothesis tailOccurrence).trans tailAvailable

/-- Inverting an application occurrence to its exact selected argument
removes precisely that application's quote action. -/
theorem rhoStaticContextReflectiveAvailable_applyOccurrenceArgument
    (ambient : List TypeExpr) (constructor : String)
    (arguments : List Pattern)
    (occurrence : CostStaticFVarOccurrence (.apply constructor arguments)) :
    rhoStaticContextReflectiveAvailable
        (if ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.reflection.1
            constructor then [] else ambient)
        (applyOccurrenceArgument constructor arguments occurrence
          ).occurrence.context =
      rhoStaticContextReflectiveAvailable ambient occurrence.context := by
  unfold applyOccurrenceArgument
  let view := Classical.choice
    (CostApplyOccurrenceView.nonempty constructor arguments occurrence)
  change rhoStaticContextReflectiveAvailable
      (if ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.reflection.1
          constructor then [] else ambient) view.inner =
    rhoStaticContextReflectiveAvailable ambient occurrence.context
  rw [view.context_eq]
  rfl

/-- Inverting a collection occurrence to its exact selected member removes a
wrapper which has no reflective availability action. -/
theorem rhoStaticContextReflectiveAvailable_collectionOccurrenceMember
    (ambient : List TypeExpr) (collectionType : CollType)
    (patterns : List Pattern) (rest : Option String)
    (occurrence : CostStaticFVarOccurrence
      (.collection collectionType patterns rest)) :
    rhoStaticContextReflectiveAvailable ambient
        (collectionOccurrenceMember collectionType patterns rest occurrence
          ).occurrence.context =
      rhoStaticContextReflectiveAvailable ambient occurrence.context := by
  unfold collectionOccurrenceMember
  let view := collectionOccurrenceView collectionType patterns rest occurrence
  change rhoStaticContextReflectiveAvailable ambient view.inner =
    rhoStaticContextReflectiveAvailable ambient occurrence.context
  rw [view.context_eq]
  rfl

/-- Pulling an occurrence through one parallel splice preserves its
quote-local availability.  Nested parallel collections add only a collection
zipper; every other splice is a singleton. -/
theorem rhoStaticContextReflectiveAvailable_parallelSpliceOccurrenceSource
    (declaration : ReflectivePresentationDecl) {pattern : Pattern}
    (occurrence : CostStaticFVarListOccurrence
      (parallelSplice declaration pattern)) (ambient : List TypeExpr) :
    rhoStaticContextReflectiveAvailable ambient
        (parallelSpliceOccurrenceSource declaration occurrence).context =
      rhoStaticContextReflectiveAvailable ambient
        occurrence.occurrence.context := by
  cases pattern with
  | collection collectionType elements rest =>
      cases rest with
      | some restName =>
          have spliceEquality :
              parallelSplice declaration
                  (.collection collectionType elements (some restName)) =
                [.collection collectionType elements (some restName)] := rfl
          exact
            (rhoStaticContextReflectiveAvailable_singletonListOccurrenceRoot
              (occurrence.castPatterns spliceEquality) ambient).trans
            (rhoStaticContextReflectiveAvailable_castPatterns spliceEquality
              occurrence ambient)
      | none =>
          by_cases parallel :
              collectionType = declaration.parallelCollection
          · subst collectionType
            have spliceEquality :
                parallelSplice declaration
                    (.collection declaration.parallelCollection elements
                      none) = elements := by
              simp [parallelSplice]
            exact
              (rhoStaticContextReflectiveAvailable_inCollection ambient
                declaration.parallelCollection none
                  (occurrence.castPatterns spliceEquality)).trans
              (rhoStaticContextReflectiveAvailable_castPatterns spliceEquality
                occurrence ambient)
          · have spliceEquality :
                parallelSplice declaration
                    (.collection collectionType elements none) =
                  [.collection collectionType elements none] := by
              simp [parallelSplice, parallel]
            exact
              (rhoStaticContextReflectiveAvailable_singletonListOccurrenceRoot
                (occurrence.castPatterns spliceEquality) ambient).trans
              (rhoStaticContextReflectiveAvailable_castPatterns spliceEquality
                occurrence ambient)
  | bvar index =>
      exact rhoStaticContextReflectiveAvailable_singletonListOccurrenceRoot
        occurrence ambient
  | fvar name =>
      exact rhoStaticContextReflectiveAvailable_singletonListOccurrenceRoot
        occurrence ambient
  | apply constructor arguments =>
      exact rhoStaticContextReflectiveAvailable_singletonListOccurrenceRoot
        occurrence ambient
  | lambda binder body =>
      exact rhoStaticContextReflectiveAvailable_singletonListOccurrenceRoot
        occurrence ambient
  | multiLambda arity binders body =>
      exact rhoStaticContextReflectiveAvailable_singletonListOccurrenceRoot
        occurrence ambient
  | subst body replacement =>
      exact rhoStaticContextReflectiveAvailable_singletonListOccurrenceRoot
        occurrence ambient

/-- Pulling an occurrence through flattening of parallel splices preserves
quote-local availability. -/
theorem rhoStaticContextReflectiveAvailable_parallelFlatMapOccurrenceSource
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern)
    (occurrence : CostStaticFVarListOccurrence
      (patterns.flatMap (parallelSplice declaration)))
    (ambient : List TypeExpr) :
    rhoStaticContextReflectiveAvailable ambient
        (parallelFlatMapOccurrenceSource declaration patterns occurrence
          ).occurrence.context =
      rhoStaticContextReflectiveAvailable ambient
        occurrence.occurrence.context := by
  unfold parallelFlatMapOccurrenceSource
  let source := CostStaticFVarListOccurrence.flatMapOccurrenceSource
    (parallelSplice declaration) patterns occurrence
  exact
    (rhoStaticContextReflectiveAvailable_parallelSpliceOccurrenceSource
      declaration source.expandedOccurrence ambient).trans
    (rhoStaticContextReflectiveAvailable_flatMapOccurrenceSource
      (parallelSplice declaration) patterns occurrence ambient)

/-- The complete flatten/filter/stable-sort parallel list phase preserves
quote-local availability at every exact retained occurrence. -/
theorem rhoStaticContextReflectiveAvailable_normalizeParallelOccurrenceSource
    {Key : Type} [LinearOrder Key] (key : Pattern → Key)
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern)
    (occurrence : CostStaticFVarListOccurrence
      (normalizeParallelElementsBy key declaration patterns))
    (ambient : List TypeExpr) :
    rhoStaticContextReflectiveAvailable ambient
        (normalizeParallelElementsByOccurrenceSource key declaration patterns
          occurrence).occurrence.context =
      rhoStaticContextReflectiveAvailable ambient
        occurrence.occurrence.context := by
  unfold normalizeParallelElementsByOccurrenceSource
  let flattened := patterns.flatMap (parallelSplice declaration)
  let retained := flattened.filter fun pattern =>
    pattern ≠ .apply declaration.parallelUnitConstructor []
  let phaseEquality : normalizeParallelElementsBy key declaration patterns =
      Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy key retained := by
    rfl
  let sortedOccurrence : CostStaticFVarListOccurrence
      (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy key retained) :=
    occurrence.castPatterns phaseEquality
  let retainedOccurrence :=
    sortPatternsByOccurrenceSource key retained sortedOccurrence
  let flattenedOccurrence := filterOccurrenceSource
    (fun pattern => pattern ≠
      .apply declaration.parallelUnitConstructor [])
    flattened retainedOccurrence
  exact
    (rhoStaticContextReflectiveAvailable_parallelFlatMapOccurrenceSource
      declaration patterns flattenedOccurrence ambient).trans
    ((rhoStaticContextReflectiveAvailable_filterOccurrenceSource
      (fun pattern => pattern ≠
        .apply declaration.parallelUnitConstructor [])
      flattened retainedOccurrence ambient).trans
    ((rhoStaticContextReflectiveAvailable_sortPatternsByOccurrenceSource
      key retained sortedOccurrence ambient).trans
    (rhoStaticContextReflectiveAvailable_castPatterns phaseEquality occurrence
      ambient)))

/-- Empty/singleton/parallel rebuilding changes only a collection wrapper and
therefore preserves quote-local availability. -/
theorem rhoStaticContextReflectiveAvailable_collapseParallelOccurrenceSource
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern)
    (occurrence : CostStaticFVarOccurrence
      (collapseParallel declaration patterns)) (ambient : List TypeExpr) :
    rhoStaticContextReflectiveAvailable ambient
        (collapseParallelOccurrenceSource declaration patterns occurrence
          ).occurrence.context =
      rhoStaticContextReflectiveAvailable ambient occurrence.context := by
  cases patterns with
  | nil =>
      have impossible := occurrence.name_mem_freeFvarNames
      simp [collapseParallel, Pattern.freeFvarNames] at impossible
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second tail =>
          exact rhoStaticContextReflectiveAvailable_collectionOccurrenceMember
            ambient declaration.parallelCollection (first :: second :: tail)
              none occurrence

/-- Every outer parallel phase preserves quote-local availability exactly. -/
theorem rhoStaticContextReflectiveAvailable_keyedParallelPhaseOccurrenceSource
    {Key : Type} [LinearOrder Key] (key : Pattern → Key)
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern)
    (occurrence : CostStaticFVarOccurrence
      (collapseParallel declaration
        (normalizeParallelElementsBy key declaration patterns)))
    (ambient : List TypeExpr) :
    rhoStaticContextReflectiveAvailable ambient
        (keyedParallelPhaseOccurrenceSource key declaration patterns occurrence
          ).occurrence.context =
      rhoStaticContextReflectiveAvailable ambient occurrence.context := by
  unfold keyedParallelPhaseOccurrenceSource
  let normalizedOccurrence := collapseParallelOccurrenceSource declaration
    (normalizeParallelElementsBy key declaration patterns) occurrence
  exact
    (rhoStaticContextReflectiveAvailable_normalizeParallelOccurrenceSource
      key declaration patterns normalizedOccurrence ambient).trans
    (rhoStaticContextReflectiveAvailable_collapseParallelOccurrenceSource
      declaration (normalizeParallelElementsBy key declaration patterns)
        occurrence ambient)

/-- The application finisher either retains the exact application zipper or
exposes a payload through Quote(Drop(-)).  In the latter case the authored
argument was already below the quote reset, so its availability is the empty
suffix of the exposed target availability. -/
theorem rhoStaticContextReflectiveAvailable_finishApplyOccurrenceSource
    (constructor : String) (arguments : List Pattern)
    (occurrence : CostStaticFVarOccurrence
      (finishNormalizeReflectiveApply rhoReflectivePresentation constructor
        arguments)) (ambient : List TypeExpr) :
    rhoStaticContextReflectiveAvailable
        (if ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.reflection.1
            constructor then [] else ambient)
        (finishApplyOccurrenceSource rhoReflectivePresentation constructor
          arguments occurrence).occurrence.context <:+
      rhoStaticContextReflectiveAvailable ambient occurrence.context := by
  unfold finishApplyOccurrenceSource
  generalize shapeEquality :
    finishApplyShape rhoReflectivePresentation constructor arguments = shape
  cases shape with
  | retained resultEquality =>
      have argumentEquality :=
        rhoStaticContextReflectiveAvailable_applyOccurrenceArgument ambient
          constructor arguments (occurrence.castRoot resultEquality)
      have castEquality := rhoStaticContextReflectiveAvailable_castRoot
        resultEquality occurrence ambient
      exact List.suffix_of_eq (argumentEquality.trans castEquality)
  | exposed name constructorEquality argumentsEquality resultEquality =>
      have quoted : ReflectiveContextSupport.isQuoteConstructor
          rhoCIGSLT.reflection.1 constructor = true := by
        subst constructor
        simp [rhoReflectionProfile,
          ReflectiveContextSupport.isQuoteConstructor,
          rhoReflectivePresentation]
      rw [if_pos quoted]
      rw [rhoStaticContextReflectiveAvailable_nil]
      exact List.nil_suffix

/-- Semantic-atom reification renames only free variables, so it leaves the
quote structure—and therefore the local reflective availability—unchanged. -/
theorem rhoStaticContextReflectiveAvailable_reifyContext
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (ambient : List TypeExpr) (context : OneHoleContext) :
    rhoStaticContextReflectiveAvailable ambient
        (environment.reifyContext context) =
      rhoStaticContextReflectiveAvailable ambient context := by
  rw [environment.reifyContext_eq_renameFVarsContext]
  induction context generalizing ambient with
  | hole => rfl
  | apply constructor before inner after inductionHypothesis =>
      simpa [StructuralPatternAction.renameFVarsContext,
        rhoStaticContextReflectiveAvailable] using
        inductionHypothesis
          (if ReflectiveContextSupport.isQuoteConstructor
              rhoCIGSLT.reflection.1 constructor then [] else ambient)
  | lambda binder inner inductionHypothesis =>
      exact inductionHypothesis ambient
  | multiLambda arity binders inner inductionHypothesis =>
      exact inductionHypothesis ambient
  | substBody inner replacement inductionHypothesis =>
      exact inductionHypothesis ambient
  | substReplacement body inner inductionHypothesis =>
      exact inductionHypothesis ambient
  | collection collectionType before inner after rest inductionHypothesis =>
      exact inductionHypothesis ambient

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
mutual
  /-- Exact occurrence ancestry through full two-depth rho canonicalization
  never loses authored quote-local availability.  Every ordinary phase
  preserves it; Quote(Drop(-)) exposure is the sole strict suffix step. -/
  theorem rhoStaticContextReflectiveAvailable_canonicalizeByDepthsOccurrenceSource
      {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
      (availableDepth scopeDepth : Nat) :
      ∀ (pattern : Pattern)
        (occurrence : CostStaticFVarOccurrence
          (canonicalizeByDepths key rhoReflectivePresentation availableDepth
            scopeDepth pattern))
        (ambient : List TypeExpr),
        rhoStaticFrameBinderFree pattern = true →
          rhoStaticContextReflectiveAvailable ambient
              (canonicalizeByDepthsOccurrenceSource key
                rhoReflectivePresentation availableDepth scopeDepth pattern
                  occurrence).context <:+
            rhoStaticContextReflectiveAvailable ambient occurrence.context
    | .bvar index, occurrence, _, _ => by
        have impossible := occurrence.name_mem_freeFvarNames
        simp [canonicalizeByDepths, Pattern.freeFvarNames] at impossible
    | .fvar name, occurrence, _, _ => List.suffix_rfl
    | .apply constructor arguments, occurrence, ambient, frameFree => by
        rw [canonicalizeByDepthsOccurrenceSource]
        let childAvailableDepth :=
          if constructor == rhoReflectivePresentation.quoteConstructor then 0
          else availableDepth
        let childAmbient :=
          if ReflectiveContextSupport.isQuoteConstructor
              rhoCIGSLT.reflection.1 constructor then [] else ambient
        let normalizedArguments :=
          canonicalizeListByDepths key rhoReflectivePresentation
            childAvailableDepth scopeDepth arguments
        let normalizedArgument := finishApplyOccurrenceSource
          rhoReflectivePresentation constructor normalizedArguments occurrence
        let sourceArgument := canonicalizeListByDepthsOccurrenceSource key
          rhoReflectivePresentation childAvailableDepth scopeDepth arguments
            normalizedArgument
        change rhoStaticContextReflectiveAvailable ambient
            (sourceArgument.inApply constructor).context <:+
          rhoStaticContextReflectiveAvailable ambient occurrence.context
        rw [rhoStaticContextReflectiveAvailable_inApply]
        exact
          (rhoStaticContextReflectiveAvailable_canonicalizeListByDepthsOccurrenceSource
            key childAvailableDepth scopeDepth arguments normalizedArgument
              childAmbient (by simpa [rhoStaticFrameBinderFree] using
                frameFree)).trans
          (rhoStaticContextReflectiveAvailable_finishApplyOccurrenceSource
            constructor normalizedArguments occurrence ambient)
    | .lambda binder body, _, _, frameFree => by
        simp [rhoStaticFrameBinderFree] at frameFree
    | .multiLambda arity binders body, _, _, frameFree => by
        simp [rhoStaticFrameBinderFree] at frameFree
    | .subst body replacement, _, _, frameFree => by
        simp [rhoStaticFrameBinderFree] at frameFree
    | .collection collectionType elements none, occurrence, ambient,
        frameFree => by
        rw [canonicalizeByDepthsOccurrenceSource]
        let normalizedElements := canonicalizeListByDepths key
          rhoReflectivePresentation availableDepth scopeDepth elements
        by_cases parallel :
            collectionType = rhoReflectivePresentation.parallelCollection
        · subst collectionType
          rw [dif_pos rfl]
          let phaseEquality :
              canonicalizeByDepths key rhoReflectivePresentation availableDepth
                  scopeDepth
                  (.collection rhoReflectivePresentation.parallelCollection
                    elements none) =
                collapseParallel rhoReflectivePresentation
                  (normalizeParallelElementsBy
                    (key availableDepth scopeDepth) rhoReflectivePresentation
                      normalizedElements) := by
            simp [canonicalizeByDepths, normalizedElements]
          let finalOccurrence := occurrence.castRoot phaseEquality
          let normalizedOccurrence := keyedParallelPhaseOccurrenceSource
            (key availableDepth scopeDepth) rhoReflectivePresentation
              normalizedElements finalOccurrence
          let sourceOccurrence := canonicalizeListByDepthsOccurrenceSource key
            rhoReflectivePresentation availableDepth scopeDepth elements
              normalizedOccurrence
          change rhoStaticContextReflectiveAvailable ambient
              (sourceOccurrence.inCollection
                rhoReflectivePresentation.parallelCollection none).context <:+
            rhoStaticContextReflectiveAvailable ambient occurrence.context
          rw [rhoStaticContextReflectiveAvailable_inCollection]
          exact
            (rhoStaticContextReflectiveAvailable_canonicalizeListByDepthsOccurrenceSource
              key availableDepth scopeDepth elements normalizedOccurrence ambient
                (by simpa [rhoStaticFrameBinderFree] using frameFree)).trans
            ((List.suffix_of_eq
              (rhoStaticContextReflectiveAvailable_keyedParallelPhaseOccurrenceSource
                (key availableDepth scopeDepth) rhoReflectivePresentation
                  normalizedElements finalOccurrence ambient)).trans
            (List.suffix_of_eq
              (rhoStaticContextReflectiveAvailable_castRoot phaseEquality
                occurrence ambient)))
        · rw [dif_neg parallel]
          let phaseEquality :
              canonicalizeByDepths key rhoReflectivePresentation availableDepth
                  scopeDepth (.collection collectionType elements none) =
                .collection collectionType normalizedElements none := by
            simp [canonicalizeByDepths, normalizedElements, parallel]
          let finalOccurrence := occurrence.castRoot phaseEquality
          let normalizedOccurrence := collectionOccurrenceMember collectionType
            normalizedElements none finalOccurrence
          let sourceOccurrence := canonicalizeListByDepthsOccurrenceSource key
            rhoReflectivePresentation availableDepth scopeDepth elements
              normalizedOccurrence
          change rhoStaticContextReflectiveAvailable ambient
              (sourceOccurrence.inCollection collectionType none).context <:+
            rhoStaticContextReflectiveAvailable ambient occurrence.context
          rw [rhoStaticContextReflectiveAvailable_inCollection]
          exact
            (rhoStaticContextReflectiveAvailable_canonicalizeListByDepthsOccurrenceSource
              key availableDepth scopeDepth elements normalizedOccurrence ambient
                (by simpa [rhoStaticFrameBinderFree] using frameFree)).trans
            ((List.suffix_of_eq
              (rhoStaticContextReflectiveAvailable_collectionOccurrenceMember
                ambient collectionType normalizedElements none
                  finalOccurrence)).trans
            (List.suffix_of_eq
              (rhoStaticContextReflectiveAvailable_castRoot phaseEquality
                occurrence ambient)))
    | .collection collectionType elements (some rest), occurrence, ambient,
        frameFree => by
        rw [canonicalizeByDepthsOccurrenceSource]
        let normalizedElements := canonicalizeListByDepths key
          rhoReflectivePresentation availableDepth scopeDepth elements
        let phaseEquality :
            canonicalizeByDepths key rhoReflectivePresentation availableDepth
                scopeDepth (.collection collectionType elements (some rest)) =
              .collection collectionType normalizedElements (some rest) := by
          simp [canonicalizeByDepths, normalizedElements]
        let finalOccurrence := occurrence.castRoot phaseEquality
        let normalizedOccurrence := collectionOccurrenceMember collectionType
          normalizedElements (some rest) finalOccurrence
        let sourceOccurrence := canonicalizeListByDepthsOccurrenceSource key
          rhoReflectivePresentation availableDepth scopeDepth elements
            normalizedOccurrence
        change rhoStaticContextReflectiveAvailable ambient
            (sourceOccurrence.inCollection collectionType (some rest)
              ).context <:+
          rhoStaticContextReflectiveAvailable ambient occurrence.context
        rw [rhoStaticContextReflectiveAvailable_inCollection]
        exact
          (rhoStaticContextReflectiveAvailable_canonicalizeListByDepthsOccurrenceSource
            key availableDepth scopeDepth elements normalizedOccurrence ambient
              (by simpa [rhoStaticFrameBinderFree] using frameFree)).trans
          ((List.suffix_of_eq
            (rhoStaticContextReflectiveAvailable_collectionOccurrenceMember
              ambient collectionType normalizedElements (some rest)
                finalOccurrence)).trans
          (List.suffix_of_eq
            (rhoStaticContextReflectiveAvailable_castRoot phaseEquality
              occurrence ambient)))
  termination_by pattern => 3 * sizeOf pattern + 2

  /-- Pointwise list companion to exact quote-local ancestry. -/
  theorem rhoStaticContextReflectiveAvailable_canonicalizeListByDepthsOccurrenceSource
      {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
      (availableDepth scopeDepth : Nat) :
      ∀ (patterns : List Pattern)
        (occurrence : CostStaticFVarListOccurrence
          (canonicalizeListByDepths key rhoReflectivePresentation
            availableDepth scopeDepth patterns))
        (ambient : List TypeExpr),
        rhoStaticFrameListBinderFree patterns = true →
          rhoStaticContextReflectiveAvailable ambient
              (canonicalizeListByDepthsOccurrenceSource key
                rhoReflectivePresentation availableDepth scopeDepth patterns
                  occurrence).occurrence.context <:+
            rhoStaticContextReflectiveAvailable ambient
              occurrence.occurrence.context
    | [], occurrence, _, _ => Fin.elim0 occurrence.position
    | head :: tail, occurrence, ambient, frameFree => by
        rcases occurrence with ⟨position, nested⟩
        cases position using Fin.cases with
        | zero =>
            rw [canonicalizeListByDepthsOccurrenceSource]
            exact
              rhoStaticContextReflectiveAvailable_canonicalizeByDepthsOccurrenceSource
                key availableDepth scopeDepth head nested ambient
                  (by simpa [rhoStaticFrameListBinderFree] using frameFree)
        | succ tailPosition =>
            rw [canonicalizeListByDepthsOccurrenceSource]
            let tailOccurrence : CostStaticFVarListOccurrence
                (canonicalizeListByDepths key rhoReflectivePresentation
                  availableDepth scopeDepth tail) :=
              { position := tailPosition
                occurrence := nested }
            exact
              rhoStaticContextReflectiveAvailable_canonicalizeListByDepthsOccurrenceSource
                key availableDepth scopeDepth tail tailOccurrence ambient
                  (by simpa [rhoStaticFrameListBinderFree] using frameFree)
  termination_by patterns => 3 * sizeOf patterns + 1

  decreasing_by
    all_goals simp_all <;> omega
end

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
mutual
  /-- Typed exact ancestry through full rho canonicalization.  Either the
  authored and final occurrence have identical quote-local availability, or
  the authored occurrence names a value in rho's `Name` fibre. -/
  theorem rhoStaticContextReflectiveAvailable_canonicalizeByDepthsOccurrenceSource_eq_or_name
      {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
      (availableDepth scopeDepth : Nat) :
      ∀ (pattern : Pattern) (free : WellSorted.FreeTypeContext)
        (bound : List TypeExpr) (type : TypeExpr)
        (typed : WellSorted.HasType rhoCalc free bound pattern type)
        (occurrence : CostStaticFVarOccurrence
          (canonicalizeByDepths key rhoReflectivePresentation availableDepth
            scopeDepth pattern))
        (ambient : List TypeExpr),
        rhoStaticFrameBinderFree pattern = true →
        WellSorted.isObjectPattern pattern = true →
          rhoStaticContextReflectiveAvailable ambient
              (canonicalizeByDepthsOccurrenceSource key
                rhoReflectivePresentation availableDepth scopeDepth pattern
                  occurrence).context =
            rhoStaticContextReflectiveAvailable ambient occurrence.context ∨
          (rhoStaticContextReflectiveAvailable ambient
              (canonicalizeByDepthsOccurrenceSource key
                rhoReflectivePresentation availableDepth scopeDepth pattern
                  occurrence).context = [] ∧
            free (canonicalizeByDepthsOccurrenceSource key
              rhoReflectivePresentation availableDepth scopeDepth pattern
                occurrence).name = some TypeExpr.name)
    | .bvar index, free, bound, type, typed, occurrence, _, _, _ => by
        have impossible := occurrence.name_mem_freeFvarNames
        simp [canonicalizeByDepths, Pattern.freeFvarNames] at impossible
    | .fvar name, free, bound, type, typed, occurrence, _, _, _ =>
        Or.inl rfl
    | .apply constructor arguments, free, bound, type, typed, occurrence,
        ambient, frameFree, object => by
        obtain ⟨rule, membership, labelEquality, notBare, typeEquality,
            argumentsTyped⟩ := WellSorted.hasType_apply_inversion typed
        subst constructor
        let childAvailableDepth :=
          if rule.label == rhoReflectivePresentation.quoteConstructor then 0
          else availableDepth
        let childAmbient :=
          if ReflectiveContextSupport.isQuoteConstructor
              rhoCIGSLT.reflection.1 rule.label then [] else ambient
        let normalizedArguments :=
          canonicalizeListByDepths key rhoReflectivePresentation
            childAvailableDepth scopeDepth arguments
        let normalizedArgument := finishApplyOccurrenceSource
          rhoReflectivePresentation rule.label normalizedArguments occurrence
        let sourceArgument := canonicalizeListByDepthsOccurrenceSource key
          rhoReflectivePresentation childAvailableDepth scopeDepth arguments
            normalizedArgument
        have argumentsObject :
            WellSorted.isObjectPatternList arguments = true := by
          simpa [WellSorted.isObjectPattern] using object
        have argumentsFree : rhoStaticFrameListBinderFree arguments = true := by
          simpa [rhoStaticFrameBinderFree] using frameFree
        have parametersCanonicalizable :=
          CanonicalSupport.rhoRule_parametersCanonicalizable membership notBare
        have normalizedArgumentsTyped :
            WellSorted.ArgumentsHaveTypes rhoCalc free bound
              normalizedArguments rule.params := by
          exact rhoCanonicalizeListByDepths_argumentsTyped key
            childAvailableDepth scopeDepth argumentsTyped
              parametersCanonicalizable argumentsObject
        let preFinishTyped : WellSorted.HasType rhoCalc free bound
            (.apply rule.label normalizedArguments) (.base rule.category) :=
          .constructor membership notBare normalizedArgumentsTyped
        have normalizedArgumentsObject :
            WellSorted.isObjectPatternList normalizedArguments = true := by
          exact canonicalizeListByDepths_isObjectPatternList key
            rhoReflectivePresentation childAvailableDepth scopeDepth arguments
              argumentsObject
        have preFinishObject : WellSorted.isObjectPattern
            (.apply rule.label normalizedArguments) = true := by
          simpa [WellSorted.isObjectPattern] using normalizedArgumentsObject
        have nested :=
          rhoStaticContextReflectiveAvailable_canonicalizeListByDepthsOccurrenceSource_eq_or_name
            key childAvailableDepth scopeDepth arguments free bound
              (RhoPatternListHasType.ofArguments argumentsTyped)
                normalizedArgument childAmbient argumentsFree argumentsObject
        have finished :=
          rhoStaticContextReflectiveAvailable_finishApplyOccurrenceSource_eq_or_name
            rule.label normalizedArguments preFinishTyped preFinishObject
              occurrence ambient
        rw [canonicalizeByDepthsOccurrenceSource]
        change rhoStaticContextReflectiveAvailable ambient
            (sourceArgument.inApply rule.label).context =
              rhoStaticContextReflectiveAvailable ambient occurrence.context ∨
            (rhoStaticContextReflectiveAvailable childAmbient
                sourceArgument.occurrence.context = [] ∧
              free (sourceArgument.inApply rule.label).name =
                some TypeExpr.name)
        rw [rhoStaticContextReflectiveAvailable_inApply]
        rcases nested with nestedEq | nestedExposure
        · rcases finished with finishedEq | finishedName
          · exact Or.inl (nestedEq.trans finishedEq)
          · right
            constructor
            · exact nestedEq.trans finishedName.1
            have sourceName :=
              canonicalizeListByDepthsOccurrenceSource_name key
                rhoReflectivePresentation childAvailableDepth scopeDepth
                  arguments normalizedArgument
            simpa [sourceArgument] using sourceName.trans finishedName.2
        · exact Or.inr nestedExposure
    | .lambda binder body, free, bound, type, typed, occurrence, ambient,
        frameFree, object => by
        simp [rhoStaticFrameBinderFree] at frameFree
    | .multiLambda arity binders body, free, bound, type, typed, occurrence,
        ambient, frameFree, object => by
        simp [rhoStaticFrameBinderFree] at frameFree
    | .subst body replacement, free, bound, type, typed, occurrence, ambient,
        frameFree, object => by
        simp [rhoStaticFrameBinderFree] at frameFree
    | .collection collectionType elements rest, free, bound, type, typed,
        occurrence, ambient, frameFree, object => by
        obtain ⟨elementType, elementsTyped⟩ : ∃ elementType,
            WellSorted.ElementsHaveType rhoCalc free bound elements
              elementType := by
          rcases WellSorted.hasType_collection_inversion typed with
            ⟨elementType, _typeEq, elementsTyped⟩ |
              ⟨rule, parameterName, elementType, membership, parameterShape,
                _typeEq, elementsTyped⟩
          · exact ⟨elementType, elementsTyped⟩
          · exact ⟨elementType, elementsTyped⟩
        have elementsFree : rhoStaticFrameListBinderFree elements = true := by
          simpa [rhoStaticFrameBinderFree] using frameFree
        have elementsObject : WellSorted.isObjectPatternList elements = true := by
          simpa [WellSorted.isObjectPattern] using object
        let normalizedElements := canonicalizeListByDepths key
          rhoReflectivePresentation availableDepth scopeDepth elements
        cases rest with
        | none =>
            by_cases parallel :
                collectionType = rhoReflectivePresentation.parallelCollection
            · subst collectionType
              rw [canonicalizeByDepthsOccurrenceSource, dif_pos rfl]
              let phaseEquality :
                  canonicalizeByDepths key rhoReflectivePresentation
                      availableDepth scopeDepth
                      (.collection rhoReflectivePresentation.parallelCollection
                        elements none) =
                    collapseParallel rhoReflectivePresentation
                      (normalizeParallelElementsBy
                        (key availableDepth scopeDepth) rhoReflectivePresentation
                          normalizedElements) := by
                simp [canonicalizeByDepths, normalizedElements]
              let finalOccurrence := occurrence.castRoot phaseEquality
              let normalizedOccurrence := keyedParallelPhaseOccurrenceSource
                (key availableDepth scopeDepth) rhoReflectivePresentation
                  normalizedElements finalOccurrence
              let sourceOccurrence :=
                canonicalizeListByDepthsOccurrenceSource key
                  rhoReflectivePresentation availableDepth scopeDepth elements
                    normalizedOccurrence
              have nested :=
                rhoStaticContextReflectiveAvailable_canonicalizeListByDepthsOccurrenceSource_eq_or_name
                  key availableDepth scopeDepth elements free bound
                    (RhoPatternListHasType.ofElements elementsTyped)
                      normalizedOccurrence ambient elementsFree elementsObject
              change rhoStaticContextReflectiveAvailable ambient
                  (sourceOccurrence.inCollection
                    rhoReflectivePresentation.parallelCollection none).context =
                    rhoStaticContextReflectiveAvailable ambient
                      occurrence.context ∨
                  (rhoStaticContextReflectiveAvailable ambient
                      sourceOccurrence.occurrence.context = [] ∧
                    free (sourceOccurrence.inCollection
                      rhoReflectivePresentation.parallelCollection none).name =
                      some TypeExpr.name)
              rw [rhoStaticContextReflectiveAvailable_inCollection]
              rcases nested with nestedEq | nestedName
              · left
                exact nestedEq.trans
                  ((rhoStaticContextReflectiveAvailable_keyedParallelPhaseOccurrenceSource
                    (key availableDepth scopeDepth) rhoReflectivePresentation
                      normalizedElements finalOccurrence ambient).trans
                  (rhoStaticContextReflectiveAvailable_castRoot phaseEquality
                    occurrence ambient))
              · exact Or.inr nestedName
            · rw [canonicalizeByDepthsOccurrenceSource, dif_neg parallel]
              let phaseEquality :
                  canonicalizeByDepths key rhoReflectivePresentation
                      availableDepth scopeDepth
                      (.collection collectionType elements none) =
                    .collection collectionType normalizedElements none := by
                simp [canonicalizeByDepths, normalizedElements, parallel]
              let finalOccurrence := occurrence.castRoot phaseEquality
              let normalizedOccurrence := collectionOccurrenceMember
                collectionType normalizedElements none finalOccurrence
              let sourceOccurrence :=
                canonicalizeListByDepthsOccurrenceSource key
                  rhoReflectivePresentation availableDepth scopeDepth elements
                    normalizedOccurrence
              have nested :=
                rhoStaticContextReflectiveAvailable_canonicalizeListByDepthsOccurrenceSource_eq_or_name
                  key availableDepth scopeDepth elements free bound
                    (RhoPatternListHasType.ofElements elementsTyped)
                      normalizedOccurrence ambient elementsFree elementsObject
              change rhoStaticContextReflectiveAvailable ambient
                  (sourceOccurrence.inCollection collectionType none).context =
                    rhoStaticContextReflectiveAvailable ambient
                      occurrence.context ∨
                  (rhoStaticContextReflectiveAvailable ambient
                      sourceOccurrence.occurrence.context = [] ∧
                    free (sourceOccurrence.inCollection collectionType
                      none).name = some TypeExpr.name)
              rw [rhoStaticContextReflectiveAvailable_inCollection]
              rcases nested with nestedEq | nestedName
              · left
                exact nestedEq.trans
                  ((rhoStaticContextReflectiveAvailable_collectionOccurrenceMember
                    ambient collectionType normalizedElements none
                      finalOccurrence).trans
                  (rhoStaticContextReflectiveAvailable_castRoot phaseEquality
                    occurrence ambient))
              · exact Or.inr nestedName
        | some collectionRest =>
            rw [canonicalizeByDepthsOccurrenceSource]
            let phaseEquality :
                canonicalizeByDepths key rhoReflectivePresentation
                    availableDepth scopeDepth
                    (.collection collectionType elements
                      (some collectionRest)) =
                  .collection collectionType normalizedElements
                    (some collectionRest) := by
              simp [canonicalizeByDepths, normalizedElements]
            let finalOccurrence := occurrence.castRoot phaseEquality
            let normalizedOccurrence := collectionOccurrenceMember
              collectionType normalizedElements (some collectionRest)
                finalOccurrence
            let sourceOccurrence :=
              canonicalizeListByDepthsOccurrenceSource key
                rhoReflectivePresentation availableDepth scopeDepth elements
                  normalizedOccurrence
            have nested :=
              rhoStaticContextReflectiveAvailable_canonicalizeListByDepthsOccurrenceSource_eq_or_name
                key availableDepth scopeDepth elements free bound
                  (RhoPatternListHasType.ofElements elementsTyped)
                    normalizedOccurrence ambient elementsFree elementsObject
            change rhoStaticContextReflectiveAvailable ambient
                (sourceOccurrence.inCollection collectionType
                  (some collectionRest)).context =
                  rhoStaticContextReflectiveAvailable ambient
                    occurrence.context ∨
                (rhoStaticContextReflectiveAvailable ambient
                    sourceOccurrence.occurrence.context = [] ∧
                  free (sourceOccurrence.inCollection collectionType
                    (some collectionRest)).name = some TypeExpr.name)
            rw [rhoStaticContextReflectiveAvailable_inCollection]
            rcases nested with nestedEq | nestedName
            · left
              exact nestedEq.trans
                ((rhoStaticContextReflectiveAvailable_collectionOccurrenceMember
                  ambient collectionType normalizedElements
                    (some collectionRest) finalOccurrence).trans
                (rhoStaticContextReflectiveAvailable_castRoot phaseEquality
                  occurrence ambient))
            · exact Or.inr nestedName
  termination_by pattern => 3 * sizeOf pattern + 2

  /-- Elementwise-typed list companion to the full rho ancestry
  dichotomy. -/
  theorem rhoStaticContextReflectiveAvailable_canonicalizeListByDepthsOccurrenceSource_eq_or_name
      {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
      (availableDepth scopeDepth : Nat) :
      ∀ (patterns : List Pattern) (free : WellSorted.FreeTypeContext)
        (bound : List TypeExpr)
        (typed : RhoPatternListHasType free bound patterns)
        (occurrence : CostStaticFVarListOccurrence
          (canonicalizeListByDepths key rhoReflectivePresentation
            availableDepth scopeDepth patterns))
        (ambient : List TypeExpr),
        rhoStaticFrameListBinderFree patterns = true →
        WellSorted.isObjectPatternList patterns = true →
          rhoStaticContextReflectiveAvailable ambient
              (canonicalizeListByDepthsOccurrenceSource key
                rhoReflectivePresentation availableDepth scopeDepth patterns
                  occurrence).occurrence.context =
            rhoStaticContextReflectiveAvailable ambient
              occurrence.occurrence.context ∨
          (rhoStaticContextReflectiveAvailable ambient
              (canonicalizeListByDepthsOccurrenceSource key
                rhoReflectivePresentation availableDepth scopeDepth patterns
                  occurrence).occurrence.context = [] ∧
            free (canonicalizeListByDepthsOccurrenceSource key
              rhoReflectivePresentation availableDepth scopeDepth patterns
                occurrence).occurrence.name = some TypeExpr.name)
    | [], free, bound, typed, occurrence, ambient, frameFree, object =>
        Fin.elim0 occurrence.position
    | head :: tail, free, bound, typed, occurrence, ambient, frameFree,
        object => by
        have headTyped : ∃ type,
            WellSorted.HasType rhoCalc free bound head type :=
          typed head (by simp)
        have tailTyped : RhoPatternListHasType free bound tail := by
          intro pattern membership
          exact typed pattern (by simp [membership])
        have freeParts : rhoStaticFrameBinderFree head = true ∧
            rhoStaticFrameListBinderFree tail = true := by
          simpa [rhoStaticFrameListBinderFree] using frameFree
        have objectParts : WellSorted.isObjectPattern head = true ∧
            WellSorted.isObjectPatternList tail = true := by
          simpa [WellSorted.isObjectPatternList] using object
        rcases occurrence with ⟨position, nested⟩
        cases position using Fin.cases with
        | zero =>
            rw [canonicalizeListByDepthsOccurrenceSource]
            obtain ⟨type, headTyped⟩ := headTyped
            exact
              rhoStaticContextReflectiveAvailable_canonicalizeByDepthsOccurrenceSource_eq_or_name
                key availableDepth scopeDepth head free bound type headTyped
                  nested ambient freeParts.1 objectParts.1
        | succ tailPosition =>
            rw [canonicalizeListByDepthsOccurrenceSource]
            let tailOccurrence : CostStaticFVarListOccurrence
                (canonicalizeListByDepths key rhoReflectivePresentation
                  availableDepth scopeDepth tail) :=
              { position := tailPosition
                occurrence := nested }
            exact
              rhoStaticContextReflectiveAvailable_canonicalizeListByDepthsOccurrenceSource_eq_or_name
                key availableDepth scopeDepth tail free bound tailTyped
                  tailOccurrence ambient freeParts.2 objectParts.2
  termination_by patterns => 3 * sizeOf patterns + 1

  decreasing_by
    all_goals simp_all <;> omega
end

/-- Exact source-inventory ancestry for one occurrence in rho's actual
scope-sensitive hereditary canonical representative. -/
abbrev RhoCanonicalInventoryOccurrenceCertificate
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    (targetOccurrence : CostStaticFVarOccurrence
      (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
        rhoReflectivePresentation node.targetBound.length 0
        (node.reifiedSourceFrame environment).1)) :=
  CostCanonicalInventoryOccurrenceCertificate environment
    (sourceSemanticPatternKeyAt node environment) rhoReflectivePresentation
      node.targetBound.length 0 targetOccurrence

/-- Instantiate the generic two-depth ancestry theorem at the exact source
key and frame chosen by hereditary rho normalization. -/
noncomputable def rhoCanonicalInventoryOccurrenceCertificate
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    (targetOccurrence : CostStaticFVarOccurrence
      (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
        rhoReflectivePresentation node.targetBound.length 0
        (node.reifiedSourceFrame environment).1)) :
    RhoCanonicalInventoryOccurrenceCertificate node environment
      targetOccurrence := by
  simpa only [node.reifiedSourceFrame_pattern] using
    costCanonicalInventoryOccurrenceCertificate environment
      (sourceSemanticPatternKeyAt node environment) rhoReflectivePresentation
        node.targetBound.length 0 targetOccurrence

/-- The authored plan availability attached to the exact inventory ancestor
is a suffix of the final canonical occurrence's availability.  Reification
only renames leaves; all strict growth is accounted for by Quote/Drop
exposure in the recursive canonical trace. -/
theorem rhoCanonicalInventoryOccurrence_sourceAvailable_suffix_targetAvailable
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    (targetOccurrence : CostStaticFVarOccurrence
      (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
        rhoReflectivePresentation node.targetBound.length 0
        (node.reifiedSourceFrame environment).1))
    (ambient : List TypeExpr) :
    rhoStaticContextReflectiveAvailable ambient
        (planDecorationOccurrenceAt node inventory
          (rhoCanonicalInventoryOccurrenceCertificate node environment
            targetOccurrence).sourcePosition).context <:+
      rhoStaticContextReflectiveAvailable ambient targetOccurrence.context := by
  let ancestry := rhoCanonicalInventoryOccurrenceCertificate node environment
    targetOccurrence
  have traced :=
    rhoStaticContextReflectiveAvailable_canonicalizeByDepthsOccurrenceSource
      (sourceSemanticPatternKeyAt node environment) node.targetBound.length 0
        (node.reifiedSourceFrame environment).1 targetOccurrence ambient
          (reifiedSourceFrame_binderFree node environment)
  have reifiedTrace :
      rhoStaticContextReflectiveAvailable ambient
          ancestry.reifiedOccurrence.context <:+
        rhoStaticContextReflectiveAvailable ambient targetOccurrence.context := by
    rw [ancestry.canonical_source_eq]
    exact traced
  have planToReified :
      rhoStaticContextReflectiveAvailable ambient
          (planDecorationOccurrenceAt node inventory
            ancestry.sourcePosition).context =
        rhoStaticContextReflectiveAvailable ambient
          ancestry.reifiedOccurrence.context := by
    calc
      rhoStaticContextReflectiveAvailable ambient
          (planDecorationOccurrenceAt node inventory
            ancestry.sourcePosition).context =
          rhoStaticContextReflectiveAvailable ambient
            (inventory.occurrenceAt ancestry.sourcePosition
              ).fvarOccurrence.context := by
            rw [planDecorationOccurrenceAt_context]
      _ = rhoStaticContextReflectiveAvailable ambient
            ancestry.sourceOccurrence.context := by
          rw [ancestry.position_eq]
      _ = rhoStaticContextReflectiveAvailable ambient
            (environment.reifyOccurrence ancestry.sourceOccurrence
              ).context := by
          symm
          simpa using rhoStaticContextReflectiveAvailable_reifyContext
            environment ambient ancestry.sourceOccurrence.context
      _ = rhoStaticContextReflectiveAvailable ambient
            ancestry.reifiedOccurrence.context := by
          rw [ancestry.reified_eq]
  exact (List.suffix_of_eq planToReified).trans reifiedTrace

/-- Typed inventory specialization of canonical ancestry.  A final occurrence
either retains its exact authored availability or belongs to a semantic atom
whose authored type is `Name`; no other strict availability growth is
possible. -/
theorem rhoCanonicalInventoryOccurrence_sourceAvailable_eq_targetAvailable_or_sourceName
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    (targetOccurrence : CostStaticFVarOccurrence
      (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
        rhoReflectivePresentation node.targetBound.length 0
        (node.reifiedSourceFrame environment).1))
    (ambient : List TypeExpr) :
    let ancestry := rhoCanonicalInventoryOccurrenceCertificate node
      environment targetOccurrence
    rhoStaticContextReflectiveAvailable ambient
        (planDecorationOccurrenceAt node inventory
          ancestry.sourcePosition).context =
        rhoStaticContextReflectiveAvailable ambient
          targetOccurrence.context ∨
      (rhoStaticContextReflectiveAvailable ambient
          (planDecorationOccurrenceAt node inventory
            ancestry.sourcePosition).context = [] ∧
        (environment.atomValue
          (environment.occurrenceSlot ancestry.sourcePosition)
            ).key.sourceType = TypeExpr.name) := by
  let ancestry := rhoCanonicalInventoryOccurrenceCertificate node environment
    targetOccurrence
  let sourceSupported := node.reifiedSourceFrame_supported environment
  have traced :=
    rhoStaticContextReflectiveAvailable_canonicalizeByDepthsOccurrenceSource_eq_or_name
      (sourceSemanticPatternKeyAt node environment) node.targetBound.length 0
        (node.reifiedSourceFrame environment).1 environment.sourceAtomFreeContext
          node.sourceBound (.base node.sourceSort.1) sourceSupported.toHasType
            targetOccurrence ambient
              (reifiedSourceFrame_binderFree node environment)
                (node.reifiedSourceFrame environment).2.1.2.2.1
  have tracedAtCertificate :
      rhoStaticContextReflectiveAvailable ambient
          ancestry.reifiedOccurrence.context =
            rhoStaticContextReflectiveAvailable ambient
              targetOccurrence.context ∨
        (rhoStaticContextReflectiveAvailable ambient
            ancestry.reifiedOccurrence.context = [] ∧
          environment.sourceAtomFreeContext ancestry.reifiedOccurrence.name =
            some TypeExpr.name) := by
    rw [ancestry.canonical_source_eq]
    exact traced
  have planToReified :
      rhoStaticContextReflectiveAvailable ambient
          (planDecorationOccurrenceAt node inventory
            ancestry.sourcePosition).context =
        rhoStaticContextReflectiveAvailable ambient
          ancestry.reifiedOccurrence.context := by
    calc
      rhoStaticContextReflectiveAvailable ambient
          (planDecorationOccurrenceAt node inventory
            ancestry.sourcePosition).context =
          rhoStaticContextReflectiveAvailable ambient
            (inventory.occurrenceAt ancestry.sourcePosition
              ).fvarOccurrence.context := by
            rw [planDecorationOccurrenceAt_context]
      _ = rhoStaticContextReflectiveAvailable ambient
            ancestry.sourceOccurrence.context := by
          rw [ancestry.position_eq]
      _ = rhoStaticContextReflectiveAvailable ambient
            (environment.reifyOccurrence ancestry.sourceOccurrence
              ).context := by
          symm
          simpa using rhoStaticContextReflectiveAvailable_reifyContext
            environment ambient ancestry.sourceOccurrence.context
      _ = rhoStaticContextReflectiveAvailable ambient
            ancestry.reifiedOccurrence.context := by
          rw [ancestry.reified_eq]
  rcases tracedAtCertificate with sameAvailable | exposure
  · exact Or.inl (planToReified.trans sameAvailable)
  · right
    constructor
    · exact planToReified.trans exposure.1
    · have reifiedName : ancestry.reifiedOccurrence.name =
          environment.atomName
            (environment.occurrenceSlot ancestry.sourcePosition) :=
        ancestry.canonical_name_eq.trans ancestry.target_name_eq_atomName
      rw [reifiedName, environment.sourceAtomFreeContext_atomName] at exposure
      exact Option.some.inj exposure.2

/-- The complete local evidence currently earned for one final canonical rho
atom occurrence.  It includes the exact authored position, safe normalized
value at that occurrence's plan-derived availability, and the selected class
suffix. -/
structure RhoCanonicalOccurrenceSupportWitness
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (profile : CostStaticOccurrenceSupportProfile environment support
      binderImage)
    (targetOccurrence : CostStaticFVarOccurrence
      (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
        rhoReflectivePresentation node.targetBound.length 0
        (node.reifiedSourceFrame environment).1)) where
  ancestry : RhoCanonicalInventoryOccurrenceCertificate node environment
    targetOccurrence
  occurrenceSafe :
    (inventory.occurrenceAtom ancestry.sourcePosition).normalTyped.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile support
          (profile.classSupport.occurrenceAvailable ancestry.sourcePosition)
            binderImage
  classSuffix :
    profile.classSupport.classAvailable
        (environment.occurrenceSlot ancestry.sourcePosition) <:+
      profile.classSupport.occurrenceAvailable ancestry.sourcePosition

/-- Project the proved occurrence support profile along exact canonical
ancestry.  No class-wide output footprint premise is used. -/
noncomputable def rhoCanonicalOccurrenceSupportWitness
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (profile : CostStaticOccurrenceSupportProfile environment support
      binderImage)
    (targetOccurrence : CostStaticFVarOccurrence
      (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
        rhoReflectivePresentation node.targetBound.length 0
        (node.reifiedSourceFrame environment).1)) :
    RhoCanonicalOccurrenceSupportWitness node environment profile
      targetOccurrence := by
  let ancestry := rhoCanonicalInventoryOccurrenceCertificate node environment
    targetOccurrence
  exact
    { ancestry := ancestry
      occurrenceSafe := profile.occurrenceSafe ancestry.sourcePosition
      classSuffix := profile.atomAvailable_suffix_occurrenceAvailable
        ancestry.sourcePosition }

/-- Every final canonical occurrence names exactly the semantic atom class
whose authored occurrence and local support are retained by the witness. -/
theorem rhoCanonicalOccurrenceSupportWitness_targetName
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (profile : CostStaticOccurrenceSupportProfile environment support
      binderImage)
    (targetOccurrence : CostStaticFVarOccurrence
      (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
        rhoReflectivePresentation node.targetBound.length 0
        (node.reifiedSourceFrame environment).1)) :
    targetOccurrence.name = environment.atomName
      (environment.occurrenceSlot
        (rhoCanonicalOccurrenceSupportWitness node environment profile
          targetOccurrence).ancestry.sourcePosition) := by
  exact (rhoCanonicalOccurrenceSupportWitness node environment profile
    targetOccurrence).ancestry.target_name_eq_atomName

/-- The semantic value selected for every exact final canonical occurrence is
safe at that occurrence's final quote-local availability.  Equal-availability
ancestry is direct transport; Quote/Drop exposure uses the sealed source and
the generated rho `Name`-fibre lifting theorem. -/
theorem rhoCanonicalOccurrence_atomSafeAt_targetAvailable
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (support : ContextSupport.Support) (available : List TypeExpr)
    (binderImage : TypeExpr → TypeExpr)
    (childrenPreserve : CostStaticBoundaryChildReflectiveSupportPreserving
      node.boundaryTable values support binderImage)
    (inputSafe : node.term.2.1.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support available binderImage)
    (targetOccurrence : CostStaticFVarOccurrence
      (canonicalizeByDepths
        (sourceSemanticPatternKeyAt node
          (CostStaticAtomEnvironment.ofInventory inventory))
        rhoReflectivePresentation node.targetBound.length 0
        (node.reifiedSourceFrame
          (CostStaticAtomEnvironment.ofInventory inventory)).1)) :
    let environment := CostStaticAtomEnvironment.ofInventory inventory
    let profile := quoteLocalOccurrenceSupportProfile node values inventory
      support available binderImage childrenPreserve inputSafe
    let witness := rhoCanonicalOccurrenceSupportWitness node environment
      profile targetOccurrence
    (inventory.occurrenceAtom
      witness.ancestry.sourcePosition).normalTyped.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile support
          (rhoStaticContextReflectiveAvailable available
            targetOccurrence.context) binderImage := by
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  let profile := quoteLocalOccurrenceSupportProfile node values inventory
    support available binderImage childrenPreserve inputSafe
  let witness := rhoCanonicalOccurrenceSupportWitness node environment profile
    targetOccurrence
  have ancestry :=
    rhoCanonicalInventoryOccurrence_sourceAvailable_eq_targetAvailable_or_sourceName
      node environment targetOccurrence available
  have occurrenceAvailable :
      profile.classSupport.occurrenceAvailable
          witness.ancestry.sourcePosition =
        rhoStaticContextReflectiveAvailable available
          (planDecorationOccurrenceAt node inventory
            witness.ancestry.sourcePosition).context := by
    exact quoteLocalOccurrenceSupportProfile_occurrenceAvailable node values
      inventory support available binderImage childrenPreserve inputSafe
        witness.ancestry.sourcePosition
  rcases ancestry with sameAvailable | exposure
  · rw [occurrenceAvailable, sameAvailable] at witness.occurrenceSafe
    exact witness.occurrenceSafe
  · have safeAtNil :
        (inventory.occurrenceAtom
          witness.ancestry.sourcePosition).normalTyped.ReflectiveSupportSafeAt
            rhoCIGSLT.costWholeReflectionProfile support [] binderImage := by
      rw [occurrenceAvailable, exposure.1] at witness.occurrenceSafe
      exact witness.occurrenceSafe
    let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
      rhoReflectivePresentation.toReflectivePresentationDecl
    have sourceMembership :
        rhoReflectivePresentation.toReflectivePresentationDecl ∈
          rhoCIGSLT.reflection.1.presentations := by
      rw [rhoCIGSLT_reflection_eq_rhoReflectionProfile]
      simp [rhoReflectionProfile]
    have declarationMembership : declaration ∈
        rhoCIGSLT.costWholeReflectionProfile.presentations := by
      simpa [declaration] using
        costStaticReflectivePresentationDecl_mem rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
            sourceMembership
    have mappedType := node.semanticAtom_typeMap values inventory
      (environment.occurrenceSlot witness.ancestry.sourcePosition)
    rw [environment.occurrenceValue] at mappedType
    have targetTypeName :
        (inventory.occurrenceAtom
          witness.ancestry.sourcePosition).key.targetType =
            .base declaration.nameSort := by
      calc
        (inventory.occurrenceAtom
            witness.ancestry.sourcePosition).key.targetType =
            mapTypeExpr (color.symbols rhoCIGSLT)
              (inventory.occurrenceAtom
                witness.ancestry.sourcePosition).key.sourceType :=
          mappedType.symm
        _ = mapTypeExpr (color.symbols rhoCIGSLT) TypeExpr.name := by
          rw [exposure.2]
        _ = .base declaration.nameSort := by
          cases color <;>
            simp [declaration, costStaticReflectivePresentationDecl_eq_map,
              mapReflectivePresentation, CostStaticColor.symbols,
              costBaseStaticSymbols, costBaseLanguageDefSymbolMap,
              costWrappedStaticSymbols, rhoReflectivePresentation]
    exact
      WellSorted.HasType.ReflectiveSupportSafeAt.nameResult_of_nil
        rho_costReflectiveNameResultsQuoted declaration declarationMembership
          (inventory.occurrenceAtom
            witness.ancestry.sourcePosition).normalTyped targetTypeName
              safeAtNil
                (inventory.occurrenceAtom
                  witness.ancestry.sourcePosition).normalObject
                    (rhoStaticContextReflectiveAvailable available
                      targetOccurrence.context)

/-- The GCS support selected from exact authored occurrences is sufficient at
every occurrence of the final canonical source frame. -/
theorem semanticCanonicalizedSourcePattern_supportBounded
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (support : ContextSupport.Support) (available : List TypeExpr)
    (binderImage : TypeExpr → TypeExpr)
    (childrenPreserve : CostStaticBoundaryChildReflectiveSupportPreserving
      node.boundaryTable values support binderImage)
    (inputSafe : node.term.2.1.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support available binderImage) :
    let environment := CostStaticAtomEnvironment.ofInventory inventory
    let profile := quoteLocalOccurrenceSupportProfile node values inventory
      support available binderImage childrenPreserve inputSafe
    RhoStaticOccurrenceSupportBounded profile.semanticInputSupport available
      (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
        rhoReflectivePresentation node.targetBound.length 0
        (node.reifiedSourceFrame environment).1) := by
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  let profile := quoteLocalOccurrenceSupportProfile node values inventory
    support available binderImage childrenPreserve inputSafe
  intro targetOccurrence
  let witness := rhoCanonicalOccurrenceSupportWitness node environment profile
    targetOccurrence
  have classToAuthored := witness.classSuffix
  have occurrenceAvailable :
      profile.classSupport.occurrenceAvailable
          witness.ancestry.sourcePosition =
        rhoStaticContextReflectiveAvailable available
          (planDecorationOccurrenceAt node inventory
            witness.ancestry.sourcePosition).context := by
    exact quoteLocalOccurrenceSupportProfile_occurrenceAvailable node values
      inventory support available binderImage childrenPreserve inputSafe
        witness.ancestry.sourcePosition
  have ancestry :=
    rhoCanonicalInventoryOccurrence_sourceAvailable_eq_targetAvailable_or_sourceName
      node environment targetOccurrence available
  have classToTarget : profile.classSupport.classAvailable
      (environment.occurrenceSlot witness.ancestry.sourcePosition) <:+
        rhoStaticContextReflectiveAvailable available
          targetOccurrence.context := by
    rcases ancestry with sameAvailable | exposure
    · rw [occurrenceAvailable, sameAvailable] at classToAuthored
      exact classToAuthored
    · rw [occurrenceAvailable, exposure.1] at classToAuthored
      have classEmpty : profile.classSupport.classAvailable
          (environment.occurrenceSlot witness.ancestry.sourcePosition) = [] :=
        classToAuthored.eq_nil
      rw [classEmpty]
      exact List.nil_suffix
  have targetName := rhoCanonicalOccurrenceSupportWitness_targetName node
    environment profile targetOccurrence
  rw [targetName]
  rw [profile.semanticInputSupport_atomName]
  exact classToTarget

/-- The canonical source frame is typed and safe for the exact occurrence-GCS
support, not only for the coarser restoration support carried by the original
atom environment. -/
theorem semanticCanonicalizedSourceFrame_supportSafeAt_quoteLocalGCS
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (support : ContextSupport.Support) (available : List TypeExpr)
    (binderImage : TypeExpr → TypeExpr)
    (childrenPreserve : CostStaticBoundaryChildReflectiveSupportPreserving
      node.boundaryTable values support binderImage)
    (inputSafe : node.term.2.1.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support available binderImage) :
    let environment := CostStaticAtomEnvironment.ofInventory inventory
    let profile := quoteLocalOccurrenceSupportProfile node values inventory
      support available binderImage childrenPreserve inputSafe
    ∃ sourceNormalized : WellSorted.HasTypeWithConstructors rhoCalc
        (· ∈ rhoContinuationRetyping.wrappedLabels)
        environment.sourceAtomFreeContext node.sourceBound
        (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
          rhoReflectivePresentation node.targetBound.length 0
          (node.reifiedSourceFrame environment).1)
        (.base node.sourceSort.1),
      sourceNormalized.toHasType.ReflectiveSupportSafeAt rhoReflectionProfile
        profile.semanticInputSupport available
          (mapTypeExpr (color.symbols rhoCIGSLT)) := by
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  let profile := quoteLocalOccurrenceSupportProfile node values inventory
    support available binderImage childrenPreserve inputSafe
  let sourceSupported := node.reifiedSourceFrame_supported environment
  have sourceSafe : sourceSupported.toHasType.ReflectiveSupportSafeAt
      rhoReflectionProfile environment.sourceAtomSupport node.targetBound
      (mapTypeExpr (color.symbols rhoCIGSLT)) :=
    (node.reifiedSourceFrame_supportSafe environment).castTyping
  obtain ⟨sourceNormalized, _sourceNormalizedSafe⟩ :=
    rhoCanonicalizeByDepths_hasTypeWithConstructors
      (sourceSemanticPatternKeyAt node environment) 0 sourceSupported
        sourceSafe (by trivial)
          (node.reifiedSourceFrame environment).2.1.2.2.1
  have bounded : RhoStaticOccurrenceSupportBounded
      profile.semanticInputSupport available
      (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
        rhoReflectivePresentation node.targetBound.length 0
        (node.reifiedSourceFrame environment).1) :=
    semanticCanonicalizedSourcePattern_supportBounded node values inventory
      support available binderImage childrenPreserve inputSafe
  have safe :=
    sourceNormalized.toHasType.rhoStaticFrame_supportSafe_of_occurrences
      (semanticCanonicalizedSourcePattern_binderFree node environment) bounded
      (binderImage := mapTypeExpr (color.symbols rhoCIGSLT))
  exact ⟨sourceNormalized, safe⟩

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
mutual
  /-- Binder-free reflective-support evidence is independent of the selected
  interpretation of binder types. -/
  theorem WellSorted.HasType.ReflectiveSupportSafeAt.rhoStaticFrame_changeBinderImage
      {language : LanguageDef} {free : WellSorted.FreeTypeContext}
      {profile : ReflectionProfile} {support : ContextSupport.Support}
      {bound available : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      {typed : WellSorted.HasType language free bound pattern type}
      {sourceImage : TypeExpr → TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt profile support available
        sourceImage)
      (frameFree : rhoStaticFrameBinderFree pattern = true)
      (targetImage : TypeExpr → TypeExpr) :
      typed.ReflectiveSupportSafeAt profile support available targetImage := by
    cases safe with
    | bvar lookup currentAvailable => exact .bvar lookup currentAvailable
    | fvar lookup currentAvailable shape =>
        exact .fvar lookup currentAvailable shape
    | @constructorQuote bound rule arguments membership notBare argumentsTyped
        currentAvailable binderImage quoted argumentsSafe =>
        have argumentsFree : rhoStaticFrameListBinderFree arguments = true := by
          simpa [rhoStaticFrameBinderFree] using frameFree
        exact .constructorQuote (membership := membership)
          (notBare := notBare) quoted
          (argumentsSafe.rhoStaticFrame_changeBinderImage argumentsFree
            targetImage)
    | @constructorOrdinary bound rule arguments membership notBare
        argumentsTyped currentAvailable binderImage ordinary argumentsSafe =>
        have argumentsFree : rhoStaticFrameListBinderFree arguments = true := by
          simpa [rhoStaticFrameBinderFree] using frameFree
        exact .constructorOrdinary (membership := membership)
          (notBare := notBare) ordinary
          (argumentsSafe.rhoStaticFrame_changeBinderImage argumentsFree
            targetImage)
    | lambda bodySafe => simp [rhoStaticFrameBinderFree] at frameFree
    | multiLambda bodySafe => simp [rhoStaticFrameBinderFree] at frameFree
    | subst bodySafe replacementSafe =>
        simp [rhoStaticFrameBinderFree] at frameFree
    | @collection bound collectionType elements rest elementType elementsTyped
        currentAvailable binderImage elementsSafe =>
        have elementsFree : rhoStaticFrameListBinderFree elements = true := by
          simpa [rhoStaticFrameBinderFree] using frameFree
        exact .collection
          (elementsSafe.rhoStaticFrame_changeBinderImage elementsFree
            targetImage)
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType membership parameterShape elementsTyped
        currentAvailable binderImage elementsSafe =>
        have elementsFree : rhoStaticFrameListBinderFree elements = true := by
          simpa [rhoStaticFrameBinderFree] using frameFree
        exact .collectionConstructor (membership := membership)
          (parameterShape := parameterShape)
          (elementsSafe.rhoStaticFrame_changeBinderImage elementsFree
            targetImage)
  termination_by 3 * sizeOf pattern + 2

  /-- Ordered-argument companion to binder-image independence. -/
  theorem WellSorted.ArgumentsHaveTypes.ReflectiveSupportSafeAt.rhoStaticFrame_changeBinderImage
      {language : LanguageDef} {free : WellSorted.FreeTypeContext}
      {profile : ReflectionProfile} {support : ContextSupport.Support}
      {bound available : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      {typed : WellSorted.ArgumentsHaveTypes language free bound arguments
        parameters}
      {sourceImage : TypeExpr → TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt profile support available
        sourceImage)
      (frameFree : rhoStaticFrameListBinderFree arguments = true)
      (targetImage : TypeExpr → TypeExpr) :
      typed.ReflectiveSupportSafeAt profile support available targetImage := by
    cases safe with
    | nil => exact .nil bound available
    | @cons bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped
        currentAvailable binderImage argumentSafe argumentsSafe =>
        have freeParts : rhoStaticFrameBinderFree argument = true ∧
            rhoStaticFrameListBinderFree arguments = true := by
          simpa [rhoStaticFrameListBinderFree] using frameFree
        exact .cons (representation := representation)
          (parameterType := parameterType)
          (argumentSafe.rhoStaticFrame_changeBinderImage freeParts.1
            targetImage)
          (argumentsSafe.rhoStaticFrame_changeBinderImage freeParts.2
            targetImage)
  termination_by 3 * sizeOf arguments + 1

  /-- Homogeneous-element companion to binder-image independence. -/
  theorem WellSorted.ElementsHaveType.ReflectiveSupportSafeAt.rhoStaticFrame_changeBinderImage
      {language : LanguageDef} {free : WellSorted.FreeTypeContext}
      {profile : ReflectionProfile} {support : ContextSupport.Support}
      {bound available : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      {typed : WellSorted.ElementsHaveType language free bound elements
        elementType}
      {sourceImage : TypeExpr → TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt profile support available
        sourceImage)
      (frameFree : rhoStaticFrameListBinderFree elements = true)
      (targetImage : TypeExpr → TypeExpr) :
      typed.ReflectiveSupportSafeAt profile support available targetImage := by
    cases safe with
    | nil => exact .nil bound elementType available
    | @cons bound element elements elementType elementTyped elementsTyped
        currentAvailable binderImage elementSafe elementsSafe =>
        have freeParts : rhoStaticFrameBinderFree element = true ∧
            rhoStaticFrameListBinderFree elements = true := by
          simpa [rhoStaticFrameListBinderFree] using frameFree
        exact .cons
          (elementSafe.rhoStaticFrame_changeBinderImage freeParts.1
            targetImage)
          (elementsSafe.rhoStaticFrame_changeBinderImage freeParts.2
            targetImage)
  termination_by 3 * sizeOf elements + 1

  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega
end

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
mutual
  /-- A binder-free static frame whose reflective availability is either its
  complete typing context or the sealed context is aligned with substitution
  by its own support.  This is the exact depth invariant used by restoration;
  no equality between caller support and restoration support is assumed. -/
  theorem WellSorted.HasType.ReflectiveSupportSafeAt.rhoStaticFrame_selfAligned
      {language : LanguageDef} {free : WellSorted.FreeTypeContext}
      {profile : ReflectionProfile} {support : ContextSupport.Support}
      {bound available : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      {typed : WellSorted.HasType language free bound pattern type}
      {binderImage : TypeExpr → TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt profile support available
        binderImage)
      (frameFree : rhoStaticFrameBinderFree pattern = true)
      (rootOrSealed : available = bound ∨ available = []) :
      WellSorted.ReflectiveSupportSubstitutionAlignedAt support safe := by
    cases safe with
    | bvar lookup currentAvailable => exact .bvar
    | @fvar bound name type lookup currentAvailable binderImage shape =>
        rcases rootOrSealed with root | sealed
        · subst currentAvailable
          obtain ⟨active, availableShape⟩ := shape
          refine .fvar ⟨active, [], ?_, ?_⟩
          · simpa using availableShape.symm
          · have lengths := congrArg List.length availableShape
            simp only [List.length_append] at lengths ⊢
            omega
        · subst currentAvailable
          obtain ⟨active, availableShape⟩ := shape
          have emptyParts : active = [] ∧ support name = [] :=
            List.append_eq_nil_iff.mp availableShape.symm
          refine .fvar ⟨[], bound, ?_, by simp⟩
          simp [emptyParts.2]
    | @constructorQuote bound rule arguments membership notBare argumentsTyped
        currentAvailable binderImage quoted argumentsSafe =>
        have argumentsFree : rhoStaticFrameListBinderFree arguments = true := by
          simpa [rhoStaticFrameBinderFree] using frameFree
        exact .constructorQuote
          (argumentsSafe.rhoStaticFrame_selfAligned argumentsFree
            (Or.inr rfl))
    | @constructorOrdinary bound rule arguments membership notBare
        argumentsTyped currentAvailable binderImage ordinary argumentsSafe =>
        have argumentsFree : rhoStaticFrameListBinderFree arguments = true := by
          simpa [rhoStaticFrameBinderFree] using frameFree
        exact .constructorOrdinary
          (argumentsSafe.rhoStaticFrame_selfAligned argumentsFree rootOrSealed)
    | lambda bodySafe => simp [rhoStaticFrameBinderFree] at frameFree
    | multiLambda bodySafe => simp [rhoStaticFrameBinderFree] at frameFree
    | subst bodySafe replacementSafe =>
        simp [rhoStaticFrameBinderFree] at frameFree
    | @collection bound collectionType elements rest elementType elementsTyped
        currentAvailable binderImage elementsSafe =>
        have elementsFree : rhoStaticFrameListBinderFree elements = true := by
          simpa [rhoStaticFrameBinderFree] using frameFree
        exact .collection
          (elementsSafe.rhoStaticFrame_selfAligned elementsFree rootOrSealed)
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType membership parameterShape elementsTyped
        currentAvailable binderImage elementsSafe =>
        have elementsFree : rhoStaticFrameListBinderFree elements = true := by
          simpa [rhoStaticFrameBinderFree] using frameFree
        exact .collectionConstructor
          (elementsSafe.rhoStaticFrame_selfAligned elementsFree rootOrSealed)
  termination_by 3 * sizeOf pattern + 2

  theorem WellSorted.ArgumentsHaveTypes.ReflectiveSupportSafeAt.rhoStaticFrame_selfAligned
      {language : LanguageDef} {free : WellSorted.FreeTypeContext}
      {profile : ReflectionProfile} {support : ContextSupport.Support}
      {bound available : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      {typed : WellSorted.ArgumentsHaveTypes language free bound arguments
        parameters}
      {binderImage : TypeExpr → TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt profile support available
        binderImage)
      (frameFree : rhoStaticFrameListBinderFree arguments = true)
      (rootOrSealed : available = bound ∨ available = []) :
      WellSorted.ReflectiveArgumentsSupportSubstitutionAlignedAt support
        safe := by
    cases safe with
    | nil => exact .nil _ _
    | @cons bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped
        currentAvailable binderImage argumentSafe argumentsSafe =>
        have freeParts : rhoStaticFrameBinderFree argument = true ∧
            rhoStaticFrameListBinderFree arguments = true := by
          simpa [rhoStaticFrameListBinderFree] using frameFree
        exact .cons
          (argumentSafe.rhoStaticFrame_selfAligned freeParts.1 rootOrSealed)
          (argumentsSafe.rhoStaticFrame_selfAligned freeParts.2 rootOrSealed)
  termination_by 3 * sizeOf arguments + 1

  theorem WellSorted.ElementsHaveType.ReflectiveSupportSafeAt.rhoStaticFrame_selfAligned
      {language : LanguageDef} {free : WellSorted.FreeTypeContext}
      {profile : ReflectionProfile} {support : ContextSupport.Support}
      {bound available : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      {typed : WellSorted.ElementsHaveType language free bound elements
        elementType}
      {binderImage : TypeExpr → TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt profile support available
        binderImage)
      (frameFree : rhoStaticFrameListBinderFree elements = true)
      (rootOrSealed : available = bound ∨ available = []) :
      WellSorted.ReflectiveElementsSupportSubstitutionAlignedAt support
        safe := by
    cases safe with
    | nil => exact .nil _ _ _
    | @cons bound element elements elementType elementTyped elementsTyped
        currentAvailable binderImage elementSafe elementsSafe =>
        have freeParts : rhoStaticFrameBinderFree element = true ∧
            rhoStaticFrameListBinderFree elements = true := by
          simpa [rhoStaticFrameListBinderFree] using frameFree
        exact .cons
          (elementSafe.rhoStaticFrame_selfAligned freeParts.1 rootOrSealed)
          (elementsSafe.rhoStaticFrame_selfAligned freeParts.2 rootOrSealed)
  termination_by 3 * sizeOf elements + 1

  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega
end

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
mutual
  /-- Build occurrence-local assignment evidence from a positional callback.
  The embedding retains the exact root occurrence through every syntax
  constructor, including duplicate list members. -/
  theorem WellSorted.ReflectiveSupportSubstitutionAlignedAt.occurrenceValues_of
      {language : LanguageDef}
      {source target : WellSorted.FreeTypeContext}
      {typingSupport inputSupport outputSupport : ContextSupport.Support}
      {profile : ReflectionProfile}
      (assignment : WellSorted.SupportedAssignment language source target
        typingSupport)
      {bound available : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      {typed : WellSorted.HasType language source bound pattern type}
      {binderImage : TypeExpr → TypeExpr}
      {safe : typed.ReflectiveSupportSafeAt profile inputSupport available
        binderImage}
      (aligned : WellSorted.ReflectiveSupportSubstitutionAlignedAt
        typingSupport safe)
      {Root : Type}
      (embed : CostStaticFVarOccurrence pattern → Nat → Root)
      (valueSafe : ∀ {bound name type}
        {lookup : source name = some type} {available : List TypeExpr},
        Root →
          (assignment.typed lookup).ReflectiveSupportSafeAt profile
            outputSupport available binderImage) :
      WellSorted.ReflectiveSupportOccurrenceValuesSafeAt
        (profile := profile) (binderImage := binderImage) assignment
          outputSupport aligned := by
    cases aligned with
    | bvar => exact .bvar
    | @fvar bound name type lookup currentAvailable binderImage shape
        contextShape =>
        let point : CostStaticFVarOccurrence (.fvar name) :=
          ⟨name, .hole, .here⟩
        exact .fvar (valueSafe (embed point))
    | @constructorQuote bound rule arguments membership notBare argumentsTyped
        currentAvailable binderImage quoted argumentsSafe argumentsAligned =>
        exact .constructorQuote
          (argumentsAligned.occurrenceValues_of assignment
            (fun occurrence => embed (occurrence.inApply rule.label))
              valueSafe)
    | @constructorOrdinary bound rule arguments membership notBare
        argumentsTyped currentAvailable binderImage ordinary argumentsSafe
        argumentsAligned =>
        exact .constructorOrdinary
          (argumentsAligned.occurrenceValues_of assignment
            (fun occurrence => embed (occurrence.inApply rule.label))
              valueSafe)
    | @lambda bound binder body domain codomain bodyTyped currentAvailable
        binderImage bodySafe bodyAligned =>
        exact .lambda
          (bodyAligned.occurrenceValues_of assignment
            (fun occurrence => embed (occurrence.inContext
              (.lambda binder .hole))) valueSafe)
    | @multiLambda bound arity binders body domain codomain bodyTyped
        currentAvailable binderImage bodySafe bodyAligned =>
        exact .multiLambda
          (bodyAligned.occurrenceValues_of assignment
            (fun occurrence => embed (occurrence.inContext
              (.multiLambda arity binders .hole))) valueSafe)
    | @subst bound body replacement domain codomain bodyTyped replacementTyped
        currentAvailable binderImage bodySafe replacementSafe bodyAligned
        replacementAligned =>
        exact .subst
          (bodyAligned.occurrenceValues_of assignment
            (fun occurrence => embed (occurrence.inContext
              (.substBody .hole replacement))) valueSafe)
          (replacementAligned.occurrenceValues_of assignment
            (fun occurrence => embed (occurrence.inContext
              (.substReplacement body .hole))) valueSafe)
    | @collection bound collectionType elements rest elementType elementsTyped
        currentAvailable binderImage elementsSafe elementsAligned =>
        exact .collection
          (elementsAligned.occurrenceValues_of assignment
            (fun occurrence => embed
              (occurrence.inCollection collectionType rest)) valueSafe)
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType membership parameterShape elementsTyped
        currentAvailable binderImage elementsSafe elementsAligned =>
        exact .collectionConstructor
          (elementsAligned.occurrenceValues_of assignment
            (fun occurrence => embed
              (occurrence.inCollection collectionType rest)) valueSafe)
  termination_by 3 * sizeOf pattern + 2

  theorem WellSorted.ReflectiveArgumentsSupportSubstitutionAlignedAt.occurrenceValues_of
      {language : LanguageDef}
      {source target : WellSorted.FreeTypeContext}
      {typingSupport inputSupport outputSupport : ContextSupport.Support}
      {profile : ReflectionProfile}
      (assignment : WellSorted.SupportedAssignment language source target
        typingSupport)
      {bound available : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      {typed : WellSorted.ArgumentsHaveTypes language source bound arguments
        parameters}
      {binderImage : TypeExpr → TypeExpr}
      {safe : typed.ReflectiveSupportSafeAt profile inputSupport available
        binderImage}
      (aligned : WellSorted.ReflectiveArgumentsSupportSubstitutionAlignedAt
        typingSupport safe)
      {Root : Type}
      (embed : CostStaticFVarListOccurrence arguments → Root)
      (valueSafe : ∀ {bound name type}
        {lookup : source name = some type} {available : List TypeExpr},
        Root →
          (assignment.typed lookup).ReflectiveSupportSafeAt profile
            outputSupport available binderImage) :
      WellSorted.ReflectiveArgumentsSupportOccurrenceValuesSafeAt
        (profile := profile) (binderImage := binderImage) assignment
          outputSupport aligned := by
    cases aligned with
    | nil => exact .nil _ _
    | @cons bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped
        currentAvailable binderImage argumentSafe argumentsSafe
        argumentAligned argumentsAligned =>
        let embedHead : CostStaticFVarOccurrence argument → Root :=
          fun occurrence => embed
            { position := ⟨0, by simp⟩
              occurrence := occurrence }
        let embedTail : CostStaticFVarListOccurrence arguments → Root :=
          fun occurrence => embed
            { position := ⟨occurrence.position.val + 1, by
                simpa using occurrence.position.isLt⟩
              occurrence := occurrence.occurrence }
        exact .cons
          (argumentAligned.occurrenceValues_of assignment embedHead valueSafe)
          (argumentsAligned.occurrenceValues_of assignment embedTail valueSafe)
  termination_by 3 * sizeOf arguments + 1

  theorem WellSorted.ReflectiveElementsSupportSubstitutionAlignedAt.occurrenceValues_of
      {language : LanguageDef}
      {source target : WellSorted.FreeTypeContext}
      {typingSupport inputSupport outputSupport : ContextSupport.Support}
      {profile : ReflectionProfile}
      (assignment : WellSorted.SupportedAssignment language source target
        typingSupport)
      {bound available : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      {typed : WellSorted.ElementsHaveType language source bound elements
        elementType}
      {binderImage : TypeExpr → TypeExpr}
      {safe : typed.ReflectiveSupportSafeAt profile inputSupport available
        binderImage}
      (aligned : WellSorted.ReflectiveElementsSupportSubstitutionAlignedAt
        typingSupport safe)
      {Root : Type}
      (embed : CostStaticFVarListOccurrence elements → Root)
      (valueSafe : ∀ {bound name type}
        {lookup : source name = some type} {available : List TypeExpr},
        Root →
          (assignment.typed lookup).ReflectiveSupportSafeAt profile
            outputSupport available binderImage) :
      WellSorted.ReflectiveElementsSupportOccurrenceValuesSafeAt
        (profile := profile) (binderImage := binderImage) assignment
          outputSupport aligned := by
    cases aligned with
    | nil => exact .nil _ _ _
    | @cons bound element elements elementType elementTyped elementsTyped
        currentAvailable binderImage elementSafe elementsSafe elementAligned
        elementsAligned =>
        let embedHead : CostStaticFVarOccurrence element → Root :=
          fun occurrence => embed
            { position := ⟨0, by simp⟩
              occurrence := occurrence }
        let embedTail : CostStaticFVarListOccurrence elements → Root :=
          fun occurrence => embed
            { position := ⟨occurrence.position.val + 1, by
                simpa using occurrence.position.isLt⟩
              occurrence := occurrence.occurrence }
        exact .cons
          (elementAligned.occurrenceValues_of assignment embedHead valueSafe)
          (elementsAligned.occurrenceValues_of assignment embedTail valueSafe)
  termination_by 3 * sizeOf elements + 1

  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega
end

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
mutual
  /-- Substitute at the executor's actual depth while proving output support
  from exact positional leaf replacements.  Unlike the alignment interface,
  the leaf callback may discharge closed or quote-exposed values directly;
  it need not identify caller availability with the typing fibre. -/
  theorem WellSorted.HasType.ReflectiveSupportSafeAt.substituteAtPreservingReflectiveSupportFromOccurrences
      {language : LanguageDef}
      {source target : WellSorted.FreeTypeContext}
      {typingSupport inputSupport outputSupport : ContextSupport.Support}
      {profile : ReflectionProfile}
      (assignment : WellSorted.SupportedAssignment language source target
        typingSupport)
      {bound available : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      {typed : WellSorted.HasType language source bound pattern type}
      {binderImage : TypeExpr → TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt profile inputSupport available
        binderImage)
      (actualDepth : Nat)
      {Root : Type}
      (embed : CostStaticFVarOccurrence pattern → Root)
      (valueSafe : ∀ {bound name type}
        {lookup : source name = some type} {available : List TypeExpr},
        Root → (depth : Nat) →
          ∃ outputTyped : WellSorted.HasType language target bound
              (ReflectiveContextSupport.substituteAt profile typingSupport
                assignment.assignment depth (.fvar name)) type,
            outputTyped.ReflectiveSupportSafeAt profile outputSupport
              available binderImage) :
      ∃ outputTyped : WellSorted.HasType language target bound
          (ReflectiveContextSupport.substituteAt profile typingSupport
            assignment.assignment actualDepth pattern) type,
        outputTyped.ReflectiveSupportSafeAt profile outputSupport available
          binderImage := by
    cases safe with
    | @bvar bound index type lookup currentAvailable binderImage =>
        let outputTyped : WellSorted.HasType language target bound
            (.bvar index) type := .bvar lookup
        simpa [ReflectiveContextSupport.substituteAt] using
          (⟨outputTyped, WellSorted.HasType.ReflectiveSupportSafeAt.bvar
            (binderImage := binderImage) lookup available⟩)
    | @fvar bound name type lookup currentAvailable binderImage shape =>
        let point : CostStaticFVarOccurrence (.fvar name) :=
          ⟨name, .hole, .here⟩
        exact valueSafe (embed point actualDepth) actualDepth
    | @constructorQuote bound rule arguments membership notBare argumentsTyped
        currentAvailable binderImage quoted argumentsSafe =>
        obtain ⟨outputArguments, outputSafe⟩ :=
          argumentsSafe.substituteAtPreservingReflectiveSupportFromOccurrences
            assignment 0
              (fun occurrence depth =>
                embed (occurrence.inApply rule.label) depth)
                valueSafe
        let outputTyped := WellSorted.HasType.constructor membership notBare
          outputArguments
        simpa [ReflectiveContextSupport.substituteAt, quoted] using
          (⟨outputTyped,
            WellSorted.HasType.ReflectiveSupportSafeAt.constructorQuote
              (membership := membership) (notBare := notBare) quoted
                outputSafe⟩)
    | @constructorOrdinary bound rule arguments membership notBare
        argumentsTyped currentAvailable binderImage ordinary argumentsSafe =>
        obtain ⟨outputArguments, outputSafe⟩ :=
          argumentsSafe.substituteAtPreservingReflectiveSupportFromOccurrences
            assignment actualDepth
              (fun occurrence depth =>
                embed (occurrence.inApply rule.label) depth)
                valueSafe
        let outputTyped := WellSorted.HasType.constructor membership notBare
          outputArguments
        simpa [ReflectiveContextSupport.substituteAt, ordinary] using
          (⟨outputTyped,
            WellSorted.HasType.ReflectiveSupportSafeAt.constructorOrdinary
              (membership := membership) (notBare := notBare) ordinary
                outputSafe⟩)
    | @lambda bound binder body domain codomain bodyTyped currentAvailable
        binderImage bodySafe =>
        obtain ⟨outputBody, outputSafe⟩ :=
          bodySafe.substituteAtPreservingReflectiveSupportFromOccurrences
            assignment (actualDepth + 1)
              (fun occurrence depth => embed (occurrence.inContext
                (.lambda binder .hole)) depth) valueSafe
        let outputTyped := WellSorted.HasType.lambda (binder := binder)
          outputBody
        simpa [ReflectiveContextSupport.substituteAt] using
          (⟨outputTyped,
            WellSorted.HasType.ReflectiveSupportSafeAt.lambda outputSafe⟩)
    | @multiLambda bound arity binders body domain codomain bodyTyped
        currentAvailable binderImage bodySafe =>
        obtain ⟨outputBody, outputSafe⟩ :=
          bodySafe.substituteAtPreservingReflectiveSupportFromOccurrences
            assignment (actualDepth + arity)
              (fun occurrence depth => embed (occurrence.inContext
                (.multiLambda arity binders .hole)) depth) valueSafe
        let rawOutputTyped := WellSorted.HasType.multiLambda
          (binders := binders) outputBody
        let outputTyped : WellSorted.HasType language target bound
            (ReflectiveContextSupport.substituteAt profile typingSupport
              assignment.assignment actualDepth
                (.multiLambda arity binders body))
            (.arrow (.multiBinder domain) codomain) := by
          simpa only [ReflectiveContextSupport.substituteAt, Nat.add_comm]
            using rawOutputTyped
        have rawOutputSafe :=
          WellSorted.HasType.ReflectiveSupportSafeAt.multiLambda
            (binders := binders) outputSafe
        have outputSafe' : outputTyped.ReflectiveSupportSafeAt profile
            outputSupport available binderImage := by
          apply WellSorted.HasType.ReflectiveSupportSafeAt.castTyping
          simpa only [ReflectiveContextSupport.substituteAt, Nat.add_comm]
            using rawOutputSafe
          exact outputTyped
        exact ⟨outputTyped, outputSafe'⟩
    | @subst bound body replacement domain codomain bodyTyped replacementTyped
        currentAvailable binderImage bodySafe replacementSafe =>
        obtain ⟨outputBody, outputBodySafe⟩ :=
          bodySafe.substituteAtPreservingReflectiveSupportFromOccurrences
            assignment (actualDepth + 1)
              (fun occurrence depth => embed (occurrence.inContext
                (.substBody .hole replacement)) depth) valueSafe
        obtain ⟨outputReplacement, outputReplacementSafe⟩ :=
          replacementSafe.substituteAtPreservingReflectiveSupportFromOccurrences
            assignment actualDepth
              (fun occurrence depth => embed (occurrence.inContext
                (.substReplacement body .hole)) depth) valueSafe
        let outputTyped := WellSorted.HasType.subst outputBody
          outputReplacement
        simpa [ReflectiveContextSupport.substituteAt] using
          (⟨outputTyped, WellSorted.HasType.ReflectiveSupportSafeAt.subst
            outputBodySafe outputReplacementSafe⟩)
    | @collection bound collectionType elements rest elementType elementsTyped
        currentAvailable binderImage elementsSafe =>
        obtain ⟨outputElements, outputSafe⟩ :=
          elementsSafe.substituteAtPreservingReflectiveSupportFromOccurrences
            assignment actualDepth
              (fun occurrence depth => embed
                (occurrence.inCollection collectionType rest) depth) valueSafe
        let outputTyped := WellSorted.HasType.collection
          (collectionType := collectionType) (rest := rest) outputElements
        simpa only [ReflectiveContextSupport.substituteAt] using
          (⟨outputTyped,
            WellSorted.HasType.ReflectiveSupportSafeAt.collection outputSafe⟩)
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType membership parameterShape elementsTyped
        currentAvailable binderImage elementsSafe =>
        obtain ⟨outputElements, outputSafe⟩ :=
          elementsSafe.substituteAtPreservingReflectiveSupportFromOccurrences
            assignment actualDepth
              (fun occurrence depth => embed
                (occurrence.inCollection collectionType rest) depth) valueSafe
        let outputTyped := WellSorted.HasType.collectionConstructor
          (rest := rest) membership parameterShape outputElements
        simpa only [ReflectiveContextSupport.substituteAt] using
          (⟨outputTyped,
            WellSorted.HasType.ReflectiveSupportSafeAt.collectionConstructor
              (membership := membership) (parameterShape := parameterShape)
                outputSafe⟩)
  termination_by 3 * sizeOf pattern + 2

  theorem WellSorted.ArgumentsHaveTypes.ReflectiveSupportSafeAt.substituteAtPreservingReflectiveSupportFromOccurrences
      {language : LanguageDef}
      {source target : WellSorted.FreeTypeContext}
      {typingSupport inputSupport outputSupport : ContextSupport.Support}
      {profile : ReflectionProfile}
      (assignment : WellSorted.SupportedAssignment language source target
        typingSupport)
      {bound available : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      {typed : WellSorted.ArgumentsHaveTypes language source bound arguments
        parameters}
      {binderImage : TypeExpr → TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt profile inputSupport available
        binderImage)
      (actualDepth : Nat)
      {Root : Type}
      (embed : CostStaticFVarListOccurrence arguments → Nat → Root)
      (valueSafe : ∀ {bound name type}
        {lookup : source name = some type} {available : List TypeExpr},
        Root → (depth : Nat) →
          ∃ outputTyped : WellSorted.HasType language target bound
              (ReflectiveContextSupport.substituteAt profile typingSupport
                assignment.assignment depth (.fvar name)) type,
            outputTyped.ReflectiveSupportSafeAt profile outputSupport
              available binderImage) :
      ∃ outputTyped : WellSorted.ArgumentsHaveTypes language target bound
          (arguments.map (ReflectiveContextSupport.substituteAt profile
            typingSupport assignment.assignment actualDepth)) parameters,
        outputTyped.ReflectiveSupportSafeAt profile outputSupport available
          binderImage := by
    cases safe with
    | nil => exact ⟨. nil, .nil _ _⟩
    | @cons bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped
        currentAvailable binderImage argumentSafe argumentsSafe =>
        let embedHead : CostStaticFVarOccurrence argument → Nat → Root :=
          fun occurrence depth => embed
            { position := ⟨0, by simp⟩
              occurrence := occurrence } depth
        let embedTail : CostStaticFVarListOccurrence arguments → Nat → Root :=
          fun occurrence depth => embed
            { position := ⟨occurrence.position.val + 1, by
                simpa using occurrence.position.isLt⟩
              occurrence := occurrence.occurrence } depth
        obtain ⟨outputArgument, outputArgumentSafe⟩ :=
          argumentSafe.substituteAtPreservingReflectiveSupportFromOccurrences
            assignment actualDepth embedHead valueSafe
        obtain ⟨outputArguments, outputArgumentsSafe⟩ :=
          argumentsSafe.substituteAtPreservingReflectiveSupportFromOccurrences
            assignment actualDepth embedTail valueSafe
        let outputRepresentation := representation.substituteReflectiveAt
          profile parameter argument typingSupport assignment.assignment
            actualDepth
        let outputTyped := WellSorted.ArgumentsHaveTypes.cons
          outputRepresentation parameterType outputArgument outputArguments
        exact ⟨outputTyped, .cons (representation := outputRepresentation)
          (parameterType := parameterType) outputArgumentSafe
            outputArgumentsSafe⟩
  termination_by 3 * sizeOf arguments + 1

  theorem WellSorted.ElementsHaveType.ReflectiveSupportSafeAt.substituteAtPreservingReflectiveSupportFromOccurrences
      {language : LanguageDef}
      {source target : WellSorted.FreeTypeContext}
      {typingSupport inputSupport outputSupport : ContextSupport.Support}
      {profile : ReflectionProfile}
      (assignment : WellSorted.SupportedAssignment language source target
        typingSupport)
      {bound available : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      {typed : WellSorted.ElementsHaveType language source bound elements
        elementType}
      {binderImage : TypeExpr → TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt profile inputSupport available
        binderImage)
      (actualDepth : Nat)
      {Root : Type}
      (embed : CostStaticFVarListOccurrence elements → Nat → Root)
      (valueSafe : ∀ {bound name type}
        {lookup : source name = some type} {available : List TypeExpr},
        Root → (depth : Nat) →
          ∃ outputTyped : WellSorted.HasType language target bound
              (ReflectiveContextSupport.substituteAt profile typingSupport
                assignment.assignment depth (.fvar name)) type,
            outputTyped.ReflectiveSupportSafeAt profile outputSupport
              available binderImage) :
      ∃ outputTyped : WellSorted.ElementsHaveType language target bound
          (elements.map (ReflectiveContextSupport.substituteAt profile
            typingSupport assignment.assignment actualDepth)) elementType,
        outputTyped.ReflectiveSupportSafeAt profile outputSupport available
          binderImage := by
    cases safe with
    | nil => exact ⟨.nil, .nil _ _ _⟩
    | @cons bound element elements elementType elementTyped elementsTyped
        currentAvailable binderImage elementSafe elementsSafe =>
        let embedHead : CostStaticFVarOccurrence element → Nat → Root :=
          fun occurrence depth => embed
            { position := ⟨0, by simp⟩
              occurrence := occurrence } depth
        let embedTail : CostStaticFVarListOccurrence elements → Nat → Root :=
          fun occurrence depth => embed
            { position := ⟨occurrence.position.val + 1, by
                simpa using occurrence.position.isLt⟩
              occurrence := occurrence.occurrence } depth
        obtain ⟨outputElement, outputElementSafe⟩ :=
          elementSafe.substituteAtPreservingReflectiveSupportFromOccurrences
            assignment actualDepth embedHead valueSafe
        obtain ⟨outputElements, outputElementsSafe⟩ :=
          elementsSafe.substituteAtPreservingReflectiveSupportFromOccurrences
            assignment actualDepth embedTail valueSafe
        let outputTyped := WellSorted.ElementsHaveType.cons outputElement
          outputElements
        exact ⟨outputTyped, .cons outputElementSafe outputElementsSafe⟩
  termination_by 3 * sizeOf elements + 1

  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega
end

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
mutual
  /-- Binder-free rho substitution may use the executor's actual quote-local
  depth for typing while preserving an independent caller-relative support.
  The two availabilities are intentionally separate. -/
  theorem WellSorted.HasType.ReflectiveSupportSafeAt.rhoStaticFrame_substituteAtFromOccurrences
      {source target : WellSorted.FreeTypeContext}
      {typingSupport inputSupport outputSupport : ContextSupport.Support}
      (assignment : WellSorted.SupportedAssignment rhoCalc source target
        typingSupport)
      {bound callerAvailable : List TypeExpr} {pattern : Pattern}
      {type : TypeExpr}
      {typed : WellSorted.HasType rhoCalc source bound pattern type}
      {binderImage : TypeExpr → TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt rhoReflectionProfile inputSupport
        callerAvailable binderImage)
      (frameFree : rhoStaticFrameBinderFree pattern = true)
      (actualAvailable sealed : List TypeExpr)
      (boundShape : bound = actualAvailable ++ sealed)
      (actualBounded : RhoStaticOccurrenceSupportBounded typingSupport
        actualAvailable pattern)
      {Root : Type}
      (embed : CostStaticFVarOccurrence pattern → Root)
      (valueSafe : ∀ {bound name type}
        {lookup : source name = some type} {available : List TypeExpr},
        Root →
          (assignment.typed lookup).ReflectiveSupportSafeAt
            rhoReflectionProfile outputSupport available binderImage) :
      ∃ outputTyped : WellSorted.HasType rhoCalc target bound
          (ReflectiveContextSupport.substituteAt rhoReflectionProfile
            typingSupport assignment.assignment actualAvailable.length
              pattern) type,
        outputTyped.ReflectiveSupportSafeAt rhoReflectionProfile outputSupport
          callerAvailable binderImage := by
    cases safe with
    | @bvar bound index type lookup currentAvailable binderImage =>
        let outputTyped : WellSorted.HasType rhoCalc target bound
            (.bvar index) type := .bvar lookup
        simpa [ReflectiveContextSupport.substituteAt] using
          (⟨outputTyped, WellSorted.HasType.ReflectiveSupportSafeAt.bvar
            (binderImage := binderImage) lookup callerAvailable⟩)
    | @fvar bound name type lookup currentAvailable binderImage shape =>
        let point : CostStaticFVarOccurrence (.fvar name) :=
          ⟨name, .hole, .here⟩
        have actualSuffix := actualBounded point
        obtain ⟨active, actualShape⟩ :=
          List.suffix_iff_exists_eq_append.mp
            (by simpa [rhoStaticContextReflectiveAvailable] using actualSuffix)
        have assignedSafe := valueSafe (embed point)
        obtain ⟨liftedTyped, liftedSafe⟩ := assignedSafe.liftBVars_insert
          [] (typingSupport name) active rfl
        let liftedTyped' : WellSorted.HasType rhoCalc target
            (active ++ typingSupport name)
            (liftBVars 0 active.length (assignment.assignment name)) type := by
          simpa only [List.nil_append, List.length_nil] using liftedTyped
        have liftedSafe' : liftedTyped'.ReflectiveSupportSafeAt
            rhoReflectionProfile outputSupport callerAvailable binderImage := by
          apply WellSorted.HasType.ReflectiveSupportSafeAt.castTyping
          simpa only [List.nil_append, List.length_nil] using liftedSafe
        obtain ⟨extendedTyped, extendedSafe⟩ := liftedSafe'.extendOuter sealed
        have shiftEquality :
            actualAvailable.length - (typingSupport name).length =
              active.length := by
          rw [actualShape]
          simp only [List.length_append]
          omega
        have packaged : ∃ outputTyped : WellSorted.HasType rhoCalc target
            ((active ++ typingSupport name) ++ sealed)
            (ReflectiveContextSupport.substituteAt rhoReflectionProfile
              typingSupport assignment.assignment actualAvailable.length
                (.fvar name)) type,
          outputTyped.ReflectiveSupportSafeAt rhoReflectionProfile
            outputSupport callerAvailable binderImage := by
          simpa only [ReflectiveContextSupport.substituteAt, shiftEquality]
            using (⟨extendedTyped, extendedSafe⟩)
        rw [actualShape] at boundShape
        simpa only [boundShape] using packaged
    | @constructorQuote bound rule arguments membership notBare argumentsTyped
        currentAvailable binderImage quoted argumentsSafe =>
        have argumentsFree : rhoStaticFrameListBinderFree arguments = true := by
          simpa [rhoStaticFrameBinderFree] using frameFree
        have actualArgumentsBounded :=
          rhoStaticListOccurrenceSupportBounded_of_apply typingSupport
            actualAvailable rule.label arguments actualBounded
        have actualArgumentsBounded' : RhoStaticListOccurrenceSupportBounded
            typingSupport [] arguments := by
          simpa [quoted] using actualArgumentsBounded
        obtain ⟨outputArguments, outputSafe⟩ :=
          argumentsSafe.rhoStaticFrame_substituteAtFromOccurrences assignment
            argumentsFree [] bound (by simp) actualArgumentsBounded'
              (fun occurrence => embed (occurrence.inApply rule.label))
                valueSafe
        let outputTyped := WellSorted.HasType.constructor membership notBare
          outputArguments
        simpa [ReflectiveContextSupport.substituteAt, quoted] using
          (⟨outputTyped,
            WellSorted.HasType.ReflectiveSupportSafeAt.constructorQuote
              (membership := membership) (notBare := notBare) quoted
                outputSafe⟩)
    | @constructorOrdinary bound rule arguments membership notBare
        argumentsTyped currentAvailable binderImage ordinary argumentsSafe =>
        have argumentsFree : rhoStaticFrameListBinderFree arguments = true := by
          simpa [rhoStaticFrameBinderFree] using frameFree
        have actualArgumentsBounded :=
          rhoStaticListOccurrenceSupportBounded_of_apply typingSupport
            actualAvailable rule.label arguments actualBounded
        have actualArgumentsBounded' : RhoStaticListOccurrenceSupportBounded
            typingSupport actualAvailable arguments := by
          simpa [ordinary] using actualArgumentsBounded
        obtain ⟨outputArguments, outputSafe⟩ :=
          argumentsSafe.rhoStaticFrame_substituteAtFromOccurrences assignment
            argumentsFree actualAvailable sealed boundShape
              actualArgumentsBounded'
                (fun occurrence => embed (occurrence.inApply rule.label))
                  valueSafe
        let outputTyped := WellSorted.HasType.constructor membership notBare
          outputArguments
        simpa [ReflectiveContextSupport.substituteAt, ordinary] using
          (⟨outputTyped,
            WellSorted.HasType.ReflectiveSupportSafeAt.constructorOrdinary
              (membership := membership) (notBare := notBare) ordinary
                outputSafe⟩)
    | lambda => simp [rhoStaticFrameBinderFree] at frameFree
    | multiLambda => simp [rhoStaticFrameBinderFree] at frameFree
    | subst => simp [rhoStaticFrameBinderFree] at frameFree
    | @collection bound collectionType elements rest elementType elementsTyped
        currentAvailable binderImage elementsSafe =>
        have elementsFree : rhoStaticFrameListBinderFree elements = true := by
          simpa [rhoStaticFrameBinderFree] using frameFree
        have actualElementsBounded :=
          rhoStaticListOccurrenceSupportBounded_of_collection typingSupport
            actualAvailable collectionType elements rest actualBounded
        obtain ⟨outputElements, outputSafe⟩ :=
          elementsSafe.rhoStaticFrame_substituteAtFromOccurrences assignment
            elementsFree actualAvailable sealed boundShape
              actualElementsBounded
                (fun occurrence => embed
                  (occurrence.inCollection collectionType rest)) valueSafe
        let outputTyped := WellSorted.HasType.collection
          (collectionType := collectionType) (rest := rest) outputElements
        simpa only [ReflectiveContextSupport.substituteAt] using
          (⟨outputTyped,
            WellSorted.HasType.ReflectiveSupportSafeAt.collection outputSafe⟩)
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType membership parameterShape elementsTyped
        currentAvailable binderImage elementsSafe =>
        have elementsFree : rhoStaticFrameListBinderFree elements = true := by
          simpa [rhoStaticFrameBinderFree] using frameFree
        have actualElementsBounded :=
          rhoStaticListOccurrenceSupportBounded_of_collection typingSupport
            actualAvailable collectionType elements rest actualBounded
        obtain ⟨outputElements, outputSafe⟩ :=
          elementsSafe.rhoStaticFrame_substituteAtFromOccurrences assignment
            elementsFree actualAvailable sealed boundShape
              actualElementsBounded
                (fun occurrence => embed
                  (occurrence.inCollection collectionType rest)) valueSafe
        let outputTyped := WellSorted.HasType.collectionConstructor
          (rest := rest) membership parameterShape outputElements
        simpa only [ReflectiveContextSupport.substituteAt] using
          (⟨outputTyped,
            WellSorted.HasType.ReflectiveSupportSafeAt.collectionConstructor
              (membership := membership) (parameterShape := parameterShape)
                outputSafe⟩)
  termination_by 3 * sizeOf pattern + 2

  theorem WellSorted.ArgumentsHaveTypes.ReflectiveSupportSafeAt.rhoStaticFrame_substituteAtFromOccurrences
      {source target : WellSorted.FreeTypeContext}
      {typingSupport inputSupport outputSupport : ContextSupport.Support}
      (assignment : WellSorted.SupportedAssignment rhoCalc source target
        typingSupport)
      {bound callerAvailable : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      {typed : WellSorted.ArgumentsHaveTypes rhoCalc source bound arguments
        parameters}
      {binderImage : TypeExpr → TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt rhoReflectionProfile inputSupport
        callerAvailable binderImage)
      (frameFree : rhoStaticFrameListBinderFree arguments = true)
      (actualAvailable sealed : List TypeExpr)
      (boundShape : bound = actualAvailable ++ sealed)
      (actualBounded : RhoStaticListOccurrenceSupportBounded typingSupport
        actualAvailable arguments)
      {Root : Type}
      (embed : CostStaticFVarListOccurrence arguments → Root)
      (valueSafe : ∀ {bound name type}
        {lookup : source name = some type} {available : List TypeExpr},
        Root →
          (assignment.typed lookup).ReflectiveSupportSafeAt
            rhoReflectionProfile outputSupport available binderImage) :
      ∃ outputTyped : WellSorted.ArgumentsHaveTypes rhoCalc target bound
          (arguments.map (ReflectiveContextSupport.substituteAt
            rhoReflectionProfile typingSupport assignment.assignment
              actualAvailable.length)) parameters,
        outputTyped.ReflectiveSupportSafeAt rhoReflectionProfile outputSupport
          callerAvailable binderImage := by
    cases safe with
    | nil => exact ⟨.nil, .nil _ _⟩
    | @cons bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped
        currentAvailable binderImage argumentSafe argumentsSafe =>
        have freeParts : rhoStaticFrameBinderFree argument = true ∧
            rhoStaticFrameListBinderFree arguments = true := by
          simpa [rhoStaticFrameListBinderFree] using frameFree
        obtain ⟨outputArgument, outputArgumentSafe⟩ :=
          argumentSafe.rhoStaticFrame_substituteAtFromOccurrences assignment
            freeParts.1 actualAvailable sealed boundShape
              (rhoStaticOccurrenceSupportBounded_head typingSupport
                actualAvailable argument arguments actualBounded)
              (fun occurrence => embed
                { position := ⟨0, by simp⟩
                  occurrence := occurrence }) valueSafe
        obtain ⟨outputArguments, outputArgumentsSafe⟩ :=
          argumentsSafe.rhoStaticFrame_substituteAtFromOccurrences assignment
            freeParts.2 actualAvailable sealed boundShape
              (rhoStaticListOccurrenceSupportBounded_tail typingSupport
                actualAvailable argument arguments actualBounded)
              (fun occurrence => embed
                { position := Fin.succ occurrence.position
                  occurrence := occurrence.occurrence }) valueSafe
        let outputRepresentation := representation.substituteReflectiveAt
          rhoReflectionProfile parameter argument typingSupport
            assignment.assignment actualAvailable.length
        let outputTyped := WellSorted.ArgumentsHaveTypes.cons
          outputRepresentation parameterType outputArgument outputArguments
        exact ⟨outputTyped, .cons (representation := outputRepresentation)
          (parameterType := parameterType) outputArgumentSafe
            outputArgumentsSafe⟩
  termination_by 3 * sizeOf arguments + 1

  theorem WellSorted.ElementsHaveType.ReflectiveSupportSafeAt.rhoStaticFrame_substituteAtFromOccurrences
      {source target : WellSorted.FreeTypeContext}
      {typingSupport inputSupport outputSupport : ContextSupport.Support}
      (assignment : WellSorted.SupportedAssignment rhoCalc source target
        typingSupport)
      {bound callerAvailable : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      {typed : WellSorted.ElementsHaveType rhoCalc source bound elements
        elementType}
      {binderImage : TypeExpr → TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt rhoReflectionProfile inputSupport
        callerAvailable binderImage)
      (frameFree : rhoStaticFrameListBinderFree elements = true)
      (actualAvailable sealed : List TypeExpr)
      (boundShape : bound = actualAvailable ++ sealed)
      (actualBounded : RhoStaticListOccurrenceSupportBounded typingSupport
        actualAvailable elements)
      {Root : Type}
      (embed : CostStaticFVarListOccurrence elements → Root)
      (valueSafe : ∀ {bound name type}
        {lookup : source name = some type} {available : List TypeExpr},
        Root →
          (assignment.typed lookup).ReflectiveSupportSafeAt
            rhoReflectionProfile outputSupport available binderImage) :
      ∃ outputTyped : WellSorted.ElementsHaveType rhoCalc target bound
          (elements.map (ReflectiveContextSupport.substituteAt
            rhoReflectionProfile typingSupport assignment.assignment
              actualAvailable.length)) elementType,
        outputTyped.ReflectiveSupportSafeAt rhoReflectionProfile outputSupport
          callerAvailable binderImage := by
    cases safe with
    | nil => exact ⟨.nil, .nil _ _ _⟩
    | @cons bound element elements elementType elementTyped elementsTyped
        currentAvailable binderImage elementSafe elementsSafe =>
        have freeParts : rhoStaticFrameBinderFree element = true ∧
            rhoStaticFrameListBinderFree elements = true := by
          simpa [rhoStaticFrameListBinderFree] using frameFree
        obtain ⟨outputElement, outputElementSafe⟩ :=
          elementSafe.rhoStaticFrame_substituteAtFromOccurrences assignment
            freeParts.1 actualAvailable sealed boundShape
              (rhoStaticOccurrenceSupportBounded_head typingSupport
                actualAvailable element elements actualBounded)
              (fun occurrence => embed
                { position := ⟨0, by simp⟩
                  occurrence := occurrence }) valueSafe
        obtain ⟨outputElements, outputElementsSafe⟩ :=
          elementsSafe.rhoStaticFrame_substituteAtFromOccurrences assignment
            freeParts.2 actualAvailable sealed boundShape
              (rhoStaticListOccurrenceSupportBounded_tail typingSupport
                actualAvailable element elements actualBounded)
              (fun occurrence => embed
                { position := Fin.succ occurrence.position
                  occurrence := occurrence.occurrence }) valueSafe
        let outputTyped := WellSorted.ElementsHaveType.cons outputElement
          outputElements
        exact ⟨outputTyped, .cons outputElementSafe outputElementsSafe⟩
  termination_by 3 * sizeOf elements + 1

  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega
end

mutual
  /-- Static symbol mapping changes labels and sorts but introduces no binder
  syntax. -/
  theorem rhoStaticFrameBinderFree_mapPattern
      (symbols : LanguageDefSymbolMap) : ∀ pattern,
      rhoStaticFrameBinderFree (mapPattern symbols pattern) =
        rhoStaticFrameBinderFree pattern
    | .bvar _ => rfl
    | .fvar _ => rfl
    | .apply constructor arguments => by
        simp only [mapPattern, rhoStaticFrameBinderFree]
        exact rhoStaticFrameListBinderFree_mapPatternList symbols arguments
    | .lambda _ _ => rfl
    | .multiLambda _ _ _ => rfl
    | .subst _ _ => rfl
    | .collection collectionType elements rest => by
        simp only [mapPattern, rhoStaticFrameBinderFree]
        exact rhoStaticFrameListBinderFree_mapPatternList symbols elements
  termination_by pattern => 3 * sizeOf pattern + 2

  /-- List companion to binder-freedom under static symbol mapping. -/
  theorem rhoStaticFrameListBinderFree_mapPatternList
      (symbols : LanguageDefSymbolMap) : ∀ patterns,
      rhoStaticFrameListBinderFree (mapPatternList symbols patterns) =
        rhoStaticFrameListBinderFree patterns
    | [] => rfl
    | pattern :: patterns => by
        simp only [mapPatternList, rhoStaticFrameListBinderFree,
          rhoStaticFrameBinderFree_mapPattern symbols pattern,
          rhoStaticFrameListBinderFree_mapPatternList symbols patterns]
  termination_by patterns => 3 * sizeOf patterns + 1

  decreasing_by
    all_goals simp_wf <;> omega
end

mutual
  /-- Certified ambient-binder reinsertion changes indices but introduces no
  binder syntax. -/
  theorem rhoStaticFrameBinderFree_thickenAmbientBVars
      {source : CIGSLT} {color : CostStaticColor}
      {sourceBound targetBound : List TypeExpr}
      (thinning : CostStaticBinderThinning source color sourceBound
        targetBound) (depth : Nat) : ∀ pattern,
      rhoStaticFrameBinderFree
          (thinning.thickenAmbientBVars depth pattern) =
        rhoStaticFrameBinderFree pattern
    | .bvar _ => rfl
    | .fvar _ => rfl
    | .apply constructor arguments => by
        simp only [CostStaticBinderThinning.thickenAmbientBVars,
          rhoStaticFrameBinderFree]
        exact rhoStaticFrameListBinderFree_thickenAmbientBVars thinning depth
          arguments
    | .lambda _ _ => rfl
    | .multiLambda _ _ _ => rfl
    | .subst _ _ => rfl
    | .collection collectionType elements rest => by
        simp only [CostStaticBinderThinning.thickenAmbientBVars,
          rhoStaticFrameBinderFree]
        exact rhoStaticFrameListBinderFree_thickenAmbientBVars thinning depth
          elements
  termination_by pattern => 3 * sizeOf pattern + 2

  /-- List companion to binder-freedom under ambient-binder reinsertion. -/
  theorem rhoStaticFrameListBinderFree_thickenAmbientBVars
      {source : CIGSLT} {color : CostStaticColor}
      {sourceBound targetBound : List TypeExpr}
      (thinning : CostStaticBinderThinning source color sourceBound
        targetBound) (depth : Nat) : ∀ patterns,
      rhoStaticFrameListBinderFree
          (patterns.map (thinning.thickenAmbientBVars depth)) =
        rhoStaticFrameListBinderFree patterns
    | [] => rfl
    | pattern :: patterns => by
        simp only [List.map, rhoStaticFrameListBinderFree,
          rhoStaticFrameBinderFree_thickenAmbientBVars thinning depth pattern,
          rhoStaticFrameListBinderFree_thickenAmbientBVars thinning depth
            patterns]
  termination_by patterns => 3 * sizeOf patterns + 1

  decreasing_by
    all_goals simp_wf <;> omega
end

/-- Reflect one exact free-variable occurrence in a mapped and ambient-thickened
static frame back to an exact occurrence of the source frame.  Besides the
leaf name, the result preserves the quote-local availability of the complete
zipper. -/
theorem exists_sourceOccurrence_of_mappedThickenedOccurrence
    {color : CostStaticColor} {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound) (sourceRoot : Pattern) (ambient : List TypeExpr)
    (targetOccurrence : CostStaticFVarOccurrence
      (thinning.thickenAmbientBVars 0
        (mapPattern (color.symbols rhoCIGSLT) sourceRoot))) :
    ∃ sourceOccurrence : CostStaticFVarOccurrence sourceRoot,
      sourceOccurrence.name = targetOccurrence.name ∧
        rhoStaticContextReflectiveAvailable ambient sourceOccurrence.context =
          rhoStaticContextReflectiveAvailable ambient targetOccurrence.context := by
  obtain ⟨mappedPayload, mappedContext, holeDepth, mappedSelected,
      mappedContextEquality, mappedPayloadEquality⟩ :=
    Mettapedia.GSLT.LanguageDef.Selects.exists_preimage_thickenAmbientBVars
      thinning 0 targetOccurrence.selected
  have mappedPayloadShape : mappedPayload = .fvar targetOccurrence.name := by
    cases mappedPayload <;>
      simp_all [CostStaticBinderThinning.thickenAmbientBVars]
  subst mappedPayload
  obtain ⟨sourcePayload, sourceContext, sourceSelected,
      sourceContextEquality, sourcePayloadEquality⟩ :=
    Mettapedia.GSLT.LanguageDef.Selects.exists_preimage_mapPattern
      (color.symbols rhoCIGSLT) mappedSelected
  cases sourcePayload with
  | bvar index => simp [mapPattern] at sourcePayloadEquality
  | fvar sourceName =>
      simp only [mapPattern, Pattern.fvar.injEq] at sourcePayloadEquality
      let sourceOccurrence : CostStaticFVarOccurrence sourceRoot :=
        { name := sourceName
          context := sourceContext
          selected := sourceSelected }
      refine ⟨sourceOccurrence, sourcePayloadEquality, ?_⟩
      have mappedContextTarget :
          (ContextSubstitution.renameAmbientContextAt thinning.toTargetIndex 0
            mappedContext).1 = targetOccurrence.context :=
        congrArg Prod.fst mappedContextEquality
      calc
        rhoStaticContextReflectiveAvailable ambient sourceOccurrence.context =
            rhoStaticContextReflectiveAvailable ambient
              (CIGSLT.mapOneHoleContext (color.symbols rhoCIGSLT)
                sourceContext) :=
          (rhoStaticContextReflectiveAvailable_mapOneHoleContext color ambient
            sourceContext).symm
        _ = rhoStaticContextReflectiveAvailable ambient mappedContext := by
          rw [sourceContextEquality]
        _ = rhoStaticContextReflectiveAvailable ambient
              (ContextSubstitution.renameAmbientContextAt
                thinning.toTargetIndex 0 mappedContext).1 :=
          (rhoStaticContextReflectiveAvailable_renameAmbientContextAt
            thinning.toTargetIndex 0 ambient mappedContext).symm
        _ = rhoStaticContextReflectiveAvailable ambient
              targetOccurrence.context := by
          rw [mappedContextTarget]
  | apply constructor arguments => simp [mapPattern] at sourcePayloadEquality
  | lambda binder body => simp [mapPattern] at sourcePayloadEquality
  | multiLambda arity binders body =>
      simp [mapPattern] at sourcePayloadEquality
  | subst body replacement => simp [mapPattern] at sourcePayloadEquality
  | collection collectionType elements rest =>
      simp [mapPattern] at sourcePayloadEquality

/-- Mapping and ambient thinning transport the occurrence-GCS certificate to
the exact generated target frame.  Binder-freedom then changes the mapped
identity binder interpretation to the caller's arbitrary interpretation. -/
theorem canonicalizeReifiedTargetFrame_supportSafeAt_quoteLocalGCS
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (support : ContextSupport.Support) (available : List TypeExpr)
    (binderImage : TypeExpr → TypeExpr)
    (childrenPreserve : CostStaticBoundaryChildReflectiveSupportPreserving
      node.boundaryTable values support binderImage)
    (inputSafe : node.term.2.1.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support available binderImage) :
    let environment := CostStaticAtomEnvironment.ofInventory inventory
    let profile := quoteLocalOccurrenceSupportProfile node values inventory
      support available binderImage childrenPreserve inputSafe
    ∃ targetTyped : WellSorted.HasType rhoCIGSLT.costWholeLanguage
        environment.atomFreeContext node.targetBound
        (node.canonicalizeReifiedTargetFrame environment
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation))
        (.base (color.mapLangSort rhoCIGSLT node.sourceSort).1),
      targetTyped.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile profile.semanticInputSupport
          available binderImage := by
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  let profile := quoteLocalOccurrenceSupportProfile node values inventory
    support available binderImage childrenPreserve inputSafe
  obtain ⟨sourceNormalized, sourceSafe⟩ :=
    semanticCanonicalizedSourceFrame_supportSafeAt_quoteLocalGCS node values
      inventory support available binderImage childrenPreserve inputSafe
  obtain ⟨mappedTypedRaw, mappedSafeRaw⟩ :=
    sourceSafe.mapCostStatic rhoCIGSLT color
      sourceNormalized.constructorsWithin
  have contextEquality :
      environment.sourceAtomFreeContext.map (color.symbols rhoCIGSLT) =
        environment.atomFreeContext :=
    environment.sourceAtomFreeContext_map_eq_atomFreeContext
      (node.semanticAtom_typeMap values inventory)
  rw [← contextEquality]
  let thickenedTypedRaw := mappedTypedRaw.thickenAmbientBVars
    (inner := []) node.thinning
  have thickenedSafeRaw := mappedSafeRaw.thickenAmbientBVars
    (inner := []) node.thinning
  have thickenedTyped : WellSorted.HasType rhoCIGSLT.costWholeLanguage
      (environment.sourceAtomFreeContext.map (color.symbols rhoCIGSLT))
      node.targetBound
      (node.thinning.thickenAmbientBVars 0
        (mapPattern (color.symbols rhoCIGSLT)
          (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
            rhoReflectivePresentation node.targetBound.length 0
            (node.reifiedSourceFrame environment).1)))
      (.base (color.mapLangSort rhoCIGSLT node.sourceSort).1) := by
    simpa only [List.nil_append, List.length_nil, mapTypeExpr,
      CostStaticColor.mapLangSort_name] using thickenedTypedRaw
  have thickenedSafeId : thickenedTyped.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile profile.semanticInputSupport
      available id :=
    thickenedSafeRaw.castTyping
  have sourceFrameFree := semanticCanonicalizedSourcePattern_binderFree node
    environment
  have mappedFrameFree : rhoStaticFrameBinderFree
      (mapPattern (color.symbols rhoCIGSLT)
        (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
          rhoReflectivePresentation node.targetBound.length 0
          (node.reifiedSourceFrame environment).1)) = true := by
    rw [rhoStaticFrameBinderFree_mapPattern]
    exact sourceFrameFree
  have thickenedFrameFree : rhoStaticFrameBinderFree
      (node.thinning.thickenAmbientBVars 0
        (mapPattern (color.symbols rhoCIGSLT)
          (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
            rhoReflectivePresentation node.targetBound.length 0
            (node.reifiedSourceFrame environment).1))) = true := by
    rw [rhoStaticFrameBinderFree_thickenAmbientBVars]
    exact mappedFrameFree
  have thickenedSafe :=
    thickenedSafeId.rhoStaticFrame_changeBinderImage thickenedFrameFree
      binderImage
  rw [canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize node
    environment]
  exact ⟨thickenedTyped, thickenedSafe⟩

/-! ## The exact negative boundary for canonical exposure -/

/-- Canonical ancestry by itself cannot transport caller-relative safety from
the authored occurrence to the final occurrence.  A quote/drop contraction
may expose an atom value that is safe at the quote-local context `[]` but not
at an unrelated ambient context.  The value below is an object, so objectness
does not repair the missing typed exposure distinction. -/
theorem canonicalAncestry_sourceSafety_does_not_imply_ambientSafety
    (ambient binder : TypeExpr) (different : binder ≠ ambient) :
    let free : WellSorted.FreeTypeContext := fun name =>
      if name = "captured" then some binder else none
    let support : ContextSupport.Support := fun name =>
      if name = "captured" then [binder] else []
    let bodyTyped : WellSorted.HasType rhoCalc free [binder]
        (.fvar "captured") binder :=
      WellSorted.HasType.fvar (by simp [free])
    let valueTyped : WellSorted.HasType rhoCalc free []
        (.lambda (some "z") (.fvar "captured")) (.arrow binder binder) :=
      WellSorted.HasType.lambda bodyTyped
    let source := .apply "NQuote"
      [.apply "PDrop" [.fvar "atom"]]
    let finalOccurrence : CostStaticFVarOccurrence
        (canonicalizeByDepths (fun _ _ pattern =>
          Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode pattern)
          rhoReflectivePresentation [ambient].length 0 source) :=
      { name := "atom"
        context := .hole
        selected := .here }
    let ancestry := keyedCanonicalDepthsFVarCertificate
      (fun _ _ pattern =>
        Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode pattern)
        rhoReflectivePresentation
        [ambient].length 0 source finalOccurrence
    ancestry.sourceOccurrence.name = finalOccurrence.name ∧
      valueTyped.ReflectiveSupportSafeAt rhoReflectionProfile support [] id ∧
      ¬ valueTyped.ReflectiveSupportSafeAt rhoReflectionProfile support
          [ambient] id := by
  dsimp
  constructor
  · exact (keyedCanonicalDepthsFVarCertificate
      (fun _ _ pattern =>
        Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode pattern)
        rhoReflectivePresentation
        [ambient].length 0
        (.apply "NQuote" [.apply "PDrop" [.fvar "atom"]])
        { name := "atom"
          context := .hole
          selected := .here }).name_eq
  constructor
  · apply WellSorted.HasType.ReflectiveSupportSafeAt.lambda
    exact WellSorted.HasType.ReflectiveSupportSafeAt.fvar
      (by simp) [binder] ⟨[], by simp⟩
  · intro alleged
    cases alleged with
    | lambda bodySafe =>
        cases bodySafe with
        | fvar _ _ shape =>
            obtain ⟨inner, impossible⟩ := shape
            have headEquality := congrArg List.getLast? impossible
            simp at headEquality
            have binderEqAmbient : binder = ambient := by
              exact headEquality.symm
            exact different binderEqAmbient

end CostStaticRegionNode

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
