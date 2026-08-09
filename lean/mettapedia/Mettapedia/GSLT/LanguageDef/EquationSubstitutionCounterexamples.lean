import Mettapedia.GSLT.LanguageDef.EquationSubstitution
import Mettapedia.OSLF.MeTTaIL.MatchSpec

/-!
# Sharp boundaries for supported equation substitution

The examples in this module are small validated presentations that expose
which hypotheses a substitution-congruence theorem must retain.  In
particular, binder-support lists record binder types but not binder
occurrences.  Repeated equal binder types can therefore satisfy the current
support-suffix judgment on both sides of a reflective Quote/Drop equation
while selecting different de Bruijn levels after substitution.
-/

namespace Mettapedia.GSLT.LanguageDef.EquationSubstitutionCounterexamples

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.GSLT.LanguageDef.ReflectiveEquationSemantics
open Mettapedia.GSLT.LanguageDef.WellSorted

private def zeroRule : GrammarRule where
  label := "PZero"
  category := "Proc"
  params := []
  syntaxPattern := []

private def dropRule : GrammarRule where
  label := "PDrop"
  category := "Proc"
  params := [.simple "name" TypeExpr.name]
  syntaxPattern := []

private def quoteRule : GrammarRule where
  label := "NQuote"
  category := "Name"
  params := [.simple "process" TypeExpr.proc]
  syntaxPattern := []

private def parallelRule : GrammarRule where
  label := "PPar"
  category := "Proc"
  params := [.simple "processes" (TypeExpr.bag TypeExpr.proc)]
  syntaxPattern := []

/-- A name constructor whose body binds another name.  This is legal in a
generic validated `LanguageDef`, but it makes binder occurrence identity
observable at the reflective Quote/Drop boundary. -/
private def nameBinderRule : GrammarRule where
  label := "NBind"
  category := "Name"
  params := [.abstraction "body" (TypeExpr.funType TypeExpr.name TypeExpr.name)]
  syntaxPattern := []

private def quoteDropEquation : Equation where
  name := "QuoteDrop"
  typeContext := [("N", TypeExpr.name)]
  premises := []
  left := .apply "NQuote" [.apply "PDrop" [.fvar "N"]]
  right := .fvar "N"

private def presentation : ReflectivePresentationDecl where
  name := "BinderOccurrenceCollision"
  processSort := "Proc"
  nameSort := "Name"
  quoteConstructor := "NQuote"
  dropConstructor := "PDrop"
  parallelCollection := .hashBag
  parallelUnitConstructor := "PZero"
  quoteDropEquation := "QuoteDrop"

private def binderOccurrenceProfile : ReflectionProfile where
  presentations := [presentation]

/-- A fully validated reflective presentation with an additional
abstraction-bearing name constructor. -/
def binderOccurrenceLanguage : LanguageDef where
  name := "BinderOccurrenceCollision"
  types := ["Proc", "Name"]
  terms := [zeroRule, dropRule, quoteRule, parallelRule, nameBinderRule]
  equations := [quoteDropEquation]
  rewrites := []

theorem binderOccurrenceLanguage_valid :
    binderOccurrenceLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorEquationsAndRewrites
  all_goals
    simp [binderOccurrenceLanguage, zeroRule, dropRule, quoteRule,
      parallelRule, nameBinderRule, quoteDropEquation,
      LanguageDef.typeNames, TypeDecl.plain, TypeExpr.name, TypeExpr.proc,
      TypeExpr.baseType,
      LanguageDef.validateEquation, LanguageDef.validatePatternConstructors,
      LanguageDef.validateRulePatterns,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
      Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, TermParam.typeExpr, TypeExpr.baseNames]
  case hparams =>
    simp [TypeExpr.bag, TypeExpr.funType, TypeExpr.baseNames]
  case hequationValid =>
    intro constructor arity reference
    rcases reference with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

private theorem presentation_valid :
    binderOccurrenceLanguage.validateReflectivePresentation presentation = [] := by
  apply LanguageDef.validateReflectivePresentation_eq_nil_of_unique
      (quote := quoteRule) (drop := dropRule) (unit := zeroRule)
      (equation := quoteDropEquation)
      (quoteParameter := "process") (dropParameter := "name")
      (equationVariable := "N")
  all_goals
    simp [binderOccurrenceLanguage, zeroRule, dropRule, quoteRule,
      parallelRule, nameBinderRule, quoteDropEquation, presentation,
      LanguageDef.typeNames,
      TypeDecl.plain, TypeExpr.name, TypeExpr.proc, TypeExpr.baseType]

private theorem binderOccurrenceProfile_valid :
    Mettapedia.OSLF.MeTTaIL.Reflection.validate
      binderOccurrenceLanguage binderOccurrenceProfile = [] := by
  simp [Mettapedia.OSLF.MeTTaIL.Reflection.validate,
    binderOccurrenceProfile, presentation_valid]

private def support : ContextSupport.Support
  | "M" => [TypeExpr.name]
  | _ => []

private def assignment : ContextSupport.Assignment
  | "M" => .bvar 0
  | name => .fvar name

private def bound : List TypeExpr := [TypeExpr.name]

private def free : FreeTypeContext := fun name =>
  if name = "M" then some TypeExpr.name else none

private def bareName : Pattern :=
  .apply "NBind" [.lambda none (.fvar "M")]

private def quotedName : Pattern :=
  .apply "NQuote" [.apply "PDrop" [bareName]]

/-- The unquoted endpoint is a name even under the additional ambient name
binder.  Its inner lambda introduces a second binder of exactly the same
type. -/
theorem bareName_typed :
    HasType binderOccurrenceLanguage free bound bareName TypeExpr.name := by
  apply HasType.constructor (rule := nameBinderRule)
  · simp [binderOccurrenceLanguage, nameBinderRule]
  · simp [UsesBareCollection, nameBinderRule, TypeExpr.funType,
      TypeExpr.name, TypeExpr.baseType]
  · apply ArgumentsHaveTypes.cons
    · trivial
    · rfl
    · apply HasType.lambda
      apply HasType.fvar
      simp [free]
    · exact .nil

/-- The reflected endpoint has the same type in the same free and bound
contexts. -/
theorem quotedName_typed :
    HasType binderOccurrenceLanguage free bound quotedName TypeExpr.name := by
  apply HasType.constructor (rule := quoteRule)
  · simp [binderOccurrenceLanguage, quoteRule]
  · simp [UsesBareCollection, quoteRule, TypeExpr.proc, TypeExpr.baseType]
  · apply ArgumentsHaveTypes.cons
    · trivial
    · rfl
    · apply HasType.constructor (rule := dropRule)
      · simp [binderOccurrenceLanguage, dropRule]
      · simp [UsesBareCollection, dropRule, TypeExpr.name,
          TypeExpr.baseType]
      · exact .cons trivial rfl bareName_typed .nil
    · exact .nil

private theorem bareName_supportSafeAt
    (available : List TypeExpr)
    (shape : ∃ inner, TypeExpr.name :: available = inner ++ support "M") :
    bareName_typed.ReflectiveSupportSafeAt
      binderOccurrenceProfile support available := by
  have lookup : free "M" = some TypeExpr.name := by
    simp [free]
  let bodyTyped : HasType binderOccurrenceLanguage free
      (TypeExpr.name :: bound) (.fvar "M") TypeExpr.name :=
    HasType.fvar lookup
  let lambdaTyped : HasType binderOccurrenceLanguage free bound
      (.lambda none (.fvar "M"))
      (TypeExpr.funType TypeExpr.name TypeExpr.name) :=
    HasType.lambda bodyTyped
  have membership : nameBinderRule ∈ binderOccurrenceLanguage.terms := by
    simp [binderOccurrenceLanguage, nameBinderRule]
  have notBare : ¬ UsesBareCollection nameBinderRule := by
    simp [UsesBareCollection, nameBinderRule, TypeExpr.funType,
      TypeExpr.name, TypeExpr.baseType]
  have representation : MatchesParameterRepresentation
      (.abstraction "body" (TypeExpr.funType TypeExpr.name TypeExpr.name))
      (.lambda none (.fvar "M")) := trivial
  have parameterType : parameterType?
      (.abstraction "body" (TypeExpr.funType TypeExpr.name TypeExpr.name)) =
        some (TypeExpr.funType TypeExpr.name TypeExpr.name) := rfl
  let argumentsTyped : ArgumentsHaveTypes binderOccurrenceLanguage free bound
      [.lambda none (.fvar "M")] nameBinderRule.params :=
    .cons representation parameterType lambdaTyped .nil
  let outputTyped : HasType binderOccurrenceLanguage free bound bareName
      TypeExpr.name :=
    HasType.constructor membership notBare argumentsTyped
  have ordinary : ReflectiveContextSupport.isQuoteConstructor
      binderOccurrenceProfile nameBinderRule.label = false := by
    simp [ReflectiveContextSupport.isQuoteConstructor,
      binderOccurrenceProfile, presentation, nameBinderRule]
  have bodySafe : bodyTyped.ReflectiveSupportSafeAt binderOccurrenceProfile support
      (TypeExpr.name :: available) :=
    .fvar lookup (TypeExpr.name :: available) shape
  have lambdaSafe : lambdaTyped.ReflectiveSupportSafeAt
      binderOccurrenceProfile support available :=
    .lambda bodySafe
  have argumentsSafe : argumentsTyped.ReflectiveSupportSafeAt
      binderOccurrenceProfile support available :=
    .cons (representation := representation) (parameterType := parameterType)
      lambdaSafe (.nil bound available)
  exact HasType.ReflectiveSupportSafeAt.castTyping
    (source := outputTyped) (target := bareName_typed)
    (.constructorOrdinary (membership := membership) (notBare := notBare)
      (argumentsTyped := argumentsTyped) ordinary argumentsSafe)

/-- The direct endpoint passes the existing support-suffix discipline. -/
theorem bareName_supportSafe :
    bareName_typed.ReflectiveSupportSafeAt
      binderOccurrenceProfile support bound := by
  apply bareName_supportSafeAt bound
  exact ⟨[TypeExpr.name], by simp [support, bound]⟩

/-- The quoted endpoint also passes the same discipline: quotation resets the
available support before entering the drop, and the inner lambda then restores
one name-typed slot. -/
theorem quotedName_supportSafe :
    quotedName_typed.ReflectiveSupportSafeAt
      binderOccurrenceProfile support bound := by
  have dropMembership : dropRule ∈ binderOccurrenceLanguage.terms := by
    simp [binderOccurrenceLanguage, dropRule]
  have dropNotBare : ¬ UsesBareCollection dropRule := by
    simp [UsesBareCollection, dropRule, TypeExpr.name, TypeExpr.baseType]
  have dropRepresentation : MatchesParameterRepresentation
      (.simple "name" TypeExpr.name) bareName := trivial
  have dropParameterType : parameterType? (.simple "name" TypeExpr.name) =
      some TypeExpr.name := rfl
  let dropArgumentsTyped : ArgumentsHaveTypes binderOccurrenceLanguage free
      bound [bareName] dropRule.params :=
    .cons dropRepresentation dropParameterType bareName_typed .nil
  let dropTyped : HasType binderOccurrenceLanguage free bound
      (.apply "PDrop" [bareName]) TypeExpr.proc :=
    HasType.constructor dropMembership dropNotBare dropArgumentsTyped
  have quoteMembership : quoteRule ∈ binderOccurrenceLanguage.terms := by
    simp [binderOccurrenceLanguage, quoteRule]
  have quoteNotBare : ¬ UsesBareCollection quoteRule := by
    simp [UsesBareCollection, quoteRule, TypeExpr.proc, TypeExpr.baseType]
  have quoteRepresentation : MatchesParameterRepresentation
      (.simple "process" TypeExpr.proc) (.apply "PDrop" [bareName]) := trivial
  have quoteParameterType : parameterType? (.simple "process" TypeExpr.proc) =
      some TypeExpr.proc := rfl
  let quoteArgumentsTyped : ArgumentsHaveTypes binderOccurrenceLanguage free
      bound [.apply "PDrop" [bareName]] quoteRule.params :=
    .cons quoteRepresentation quoteParameterType dropTyped .nil
  let outputTyped : HasType binderOccurrenceLanguage free bound quotedName
      TypeExpr.name :=
    HasType.constructor quoteMembership quoteNotBare quoteArgumentsTyped
  have bareSafeAtQuote : bareName_typed.ReflectiveSupportSafeAt
      binderOccurrenceProfile support [] := by
    apply bareName_supportSafeAt []
    exact ⟨[], by simp [support]⟩
  have dropOrdinary : ReflectiveContextSupport.isQuoteConstructor
      binderOccurrenceProfile dropRule.label = false := by
    simp [ReflectiveContextSupport.isQuoteConstructor,
      binderOccurrenceProfile, presentation, dropRule]
  have dropArgumentsSafe : dropArgumentsTyped.ReflectiveSupportSafeAt
      binderOccurrenceProfile support [] :=
    .cons (representation := dropRepresentation)
      (parameterType := dropParameterType) bareSafeAtQuote (.nil bound [])
  have dropSafe : dropTyped.ReflectiveSupportSafeAt
      binderOccurrenceProfile support [] :=
    .constructorOrdinary (membership := dropMembership)
      (notBare := dropNotBare) (argumentsTyped := dropArgumentsTyped)
      dropOrdinary dropArgumentsSafe
  have quoteStatus : ReflectiveContextSupport.isQuoteConstructor
      binderOccurrenceProfile quoteRule.label = true := by
    simp [ReflectiveContextSupport.isQuoteConstructor,
      binderOccurrenceProfile, presentation, quoteRule]
  have quoteArgumentsSafe : quoteArgumentsTyped.ReflectiveSupportSafeAt
      binderOccurrenceProfile support [] :=
    .cons (representation := quoteRepresentation)
      (parameterType := quoteParameterType) dropSafe (.nil bound [])
  exact HasType.ReflectiveSupportSafeAt.castTyping
    (source := outputTyped) (target := quotedName_typed)
    (.constructorQuote (membership := quoteMembership)
      (notBare := quoteNotBare) (argumentsTyped := quoteArgumentsTyped)
      quoteStatus quoteArgumentsSafe)

private def bareOpenPattern :
    ReflectiveWellSorted.OpenPattern binderOccurrenceProfile
      binderOccurrenceLanguage free bound TypeExpr.name := by
  refine ⟨bareName, ?_, ?_⟩
  · refine ⟨bareName_typed, rfl, rfl, ?_⟩
    simp [bareName, bound, ScopeSafeAt, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]
  · intro declaration membership
    simp [binderOccurrenceProfile] at membership
    subst declaration
    rfl

private def quotedOpenPattern :
    ReflectiveWellSorted.OpenPattern binderOccurrenceProfile
      binderOccurrenceLanguage free bound TypeExpr.name := by
  refine ⟨quotedName, ?_, ?_⟩
  · refine ⟨quotedName_typed, rfl, rfl, ?_⟩
    simp [quotedName, bareName, bound, ScopeSafeAt, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]
  · intro declaration membership
    simp [binderOccurrenceProfile] at membership
    subst declaration
    rfl

private def bareSupportSafePattern :
    SupportSafeOpenPattern binderOccurrenceProfile binderOccurrenceLanguage
      free support bound TypeExpr.name :=
  ⟨bareOpenPattern, bareName_supportSafe⟩

private def quotedSupportSafePattern :
    SupportSafeOpenPattern binderOccurrenceProfile binderOccurrenceLanguage
      free support bound TypeExpr.name :=
  ⟨quotedOpenPattern, quotedName_supportSafe⟩

private def supportedAssignment : SupportedOpenAssignment
    binderOccurrenceProfile binderOccurrenceLanguage free
      FreeTypeContext.empty support where
  assignment := assignment
  typed := by
    intro name type lookup
    by_cases equality : name = "M"
    · subst name
      simp [free] at lookup
      subst type
      apply HasType.bvar
      simp [support]
    · simp [free, equality] at lookup
  canonicalBinderMetadata := by
    intro name type lookup
    by_cases equality : name = "M"
    · subst name
      simp [free] at lookup
      subst type
      rfl
    · simp [free, equality] at lookup
  objectPattern := by
    intro name type lookup
    by_cases equality : name = "M"
    · subst name
      simp [free] at lookup
      subst type
      rfl
    · simp [free, equality] at lookup
  reflectiveScopeSafe := by
    intro name type lookup
    by_cases equality : name = "M"
    · subst name
      simp [free] at lookup
      subst type
      intro declaration membership
      simp [binderOccurrenceProfile] at membership
      subst declaration
      rfl
    · simp [free, equality] at lookup

/-- The source terms are identified by the authored reflective
canonicalizer. -/
theorem canonicalize_before_substitution :
    canonicalize presentation quotedName =
      canonicalize presentation bareName := by
  rfl

theorem substitute_quotedName :
    ReflectiveContextSupport.substitute binderOccurrenceProfile support
        assignment bound quotedName =
      .apply "NQuote"
        [.apply "PDrop"
          [.apply "NBind" [.lambda none (.bvar 0)]]] := by
  simp [ReflectiveContextSupport.substitute,
    ReflectiveContextSupport.substituteAt,
    ReflectiveContextSupport.isQuoteConstructor, binderOccurrenceProfile,
    presentation, support, assignment, bound, quotedName, bareName, liftBVars]

theorem substitute_bareName :
    ReflectiveContextSupport.substitute binderOccurrenceProfile support
        assignment bound bareName =
      .apply "NBind" [.lambda none (.bvar 1)] := by
  simp [ReflectiveContextSupport.substitute,
    ReflectiveContextSupport.substituteAt,
    ReflectiveContextSupport.isQuoteConstructor, binderOccurrenceProfile,
    presentation, support, assignment, bound, bareName, liftBVars]

/-- Canonical equality is not preserved: the same type-only support suffix
selects the inner binder below quotation and the outer equal-typed binder
after Quote/Drop cancellation. -/
theorem canonicalize_after_substitution_ne :
    canonicalize presentation
        (ReflectiveContextSupport.substitute binderOccurrenceProfile support
          assignment bound quotedName) ≠
      canonicalize presentation
        (ReflectiveContextSupport.substitute binderOccurrenceProfile support
          assignment bound bareName) := by
  rw [substitute_quotedName, substitute_bareName]
  simp [canonicalize, canonicalizeList, presentation,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply]

private theorem equationInstanceAt_canonicalize_eq
    {fuel : Nat} {source target : Pattern}
    (witness : EquationSemantics.EquationInstanceAt defaultBasePremises
      binderOccurrenceLanguage fuel source target) :
    canonicalize presentation source = canonicalize presentation target := by
  cases witness with
  | @forward equation source target initialBindings finalBindings
      membership matched premises targetEquality =>
      have equationEquality : equation = quoteDropEquation := by
        change List.Mem equation [quoteDropEquation] at membership
        cases membership with
        | head => rfl
        | tail _ impossible => cases impossible
      have premisesEmpty : equation.premises = [] := by
        rw [equationEquality]
        rfl
      have leftEquality : equation.left =
          .apply "NQuote" [.apply "PDrop" [.fvar "N"]] := by
        rw [equationEquality]
        rfl
      have rightEquality : equation.right = .fvar "N" := by
        rw [equationEquality]
        rfl
      rw [premisesEmpty] at premises
      cases premises
      rw [leftEquality] at matched
      rw [rightEquality] at targetEquality
      have sourceEquality := matchPattern_correct matched (by decide)
      rw [← sourceEquality, ← targetEquality]
      simp [applyBindings, canonicalize, canonicalizeList, presentation,
        Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply]
  | @reverse equation source target initialBindings finalBindings
      membership matched premises targetEquality =>
      have equationEquality : equation = quoteDropEquation := by
        change List.Mem equation [quoteDropEquation] at membership
        cases membership with
        | head => rfl
        | tail _ impossible => cases impossible
      have premisesEmpty : equation.premises = [] := by
        rw [equationEquality]
        rfl
      have leftEquality : equation.left =
          .apply "NQuote" [.apply "PDrop" [.fvar "N"]] := by
        rw [equationEquality]
        rfl
      have rightEquality : equation.right = .fvar "N" := by
        rw [equationEquality]
        rfl
      rw [premisesEmpty] at premises
      cases premises
      rw [rightEquality] at matched
      rw [leftEquality] at targetEquality
      have sourceEquality := matchPattern_correct matched (by decide)
      rw [← sourceEquality, ← targetEquality]
      simp [applyBindings, canonicalize, canonicalizeList, presentation,
        Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply]

private theorem equationContextStep_canonicalize_eq
    {left right : Pattern}
    (step : ReflectiveEquationContextStep binderOccurrenceProfile
      defaultBasePremises binderOccurrenceLanguage left right) :
    canonicalize presentation left = canonicalize presentation right := by
  cases step with
  | core coreStep =>
      cases coreStep with
      | @inContext context redex contractum equationInstance =>
          obtain ⟨fuel, bounded⟩ := equationInstance
          exact canonicalize_fill_congr presentation context
            (equationInstanceAt_canonicalize_eq bounded)
  | @reflectiveInContext context declaration reflectedLeft reflectedRight
      membership representatives =>
      have declarationEquality : declaration = presentation := by
        change List.Mem declaration [presentation] at membership
        cases membership with
        | head => rfl
        | tail _ impossible => cases impossible
      rw [declarationEquality] at representatives
      exact canonicalize_fill_congr presentation context representatives

/-- For this validated fixture, the authored contextual equation relation is
exactly sound for the declared reflective representative. -/
theorem equationEquiv_canonicalize_eq
    {left right : Pattern}
    (equivalent : ReflectiveEquationEquiv binderOccurrenceProfile
      defaultBasePremises binderOccurrenceLanguage left right) :
    canonicalize presentation left = canonicalize presentation right := by
  induction equivalent with
  | rel left right step =>
      exact equationContextStep_canonicalize_eq step
  | refl pattern => rfl
  | symm left right relation inductionHypothesis =>
      exact inductionHypothesis.symm
  | trans left middle right first second firstIH secondIH =>
      exact firstIH.trans secondIH

/-- Strong negative control: the two support-safe, well-sorted endpoints are
an authored reflective-equation edge before substitution, but their images
are not even related by the authored contextual equation closure afterward. -/
theorem substituted_endpoints_not_equivalent :
    ¬ ReflectiveEquationEquiv binderOccurrenceProfile defaultBasePremises
      binderOccurrenceLanguage
      (ReflectiveContextSupport.substitute binderOccurrenceProfile support
        assignment bound quotedName)
      (ReflectiveContextSupport.substitute binderOccurrenceProfile support
        assignment bound bareName) := by
  intro equivalent
  exact canonicalize_after_substitution_ne
    (equationEquiv_canonicalize_eq equivalent)

/-- Validation, well-sortedness, object syntax, reflective scope safety, and
the current type-suffix support judgment do not imply reflective equation
substitution stability.  The missing information is the identity of the
equal-typed binder occurrence selected by each free parameter use. -/
theorem binderOccurrenceLanguage_not_reflectiveEquationSubstitutionStable :
    ¬ ReflectiveEquationSubstitutionStable
      (profile := binderOccurrenceProfile) binderOccurrenceLanguage := by
  intro stable
  have preserved := stable supportedAssignment
    (declaration := presentation)
    (by simp [binderOccurrenceProfile])
    quotedSupportSafePattern bareSupportSafePattern
    canonicalize_before_substitution
  apply substituted_endpoints_not_equivalent
  simpa [supportedAssignment, quotedSupportSafePattern, quotedOpenPattern,
    bareSupportSafePattern, bareOpenPattern] using preserved

/-- The same fixture fails the structural sealing condition for exactly the
ordinary name-returning binder constructor that drives the counterexample. -/
theorem binderOccurrenceLanguage_not_reflectiveNameResultSealed :
    ¬ ReflectiveNameResultSealed
      (profile := binderOccurrenceProfile) binderOccurrenceLanguage := by
  intro sealed
  have forbidden := sealed presentation (by
      simp [binderOccurrenceProfile]) nameBinderRule (by
      simp [binderOccurrenceLanguage, nameBinderRule]) (by
      simp [nameBinderRule, presentation])
  simp [nameBinderRule, presentation] at forbidden

/-! ## Raw reflective equality does not preserve typed fibers -/

private def zeroProcess : Pattern :=
  .apply "PZero" []

private def malformedQuoteDrop : Pattern :=
  .apply "NQuote" [.apply "PDrop" [zeroProcess]]

private theorem zeroProcess_openWellSorted :
    ReflectiveWellSorted.OpenPatternWellSorted binderOccurrenceProfile
      binderOccurrenceLanguage FreeTypeContext.empty [] TypeExpr.proc
      zeroProcess := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, rfl, rfl, ?_⟩
    · apply HasType.constructor (rule := zeroRule)
      · simp [binderOccurrenceLanguage, zeroRule]
      · simp [UsesBareCollection, zeroRule]
      · exact .nil
    · simp [zeroProcess, ScopeSafeAt, Pattern.isWellScopedAt,
        Pattern.isWellScopedListAt]
  · intro declaration membership
    simp [binderOccurrenceProfile] at membership
    subst declaration
    rfl

private theorem malformedQuoteDrop_not_typed :
    ¬ HasType binderOccurrenceLanguage FreeTypeContext.empty []
      malformedQuoteDrop TypeExpr.proc := by
  intro typed
  have safe := typed.reflectiveSupportSafeAt_empty
    (profile := binderOccurrenceProfile) []
  have declarationMembership : presentation ∈
      binderOccurrenceProfile.presentations := by
    change List.Mem presentation [presentation]
    exact .head _
  obtain ⟨dropPattern, dropTyped, dropShape, dropSafe⟩ :=
    typed.selectedQuoteArgument binderOccurrenceLanguage_valid
      binderOccurrenceProfile_valid declarationMembership safe
  have dropPatternEq : dropPattern = .apply "PDrop" [zeroProcess] := by
    simpa using (congrArg List.head? dropShape).symm
  subst dropPattern
  have dropOrdinary : ReflectiveContextSupport.isQuoteConstructor
      binderOccurrenceProfile presentation.dropConstructor = false := by
    simp [ReflectiveContextSupport.isQuoteConstructor,
      binderOccurrenceProfile, presentation]
  obtain ⟨zero, zeroTyped, zeroShape, zeroSafe⟩ :=
    dropTyped.selectedOrdinaryDropArgument binderOccurrenceLanguage_valid
      binderOccurrenceProfile_valid declarationMembership dropOrdinary dropSafe
  have zeroEq : zero = zeroProcess := by
    simpa using (congrArg List.head? zeroShape).symm
  subst zero
  have zeroProcType : HasType binderOccurrenceLanguage
      FreeTypeContext.empty [] zeroProcess TypeExpr.proc :=
    zeroProcess_openWellSorted.1.1
  have impossible := HasType.apply_type_unique_of_validate_eq_nil
    binderOccurrenceLanguage_valid zeroTyped zeroProcType
  simp [presentation, TypeExpr.proc, TypeExpr.baseType] at impossible

/-- Validation cannot make the untyped reflective generator preserve every
typed open fiber.  Quote/Drop canonicalization identifies the well-sorted
zero process with a raw preimage whose Drop argument has the wrong sort. -/
theorem binderOccurrenceLanguage_not_openEquationFiberStable :
    ¬ ReflectiveOpenEquationFiberStable
      binderOccurrenceProfile defaultBasePremises binderOccurrenceLanguage := by
  intro stable
  have generator : ReflectiveEquationContextStep binderOccurrenceProfile
      defaultBasePremises binderOccurrenceLanguage
      malformedQuoteDrop zeroProcess := by
    apply ReflectiveEquationContextStep.reflectiveInContext .hole
      (declaration := presentation)
    · change List.Mem presentation [presentation]
      exact .head _
    · rfl
  have malformedWellSorted := (stable generator).mpr zeroProcess_openWellSorted
  exact malformedQuoteDrop_not_typed malformedWellSorted.1.1

end Mettapedia.GSLT.LanguageDef.EquationSubstitutionCounterexamples
