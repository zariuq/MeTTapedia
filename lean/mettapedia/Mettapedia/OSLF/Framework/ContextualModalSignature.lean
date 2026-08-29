import Mettapedia.OSLF.Framework.DisplayedContextProfile
import Mettapedia.OSLF.Framework.SelectedModalNaming
import Mettapedia.OSLF.Framework.SelectedUnaryModalSignature

/-!
# Context-sensitive modal type-former signatures

For a displayed source occurrence `t` in a one-hole context `C[-]`, the
generated modal type former is not generally unary.  Its signature retains:

* one rely-type argument for every free variable in the fixed part of `C`;
* one result-type family, curried over those same variables;
* the carrier of the focused occurrence as its result carrier.

This is the signature coordinate of the syntactic OSLF construction.  A local
star/box assignment and the corresponding formation, introduction, and
elimination rules are separate generated coordinates.  Keeping the two
coordinates distinct prevents a signature compiler from silently selecting a
hypercube vertex.

Carrier objects are abstract here.  `resolve` is supplied by the sparse
carrier-object compiler and maps each source `TypeExpr` to its generated sort
name.  Consequently this module describes the mathematical signature once;
positional, structural, and future intrinsic carrier encodings can share it.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted

namespace ContextualModalSignature

/-- Turn a sequence of dependency carriers into a curried function carrier. -/
def curryType : List TypeExpr → TypeExpr → TypeExpr
  | [], codomain => codomain
  | domain :: domains, codomain => .arrow domain (curryType domains codomain)

@[simp] theorem curryType_nil (codomain : TypeExpr) :
    curryType [] codomain = codomain :=
  rfl

@[simp] theorem curryType_cons (domain : TypeExpr) (domains : List TypeExpr)
    (codomain : TypeExpr) :
    curryType (domain :: domains) codomain =
      .arrow domain (curryType domains codomain) :=
  rfl

/-- Base-name support of a curried carrier is exactly the support of its
ordered domains followed by the support of its codomain. -/
theorem curryType_baseNames (domains : List TypeExpr) (codomain : TypeExpr) :
    (curryType domains codomain).baseNames =
      domains.flatMap TypeExpr.baseNames ++ codomain.baseNames := by
  induction domains with
  | nil => rfl
  | cons domain domains inductionHypothesis =>
      simp [curryType, TypeExpr.baseNames, inductionHypothesis,
        List.append_assoc]

/-- Reified carrier type used in the generated first-order signature. -/
def resolvedCarrier (resolve : TypeExpr → String) (object : TypeExpr) :
    TypeExpr :=
  .base (resolve object)

/-- The fixed-context variables whose types parameterize one modal former. -/
def relyBindings {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) : List (String × TypeExpr) :=
  DisplayedContextProfile.bindings typing

/-- Ordered input carrier objects of a modal former: all relies, followed by
the reduct/result carrier. -/
def inputCarriers {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) : List TypeExpr :=
  (relyBindings typing).map Prod.snd ++ [typing.rewriteType]

/-- Exact carrier support of one contextual modal declaration: its result
carrier followed by every carrier mentioned by its parameter row. -/
def carrierSupport {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) : List TypeExpr :=
  typing.focusType :: inputCarriers typing

/-- The result type may depend on every fixed-context variable.  In the
first-order carrier encoding this dependency is represented by a curried
function object, with the authored context order preserved exactly. -/
def resultFamilyType {source : ValidatedLanguageDef}
    (resolve : TypeExpr → String)
    (typing : DisplayedRewriteTyping source) : TypeExpr :=
  curryType
    ((relyBindings typing).map fun binding =>
      resolvedCarrier resolve binding.2)
    (resolvedCarrier resolve typing.rewriteType)

/-- One rely-type parameter per fixed-context variable. -/
def relyParametersFor (resolve : TypeExpr → String)
    (bindings : List (String × TypeExpr)) : List TermParam :=
  bindings.map fun binding =>
    .simple ("rely:" ++ binding.1) (resolvedCarrier resolve binding.2)

/-- Complete parameter row of one contextual modal former. -/
def parametersFor (resolve : TypeExpr → String)
    (bindings : List (String × TypeExpr))
    (resultCarrier : TypeExpr) : List TermParam :=
  relyParametersFor resolve bindings ++
    [.simple "result-family"
      (curryType
        (bindings.map fun binding => resolvedCarrier resolve binding.2)
        (resolvedCarrier resolve resultCarrier))]

/-- Contextual parameter generation depends only on resolver values at its
explicit carrier support. -/
theorem parametersFor_congr (first second : TypeExpr → String)
    (bindings : List (String × TypeExpr)) (resultCarrier : TypeExpr)
    (agree : ∀ object ∈ bindings.map Prod.snd ++ [resultCarrier],
      first object = second object) :
    parametersFor first bindings resultCarrier =
      parametersFor second bindings resultCarrier := by
  have relyEquality :
      relyParametersFor first bindings = relyParametersFor second bindings := by
    unfold relyParametersFor
    apply List.map_congr_left
    intro binding bindingMembership
    simp only [resolvedCarrier]
    rw [agree binding.2]
    exact List.mem_append_left _
      (List.mem_map_of_mem bindingMembership)
  have domainEquality :
      (bindings.map fun binding => resolvedCarrier first binding.2) =
        bindings.map fun binding => resolvedCarrier second binding.2 := by
    apply List.map_congr_left
    intro binding bindingMembership
    simp only [resolvedCarrier]
    rw [agree binding.2]
    exact List.mem_append_left _
      (List.mem_map_of_mem bindingMembership)
  have resultEquality :
      resolvedCarrier first resultCarrier =
        resolvedCarrier second resultCarrier := by
    simp only [resolvedCarrier]
    rw [agree resultCarrier (by simp)]
  simp [parametersFor, relyEquality, domainEquality, resultEquality]

/-- Every base name mentioned by a contextual parameter comes from exactly
one authored input carrier: a fixed-context rely or the rewrite result.  This
is the generic validation bridge used by sparse carrier compilers. -/
theorem parameter_baseName_origin (resolve : TypeExpr → String)
    (bindings : List (String × TypeExpr)) (resultCarrier : TypeExpr)
    {parameter : TermParam} (parameterMembership :
      parameter ∈ parametersFor resolve bindings resultCarrier)
    {typeName : String}
    (typeNameMembership :
      typeName ∈ (TermParam.typeExpr parameter).baseNames) :
    ∃ object ∈ bindings.map Prod.snd ++ [resultCarrier],
      typeName = resolve object := by
  rw [parametersFor, List.mem_append] at parameterMembership
  rcases parameterMembership with relyMembership | resultMembership
  · unfold relyParametersFor at relyMembership
    obtain ⟨binding, bindingMembership, rfl⟩ :=
      List.mem_map.mp relyMembership
    simp only [TermParam.typeExpr, resolvedCarrier, TypeExpr.baseNames,
      List.mem_singleton] at typeNameMembership
    refine ⟨binding.2, ?_, typeNameMembership⟩
    exact List.mem_append_left _ (List.mem_map_of_mem bindingMembership)
  · have parameterEquality : parameter =
        .simple "result-family"
          (curryType
            (bindings.map fun binding => resolvedCarrier resolve binding.2)
            (resolvedCarrier resolve resultCarrier)) := by
      simpa using resultMembership
    subst parameter
    simp only [TermParam.typeExpr] at typeNameMembership
    rw [curryType_baseNames] at typeNameMembership
    rcases List.mem_append.mp typeNameMembership with
        domainMembership | resultTypeMembership
    · obtain ⟨domain, domainMembership, nameMembership⟩ :=
        List.mem_flatMap.mp domainMembership
      obtain ⟨binding, bindingMembership, rfl⟩ :=
        List.mem_map.mp domainMembership
      simp only [resolvedCarrier, TypeExpr.baseNames,
        List.mem_singleton] at nameMembership
      refine ⟨binding.2, ?_, nameMembership⟩
      exact List.mem_append_left _ (List.mem_map_of_mem bindingMembership)
    · simp only [resolvedCarrier, TypeExpr.baseNames,
        List.mem_singleton] at resultTypeMembership
      exact ⟨resultCarrier, by simp, resultTypeMembership⟩

/-- Complete parameter row extracted from one typed displayed occurrence. -/
def parameters {source : ValidatedLanguageDef}
    (resolve : TypeExpr → String)
    (typing : DisplayedRewriteTyping source) : List TermParam :=
  parametersFor resolve (relyBindings typing) typing.rewriteType

/-- One context-sensitive modal type-former declaration.

The stable label records occurrence identity.  Its category is the focused
carrier; its arguments expose every rely type and the dependent result family.
-/
def modalRule {source : ValidatedLanguageDef}
    (resolve : TypeExpr → String) (slot : Nat)
    (typing : DisplayedRewriteTyping source) : GrammarRule where
  label := SelectedModalNaming.label slot
  category := resolve typing.focusType
  params := parameters resolve typing
  syntaxPattern := []

/-- Contextual modal generation is extensional on its finite carrier
support; unrelated resolver entries cannot perturb the generated row. -/
theorem modalRule_congr {source : ValidatedLanguageDef}
    (first second : TypeExpr → String) (slot : Nat)
    (typing : DisplayedRewriteTyping source)
    (agree : ∀ object ∈ carrierSupport typing,
      first object = second object) :
    modalRule first slot typing = modalRule second slot typing := by
  have categoryEquality : first typing.focusType = second typing.focusType :=
    agree typing.focusType (by simp [carrierSupport])
  have parameterEquality :
      parameters first typing = parameters second typing := by
    unfold parameters
    apply parametersFor_congr
    intro object membership
    apply agree object
    apply List.mem_cons_of_mem
    simpa [inputCarriers] using membership
  simp [modalRule, categoryEquality, parameterEquality]

@[simp] theorem modalRule_label {source : ValidatedLanguageDef}
    (resolve : TypeExpr → String) (slot : Nat)
    (typing : DisplayedRewriteTyping source) :
    (modalRule resolve slot typing).label =
      SelectedModalNaming.label slot :=
  rfl

@[simp] theorem modalRule_category {source : ValidatedLanguageDef}
    (resolve : TypeExpr → String) (slot : Nat)
    (typing : DisplayedRewriteTyping source) :
    (modalRule resolve slot typing).category = resolve typing.focusType :=
  rfl

@[simp] theorem length_relyParametersFor (resolve : TypeExpr → String)
    (bindings : List (String × TypeExpr)) :
    (relyParametersFor resolve bindings).length = bindings.length := by
  simp [relyParametersFor]

@[simp] theorem length_parametersFor (resolve : TypeExpr → String)
    (bindings : List (String × TypeExpr)) (resultCarrier : TypeExpr) :
    (parametersFor resolve bindings resultCarrier).length =
      bindings.length + 1 := by
  simp [parametersFor]

/-- Contextual arity is exact: one argument per fixed-context rely and one
dependent result-family argument. -/
@[simp] theorem modalRule_parameter_count {source : ValidatedLanguageDef}
    (resolve : TypeExpr → String) (slot : Nat)
    (typing : DisplayedRewriteTyping source) :
    (modalRule resolve slot typing).params.length =
      (DisplayedContextProfile.bindings typing).length + 1 := by
  simp [modalRule, parameters, relyBindings]

@[simp] theorem inputCarriers_length {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) :
    (inputCarriers typing).length =
      (DisplayedContextProfile.bindings typing).length + 1 := by
  simp [inputCarriers, relyBindings]

/-- The old globally unary declaration cannot represent a genuinely
contextual occurrence.  This is a structural obstruction, independent of any
later semantic interpretation. -/
theorem unary_rule_ne_contextual_of_nonempty
    {source : ValidatedLanguageDef}
    (resolve : TypeExpr → String) (slot : Nat)
    (typing : DisplayedRewriteTyping source)
    (nonempty : DisplayedContextProfile.bindings typing ≠ []) :
    SelectedUnaryModalSignature.modalRule slot ≠ modalRule resolve slot typing := by
  intro equality
  have arities := congrArg (fun rule : GrammarRule => rule.params.length) equality
  have positive : 0 < (DisplayedContextProfile.bindings typing).length :=
    List.length_pos_of_ne_nil nonempty
  have impossible :
      1 = (DisplayedContextProfile.bindings typing).length + 1 := by
    simpa [SelectedUnaryModalSignature.modalRule] using arities
  omega

/-! ## Positive and negative controls -/

namespace Canary

private def resolve : TypeExpr → String
  | .base name => "generated:" ++ name
  | .arrow _ _ => "generated:arrow"
  | .multiBinder _ => "generated:multibinder"
  | .collection _ _ => "generated:collection"

private def twoBindings : List (String × TypeExpr) :=
  [("left", .base "Left"), ("right", .base "Right")]

/-- Two fixed-context variables yield two rely inputs and one dependent result
family, in authored order. -/
theorem two_dependencies_have_three_parameters :
    parametersFor resolve twoBindings (.base "Result") =
      [ .simple "rely:left" (.base "generated:Left")
      , .simple "rely:right" (.base "generated:Right")
      , .simple "result-family"
          (.arrow (.base "generated:Left")
            (.arrow (.base "generated:Right")
              (.base "generated:Result"))) ] := by
  rfl

/-- Erasing the dependency telescope changes the result-family carrier. -/
theorem dependent_result_family_ne_flat_result :
    curryType [.base "A", .base "B"] (.base "R") ≠ .base "R" := by
  decide

/-- The empty-context specialization is genuinely unary; this is the precise
fragment in which the former placeholder happened to have the right arity. -/
theorem empty_context_has_one_parameter :
    (parametersFor resolve [] (.base "Result")).length = 1 := by
  rfl

def termType : TypeDecl :=
  TypeDecl.plain "contextual-modal-signature:Term"

def ternaryTerm : GrammarRule where
  label := "contextual-modal-signature:ternary"
  category := termType.name
  params :=
    [ .simple "left" (.base termType.name)
    , .simple "focus" (.base termType.name)
    , .simple "right" (.base termType.name) ]
  syntaxPattern := []

def contextualRewrite : RewriteRule where
  name := "contextual-modal-signature:select-middle"
  typeContext :=
    [ ("left", .base termType.name)
    , ("focus", .base termType.name)
    , ("right", .base termType.name) ]
  premises := []
  left := .apply ternaryTerm.label
    [.fvar "left", .fvar "focus", .fvar "right"]
  right := .fvar "focus"

def sourceLanguage : LanguageDef :=
  { name := "contextual-modal-signature-source"
    types := [termType]
    terms := [ternaryTerm]
    equations := []
    rewrites := [contextualRewrite] }

private theorem sourceLanguage_valid : sourceLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  case hequations => rfl
  case htypes => decide
  case hconstructors => decide
  case hrewrites => decide
  case hcategory => decide
  case hparams => decide
  case hsyntax => decide
  case hrewriteValid =>
    intro rewrite membership
    change List.Mem rewrite [contextualRewrite] at membership
    have equality := List.mem_singleton.mp membership
    subst rewrite
    simp [LanguageDef.validateRewrite, sourceLanguage, contextualRewrite,
      ternaryTerm, termType, LanguageDef.validatePatternConstructors,
      LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, LanguageDef.typeNames, TypeDecl.plain]
    apply LanguageDef.validateTypeExpr_eq_nil_of_baseNames
    intro name nameMembership
    simpa [TypeExpr.baseNames] using nameMembership

def source : ValidatedLanguageDef :=
  ⟨sourceLanguage, sourceLanguage_valid⟩

def middleSite : DisplayedRewriteSite source.language where
  rewriteIndex := ⟨0, by decide⟩
  focus := .fvar "focus"
  context := .apply ternaryTerm.label [.fvar "left"] .hole [.fvar "right"]
  selects := .apply .here

private theorem leftTyped :
    HasType sourceLanguage
      (FreeTypeContext.ofList contextualRewrite.typeContext) []
      contextualRewrite.left (.base termType.name) := by
  apply HasType.constructor (rule := ternaryTerm)
  · simp [sourceLanguage]
  · simp [UsesBareCollection, ternaryTerm]
  · apply ArgumentsHaveTypes.cons
    · trivial
    · rfl
    · apply HasType.fvar
      simp [contextualRewrite, FreeTypeContext.ofList]
    · apply ArgumentsHaveTypes.cons
      · trivial
      · rfl
      · apply HasType.fvar
        simp [contextualRewrite, FreeTypeContext.ofList]
      · apply ArgumentsHaveTypes.cons
        · trivial
        · rfl
        · apply HasType.fvar
          simp [contextualRewrite, FreeTypeContext.ofList]
        · exact ArgumentsHaveTypes.nil

private theorem rightTyped :
    HasType sourceLanguage
      (FreeTypeContext.ofList contextualRewrite.typeContext) []
      contextualRewrite.right (.base termType.name) := by
  apply HasType.fvar
  simp [contextualRewrite, FreeTypeContext.ofList]

def middleTyping : DisplayedRewriteTyping source where
  site := middleSite
  rewriteType := .base termType.name
  focusBoundPrefix := []
  focusType := .base termType.name
  rewriteLeftTyped := by
    simpa [source, middleSite, DisplayedRewriteSite.rewrite, sourceLanguage]
      using leftTyped
  rewriteRightTyped := by
    simpa [source, middleSite, DisplayedRewriteSite.rewrite, sourceLanguage]
      using rightTyped
  sourceIsObject := by decide
  focusTyped := by
    apply HasType.fvar
    simp [source, middleSite, DisplayedRewriteSite.rewrite, sourceLanguage,
      contextualRewrite, FreeTypeContext.ofList]

/-- A certified non-root occurrence recovers both fixed-frame dependencies
from the authored rewrite context, in their contextual order. -/
theorem middle_occurrence_dependencies_exact :
    DisplayedContextProfile.bindings middleTyping =
      [("left", .base termType.name), ("right", .base termType.name)] := by
  simp [DisplayedContextProfile.bindings,
    DisplayedContextProfile.variableNames,
    DisplayedContextProfile.externalFreeFvarNames,
    DisplayedContextProfile.variableType?, middleTyping, middleSite,
    DisplayedRewriteSite.rewrite, source, sourceLanguage, contextualRewrite,
    FreeTypeContext.ofList, Pattern.freeFvarNames]
  decide

/-- The contextual compiler therefore emits a genuinely ternary modal
signature for the certified middle occurrence. -/
theorem middle_occurrence_has_three_parameters :
    (modalRule resolve 0 middleTyping).params.length = 3 := by
  rw [modalRule_parameter_count, middle_occurrence_dependencies_exact]
  rfl

/-- The unary placeholder is refuted by an actual well-sorted displayed
rewrite occurrence, not merely by a synthetic dependency list. -/
theorem unary_rule_rejected_by_middle_occurrence :
    SelectedUnaryModalSignature.modalRule 0 ≠ modalRule resolve 0 middleTyping := by
  apply unary_rule_ne_contextual_of_nonempty
  rw [middle_occurrence_dependencies_exact]
  decide

end Canary

#print axioms curryType
#print axioms modalRule_parameter_count
#print axioms curryType_baseNames
#print axioms parameter_baseName_origin
#print axioms parametersFor_congr
#print axioms modalRule_congr
#print axioms unary_rule_ne_contextual_of_nonempty
#print axioms Canary.two_dependencies_have_three_parameters
#print axioms Canary.dependent_result_family_ne_flat_result
#print axioms Canary.empty_context_has_one_parameter
#print axioms Canary.middle_occurrence_dependencies_exact
#print axioms Canary.middle_occurrence_has_three_parameters
#print axioms Canary.unary_rule_rejected_by_middle_occurrence

end ContextualModalSignature

end Mettapedia.OSLF.Framework
