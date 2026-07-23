import Mettapedia.OSLF.MeTTaIL.Match

/-!
# Compiling declarative reflective substitution

This module interprets `ReflectivePresentationDecl` and `ReflectiveRuleDecl`
as data.  It does not attach a Lean callback to a language definition.
Languages without a uniquely selected substitution presentation retain the
ordinary syntactic `applyBindings` behavior.

The compiled operation has the two boundaries required by reflective COMM:

* quotation is opaque to substitution;
* a drop collapses only when this substitution replaced the dropped bound
  name with a quotation.

Static parallel canonicalization is a separate compiler pass.  Consequently
this module fixes semantic RHS substitution but does not yet claim that the
generic matcher recognizes every structurally congruent channel name.
-/

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

/-! ## Rule and presentation lookup -/

/-- Fail-closed lookup of a rule-local reflective selection. -/
def reflectiveRuleForRule? (lang : LanguageDef) (rule : RewriteRule) :
    Option ReflectiveRuleDecl :=
  match lang.reflectiveRules.filter fun declaration =>
      declaration.rewriteRule == rule.name with
  | [declaration] => some declaration
  | _ => none

/-- Fail-closed lookup of a reusable reflective presentation by name. -/
def presentationNamed? (lang : LanguageDef) (name : String) :
    Option ReflectivePresentationDecl :=
  match lang.reflectivePresentations.filter fun declaration =>
      declaration.name == name with
  | [declaration] => some declaration
  | _ => none

/-- Presentation used to compare repeated metavariable occurrences. -/
def matchingPresentationForRule?
    (lang : LanguageDef) (rule : RewriteRule) :
    Option ReflectivePresentationDecl :=
  match reflectiveRuleForRule? lang rule with
  | some selection => presentationNamed? lang selection.matchingPresentation
  | none => none

/-- Presentation used to interpret explicit substitution in a contractum. -/
def substitutionPresentationForRule?
    (lang : LanguageDef) (rule : RewriteRule) :
    Option ReflectivePresentationDecl :=
  match reflectiveRuleForRule? lang rule with
  | some selection => presentationNamed? lang selection.substitutionPresentation
  | none => none

/-- Rule-local lookup depends only on the two reflective data tables. -/
theorem matchingPresentationForRule?_eq_of_reflectiveData_eq
    {lang₁ lang₂ : LanguageDef}
    (samePresentations :
      lang₁.reflectivePresentations = lang₂.reflectivePresentations)
    (sameRules : lang₁.reflectiveRules = lang₂.reflectiveRules)
    (rule : RewriteRule) :
    matchingPresentationForRule? lang₁ rule =
      matchingPresentationForRule? lang₂ rule := by
  simp [matchingPresentationForRule?, reflectiveRuleForRule?,
    presentationNamed?, samePresentations, sameRules]

theorem substitutionPresentationForRule?_eq_of_reflectiveData_eq
    {lang₁ lang₂ : LanguageDef}
    (samePresentations :
      lang₁.reflectivePresentations = lang₂.reflectivePresentations)
    (sameRules : lang₁.reflectiveRules = lang₂.reflectiveRules)
    (rule : RewriteRule) :
    substitutionPresentationForRule? lang₁ rule =
      substitutionPresentationForRule? lang₂ rule := by
  simp [substitutionPresentationForRule?, reflectiveRuleForRule?,
    presentationNamed?, samePresentations, sameRules]

@[simp] theorem matchingPresentationForRule?_eq_none_of_no_presentations
    {lang : LanguageDef} (empty : lang.reflectivePresentations = [])
    (rule : RewriteRule) :
    matchingPresentationForRule? lang rule = none := by
  unfold matchingPresentationForRule?
  cases reflectiveRuleForRule? lang rule <;>
    simp [presentationNamed?, empty]

@[simp] theorem matchingPresentationForRule?_eq_none_of_no_rules
    {lang : LanguageDef} (empty : lang.reflectiveRules = [])
    (rule : RewriteRule) :
    matchingPresentationForRule? lang rule = none := by
  simp [matchingPresentationForRule?, reflectiveRuleForRule?, empty]

@[simp] theorem substitutionPresentationForRule?_eq_none_of_no_presentations
    {lang : LanguageDef} (empty : lang.reflectivePresentations = [])
    (rule : RewriteRule) :
    substitutionPresentationForRule? lang rule = none := by
  unfold substitutionPresentationForRule?
  cases reflectiveRuleForRule? lang rule <;>
    simp [presentationNamed?, empty]

@[simp] theorem substitutionPresentationForRule?_eq_none_of_no_rules
    {lang : LanguageDef} (empty : lang.reflectiveRules = [])
    (rule : RewriteRule) :
    substitutionPresentationForRule? lang rule = none := by
  simp [substitutionPresentationForRule?, reflectiveRuleForRule?, empty]

/-! ## Static quote-drop normalization -/

/-- Apply the declared quote-drop equation after an application's children
have been normalized. -/
def finishNormalizeReflectiveApply
    (declaration : ReflectivePresentationDecl)
    (constructor : String) (normalizedArguments : List Pattern) : Pattern :=
  if constructor == declaration.quoteConstructor then
    match normalizedArguments with
    | [.apply drop [name]] =>
        if drop == declaration.dropConstructor then name
        else .apply constructor normalizedArguments
    | _ => .apply constructor normalizedArguments
  else
    .apply constructor normalizedArguments

mutual
  /-- Normalize the declared quote-drop equation throughout a pattern.  This
  is the equational operation; it never orients `drop (quote process)` into a
  process step.  Children are normalized before the outer equation is tested,
  so nested quote-drop equations cannot be hidden by an enclosing constructor. -/
  def normalizeReflective
      (declaration : ReflectivePresentationDecl) : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply constructor arguments =>
        finishNormalizeReflectiveApply declaration constructor
          (normalizeReflectiveList declaration arguments)
    | .lambda binderName body =>
        .lambda binderName (normalizeReflective declaration body)
    | .multiLambda arity binderNames body =>
        .multiLambda arity binderNames (normalizeReflective declaration body)
    | .subst body replacement =>
        .subst (normalizeReflective declaration body)
          (normalizeReflective declaration replacement)
    | .collection collectionType elements rest =>
        .collection collectionType
          (normalizeReflectiveList declaration elements) rest

  /-- List recursion for `normalizeReflective`. -/
  def normalizeReflectiveList
      (declaration : ReflectivePresentationDecl) : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns =>
        normalizeReflective declaration pattern ::
          normalizeReflectiveList declaration patterns
end

/-- Normalize an operational substitution replacement while preserving a
quotation introduced by the rewrite rule itself.  The quoted process is
normalized, but the provenance-carrying outer quote is not cancelled. -/
def normalizeReflectiveReplacement
    (declaration : ReflectivePresentationDecl) (replacement : Pattern) : Pattern :=
  match replacement with
  | .apply constructor [payload] =>
      if constructor == declaration.quoteConstructor then
        .apply constructor [normalizeReflective declaration payload]
      else
        normalizeReflective declaration replacement
  | _ => normalizeReflective declaration replacement

/-! ## Provenance-sensitive substitution -/

/-- Substitute in a name after static normalization.  The Boolean records
whether the selected bound variable was actually replaced. -/
def substituteNameMark
    (declaration : ReflectivePresentationDecl)
    (depth : Nat) (replacementName name : Pattern) : Pattern × Bool :=
  match normalizeReflective declaration name with
  | .bvar index =>
      if index == depth then (replacementName, true) else (.bvar index, false)
  | normalized => (normalized, false)

mutual
  /-- Compile paper-style reflective substitution on a process body.

  The operation is structural except at the declared quote and drop
  constructors.  Literal quotation is opaque.  A matched drop exposes its
  payload exactly when substitution supplied a quotation; a free dropped
  quotation is left inert. -/
  def substituteReflective
      (declaration : ReflectivePresentationDecl)
      (depth : Nat) (replacementName : Pattern) : Pattern → Pattern
    | .bvar index =>
        if index == depth then replacementName else .bvar index
    | .fvar name => .fvar name
    | .apply constructor [payload] =>
        if constructor == declaration.quoteConstructor then
          (substituteNameMark declaration depth replacementName
            (.apply constructor [payload])).1
        else if constructor == declaration.dropConstructor then
          let (name, matched) :=
            substituteNameMark declaration depth replacementName payload
          match name, matched with
          | .apply quote [process], true =>
              if quote == declaration.quoteConstructor then process
              else .apply constructor [name]
          | _, _ => .apply constructor [name]
        else
          .apply constructor
            [substituteReflective declaration depth replacementName payload]
    | .apply constructor arguments =>
        .apply constructor
          (substituteReflectiveList declaration depth replacementName arguments)
    | .lambda binderName body =>
        .lambda binderName
          (substituteReflective declaration (depth + 1) replacementName body)
    | .multiLambda arity binderNames body =>
        .multiLambda arity binderNames
          (substituteReflective declaration (depth + arity) replacementName body)
    | .subst body replacement =>
        .subst
          (substituteReflective declaration (depth + 1) replacementName body)
          (substituteReflective declaration depth replacementName replacement)
    | .collection collectionType elements rest =>
        .collection collectionType
          (substituteReflectiveList declaration depth replacementName elements) rest

  /-- List recursion for `substituteReflective`. -/
  def substituteReflectiveList
      (declaration : ReflectivePresentationDecl)
      (depth : Nat) (replacementName : Pattern) : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns =>
        substituteReflective declaration depth replacementName pattern ::
          substituteReflectiveList declaration depth replacementName patterns
end

/-! ## Binding application -/

mutual
  /-- Apply matcher bindings while interpreting explicit `.subst` nodes using
  the selected reflective declaration.  All other binding behavior, including
  collection-rest handling, matches `Match.applyBindings`. -/
  def applyBindingsReflective
      (declaration : ReflectivePresentationDecl)
      (bindings : Bindings) : Pattern → Pattern
    | .fvar name =>
        match bindings.find? (·.1 == name) with
        | some (_, value) => value
        | none => .fvar name
    | .bvar index => .bvar index
    | .apply constructor arguments =>
        .apply constructor
          (applyBindingsReflectiveList declaration bindings arguments)
    | .lambda binderName body =>
        .lambda binderName (applyBindingsReflective declaration bindings body)
    | .multiLambda arity binderNames body =>
        .multiLambda arity binderNames
          (applyBindingsReflective declaration bindings body)
    | .subst body replacement =>
        let body' := applyBindingsReflective declaration bindings body
        let replacement' :=
          normalizeReflectiveReplacement declaration
            (applyBindingsReflective declaration bindings replacement)
        substituteReflective declaration 0 replacement' body'
    | .collection collectionType elements rest =>
        let elements' :=
          applyBindingsReflectiveList declaration bindings elements
        let (restElements, unresolvedRest) := match rest with
          | some restName =>
              match bindings.find? (·.1 == restName) with
              | some (_, .collection boundType boundElements none) =>
                  if boundType == collectionType then (boundElements, none)
                  else ([], some restName)
              | _ => ([], some restName)
          | none => ([], none)
        .collection collectionType (elements' ++ restElements) unresolvedRest

  /-- List recursion for reflective binding application. -/
  def applyBindingsReflectiveList
      (declaration : ReflectivePresentationDecl)
      (bindings : Bindings) : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns =>
        applyBindingsReflective declaration bindings pattern ::
          applyBindingsReflectiveList declaration bindings patterns
end

/-- Rule-aware binding application compiled from the authored `LanguageDef`.
The absence of a unique declaration is definitionally backward compatible. -/
def applyBindingsForRule
    (lang : LanguageDef) (rule : RewriteRule) (bindings : Bindings) : Pattern :=
  match substitutionPresentationForRule? lang rule with
  | some declaration => applyBindingsReflective declaration bindings rule.right
  | none => applyBindings bindings rule.right

/-- Rule-aware substitution is unchanged when two languages share both
reflective data tables. -/
theorem applyBindingsForRule_eq_of_reflectiveData_eq
    {lang₁ lang₂ : LanguageDef}
    (samePresentations :
      lang₁.reflectivePresentations = lang₂.reflectivePresentations)
    (sameRules : lang₁.reflectiveRules = lang₂.reflectiveRules)
    (rule : RewriteRule) (bindings : Bindings) :
    applyBindingsForRule lang₁ rule bindings =
      applyBindingsForRule lang₂ rule bindings := by
  simp only [applyBindingsForRule]
  rw [substitutionPresentationForRule?_eq_of_reflectiveData_eq
    samePresentations sameRules rule]

theorem applyBindingsForRule_eq_syntactic_of_no_presentation
    {lang : LanguageDef} {rule : RewriteRule}
    (missing : substitutionPresentationForRule? lang rule = none)
    (bindings : Bindings) :
    applyBindingsForRule lang rule bindings = applyBindings bindings rule.right := by
  simp [applyBindingsForRule, missing]

@[simp] theorem applyBindingsForRule_eq_syntactic_of_no_presentations
    {lang : LanguageDef} (empty : lang.reflectivePresentations = [])
    (rule : RewriteRule) (bindings : Bindings) :
    applyBindingsForRule lang rule bindings = applyBindings bindings rule.right := by
  apply applyBindingsForRule_eq_syntactic_of_no_presentation
  exact substitutionPresentationForRule?_eq_none_of_no_presentations empty rule

@[simp] theorem applyBindingsForRule_eq_syntactic_of_no_reflectiveRules
    {lang : LanguageDef} (empty : lang.reflectiveRules = [])
    (rule : RewriteRule) (bindings : Bindings) :
    applyBindingsForRule lang rule bindings = applyBindings bindings rule.right := by
  apply applyBindingsForRule_eq_syntactic_of_no_presentation
  exact substitutionPresentationForRule?_eq_none_of_no_rules empty rule

/-! ## Executable boundary examples -/

private def fixtureDeclaration : ReflectivePresentationDecl where
  name := "fixture"
  processSort := "Proc"
  nameSort := "Name"
  quoteConstructor := "NQuote"
  dropConstructor := "PDrop"
  parallelCollection := .hashBag
  parallelUnitConstructor := "PZero"
  quoteDropEquation := "QuoteDrop"

/-- Positive: a COMM-supplied quotation exposes the matched dropped name. -/
example :
    substituteReflective fixtureDeclaration 0
        (.apply "NQuote" [.apply "PZero" []])
        (.apply "PDrop" [.bvar 0]) =
      .apply "PZero" [] := by
  rfl

/-- Regression: normalization must see a quote-drop equation nested beneath
an ordinary drop, without turning the outer drop into an executable step. -/
example :
    normalizeReflective fixtureDeclaration
        (.apply "PDrop"
          [.apply "NQuote" [.apply "PDrop" [.fvar "x"]]]) =
      .apply "PDrop" [.fvar "x"] := by
  rfl

/-- Regression: a quote introduced by COMM remains present even when its
payload is a drop; only the payload is statically normalized. -/
example :
    let payload := .apply "PDrop"
      [.apply "NQuote" [.apply "PZero" []]]
    substituteReflective fixtureDeclaration 0
        (normalizeReflectiveReplacement fixtureDeclaration
          (.apply "NQuote" [payload]))
        (.apply "PDrop" [.bvar 0]) =
      payload := by
  rfl

/-- Negative: a free dropped quotation is not an executable reduction. -/
example :
    substituteReflective fixtureDeclaration 0
        (.apply "NQuote" [.apply "PZero" []])
        (.apply "PDrop" [.apply "NQuote" [.apply "PZero" []]]) =
      .apply "PDrop" [.apply "NQuote" [.apply "PZero" []]] := by
  rfl

/-- Negative: substitution does not enter literal quoted code. -/
example :
    substituteReflective fixtureDeclaration 0
        (.apply "NQuote" [.apply "PZero" []])
        (.apply "NQuote"
          [.apply "POutput" [.bvar 0, .apply "PZero" []]]) =
      .apply "NQuote"
        [.apply "POutput" [.bvar 0, .apply "PZero" []]] := by
  rfl

/-- Regression: a free drop around quoted code remains inert, and substitution
does not enter the quoted process through the outer unary constructor. -/
example :
    substituteReflective fixtureDeclaration 0
        (.apply "NQuote" [.apply "PZero" []])
        (.apply "PDrop"
          [.apply "NQuote"
            [.apply "POutput" [.bvar 0, .apply "PZero" []]]]) =
      .apply "PDrop"
        [.apply "NQuote"
          [.apply "POutput" [.bvar 0, .apply "PZero" []]]] := by
  rfl

end Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
