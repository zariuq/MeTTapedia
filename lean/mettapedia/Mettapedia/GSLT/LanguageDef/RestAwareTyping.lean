import Mettapedia.GSLT.LanguageDef.SchemaTyping

/-!
# Typing schema collection rests

`WellSorted.HasType` types the elements of a collection but does not inspect
its optional rest metavariable. This separate judgment preserves all of that
typing structure and requires each rest, including nested rests, to have the
collection type determined by the same derivation. It describes rule schemas;
the rest-free object-term carrier remains the one in `WellSorted`.
-/

namespace Mettapedia.GSLT.LanguageDef.RestAwareTyping

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax

set_option autoImplicit false

/-- A schema rest denotes a collection at precisely its enclosing element
type. No declaration is required when the collection has no rest. -/
def RestHasType (free : FreeTypeContext) (kind : CollType)
    (elementType : TypeExpr) : Option String → Prop
  | none => True
  | some name => free name = some (.collection kind elementType)

mutual
  /-- Declaration-derived typing of a schema, including every collection
  rest and every nested constructor argument. -/
  inductive HasType (language : LanguageDef) (free : FreeTypeContext) :
      List TypeExpr → Pattern → TypeExpr → Prop where
    | bvar {bound : List TypeExpr} {index : Nat} {type : TypeExpr} :
        bound[index]? = some type →
        HasType language free bound (.bvar index) type
    | fvar {bound : List TypeExpr} {name : String} {type : TypeExpr} :
        free name = some type →
        HasType language free bound (.fvar name) type
    | constructor
        {bound : List TypeExpr} {rule : GrammarRule} {arguments : List Pattern} :
        rule ∈ language.terms →
        ¬ UsesBareCollection rule →
        ArgumentsHaveTypes language free bound arguments rule.params →
        HasType language free bound (.apply rule.label arguments)
          (.base rule.category)
    | lambda
        {bound : List TypeExpr} {binder : Option String} {body : Pattern}
        {domain codomain : TypeExpr} :
        HasType language free (domain :: bound) body codomain →
        HasType language free bound (.lambda binder body)
          (.arrow domain codomain)
    | multiLambda
        {bound : List TypeExpr} {arity : Nat} {binders : List String}
        {body : Pattern} {domain codomain : TypeExpr} :
        HasType language free (List.replicate arity domain ++ bound) body codomain →
        HasType language free bound (.multiLambda arity binders body)
          (.arrow (.multiBinder domain) codomain)
    | subst
        {bound : List TypeExpr} {body replacement : Pattern}
        {domain codomain : TypeExpr} :
        HasType language free (domain :: bound) body codomain →
        HasType language free bound replacement domain →
        HasType language free bound (.subst body replacement) codomain
    | collection
        {bound : List TypeExpr} {kind : CollType}
        {elements : List Pattern} {rest : Option String} {elementType : TypeExpr} :
        ElementsHaveType language free bound elements elementType →
        RestHasType free kind elementType rest →
        HasType language free bound (.collection kind elements rest)
          (.collection kind elementType)
    | collectionConstructor
        {bound : List TypeExpr} {rule : GrammarRule} {parameterName : String}
        {kind : CollType} {elements : List Pattern}
        {rest : Option String} {elementType : TypeExpr} :
        rule ∈ language.terms →
        rule.params = [.simple parameterName (.collection kind elementType)] →
        ElementsHaveType language free bound elements elementType →
        RestHasType free kind elementType rest →
        HasType language free bound (.collection kind elements rest)
          (.base rule.category)

  /-- Ordered, representation-aware constructor arguments. -/
  inductive ArgumentsHaveTypes (language : LanguageDef)
      (free : FreeTypeContext) :
      List TypeExpr → List Pattern → List TermParam → Prop where
    | nil {bound : List TypeExpr} :
        ArgumentsHaveTypes language free bound [] []
    | cons
        {bound : List TypeExpr} {argument : Pattern} {arguments : List Pattern}
        {parameter : TermParam} {parameters : List TermParam}
        {expected : TypeExpr} :
        MatchesParameterRepresentation parameter argument →
        parameterType? parameter = some expected →
        HasType language free bound argument expected →
        ArgumentsHaveTypes language free bound arguments parameters →
        ArgumentsHaveTypes language free bound
          (argument :: arguments) (parameter :: parameters)

  /-- Every collection element has its declared element type. -/
  inductive ElementsHaveType (language : LanguageDef)
      (free : FreeTypeContext) :
      List TypeExpr → List Pattern → TypeExpr → Prop where
    | nil (bound : List TypeExpr) (elementType : TypeExpr) :
        ElementsHaveType language free bound [] elementType
    | cons
        {bound : List TypeExpr} {element : Pattern} {elements : List Pattern}
        {elementType : TypeExpr} :
        HasType language free bound element elementType →
        ElementsHaveType language free bound elements elementType →
        ElementsHaveType language free bound (element :: elements) elementType
end

mutual
  /-- Forget the extra rest premises and recover the original judgment. -/
  theorem HasType.forget
      {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (typed : HasType language free bound pattern type) :
      WellSorted.HasType language free bound pattern type := by
    cases typed with
    | bvar lookup => exact .bvar lookup
    | fvar lookup => exact .fvar lookup
    | constructor membership shape arguments =>
        exact .constructor membership shape arguments.forget
    | lambda body => exact .lambda body.forget
    | multiLambda body => exact .multiLambda body.forget
    | subst body replacement => exact .subst body.forget replacement.forget
    | collection elements _ => exact .collection elements.forget
    | collectionConstructor membership shape elements _ =>
        exact .collectionConstructor membership shape elements.forget

  theorem ArgumentsHaveTypes.forget
      {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language free bound arguments parameters) :
      WellSorted.ArgumentsHaveTypes language free bound arguments parameters := by
    cases typed with
    | nil => exact .nil
    | cons representation expected argument rest =>
        exact .cons representation expected argument.forget rest.forget

  theorem ElementsHaveType.forget
      {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (typed : ElementsHaveType language free bound elements elementType) :
      WellSorted.ElementsHaveType language free bound elements elementType := by
    cases typed with
    | nil => exact .nil _ _
    | cons element rest => exact .cons element.forget rest.forget
end

mutual
  /-- On object patterns the additional schema-rest condition is vacuous.
  This is the exact comparison with the existing object-term judgment. -/
  theorem HasType.ofObject
      {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (typed : WellSorted.HasType language free bound pattern type)
      (object : isObjectPattern pattern = true) :
      HasType language free bound pattern type := by
    cases typed with
    | bvar lookup => exact .bvar lookup
    | fvar lookup => exact .fvar lookup
    | constructor membership shape arguments =>
        exact .constructor membership shape
          (ArgumentsHaveTypes.ofObjects arguments
            (by simpa [isObjectPattern] using object))
    | lambda body =>
        exact .lambda (HasType.ofObject body (by simpa [isObjectPattern] using object))
    | multiLambda body =>
        exact .multiLambda (HasType.ofObject body (by simpa [isObjectPattern] using object))
    | subst body replacement =>
        simp [isObjectPattern] at object
    | @collection bound kind elements rest elementType elementsTyped =>
        simp only [isObjectPattern, Bool.and_eq_true] at object
        cases rest with
        | none =>
            exact .collection (ElementsHaveType.ofObjects elementsTyped object.2) trivial
        | some name =>
            simp at object
    | @collectionConstructor bound rule parameterName kind elements rest elementType
        membership shape elementsTyped =>
        simp only [isObjectPattern, Bool.and_eq_true] at object
        cases rest with
        | none =>
            exact .collectionConstructor membership shape
              (ElementsHaveType.ofObjects elementsTyped object.2) trivial
        | some name =>
            simp at object

  theorem ArgumentsHaveTypes.ofObjects
      {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (typed : WellSorted.ArgumentsHaveTypes language free bound arguments parameters)
      (objects : isObjectPatternList arguments = true) :
      ArgumentsHaveTypes language free bound arguments parameters := by
    cases typed with
    | nil => exact .nil
    | cons representation expected argument rest =>
        simp only [isObjectPatternList, Bool.and_eq_true] at objects
        exact .cons representation expected
          (HasType.ofObject argument objects.1)
          (ArgumentsHaveTypes.ofObjects rest objects.2)

  theorem ElementsHaveType.ofObjects
      {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (typed : WellSorted.ElementsHaveType language free bound elements elementType)
      (objects : isObjectPatternList elements = true) :
      ElementsHaveType language free bound elements elementType := by
    cases typed with
    | nil => exact .nil _ _
    | cons element rest =>
        simp only [isObjectPatternList, Bool.and_eq_true] at objects
        exact .cons (HasType.ofObject element objects.1)
          (ElementsHaveType.ofObjects rest objects.2)
end

/-- Any typed collection rest must be declared at the enclosing collection
type, whether the collection is a value or an authored constructor. -/
theorem HasType.restDeclared
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {kind : CollType} {elements : List Pattern}
    {restName : String} {expected : TypeExpr}
    (typed : HasType language free bound
      (.collection kind elements (some restName)) expected) :
    ∃ elementType, free restName = some (.collection kind elementType) := by
  cases typed with
  | collection _ restTyped => exact ⟨_, restTyped⟩
  | collectionConstructor _ _ _ restTyped => exact ⟨_, restTyped⟩

/-- A schema pair has one common type and types every collection rest in its
own authored context. -/
def SchemaSidesHaveType (language : LanguageDef)
    (typeContext : List (String × TypeExpr))
    (left right : Pattern) : Prop :=
  ∃ type,
    HasType language (FreeTypeContext.ofList typeContext) [] left type ∧
    HasType language (FreeTypeContext.ofList typeContext) [] right type

theorem SchemaSidesHaveType.forget
    {language : LanguageDef} {typeContext : List (String × TypeExpr)}
    {left right : Pattern}
    (typed : SchemaSidesHaveType language typeContext left right) :
    SchemaSidesWellSorted language typeContext left right := by
  obtain ⟨type, leftTyped, rightTyped⟩ := typed
  exact ⟨type, leftTyped.forget, rightTyped.forget⟩

/-- Both sides of one authored rewrite have one type, with every rest typed. -/
def RewriteHasType (language : LanguageDef) (rewrite : RewriteRule) : Prop :=
  SchemaSidesHaveType language rewrite.typeContext rewrite.left rewrite.right

theorem RewriteHasType.forget
    {language : LanguageDef} {rewrite : RewriteRule}
    (typed : RewriteHasType language rewrite) :
    RewriteWellSorted language rewrite :=
  SchemaSidesHaveType.forget typed

/-- The same condition for an authored bidirectional equation. -/
def EquationHasType (language : LanguageDef) (equation : Equation) : Prop :=
  SchemaSidesHaveType language equation.typeContext equation.left equation.right

theorem EquationHasType.forget
    {language : LanguageDef} {equation : Equation}
    (typed : EquationHasType language equation) :
    EquationWellSorted language equation :=
  SchemaSidesHaveType.forget typed

/-- Every rewrite of one validated authored presentation has typed schema
sides, including every collection rest. Premise typing is a separate law. -/
def RewritesHaveType (presentation : ValidatedLanguageDef) : Prop :=
  ∀ rewrite ∈ presentation.language.rewrites,
    RewriteHasType presentation.language rewrite

theorem RewritesHaveType.forget
    {presentation : ValidatedLanguageDef}
    (typed : RewritesHaveType presentation) :
    RewritesWellSorted presentation := by
  intro rewrite membership
  exact (typed rewrite membership).forget

/-- Equation-side typing for every equation of an authored presentation. -/
def EquationsHaveType (presentation : ValidatedLanguageDef) : Prop :=
  ∀ equation ∈ presentation.language.equations,
    EquationHasType presentation.language equation

theorem EquationsHaveType.forget
    {presentation : ValidatedLanguageDef}
    (typed : EquationsHaveType presentation) :
    EquationsWellSorted presentation := by
  intro equation membership
  exact (typed equation membership).forget

end Mettapedia.GSLT.LanguageDef.RestAwareTyping
