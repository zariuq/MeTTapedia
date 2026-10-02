import Mettapedia.GSLT.LanguageDef.TypingInversion

/-!
# What the closed terms of a sort look like

A closed term of a sort is a sorted pattern satisfying four further
conditions: it is ground, its binder metadata is canonical, it is an object
pattern, and it is locally scoped.  This module separates the two parts and
reads each of them at a constructor application.

* The four conditions hold of an application exactly when they hold of each
  argument.
* In a validated language an application of a declared constructor is typed
  by that constructor's own declaration and by no other.
* Arguments are typed by a list of plain parameters exactly when they are as
  many and each has the type of its parameter.
* A closed term of a sort is headed by a declared constructor of that sort:
  an application of an ordinary constructor, or the bare collection of a
  collection constructor.

Together they turn "closed term of sort `s`" into a case analysis on the
constructors of `s`, in both directions.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.WellSorted

open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The conditions a closed term satisfies besides having its sort. -/
def ClosedShape (pattern : Pattern) : Prop :=
  pattern.isGround = true ∧ pattern.hasCanonicalBinderMetadata = true ∧
    isObjectPattern pattern = true ∧ pattern.isWellScopedAt 0 = true

/-- A closed term is a sorted pattern of closed shape. -/
theorem closedTermWellSorted_iff {language : LanguageDef} {sort : LangSort language}
    {pattern : Pattern} :
    ClosedTermWellSorted language sort pattern ↔
      HasSort language FreeTypeContext.empty [] pattern sort.1 ∧ ClosedShape pattern :=
  Iff.rfl

/-- A constructor application has closed shape exactly when each of its
arguments has. -/
theorem closedShape_apply {label : String} {arguments : List Pattern} :
    ClosedShape (.apply label arguments) ↔ ∀ argument ∈ arguments, ClosedShape argument := by
  induction arguments with
  | nil =>
      simp [ClosedShape, Pattern.isGround, Pattern.isGroundAt, Pattern.isGroundListAt,
        Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
        isObjectPattern, isObjectPatternList, Pattern.isWellScopedAt,
        Pattern.isWellScopedListAt]
  | cons head tail recurse =>
      simp only [ClosedShape, Pattern.isGround, Pattern.isGroundAt, Pattern.isGroundListAt,
        Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
        isObjectPattern, isObjectPatternList, Pattern.isWellScopedAt,
        Pattern.isWellScopedListAt, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
        at recurse ⊢
      rw [← recurse]
      tauto

/-- In a validated language, an application of a declared constructor is
typed by that constructor's declaration: its type is the constructor's sort
and its arguments are typed by the constructor's parameters. -/
theorem hasType_apply_iff {language : LanguageDef} (valid : language.validate = [])
    {rule : GrammarRule} (membership : rule ∈ language.terms)
    (notBare : ¬ UsesBareCollection rule)
    {free : FreeTypeContext} {bound : List TypeExpr} {arguments : List Pattern}
    {type : TypeExpr} :
    HasType language free bound (.apply rule.label arguments) type ↔
      type = .base rule.category ∧
        ArgumentsHaveTypes language free bound arguments rule.params := by
  constructor
  · intro typed
    obtain ⟨other, otherMember, sameLabel, typeEq, -, argumentsTyped⟩ := typed.apply_inv
    have same : other = rule :=
      List.inj_on_of_nodup_map
        (LanguageDef.constructorLabels_nodup_of_validate_eq_nil language valid)
        otherMember membership sameLabel
    subst same
    exact ⟨typeEq, argumentsTyped⟩
  · rintro ⟨rfl, argumentsTyped⟩
    exact HasType.constructor membership notBare argumentsTyped

/-- Arguments are typed by a list of plain parameters exactly when there are
as many arguments as parameters and each has the type of its parameter. -/
theorem argumentsHaveTypes_simple_iff {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} (arguments : List Pattern)
    (parameters : List (String × TypeExpr)) :
    ArgumentsHaveTypes language free bound arguments
        (parameters.map fun parameter => TermParam.simple parameter.1 parameter.2) ↔
      List.Forall₂
        (fun argument (parameter : String × TypeExpr) =>
          HasType language free bound argument parameter.2)
        arguments parameters := by
  induction parameters generalizing arguments with
  | nil =>
      constructor
      · intro typed
        cases typed
        exact .nil
      · intro pointwise
        cases pointwise
        exact .nil
  | cons parameter parameters recurse =>
      constructor
      · intro typed
        cases typed with
        | cons representation expected headTyped tailTyped =>
            simp only [parameterType?, Option.some.injEq] at expected
            subst expected
            exact .cons headTyped ((recurse _).mp tailTyped)
      · intro pointwise
        cases pointwise with
        | cons headTyped tailTyped =>
            exact .cons trivial rfl headTyped ((recurse _).mpr tailTyped)

/-- **The head of a closed term.**  A closed term of a sort is an application
of a declared constructor of that sort to arguments typed by its parameters,
or the bare collection, with no open tail, of a declared collection
constructor of that sort. -/
theorem ClosedTermWellSorted.head_cases {language : LanguageDef}
    {sort : LangSort language} {pattern : Pattern}
    (closed : ClosedTermWellSorted language sort pattern) :
    (∃ rule arguments, rule ∈ language.terms ∧ rule.category = sort.1 ∧
        ¬ UsesBareCollection rule ∧ pattern = .apply rule.label arguments ∧
          ArgumentsHaveTypes language FreeTypeContext.empty [] arguments rule.params) ∨
      (∃ rule collectionType elements, rule ∈ language.terms ∧ rule.category = sort.1 ∧
        UsesBareCollection rule ∧ pattern = .collection collectionType elements none) := by
  obtain ⟨typed, -, -, object, -⟩ := closed
  have typed' : HasType language FreeTypeContext.empty [] pattern (.base sort.1) := typed
  generalize expected : TypeExpr.base sort.1 = type at typed'
  cases typed' with
  | bvar lookup => simp at lookup
  | fvar lookup => simp [FreeTypeContext.empty] at lookup
  | constructor membership notBare argumentsTyped =>
      simp only [TypeExpr.base.injEq] at expected
      exact Or.inl ⟨_, _, membership, expected.symm, notBare, rfl, argumentsTyped⟩
  | lambda _ => cases expected
  | multiLambda _ => cases expected
  | subst _ _ => simp [isObjectPattern] at object
  | collection _ => cases expected
  | @collectionConstructor _ rule parameterName collectionType elements rest elementType
      membership parameters _ =>
      simp only [TypeExpr.base.injEq] at expected
      simp only [isObjectPattern, Bool.and_eq_true, Option.isNone_iff_eq_none] at object
      obtain ⟨rfl, -⟩ := object
      exact Or.inr ⟨rule, collectionType, elements, membership, expected.symm,
        ⟨parameterName, collectionType, elementType, parameters⟩, rfl⟩

end Mettapedia.GSLT.LanguageDef.WellSorted
