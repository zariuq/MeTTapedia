import Mettapedia.GSLT.LanguageDef.SchemaTyping
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-! # Sorting checks for arbitrary declared rewrite systems

Language-specific controls are in `GSLT.Examples.AuthoredRuleSorting`.
-/

namespace Mettapedia.GSLT.LanguageDef.AuthoredRuleSorting

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted

set_option autoImplicit false

/-! ## Deciding the sorting of an authored rule -/

/-- Both sides of a rule inhabit one declared base sort, in the rule's own
declared variable context.  This decides a sufficient condition for
`RewriteWellSorted`, whose type is existentially quantified: searching the
declared sorts is what makes the search finite. -/
def checkRewriteWellSorted (lang : LanguageDef) (rule : RewriteRule) : Bool :=
  lang.types.any fun declaration =>
    checkHasType lang (FreeTypeContext.ofList rule.typeContext) []
        rule.left (.base declaration.name)
      && checkHasType lang (FreeTypeContext.ofList rule.typeContext) []
        rule.right (.base declaration.name)

/-- **The decision is sound for the declarative property.**  A rule the check
accepts really is sorted in the sense the schema layer states. -/
theorem checkRewriteWellSorted_sound {lang : LanguageDef} {rule : RewriteRule}
    (checked : checkRewriteWellSorted lang rule = true) :
    RewriteWellSorted lang rule := by
  simp only [checkRewriteWellSorted, List.any_eq_true, Bool.and_eq_true] at checked
  obtain ⟨declaration, _, leftChecked, rightChecked⟩ := checked
  exact ⟨.base declaration.name, checkHasType_sound leftChecked,
    checkHasType_sound rightChecked⟩

/-- How many of a language's rules the check accepts. -/
def sortedCount (lang : LanguageDef) : Nat :=
  (lang.rewrites.filter (checkRewriteWellSorted lang)).length


/-- **No collection pattern with a rest is ever sorted**, in any language, at
any type, in any context.  The rest variable is a metavariable of the rule with
nowhere to declare its type, so there is nothing to check it against. -/
theorem collection_with_rest_never_sorted
    (lang : LanguageDef) (free : FreeTypeContext) (bound : List TypeExpr)
    (kind : CollType) (elements : List Pattern) (restVar : String)
    (expected : TypeExpr) :
    checkHasType lang free bound (.collection kind elements restVar) expected
      = false := rfl

/-- Removing the rest from a shipped left-hand side, and nothing else. -/
def dropRest : Pattern → Pattern
  | .collection kind elements _ => .collection kind elements none
  | pattern => pattern


/-- **No explicit substitution is ever sorted**, in any language, at any type.
This is what the intrinsic pure fragment's beta rule runs into: its right-hand
side is a schema substitution. -/
theorem subst_never_sorted
    (lang : LanguageDef) (free : FreeTypeContext) (bound : List TypeExpr)
    (body replacement : Pattern) (expected : TypeExpr) :
    checkHasType lang free bound (.subst body replacement) expected = false :=
  rfl


/-- **A variable absent from the declared context is never sorted.** -/
theorem undeclared_fvar_never_sorted
    (lang : LanguageDef) (bound : List TypeExpr) (varName : String)
    (expected : TypeExpr) :
    checkHasType lang (FreeTypeContext.ofList []) bound (.fvar varName) expected
      = false := by
  simp [checkHasType, FreeTypeContext.ofList]


/-- **The judgment ignores the rest entirely.**  A collection's typing survives
replacing its rest by any other, including by none. -/
theorem hasType_rest_irrelevant {lang : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {kind : CollType} {elements : List Pattern}
    {restOne restTwo : Option String} {expected : TypeExpr} :
    HasType lang free bound (.collection kind elements restOne) expected →
    HasType lang free bound (.collection kind elements restTwo) expected := by
  intro typed
  cases typed with
  | collection elementsTyped => exact .collection elementsTyped
  | collectionConstructor membership shape elementsTyped =>
      exact .collectionConstructor membership shape elementsTyped


/-- The rest of a top-level collection is declared at that collection's own
type.  This is the shape a rule side actually has in the reflective calculus;
the nested case wants the condition inside the typing judgment's collection
cases, which is a change to `HasType` rather than an addition beside it. -/
def topRestDeclared (free : FreeTypeContext) (elementType : TypeExpr) :
    Pattern → Prop
  | .collection kind _ (some restVar) =>
      free restVar = some (.collection kind elementType)
  | _ => True

instance (free : FreeTypeContext) (elementType : TypeExpr) (pattern : Pattern)
    [DecidableEq TypeExpr] : Decidable (topRestDeclared free elementType pattern) := by
  unfold topRestDeclared
  split <;> infer_instance


end Mettapedia.GSLT.LanguageDef.AuthoredRuleSorting
