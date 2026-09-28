import Mettapedia.GSLT.Examples.RestAwareMorphism
import Mettapedia.GSLT.LanguageDef.TypedOccurrenceSubstitution
import Mettapedia.GSLT.LanguageDef.RestAwareOccurrenceSubstitution

/-!
# A many-sorted executable occurrence

An Atom dependency is supplied by an ambient Atom below a local Proc binder.
The authored `Embed` constructor requires Atom and returns Proc. The exact
runtime substitution retains the ambient variable at index one. A contrasting
well-scoped Proc argument passes the runtime scope check but has the wrong
authored sort, so it cannot be supplied to the typed theorem.
-/

namespace Mettapedia.GSLT.Examples.TypedOccurrenceSubstitution

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.Examples.RestAwareMorphism
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding

set_option autoImplicit false

private abbrev atom : TypeExpr := .base "Atom"
private abbrev proc : TypeExpr := .base "Proc"

def ambientAtomArgument :
    TypedOccurrenceArguments collectionLanguage FreeTypeContext.empty
      [atom] [atom] [proc] where
  argument := fun _ => .bvar 1
  typed := by
    intro index
    rcases index with ⟨index, inBounds⟩
    have inBounds' : index < 1 := by simpa using inBounds
    have indexZero : index = 0 := by omega
    subst index
    have typedAtom : HasType collectionLanguage FreeTypeContext.empty
        ([proc] ++ [atom]) (.bvar 1) atom :=
      (RestAwareTyping.checkSchemaHasType_sound
        (by decide +kernel)).forget
    simpa using typedAtom

theorem embeddedDependencyTyped :
    HasType collectionLanguage FreeTypeContext.empty
      ([atom] ++ [atom]) (.apply "Embed" [.bvar 0]) proc :=
  (RestAwareTyping.checkSchemaHasType_sound (by decide +kernel)).forget

/-- The general law types the actual substitution read by the executor. -/
theorem embeddedAmbientOutputTyped :
    HasType collectionLanguage FreeTypeContext.empty
      ([proc] ++ [atom])
      (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
        (occurrenceAssignment 1 1 ambientAtomArgument.raw)
        (.apply "Embed" [.bvar 0])) proc :=
  embeddedDependencyTyped.substituteOccurrence ambientAtomArgument

/-- Both the executable result and its authored typing retain index one. -/
theorem embeddedAmbientOutput :
    instantiateValue?
      { dependencies := [atom], ambient := 1,
        body := .apply "Embed" [.bvar 0] }
      1 1 ambientAtomArgument.raw =
      some (.apply "Embed" [.bvar 1]) := by
  simpa [ambientAtomArgument, TypedOccurrenceArguments.raw,
    occurrenceAssignment,
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute] using
    ambientAtomArgument.instantiateValue?_typed embeddedDependencyTyped

/-- The declaration-shaped argument list gives the same open executable
result; the ambient Atom remains at index one below the local Proc binder. -/
theorem embeddedAmbientOutputFromList :
    instantiateValue?
      { dependencies := [atom], ambient := 1,
        body := .apply "Embed" [.bvar 0] }
      1 1 [.bvar 1] = some (.apply "Embed" [.bvar 1]) := by
  have argumentsTyped : List.Forall₂
      (fun argument dependency =>
        HasType collectionLanguage FreeTypeContext.empty
          ([proc] ++ [atom]) argument dependency)
      [.bvar 1] [atom] :=
    .cons (RestAwareTyping.checkSchemaHasType_sound
      (by decide +kernel)).forget .nil
  simpa [occurrenceAssignment,
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute] using
    instantiateValue?_typedList embeddedDependencyTyped argumentsTyped

/-- The executor checks scope, while the typed profile additionally rejects
an occurrence argument at the wrong authored sort. -/
theorem localProcNotAtom :
    ¬ HasType collectionLanguage FreeTypeContext.empty
      ([proc] ++ [atom]) (.bvar 0) atom := by
  intro typed
  cases typed with
  | bvar lookup => simp [atom, proc] at lookup

theorem wrongSortStillPassesRawScopeCheck :
    instantiateValue?
      { dependencies := [atom], ambient := 1, body := .bvar 0 }
      1 1 [.bvar 0] = some (.bvar 0) := by
  decide +kernel

private def restContext : FreeTypeContext :=
  FreeTypeContext.ofList
    [("rest", .collection .hashBag proc)]

def restAwareAmbientArgument :
    RestAwareTyping.TypedOccurrenceArguments collectionLanguage
      restContext [atom] [atom] [proc] where
  argument := fun _ => .bvar 1
  typed := by
    intro index
    rcases index with ⟨index, inBounds⟩
    have inBounds' : index < 1 := by simpa using inBounds
    have indexZero : index = 0 := by omega
    subst index
    have typedAtom : RestAwareTyping.HasType collectionLanguage
        restContext ([proc] ++ [atom]) (.bvar 1) atom :=
      RestAwareTyping.checkSchemaHasType_sound (by decide +kernel)
    simpa using typedAtom

private def restSchemaBody : Pattern :=
  .lambda none
    (.collection .hashBag
      [.apply "Embed" [.bvar 1]] (some "rest"))

theorem restSchemaBodyTyped :
    RestAwareTyping.HasType collectionLanguage restContext
      ([atom] ++ [atom]) restSchemaBody
      (.arrow proc (.collection .hashBag proc)) :=
  RestAwareTyping.checkSchemaHasType_sound (by decide +kernel)

/-- Both the inner lambda and the outer occurrence binder move the ambient
Atom below them; the collection rest stays declared and unchanged. -/
theorem restAwareOpenOutputTyped :
    RestAwareTyping.HasType collectionLanguage restContext
      ([proc] ++ [atom])
      (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
        (occurrenceAssignment 1 1 restAwareAmbientArgument.raw)
        restSchemaBody)
      (.arrow proc (.collection .hashBag proc)) :=
  restSchemaBodyTyped.substituteOccurrence restAwareAmbientArgument

theorem restAwareOpenOutput :
    instantiateValue?
      { dependencies := [atom], ambient := 1, body := restSchemaBody }
      1 1 restAwareAmbientArgument.raw =
      some (.lambda none
        (.collection .hashBag
          [.apply "Embed" [.bvar 2]] (some "rest"))) := by
  simpa [restAwareAmbientArgument,
    RestAwareTyping.TypedOccurrenceArguments.raw,
    RestAwareTyping.TypedOccurrenceArguments.forget,
    TypedOccurrenceArguments.raw, restSchemaBody,
    occurrenceAssignment,
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute,
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift,
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars] using
    restAwareAmbientArgument.instantiateValue?_typed restSchemaBodyTyped

/-- The same open, rest-bearing result follows from a declaration-shaped
singleton argument list rather than an independently constructed family. -/
theorem restAwareOpenOutputFromList :
    instantiateValue?
      { dependencies := [atom], ambient := 1, body := restSchemaBody }
      1 1 [.bvar 1] =
      some (.lambda none
        (.collection .hashBag
          [.apply "Embed" [.bvar 2]] (some "rest"))) := by
  have argumentsTyped : List.Forall₂
      (fun argument dependency =>
        RestAwareTyping.HasType collectionLanguage restContext
          ([proc] ++ [atom]) argument dependency)
      [.bvar 1] [atom] :=
    .cons (RestAwareTyping.checkSchemaHasType_sound
      (by decide +kernel)) .nil
  simpa [restSchemaBody, occurrenceAssignment,
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute,
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift,
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars] using
    RestAwareTyping.instantiateValue?_typedList
      restSchemaBodyTyped argumentsTyped

/-- Ordinary typing can ignore a rest, but the stronger judgment requires its
exact collection declaration. -/
theorem undeclaredRestNotTyped :
    ¬ RestAwareTyping.HasType collectionLanguage FreeTypeContext.empty
      ([atom] ++ [atom])
      (.collection .hashBag
        [.apply "Embed" [.bvar 0]] (some "rest"))
      (.collection .hashBag proc) := by
  intro typed
  obtain ⟨elementType, lookup⟩ := typed.restDeclared
  simp [FreeTypeContext.empty] at lookup

/-- Structural binding admission checks a dependency argument's scope and
declared sort name, but does not establish that the argument has that sort
under the constructor's binder. This presentation isolates that gap. -/
def wrongSortBindingRule : RewriteRule :=
  { name := "WrongSortBinding"
    premises := []
    typeContext := [("X", proc)]
    left := .apply "Wrap" [.lambda none (.fvar "X")]
    right := .apply "Wrap" [.lambda none (.fvar "X")]
    bindings := some {
      dependencies := [("X", [atom])]
      occurrences :=
        [{ name := "X", site := .left, path := [0, 0],
           arguments := [.bvar 0] },
         { name := "X", site := .right, path := [0, 0],
           arguments := [.bvar 0] }] } }

def wrongSortBindingLanguage : LanguageDef :=
  { name := "WrongSortBindingControl"
    types := [TypeDecl.plain "Atom", TypeDecl.plain "Proc"]
    terms :=
      [{ label := "Wrap", category := "Proc",
         params := [.abstractionNamed none "body" proc],
         syntaxPattern := [.terminal "wrap", .nonTerminal "body"] }]
    equations := []
    rewrites := [wrongSortBindingRule] }

theorem wrongSortBindingLanguage_validates :
    wrongSortBindingLanguage.validate = [] := by
  simp [LanguageDef.validate, wrongSortBindingLanguage,
    wrongSortBindingRule, LanguageDef.duplicateErrors,
    LanguageDef.duplicateErrorsAux, LanguageDef.validateTerm,
    LanguageDef.validateRewrite,
    LanguageDef.validateTypeExpr_eq_nil_iff,
    LanguageDef.validatePatternConstructors,
    LanguageDef.validateRulePatterns,
    LanguageDef.typeNames, TypeDecl.plain, TypeExpr.baseNames,
    TermParam.bodyName, TermParam.binderNames, TermParam.typeExpr,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt]

theorem wrongSortBindingPassesStructuralGate :
    bindingDeclarationsValid wrongSortBindingLanguage = true := by
  simp only [bindingDeclarationsValid, wrongSortBindingLanguage_validates,
    List.isEmpty_nil, Bool.true_and]
  decide +kernel

theorem wrongSortBindingSchemaChecks :
    RestAwareTyping.checkRewriteHasType wrongSortBindingLanguage
      wrongSortBindingRule = true := by
  decide +kernel

theorem wrongSortBindingSchemaTyped :
    RestAwareTyping.RewriteHasType wrongSortBindingLanguage
      wrongSortBindingRule :=
  RestAwareTyping.checkRewriteHasType_sound wrongSortBindingSchemaChecks

theorem wrongSortDependencyArgumentUntypable :
    ¬ RestAwareTyping.HasType wrongSortBindingLanguage
      FreeTypeContext.empty [proc] (.bvar 0) atom := by
  intro typed
  cases typed with
  | bvar lookup => simp [atom, proc] at lookup

/-- The actual authored singleton row cannot be converted to typed
occurrence arguments in the Proc binder context. -/
theorem wrongSortOccurrenceRowUntypable :
    ¬ List.Forall₂
      (fun argument dependency =>
        RestAwareTyping.HasType wrongSortBindingLanguage
          FreeTypeContext.empty [proc] argument dependency)
      [.bvar 0] [atom] := by
  intro typed
  cases typed with
  | cons argumentTyped _ =>
      exact wrongSortDependencyArgumentUntypable argumentTyped

end Mettapedia.GSLT.Examples.TypedOccurrenceSubstitution
