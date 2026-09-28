import Mettapedia.GSLT.LanguageDef.TypedRowArgumentAdmission
import Mettapedia.GSLT.Examples.ScopedRhoBinding

/-!
# Exact binder sort of the authored rho input row

The input continuation's local binder is `Name` because of the actual
`PInput` parameter declaration. An explicit typed zipper follows that
declaration through `PInput` and the outer parallel collection. The stored
row's `Name` argument then passes sorted checking and supplies an executable
typed occurrence substitution.
-/

namespace Mettapedia.GSLT.Examples.TypedRhoRowExecution

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.RestAwareTyping
open Mettapedia.GSLT.Examples.ScopedRhoBinding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.OccurrenceZipperAddress
open Mettapedia.OSLF.MeTTaIL.RuleBinding

set_option autoImplicit false

private abbrev nameSort : TypeExpr := .base "Name"
private abbrev procSort : TypeExpr := .base "Proc"
private def free : FreeTypeContext :=
  FreeTypeContext.ofList scopedCommRewrite.typeContext

private def pInputRule : GrammarRule :=
  (rhoCalcWithScopedSchemas.terms.find? (fun rule => rule.label == "PInput")).get
    (by decide +kernel)

private def pParRule : GrammarRule :=
  (rhoCalcWithScopedSchemas.terms.find? (fun rule => rule.label == "PPar")).get
    (by decide +kernel)

private def inputContext : OneHoleContext :=
  .apply "PInput" [.fvar "n"] (.lambda none .hole) []

private def outerContext : OneHoleContext :=
  .collection .hashBag [] inputContext
    [.apply "POutput" [.fvar "n", .fvar "q"]] (some "rest")

private theorem pInputMember : pInputRule ∈ rhoCalcWithScopedSchemas.terms := by
  decide +kernel

private theorem pParMember : pParRule ∈ rhoCalcWithScopedSchemas.terms := by
  decide +kernel

private theorem pInputNotBare : ¬ UsesBareCollection pInputRule := by
  intro h
  rcases h with ⟨_, _, _, shape⟩
  have actual : pInputRule.params.length = 2 := by decide +kernel
  rw [shape] at actual
  cases actual

private theorem inputArgumentsTyped :
    WellSorted.ArgumentsHaveTypes rhoCalcWithScopedSchemas free []
      [.fvar "n", .lambda none (.fvar "p")] pInputRule.params := by
  apply Mettapedia.GSLT.LanguageDef.RestAwareTyping.ArgumentsHaveTypes.forget
  apply checkSchemaArguments_sound_of
    (fun argument _ expected checked => checkSchemaHasType_sound checked)
  decide +kernel

private theorem elementsTyped :
    WellSorted.ElementsHaveType rhoCalcWithScopedSchemas free []
      [.apply "PInput" [.fvar "n", .lambda none (.fvar "p")],
       .apply "POutput" [.fvar "n", .fvar "q"]] procSort := by
  apply Mettapedia.GSLT.LanguageDef.RestAwareTyping.ElementsHaveType.forget
  apply checkSchemaElements_sound_of
    (fun argument _ checked => checkSchemaHasType_sound checked)
  decide +kernel

private theorem focusTyped :
    WellSorted.HasType rhoCalcWithScopedSchemas free [nameSort]
      (.fvar "p") procSort :=
  .fvar (by decide +kernel)

private theorem inputSelected :
    TypedAt rhoCalcWithScopedSchemas free (.fvar "p") inputContext
      [] procSort [nameSort] procSort := by
  apply TypedAt.application (rule := pInputRule)
    (expected := .arrow nameSort procSort)
    (beforeParams := [.simple "n" nameSort])
    (parameter := .abstractionNamed none "p" (.arrow nameSort procSort))
    (afterParams := [])
  · exact pInputMember
  · exact pInputNotBare
  · exact inputArgumentsTyped
  · decide +kernel
  · rfl
  · decide +kernel
  · exact TypedAt.lambda (TypedAt.here focusTyped)

private theorem fullSelected :
    TypedAt rhoCalcWithScopedSchemas free (.fvar "p") outerContext
      [] procSort [nameSort] procSort := by
  apply TypedAt.collectionConstructor (rule := pParRule)
    (element := procSort) (parameter := "ps")
  · exact pParMember
  · decide +kernel
  · exact elementsTyped
  · exact inputSelected

/-- The actual authored row address has precisely the `Name` binder sort,
not merely one unspecified binder. -/
theorem rhoLeftExactBinder :
    TypedOccurrenceAt rhoCalcWithScopedSchemas free []
      scopedCommRewrite.left procSort [nameSort] [0, 1, 0] "p" := by
  apply TypedOccurrenceAt.term outerContext [nameSort] procSort
  · decide +kernel
  · exact fullSelected
  · decide +kernel
  · rfl
  · decide +kernel
  · decide +kernel

private def storedRow : MetavariableOccurrence :=
  { «name» := "p", site := .left, path := [0, 1, 0],
    arguments := [.bvar 0] }

private def capturedValue : ContextualValue :=
  { dependencies := [nameSort], ambient := 0,
    body := .apply "PDrop" [.bvar 0] }

theorem capturedValueTyped :
    ContextualValueHasType rhoCalcWithScopedSchemas free
      [nameSort] [] procSort capturedValue := by
  refine ⟨rfl, rfl, ?_⟩
  exact checkSchemaHasType_sound (by decide +kernel)

theorem storedRowIsAuthored :
    storedRow ∈ scopedCommBindingSpec.occurrences ∧
    dependencies? scopedCommBindingSpec storedRow.name =
      some [nameSort] ∧
    admittedFor scopedCommRewrite scopedCommBindingSpec = true := by
  decide +kernel

theorem storedRowArgumentsCheck :
    checkStoredRowArguments rhoCalcWithScopedSchemas free
      [nameSort] [] scopedCommBindingSpec storedRow = true := by
  decide +kernel

/-- The exact declared row and binder sort transport a captured process
that depends on its received name through executable substitution. -/
theorem storedRowOpenValueTyped :
    ∃ result,
      occurrenceDepthAt? scopedCommRewrite.left storedRow.path 0 = some 1 ∧
      instantiateValue? capturedValue 0 1 storedRow.arguments =
        some result ∧
      RestAwareTyping.HasType rhoCalcWithScopedSchemas free
        [nameSort] result procSort := by
  obtain ⟨member, declared, admitted⟩ := storedRowIsAuthored
  obtain ⟨result, siteDepth, executed, resultTyped⟩ :=
    rhoLeftExactBinder.instantiateAdmittedCapturedValue
      (rule := scopedCommRewrite) (spec := scopedCommBindingSpec)
      (by decide +kernel) admitted member declared
      storedRowArgumentsCheck capturedValueTyped
  refine ⟨result, ?_, executed, resultTyped⟩
  simpa [sitePattern?, storedRow] using siteDepth

theorem storedRowOpenValueExact :
    instantiateValue? capturedValue 0 1 storedRow.arguments =
        some (.apply "PDrop" [.bvar 0]) ∧
    RestAwareTyping.HasType rhoCalcWithScopedSchemas free
      [nameSort] (.apply "PDrop" [.bvar 0]) procSort := by
  obtain ⟨result, _, executed, typed⟩ := storedRowOpenValueTyped
  have computed : instantiateValue? capturedValue
      0 1 storedRow.arguments =
        some (.apply "PDrop" [.bvar 0]) := by decide +kernel
  have resultEq : result = .apply "PDrop" [.bvar 0] :=
    Option.some.inj (executed.symm.trans computed)
  exact ⟨computed, resultEq ▸ typed⟩

private def rightContext : OneHoleContext :=
  .collection .hashBag []
    (.substBody .hole (.apply "NQuote" [.fvar "q"]))
    [] (some "rest")

private theorem rightElementsTyped :
    WellSorted.ElementsHaveType rhoCalcWithScopedSchemas free []
      [.subst (.fvar "p") (.apply "NQuote" [.fvar "q"])] procSort := by
  apply Mettapedia.GSLT.LanguageDef.RestAwareTyping.ElementsHaveType.forget
  apply checkSchemaElements_sound_of
    (fun argument _ checked => checkSchemaHasType_sound checked)
  decide +kernel

private theorem replacementTyped :
    WellSorted.HasType rhoCalcWithScopedSchemas free []
      (.apply "NQuote" [.fvar "q"]) nameSort :=
  (checkSchemaHasType_sound (by decide +kernel)).forget

private theorem rightSelected :
    TypedAt rhoCalcWithScopedSchemas free (.fvar "p") rightContext
      [] procSort [nameSort] procSort := by
  apply TypedAt.collectionConstructor (rule := pParRule)
    (element := procSort) (parameter := "ps")
  · exact pParMember
  · decide +kernel
  · exact rightElementsTyped
  · exact TypedAt.substBody replacementTyped
      (TypedAt.here focusTyped)

/-- The second stored occurrence of `p` crosses an explicit-substitution
body, whose replacement has the declared `Name` sort. -/
theorem rhoRightExactBinder :
    TypedOccurrenceAt rhoCalcWithScopedSchemas free []
      scopedCommRewrite.right procSort [nameSort] [0, 0] "p" := by
  apply TypedOccurrenceAt.term rightContext [nameSort] procSort
  · decide +kernel
  · exact rightSelected
  · decide +kernel
  · rfl
  · decide +kernel
  · decide +kernel

private def rightStoredRow : MetavariableOccurrence :=
  { «name» := "p", site := .right, path := [0, 0],
    arguments := [.bvar 0] }

theorem rightStoredRowIsAuthored :
    rightStoredRow ∈ scopedCommBindingSpec.occurrences ∧
    dependencies? scopedCommBindingSpec rightStoredRow.name =
      some [nameSort] ∧
    admittedFor scopedCommRewrite scopedCommBindingSpec = true := by
  decide +kernel

theorem rightStoredRowArgumentsCheck :
    checkStoredRowArguments rhoCalcWithScopedSchemas free
      [nameSort] [] scopedCommBindingSpec rightStoredRow = true := by
  decide +kernel

theorem rightStoredRowOpenValueTyped :
    ∃ result,
      occurrenceDepthAt? scopedCommRewrite.right
        rightStoredRow.path 0 = some 1 ∧
      instantiateValue? capturedValue 0 1 rightStoredRow.arguments =
        some result ∧
      RestAwareTyping.HasType rhoCalcWithScopedSchemas free
        [nameSort] result procSort := by
  obtain ⟨member, declared, admitted⟩ := rightStoredRowIsAuthored
  obtain ⟨result, siteDepth, executed, resultTyped⟩ :=
    rhoRightExactBinder.instantiateAdmittedCapturedValue
      (rule := scopedCommRewrite) (spec := scopedCommBindingSpec)
      (by decide +kernel) admitted member declared
      rightStoredRowArgumentsCheck capturedValueTyped
  refine ⟨result, ?_, executed, resultTyped⟩
  simpa [sitePattern?, rightStoredRow] using siteDepth

theorem rightStoredRowOpenValueExact :
    instantiateValue? capturedValue 0 1 rightStoredRow.arguments =
        some (.apply "PDrop" [.bvar 0]) ∧
    RestAwareTyping.HasType rhoCalcWithScopedSchemas free
      [nameSort] (.apply "PDrop" [.bvar 0]) procSort := by
  obtain ⟨result, _, executed, typed⟩ := rightStoredRowOpenValueTyped
  have computed : instantiateValue? capturedValue
      0 1 rightStoredRow.arguments =
        some (.apply "PDrop" [.bvar 0]) := by decide +kernel
  have resultEq : result = .apply "PDrop" [.bvar 0] :=
    Option.some.inj (executed.symm.trans computed)
  exact ⟨computed, resultEq ▸ typed⟩

/-- Both authored occurrences supply the same dependency context and
instantiate the same captured process; one path crosses a lambda and the
other an explicit substitution. This is a checked occurrence-level
comparison, with general matcher recovery still a separate obligation. -/
theorem storedRepeatedValueExact :
    instantiateValue? capturedValue 0 1 storedRow.arguments =
        some (.apply "PDrop" [.bvar 0]) ∧
    instantiateValue? capturedValue 0 1 rightStoredRow.arguments =
        some (.apply "PDrop" [.bvar 0]) := by
  exact ⟨storedRowOpenValueExact.1, rightStoredRowOpenValueExact.1⟩

end Mettapedia.GSLT.Examples.TypedRhoRowExecution
