import Mettapedia.GSLT.LanguageDef.TypedOccurrenceCoverage
import Mettapedia.GSLT.LanguageDef.TypedSideOccurrenceAdmission
import Mettapedia.GSLT.LanguageDef.TypedRowArgumentAdmission
import Mettapedia.GSLT.Examples.TypedRestOccurrenceAddress
import Mettapedia.GSLT.Examples.TypedOccurrenceAddress

/-!
# Executable occurrence coverage for authored rules

The generic classifier is applied to both address forms in the authored rho
communication rule and to a collection rest under a binder. In particular,
the executable rest slot cannot be mistaken for an ordinary term hole.
-/

namespace Mettapedia.GSLT.Examples.TypedOccurrenceCoverage

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.RestAwareTyping
open Mettapedia.GSLT.Examples.ScopedRhoBinding
open Mettapedia.GSLT.Examples.TypedRestOccurrenceAddress
open Mettapedia.GSLT.Examples.TypedOccurrenceSubstitution
open Mettapedia.GSLT.Examples.RestAwareMorphism
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.OccurrenceZipperAddress
open Mettapedia.OSLF.MeTTaIL.RestOccurrenceAddress

set_option autoImplicit false

theorem rhoLeftTermClassified :
    ∃ rootType binderPrefix,
      TypedOccurrenceAt rhoCalcWithScopedSchemas
        (WellSorted.FreeTypeContext.ofList scopedCommRewrite.typeContext)
        [] scopedCommRewrite.left rootType binderPrefix [0, 1, 0] "p" := by
  have membership : scopedCommRewrite ∈ rhoCalcWithScopedSchemas.rewrites := by
    simp [rhoCalcWithScopedSchemas]
  obtain ⟨rootType, leftTyped, _⟩ :=
    checkRewriteHasType_sound
      (scoped_rho_all_rewrites_check scopedCommRewrite membership)
  have observed : occurrenceAt? scopedCommRewrite.left [0, 1, 0] =
      some "p" := by decide +kernel
  obtain ⟨binderPrefix, classified⟩ :=
    leftTyped.occurrenceAt_typed observed
  exact ⟨rootType, binderPrefix, classified⟩

private def rhoLeftStoredRow : MetavariableOccurrence :=
  { «name» := "p", site := .left, path := [0, 1, 0],
    arguments := [.bvar 0] }

/-- A stored row in the canonical rho binding declaration inherits the
typed address from structural admission and rewrite-side typing. -/
theorem rhoLeftStoredRowTyped :
    ∃ pattern rootType binderPrefix,
      sitePattern? scopedCommRewrite rhoLeftStoredRow.site = some pattern ∧
      TypedOccurrenceAt rhoCalcWithScopedSchemas
        (WellSorted.FreeTypeContext.ofList scopedCommRewrite.typeContext)
        [] pattern rootType binderPrefix
        rhoLeftStoredRow.path rhoLeftStoredRow.name := by
  have membership : scopedCommRewrite ∈ rhoCalcWithScopedSchemas.rewrites := by
    simp [rhoCalcWithScopedSchemas]
  have typed : RewriteHasType rhoCalcWithScopedSchemas
      scopedCommRewrite :=
    checkRewriteHasType_sound
      (scoped_rho_all_rewrites_check scopedCommRewrite membership)
  have admitted : admittedFor scopedCommRewrite scopedCommBindingSpec = true := by
    decide +kernel
  have rowMember : rhoLeftStoredRow ∈
      scopedCommBindingSpec.occurrences := by decide +kernel
  exact typed.typedSideRow admitted rowMember
    (Or.inl (by decide +kernel))

/-- The row's declared Name dependency checks under the Name binder of the
authored input continuation. Identifying this exact list with the prefix
extracted from the whole rho side is a separate theorem. -/
theorem rhoLeftStoredArgumentsCheck :
    checkStoredRowArguments rhoCalcWithScopedSchemas
      (WellSorted.FreeTypeContext.ofList scopedCommRewrite.typeContext)
      [.base "Name"] [] scopedCommBindingSpec rhoLeftStoredRow = true := by
  decide +kernel

theorem rhoLeftRestClassified :
    ∃ rootType binderPrefix,
      TypedOccurrenceAt rhoCalcWithScopedSchemas
        (WellSorted.FreeTypeContext.ofList scopedCommRewrite.typeContext)
        [] scopedCommRewrite.left rootType binderPrefix [2] "rest" := by
  have membership : scopedCommRewrite ∈ rhoCalcWithScopedSchemas.rewrites := by
    simp [rhoCalcWithScopedSchemas]
  obtain ⟨rootType, leftTyped, _⟩ :=
    checkRewriteHasType_sound
      (scoped_rho_all_rewrites_check scopedCommRewrite membership)
  have observed : occurrenceAt? scopedCommRewrite.left [2] =
      some "rest" := by decide +kernel
  obtain ⟨binderPrefix, classified⟩ :=
    leftTyped.occurrenceAt_typed observed
  exact ⟨rootType, binderPrefix, classified⟩

theorem rhoRightRestClassified :
    ∃ rootType binderPrefix,
      TypedOccurrenceAt rhoCalcWithScopedSchemas
        (WellSorted.FreeTypeContext.ofList scopedCommRewrite.typeContext)
        [] scopedCommRewrite.right rootType binderPrefix [1] "rest" := by
  have membership : scopedCommRewrite ∈ rhoCalcWithScopedSchemas.rewrites := by
    simp [rhoCalcWithScopedSchemas]
  obtain ⟨rootType, _, rightTyped⟩ :=
    checkRewriteHasType_sound
      (scoped_rho_all_rewrites_check scopedCommRewrite membership)
  have observed : occurrenceAt? scopedCommRewrite.right [1] =
      some "rest" := by decide +kernel
  obtain ⟨binderPrefix, classified⟩ :=
    rightTyped.occurrenceAt_typed observed
  exact ⟨rootType, binderPrefix, classified⟩

theorem nestedRestClassified :
    ∃ binderPrefix, TypedOccurrenceAt
      Mettapedia.GSLT.Examples.RestAwareMorphism.collectionLanguage
      (WellSorted.FreeTypeContext.ofList
        [("rest", .collection .hashBag (.base "Proc"))])
      [.base "Atom"] nestedRestSchema
      (.arrow (.base "Proc") (.collection .hashBag (.base "Proc")))
      binderPrefix [0, 1] "rest" := by
  have observed : occurrenceAt? nestedRestSchema [0, 1] =
      some "rest" := by decide +kernel
  exact nestedRestSchemaTyped.occurrenceAt_typed observed

theorem rhoRestCannotBeTermHole :
    termZipperAt? scopedCommRewrite.left [2] = none := by
  decide +kernel

private abbrev atom : TypeExpr := .base "Atom"
private abbrev proc : TypeExpr := .base "Proc"

private def restFree : WellSorted.FreeTypeContext :=
  WellSorted.FreeTypeContext.ofList
    [("rest", .collection .hashBag proc)]

private def nestedSite : RestSite :=
  ⟨"rest", .hashBag, [.apply "Embed" [.bvar 1]],
    .lambda none .hole⟩

theorem nestedRestPreciselyClassified :
    TypedOccurrenceAt collectionLanguage restFree [atom]
      nestedRestSchema (.arrow proc (.collection .hashBag proc))
      [proc] [0, 1] "rest" := by
  refine .rest nestedSite [proc, atom] (.collection .hashBag proc) proc
    (by decide +kernel) rfl ?_ (by decide +kernel) rfl rfl
    (by decide +kernel)
  exact checkSchemaHasType_sound (by decide +kernel)

/-- The rest address is under a Proc binder, while the supplied open Atom
depends on the ambient binder. The selected runtime depth is one and the
returned variable remains at index one. -/
theorem nestedRestOpenInstance :
    ∃ instantiated,
      occurrenceDepthAt? nestedRestSchema [0, 1] 0 = some 1 ∧
      instantiateValue?
        { dependencies := [atom], ambient := 1, body := .bvar 0 }
        1 1 [.bvar 1] = some instantiated ∧
      HasType collectionLanguage restFree [proc, atom]
        instantiated atom := by
  have bodyTyped : HasType collectionLanguage restFree
      ([atom] ++ [atom]) (.bvar 0) atom :=
    checkSchemaHasType_sound (by decide +kernel)
  have argumentsChecked : checkOccurrenceArguments
      collectionLanguage restFree [proc] [atom]
      [.bvar 1] [atom] = true := by decide +kernel
  simpa using nestedRestPreciselyClassified.instantiateChecked
    bodyTyped argumentsChecked

theorem nestedRestOpenInstance_exact :
    instantiateValue?
      { dependencies := [atom], ambient := 1, body := .bvar 0 }
      1 1 [.bvar 1] = some (.bvar 1) ∧
    HasType collectionLanguage restFree [proc, atom] (.bvar 1) atom := by
  obtain ⟨instantiated, _, executed, typed⟩ := nestedRestOpenInstance
  have computed : instantiateValue?
      { dependencies := [atom], ambient := 1, body := .bvar 0 }
      1 1 [.bvar 1] = some (.bvar 1) := by decide +kernel
  have resultEq : instantiated = .bvar 1 :=
    Option.some.inj (executed.symm.trans computed)
  exact ⟨computed, resultEq ▸ typed⟩

theorem wrongAddressNotClassified
    {rootType : TypeExpr} {binderPrefix : List TypeExpr} :
    ¬ TypedOccurrenceAt rhoCalcWithScopedSchemas
      (WellSorted.FreeTypeContext.ofList scopedCommRewrite.typeContext)
      [] scopedCommRewrite.left rootType binderPrefix [2] "p" := by
  intro classified
  have observed := classified.executable
  have actual : occurrenceAt? scopedCommRewrite.left [2] =
      some "rest" := by decide +kernel
  rw [actual] at observed
  have wrong : ("rest" : String) = "p" := Option.some.inj observed
  exact (by decide : ("rest" : String) ≠ "p") wrong

private def wrongSortStoredSpec : RuleBindingSpec :=
  wrongSortBindingRule.bindings.getD { dependencies := [] }

private def wrongSortStoredRow : MetavariableOccurrence :=
  { «name» := "X", site := .left, path := [0, 0],
    arguments := [.bvar 0] }

theorem wrongSortRowIsStructurallyAdmitted :
    wrongSortBindingRule.bindings = some wrongSortStoredSpec ∧
    wrongSortStoredRow ∈ wrongSortStoredSpec.occurrences ∧
    admittedFor wrongSortBindingRule wrongSortStoredSpec = true := by
  decide +kernel

/-- The existing structural gate accepts this exact stored row, but sorted
checking rejects its Proc argument at the declared Atom dependency sort. -/
theorem wrongSortStoredArgumentsRejected :
    checkStoredRowArguments wrongSortBindingLanguage
      (WellSorted.FreeTypeContext.ofList
        wrongSortBindingRule.typeContext)
      [.base "Proc"] [] wrongSortStoredSpec wrongSortStoredRow = false := by
  decide +kernel

theorem wrongSortRawExecutionDoesNotCertifyTyping :
    admittedFor wrongSortBindingRule wrongSortStoredSpec = true ∧
    checkStoredRowArguments wrongSortBindingLanguage
      (WellSorted.FreeTypeContext.ofList
        wrongSortBindingRule.typeContext)
      [.base "Proc"] [] wrongSortStoredSpec wrongSortStoredRow = false ∧
    instantiateValue?
      { dependencies := [.base "Atom"], ambient := 0, body := .bvar 0 }
      0 1 wrongSortStoredRow.arguments = some (.bvar 0) := by
  exact ⟨wrongSortRowIsStructurallyAdmitted.2.2,
    wrongSortStoredArgumentsRejected, by decide +kernel⟩

end Mettapedia.GSLT.Examples.TypedOccurrenceCoverage
