import Mettapedia.GSLT.LanguageDef.Cost.FiniteReflection

/-!
# Rest-free active-pair schemas

Chapter 11's single-signature rule seals the selected interacting pair.
An ambient collection remainder belongs to an external authored context.
This operation specializes a root collection schema to an empty remainder;
it does not evaluate explicit substitution nodes or alter payloads.

Sorting is preserved generically. Correspondence with an authored reduction
and contextual coverage must additionally be proved for the selected source
rule. This module does not replace the earlier whole-redex construction.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open WellSorted

/-- Remove only a root collection's optional remainder, preserving its
explicit elements and every binder or substitution within them. -/
def closeRootCollectionRest : Pattern → Pattern
  | .collection kind elements _ => .collection kind elements none
  | pattern => pattern

theorem WellSorted.HasType.closeRootCollectionRest
    {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {term : Pattern} {type : TypeExpr}
    (typed : HasType language free bound term type) :
    HasType language free bound (closeRootCollectionRest term) type := by
  cases typed <;> (first | assumption | constructor <;> assumption)

theorem closeRootCollectionRest_mapPattern (symbols : LanguageDefSymbolMap) (term : Pattern) :
    closeRootCollectionRest (mapPattern symbols term) =
      mapPattern symbols (closeRootCollectionRest term) := by
  cases term <;> rfl

namespace ContinuationDecorationProfile

variable {theory : IGSLT} {cut : InteractionCutPresentation theory}

def costActivePairRedex (_profile : ContinuationDecorationProfile cut) : Pattern :=
  mapPatternSchemaNames costSourceSchemaName
    (mapPattern costBaseLanguageDefSymbolMap
      (closeRootCollectionRest theory.presentation.interactionRewrite.1.left))

def costActivePairContractum (profile : ContinuationDecorationProfile cut) : Pattern :=
  mapPatternSchemaNames costSourceSchemaName
    (profile.mapContractum
      (closeRootCollectionRest theory.presentation.interactionRewrite.1.right))

def costActivePairSource (profile : ContinuationDecorationProfile cut) : Pattern :=
  .apply costContactConstructorName
    [.apply costSignedConstructorName
      [profile.costActivePairRedex, .fvar (costAdministrativeSchemaName "signature")],
      .apply costFundingConstructorName
        [.apply costTokenStackConsConstructorName
          [.fvar (costAdministrativeSchemaName "signature"),
            .fvar (costAdministrativeSchemaName "stack-tail")]]]

def costActivePairTarget (profile : ContinuationDecorationProfile cut) : Pattern :=
  .apply costContactConstructorName
    [profile.costActivePairContractum,
      .apply costFundingConstructorName
        [.fvar (costAdministrativeSchemaName "stack-tail")]]

/-- The same selected rule name and administrative context, with only the
root collection remainder specialized before applying the Cost maps. -/
def costActivePairRewrite (profile : ContinuationDecorationProfile cut) : RewriteRule :=
  { profile.costWholeRedexRewrite with
    left := profile.costActivePairSource
    right := profile.costActivePairTarget }

/-- Retain the source dependency context, retyped by the same selected-variable
policy as the finite generator. Source remainder variables absent from the
generated rule context are omitted. This is data transport; admission of the
result still checks every actual occurrence address and dependency spine. -/
def costActivePairBindingSpec (profile : ContinuationDecorationProfile cut)
    (source : RuleBindingSpec) : RuleBindingSpec where
  dependencies :=
    ((source.dependencies.filter fun entry =>
      theory.presentation.interactionRewrite.1.typeContext.any
        (fun declared => declared.1 == entry.1)).map fun entry =>
      (costSourceSchemaName entry.1,
        entry.2.map (if profile.selectedVariable entry.1 then
          costWrappedTypeExpr theory.presentation.interactingSort.1.name
        else costBaseTypeExpr))) ++
      [(costAdministrativeSchemaName "signature", []),
       (costAdministrativeSchemaName "stack-tail", [])]
  occurrences := (source.occurrences.filter fun row =>
    theory.presentation.interactionRewrite.1.typeContext.any
      (fun declared => declared.1 == row.name)).map fun row =>
    { name := costSourceSchemaName row.name
      site := row.site
      path := (match row.site with
        | .left => [0, 0]
        | .right => [0]
        | .premise _ _ _ => []) ++ row.path
      arguments := row.arguments.map fun argument =>
        mapPatternSchemaNames costSourceSchemaName
          (mapPattern (match row.site with
            | .right => profile.contractumSymbols
            | _ => costBaseLanguageDefSymbolMap) argument) }

theorem costActivePairRedex_hasType (profile : ContinuationDecorationProfile cut)
    (redexTyped : profile.RedexRetypable) :
    HasSort profile.costCoreLanguage profile.costWholeRedexFreeContext []
      profile.costActivePairRedex (costBaseSortName theory.presentation.interactingSort.1.name) := by
  have closed := redexTyped.closeRootCollectionRest
  rw [closeRootCollectionRest_mapPattern] at closed
  exact (profile.hasType_costCoreLanguage closed).mapSchemaNames
    costSourceSchemaName profile.costWholeRedexFreeContext_source

theorem costActivePairContractum_hasType (profile : ContinuationDecorationProfile cut)
    (contractumTyped : profile.Wrappable) :
    HasSort profile.costCoreLanguage profile.costWholeRedexFreeContext []
      profile.costActivePairContractum costWrappedSortName := by
  have closed := contractumTyped.closeRootCollectionRest
  change HasSort profile.generatedLanguage profile.generatedFreeContext []
    (closeRootCollectionRest (mapPattern profile.contractumSymbols
      theory.presentation.interactionRewrite.1.right)) costWrappedSortName at closed
  rw [closeRootCollectionRest_mapPattern] at closed
  exact (profile.hasType_costCoreLanguage closed).mapSchemaNames
    costSourceSchemaName profile.costWholeRedexFreeContext_source

#print axioms costActivePairRedex_hasType
#print axioms costActivePairContractum_hasType

end ContinuationDecorationProfile
end Mettapedia.GSLT.LanguageDef
