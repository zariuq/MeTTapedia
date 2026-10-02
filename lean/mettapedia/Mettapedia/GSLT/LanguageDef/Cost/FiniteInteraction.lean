import Mettapedia.GSLT.LanguageDef.Cost.FiniteCore
import Mettapedia.GSLT.LanguageDef.CostInteractionClosure

/-!
# Funded interaction with finite continuation bundles

The whole-redex rule retains the selected authored cut and decorates every
continuation selected by its finite profile. Its administrative variables are
disjoint from the source variables. The schema consumes one matching stack
head and returns the actual decorated contractum with the remaining stack.

Sorting of the rule is independent of canonical sections and iteration. The
cut's premise-free condition is inherited from `InteractionCutPresentation`;
this construction does not remove executable premises from arbitrary rules.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open WellSorted ContinuationRetypingPlan

set_option autoImplicit false

namespace CostApparatus

variable {language : LanguageDef} {free : FreeTypeContext}
  {bound : List TypeExpr}

/-- Signing is an ordinary typed constructor, in any signature containing
the declared Cost signing row. -/
theorem signed_hasType {sort : String} {body key : Pattern}
    (declared : costSignedConstructor sort ∈ language.terms)
    (bodyTyped : HasSort language free bound body (costBaseSortName sort))
    (keyTyped : HasSort language free bound key costSignatureSortName) :
    HasSort language free bound
      (.apply costSignedConstructorName [body, key]) costWrappedSortName := by
  apply HasType.constructor declared
  · simp [UsesBareCollection, costSignedConstructor]
  · exact .cons (by trivial) rfl bodyTyped
      (.cons (by trivial) rfl keyTyped .nil)

theorem stackCons_hasType {key tail : Pattern}
    (declared : costTokenStackConsConstructor ∈ language.terms)
    (keyTyped : HasSort language free bound key costSignatureSortName)
    (tailTyped : HasSort language free bound tail costTokenStackSortName) :
    HasSort language free bound
      (.apply costTokenStackConsConstructorName [key, tail]) costTokenStackSortName := by
  apply HasType.constructor declared
  · simp [UsesBareCollection, costTokenStackConsConstructor]
  · exact .cons (by trivial) rfl keyTyped
      (.cons (by trivial) rfl tailTyped .nil)

theorem funding_hasType {stack : Pattern}
    (declared : costFundingConstructor ∈ language.terms)
    (stackTyped : HasSort language free bound stack costTokenStackSortName) :
    HasSort language free bound
      (.apply costFundingConstructorName [stack]) costWrappedSortName := by
  apply HasType.constructor declared
  · simp [UsesBareCollection, costFundingConstructor]
  · exact .cons (by trivial) rfl stackTyped .nil

theorem contact_hasType {left right : Pattern}
    (declared : costContactConstructor ∈ language.terms)
    (leftTyped : HasSort language free bound left costWrappedSortName)
    (rightTyped : HasSort language free bound right costWrappedSortName) :
    HasSort language free bound
      (.apply costContactConstructorName [left, right]) costWrappedSortName := by
  apply HasType.constructor declared
  · simp [UsesBareCollection, costContactConstructor]
  · exact .cons (by trivial) rfl leftTyped
      (.cons (by trivial) rfl rightTyped .nil)

end CostApparatus

namespace ContinuationDecorationProfile

variable {theory : IGSLT} {cut : InteractionCutPresentation theory}

/-- Source-variable types follow all selected continuation positions. -/
def costRetypedSourceContext (profile : ContinuationDecorationProfile cut) :
    List (String × TypeExpr) :=
  theory.presentation.interactionRewrite.1.typeContext.map fun entry =>
    (costSourceSchemaName entry.1,
      if profile.selectedVariable entry.1 then
        costWrappedTypeExpr theory.presentation.interactingSort.1.name entry.2
      else costBaseTypeExpr entry.2)

/-- The two fresh administrative variables carry the consumed signature and
the remainder of the stack. -/
def costWholeRedexTypeContext (profile : ContinuationDecorationProfile cut) :
    List (String × TypeExpr) :=
  profile.costRetypedSourceContext ++
    [(costAdministrativeSchemaName "signature", .base costSignatureSortName),
      (costAdministrativeSchemaName "stack-tail", .base costTokenStackSortName)]

def costWholeRedexFreeContext (profile : ContinuationDecorationProfile cut) :
    FreeTypeContext := lookupTypeContext profile.costWholeRedexTypeContext

def costMappedRedex (_profile : ContinuationDecorationProfile cut) : Pattern :=
  mapPatternSchemaNames costSourceSchemaName
    (mapPattern costBaseLanguageDefSymbolMap theory.presentation.interactionRewrite.1.left)

def costMappedContractum (profile : ContinuationDecorationProfile cut) : Pattern :=
  mapPatternSchemaNames costSourceSchemaName
    (profile.mapContractum theory.presentation.interactionRewrite.1.right)

/-- Located whole-redex funding: the signing key equals the adjacent stack head. -/
def costWholeRedexSource (profile : ContinuationDecorationProfile cut) : Pattern :=
  .apply costContactConstructorName
    [.apply costSignedConstructorName
      [profile.costMappedRedex, .fvar (costAdministrativeSchemaName "signature")],
      .apply costFundingConstructorName
        [.apply costTokenStackConsConstructorName
          [.fvar (costAdministrativeSchemaName "signature"),
            .fvar (costAdministrativeSchemaName "stack-tail")]]]

/-- Exactly the authored contractum and unconsumed tail survive the firing. -/
def costWholeRedexTarget (profile : ContinuationDecorationProfile cut) : Pattern :=
  .apply costContactConstructorName
    [profile.costMappedContractum,
      .apply costFundingConstructorName
        [.fvar (costAdministrativeSchemaName "stack-tail")]]

def costWholeRedexRewrite (profile : ContinuationDecorationProfile cut) : RewriteRule where
  name := costWholeRedexRewriteName
  typeContext := profile.costWholeRedexTypeContext
  premises := []
  left := profile.costWholeRedexSource
  right := profile.costWholeRedexTarget

/-- The operational fragment generated by this selected cut. Other authored
rules and static equations require their own coverage and transport laws. -/
def costWholeRedexLanguage (profile : ContinuationDecorationProfile cut) : LanguageDef :=
  { profile.costCoreLanguage with rewrites := [profile.costWholeRedexRewrite] }

/-- No premise is erased: cuts in this domain already have premise-free contraction. -/
theorem costWholeRedexRewrite_premises (profile : ContinuationDecorationProfile cut) :
    profile.costWholeRedexRewrite.premises =
      theory.presentation.interactionRewrite.1.premises :=
  cut.interactionPremisesEmpty.symm

theorem lookup_costRetypedSourceContext (profile : ContinuationDecorationProfile cut)
    (name : String) :
    lookupTypeContext profile.costRetypedSourceContext (costSourceSchemaName name) =
      profile.generatedFreeContext name := by
  rw [generatedFreeContext_apply]
  unfold costRetypedSourceContext
  exact lookupTypeContext_map_injective _ _
    (fun name type => if profile.selectedVariable name then
      costWrappedTypeExpr theory.presentation.interactingSort.1.name type
      else costBaseTypeExpr type) costSourceSchemaName_injective name

theorem costWholeRedexFreeContext_source (profile : ContinuationDecorationProfile cut)
    (name : String) (type : TypeExpr)
    (lookup : profile.generatedFreeContext name = some type) :
    profile.costWholeRedexFreeContext (costSourceSchemaName name) = some type := by
  rw [costWholeRedexFreeContext, costWholeRedexTypeContext,
    lookupTypeContext_append, lookup_costRetypedSourceContext, lookup]

theorem lookup_costRetypedSourceContext_administrative
    (profile : ContinuationDecorationProfile cut) (name : String) :
    lookupTypeContext profile.costRetypedSourceContext
      (costAdministrativeSchemaName name) = none :=
  lookupTypeContext_map_outside _ _
    (fun name type => if profile.selectedVariable name then
      costWrappedTypeExpr theory.presentation.interactingSort.1.name type
      else costBaseTypeExpr type) _
    (fun source => costSourceSchemaName_ne_administrative source name)

@[simp]
theorem costWholeRedexFreeContext_signature (profile : ContinuationDecorationProfile cut) :
    profile.costWholeRedexFreeContext (costAdministrativeSchemaName "signature") =
      some (.base costSignatureSortName) := by
  rw [costWholeRedexFreeContext, costWholeRedexTypeContext,
    lookupTypeContext_append, lookup_costRetypedSourceContext_administrative]
  simp [lookupTypeContext]

@[simp]
theorem costWholeRedexFreeContext_stackTail (profile : ContinuationDecorationProfile cut) :
    profile.costWholeRedexFreeContext (costAdministrativeSchemaName "stack-tail") =
      some (.base costTokenStackSortName) := by
  rw [costWholeRedexFreeContext, costWholeRedexTypeContext,
    lookupTypeContext_append, lookup_costRetypedSourceContext_administrative]
  have different : costAdministrativeSchemaName "signature" ≠
      costAdministrativeSchemaName "stack-tail" := by
    intro equality
    have := costAdministrativeSchemaName_injective equality
    contradiction
  simp [lookupTypeContext, different]

/-- Transport the retyped source derivation once across signature extension
and the reserved schema namespace. -/
theorem costMappedRedex_hasType (profile : ContinuationDecorationProfile cut)
    (redexTyped : profile.RedexRetypable) :
    HasSort profile.costCoreLanguage profile.costWholeRedexFreeContext []
      profile.costMappedRedex (costBaseSortName theory.presentation.interactingSort.1.name) :=
  (profile.hasType_costCoreLanguage redexTyped).mapSchemaNames
    costSourceSchemaName profile.costWholeRedexFreeContext_source

theorem costMappedContractum_hasType (profile : ContinuationDecorationProfile cut)
    (contractumTyped : profile.Wrappable) :
    HasSort profile.costCoreLanguage profile.costWholeRedexFreeContext []
      profile.costMappedContractum costWrappedSortName :=
  (profile.hasType_costCoreLanguage contractumTyped).mapSchemaNames
    costSourceSchemaName profile.costWholeRedexFreeContext_source

theorem apparatus_mem_costCore (profile : ContinuationDecorationProfile cut)
    (term : GrammarRule)
    (member : term ∈ costCoreConstructors theory.presentation.interactingSort.1.name) :
    term ∈ profile.costCoreLanguage.terms := List.mem_append_right _ member

theorem costWholeRedexSource_hasType (profile : ContinuationDecorationProfile cut)
    (redexTyped : profile.RedexRetypable) :
    HasSort profile.costCoreLanguage profile.costWholeRedexFreeContext []
      profile.costWholeRedexSource costWrappedSortName := by
  have declared := profile.apparatus_mem_costCore
  have keyTyped : HasSort profile.costCoreLanguage profile.costWholeRedexFreeContext []
      (.fvar (costAdministrativeSchemaName "signature")) costSignatureSortName :=
    .fvar profile.costWholeRedexFreeContext_signature
  have tailTyped : HasSort profile.costCoreLanguage profile.costWholeRedexFreeContext []
      (.fvar (costAdministrativeSchemaName "stack-tail")) costTokenStackSortName :=
    .fvar profile.costWholeRedexFreeContext_stackTail
  exact CostApparatus.contact_hasType (declared _ (by simp [costCoreConstructors]))
    (CostApparatus.signed_hasType (declared _ (by simp [costCoreConstructors]))
      (profile.costMappedRedex_hasType redexTyped) keyTyped)
    (CostApparatus.funding_hasType (declared _ (by simp [costCoreConstructors]))
      (CostApparatus.stackCons_hasType (declared _ (by simp [costCoreConstructors]))
        keyTyped tailTyped))

theorem costWholeRedexTarget_hasType (profile : ContinuationDecorationProfile cut)
    (contractumTyped : profile.Wrappable) :
    HasSort profile.costCoreLanguage profile.costWholeRedexFreeContext []
      profile.costWholeRedexTarget costWrappedSortName := by
  have declared := profile.apparatus_mem_costCore
  exact CostApparatus.contact_hasType (declared _ (by simp [costCoreConstructors]))
    (profile.costMappedContractum_hasType contractumTyped)
    (CostApparatus.funding_hasType (declared _ (by simp [costCoreConstructors]))
      (.fvar profile.costWholeRedexFreeContext_stackTail))

/-- The two-slot context is recovered exactly; there is no second policy for
which source variables receive wrapped types. -/
theorem ofRetypingPlan_costRetypedSourceContext (source : CIGSLT) :
    (ofRetypingPlan source.continuationRetyping).costRetypedSourceContext =
      source.costRetypedSourceContext := by
  simp only [costRetypedSourceContext, CIGSLT.costRetypedSourceContext,
    selectedVariable, ofRetypingPlan, primary, List.any_nil, Bool.or_false,
    Bool.or_eq_true, beq_iff_eq]

theorem ofRetypingPlan_costWholeRedexTypeContext (source : CIGSLT) :
    (ofRetypingPlan source.continuationRetyping).costWholeRedexTypeContext =
      source.costWholeRedexTypeContext := by
  unfold costWholeRedexTypeContext CIGSLT.costWholeRedexTypeContext
  rw [ofRetypingPlan_costRetypedSourceContext]
  rfl

theorem ofRetypingPlan_costWholeRedexSource (source : CIGSLT) :
    (ofRetypingPlan source.continuationRetyping).costWholeRedexSource =
      source.costWholeRedexSource := by
  rw [source.costWholeRedexSource_eq]
  rfl

theorem ofRetypingPlan_costWholeRedexTarget (source : CIGSLT) :
    (ofRetypingPlan source.continuationRetyping).costWholeRedexTarget =
      source.costWholeRedexTarget := by
  unfold costWholeRedexTarget costMappedContractum
  rw [ofRetypingPlan_mapContractum]
  rfl

/-- The existing whole-redex rule is the two-slot instance of this finite
construction, including its exact context and ordered endpoints. -/
theorem ofRetypingPlan_costWholeRedexRewrite (source : CIGSLT) :
    (ofRetypingPlan source.continuationRetyping).costWholeRedexRewrite =
      source.costWholeRedexRewrite := by
  unfold costWholeRedexRewrite
  rw [ofRetypingPlan_costWholeRedexTypeContext, ofRetypingPlan_costWholeRedexSource,
    ofRetypingPlan_costWholeRedexTarget]
  rfl

#print axioms costWholeRedexSource_hasType
#print axioms costWholeRedexTarget_hasType

end ContinuationDecorationProfile
end Mettapedia.GSLT.LanguageDef
