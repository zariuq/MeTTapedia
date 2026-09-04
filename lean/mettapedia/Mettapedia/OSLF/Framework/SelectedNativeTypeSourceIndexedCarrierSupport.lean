import Mettapedia.OSLF.Framework.CarrierObjectNameLookup
import Mettapedia.OSLF.Framework.ContextualCarrierClaims
import Mettapedia.OSLF.Framework.ContextualModalExtension
import Mettapedia.OSLF.Framework.SelectedNativeTypeDemand

/-!
# Authored carrier support for source-indexed selected native types

The contextual modal signature needs the rewrite, focus, binder-prefix, and
fixed-context carriers of a selected occurrence.  A source-indexed
introduction rule additionally embeds the literal authored endpoints, so it
must also be able to type every variable from the rewrite's type context.

Those endpoint carriers form an append-only suffix.  The source validator
already proves them grounded, and positional naming preserves every carrier
name allocated by the earlier modal signature.  Consequently this extension
adds only genuinely missing carrier/universe rows and their contextual claim
bridges; it does not mutate the standalone modal generator.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedCarrierSupport

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Framework

/-- Authored endpoint-variable carriers in selected occurrence order and
source type-context order.  Repeated roots remain visible at this boundary;
the carrier request performs stable first-occurrence closure. -/
def authoredRoots {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) : List TypeExpr :=
  demand.occurrences.flatMap fun occurrence =>
    SelectedNativeTypeFoundation.authoredVariableCarrierTypes
      occurrence.typing

/-- Endpoint support certified entirely by the authored source validator. -/
def authoredRequest {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    CarrierObjectClosure.Request source where
  roots := authoredRoots demand
  grounded := by
    intro object objectMembership
    rw [authoredRoots, List.mem_flatMap] at objectMembership
    obtain ⟨occurrence, _occurrenceMembership, carrierMembership⟩ :=
      objectMembership
    exact SelectedNativeTypeFoundation.authoredVariableCarrier_grounded
      occurrence.typing carrierMembership

/-- Complete carrier support used by literal source-indexed rules.  The
standalone modal foundation is the exact prefix. -/
def augmentedRequest {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    CarrierObjectClosure.Request source :=
  demand.foundation.carrierObjects.append (authoredRequest demand)

/-- Fail-closed resolver over the augmented source-indexed inventory. -/
def resolve {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (object : TypeExpr) : String :=
  (CarrierObjectNameLookup.indexed? (augmentedRequest demand) object).getD ""

/-- An exact selected endpoint carrier is retained by the augmented
inventory. -/
theorem authoredCarrier_mem_augmented
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (slot : Fin demand.occurrences.length) {object : TypeExpr}
    (membership : object ∈
      SelectedNativeTypeFoundation.authoredVariableCarrierTypes
        (demand.occurrences.get slot).typing) :
    object ∈ (augmentedRequest demand).objects := by
  apply CarrierObjectClosure.Request.root_mem_objects
  unfold augmentedRequest
  rw [CarrierObjectClosure.Request.append_roots, List.mem_append]
  apply Or.inr
  change object ∈ authoredRoots demand
  rw [authoredRoots, List.mem_flatMap]
  exact ⟨demand.occurrences.get slot,
    List.get_mem demand.occurrences slot, membership⟩

/-- Appending endpoint support preserves every previously allocated modal
carrier name exactly. -/
theorem resolve_eq_modal_of_mem
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) {object : TypeExpr}
    (membership : object ∈ demand.foundation.carrierObjects.objects) :
    resolve demand object =
      ContextualModalExtension.compiledCarrierName demand.foundation object := by
  unfold resolve augmentedRequest
  unfold ContextualModalExtension.compiledCarrierName
  rw [CarrierObjectNameLookup.indexed?_append_of_mem
    demand.foundation.carrierObjects (authoredRequest demand) membership]

/-- The selected typing at any demand occurrence is present in the derived
modal foundation at the same authored position. -/
theorem selectedTyping_mem_foundation
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (slot : Fin demand.occurrences.length) :
    (demand.occurrences.get slot).typing ∈ demand.foundation.typings := by
  change (demand.occurrences.get slot).typing ∈
    demand.occurrences.map ProfiledRewriteOccurrence.typing
  exact List.mem_map.mpr
    ⟨demand.occurrences.get slot, List.get_mem demand.occurrences slot, rfl⟩

/-- Every carrier required by the earlier modal signature keeps its old name
inside the source-indexed extension. -/
theorem resolve_eq_modal_of_required
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (slot : Fin demand.occurrences.length) {object : TypeExpr}
    (required : object ∈
      SelectedNativeTypeFoundation.requiredCarrierRoots
        (demand.occurrences.get slot).typing) :
    resolve demand object =
      ContextualModalExtension.compiledCarrierName demand.foundation object := by
  apply resolve_eq_modal_of_mem demand
  exact demand.foundation.requiredCarrier_mem_objects
    (selectedTyping_mem_foundation demand slot) required

/-- Minimal new carrier rows after the standalone modal foundation. -/
def carrierExtension {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) : CalculusLanguageExtension :=
  CarrierObjectLanguageDef.indexedAppendExtension
    demand.foundation.carrierObjects (authoredRequest demand)

/-- Exact names introduced by the endpoint carrier suffix. -/
def additionalCarrierNames {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) : List String :=
  (carrierExtension demand).newTypes.map TypeDecl.name

/-- The earlier modal carrier names and the exact append-only suffix are the
complete names of the augmented carrier inventory. -/
theorem carrierNames_append {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
        additionalCarrierNames demand =
      (CarrierObjectLanguageDef.indexedDefinition
        (augmentedRequest demand)).toLanguageDef.typeNames := by
  have applied := CarrierObjectLanguageDef.indexedAppendExtension_apply
    demand.foundation.carrierObjects (authoredRequest demand)
  have typesEqual := congrArg
    (fun definition : CalculusLanguageDef => definition.types) applied
  have namesEqual := congrArg (List.map TypeDecl.name) typesEqual
  simpa [carrierExtension, additionalCarrierNames, augmentedRequest,
    SelectedNativeTypeFoundation.definition,
    SelectedNativeTypeFoundation.stableCarrierNames,
    SelectedNativeTypeFoundation.stableCarrierTypes,
    CarrierObjectLanguageDef.indexedDefinition,
    CalculusLanguageExtension.apply_types,
    LanguageDef.typeNames, List.map_append] using namesEqual

/-- Resolving any retained source carrier yields a name in the exact combined
carrier namespace; failure defaults never enter this covered theorem. -/
theorem resolve_mem_carrierNames {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) {object : TypeExpr}
    (membership : object ∈ (augmentedRequest demand).objects) :
    resolve demand object ∈
      SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
        additionalCarrierNames demand := by
  rw [carrierNames_append]
  have retained := CarrierObjectNameLookup.indexed_name_mem_typeNames membership
  simpa [resolve, CarrierObjectNameLookup.indexed?,
    CarrierObjectNameLookup.lookup?_eq_some_of_mem _ membership,
    CarrierObjectLanguageDef.indexedDefinition,
    CarrierObjectLanguageDef.definition,
    CarrierTypingLanguageDef.definition,
    CarrierObjectLanguageDef.validatedCarrierSignature,
    CarrierObjectLanguageDef.carrierSignature,
    CarrierUniverseSignature.language,
    LanguageDef.typeNames] using retained

/-- The carrier residual contains precisely the universe-code rows of the
new carrier-name suffix. -/
theorem carrierExtension_terms {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    (carrierExtension demand).newTerms =
      CarrierUniverseSignature.termsFor (additionalCarrierNames demand) := by
  unfold carrierExtension CarrierObjectLanguageDef.indexedAppendExtension
    CalculusLanguageExtension.AppendOnlyCalculusRefinement.residual
  change
    (CarrierObjectLanguageDef.indexedDefinition
      (demand.foundation.carrierObjects.append
        (authoredRequest demand))).terms.drop
      (CarrierObjectLanguageDef.indexedDefinition
        demand.foundation.carrierObjects).terms.length = _
  unfold CarrierObjectLanguageDef.indexedDefinition
  rw [CarrierObjectLanguageDef.definition_terms,
    CarrierObjectLanguageDef.definition_terms]
  have nameEqRaw :
      SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
          additionalCarrierNames demand =
        (CarrierObjectLanguageDef.carrierTypes
          (CarrierObjectLanguageDef.Naming.indexed
            (demand.foundation.carrierObjects.append
              (authoredRequest demand)))).map TypeDecl.name := by
    simpa [augmentedRequest, CarrierObjectLanguageDef.indexedDefinition,
      CarrierObjectLanguageDef.definition, CarrierTypingLanguageDef.definition,
      CarrierObjectLanguageDef.validatedCarrierSignature,
      CarrierObjectLanguageDef.carrierSignature,
      CarrierUniverseSignature.language, LanguageDef.typeNames] using
        carrierNames_append demand
  rw [← nameEqRaw]
  change
    (CarrierUniverseSignature.termsFor
      (SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
        additionalCarrierNames demand)).drop
      (CarrierUniverseSignature.termsFor
        (SelectedNativeTypeFoundation.stableCarrierNames
          demand.foundation)).length = _
  rw [CarrierUniverseSignature.termsFor_append]
  simp

/-- The same residual exposes precisely the typing-judgment rows of the new
carrier-name suffix. -/
theorem carrierExtension_judgments {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    (carrierExtension demand).newJudgments =
      (additionalCarrierNames demand).map
        CarrierTypingLanguageDef.judgment := by
  unfold carrierExtension CarrierObjectLanguageDef.indexedAppendExtension
    CalculusLanguageExtension.AppendOnlyCalculusRefinement.residual
  change
    (CarrierObjectLanguageDef.indexedDefinition
      (demand.foundation.carrierObjects.append
        (authoredRequest demand))).judgments.drop
      (CarrierObjectLanguageDef.indexedDefinition
        demand.foundation.carrierObjects).judgments.length = _
  unfold CarrierObjectLanguageDef.indexedDefinition
  rw [CarrierObjectLanguageDef.definition_judgments,
    CarrierObjectLanguageDef.definition_judgments]
  have nameEqRaw :
      SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
          additionalCarrierNames demand =
        (CarrierObjectLanguageDef.carrierTypes
          (CarrierObjectLanguageDef.Naming.indexed
            (demand.foundation.carrierObjects.append
              (authoredRequest demand)))).map TypeDecl.name := by
    simpa [augmentedRequest, CarrierObjectLanguageDef.indexedDefinition,
      CarrierObjectLanguageDef.definition, CarrierTypingLanguageDef.definition,
      CarrierObjectLanguageDef.validatedCarrierSignature,
      CarrierObjectLanguageDef.carrierSignature,
      CarrierUniverseSignature.language, LanguageDef.typeNames] using
        carrierNames_append demand
  rw [← nameEqRaw]
  change
    ((SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
      additionalCarrierNames demand).map
        CarrierTypingLanguageDef.judgment).drop
      ((SelectedNativeTypeFoundation.stableCarrierNames
        demand.foundation).map CarrierTypingLanguageDef.judgment).length = _
  rw [List.map_append]
  simp

/-- Carrier-universe axioms follow the same exact append decomposition. -/
theorem carrierExtension_rules {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    (carrierExtension demand).newRules =
      (additionalCarrierNames demand).map
        CarrierTypingLanguageDef.universeAxiom := by
  unfold carrierExtension CarrierObjectLanguageDef.indexedAppendExtension
    CalculusLanguageExtension.AppendOnlyCalculusRefinement.residual
  change
    (CarrierObjectLanguageDef.indexedDefinition
      (demand.foundation.carrierObjects.append
        (authoredRequest demand))).rules.drop
      (CarrierObjectLanguageDef.indexedDefinition
        demand.foundation.carrierObjects).rules.length = _
  unfold CarrierObjectLanguageDef.indexedDefinition
  rw [CarrierObjectLanguageDef.definition_rules,
    CarrierObjectLanguageDef.definition_rules]
  have nameEqRaw :
      SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
          additionalCarrierNames demand =
        (CarrierObjectLanguageDef.carrierTypes
          (CarrierObjectLanguageDef.Naming.indexed
            (demand.foundation.carrierObjects.append
              (authoredRequest demand)))).map TypeDecl.name := by
    simpa [augmentedRequest, CarrierObjectLanguageDef.indexedDefinition,
      CarrierObjectLanguageDef.definition, CarrierTypingLanguageDef.definition,
      CarrierObjectLanguageDef.validatedCarrierSignature,
      CarrierObjectLanguageDef.carrierSignature,
      CarrierUniverseSignature.language, LanguageDef.typeNames] using
        carrierNames_append demand
  rw [← nameEqRaw]
  change
    ((SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
      additionalCarrierNames demand).map
        CarrierTypingLanguageDef.universeAxiom).drop
      ((SelectedNativeTypeFoundation.stableCarrierNames
        demand.foundation).map CarrierTypingLanguageDef.universeAxiom).length = _
  rw [List.map_append]
  simp

/-- Contextual variable/typing/reduction claims for exactly the new carrier
suffix.  Shared context rows already belong to the standalone signature. -/
def claimExtension {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) : CalculusLanguageExtension :=
  ContextualCarrierClaims.carrierExtension (additionalCarrierNames demand)

/-- Complete proof-only endpoint-support suffix. -/
def extension {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) : CalculusLanguageExtension :=
  (carrierExtension demand).comp (claimExtension demand)

/-- The complete endpoint-support term suffix consists of the new universe
codes followed by the contextual claim constructors for exactly the same
carrier names. -/
theorem extension_terms {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    (extension demand).newTerms =
      CarrierUniverseSignature.termsFor (additionalCarrierNames demand) ++
        ContextualCarrierClaims.claimTermsFor
          (additionalCarrierNames demand) := by
  simp [extension, carrierExtension_terms, claimExtension,
    ContextualCarrierClaims.carrierExtension,
    CalculusLanguageExtension.comp]

/-- No duplicate judgment family is introduced: the residual contains one
carrier-indexed typing judgment for every genuinely new carrier. -/
theorem extension_judgments {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    (extension demand).newJudgments =
      (additionalCarrierNames demand).map
        CarrierTypingLanguageDef.judgment := by
  simp [extension, carrierExtension_judgments, claimExtension,
    ContextualCarrierClaims.carrierExtension,
    CalculusLanguageExtension.comp]

/-- Universe axioms precede their contextual typing bridges in the exact
residual rule inventory. -/
theorem extension_rules {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    (extension demand).newRules =
      (additionalCarrierNames demand).map
          CarrierTypingLanguageDef.universeAxiom ++
        ContextualCarrierClaims.bridgeRules
          (additionalCarrierNames demand) := by
  simp [extension, carrierExtension_rules, claimExtension,
    ContextualCarrierClaims.carrierExtension,
    CalculusLanguageExtension.comp]

@[simp] theorem extension_equations_empty
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    (extension demand).newEquations = [] := by
  rfl

@[simp] theorem extension_rewrites_empty
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    (extension demand).newRewrites = [] := by
  rfl

/-- With no selected occurrences there is no authored endpoint suffix. -/
theorem empty_authoredRoots (source : ValidatedLanguageDef) :
    authoredRoots (SelectedNativeTypeDemand.empty source) = [] := by
  rfl

#print axioms authoredCarrier_mem_augmented
#print axioms resolve_eq_modal_of_mem
#print axioms resolve_eq_modal_of_required
#print axioms extension_terms
#print axioms extension_judgments
#print axioms extension_rules
#print axioms extension_rewrites_empty

end Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedCarrierSupport
