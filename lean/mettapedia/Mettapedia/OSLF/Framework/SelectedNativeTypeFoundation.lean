import Mettapedia.OSLF.Framework.CarrierObjectLanguageDef
import Mettapedia.OSLF.Framework.DisplayedContextProfile
import Mettapedia.OSLF.Framework.DisplayedOccurrenceLanguage

/-!
# Carrier foundation selected by typed rewrite occurrences

A typed occurrence determines the carrier objects needed by contextual OSLF
generation: the rewrite and focus carriers, binder-prefix carriers, and every
fixed-context dependency carrier. One ordered demand collects those roots,
checks that they are grounded in the authored source GSLT, and closes them
hereditarily.

The generated foundation is exactly the existing sparse carrier-object
calculus. It contains carrier sorts, their star/box universe constructors,
carrier-indexed typing judgments, and universe axioms. It contains no modal
constructor and chooses no hypercube vertex. Contextual modal signatures and
their proof calculus are later extensions of this one flat GSLT.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.WellSorted

namespace SelectedNativeTypeFoundation

/-- Carrier expressions required by one typed displayed rewrite site. -/
def requiredCarrierRoots {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) : List TypeExpr :=
  [typing.rewriteType, typing.focusType] ++ typing.focusBoundPrefix ++
    DisplayedContextProfile.carrierTypes typing

/-- Every generated carrier root refers only to source-declared base sorts. -/
def CarrierGrounded {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) : Prop :=
  ∀ object ∈ requiredCarrierRoots typing,
    CarrierObjectClosure.GroundedIn source object

/-- Ordered, proof-carrying carrier-foundation demand over one source GSLT. -/
structure Demand (source : ValidatedLanguageDef) where
  typings : List (DisplayedRewriteTyping source)
  grounded : ∀ typing ∈ typings, CarrierGrounded typing

namespace Demand

@[ext]
theorem ext {source : ValidatedLanguageDef} {first second : Demand source}
    (typings : first.typings = second.typings) : first = second := by
  cases first
  cases second
  cases typings
  rfl

/-- Empty carrier demand. -/
def empty (source : ValidatedLanguageDef) : Demand source where
  typings := []
  grounded := by simp

/-- Ordered composition of carrier demands. -/
def append {source : ValidatedLanguageDef}
    (first second : Demand source) : Demand source where
  typings := first.typings ++ second.typings
  grounded := by
    intro typing membership
    rw [List.mem_append] at membership
    rcases membership with firstMembership | secondMembership
    · exact first.grounded typing firstMembership
    · exact second.grounded typing secondMembership

@[simp]
theorem empty_typings (source : ValidatedLanguageDef) :
    (empty source).typings = [] :=
  rfl

@[simp]
theorem append_typings {source : ValidatedLanguageDef}
    (first second : Demand source) :
    (first.append second).typings = first.typings ++ second.typings :=
  rfl

theorem empty_append {source : ValidatedLanguageDef}
    (demand : Demand source) : (empty source).append demand = demand := by
  apply Demand.ext
  simp

theorem append_empty {source : ValidatedLanguageDef}
    (demand : Demand source) : demand.append (empty source) = demand := by
  apply Demand.ext
  simp

theorem append_assoc {source : ValidatedLanguageDef}
    (first second third : Demand source) :
    (first.append second).append third = first.append (second.append third) := by
  apply Demand.ext
  simp [List.append_assoc]

/-- Exact occurrence selection underlying the carrier demand. -/
def selectedSites {source : ValidatedLanguageDef}
    (demand : Demand source) : DisplayedSiteSelection source.language :=
  demand.typings.map (·.site)

/-- Ordered carrier roots underlying the demand. -/
def carrierRoots {source : ValidatedLanguageDef}
    (demand : Demand source) : List TypeExpr :=
  demand.typings.flatMap requiredCarrierRoots

/-- Hereditarily closed, source-grounded carrier inventory. -/
def carrierObjects {source : ValidatedLanguageDef}
    (demand : Demand source) : CarrierObjectClosure.Request source where
  roots := demand.carrierRoots
  grounded := by
    intro object objectMembership
    obtain ⟨typing, typingMembership, objectMembership⟩ :=
      List.mem_flatMap.mp objectMembership
    exact demand.grounded typing typingMembership object objectMembership

/-- Occurrence-sensitive view used by later contextual generation. -/
def occurrenceLanguage {source : ValidatedLanguageDef}
    (demand : Demand source) : DisplayedOccurrenceLanguage :=
  .atSelection source demand.selectedSites

@[simp]
theorem selectedSites_append {source : ValidatedLanguageDef}
    (first second : Demand source) :
    (first.append second).selectedSites =
      first.selectedSites ++ second.selectedSites := by
  simp [selectedSites, append]

@[simp]
theorem carrierRoots_append {source : ValidatedLanguageDef}
    (first second : Demand source) :
    (first.append second).carrierRoots =
      first.carrierRoots ++ second.carrierRoots := by
  simp [carrierRoots, append]

theorem carrierObjects_append {source : ValidatedLanguageDef}
    (first second : Demand source) :
    (first.append second).carrierObjects =
      first.carrierObjects.append second.carrierObjects := by
  apply CarrierObjectClosure.Request.ext
  exact carrierRoots_append first second

theorem carrierObjects_prefix_append {source : ValidatedLanguageDef}
    (first second : Demand source) :
    first.carrierObjects.objects.IsPrefix
      (first.append second).carrierObjects.objects := by
  rw [carrierObjects_append]
  exact CarrierObjectClosure.Request.objects_prefix_append _ _

@[simp]
theorem length_selectedSites {source : ValidatedLanguageDef}
    (demand : Demand source) :
    demand.selectedSites.length = demand.typings.length := by
  simp [selectedSites]

@[simp]
theorem carrierObjects_roots {source : ValidatedLanguageDef}
    (demand : Demand source) :
    demand.carrierObjects.roots = demand.carrierRoots :=
  rfl

/-- Every carrier explicitly required by a selected typing is retained by the
closed carrier inventory.  Later syntax generators use this theorem instead
of performing an unchecked positional lookup. -/
theorem requiredCarrier_mem_objects {source : ValidatedLanguageDef}
    (demand : Demand source) {typing : DisplayedRewriteTyping source}
    (typingMembership : typing ∈ demand.typings) {object : TypeExpr}
    (required : object ∈ requiredCarrierRoots typing) :
    object ∈ demand.carrierObjects.objects := by
  apply CarrierObjectClosure.Request.root_mem_objects
  change object ∈ demand.carrierRoots
  exact List.mem_flatMap.mpr
    ⟨typing, typingMembership, required⟩

end Demand

/-- One flat carrier calculus, obtained by the generic carrier-object
construction rather than a second allocation machine. -/
def definition {source : ValidatedLanguageDef}
    (demand : Demand source) : CalculusLanguageDef :=
  CarrierObjectLanguageDef.indexedDefinition demand.carrierObjects

/-- Admission delegates to the ordinary calculus-language validator. -/
def validate? {source : ValidatedLanguageDef}
    (demand : Demand source) : Option ValidatedCalculusLanguageDef :=
  (definition demand).validate?

/-- Exact suffix needed to continue an already generated carrier foundation. -/
def appendExtension {source : ValidatedLanguageDef}
    (earlier later : Demand source) : CalculusLanguageExtension :=
  CarrierObjectLanguageDef.indexedAppendExtension
    earlier.carrierObjects later.carrierObjects

/-- Demand append is the generic carrier-request append operation. -/
theorem definition_append {source : ValidatedLanguageDef}
    (earlier later : Demand source) :
    definition (earlier.append later) =
      (appendExtension earlier later).apply (definition earlier) := by
  rw [definition, appendExtension, Demand.carrierObjects_append]
  exact (CarrierObjectLanguageDef.indexedAppendExtension_apply
    earlier.carrierObjects later.carrierObjects).symm

/-- Every previously generated carrier row remains an exact prefix. -/
theorem definition_appendOnly {source : ValidatedLanguageDef}
    (earlier later : Demand source) :
    CalculusLanguageExtension.AppendOnlyCalculusRefinement
      (definition earlier) (definition (earlier.append later)) := by
  change CalculusLanguageExtension.AppendOnlyCalculusRefinement
    (CarrierObjectLanguageDef.indexedDefinition earlier.carrierObjects)
    (CarrierObjectLanguageDef.indexedDefinition
      (earlier.append later).carrierObjects)
  rw [Demand.carrierObjects_append]
  exact CarrierObjectLanguageDef.indexedDefinition_appendOnly
    earlier.carrierObjects later.carrierObjects

/-- Stable private carrier declarations in inventory order. -/
def stableCarrierTypes {source : ValidatedLanguageDef}
    (demand : Demand source) : List TypeDecl :=
  CarrierObjectLanguageDef.carrierTypes
    (CarrierObjectLanguageDef.Naming.indexed demand.carrierObjects)

/-- Stable private carrier names in inventory order. -/
def stableCarrierNames {source : ValidatedLanguageDef}
    (demand : Demand source) : List String :=
  (stableCarrierTypes demand).map (·.name)

/-- Positional carrier declarations depend only on inventory cardinality;
their proof-relevant carrier denotation remains in the request slots. -/
theorem stableCarrierTypes_eq_of_object_count
    {firstSource secondSource : ValidatedLanguageDef}
    (first : Demand firstSource) (second : Demand secondSource)
    (count : first.carrierObjects.objects.length =
      second.carrierObjects.objects.length) :
    stableCarrierTypes first = stableCarrierTypes second := by
  unfold stableCarrierTypes CarrierObjectLanguageDef.carrierTypes
  rw [List.ofFn_congr count]
  rfl

theorem stableCarrierNames_nodup {source : ValidatedLanguageDef}
    (demand : Demand source) : (stableCarrierNames demand).Nodup := by
  unfold stableCarrierNames stableCarrierTypes
  simpa [CarrierObjectLanguageDef.carrierSignature,
    LanguageDef.typeNames] using
    CarrierObjectLanguageDef.carrierTypeNames_nodup
      (CarrierObjectLanguageDef.Naming.indexed demand.carrierObjects)

@[simp]
theorem length_stableCarrierNames {source : ValidatedLanguageDef}
    (demand : Demand source) :
    (stableCarrierNames demand).length =
      demand.carrierObjects.objects.length := by
  simp [stableCarrierNames, stableCarrierTypes,
    CarrierObjectLanguageDef.length_carrierTypes]

@[simp]
theorem definition_types {source : ValidatedLanguageDef}
    (demand : Demand source) :
    (definition demand).types = stableCarrierTypes demand :=
  rfl

@[simp]
theorem definition_typeNames {source : ValidatedLanguageDef}
    (demand : Demand source) :
    (definition demand).toLanguageDef.typeNames = stableCarrierNames demand := by
  simp [LanguageDef.typeNames, stableCarrierNames]

@[simp]
theorem definition_terms {source : ValidatedLanguageDef}
    (demand : Demand source) :
    (definition demand).terms =
      CarrierUniverseSignature.termsFor (stableCarrierNames demand) := by
  rfl

@[simp]
theorem definition_judgments {source : ValidatedLanguageDef}
    (demand : Demand source) :
    (definition demand).judgments =
      (stableCarrierNames demand).map CarrierTypingLanguageDef.judgment := by
  rfl

@[simp]
theorem definition_rules {source : ValidatedLanguageDef}
    (demand : Demand source) :
    (definition demand).rules =
      (stableCarrierNames demand).map
        CarrierTypingLanguageDef.universeAxiom := by
  rfl

@[simp]
theorem definition_equations {source : ValidatedLanguageDef}
    (demand : Demand source) : (definition demand).equations = [] :=
  rfl

@[simp]
theorem definition_rewrites {source : ValidatedLanguageDef}
    (demand : Demand source) : (definition demand).rewrites = [] :=
  rfl

@[simp]
theorem definition_conversion {source : ValidatedLanguageDef}
    (demand : Demand source) : (definition demand).conversion = none :=
  rfl

@[simp]
theorem definition_term_count {source : ValidatedLanguageDef}
    (demand : Demand source) :
    (definition demand).terms.length =
      2 * demand.carrierObjects.objects.length := by
  rw [definition_terms, CarrierUniverseSignature.length_termsFor]
  simp [stableCarrierNames, stableCarrierTypes,
    CarrierObjectLanguageDef.carrierTypes]

/-! ## Positive and negative controls -/

namespace Canary

/-- Empty selection generates the empty carrier calculus. -/
theorem empty_demand_counts (source : ValidatedLanguageDef) :
    (definition (Demand.empty source)).types.length = 0 ∧
      (definition (Demand.empty source)).terms.length = 0 ∧
      (definition (Demand.empty source)).judgments.length = 0 ∧
      (definition (Demand.empty source)).rules.length = 0 := by
  have emptyObjects :
      (Demand.empty source).carrierObjects.objects = [] := by
    rfl
  constructor
  · rw [definition_types]
    unfold stableCarrierTypes
    rw [CarrierObjectLanguageDef.length_carrierTypes, emptyObjects]
    rfl
  constructor
  · rw [definition_term_count, emptyObjects]
    rfl
  constructor
  · rw [definition_judgments]
    simp [stableCarrierNames, stableCarrierTypes,
      CarrierObjectLanguageDef.length_carrierTypes, emptyObjects]
  · rw [definition_rules]
    simp [stableCarrierNames, stableCarrierTypes,
      CarrierObjectLanguageDef.length_carrierTypes, emptyObjects]

/-- A typing known not to be grounded cannot be smuggled into a singleton
foundation demand. -/
theorem ungrounded_typing_cannot_be_selected
    {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source)
    (ungrounded : ¬ CarrierGrounded typing) :
    ¬ ∃ demand : Demand source, demand.typings = [typing] := by
  rintro ⟨demand, equality⟩
  apply ungrounded
  exact demand.grounded typing (by simp [equality])

end Canary


#print axioms Demand.append_assoc
#print axioms Demand.carrierObjects_append
#print axioms Demand.carrierObjects_prefix_append
#print axioms Demand.requiredCarrier_mem_objects
#print axioms definition_append
#print axioms definition_appendOnly
#print axioms stableCarrierNames_nodup
#print axioms definition_typeNames
#print axioms stableCarrierTypes_eq_of_object_count
#print axioms length_stableCarrierNames
#print axioms definition_types
#print axioms definition_terms
#print axioms definition_term_count
#print axioms Canary.empty_demand_counts
#print axioms Canary.ungrounded_typing_cannot_be_selected

end SelectedNativeTypeFoundation

end Mettapedia.OSLF.Framework
