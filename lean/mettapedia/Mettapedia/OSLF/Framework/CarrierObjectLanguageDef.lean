import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Infix
import Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension
import Mettapedia.OSLF.Framework.CarrierObjectClosure
import Mettapedia.OSLF.Framework.CarrierTypingLanguageDef

/-!
# Sparse carrier-object calculus languages

`CarrierObjectClosure.Request` determines the finite family of carrier objects
needed by one native-type generation request.  This module assigns those
objects injective request-local names and reuses the per-carrier
Stay--Wells construction to obtain one checked calculus language.

The naming interface is intentionally abstract.  A compact positional naming
is supplied for revision-bound compilation, but no theorem treats those names
as globally meaningful: their denotation is the proof-relevant slot map back
to the request's `TypeExpr` inventory.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef

namespace CarrierObjectLanguageDef

open CarrierObjectClosure

/-- An injective wire naming for every carrier slot in one sparse request. -/
structure Naming {source : ValidatedLanguageDef}
    (request : CarrierObjectClosure.Request source) where
  name : request.Slot → String
  injective : Function.Injective name

namespace Naming

/-- Compact wire name for a numerical carrier slot.  The number has meaning
only together with the revision-bound request that supplies the slot-to-object
map; it is not a serialization of `TypeExpr`. -/
def indexedNameAt (index : Nat) : String :=
  String.ofList
    ("$oslf:carrier-object:".toList ++ List.replicate index 'i')

theorem indexedNameAt_injective : Function.Injective indexedNameAt := by
  intro first second equality
  have lists := congrArg String.toList equality
  have suffixEquality : List.replicate first 'i' =
      List.replicate second 'i' := by
    apply List.append_left_injective "$oslf:carrier-object:".toList
    simpa [indexedNameAt] using lists
  have lengths := congrArg List.length suffixEquality
  simpa using lengths

/-- Request-typed form of `indexedNameAt`. -/
def indexedName {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    (slot : request.Slot) : String :=
  indexedNameAt slot.val

theorem indexedName_injective {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source} :
    Function.Injective (indexedName (request := request)) := by
  intro first second equality
  apply Fin.ext
  exact indexedNameAt_injective equality

/-- Default compact naming for a revision-bound generated language. -/
def indexed {source : ValidatedLanguageDef}
    (request : CarrierObjectClosure.Request source) : Naming request where
  name := indexedName
  injective := indexedName_injective

/-- Append-only request inclusion preserves every earlier indexed wire name
on the nose. -/
@[simp]
theorem indexedName_appendSlot {source : ValidatedLanguageDef}
    (first second : CarrierObjectClosure.Request source)
    (slot : first.Slot) :
    indexedName (request := first.append second)
        (first.appendSlot second slot) =
      indexedName (request := first) slot :=
  rfl

end Naming

/-- One private base-sort declaration for each retained carrier object. -/
def carrierTypes {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    (naming : Naming request) : List TypeDecl :=
  List.ofFn fun slot : request.Slot => TypeDecl.plain (naming.name slot)

/-- The finite object-reification signature.  It has no term or reduction
rules; universe codes and typing rules are added by the existing checked
per-carrier construction. -/
def carrierSignature {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    (naming : Naming request) : LanguageDef :=
  { name := "$oslf:carrier-objects:" ++ source.language.name
    types := carrierTypes naming
    terms := []
    equations := []
    rewrites := [] }

theorem carrierTypeNames {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    (naming : Naming request) :
    (carrierSignature naming).typeNames = List.ofFn naming.name := by
  simp [carrierSignature, carrierTypes, LanguageDef.typeNames, List.map_ofFn,
    Function.comp_def, TypeDecl.plain]

theorem carrierTypeNames_nodup {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    (naming : Naming request) :
    (carrierSignature naming).typeNames.Nodup := by
  rw [carrierTypeNames]
  exact List.nodup_ofFn_ofInjective naming.injective

theorem carrierSignature_valid {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    (naming : Naming request) :
    (carrierSignature naming).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly
  · rfl
  · rfl
  · exact carrierTypeNames_nodup naming
  · simp [carrierSignature]
  · intro term membership
    simp [carrierSignature] at membership
  · intro term membership
    simp [carrierSignature] at membership
  · intro term membership
    simp [carrierSignature] at membership

/-- Validated carrier-object signature used as the input to the per-carrier
typing construction. -/
def validatedCarrierSignature {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    (naming : Naming request) : ValidatedLanguageDef :=
  ⟨carrierSignature naming, carrierSignature_valid naming⟩

/-- Flat sparse per-object universe and typing language. -/
def definition {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    (naming : Naming request) : CalculusLanguageDef :=
  CarrierTypingLanguageDef.definition (validatedCarrierSignature naming)

/-- All flat rows generated for an ordered list of already allocated carrier
names.  This is the carrier-family homomorphism into the generic language
extension monoid; request closure and name allocation remain separate
concerns. -/
def extension (carrierNames : List String) : CalculusLanguageExtension :=
  { newTypes := carrierNames.map TypeDecl.plain
    newTerms := CarrierUniverseSignature.termsFor carrierNames
    newJudgments := carrierNames.map CarrierTypingLanguageDef.judgment
    newRules := carrierNames.map CarrierTypingLanguageDef.universeAxiom }

/-- Carrier-family generation preserves ordered composition exactly. -/
theorem extension_append (first second : List String) :
    extension (first ++ second) =
      (extension first).comp (extension second) := by
  simp [extension, CalculusLanguageExtension.comp,
    CarrierUniverseSignature.termsFor_append]

@[simp] theorem extension_types (carrierNames : List String) :
    (extension carrierNames).newTypes = carrierNames.map TypeDecl.plain :=
  rfl

@[simp] theorem extension_terms (carrierNames : List String) :
    (extension carrierNames).newTerms =
      CarrierUniverseSignature.termsFor carrierNames :=
  rfl

@[simp] theorem extension_judgments (carrierNames : List String) :
    (extension carrierNames).newJudgments =
      carrierNames.map CarrierTypingLanguageDef.judgment :=
  rfl

@[simp] theorem extension_rules (carrierNames : List String) :
    (extension carrierNames).newRules =
      carrierNames.map CarrierTypingLanguageDef.universeAxiom :=
  rfl

@[simp]
theorem definition_types {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    (naming : Naming request) :
    (definition naming).types = carrierTypes naming :=
  rfl

@[simp]
theorem definition_terms {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    (naming : Naming request) :
    (definition naming).terms =
      CarrierUniverseSignature.termsFor
        ((carrierTypes naming).map (·.name)) :=
  rfl

@[simp]
theorem definition_equations {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    (naming : Naming request) :
    (definition naming).equations = [] :=
  rfl

@[simp]
theorem definition_rewrites {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    (naming : Naming request) :
    (definition naming).rewrites = [] :=
  rfl

@[simp]
theorem definition_judgments {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    (naming : Naming request) :
    (definition naming).judgments =
      ((carrierTypes naming).map (·.name)).map
        CarrierTypingLanguageDef.judgment :=
  rfl

@[simp]
theorem definition_rules {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    (naming : Naming request) :
    (definition naming).rules =
      ((carrierTypes naming).map (·.name)).map
        CarrierTypingLanguageDef.universeAxiom :=
  rfl

@[simp]
theorem definition_conversion {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    (naming : Naming request) :
    (definition naming).conversion = none :=
  rfl

/-- The flat sparse per-object language passes the generic inference gate. -/
theorem definition_valid {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    (naming : Naming request) : (definition naming).isValid = true :=
  CarrierTypingLanguageDef.definition_valid (validatedCarrierSignature naming)

/-- Fully checked sparse per-object universe and typing language. -/
def validated {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    (naming : Naming request) : ValidatedCalculusLanguageDef :=
  ⟨definition naming, definition_valid naming⟩

@[simp]
theorem length_carrierTypes {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    (naming : Naming request) :
    (carrierTypes naming).length = request.objects.length := by
  simp [carrierTypes]

/-- Positional naming plus stable carrier closure makes all earlier carrier
sort declarations an exact prefix after request append. -/
theorem indexed_carrierTypes_prefix_append {source : ValidatedLanguageDef}
    (first second : CarrierObjectClosure.Request source) :
    (carrierTypes (Naming.indexed first)).IsPrefix
      (carrierTypes (Naming.indexed (first.append second))) := by
  rw [List.prefix_iff_getElem?]
  intro index sourceBound
  have sourceObjectBound : index < first.objects.length := by
    simpa [carrierTypes] using sourceBound
  have targetObjectBound : index < (first.append second).objects.length :=
    lt_of_lt_of_le sourceObjectBound
      (first.objects_prefix_append second).length_le
  have targetBound :
      index < (carrierTypes (Naming.indexed (first.append second))).length := by
    simpa [carrierTypes] using targetObjectBound
  rw [List.getElem?_eq_getElem targetBound]
  simp [carrierTypes, Naming.indexed, Naming.indexedName]

/-- Default flat carrier calculus for a revision-bound sparse request. -/
def indexedDefinition {source : ValidatedLanguageDef}
    (request : CarrierObjectClosure.Request source) : CalculusLanguageDef :=
  definition (Naming.indexed request)

/-- Every row family of the default carrier calculus grows append-only. -/
theorem indexedDefinition_appendOnly {source : ValidatedLanguageDef}
    (first second : CarrierObjectClosure.Request source) :
    CalculusLanguageExtension.AppendOnlyCalculusRefinement
      (indexedDefinition first)
      (indexedDefinition (first.append second)) := by
  have typeRows := indexed_carrierTypes_prefix_append first second
  have carrierNames :
      ((carrierTypes (Naming.indexed first)).map (·.name)).IsPrefix
        ((carrierTypes
          (Naming.indexed (first.append second))).map (·.name)) :=
    List.IsPrefix.map (·.name) typeRows
  have universeRows :
      (CarrierUniverseSignature.termsFor
        ((carrierTypes (Naming.indexed first)).map (·.name))).IsPrefix
      (CarrierUniverseSignature.termsFor
        ((carrierTypes
          (Naming.indexed (first.append second))).map (·.name))) :=
    List.IsPrefix.flatMap carrierNames (fun carrier =>
      [CarrierUniverseSignature.rule .star carrier,
        CarrierUniverseSignature.rule .box carrier])
  constructor
  · exact typeRows
  · simpa [indexedDefinition] using universeRows
  · simp [indexedDefinition]
  · simp [indexedDefinition]
  · simpa [indexedDefinition] using
      List.IsPrefix.map CarrierTypingLanguageDef.judgment carrierNames
  · simpa [indexedDefinition] using
      List.IsPrefix.map CarrierTypingLanguageDef.universeAxiom carrierNames
  · rfl

/-- Minimal executable suffix needed to extend one already compiled default
carrier calculus with a later request. -/
def indexedAppendExtension {source : ValidatedLanguageDef}
    (first second : CarrierObjectClosure.Request source) :
    CalculusLanguageExtension :=
  (indexedDefinition_appendOnly first second).residual

theorem indexedAppendExtension_apply {source : ValidatedLanguageDef}
    (first second : CarrierObjectClosure.Request source) :
    (indexedAppendExtension first second).apply (indexedDefinition first) =
      indexedDefinition (first.append second) :=
  (indexedDefinition_appendOnly first second).residual_apply

@[simp]
theorem length_universeCodes {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    (naming : Naming request) :
    (validated naming).1.toLanguageDef.terms.length =
      2 * request.objects.length := by
  change (CarrierUniverseSignature.terms
    (validatedCarrierSignature naming)).length = _
  rw [CarrierUniverseSignature.length_terms]
  simp [validatedCarrierSignature, carrierSignature, carrierTypes]

@[simp]
theorem length_typingJudgments {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    (naming : Naming request) :
    (validated naming).1.judgments.length = request.objects.length := by
  change (CarrierTypingLanguageDef.judgments
    (validatedCarrierSignature naming)).length = _
  rw [CarrierTypingLanguageDef.length_judgments]
  simp [validatedCarrierSignature, carrierSignature, carrierTypes]

@[simp]
theorem length_universeAxioms {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    (naming : Naming request) :
    (validated naming).1.rules.length = request.objects.length := by
  change (CarrierTypingLanguageDef.axioms
    (validatedCarrierSignature naming)).length = _
  rw [CarrierTypingLanguageDef.length_axioms]
  simp [validatedCarrierSignature, carrierSignature, carrierTypes]

/-- The generated name retains a unique proof-relevant carrier meaning. -/
theorem named_slot_unique {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    (naming : Naming request) (slot : request.Slot) :
    ∃! candidate : request.Slot,
      naming.name candidate = naming.name slot := by
  exact ⟨slot, rfl, fun candidate equality => naming.injective equality⟩

/-! ## Positive and negative controls -/

namespace Canary

private def carrierA : TypeDecl :=
  TypeDecl.plain "carrier-object-language-canary:A"

private def sourceLanguage : LanguageDef :=
  { name := "carrier-object-language-canary"
    types := [carrierA]
    terms := []
    equations := []
    rewrites := [] }

private theorem sourceLanguage_valid : sourceLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [sourceLanguage, LanguageDef.typeNames, carrierA, TypeDecl.plain]

private def source : ValidatedLanguageDef :=
  ⟨sourceLanguage, sourceLanguage_valid⟩

private def baseA : TypeExpr := .base carrierA.name
private def vectorA : TypeExpr := .collection .vec baseA
private def arrowToVector : TypeExpr := .arrow baseA vectorA

private def request : CarrierObjectClosure.Request source where
  roots := [arrowToVector]
  grounded := by
    intro object objectMembership
    simp only [List.mem_singleton] at objectMembership
    subst object
    intro name nameMembership
    simpa [arrowToVector, vectorA, baseA, TypeExpr.baseNames, source,
      sourceLanguage, LanguageDef.typeNames] using nameMembership

private def naming : Naming request := Naming.indexed request

/-- Three retained carrier objects generate three carrier sorts, six universe
codes, three typing judgments, and three universe axioms. -/
theorem sparse_generated_counts :
    (carrierTypes naming).length = 3 ∧
      (validated naming).1.toLanguageDef.terms.length = 6 ∧
      (validated naming).1.judgments.length = 3 ∧
      (validated naming).1.rules.length = 3 := by
  decide

/-- A constant two-slot naming is not admissible: it would erase the
difference between two carrier objects before any observation licensed it. -/
theorem constant_two_slot_name_not_injective :
    ¬ Function.Injective (fun _ : Fin 2 => "same-carrier") := by
  intro injective
  have inequality : (0 : Fin 2) ≠ 1 := by decide
  exact inequality (injective rfl)

end Canary

#print axioms Naming.indexedName_injective
#print axioms Naming.indexedNameAt_injective
#print axioms Naming.indexedName_appendSlot
#print axioms carrierTypeNames_nodup
#print axioms carrierSignature_valid
#print axioms definition_valid
#print axioms extension_append
#print axioms length_universeCodes
#print axioms indexed_carrierTypes_prefix_append
#print axioms indexedDefinition_appendOnly
#print axioms indexedAppendExtension_apply
#print axioms named_slot_unique
#print axioms Canary.sparse_generated_counts
#print axioms Canary.constant_two_slot_name_not_injective

end CarrierObjectLanguageDef

end Mettapedia.OSLF.Framework
