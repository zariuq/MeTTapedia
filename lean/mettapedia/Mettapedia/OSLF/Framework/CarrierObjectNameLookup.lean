import Mettapedia.OSLF.Framework.CarrierObjectLanguageDef

/-!
# Certified lookup of generated carrier names

Carrier-object compilation assigns compact names to positions in a finite,
duplicate-free inventory.  This module connects those names back to source
`TypeExpr` objects without turning absence into a plausible positional name.

The public lookup is partial: an object receives a name exactly when it is in
the request inventory.  For retained objects, the witness-bearing `slotOf`
map recovers the unique inventory slot.  Indexed names are stable under
append-only request growth because the inventory itself grows by prefix.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef

namespace CarrierObjectNameLookup

open CarrierObjectClosure
open CarrierObjectLanguageDef

/-- The unique inventory slot occupied by a retained carrier object. -/
def slotOf {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    {object : TypeExpr} (membership : object ∈ request.objects) :
    request.Slot :=
  ⟨request.objects.idxOf object,
    List.idxOf_lt_length_iff.mpr membership⟩

@[simp]
theorem slotOf_val {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    {object : TypeExpr} (membership : object ∈ request.objects) :
    (slotOf membership).val = request.objects.idxOf object :=
  rfl

/-- Decoding the selected slot recovers the retained source object. -/
@[simp]
theorem slotOf_expression {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    {object : TypeExpr} (membership : object ∈ request.objects) :
    (slotOf membership).expression = object := by
  simp [slotOf, CarrierObjectClosure.Request.Slot.expression]

/-- Name assigned to one retained object by an arbitrary injective slot
naming. -/
def nameOf {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    (naming : CarrierObjectLanguageDef.Naming request)
    {object : TypeExpr} (membership : object ∈ request.objects) : String :=
  naming.name (slotOf membership)

/-- Safe object-to-name lookup.  An object outside the compiled inventory is
reported as absent rather than being aliased to the next numerical slot. -/
def lookup? {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    (naming : CarrierObjectLanguageDef.Naming request)
    (object : TypeExpr) : Option String :=
  if membership : object ∈ request.objects then
    some (nameOf naming membership)
  else
    none

@[simp]
theorem lookup?_eq_some_of_mem {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    (naming : CarrierObjectLanguageDef.Naming request)
    {object : TypeExpr} (membership : object ∈ request.objects) :
    lookup? naming object = some (nameOf naming membership) := by
  simp [lookup?, membership]

@[simp]
theorem lookup?_eq_none_iff {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    (naming : CarrierObjectLanguageDef.Naming request)
    (object : TypeExpr) :
    lookup? naming object = none ↔ object ∉ request.objects := by
  simp [lookup?]

@[simp]
theorem lookup?_isSome_iff {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    (naming : CarrierObjectLanguageDef.Naming request)
    (object : TypeExpr) :
    (lookup? naming object).isSome = true ↔ object ∈ request.objects := by
  simp [lookup?]

/-- Injective slot naming makes retained object names injective. -/
theorem nameOf_injective {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    (naming : CarrierObjectLanguageDef.Naming request)
    {first second : TypeExpr}
    (firstMembership : first ∈ request.objects)
    (secondMembership : second ∈ request.objects)
    (names : nameOf naming firstMembership =
      nameOf naming secondMembership) :
    first = second := by
  have slots : slotOf firstMembership = slotOf secondMembership :=
    naming.injective names
  exact (List.idxOf_inj firstMembership).mp
    (congrArg Fin.val slots)

/-- Default safe lookup for compact indexed naming. -/
def indexed? {source : ValidatedLanguageDef}
    (request : CarrierObjectClosure.Request source)
    (object : TypeExpr) : Option String :=
  lookup? (CarrierObjectLanguageDef.Naming.indexed request) object

/-- Every retained object name is one of the generated carrier sort names. -/
theorem indexed_name_mem_typeNames {source : ValidatedLanguageDef}
    {request : CarrierObjectClosure.Request source}
    {object : TypeExpr} (membership : object ∈ request.objects) :
    nameOf (CarrierObjectLanguageDef.Naming.indexed request) membership ∈
      (CarrierObjectLanguageDef.carrierSignature
        (CarrierObjectLanguageDef.Naming.indexed request)).typeNames := by
  rw [CarrierObjectLanguageDef.carrierTypeNames]
  exact List.mem_ofFn.mpr ⟨slotOf membership, rfl⟩

/-- Prefix growth preserves the unique slot of every retained old object. -/
theorem slotOf_append {source : ValidatedLanguageDef}
    (first second : CarrierObjectClosure.Request source)
    {object : TypeExpr} (membership : object ∈ first.objects) :
    slotOf ((first.objects_prefix_append second).subset membership) =
      first.appendSlot second (slotOf membership) := by
  apply Fin.ext
  exact (first.objects_prefix_append second).idxOf_eq_of_mem membership |>.symm

/-- Indexed lookup is exactly stable under append-only request growth. -/
theorem indexed?_append_of_mem {source : ValidatedLanguageDef}
    (first second : CarrierObjectClosure.Request source)
    {object : TypeExpr} (membership : object ∈ first.objects) :
    indexed? (first.append second) object = indexed? first object := by
  let targetMembership : object ∈ (first.append second).objects :=
    (first.objects_prefix_append second).subset membership
  change
    lookup? (CarrierObjectLanguageDef.Naming.indexed (first.append second))
        object =
      lookup? (CarrierObjectLanguageDef.Naming.indexed first) object
  rw [lookup?_eq_some_of_mem _ targetMembership,
    lookup?_eq_some_of_mem _ membership]
  congr 1
  unfold nameOf
  rw [slotOf_append first second membership]
  exact CarrierObjectLanguageDef.Naming.indexedName_appendSlot
    first second (slotOf membership)

/-! ## Positive and negative controls -/

namespace Canary

private def carrierA : TypeDecl :=
  TypeDecl.plain "carrier-object-name-lookup:A"

private def sourceLanguage : LanguageDef :=
  { name := "carrier-object-name-lookup"
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

private def request : CarrierObjectClosure.Request source where
  roots := [baseA]
  grounded := by
    intro object objectMembership
    simp only [List.mem_singleton] at objectMembership
    subst object
    intro name nameMembership
    simpa [baseA, TypeExpr.baseNames, source, sourceLanguage,
      LanguageDef.typeNames] using nameMembership

/-- The retained carrier receives its exact slot-zero name. -/
theorem retained_object_resolves :
    indexed? request baseA =
      some (CarrierObjectLanguageDef.Naming.indexedNameAt 0) := by
  decide

/-- A foreign carrier remains explicitly unresolved; it cannot borrow the
next append-only slot name. -/
theorem foreign_object_is_absent :
    indexed? request (.base "carrier-object-name-lookup:foreign") = none := by
  decide

end Canary

#print axioms slotOf_expression
#print axioms lookup?_eq_some_of_mem
#print axioms lookup?_eq_none_iff
#print axioms nameOf_injective
#print axioms indexed_name_mem_typeNames
#print axioms slotOf_append
#print axioms indexed?_append_of_mem
#print axioms Canary.retained_object_resolves
#print axioms Canary.foreign_object_is_absent

end CarrierObjectNameLookup

end Mettapedia.OSLF.Framework
