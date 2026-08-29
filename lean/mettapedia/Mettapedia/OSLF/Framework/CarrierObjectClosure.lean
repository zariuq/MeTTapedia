import Mathlib.Data.List.Nodup
import Mettapedia.GSLT.LanguageDef.StructuralCategory

/-!
# Finite closure of requested carrier objects

The syntactic Stay--Wells construction is indexed by carrier *objects*, not
only by the base-sort declarations of a language.  In the MeTTaIL wire those
objects are represented by `TypeExpr`: base carriers, arrows, multibinder
objects, and collection objects.

This module computes the finite hereditary closure of an explicitly requested
list of carrier objects.  It deliberately does not assign wire names.  Naming
is a later compilation decision; the mathematical inventory is the duplicate-
free list of source-grounded `TypeExpr` values established here.

The closure is sparse: an unrequested object is absent.  It is nevertheless
hereditary: every constituent of a retained object is retained as well.  A
request also carries evidence that every referenced base sort belongs to the
source language, so generation cannot silently mint a foreign carrier.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef

namespace CarrierObjectClosure

/-- A carrier expression together with every carrier expression occurring
inside it.  The outer object is listed first; duplicate removal happens only
when several requested roots are combined. -/
def constituents : TypeExpr → List TypeExpr
  | object@(.base _) => [object]
  | object@(.arrow domain codomain) =>
      object :: (constituents domain ++ constituents codomain)
  | object@(.multiBinder body) => object :: constituents body
  | object@(.collection _ element) => object :: constituents element

@[simp]
theorem self_mem_constituents (object : TypeExpr) :
    object ∈ constituents object := by
  cases object <;> simp [constituents]

/-- Hereditary membership: once an inner carrier occurs in an outer carrier,
all constituents of the inner carrier already occur in the outer inventory. -/
theorem constituents_subset_of_mem {inner outer : TypeExpr}
    (membership : inner ∈ constituents outer) :
    ∀ object ∈ constituents inner, object ∈ constituents outer := by
  induction outer generalizing inner with
  | base name =>
      simp only [constituents, List.mem_singleton] at membership
      subst inner
      exact fun object objectMembership => objectMembership
  | arrow domain codomain domainIH codomainIH =>
      simp only [constituents, List.mem_cons, List.mem_append] at membership
      rcases membership with rfl | domainMembership | codomainMembership
      · exact fun object objectMembership => objectMembership
      · intro object objectMembership
        exact List.mem_cons_of_mem _
          (List.mem_append_left _
            (domainIH domainMembership object objectMembership))
      · intro object objectMembership
        exact List.mem_cons_of_mem _
          (List.mem_append_right _
            (codomainIH codomainMembership object objectMembership))
  | multiBinder body bodyIH =>
      simp only [constituents, List.mem_cons] at membership
      rcases membership with rfl | bodyMembership
      · exact fun object objectMembership => objectMembership
      · intro object objectMembership
        exact List.mem_cons_of_mem _
          (bodyIH bodyMembership object objectMembership)
  | collection collectionType element elementIH =>
      simp only [constituents, List.mem_cons] at membership
      rcases membership with rfl | elementMembership
      · exact fun object objectMembership => objectMembership
      · intro object objectMembership
        exact List.mem_cons_of_mem _
          (elementIH elementMembership object objectMembership)

/-- Base-name support agrees exactly with base objects in the hereditary
carrier inventory. -/
@[simp]
theorem base_mem_constituents_iff (name : String) (object : TypeExpr) :
    TypeExpr.base name ∈ constituents object ↔
      name ∈ object.baseNames := by
  induction object with
  | base objectName => simp [constituents, TypeExpr.baseNames]
  | arrow domain codomain domainIH codomainIH =>
      simp [constituents, TypeExpr.baseNames, domainIH, codomainIH]
  | multiBinder body bodyIH =>
      simp [constituents, TypeExpr.baseNames, bodyIH]
  | collection collectionType element elementIH =>
      simp [constituents, TypeExpr.baseNames, elementIH]

/-- Deterministic finite closure of a list of requested carrier objects. -/
def close (roots : List TypeExpr) : List TypeExpr :=
  (roots.flatMap constituents).eraseDups

private theorem eraseDups_prefix_append
    {α : Type _} [BEq α] [LawfulBEq α] :
    ∀ (first second : List α),
      first.eraseDups.IsPrefix (first ++ second).eraseDups
  | [], _ => List.nil_prefix
  | head :: tail, second => by
      rw [List.eraseDups_cons, List.cons_append, List.eraseDups_cons,
        List.filter_append]
      exact List.cons_prefix_cons.mpr
        ⟨rfl, eraseDups_prefix_append
          (tail.filter fun other => !other == head)
          (second.filter fun other => !other == head)⟩
termination_by first _ => first.length
decreasing_by
  have shorter :=
    List.length_filter_le (fun other => !other == head) tail
  simp only [List.length_cons]
  omega

/-- Appending carrier roots is an append-only operation on the compiled
inventory.  Stable first-occurrence duplicate removal cannot renumber any
carrier already compiled from the earlier roots. -/
theorem close_append_prefix (first second : List TypeExpr) :
    (close first).IsPrefix (close (first ++ second)) := by
  unfold close
  rw [List.flatMap_append]
  exact eraseDups_prefix_append _ _

private theorem eraseDups_nodup {α : Type _} [BEq α] [LawfulBEq α] :
    ∀ values : List α, values.eraseDups.Nodup
  | [] => by simp
  | value :: values => by
      rw [List.eraseDups_cons]
      refine List.nodup_cons.mpr
        ⟨?_, eraseDups_nodup (values.filter fun other => !other == value)⟩
      intro member
      rw [List.mem_eraseDups, List.mem_filter] at member
      simp at member
  termination_by values => values.length
  decreasing_by
    have shorter := List.length_filter_le (fun other => !other == value) values
    simp only [List.length_cons]
    omega

@[simp]
theorem mem_close_iff {object : TypeExpr} {roots : List TypeExpr} :
    object ∈ close roots ↔
      ∃ root ∈ roots, object ∈ constituents root := by
  simp [close]

theorem close_nodup (roots : List TypeExpr) : (close roots).Nodup := by
  exact eraseDups_nodup _

/-- Every explicitly requested root survives closure. -/
theorem root_mem_close {root : TypeExpr} {roots : List TypeExpr}
    (membership : root ∈ roots) : root ∈ close roots := by
  rw [mem_close_iff]
  exact ⟨root, membership, self_mem_constituents root⟩

/-- The computed list is closed under carrier constituents. -/
theorem close_closed_under_constituents {object : TypeExpr}
    {roots : List TypeExpr} (membership : object ∈ close roots) :
    ∀ constituent ∈ constituents object, constituent ∈ close roots := by
  rw [mem_close_iff] at membership
  obtain ⟨root, rootMembership, objectMembership⟩ := membership
  intro constituent constituentMembership
  rw [mem_close_iff]
  exact ⟨root, rootMembership,
    constituents_subset_of_mem objectMembership constituent
      constituentMembership⟩

/-- A carrier expression is grounded in a source when every base name it
mentions is an authored source sort. -/
def GroundedIn (source : ValidatedLanguageDef) (object : TypeExpr) : Prop :=
  ∀ name ∈ object.baseNames, name ∈ source.language.typeNames

/-- Sparse request for carrier objects.  Repeated roots are permitted at the
request boundary and are removed by `objects`; source grounding is mandatory. -/
structure Request (source : ValidatedLanguageDef) where
  roots : List TypeExpr
  grounded : ∀ object ∈ roots, GroundedIn source object

namespace Request

@[ext]
theorem ext {source : ValidatedLanguageDef} {first second : Request source}
    (roots : first.roots = second.roots) : first = second := by
  cases first
  cases second
  cases roots
  rfl

/-- Empty carrier demand. -/
def empty (source : ValidatedLanguageDef) : Request source where
  roots := []
  grounded := by simp

/-- Ordered composition of carrier demands.  Grounding evidence composes
with the root lists and duplicate removal remains an internal compilation
detail of `objects`. -/
def append {source : ValidatedLanguageDef}
    (first second : Request source) : Request source where
  roots := first.roots ++ second.roots
  grounded := by
    intro object membership
    rw [List.mem_append] at membership
    rcases membership with firstMembership | secondMembership
    · exact first.grounded object firstMembership
    · exact second.grounded object secondMembership

@[simp]
theorem empty_roots (source : ValidatedLanguageDef) :
    (empty source).roots = [] :=
  rfl

@[simp]
theorem append_roots {source : ValidatedLanguageDef}
    (first second : Request source) :
    (first.append second).roots = first.roots ++ second.roots :=
  rfl

theorem empty_append {source : ValidatedLanguageDef}
    (request : Request source) : (empty source).append request = request := by
  apply Request.ext
  simp

theorem append_empty {source : ValidatedLanguageDef}
    (request : Request source) : request.append (empty source) = request := by
  apply Request.ext
  simp

theorem append_assoc {source : ValidatedLanguageDef}
    (first second third : Request source) :
    (first.append second).append third = first.append (second.append third) := by
  apply Request.ext
  simp [List.append_assoc]

/-- Exact finite carrier-object inventory demanded by the request. -/
def objects {source : ValidatedLanguageDef} (request : Request source) :
    List TypeExpr :=
  close request.roots

/-- Extending a request preserves the complete earlier carrier inventory as
an exact prefix.  Hence positional carrier names remain stable under
append-only compilation. -/
theorem objects_prefix_append {source : ValidatedLanguageDef}
    (first second : Request source) :
    first.objects.IsPrefix (first.append second).objects := by
  exact close_append_prefix first.roots second.roots

theorem objects_nodup {source : ValidatedLanguageDef}
    (request : Request source) : request.objects.Nodup :=
  close_nodup request.roots

theorem root_mem_objects {source : ValidatedLanguageDef}
    (request : Request source) {root : TypeExpr}
    (membership : root ∈ request.roots) : root ∈ request.objects :=
  root_mem_close membership

theorem objects_closed_under_constituents {source : ValidatedLanguageDef}
    (request : Request source) {object : TypeExpr}
    (membership : object ∈ request.objects) :
    ∀ constituent ∈ constituents object,
      constituent ∈ request.objects :=
  close_closed_under_constituents membership

/-- Closing a grounded request cannot introduce a foreign base carrier. -/
theorem object_grounded {source : ValidatedLanguageDef}
    (request : Request source) {object : TypeExpr}
    (membership : object ∈ request.objects) :
    GroundedIn source object := by
  change object ∈ close request.roots at membership
  rw [mem_close_iff] at membership
  obtain ⟨root, rootMembership, objectMembership⟩ := membership
  intro name nameMembership
  apply request.grounded root rootMembership name
  rw [← base_mem_constituents_iff]
  exact constituents_subset_of_mem objectMembership (.base name)
    ((base_mem_constituents_iff name object).2 nameMembership)

/-- A compiled carrier slot is a position in the duplicate-free inventory.
The slot retains occurrence-free object identity while avoiding any choice of
wire serialization. -/
abbrev Slot {source : ValidatedLanguageDef} (request : Request source) :=
  Fin request.objects.length

namespace Slot

/-- Carrier expression denoted by one inventory slot. -/
def expression {source : ValidatedLanguageDef} {request : Request source}
    (slot : Slot request) : TypeExpr :=
  request.objects.get slot

theorem expression_mem {source : ValidatedLanguageDef}
    {request : Request source} (slot : Slot request) :
    slot.expression ∈ request.objects :=
  List.get_mem request.objects slot

theorem expression_grounded {source : ValidatedLanguageDef}
    {request : Request source} (slot : Slot request) :
    GroundedIn source slot.expression :=
  request.object_grounded slot.expression_mem

/-- Duplicate removal makes slot-to-expression decoding injective. -/
theorem expression_injective {source : ValidatedLanguageDef}
    {request : Request source} :
    Function.Injective (expression (request := request)) :=
  request.objects_nodup.injective_get

end Slot

/-- Canonical inclusion of an earlier carrier slot into an append-only
request.  It preserves the numerical slot, hence every positional wire name
built from that slot. -/
def appendSlot {source : ValidatedLanguageDef}
    (first second : Request source) (slot : Slot first) :
    Slot (first.append second) :=
  ⟨slot.val, lt_of_lt_of_le slot.isLt
    (objects_prefix_append first second).length_le⟩

@[simp]
theorem appendSlot_val {source : ValidatedLanguageDef}
    (first second : Request source) (slot : Slot first) :
    (appendSlot first second slot).val = slot.val :=
  rfl

theorem appendSlot_expression {source : ValidatedLanguageDef}
    (first second : Request source) (slot : Slot first) :
    (appendSlot first second slot).expression = slot.expression := by
  change (first.append second).objects[slot.val]'
      (appendSlot first second slot).isLt =
    first.objects[slot.val]'slot.isLt
  exact ((objects_prefix_append first second).getElem slot.isLt).symm

theorem appendSlot_injective {source : ValidatedLanguageDef}
    (first second : Request source) :
    Function.Injective (appendSlot first second) := by
  intro left right equality
  apply Fin.ext
  exact congrArg
    (fun slot : Slot (first.append second) => slot.val) equality

/-- Every retained carrier expression has a unique compiled slot. -/
theorem exists_unique_slot {source : ValidatedLanguageDef}
    (request : Request source) {object : TypeExpr}
    (membership : object ∈ request.objects) :
    ∃! slot : Slot request, slot.expression = object := by
  obtain ⟨slot, slotEquality⟩ :=
    (List.mem_iff_get (l := request.objects)).mp membership
  refine ⟨slot, slotEquality, ?_⟩
  intro other otherEquality
  exact Slot.expression_injective (otherEquality.trans slotEquality.symm)

end Request

/-! ## Positive and negative controls -/

namespace Canary

private def carrierA : TypeDecl :=
  TypeDecl.plain "carrier-object-closure-canary:A"

private def sourceLanguage : LanguageDef :=
  { name := "carrier-object-closure-canary"
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

private def request : Request source where
  roots := [arrowToVector]
  grounded := by
    intro object objectMembership
    simp only [List.mem_singleton] at objectMembership
    subst object
    intro name nameMembership
    simpa [arrowToVector, vectorA, baseA, TypeExpr.baseNames, source,
      sourceLanguage, LanguageDef.typeNames] using nameMembership

private def baseRequest : Request source where
  roots := [baseA]
  grounded := by
    intro object objectMembership
    simp only [List.mem_singleton] at objectMembership
    subst object
    intro name nameMembership
    simpa [baseA, TypeExpr.baseNames, source, sourceLanguage,
      LanguageDef.typeNames] using nameMembership

/-- One requested arrow retains exactly itself, its base domain, and its
collection codomain.  The repeated base constituent is stored once. -/
theorem nested_request_has_three_objects : request.objects.length = 3 := by
  decide

/-- Appending a larger carrier demand retains the already compiled base
carrier in slot zero and appends only genuinely new objects. -/
theorem append_preserves_existing_slot :
    (baseRequest.append request).objects = [baseA, arrowToVector, vectorA] := by
  decide

/-- Authored request order remains observable: demand composition is not a
commutative merge that silently renumbers carrier slots. -/
theorem append_not_commutative :
    baseRequest.append request ≠ request.append baseRequest := by
  intro equality
  have rootEquality := congrArg Request.roots equality
  simp [Request.append, baseRequest, request, baseA, arrowToVector] at rootEquality

/-- The sparse closure contains the composite collection carrier needed by
the requested arrow. -/
theorem requested_arrow_contains_collection : vectorA ∈ request.objects := by
  decide

/-- The closure does not invent an unrelated collection shape. -/
theorem unrequested_set_absent :
    TypeExpr.collection .hashSet baseA ∉ request.objects := by
  decide

/-- A base carrier absent from the source cannot satisfy the request gate. -/
theorem foreign_base_not_grounded :
    ¬ GroundedIn source (.base "carrier-object-closure-canary:Foreign") := by
  intro grounded
  have membership := grounded "carrier-object-closure-canary:Foreign"
    (by simp [TypeExpr.baseNames])
  simp [source, sourceLanguage, LanguageDef.typeNames, carrierA,
    TypeDecl.plain] at membership

end Canary

#print axioms constituents_subset_of_mem
#print axioms base_mem_constituents_iff
#print axioms close_closed_under_constituents
#print axioms close_append_prefix
#print axioms Request.append_assoc
#print axioms Request.objects_prefix_append
#print axioms Request.appendSlot_expression
#print axioms Request.appendSlot_injective
#print axioms Request.object_grounded
#print axioms Request.exists_unique_slot
#print axioms Canary.nested_request_has_three_objects
#print axioms Canary.append_preserves_existing_slot
#print axioms Canary.append_not_commutative
#print axioms Canary.requested_arrow_contains_collection
#print axioms Canary.unrequested_set_absent
#print axioms Canary.foreign_base_not_grounded

end CarrierObjectClosure

end Mettapedia.OSLF.Framework
