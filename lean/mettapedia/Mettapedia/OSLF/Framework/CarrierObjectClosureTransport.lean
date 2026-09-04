import Mettapedia.GSLT.LanguageDef.StructuralCoproduct
import Mettapedia.GSLT.LanguageDef.StructuralRenamingSemantics
import Mettapedia.OSLF.Framework.CarrierObjectClosure

/-!
# Structural transport of sparse carrier-object closure

Carrier-object generation is functorial only when a language map does not
identify distinct source sorts.  Under that exact hypothesis, structural
mapping commutes with hereditary constituent closure and stable duplicate
removal.  Hence a generated carrier slot transports without searching,
renumbering, or choosing a second representation.

The counterexample at the end records why ordinary structural morphisms are
not enough: a non-injective sort action can merge two requested carriers and
change the generated inventory cardinality.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef

namespace CarrierObjectClosure

/-- Structural type mapping commutes with hereditary carrier decomposition. -/
theorem constituents_mapTypeExpr (symbols : LanguageDefSymbolMap)
    (object : TypeExpr) :
    constituents (mapTypeExpr symbols object) =
      (constituents object).map (mapTypeExpr symbols) := by
  induction object with
  | base name => rfl
  | arrow domain codomain domainHypothesis codomainHypothesis =>
      simp [constituents, mapTypeExpr, domainHypothesis, codomainHypothesis,
        List.map_append]
  | multiBinder body inductionHypothesis =>
      simp [constituents, mapTypeExpr, inductionHypothesis]
  | collection collectionType element inductionHypothesis =>
      simp [constituents, mapTypeExpr, inductionHypothesis]

/-- Stable duplicate removal commutes with an injective map.  This lemma is
independent of carrier syntax and records the exact order-sensitive algebra
used by sparse generators. -/
theorem eraseDups_map_of_injective
    {α β : Type _} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (function : α → β) (injective : Function.Injective function) :
    ∀ values : List α,
      (values.map function).eraseDups = values.eraseDups.map function
  | [] => rfl
  | head :: tail => by
      rw [List.map_cons, List.eraseDups_cons, List.eraseDups_cons,
        List.filter_map]
      have predicateEquality :
          ((fun value => !(value == function head)) ∘ function) =
            (fun value => !(value == head)) := by
        funext value
        simp [injective.eq_iff]
      rw [predicateEquality]
      congr 1
      exact eraseDups_map_of_injective function injective
        (tail.filter fun value => !(value == head))
termination_by values => values.length
decreasing_by
  have shorter := List.length_filter_le
    (fun value => !(value == head)) tail
  simp only [List.length_cons]
  omega

/-- Mapping every requested root commutes with flattening all hereditary
constituents. -/
theorem flatMap_constituents_map (symbols : LanguageDefSymbolMap) :
    ∀ roots : List TypeExpr,
      (roots.map (mapTypeExpr symbols)).flatMap constituents =
        (roots.flatMap constituents).map (mapTypeExpr symbols)
  | [] => rfl
  | root :: roots => by
      simp [constituents_mapTypeExpr, flatMap_constituents_map symbols roots,
        List.map_append]

/-- Every carrier retained by source closure remains retained after structural
mapping.  Injectivity is unnecessary for this one-way law: distinct source
carriers may coalesce, but no mapped constituent disappears. -/
theorem mem_close_mapTypeExpr (symbols : LanguageDefSymbolMap)
    {object : TypeExpr} {roots : List TypeExpr}
    (membership : object ∈ close roots) :
    mapTypeExpr symbols object ∈
      close (roots.map (mapTypeExpr symbols)) := by
  rw [mem_close_iff] at membership ⊢
  obtain ⟨root, rootMembership, objectMembership⟩ := membership
  refine ⟨mapTypeExpr symbols root, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨root, rootMembership, rfl⟩
  · rw [constituents_mapTypeExpr]
    exact List.mem_map.mpr ⟨object, objectMembership, rfl⟩

/-- Injective sort maps commute exactly with sparse hereditary closure,
including retained order. -/
theorem close_mapTypeExpr (symbols : LanguageDefSymbolMap)
    (sortInjective : Function.Injective symbols.sort)
    (roots : List TypeExpr) :
    close (roots.map (mapTypeExpr symbols)) =
      (close roots).map (mapTypeExpr symbols) := by
  unfold close
  rw [flatMap_constituents_map]
  exact eraseDups_map_of_injective (mapTypeExpr symbols)
    (StructuralRenamingSemantics.mapTypeExpr_injective symbols sortInjective) _

/-- A structural language morphism maps every authored source sort to an
authored target sort. -/
theorem mapsTypeName
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    {name : String} (membership : name ∈ source.language.typeNames) :
    morphism.symbols.sort name ∈ target.language.typeNames := by
  obtain ⟨declaration, declarationMembership, declarationName⟩ :=
    List.mem_map.mp membership
  have mappedMembership :=
    morphism.mapsTypes declaration declarationMembership
  apply List.mem_map.mpr
  refine ⟨mapTypeDecl morphism.symbols declaration, mappedMembership, ?_⟩
  simpa [mapTypeDecl] using congrArg morphism.symbols.sort declarationName

/-- Source grounding transports along every structural language morphism. -/
theorem GroundedIn.map
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    {object : TypeExpr} (grounded : GroundedIn source object) :
    GroundedIn target (mapTypeExpr morphism.symbols object) := by
  intro mappedName mappedMembership
  rw [StructuralCoproduct.mapTypeExpr_baseNames] at mappedMembership
  obtain ⟨name, nameMembership, rfl⟩ := List.mem_map.mp mappedMembership
  exact mapsTypeName morphism (grounded name nameMembership)

namespace Request

/-- Map a sparse carrier request along a structural source-language map. -/
def map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (request : Request source) : Request target where
  roots := request.roots.map (mapTypeExpr morphism.symbols)
  grounded := by
    intro mappedObject mappedMembership
    obtain ⟨object, objectMembership, rfl⟩ :=
      List.mem_map.mp mappedMembership
    exact (request.grounded object objectMembership).map morphism

@[simp] theorem map_roots
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (request : Request source) :
    (request.map morphism).roots =
      request.roots.map (mapTypeExpr morphism.symbols) :=
  rfl

@[simp] theorem map_id
    (source : ValidatedLanguageDef) (request : Request source) :
    request.map (StructuralMorphism.id source) = request := by
  apply Request.ext
  change request.roots.map (mapTypeExpr LanguageDefSymbolMap.id) = request.roots
  induction request.roots with
  | nil => rfl
  | cons root roots inductionHypothesis =>
      simp [mapTypeExpr_id, inductionHypothesis]

theorem map_comp
    {first second third : ValidatedLanguageDef}
    (earlier : StructuralMorphism first second)
    (later : StructuralMorphism second third)
    (request : Request first) :
    request.map (StructuralMorphism.comp earlier later) =
      (request.map earlier).map later := by
  apply Request.ext
  change request.roots.map
      (mapTypeExpr (earlier.symbols.comp later.symbols)) =
    (request.roots.map (mapTypeExpr earlier.symbols)).map
      (mapTypeExpr later.symbols)
  rw [List.map_map]
  apply List.map_congr_left
  intro object _
  exact mapTypeExpr_comp earlier.symbols later.symbols object

/-- Under sort injectivity, the mapped request has exactly the pointwise
mapped carrier inventory. -/
theorem objects_map
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (request : Request source) :
    (request.map morphism).objects =
      request.objects.map (mapTypeExpr morphism.symbols) := by
  exact close_mapTypeExpr morphism.symbols sortInjective request.roots

/-- Numerical carrier slots transport directly when closure cardinality is
preserved. -/
def mapSlot
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    {request : Request source} (slot : Slot request) :
    Slot (request.map morphism) :=
  ⟨slot.val, by
    rw [objects_map morphism sortInjective request, List.length_map]
    exact slot.isLt⟩

@[simp] theorem mapSlot_val
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    {request : Request source} (slot : Slot request) :
    (mapSlot morphism sortInjective slot).val = slot.val :=
  rfl

/-- Slot transport decodes to structural type transport. -/
theorem mapSlot_expression
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    {request : Request source} (slot : Slot request) :
    (mapSlot morphism sortInjective slot).expression =
      mapTypeExpr morphism.symbols slot.expression := by
  simp [Slot.expression, mapSlot,
    objects_map morphism sortInjective request]

end Request

/-! ## Positive and negative controls -/

namespace TransportCanary

private def collapseSorts : LanguageDefSymbolMap where
  sort := fun _ => "carrier-closure-transport:merged"
  constructor := _root_.id
  relation := _root_.id
  equation := _root_.id
  rewrite := _root_.id

/-- Injective renaming preserves a compound carrier inventory exactly. -/
theorem injective_rename_preserves_inventory :
    close
        ([TypeExpr.base "carrier-closure-transport:A",
          TypeExpr.arrow (.base "carrier-closure-transport:A")
            (.base "carrier-closure-transport:B")].map
          (mapTypeExpr LanguageDefSymbolMap.id)) =
      close
        [TypeExpr.base "carrier-closure-transport:A",
          TypeExpr.arrow (.base "carrier-closure-transport:A")
            (.base "carrier-closure-transport:B")] := by
  rw [close_mapTypeExpr LanguageDefSymbolMap.id]
  · generalize close
        [TypeExpr.base "carrier-closure-transport:A",
          TypeExpr.arrow (.base "carrier-closure-transport:A")
            (.base "carrier-closure-transport:B")] = objects
    induction objects with
    | nil => rfl
    | cons head tail inductionHypothesis =>
        simp [mapTypeExpr_id, inductionHypothesis]
  · exact fun _ _ equality => equality

/-- A non-injective sort action can strictly shrink carrier closure, so the
sort-injectivity hypothesis cannot be discarded from generated transport. -/
theorem collapsing_sorts_changes_inventory :
    (close
      ([TypeExpr.base "carrier-closure-transport:A",
        TypeExpr.base "carrier-closure-transport:B"].map
        (mapTypeExpr collapseSorts))).length = 1 ∧
      (close
        [TypeExpr.base "carrier-closure-transport:A",
          TypeExpr.base "carrier-closure-transport:B"]).length = 2 := by
  decide

end TransportCanary

#print axioms constituents_mapTypeExpr
#print axioms eraseDups_map_of_injective
#print axioms mem_close_mapTypeExpr
#print axioms close_mapTypeExpr
#print axioms mapsTypeName
#print axioms GroundedIn.map
#print axioms Request.map_comp
#print axioms Request.objects_map
#print axioms Request.mapSlot_expression
#print axioms TransportCanary.injective_rename_preserves_inventory
#print axioms TransportCanary.collapsing_sorts_changes_inventory

end CarrierObjectClosure

end Mettapedia.OSLF.Framework
