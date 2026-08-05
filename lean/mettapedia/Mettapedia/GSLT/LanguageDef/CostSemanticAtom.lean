import Mettapedia.GSLT.LanguageDef.CostSemanticCarrier
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalKeyed

/-!
# Typed semantic atoms for hereditary Cost normalization

A static Cost frame contains two kinds of external parameters: retagged
source variables and proof-relevant foreign-region boundaries.  Their encoded
names record different origins, but those origins are not semantic ordering
keys.  This module separates:

* positional parameter occurrences and their provenance;
* typed normalized values, which determine semantic atoms; and
* the finite map from occurrences to atoms.

The distinction permits two differently sourced occurrences to share one atom
when their complete typed normalized values agree, without losing either
occurrence or its position.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.PatternCode
open Mettapedia.OSLF.MeTTaIL.ScopedPattern

/-- Proof-free identity of one normalized static-frame parameter.

Source and target fibers are both retained.  Equality is semantic only when
the type, reflective support, and normalized compact value all agree; encoded
source or boundary names are deliberately absent. -/
structure CostStaticAtomKey where
  sourceType : TypeExpr
  sourceSupport : List TypeExpr
  targetType : TypeExpr
  targetSupport : List TypeExpr
  normal : Pattern
deriving Repr, DecidableEq

namespace CostStaticAtomKey

/-- Equality of complete semantic keys is componentwise.  Keeping this
explicit avoids reducing proof-relevant environments merely to compare their
proof-free keys. -/
theorem ext_components {left right : CostStaticAtomKey}
    (sourceType : left.sourceType = right.sourceType)
    (sourceSupport : left.sourceSupport = right.sourceSupport)
    (targetType : left.targetType = right.targetType)
    (targetSupport : left.targetSupport = right.targetSupport)
    (normal : left.normal = right.normal) : left = right := by
  cases left
  cases right
  simp_all

/-- Collision-free code for a complete typed semantic atom key. -/
def code (key : CostStaticAtomKey) : Nat :=
  Nat.pair (typeExprCode key.sourceType)
    (Nat.pair (typeExprListCode key.sourceSupport)
      (Nat.pair (typeExprCode key.targetType)
        (Nat.pair (typeExprListCode key.targetSupport)
          (patternCode key.normal))))

/-- The executable atom code forgets neither fiber nor normalized value. -/
theorem code_injective : Function.Injective code := by
  intro left right equality
  simp only [code, Nat.pair_eq_pair] at equality
  cases left with
  | mk leftSourceType leftSourceSupport leftTargetType leftTargetSupport
      leftNormal =>
      cases right with
      | mk rightSourceType rightSourceSupport rightTargetType
          rightTargetSupport rightNormal =>
          simp only at equality
          have sourceTypeEquality : leftSourceType = rightSourceType :=
            typeExprCode_injective equality.1
          have sourceSupportEquality :
              leftSourceSupport = rightSourceSupport :=
            typeExprListCode_injective equality.2.1
          have targetTypeEquality : leftTargetType = rightTargetType :=
            typeExprCode_injective equality.2.2.1
          have targetSupportEquality :
              leftTargetSupport = rightTargetSupport :=
            typeExprListCode_injective equality.2.2.2.1
          have normalEquality : leftNormal = rightNormal :=
            patternCode_injective equality.2.2.2.2
          cases sourceTypeEquality
          cases sourceSupportEquality
          cases targetTypeEquality
          cases targetSupportEquality
          cases normalEquality
          rfl

/-- Canonical executable order of semantic atom values. -/
@[reducible] def linearOrder : LinearOrder CostStaticAtomKey :=
  LinearOrder.lift' code code_injective

end CostStaticAtomKey

/-- A semantic atom key together with the target-fiber evidence required to
restore its normalized value. -/
structure TypedCostStaticAtom (source : CIGSLT) (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext) where
  key : CostStaticAtomKey
  normalTyped : WellSorted.HasType source.costWholeLanguage targetFree
    key.targetSupport key.normal key.targetType
  normalCanonicalBinderMetadata :
    key.normal.hasCanonicalBinderMetadata = true
  normalObject : WellSorted.isObjectPattern key.normal = true
  normalReflectiveScopeSafe :
    WellSorted.ReflectiveScopeSafeAt source.costWholeLanguage
      key.targetSupport.length key.normal

namespace TypedCostStaticAtom

/-- Proof irrelevance leaves the explicit semantic key as the complete
identity of a typed atom. -/
@[ext]
theorem ext {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {left right : TypedCostStaticAtom source color targetFree}
    (keyEquality : left.key = right.key) : left = right := by
  cases left
  cases right
  cases keyEquality
  rfl

/-- Equality of typed atoms is decidable from their proof-free keys.  The
typing and scope fields carry evidence but cannot split one semantic atom
into multiple executable classes. -/
instance {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} :
    DecidableEq (TypedCostStaticAtom source color targetFree) :=
  fun left right =>
    if keyEquality : left.key = right.key then
      isTrue (TypedCostStaticAtom.ext keyEquality)
    else
      isFalse fun atomEquality => keyEquality (congrArg (·.key) atomEquality)

/-- Package a recursively normalized foreign boundary value as a semantic
atom.  Stable source-fiber data comes from the boundary; current target data
comes from the child value. -/
def ofBoundaryValue {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (boundary : TypedCostRegionBoundary source color targetFree)
    (value : WellSorted.OpenPattern source.costWholeLanguage targetFree
      boundary.boundary.targetSupport boundary.boundary.targetType) :
    TypedCostStaticAtom source color targetFree where
  key :=
    { sourceType := boundary.boundary.type
      sourceSupport := boundary.boundary.support
      targetType := boundary.boundary.targetType
      targetSupport := boundary.boundary.targetSupport
      normal := value.1 }
  normalTyped := value.2.1
  normalCanonicalBinderMetadata := value.2.2.1
  normalObject := value.2.2.2.1
  normalReflectiveScopeSafe := value.2.2.2.2

/-- Package a retagged source free variable as its generated target value.
The decoding witness records that the target type really is the selected
static image of the source type. -/
def ofSourceFVar {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (name : String) (sourceType targetType : TypeExpr)
    (targetLookup : targetFree name = some targetType)
    (_decodedType :
      decodeCostStaticTypeExpr source color targetType = some sourceType) :
    TypedCostStaticAtom source color targetFree where
  key :=
    { sourceType := sourceType
      sourceSupport := []
      targetType := targetType
      targetSupport := []
      normal := .fvar name }
  normalTyped := .fvar targetLookup
  normalCanonicalBinderMetadata := by
    simp [Pattern.hasCanonicalBinderMetadata]
  normalObject := by simp [WellSorted.isObjectPattern]
  normalReflectiveScopeSafe := by
    intro presentation membership
    simp [binderSafeAt]

end TypedCostStaticAtom

namespace TypedCostRegionBoundaryTable

/-- Source-fiber support retained by semantic atom identity.

This is deliberately distinct from `sourceSupport`, which is the target-side
support presented to the authored canonical section.  Both projections are
derived from the same finite proof-relevant table; a continuation-retyped
boundary may make them unequal. -/
def atomSourceSupport {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences) :
    ContextSupport.Support := fun name =>
  match decodeCostRegionSourceVariableName name with
  | some _ => []
  | none =>
      match table.resolve name with
      | some typedBoundary => typedBoundary.boundary.support
      | none => []

/-- Retagged authored variables originate outside every local binder suffix. -/
@[simp]
theorem atomSourceSupport_sourceVariable {source : CIGSLT}
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (name : String) :
    table.atomSourceSupport (costRegionSourceVariableName name) = [] := by
  simp [atomSourceSupport, decodeCostRegionSourceVariableName_encode]

/-- A proof-relevant boundary contributes its decoded authored support, not
the independently certified target support used during restoration. -/
@[simp]
theorem atomSourceSupport_boundaryVariable {source : CIGSLT}
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (boundary : TypedCostRegionBoundary source color targetFree)
    (membership : boundary ∈ table.entries) :
    table.atomSourceSupport
        (costRegionBoundaryVariableName boundary.boundary) =
      boundary.boundary.support := by
  simp [atomSourceSupport, decodeCostRegionSourceVariableName_boundary,
    table.resolve_of_mem_entries boundary membership]

end TypedCostRegionBoundaryTable

/-- One positional free-variable occurrence in a compact frame.  The zipper,
not merely the variable name, retains duplication and exact position. -/
structure CostStaticFVarOccurrence (root : Pattern) where
  name : String
  context : OneHoleContext
  selected : Selects (.fvar name) context root

namespace CostStaticFVarOccurrence

/-- Proof irrelevance makes a positional free-variable occurrence completely
determined by its name and zipper. -/
@[ext]
theorem ext {root : Pattern} {left right : CostStaticFVarOccurrence root}
    (nameEquality : left.name = right.name)
    (contextEquality : left.context = right.context) : left = right := by
  cases left
  cases right
  cases nameEquality
  cases contextEquality
  rfl

/-- Positional occurrence equality is decidable from its proof-free name and
zipper; the `Selects` witness is proof-irrelevant. -/
instance {root : Pattern} : DecidableEq (CostStaticFVarOccurrence root) :=
  fun left right =>
    if nameEquality : left.name = right.name then
      if contextEquality : left.context = right.context then
        isTrue (CostStaticFVarOccurrence.ext nameEquality contextEquality)
      else
        isFalse fun occurrenceEquality =>
          contextEquality (congrArg (·.context) occurrenceEquality)
    else
      isFalse fun occurrenceEquality =>
        nameEquality (congrArg (·.name) occurrenceEquality)

/-- A structurally selected free-variable occurrence contributes its name to
the ordinary free-variable traversal. -/
theorem name_mem_freeFvarNames {root : Pattern}
    (occurrence : CostStaticFVarOccurrence root) :
    occurrence.name ∈ root.freeFvarNames := by
  cases occurrence with
  | mk name context selected =>
      induction selected <;>
        simp_all [Pattern.freeFvarNames, List.mem_flatMap]

private theorem object_of_mem_objectList {patterns : List Pattern}
    {pattern : Pattern} (membership : pattern ∈ patterns)
    (objects : WellSorted.isObjectPatternList patterns = true) :
    WellSorted.isObjectPattern pattern = true := by
  induction patterns with
  | nil => simp at membership
  | cons head tail inductionHypothesis =>
      simp only [WellSorted.isObjectPatternList, Bool.and_eq_true] at objects
      simp only [List.mem_cons] at membership
      rcases membership with rfl | inTail
      · exact objects.1
      · exact inductionHypothesis inTail objects.2

/-- Every free-variable name of an object pattern has a genuine structural
occurrence.  The object hypothesis is essential: an open collection tail is
a metavariable name but is not a `Pattern.fvar` occurrence. -/
theorem exists_of_mem_freeFvarNames_of_object {root : Pattern} {name : String}
    (membership : name ∈ root.freeFvarNames)
    (object : WellSorted.isObjectPattern root = true) :
    ∃ occurrence : CostStaticFVarOccurrence root,
      occurrence.name = name := by
  induction root using Pattern.inductionOn generalizing name with
  | hbvar index =>
      simp [Pattern.freeFvarNames] at membership
  | hfvar existing =>
      simp [Pattern.freeFvarNames] at membership
      subst existing
      exact ⟨⟨name, .hole, .here⟩, rfl⟩
  | happly constructor arguments inductionHypothesis =>
      simp only [Pattern.freeFvarNames, List.mem_flatMap] at membership
      obtain ⟨argument, argumentMembership, nameMembership⟩ := membership
      have argumentsObject :
          WellSorted.isObjectPatternList arguments = true := by
        simpa [WellSorted.isObjectPattern] using object
      have argumentObject : WellSorted.isObjectPattern argument = true :=
        object_of_mem_objectList argumentMembership argumentsObject
      obtain ⟨inner, innerName⟩ :=
        inductionHypothesis argument argumentMembership nameMembership
          argumentObject
      obtain ⟨before, after, argumentsEquality⟩ :=
        List.mem_iff_append.mp argumentMembership
      subst arguments
      have innerSelected :
          Selects (.fvar name) inner.context argument := by
        simpa [innerName] using inner.selected
      exact ⟨
        ⟨name, .apply constructor before inner.context after,
          .apply innerSelected⟩,
        rfl⟩
  | hlambda binder body inductionHypothesis =>
      have bodyObject : WellSorted.isObjectPattern body = true := by
        simpa [WellSorted.isObjectPattern] using object
      have bodyMembership : name ∈ body.freeFvarNames := by
        simpa [Pattern.freeFvarNames] using membership
      obtain ⟨inner, innerName⟩ :=
        inductionHypothesis bodyMembership bodyObject
      have innerSelected : Selects (.fvar name) inner.context body := by
        simpa [innerName] using inner.selected
      exact ⟨⟨name, .lambda binder inner.context, .lambda innerSelected⟩,
        rfl⟩
  | hmultiLambda arity binders body inductionHypothesis =>
      have bodyObject : WellSorted.isObjectPattern body = true := by
        simpa [WellSorted.isObjectPattern] using object
      have bodyMembership : name ∈ body.freeFvarNames := by
        simpa [Pattern.freeFvarNames] using membership
      obtain ⟨inner, innerName⟩ :=
        inductionHypothesis bodyMembership bodyObject
      have innerSelected : Selects (.fvar name) inner.context body := by
        simpa [innerName] using inner.selected
      exact ⟨
        ⟨name, .multiLambda arity binders inner.context,
          .multiLambda innerSelected⟩,
        rfl⟩
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [WellSorted.isObjectPattern] at object
  | hcollection collectionType elements rest inductionHypothesis =>
      have objectParts : rest = none ∧
          WellSorted.isObjectPatternList elements = true := by
        simpa [WellSorted.isObjectPattern] using object
      have restEquality := objectParts.1
      cases restEquality
      simp only [Pattern.freeFvarNames, Option.toList_none,
        List.append_nil, List.mem_flatMap] at membership
      obtain ⟨element, elementMembership, nameMembership⟩ := membership
      have elementObject : WellSorted.isObjectPattern element = true :=
        object_of_mem_objectList elementMembership objectParts.2
      obtain ⟨inner, innerName⟩ :=
        inductionHypothesis element elementMembership nameMembership
          elementObject
      obtain ⟨before, after, elementsEquality⟩ :=
        List.mem_iff_append.mp elementMembership
      subst elements
      have innerSelected : Selects (.fvar name) inner.context element := by
        simpa [innerName] using inner.selected
      exact ⟨
        ⟨name, .collection collectionType before inner.context after none,
          .collection innerSelected⟩,
        rfl⟩

/-- Enumerate every positional free-variable occurrence exactly through the
existing structural zipper compiler.  Equal names are enumerated once as a
search key, while `zippersAt` retains every distinct position. -/
def enumerate (root : Pattern) : List (CostStaticFVarOccurrence root) :=
  root.freeFvarNames.dedup.flatMap fun name =>
    (zippersAt (.fvar name) root).attach.map fun selected =>
      { name := name
        context := selected.1
        selected := zippersAt_sound selected.2 }

/-- The finite zipper inventory contains every proof-relevant free-variable
occurrence. -/
theorem mem_enumerate {root : Pattern}
    (occurrence : CostStaticFVarOccurrence root) :
    occurrence ∈ enumerate root := by
  rw [enumerate, List.mem_flatMap]
  refine ⟨occurrence.name, List.mem_dedup.mpr occurrence.name_mem_freeFvarNames,
    ?_⟩
  rw [List.mem_map]
  let selected : { context // context ∈ zippersAt (.fvar occurrence.name) root } :=
    ⟨occurrence.context, zippersAt_complete occurrence.selected⟩
  refine ⟨selected, List.mem_attach _ _, ?_⟩
  apply CostStaticFVarOccurrence.ext <;> rfl

end CostStaticFVarOccurrence

/-- A classified external-parameter occurrence in one static target frame.

The source case retains both decoding witnesses.  The boundary case retains
the exact finite value lookup, including the proof-relevant boundary selected
by the table. -/
inductive CostStaticParameterOccurrence
    (source : CIGSLT) (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext)
    {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree table)
    (root : Pattern) : Type where
  | sourceFVar
      {sourceName : String} {sourceType targetType : TypeExpr}
      (occurrence : CostStaticFVarOccurrence root)
      (decodesName : decodeCostRegionSourceVariableName occurrence.name =
        some sourceName)
      (targetLookup : targetFree sourceName = some targetType)
      (decodesType : decodeCostStaticTypeExpr source color targetType =
        some sourceType) :
      CostStaticParameterOccurrence source color targetFree table values root
  | boundary
      (occurrence : CostStaticFVarOccurrence root)
      (notSource : decodeCostRegionSourceVariableName occurrence.name = none)
      (resolved : TypedCostRegionBoundaryTable.Values.Resolved
        source color targetFree)
      (resolves : values.resolve table occurrence.name = some resolved) :
      CostStaticParameterOccurrence source color targetFree table values root

namespace CostStaticParameterOccurrence

/-- Forget the source/boundary classification while retaining the exact
positional zipper occurrence. -/
def fvarOccurrence {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern} :
    CostStaticParameterOccurrence source color targetFree table values root →
      CostStaticFVarOccurrence root
  | .sourceFVar occurrence _ _ _ => occurrence
  | .boundary occurrence _ _ _ => occurrence

/-- Classify one finite zipper occurrence through the two reserved static
parameter namespaces.  Failure is explicit when the surrounding region
certificate has not established either a decoded source variable or a typed
foreign-boundary value. -/
def classify? {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree table)
    {root : Pattern} (occurrence : CostStaticFVarOccurrence root) :
    Option
      (CostStaticParameterOccurrence source color targetFree table values root) :=
  match decodedName : decodeCostRegionSourceVariableName occurrence.name with
  | some sourceName =>
      match targetLookup : targetFree sourceName with
      | none => none
      | some targetType =>
          match decodedType : decodeCostStaticTypeExpr source color targetType with
          | none => none
          | some sourceType =>
              some (.sourceFVar (sourceType := sourceType) occurrence
                decodedName targetLookup decodedType)
  | none =>
      match resolved : values.resolve table occurrence.name with
      | none => none
      | some value => some (.boundary occurrence decodedName value resolved)

/-- Classification never changes, duplicates, or invents a positional
occurrence. -/
theorem fvarOccurrence_of_classify?_eq_some
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree table)
    {root : Pattern} (occurrence : CostStaticFVarOccurrence root)
    {classified : CostStaticParameterOccurrence source color targetFree table
      values root}
    (classification : classify? table values occurrence = some classified) :
    classified.fvarOccurrence = occurrence := by
  unfold classify? at classification
  split at classification
  · split at classification
    · cases classification
    · split at classification
      · cases classification
      · cases classification
        rfl
  · split at classification
    · cases classification
    · cases classification
      rfl

/-- A completely decoded source-variable occurrence is accepted by the
classifier and retains its zipper. -/
theorem classify?_sourceFVar_isSome
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree table)
    {root : Pattern} (occurrence : CostStaticFVarOccurrence root)
    {sourceName : String} {sourceType targetType : TypeExpr}
    (decodedName : decodeCostRegionSourceVariableName occurrence.name =
      some sourceName)
    (targetLookup : targetFree sourceName = some targetType)
    (decodedType : decodeCostStaticTypeExpr source color targetType =
      some sourceType) :
    (classify? table values occurrence).isSome = true := by
  unfold classify?
  split <;> try simp_all
  all_goals split <;> try simp_all
  all_goals split <;> simp_all

/-- A non-source name resolved by the finite typed boundary vector is accepted
as exactly that boundary occurrence. -/
theorem classify?_boundary_isSome
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree table)
    {root : Pattern} (occurrence : CostStaticFVarOccurrence root)
    (notSource : decodeCostRegionSourceVariableName occurrence.name = none)
    (resolved : TypedCostRegionBoundaryTable.Values.Resolved
      source color targetFree)
    (resolution : values.resolve table occurrence.name = some resolved) :
    (classify? table values occurrence).isSome = true := by
  unfold classify?
  split <;> try simp_all
  all_goals split <;> simp_all

/-- Typing of an object skeleton makes the two-way classifier total on every
structurally selected free-variable occurrence.  The only authority is the
finite table's source context: unfolding its successful lookup yields either
a decoded authored variable or an actual boundary entry with an aligned
replacement value. -/
theorem classify?_isSome_of_typed
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree table)
    {root : Pattern} {bound : List TypeExpr} {type : TypeExpr}
    (typed : WellSorted.HasType
      source.theory.presentation.presentation.language
      table.sourceFreeContext bound root type)
    (object : WellSorted.isObjectPattern root = true)
    (occurrence : CostStaticFVarOccurrence root) :
    (classify? table values occurrence).isSome = true := by
  obtain ⟨freeType, lookup⟩ :=
    typed.freeType_of_mem_freeFvarNames_of_isObjectPattern object
      occurrence.name_mem_freeFvarNames
  cases decodedName : decodeCostRegionSourceVariableName occurrence.name with
  | some sourceName =>
      cases targetLookup : targetFree sourceName with
      | none =>
          simp [TypedCostRegionBoundaryTable.sourceFreeContext, decodedName,
            targetLookup] at lookup
      | some targetType =>
          cases decodedType : decodeCostStaticTypeExpr source color targetType with
          | none =>
              simp [TypedCostRegionBoundaryTable.sourceFreeContext, decodedName,
                targetLookup, decodedType] at lookup
          | some sourceType =>
              exact classify?_sourceFVar_isSome table values occurrence
                decodedName targetLookup decodedType
  | none =>
      cases tableResolution : table.resolve occurrence.name with
      | none =>
          simp [TypedCostRegionBoundaryTable.sourceFreeContext, decodedName,
            tableResolution] at lookup
      | some boundary =>
          have aligned := values.resolve_boundary table occurrence.name
          cases valueResolution : values.resolve table occurrence.name with
          | none => simp [valueResolution, tableResolution] at aligned
          | some resolved =>
              exact classify?_boundary_isSome table values occurrence
                decodedName resolved valueResolution

/-- Evaluate one positional occurrence to the complete typed semantic atom
that it denotes. -/
def atom {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern} :
    CostStaticParameterOccurrence source color targetFree table values root →
      TypedCostStaticAtom source color targetFree
  | .sourceFVar _ _ targetLookup decodesType =>
      TypedCostStaticAtom.ofSourceFVar _ _ _ targetLookup decodesType
  | .boundary _ _ resolved _ =>
      TypedCostStaticAtom.ofBoundaryValue resolved.1 resolved.2

/-- Classification is name-extensional: two occurrences bearing the same
reserved parameter name denote the same complete typed semantic atom.  The
zipper positions remain distinct; only their evaluated meanings coincide. -/
theorem atom_eq_of_name_eq
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    (left right : CostStaticParameterOccurrence source color targetFree table
      values root)
    (nameEquality : left.fvarOccurrence.name = right.fvarOccurrence.name) :
    left.atom = right.atom := by
  cases left with
  | sourceFVar leftOccurrence leftDecodedName leftLookup leftDecodedType =>
      cases right with
      | sourceFVar rightOccurrence rightDecodedName rightLookup
          rightDecodedType =>
          simp only [fvarOccurrence] at nameEquality
          have decodedNameEquality := congrArg
            decodeCostRegionSourceVariableName nameEquality
          rw [leftDecodedName, rightDecodedName] at decodedNameEquality
          have sourceNameEquality := Option.some.inj decodedNameEquality
          cases sourceNameEquality
          have targetTypeEquality : _ := Option.some.inj
            (leftLookup.symm.trans rightLookup)
          cases targetTypeEquality
          have sourceTypeEquality : _ := Option.some.inj
            (leftDecodedType.symm.trans rightDecodedType)
          cases sourceTypeEquality
          apply TypedCostStaticAtom.ext
          rfl
      | boundary rightOccurrence rightNotSource rightResolved rightResolution =>
          simp only [fvarOccurrence] at nameEquality
          have contradiction := congrArg decodeCostRegionSourceVariableName
            nameEquality
          rw [leftDecodedName, rightNotSource] at contradiction
          cases contradiction
  | boundary leftOccurrence leftNotSource leftResolved leftResolution =>
      cases right with
      | sourceFVar rightOccurrence rightDecodedName rightLookup
          rightDecodedType =>
          simp only [fvarOccurrence] at nameEquality
          have contradiction := congrArg decodeCostRegionSourceVariableName
            nameEquality
          rw [leftNotSource, rightDecodedName] at contradiction
          cases contradiction
      | boundary rightOccurrence rightNotSource rightResolved rightResolution =>
          simp only [fvarOccurrence] at nameEquality
          have resolutionEquality := congrArg (values.resolve table)
            nameEquality
          rw [leftResolution, rightResolution] at resolutionEquality
          have resolvedEquality := Option.some.inj resolutionEquality
          cases resolvedEquality
          apply TypedCostStaticAtom.ext
          rfl

/-- Evaluation records exactly the generated target support used by the
existing finite restoration action. -/
theorem atom_targetSupport_eq_restorationSupport
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    (parameter : CostStaticParameterOccurrence source color targetFree table
      values root) :
    parameter.atom.key.targetSupport =
      table.restorationSupport parameter.fvarOccurrence.name := by
  cases parameter with
  | sourceFVar occurrence decodedName targetLookup decodedType =>
      simp [atom, TypedCostStaticAtom.ofSourceFVar,
        TypedCostRegionBoundaryTable.restorationSupport, decodedName,
        fvarOccurrence]
  | boundary occurrence notSource resolved resolution =>
      have tableResolution : table.resolve occurrence.name = some resolved.1 := by
        have agrees := values.resolve_boundary table occurrence.name
        rw [resolution] at agrees
        simpa using agrees.symm
      simp [atom, TypedCostStaticAtom.ofBoundaryValue,
        TypedCostRegionBoundaryTable.restorationSupport, notSource,
        tableResolution, fvarOccurrence]

/-- Evaluation records exactly the normalized target value used by the
finite child-first replacement vector. -/
theorem atom_normal_eq_assignment
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    (parameter : CostStaticParameterOccurrence source color targetFree table
      values root) :
    parameter.atom.key.normal =
      values.assignment table parameter.fvarOccurrence.name := by
  cases parameter with
  | sourceFVar occurrence decodedName targetLookup decodedType =>
      simp [atom, TypedCostStaticAtom.ofSourceFVar,
        TypedCostRegionBoundaryTable.Values.assignment, decodedName,
        fvarOccurrence]
  | boundary occurrence notSource resolved resolution =>
      simp [atom, TypedCostStaticAtom.ofBoundaryValue,
        TypedCostRegionBoundaryTable.Values.assignment, notSource, resolution,
        fvarOccurrence]

/-- The atom target type is exactly the type assigned to its original rigid
parameter name by the mapped finite context. -/
theorem mappedFreeContext_eq_atom_targetType
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    (parameter : CostStaticParameterOccurrence source color targetFree table
      values root) :
    table.mappedFreeContext parameter.fvarOccurrence.name =
      some parameter.atom.key.targetType := by
  cases parameter with
  | sourceFVar occurrence decodedName targetLookup decodedType =>
      have encodedType :=
        mapTypeExpr_decodeCostStaticTypeExpr source color decodedType
      simp [TypedCostRegionBoundaryTable.mappedFreeContext, decodedName,
        targetLookup, decodedType, atom, TypedCostStaticAtom.ofSourceFVar,
        encodedType, fvarOccurrence]
  | boundary occurrence notSource resolved resolution =>
      have tableResolution : table.resolve occurrence.name = some resolved.1 := by
        have agrees := values.resolve_boundary table occurrence.name
        rw [resolution] at agrees
        simpa using agrees.symm
      simp [TypedCostRegionBoundaryTable.mappedFreeContext, notSource,
        tableResolution, atom, TypedCostStaticAtom.ofBoundaryValue,
        fvarOccurrence]

/-- The atom source type is exactly the type assigned to its original rigid
parameter name in the authored source context. -/
theorem sourceFreeContext_eq_atom_sourceType
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    (parameter : CostStaticParameterOccurrence source color targetFree table
      values root) :
    table.sourceFreeContext parameter.fvarOccurrence.name =
      some parameter.atom.key.sourceType := by
  cases parameter with
  | sourceFVar occurrence decodedName targetLookup decodedType =>
      simp [TypedCostRegionBoundaryTable.sourceFreeContext, decodedName,
        targetLookup, decodedType, atom, TypedCostStaticAtom.ofSourceFVar,
        fvarOccurrence]
  | boundary occurrence notSource resolved resolution =>
      have tableResolution : table.resolve occurrence.name = some resolved.1 := by
        have agrees := values.resolve_boundary table occurrence.name
        rw [resolution] at agrees
        simpa using agrees.symm
      simp [TypedCostRegionBoundaryTable.sourceFreeContext, notSource,
        tableResolution, atom, TypedCostStaticAtom.ofBoundaryValue,
        fvarOccurrence]

/-- Source-side canonicalization and target-side restoration use the same
generated binder suffix for every classified parameter occurrence. -/
theorem atom_targetSupport_eq_sourceSupport
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    (parameter : CostStaticParameterOccurrence source color targetFree table
      values root) :
    parameter.atom.key.targetSupport =
      table.sourceSupport parameter.fvarOccurrence.name := by
  rw [parameter.atom_targetSupport_eq_restorationSupport]
  rfl

/-- The semantic key's source support is the authored-fiber projection of
the same finite table.  It need not equal the target-side support used by the
canonicalizer and restoration action. -/
theorem atom_sourceSupport_eq_atomSourceSupport
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    (parameter : CostStaticParameterOccurrence source color targetFree table
      values root) :
    parameter.atom.key.sourceSupport =
      table.atomSourceSupport parameter.fvarOccurrence.name := by
  cases parameter with
  | sourceFVar occurrence decodedName targetLookup decodedType =>
      simp [atom, TypedCostStaticAtom.ofSourceFVar,
        TypedCostRegionBoundaryTable.atomSourceSupport, decodedName,
        fvarOccurrence]
  | boundary occurrence notSource resolved resolution =>
      have tableResolution : table.resolve occurrence.name = some resolved.1 := by
        have agrees := values.resolve_boundary table occurrence.name
        rw [resolution] at agrees
        simpa using agrees.symm
      simp [atom, TypedCostStaticAtom.ofBoundaryValue,
        TypedCostRegionBoundaryTable.atomSourceSupport, notSource,
        tableResolution, fvarOccurrence]

/-- Every parameter atom drawn from a coherent static boundary table carries
the selected Cost image of its authored source type. -/
theorem atom_targetType_eq_map_sourceType
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    (parameter : CostStaticParameterOccurrence source color targetFree table
      values root)
    (coherent : table.FiberCoherent) :
    mapTypeExpr (color.symbols source) parameter.atom.key.sourceType =
      parameter.atom.key.targetType := by
  cases parameter with
  | sourceFVar occurrence decodedName targetLookup decodedType =>
      simpa [atom, TypedCostStaticAtom.ofSourceFVar] using
        mapTypeExpr_decodeCostStaticTypeExpr source color decodedType
  | boundary occurrence notSource resolved resolution =>
      have tableResolution : table.resolve occurrence.name =
          some resolved.1 := by
        have agrees := values.resolve_boundary table occurrence.name
        rw [resolution] at agrees
        simpa using agrees.symm
      have membership : resolved.1 ∈ table.entries :=
        table.mem_entries_of_resolve_eq_some tableResolution
      simpa [atom, TypedCostStaticAtom.ofBoundaryValue] using
        coherent.typeMap resolved.1 membership

end CostStaticParameterOccurrence

/-- Explicit finite inventory of proof-relevant parameter occurrences.

Positions, rather than equality of proof objects, are the occurrence
identities.  Repeated occurrences therefore remain distinct even when their
semantic values later coalesce. -/
structure CostStaticParameterInventory
    (source : CIGSLT) (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext)
    {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree table)
    (root : Pattern) where
  entries : List
    (CostStaticParameterOccurrence source color targetFree table values root)
  positions : entries.map CostStaticParameterOccurrence.fvarOccurrence =
    CostStaticFVarOccurrence.enumerate root

namespace CostStaticParameterInventory

/-- Traverse a finite positional inventory through the fail-closed parameter
classifier.  No entry is silently discarded. -/
def classifyAll? {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree table)
    {root : Pattern} :
    List (CostStaticFVarOccurrence root) →
      Option (List
        (CostStaticParameterOccurrence source color targetFree table values root))
  | [] => some []
  | occurrence :: tail =>
      match CostStaticParameterOccurrence.classify? table values occurrence,
          classifyAll? table values tail with
      | some classified, some classifiedTail =>
          some (classified :: classifiedTail)
      | _, _ => none

/-- The fail-closed classifier preserves the exact positional occurrence
vector whenever it succeeds. -/
theorem classifyAll?_positions
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree table)
    {root : Pattern}
    {input : List (CostStaticFVarOccurrence root)}
    {output : List
      (CostStaticParameterOccurrence source color targetFree table values root)}
    (classified : classifyAll? table values input = some output) :
    output.map CostStaticParameterOccurrence.fvarOccurrence = input := by
  induction input generalizing output with
  | nil =>
      simp [classifyAll?] at classified
      subst output
      rfl
  | cons occurrence tail inductionHypothesis =>
      unfold classifyAll? at classified
      cases headResult : CostStaticParameterOccurrence.classify? table values
          occurrence with
      | none => simp [headResult] at classified
      | some head =>
          cases tailResult : classifyAll? table values tail with
          | none => simp [headResult, tailResult] at classified
          | some classifiedTail =>
              simp [headResult, tailResult] at classified
              subst output
              simp only [List.map_cons, List.cons.injEq]
              exact ⟨
                CostStaticParameterOccurrence.fvarOccurrence_of_classify?_eq_some
                  table values occurrence headResult,
                inductionHypothesis tailResult⟩

/-- If every positional occurrence is accepted, the finite traversal cannot
fail.  This isolates the later region-classification theorem as the sole
totality obligation. -/
theorem classifyAll?_isSome_of_forall
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree table)
    {root : Pattern}
    (inventory : List (CostStaticFVarOccurrence root))
    (accepted : ∀ occurrence ∈ inventory,
      (CostStaticParameterOccurrence.classify? table values occurrence).isSome =
        true) :
    (classifyAll? table values inventory).isSome = true := by
  induction inventory with
  | nil => rfl
  | cons occurrence tail inductionHypothesis =>
      have headAccepted := accepted occurrence (by simp)
      rw [Option.isSome_iff_exists] at headAccepted
      obtain ⟨classified, classifiedEquality⟩ := headAccepted
      have tailAccepted := inductionHypothesis fun other membership =>
        accepted other (by simp [membership])
      rw [Option.isSome_iff_exists] at tailAccepted
      obtain ⟨classifiedTail, tailEquality⟩ := tailAccepted
      simp [classifyAll?, classifiedEquality, tailEquality]

/-- Build the complete finite parameter inventory of a selected static frame.
The result is `none` precisely at an unclassified zipper occurrence; later
totality theorems discharge that possibility from region certification. -/
def build? {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree table)
    (root : Pattern) :
    Option (CostStaticParameterInventory source color targetFree table values
      root) :=
  match classified : classifyAll? table values
      (CostStaticFVarOccurrence.enumerate root) with
  | none => none
  | some entries => some
      ⟨entries, classifyAll?_positions (table := table) (values := values)
        classified⟩

/-- Pointwise classifier coverage is exactly the input needed to make the
finite environment builder succeed. -/
theorem build?_isSome_of_forall
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree table)
    (root : Pattern)
    (accepted : ∀ occurrence ∈ CostStaticFVarOccurrence.enumerate root,
      (CostStaticParameterOccurrence.classify? table values occurrence).isSome =
        true) :
    (build? table values root).isSome = true := by
  have total := classifyAll?_isSome_of_forall table values _ accepted
  rw [Option.isSome_iff_exists] at total
  obtain ⟨entries, classified⟩ := total
  unfold build?
  split
  · rename_i failed
    rw [failed] at classified
    cases classified
  · rfl

/-- Every well-typed object skeleton has a total executable finite parameter
inventory.  This is the bridge from declarative admission to the atom
environment; no additional namespace-coverage premise is exposed to callers. -/
theorem build?_isSome_of_typed
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree table)
    {root : Pattern} {bound : List TypeExpr} {type : TypeExpr}
    (typed : WellSorted.HasType
      source.theory.presentation.presentation.language
      table.sourceFreeContext bound root type)
    (object : WellSorted.isObjectPattern root = true) :
    (build? table values root).isSome = true := by
  apply build?_isSome_of_forall
  intro occurrence _membership
  exact CostStaticParameterOccurrence.classify?_isSome_of_typed table values
    typed object occurrence

/-- Positional identity of one parameter occurrence. -/
abbrev Occurrence {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    (inventory : CostStaticParameterInventory source color targetFree table
      values root) :=
  Fin inventory.entries.length

/-- Recover the proof-relevant occurrence stored at one finite position. -/
def occurrenceAt {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    (inventory : CostStaticParameterInventory source color targetFree table
      values root) (position : inventory.Occurrence) :
    CostStaticParameterOccurrence source color targetFree table values root :=
  inventory.entries.get position

/-- Compute the finite inventory position of one structural zipper
occurrence.  Completeness of `positions` makes the lookup total; repeated
variable names remain distinguishable because the zipper is part of the
key. -/
def positionOf {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    (inventory : CostStaticParameterInventory source color targetFree table
      values root) (occurrence : CostStaticFVarOccurrence root) :
    inventory.Occurrence :=
  ⟨List.idxOf occurrence
      (inventory.entries.map CostStaticParameterOccurrence.fvarOccurrence),
    by
      have membership : occurrence ∈
          inventory.entries.map
            CostStaticParameterOccurrence.fvarOccurrence := by
        rw [inventory.positions]
        exact occurrence.mem_enumerate
      simpa using List.idxOf_lt_length_of_mem membership⟩

/-- Looking up a structural occurrence by its computed position returns that
same occurrence. -/
@[simp]
theorem fvarOccurrence_occurrenceAt_positionOf
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    (inventory : CostStaticParameterInventory source color targetFree table
      values root) (occurrence : CostStaticFVarOccurrence root) :
    (inventory.occurrenceAt (inventory.positionOf occurrence)).fvarOccurrence =
      occurrence := by
  have membership : occurrence ∈
      inventory.entries.map
        CostStaticParameterOccurrence.fvarOccurrence := by
    rw [inventory.positions]
    exact occurrence.mem_enumerate
  have selected :=
    List.idxOf_get (l := inventory.entries.map
      CostStaticParameterOccurrence.fvarOccurrence)
      (List.idxOf_lt_length_of_mem membership)
  rw [List.get_eq_getElem, List.getElem_map] at selected
  exact selected

/-- Find the first positional occurrence bearing a given parameter name.
The result remains a finite position in the proof-relevant inventory. -/
def positionOfName? {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    (inventory : CostStaticParameterInventory source color targetFree table
      values root) (name : String) : Option inventory.Occurrence :=
  inventory.entries.findFinIdx? fun entry =>
    entry.fvarOccurrence.name == name

/-- Every structural occurrence makes the name-indexed lookup succeed. -/
theorem positionOfName?_isSome_of_occurrence
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    (inventory : CostStaticParameterInventory source color targetFree table
      values root) (occurrence : CostStaticFVarOccurrence root) :
    (inventory.positionOfName? occurrence.name).isSome = true := by
  rw [Option.isSome_iff_ne_none]
  intro absent
  have rejects := List.findFinIdx?_eq_none_iff.mp absent
  have rejected := rejects
    (inventory.occurrenceAt (inventory.positionOf occurrence))
    (List.get_mem inventory.entries (inventory.positionOf occurrence))
  apply rejected
  simp

/-- Evaluate a positional occurrence without forgetting its position. -/
def occurrenceAtom {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    (inventory : CostStaticParameterInventory source color targetFree table
      values root) (position : inventory.Occurrence) :
    TypedCostStaticAtom source color targetFree :=
  (inventory.occurrenceAt position).atom

/-- Any name-selected representative has the same semantic value as every
other occurrence of that name. -/
theorem occurrenceAtom_eq_of_positionOfName?_eq_some
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    (inventory : CostStaticParameterInventory source color targetFree table
      values root) (occurrence : CostStaticFVarOccurrence root)
    (position : inventory.Occurrence)
    (selected : inventory.positionOfName? occurrence.name = some position) :
    inventory.occurrenceAtom position =
      inventory.occurrenceAtom (inventory.positionOf occurrence) := by
  have found := (List.findFinIdx?_eq_some_iff.mp selected).1
  have leftName :
      (inventory.occurrenceAt position).fvarOccurrence.name =
        occurrence.name := by
    simpa [positionOfName?, occurrenceAt] using found
  have rightName :
      (inventory.occurrenceAt
        (inventory.positionOf occurrence)).fvarOccurrence.name =
        occurrence.name := by
    exact congrArg CostStaticFVarOccurrence.name
      (inventory.fvarOccurrence_occurrenceAt_positionOf occurrence)
  exact CostStaticParameterOccurrence.atom_eq_of_name_eq _ _
    (leftName.trans rightName.symm)

/-- One representative for each complete typed semantic value occurring in
the inventory.  Deduplication never acts on occurrence identities. -/
def semanticAtoms {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    (inventory : CostStaticParameterInventory source color targetFree table
      values root) : List (TypedCostStaticAtom source color targetFree) :=
  (inventory.entries.map CostStaticParameterOccurrence.atom).dedup

/-- Every positional value survives in the finite semantic quotient. -/
theorem occurrenceAtom_mem_semanticAtoms
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    (inventory : CostStaticParameterInventory source color targetFree table
      values root) (position : inventory.Occurrence) :
    inventory.occurrenceAtom position ∈ inventory.semanticAtoms := by
  rw [semanticAtoms, List.mem_dedup]
  exact List.mem_map.mpr
    ⟨inventory.occurrenceAt position, List.get_mem _ _, rfl⟩

/-- The semantic representative inventory contains no duplicate values. -/
theorem semanticAtoms_nodup
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    (inventory : CostStaticParameterInventory source color targetFree table
      values root) : inventory.semanticAtoms.Nodup := by
  exact List.nodup_dedup _

end CostStaticParameterInventory

/-! ## Internal semantic-atom namespace -/

/-- Reserved namespace used only while one selected Cost frame is being
canonicalized.  Atom spellings are transport handles, never ordering keys. -/
def costStaticAtomVariableTag : String := "$cost:semantic-atom:"

/-- Canonical finite atom spelling. -/
def costStaticAtomVariableName (slot : Nat) : String :=
  costStaticAtomVariableTag ++ slot.repr

/-- Canonical atom spellings are collision-free. -/
theorem costStaticAtomVariableName_injective :
    Function.Injective costStaticAtomVariableName := by
  intro left right equality
  apply Nat.repr_injective
  exact (String.append_right_inj costStaticAtomVariableTag).mp equality

/-- Decode only canonical atom spellings.  The round-trip check rejects
decimal aliases such as leading-zero variants. -/
def decodeCostStaticAtomVariableName (name : String) : Option Nat := do
  let payload ← decodeTaggedPayload costStaticAtomVariableTag name
  let slot ← payload.toNat?
  if costStaticAtomVariableName slot = name then some slot else none

@[simp]
theorem decodeCostStaticAtomVariableName_encode (slot : Nat) :
    decodeCostStaticAtomVariableName (costStaticAtomVariableName slot) =
      some slot := by
  simp [decodeCostStaticAtomVariableName, costStaticAtomVariableName]

/-- Internal atom names are disjoint from retagged authored source names. -/
@[simp]
theorem decodeCostStaticAtomVariableName_sourceVariable (name : String) :
    decodeCostStaticAtomVariableName (costRegionSourceVariableName name) =
      none := by
  simp [decodeCostStaticAtomVariableName, decodeTaggedPayload,
    costStaticAtomVariableTag, costRegionSourceVariableName,
    costRegionSourceVariableTag, dropListPrefix?]

/-- Internal atom names are disjoint from proof-relevant boundary names. -/
@[simp]
theorem decodeCostStaticAtomVariableName_boundaryVariable
    (boundary : CostRegionBoundary) :
    decodeCostStaticAtomVariableName
        (costRegionBoundaryVariableName boundary) = none := by
  simp [decodeCostStaticAtomVariableName, decodeTaggedPayload,
    costStaticAtomVariableTag, costRegionBoundaryVariableName,
    costRegionBoundaryVariableTag, dropListPrefix?]

/-- Finite semantic quotient of an explicit positional occurrence inventory.

`occurrenceSlot` preserves occurrence multiplicity.  `atomValue` carries one
typed normalized value per semantic class.  `extensional` states that the
quotient identifies exactly equal semantic atoms—no source spelling or
boundary serialization participates. -/
structure CostStaticAtomEnvironment
    (source : CIGSLT) (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext)
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    (inventory : CostStaticParameterInventory source color targetFree table
      values root) where
  atomCount : Nat
  occurrenceSlot : inventory.Occurrence → Fin atomCount
  atomValue : Fin atomCount → TypedCostStaticAtom source color targetFree
  occurrenceValue : ∀ position,
    atomValue (occurrenceSlot position) = inventory.occurrenceAtom position
  extensional : ∀ left right,
    occurrenceSlot left = occurrenceSlot right ↔
      inventory.occurrenceAtom left = inventory.occurrenceAtom right

namespace CostStaticAtomEnvironment

/-- Resolve a parameter name through the proof-relevant occurrence vector,
then project its semantic quotient slot. -/
def slotOfName? {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (name : String) : Option (Fin environment.atomCount) :=
  (inventory.positionOfName? name).map environment.occurrenceSlot

/-- Every structural occurrence is represented in the name-to-slot view. -/
theorem slotOfName?_isSome_of_occurrence
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (occurrence : CostStaticFVarOccurrence root) :
    (environment.slotOfName? occurrence.name).isSome = true := by
  obtain ⟨position, selected⟩ := Option.isSome_iff_exists.mp
    (inventory.positionOfName?_isSome_of_occurrence occurrence)
  rw [Option.isSome_iff_exists]
  exact ⟨environment.occurrenceSlot position, by
    simp [slotOfName?, selected]⟩

/-- A successful name lookup returns the semantic value of every occurrence
with that name, independently of which positional representative was found. -/
theorem atomValue_of_slotOfName?_eq_some
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (occurrence : CostStaticFVarOccurrence root)
    (slot : Fin environment.atomCount)
    (selected : environment.slotOfName? occurrence.name = some slot) :
    environment.atomValue slot =
      inventory.occurrenceAtom (inventory.positionOf occurrence) := by
  unfold slotOfName? at selected
  cases positionSelected : inventory.positionOfName? occurrence.name with
  | none => simp [positionSelected] at selected
  | some position =>
      simp [positionSelected] at selected
      subst slot
      rw [environment.occurrenceValue]
      exact inventory.occurrenceAtom_eq_of_positionOfName?_eq_some occurrence
        position positionSelected

/-- A name-selected atom has exactly the target support assigned to that
original rigid parameter by the finite restoration table. -/
theorem atomValue_targetSupport_eq_of_slotOfName?_eq_some
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (occurrence : CostStaticFVarOccurrence root)
    (slot : Fin environment.atomCount)
    (selected : environment.slotOfName? occurrence.name = some slot) :
    (environment.atomValue slot).key.targetSupport =
      table.restorationSupport occurrence.name := by
  rw [environment.atomValue_of_slotOfName?_eq_some occurrence slot selected]
  change
    (inventory.occurrenceAt
      (inventory.positionOf occurrence)).atom.key.targetSupport = _
  rw [CostStaticParameterOccurrence.atom_targetSupport_eq_restorationSupport]
  exact congrArg table.restorationSupport
    (congrArg CostStaticFVarOccurrence.name
      (inventory.fvarOccurrence_occurrenceAt_positionOf occurrence))

/-- A name-selected atom has exactly the normalized value assigned to that
original rigid parameter by the child-first finite value vector. -/
theorem atomValue_normal_eq_of_slotOfName?_eq_some
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (occurrence : CostStaticFVarOccurrence root)
    (slot : Fin environment.atomCount)
    (selected : environment.slotOfName? occurrence.name = some slot) :
    (environment.atomValue slot).key.normal =
      values.assignment table occurrence.name := by
  rw [environment.atomValue_of_slotOfName?_eq_some occurrence slot selected]
  change
    (inventory.occurrenceAt
      (inventory.positionOf occurrence)).atom.key.normal = _
  rw [CostStaticParameterOccurrence.atom_normal_eq_assignment]
  exact congrArg (values.assignment table)
    (congrArg CostStaticFVarOccurrence.name
      (inventory.fvarOccurrence_occurrenceAt_positionOf occurrence))

/-- A name-selected atom has exactly the target type assigned to that
original rigid parameter by the mapped finite context. -/
theorem mappedFreeContext_eq_atomValue_targetType_of_slotOfName?_eq_some
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (occurrence : CostStaticFVarOccurrence root)
    (slot : Fin environment.atomCount)
    (selected : environment.slotOfName? occurrence.name = some slot) :
    table.mappedFreeContext occurrence.name =
      some (environment.atomValue slot).key.targetType := by
  rw [environment.atomValue_of_slotOfName?_eq_some occurrence slot selected]
  change table.mappedFreeContext occurrence.name =
    some (inventory.occurrenceAt
      (inventory.positionOf occurrence)).atom.key.targetType
  rw [← CostStaticParameterOccurrence.mappedFreeContext_eq_atom_targetType]
  exact congrArg table.mappedFreeContext
    (congrArg CostStaticFVarOccurrence.name
      (inventory.fvarOccurrence_occurrenceAt_positionOf occurrence)).symm

/-- A name-selected atom has exactly the source type assigned to the original
rigid parameter by the authored finite context. -/
theorem sourceFreeContext_eq_atomValue_sourceType_of_slotOfName?_eq_some
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (occurrence : CostStaticFVarOccurrence root)
    (slot : Fin environment.atomCount)
    (selected : environment.slotOfName? occurrence.name = some slot) :
    table.sourceFreeContext occurrence.name =
      some (environment.atomValue slot).key.sourceType := by
  rw [environment.atomValue_of_slotOfName?_eq_some occurrence slot selected]
  change table.sourceFreeContext occurrence.name =
    some (inventory.occurrenceAt
      (inventory.positionOf occurrence)).atom.key.sourceType
  rw [← CostStaticParameterOccurrence.sourceFreeContext_eq_atom_sourceType]
  exact congrArg table.sourceFreeContext
    (congrArg CostStaticFVarOccurrence.name
      (inventory.fvarOccurrence_occurrenceAt_positionOf occurrence)).symm

/-- A name-selected atom has exactly the source-side binder support assigned
to the original rigid parameter by the certified finite table. -/
theorem atomValue_targetSupport_eq_sourceSupport_of_slotOfName?_eq_some
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (occurrence : CostStaticFVarOccurrence root)
    (slot : Fin environment.atomCount)
    (selected : environment.slotOfName? occurrence.name = some slot) :
    (environment.atomValue slot).key.targetSupport =
      table.sourceSupport occurrence.name := by
  rw [environment.atomValue_of_slotOfName?_eq_some occurrence slot selected]
  change
    (inventory.occurrenceAt
      (inventory.positionOf occurrence)).atom.key.targetSupport = _
  rw [CostStaticParameterOccurrence.atom_targetSupport_eq_sourceSupport]
  exact congrArg table.sourceSupport
    (congrArg CostStaticFVarOccurrence.name
      (inventory.fvarOccurrence_occurrenceAt_positionOf occurrence))

/-- A name-selected atom exposes the authored-fiber support retained in its
complete semantic key. -/
theorem atomValue_sourceSupport_eq_atomSourceSupport_of_slotOfName?_eq_some
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (occurrence : CostStaticFVarOccurrence root)
    (slot : Fin environment.atomCount)
    (selected : environment.slotOfName? occurrence.name = some slot) :
    (environment.atomValue slot).key.sourceSupport =
      table.atomSourceSupport occurrence.name := by
  rw [environment.atomValue_of_slotOfName?_eq_some occurrence slot selected]
  change
    (inventory.occurrenceAt
      (inventory.positionOf occurrence)).atom.key.sourceSupport = _
  rw [CostStaticParameterOccurrence.atom_sourceSupport_eq_atomSourceSupport]
  exact congrArg table.atomSourceSupport
    (congrArg CostStaticFVarOccurrence.name
      (inventory.fvarOccurrence_occurrenceAt_positionOf occurrence))

/-- Canonical internal name of one finite semantic slot. -/
def atomName {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (slot : Fin environment.atomCount) : String :=
  costStaticAtomVariableName slot.1

/-- Decode an internal atom name only when its finite index is in range. -/
def lookupAtom? {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (name : String) : Option (Fin environment.atomCount) := do
  let slot ← decodeCostStaticAtomVariableName name
  if inBounds : slot < environment.atomCount then some ⟨slot, inBounds⟩
  else none

@[simp]
theorem lookupAtom?_atomName
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (slot : Fin environment.atomCount) :
    environment.lookupAtom? (environment.atomName slot) = some slot := by
  simp [lookupAtom?, atomName]

/-- Binder support used when restoring a canonical atom frame. -/
def restorationSupport {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    ContextSupport.Support := fun name =>
  match environment.lookupAtom? name with
  | some slot => (environment.atomValue slot).key.targetSupport
  | none => []

/-- Typed normalized value used when restoring a canonical atom frame. -/
def restorationAssignment {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    ContextSupport.Assignment := fun name =>
  match environment.lookupAtom? name with
  | some slot => (environment.atomValue slot).key.normal
  | none => .fvar name

@[simp]
theorem restorationSupport_atomName
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (slot : Fin environment.atomCount) :
    environment.restorationSupport (environment.atomName slot) =
      (environment.atomValue slot).key.targetSupport := by
  simp [restorationSupport]

@[simp]
theorem restorationAssignment_atomName
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (slot : Fin environment.atomCount) :
    environment.restorationAssignment (environment.atomName slot) =
      (environment.atomValue slot).key.normal := by
  simp [restorationAssignment]

/-- Executably quotient a finite positional inventory by complete typed
semantic-atom equality. -/
def ofInventory {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    (inventory : CostStaticParameterInventory source color targetFree table
      values root) :
    CostStaticAtomEnvironment source color targetFree inventory where
  atomCount := inventory.semanticAtoms.length
  occurrenceSlot := fun position =>
    ⟨List.idxOf (inventory.occurrenceAtom position)
        inventory.semanticAtoms,
      List.idxOf_lt_length_of_mem
        (inventory.occurrenceAtom_mem_semanticAtoms position)⟩
  atomValue := inventory.semanticAtoms.get
  occurrenceValue := by
    intro position
    exact List.idxOf_get
      (List.idxOf_lt_length_of_mem
        (inventory.occurrenceAtom_mem_semanticAtoms position))
  extensional := by
    intro left right
    constructor
    · intro slotEquality
      have valueEquality := congrArg inventory.semanticAtoms.get slotEquality
      simpa only [List.idxOf_get] using valueEquality
    · intro valueEquality
      apply Fin.ext
      change List.idxOf (inventory.occurrenceAtom left)
          inventory.semanticAtoms =
        List.idxOf (inventory.occurrenceAtom right) inventory.semanticAtoms
      rw [valueEquality]

/-- Existential package returned by the executable environment builder.  The
inventory remains available for provenance replay; its semantic quotient is
carried alongside it. -/
abbrev Packed (source : CIGSLT) (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext)
    {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree table)
    (root : Pattern) :=
  Σ inventory : CostStaticParameterInventory source color targetFree table
      values root,
    CostStaticAtomEnvironment source color targetFree inventory

/-- Build the positional occurrence inventory and its exact semantic quotient
in one fail-closed executable operation. -/
def build? {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree table)
    (root : Pattern) : Option (Packed source color targetFree table values root) :=
  match CostStaticParameterInventory.build? table values root with
  | none => none
  | some inventory => some ⟨inventory, ofInventory inventory⟩

/-- The complete environment builder is total on every admitted typed object
skeleton. -/
theorem build?_isSome_of_typed
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree table)
    {root : Pattern} {bound : List TypeExpr} {type : TypeExpr}
    (typed : WellSorted.HasType
      source.theory.presentation.presentation.language
      table.sourceFreeContext bound root type)
    (object : WellSorted.isObjectPattern root = true) :
    (build? table values root).isSome = true := by
  have total := CostStaticParameterInventory.build?_isSome_of_typed table values
    typed object
  rw [Option.isSome_iff_exists] at total
  obtain ⟨inventory, inventoryBuilt⟩ := total
  simp [build?, inventoryBuilt]

/-- The executable quotient has exactly one slot for each distinct semantic
atom in the positional inventory. -/
@[simp]
theorem ofInventory_atomCount {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    (inventory : CostStaticParameterInventory source color targetFree table
      values root) :
    (ofInventory inventory).atomCount = inventory.semanticAtoms.length :=
  rfl

/-- Positive quotient law: separate positional occurrences coalesce exactly
when their complete typed normalized values agree. -/
@[simp]
theorem ofInventory_occurrenceSlot_eq_iff
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    (inventory : CostStaticParameterInventory source color targetFree table
      values root) (left right : inventory.Occurrence) :
    (ofInventory inventory).occurrenceSlot left =
        (ofInventory inventory).occurrenceSlot right ↔
      inventory.occurrenceAtom left = inventory.occurrenceAtom right :=
  (ofInventory inventory).extensional left right

/-- Negative quotient law: differing typed semantic values cannot be merged
merely because their origins or compact payloads look similar. -/
theorem ofInventory_occurrenceSlot_ne_of_atom_ne
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    (inventory : CostStaticParameterInventory source color targetFree table
      values root) (left right : inventory.Occurrence)
    (different : inventory.occurrenceAtom left ≠
      inventory.occurrenceAtom right) :
    (ofInventory inventory).occurrenceSlot left ≠
      (ofInventory inventory).occurrenceSlot right := by
  intro equalSlot
  exact different ((ofInventory inventory).extensional left right |>.mp equalSlot)

/-- Every quotient slot produced from a coherent finite inventory retains the
source-to-target type map, independently of which occurrence represents the
semantic class. -/
theorem ofInventory_atomValue_targetType_eq_map_sourceType
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    (inventory : CostStaticParameterInventory source color targetFree table
      values root)
    (coherent : table.FiberCoherent)
    (slot : Fin (ofInventory inventory).atomCount) :
    mapTypeExpr (color.symbols source)
        ((ofInventory inventory).atomValue slot).key.sourceType =
      ((ofInventory inventory).atomValue slot).key.targetType := by
  have membership : inventory.semanticAtoms.get slot ∈
      inventory.semanticAtoms := List.get_mem _ _
  have occurrenceMembership : inventory.semanticAtoms.get slot ∈
      inventory.entries.map CostStaticParameterOccurrence.atom := by
    change inventory.semanticAtoms.get slot ∈
      (inventory.entries.map CostStaticParameterOccurrence.atom).dedup at membership
    exact List.mem_dedup.mp membership
  obtain ⟨parameter, _parameterMembership, parameterValue⟩ :=
    List.mem_map.mp occurrenceMembership
  have mapped := parameter.atom_targetType_eq_map_sourceType coherent
  change mapTypeExpr (color.symbols source)
      (inventory.semanticAtoms.get slot).key.sourceType =
    (inventory.semanticAtoms.get slot).key.targetType
  rw [← parameterValue]
  exact mapped

end CostStaticAtomEnvironment

/-! ## Semantic-key canaries -/

private def atomKeyCanary : CostStaticAtomKey where
  sourceType := .base "Name"
  sourceSupport := []
  targetType := .base "Name"
  targetSupport := []
  normal := .fvar "0"

/-- Positive canary: independently sourced occurrences coalesce when every
typed semantic component agrees. -/
example :
    ({ sourceType := .base "Name"
       sourceSupport := []
       targetType := .base "Name"
       targetSupport := []
       normal := .fvar "0" } : CostStaticAtomKey) = atomKeyCanary :=
  rfl

/-- Negative canary: an equal compact value at a different reflective support
is a different semantic atom. -/
example :
    ({ atomKeyCanary with targetSupport := [.base "Name"] } :
      CostStaticAtomKey) ≠ atomKeyCanary := by
  decide

end Mettapedia.GSLT.LanguageDef
