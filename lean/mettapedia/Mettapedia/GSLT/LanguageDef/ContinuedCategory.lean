import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mettapedia.GSLT.LanguageDef.CanonicalConstructorSupport
import Mettapedia.GSLT.LanguageDef.CanonicalSection
import Mettapedia.GSLT.LanguageDef.CostStatic

/-!
# Continued interactive GSLTs

A continued interactive GSLT is an iGSLT equipped with one ordered authored
interaction cut, a computable section of its equational quotient, and a
declaration-derived proof that the cut contractum remains sorted after its
continuations are wrapped.  These fields retain the exact `LanguageDef`
selected by the underlying iGSLT.

Morphisms preserve the selected cut and continuation retyping data.  They
commute with canonicalization and are injective on canonical keys.  Thus the
forgetful functor to iGSLTs forgets object structure but no morphism action.
-/

namespace Mettapedia.GSLT.LanguageDef

open CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open StructuralMorphism

/-- A continued interactive GSLT over one exact authored presentation. -/
structure CIGSLT where
  theory : IGSLT
  cut : InteractionCutPresentation theory
  /-- Canonicalization on every declaration-derived open sorted fiber.  The
  sort, free-variable context, binder context, object boundary, and
  reflective scope are retained; the paper-facing closed section is derived
  from this datum. -/
  openCanonical : ComputableContextualOpenSection theory
  continuationRetyping : ContinuationRetypingPlan cut
  /-- A bare collection representation hides its constructor label in the
  raw `Pattern`, so every such constructor must belong to the non-principal
  hereditary fragment explicitly.  Otherwise an interaction principal could
  cross the static boundary without appearing in raw constructor support. -/
  bareCollectionConstructorsWrapped :
    ∀ rule ∈ theory.presentation.presentation.language.terms,
      WellSorted.UsesBareCollection rule →
        rule.label ∈ continuationRetyping.wrappedLabels
  /-- Canonicalization preserves the declaration-derived non-principal
  constructor fragment in every typed open fiber.  This is the intrinsic
  closure law needed to iterate continued interaction: normalization may
  rearrange authored static structure, but it cannot manufacture either
  selected interaction principal. -/
  openCanonicalPreservesWrappedConstructorTyping :
    openCanonical.PreservesTypedConstructors
      (· ∈ continuationRetyping.wrappedLabels)
  /-- Every authored static equation has both a sorted base image and a
  sorted hereditary wrapped image in the declaration-derived Cost
  signature.  This is the exact extra stability needed to carry equations
  through position-sensitive continuation retyping. -/
  equationsRetypable : EquationsRetypable continuationRetyping
  /-- Every constructor named by an authored reflective presentation remains
  in the hereditary continuation closure.  This is the exact condition under
  which Cost can transport static canonicalization into both the base and
  wrapped fibers without inventing a wrapped interaction principal. -/
  reflectivePresentationsRetypable :
    ReflectivePresentationsRetypable continuationRetyping
  /-- The path from the interaction root to its ordered core stays outside
  the two selected continuation slots.  This structural witness is stable
  under repeated Cost retyping; the generated sorting theorem is derived
  from it rather than stored as unrelated evidence. -/
  sourceEnvelopeStable : ContinuationStableContext cut
    cut.coreContact.sort.1.name theory.presentation.interactingSort.1.name
    cut.sourceShape.envelope
  redexRetypable : continuationRetyping.RedexRetypable
  wrappable : continuationRetyping.Wrappable

namespace CIGSLT

/-- Restrict the contextual canonicalizer to the closed interacting carrier.
This is the section used for canonical keys in the paper-facing interface. -/
def canonical (theory : CIGSLT) : ComputableCanonicalSection theory.theory :=
  theory.openCanonical.toComputableCanonicalSection

/-- The stable source envelope remains sorted in the declaration-derived
continuation signature. -/
theorem sourceEnvelopeRetypable (source : CIGSLT) :
    source.continuationRetyping.SourceEnvelopeRetypable :=
  source.sourceEnvelopeStable.retype source.continuationRetyping

/-- Canonical signature keys are normalized representatives of authored
equation classes, before any optional digest is applied. -/
abbrev CanonicalKey (theory : CIGSLT) :=
  { term : theory.theory.toGSLT.Term //
      theory.canonical.normalize term = term }

/-- Every canonical key lies in the image of the computable section. -/
theorem canonicalKey_in_normalize_range (theory : CIGSLT)
    (key : theory.CanonicalKey) :
    ∃ term, theory.canonical.normalize term = key.1 :=
  ⟨key.1, key.2⟩

/-- Structural action on an optional schema pattern. -/
def mapOptionalPattern (symbols : PresentationSymbols) :
    Option Pattern → Option Pattern :=
  Option.map (mapPattern symbols)

@[simp]
theorem mapOptionalPattern_id (pattern : Option Pattern) :
    mapOptionalPattern PresentationSymbols.id pattern = pattern := by
  cases pattern <;> simp [mapOptionalPattern]

theorem mapOptionalPattern_comp (first second : PresentationSymbols)
    (pattern : Option Pattern) :
    mapOptionalPattern (first.comp second) pattern =
      mapOptionalPattern second (mapOptionalPattern first pattern) := by
  cases pattern <;> simp [mapOptionalPattern, mapPattern_comp]

/-- Map a canonical key by translating its representative and then applying
the target's computable section. -/
def canonicalKeyMap {source target : CIGSLT}
    (underlying : IGSLT.Morphism source.theory target.theory) :
    source.CanonicalKey → target.CanonicalKey :=
  fun key =>
    ⟨target.canonical.normalize (underlying.mapTerm key.1),
      target.canonical.normalize_idempotent _⟩

/-- A continued morphism is one iGSLT theory map preserving the exact
ordered cut, its selected continuation positions, the finite wrapped
constructor closure, and the computable canonical keys. -/
structure Morphism (source target : CIGSLT) where
  underlying : IGSLT.Morphism source.theory target.theory
  mapsCoreSort :
    underlying.structural.structural.mapSort source.cut.coreContact.sort =
      target.cut.coreContact.sort
  mapsCoreContactConstructor :
    underlying.structural.structural.mapConstructor
        source.cut.coreContact.constructor =
      target.cut.coreContact.constructor
  mapsCorePattern :
    mapPattern underlying.structural.structural.symbols
        source.cut.sourceShape.core =
      target.cut.sourceShape.core
  mapsSourceEnvelope :
    mapOneHoleContext underlying.structural.structural.symbols
        source.cut.sourceShape.envelope =
      target.cut.sourceShape.envelope
  /-- Cost retyping is fibered over the distinguished interacting sort.
  A continued map may not collapse another source sort into that fiber. -/
  reflectsInteractingSort : ∀ sourceSort,
    underlying.structural.structural.symbols.sort sourceSort =
        target.theory.presentation.interactingSort.1.name →
      sourceSort = source.theory.presentation.interactingSort.1.name
  /-- The finite hereditary continuation fiber is preserved and reflected by
  the total constructor-symbol action.  Structural maps are total outside
  authored declarations, so this law is the exact condition that makes the
  declaration-derived contractum translation natural on raw schemas. -/
  mapsWrappedLabelMembership : ∀ sourceLabel,
    underlying.structural.structural.symbols.constructor sourceLabel ∈
        target.continuationRetyping.wrappedLabels ↔
      sourceLabel ∈ source.continuationRetyping.wrappedLabels
  /-- The selected program-introduction constructor is a reflected fiber,
  not merely a chosen image.  This prevents retyping a previously unrelated
  constructor as a continuation carrier after transport. -/
  reflectsProgramConstructor : ∀ constructor,
    mapGrammarRule underlying.structural.structural.symbols constructor =
        target.cut.program.constructor.1 →
      constructor = source.cut.program.constructor.1
  /-- The selected environment-introduction constructor is reflected for the
  same reason as the program constructor. -/
  reflectsEnvironmentConstructor : ∀ constructor,
    mapGrammarRule underlying.structural.structural.symbols constructor =
        target.cut.environment.constructor.1 →
      constructor = source.cut.environment.constructor.1
  mapsProgramConstructor :
    underlying.structural.structural.mapConstructor
        source.cut.program.constructor =
      target.cut.program.constructor
  mapsEnvironmentConstructor :
    underlying.structural.structural.mapConstructor
        source.cut.environment.constructor =
      target.cut.environment.constructor
  mapsProgramContinuationIndex :
    source.cut.program.continuation.index =
      target.cut.program.continuation.index
  mapsEnvironmentContinuationIndex :
    source.cut.environment.continuation.index =
      target.cut.environment.continuation.index
  /-- A structural map cannot turn a genuine introduction into a direct
  contact continuation, or conversely. -/
  mapsProgramKind : source.cut.program.kind = target.cut.program.kind
  mapsEnvironmentKind :
    source.cut.environment.kind = target.cut.environment.kind
  mapsProgramSchema :
    mapPattern underlying.structural.structural.symbols
        source.cut.program.schemaTerm =
      target.cut.program.schemaTerm
  mapsEnvironmentSchema :
    mapPattern underlying.structural.structural.symbols
        source.cut.environment.schemaTerm =
      target.cut.environment.schemaTerm
  mapsProgramContinuation :
    mapPattern underlying.structural.structural.symbols
        source.cut.program.continuationPattern =
      target.cut.program.continuationPattern
  mapsEnvironmentContinuation :
    mapPattern underlying.structural.structural.symbols
        source.cut.environment.continuationPattern =
      target.cut.environment.continuationPattern
  mapsProgramSurface :
    mapOptionalPattern underlying.structural.structural.symbols
        source.cut.program.surface.pattern =
      target.cut.program.surface.pattern
  mapsEnvironmentSurface :
    mapOptionalPattern underlying.structural.structural.symbols
        source.cut.environment.surface.pattern =
      target.cut.environment.surface.pattern
  /-- Structural transport preserves every reflective quotation boundary at
  arbitrary binder depth.  Closed top-level scope preservation is already a
  field of the underlying iGSLT map; the open law is the additional datum
  needed beneath binders. -/
  mapsReflectiveScopeSafeAt : ∀ {depth pattern},
    WellSorted.ReflectiveScopeSafeAt
        source.theory.presentation.presentation.language depth pattern →
      WellSorted.ReflectiveScopeSafeAt
        target.theory.presentation.presentation.language depth
          (mapPattern underlying.structural.structural.symbols pattern)
  /-- Canonicalization is natural on declaration-derived open sorted terms.
  Unlike a law on raw patterns, both sides retain the expected sort and the
  exact free and bound typing contexts. -/
  mapsOpenCanonical : ∀ {free bound sort}
      (term : OpenTerm source.theory free bound sort),
    target.openCanonical.normalize
        (WellSorted.OpenTerm.map underlying.structural.structural
          mapsReflectiveScopeSafeAt term) =
      WellSorted.OpenTerm.map underlying.structural.structural
        mapsReflectiveScopeSafeAt (source.openCanonical.normalize term)
  quoteFaithful : Function.Injective (canonicalKeyMap underlying)

namespace Morphism

/-- A continued morphism maps the selected interacting sort in its
name-indexed form to the target's selected interacting sort. -/
theorem mapsInteractingLangSort {source target : CIGSLT}
    (morphism : Morphism source target) :
    WellSorted.mapLangSort morphism.underlying.structural.structural
        source.theory.presentation.interactingLangSort =
      target.theory.presentation.interactingLangSort := by
  rw [InteractivePresentation.interactingLangSort,
    WellSorted.mapLangSort_authoredSortToLangSort,
    morphism.underlying.structural.mapsInteractingSort]
  rfl

/-- Open typed naturality restricts to naturality of the closed
paper-facing canonical sections. -/
theorem mapsCanonical {source target : CIGSLT}
    (morphism : Morphism source target) (term : source.theory.toGSLT.Term) :
    target.canonical.normalize (morphism.underlying.mapTerm term) =
      morphism.underlying.mapTerm (source.canonical.normalize term) := by
  have openNaturality :=
    morphism.mapsOpenCanonical (closedTermToOpen term)
  let symbols := morphism.underlying.structural.structural.symbols
  have freeEquality :
      WellSorted.FreeTypeContext.empty.map symbols =
        WellSorted.FreeTypeContext.empty :=
    WellSorted.FreeTypeContext.map_empty symbols
  have boundEquality :
      ([] : List TypeExpr).map (mapTypeExpr symbols) = [] :=
    rfl
  have sortEquality := morphism.mapsInteractingLangSort
  let mappedTerm := WellSorted.OpenTerm.map
    morphism.underlying.structural.structural
    morphism.mapsReflectiveScopeSafeAt (closedTermToOpen term)
  have normalizationTransport := target.openCanonical.normalize_reindex
    freeEquality boundEquality sortEquality mappedTerm
  have transportedNaturality := congrArg
    (reindexOpenTerm freeEquality boundEquality sortEquality) openNaturality
  have fiberNaturality := normalizationTransport.trans transportedNaturality
  have mappedInputEquality :
      reindexOpenTerm freeEquality boundEquality sortEquality mappedTerm =
        closedTermToOpen (morphism.underlying.mapTerm term) := by
    apply Subtype.ext
    calc
      (reindexOpenTerm freeEquality boundEquality sortEquality mappedTerm).1 =
          mappedTerm.1 := reindexOpenTerm_pattern _ _ _ _
      _ = mapPattern symbols term.1 := rfl
      _ = (closedTermToOpen (morphism.underlying.mapTerm term)).1 := rfl
  rw [mappedInputEquality] at fiberNaturality
  apply Subtype.ext
  simpa [CIGSLT.canonical,
    ComputableContextualOpenSection.toComputableCanonicalSection,
    ComputableOpenSection.toComputableCanonicalSection,
    IGSLT.Morphism.mapTerm, IGSLT.mapClosedTerm, mappedTerm,
    symbols] using congrArg Subtype.val fiberNaturality

/-- Preservation of the hereditary continuation closure is derived from
preservation and reflection of the two principal introductions.  The closure
therefore carries no independent morphism policy. -/
theorem mapsWrappedConstructors {source target : CIGSLT}
    (morphism : Morphism source target)
    (constructor : AuthoredConstructor source.theory.presentation.presentation)
    (membership : constructor ∈
      source.continuationRetyping.wrappedConstructors) :
    morphism.underlying.structural.structural.mapConstructor constructor ∈
      target.continuationRetyping.wrappedConstructors := by
  rw [ContinuationRetypingPlan.mem_wrappedConstructors_iff] at membership ⊢
  constructor
  · intro mappedProgram
    apply membership.1
    apply Subtype.ext
    apply morphism.reflectsProgramConstructor constructor.1
    simpa [StructuralMorphism.mapConstructor] using
      congrArg Subtype.val mappedProgram
  · intro mappedEnvironment
    apply membership.2
    apply Subtype.ext
    apply morphism.reflectsEnvironmentConstructor constructor.1
    simpa [StructuralMorphism.mapConstructor] using
      congrArg Subtype.val mappedEnvironment

/-- Reflection of the hereditary continuation closure is likewise forced by
the reflected principal fibers. -/
theorem reflectsWrappedConstructors {source target : CIGSLT}
    (morphism : Morphism source target)
    (constructor : AuthoredConstructor source.theory.presentation.presentation)
    (membership :
      morphism.underlying.structural.structural.mapConstructor constructor ∈
        target.continuationRetyping.wrappedConstructors) :
    constructor ∈ source.continuationRetyping.wrappedConstructors := by
  rw [ContinuationRetypingPlan.mem_wrappedConstructors_iff] at membership ⊢
  constructor
  · intro sourceProgram
    apply membership.1
    rw [sourceProgram, morphism.mapsProgramConstructor]
  · intro sourceEnvironment
    apply membership.2
    rw [sourceEnvironment, morphism.mapsEnvironmentConstructor]

/-- Continued morphisms are determined by their underlying iGSLT map. -/
@[ext]
theorem ext {source target : CIGSLT}
    {first second : Morphism source target}
    (underlying : first.underlying = second.underlying) : first = second := by
  cases first
  cases second
  cases underlying
  rfl

/-- The canonical-key action of the identity is the identity. -/
@[simp]
theorem canonicalKeyMap_id (theory : CIGSLT)
    (key : theory.CanonicalKey) :
    canonicalKeyMap (IGSLT.Morphism.id theory.theory) key = key := by
  apply Subtype.ext
  simp [canonicalKeyMap, key.2]

/-- Identity continued morphism. -/
def id (theory : CIGSLT) : Morphism theory theory where
  underlying := IGSLT.Morphism.id theory.theory
  mapsCoreSort := by
    change (StructuralMorphism.id _).mapSort theory.cut.coreContact.sort = _
    exact StructuralMorphism.mapSort_id _ _
  mapsCoreContactConstructor := by
    change (StructuralMorphism.id _).mapConstructor
      theory.cut.coreContact.constructor = _
    exact StructuralMorphism.mapConstructor_id _ _
  mapsCorePattern := by
    change mapPattern PresentationSymbols.id _ = _
    exact mapPattern_id _
  mapsSourceEnvelope := by
    change mapOneHoleContext PresentationSymbols.id _ = _
    exact mapOneHoleContext_id _
  reflectsInteractingSort := by
    intro sourceSort equality
    exact equality
  mapsWrappedLabelMembership := by
    intro sourceLabel
    rfl
  reflectsProgramConstructor := by
    intro constructor equality
    change mapGrammarRule PresentationSymbols.id constructor = _ at equality
    rw [mapGrammarRule_id] at equality
    exact equality
  reflectsEnvironmentConstructor := by
    intro constructor equality
    change mapGrammarRule PresentationSymbols.id constructor = _ at equality
    rw [mapGrammarRule_id] at equality
    exact equality
  mapsProgramConstructor := by
    change (StructuralMorphism.id _).mapConstructor
      theory.cut.program.constructor = theory.cut.program.constructor
    exact StructuralMorphism.mapConstructor_id _ _
  mapsEnvironmentConstructor := by
    change (StructuralMorphism.id _).mapConstructor
      theory.cut.environment.constructor = theory.cut.environment.constructor
    exact StructuralMorphism.mapConstructor_id _ _
  mapsProgramContinuationIndex := rfl
  mapsEnvironmentContinuationIndex := rfl
  mapsProgramKind := rfl
  mapsEnvironmentKind := rfl
  mapsProgramSchema := by
    change mapPattern PresentationSymbols.id _ = _
    exact mapPattern_id _
  mapsEnvironmentSchema := by
    change mapPattern PresentationSymbols.id _ = _
    exact mapPattern_id _
  mapsProgramContinuation := by
    change mapPattern PresentationSymbols.id _ = _
    exact mapPattern_id _
  mapsEnvironmentContinuation := by
    change mapPattern PresentationSymbols.id _ = _
    exact mapPattern_id _
  mapsProgramSurface := by
    change mapOptionalPattern PresentationSymbols.id _ = _
    exact mapOptionalPattern_id _
  mapsEnvironmentSurface := by
    change mapOptionalPattern PresentationSymbols.id _ = _
    exact mapOptionalPattern_id _
  mapsReflectiveScopeSafeAt := by
    intro depth pattern safe
    change WellSorted.ReflectiveScopeSafeAt
      theory.theory.presentation.presentation.language depth
        (mapPattern PresentationSymbols.id pattern)
    rw [mapPattern_id]
    exact safe
  mapsOpenCanonical := by
    intro free bound sort term
    have freeEquality : free = free.map PresentationSymbols.id :=
      (WellSorted.FreeTypeContext.map_id free).symm
    have boundEquality :
        bound = bound.map (mapTypeExpr PresentationSymbols.id) := by
      symm
      calc
        bound.map (mapTypeExpr PresentationSymbols.id) =
            bound.map _root_.id := by
          apply List.map_congr_left
          intro type membership
          exact mapTypeExpr_id type
        _ = bound := List.map_id bound
    have sortEquality : sort =
        WellSorted.mapLangSort
          (StructuralMorphism.id theory.theory.presentation.presentation)
          sort := by
      simp
    have naturality := theory.openCanonical.normalize_reindex
      freeEquality boundEquality sortEquality term
    let identityScope : ∀ {depth pattern},
        WellSorted.ReflectiveScopeSafeAt
            theory.theory.presentation.presentation.language depth pattern →
          WellSorted.ReflectiveScopeSafeAt
            theory.theory.presentation.presentation.language depth
              (mapPattern PresentationSymbols.id pattern) := by
      intro depth pattern safe
      simpa using safe
    change theory.openCanonical.normalize
        (WellSorted.OpenTerm.map
          (StructuralMorphism.id theory.theory.presentation.presentation)
          identityScope term) =
      WellSorted.OpenTerm.map
        (StructuralMorphism.id theory.theory.presentation.presentation)
        identityScope (theory.openCanonical.normalize term)
    have mappedInputEquality :
        WellSorted.OpenTerm.map
            (StructuralMorphism.id theory.theory.presentation.presentation)
            identityScope term =
          reindexOpenTerm freeEquality boundEquality sortEquality term := by
      apply Subtype.ext
      calc
        (WellSorted.OpenTerm.map
            (StructuralMorphism.id theory.theory.presentation.presentation)
            identityScope term).1 =
          mapPattern PresentationSymbols.id term.1 := rfl
        _ = term.1 := mapPattern_id term.1
        _ = (reindexOpenTerm freeEquality boundEquality sortEquality term).1 :=
          (reindexOpenTerm_pattern _ _ _ _).symm
    apply Subtype.ext
    rw [mappedInputEquality]
    have rawNaturality := congrArg Subtype.val naturality
    calc
      (theory.openCanonical.normalize
          (reindexOpenTerm freeEquality boundEquality sortEquality term)).1 =
        (reindexOpenTerm freeEquality boundEquality sortEquality
          (theory.openCanonical.normalize term)).1 := rawNaturality
      _ = (theory.openCanonical.normalize term).1 :=
        reindexOpenTerm_pattern _ _ _ _
      _ = mapPattern PresentationSymbols.id
          (theory.openCanonical.normalize term).1 :=
        (mapPattern_id _).symm
  quoteFaithful := by
    intro left right equality
    simpa using equality

/-- Canonical-key action respects composition. -/
theorem canonicalKeyMap_comp {first second third : CIGSLT}
    (left : Morphism first second) (right : Morphism second third)
    (key : first.CanonicalKey) :
    canonicalKeyMap (IGSLT.Morphism.comp left.underlying right.underlying) key =
      canonicalKeyMap right.underlying
        (canonicalKeyMap left.underlying key) := by
  apply Subtype.ext
  simp only [canonicalKeyMap, IGSLT.Morphism.mapTerm_comp]
  rw [right.mapsCanonical, right.mapsCanonical]
  rw [second.canonical.normalize_idempotent]

/-- Composition of continued morphisms. -/
def comp {first second third : CIGSLT}
    (left : Morphism first second) (right : Morphism second third) :
    Morphism first third where
  underlying := IGSLT.Morphism.comp left.underlying right.underlying
  mapsCoreSort := by
    change (StructuralMorphism.comp
      left.underlying.structural.structural
      right.underlying.structural.structural).mapSort
        first.cut.coreContact.sort = third.cut.coreContact.sort
    rw [StructuralMorphism.mapSort_comp,
      left.mapsCoreSort, right.mapsCoreSort]
  mapsCoreContactConstructor := by
    change (StructuralMorphism.comp
      left.underlying.structural.structural
      right.underlying.structural.structural).mapConstructor
        first.cut.coreContact.constructor =
      third.cut.coreContact.constructor
    rw [StructuralMorphism.mapConstructor_comp,
      left.mapsCoreContactConstructor, right.mapsCoreContactConstructor]
  mapsCorePattern := by
    change mapPattern
      (left.underlying.structural.structural.symbols.comp
        right.underlying.structural.structural.symbols) _ = _
    rw [mapPattern_comp, left.mapsCorePattern, right.mapsCorePattern]
  mapsSourceEnvelope := by
    change mapOneHoleContext
      (left.underlying.structural.structural.symbols.comp
        right.underlying.structural.structural.symbols) _ = _
    rw [mapOneHoleContext_comp, left.mapsSourceEnvelope,
      right.mapsSourceEnvelope]
  reflectsInteractingSort := by
    intro sourceSort equality
    apply left.reflectsInteractingSort
    apply right.reflectsInteractingSort
    exact equality
  mapsWrappedLabelMembership := by
    intro sourceLabel
    change
      right.underlying.structural.structural.symbols.constructor
          (left.underlying.structural.structural.symbols.constructor
            sourceLabel) ∈
          third.continuationRetyping.wrappedLabels ↔
        sourceLabel ∈ first.continuationRetyping.wrappedLabels
    rw [right.mapsWrappedLabelMembership,
      left.mapsWrappedLabelMembership]
  reflectsProgramConstructor := by
    intro constructor equality
    change mapGrammarRule
      (left.underlying.structural.structural.symbols.comp
        right.underlying.structural.structural.symbols) constructor = _
      at equality
    rw [mapGrammarRule_comp] at equality
    apply left.reflectsProgramConstructor
    apply right.reflectsProgramConstructor
    exact equality
  reflectsEnvironmentConstructor := by
    intro constructor equality
    change mapGrammarRule
      (left.underlying.structural.structural.symbols.comp
        right.underlying.structural.structural.symbols) constructor = _
      at equality
    rw [mapGrammarRule_comp] at equality
    apply left.reflectsEnvironmentConstructor
    apply right.reflectsEnvironmentConstructor
    exact equality
  mapsProgramConstructor := by
    change (StructuralMorphism.comp
      left.underlying.structural.structural
      right.underlying.structural.structural).mapConstructor
        first.cut.program.constructor = third.cut.program.constructor
    rw [StructuralMorphism.mapConstructor_comp,
      left.mapsProgramConstructor, right.mapsProgramConstructor]
  mapsEnvironmentConstructor := by
    change (StructuralMorphism.comp
      left.underlying.structural.structural
      right.underlying.structural.structural).mapConstructor
        first.cut.environment.constructor = third.cut.environment.constructor
    rw [StructuralMorphism.mapConstructor_comp,
      left.mapsEnvironmentConstructor, right.mapsEnvironmentConstructor]
  mapsProgramContinuationIndex :=
    left.mapsProgramContinuationIndex.trans
      right.mapsProgramContinuationIndex
  mapsEnvironmentContinuationIndex :=
    left.mapsEnvironmentContinuationIndex.trans
      right.mapsEnvironmentContinuationIndex
  mapsProgramKind := left.mapsProgramKind.trans right.mapsProgramKind
  mapsEnvironmentKind :=
    left.mapsEnvironmentKind.trans right.mapsEnvironmentKind
  mapsProgramSchema := by
    change mapPattern
      (left.underlying.structural.structural.symbols.comp
        right.underlying.structural.structural.symbols) _ = _
    rw [mapPattern_comp, left.mapsProgramSchema, right.mapsProgramSchema]
  mapsEnvironmentSchema := by
    change mapPattern
      (left.underlying.structural.structural.symbols.comp
        right.underlying.structural.structural.symbols) _ = _
    rw [mapPattern_comp, left.mapsEnvironmentSchema,
      right.mapsEnvironmentSchema]
  mapsProgramContinuation := by
    change mapPattern
      (left.underlying.structural.structural.symbols.comp
        right.underlying.structural.structural.symbols) _ = _
    rw [mapPattern_comp, left.mapsProgramContinuation,
      right.mapsProgramContinuation]
  mapsEnvironmentContinuation := by
    change mapPattern
      (left.underlying.structural.structural.symbols.comp
        right.underlying.structural.structural.symbols) _ = _
    rw [mapPattern_comp, left.mapsEnvironmentContinuation,
      right.mapsEnvironmentContinuation]
  mapsProgramSurface := by
    change mapOptionalPattern
      (left.underlying.structural.structural.symbols.comp
        right.underlying.structural.structural.symbols) _ = _
    rw [mapOptionalPattern_comp, left.mapsProgramSurface,
      right.mapsProgramSurface]
  mapsEnvironmentSurface := by
    change mapOptionalPattern
      (left.underlying.structural.structural.symbols.comp
        right.underlying.structural.structural.symbols) _ = _
    rw [mapOptionalPattern_comp, left.mapsEnvironmentSurface,
      right.mapsEnvironmentSurface]
  mapsReflectiveScopeSafeAt := by
    intro depth pattern safe
    have firstSafe := left.mapsReflectiveScopeSafeAt safe
    have secondSafe := right.mapsReflectiveScopeSafeAt firstSafe
    change WellSorted.ReflectiveScopeSafeAt
      third.theory.presentation.presentation.language depth
        (mapPattern
          (IGSLT.Morphism.comp left.underlying right.underlying).structural.structural.symbols
          pattern)
    rw [IGSLT.Morphism.comp_baseStructural]
    change WellSorted.ReflectiveScopeSafeAt
      third.theory.presentation.presentation.language depth
        (mapPattern
          (left.underlying.structural.structural.symbols.comp
            right.underlying.structural.structural.symbols) pattern)
    rw [mapPattern_comp]
    exact secondSafe
  mapsOpenCanonical := by
    intro free bound sort term
    let firstStructural := left.underlying.structural.structural
    let secondStructural := right.underlying.structural.structural
    let compositeStructural :=
      StructuralMorphism.comp firstStructural secondStructural
    let firstMapped := WellSorted.OpenTerm.map firstStructural
      left.mapsReflectiveScopeSafeAt term
    let nestedMapped := WellSorted.OpenTerm.map secondStructural
      right.mapsReflectiveScopeSafeAt firstMapped
    let nestedNormalized := WellSorted.OpenTerm.map secondStructural
      right.mapsReflectiveScopeSafeAt
        (WellSorted.OpenTerm.map firstStructural
          left.mapsReflectiveScopeSafeAt
            (first.openCanonical.normalize term))
    have rightNaturality := right.mapsOpenCanonical firstMapped
    have leftNaturality := congrArg
      (WellSorted.OpenTerm.map secondStructural
        right.mapsReflectiveScopeSafeAt)
      (left.mapsOpenCanonical term)
    have combined :
        third.openCanonical.normalize nestedMapped = nestedNormalized :=
      rightNaturality.trans leftNaturality
    have freeEquality :
        (free.map firstStructural.symbols).map secondStructural.symbols =
          free.map compositeStructural.symbols :=
      (WellSorted.FreeTypeContext.map_comp free
        firstStructural.symbols secondStructural.symbols).symm
    have boundCompositeToNested :
        bound.map (mapTypeExpr compositeStructural.symbols) =
          (bound.map (mapTypeExpr firstStructural.symbols)).map
            (mapTypeExpr secondStructural.symbols) := by
      induction bound with
      | nil => rfl
      | cons type bound inductionHypothesis =>
          simp [compositeStructural, StructuralMorphism.comp,
            mapTypeExpr_comp]
    have boundEquality :
        (bound.map (mapTypeExpr firstStructural.symbols)).map
            (mapTypeExpr secondStructural.symbols) =
          bound.map (mapTypeExpr compositeStructural.symbols) :=
      boundCompositeToNested.symm
    have sortEquality :
        WellSorted.mapLangSort secondStructural
            (WellSorted.mapLangSort firstStructural sort) =
          WellSorted.mapLangSort compositeStructural sort :=
      (WellSorted.mapLangSort_comp firstStructural secondStructural sort).symm
    have normalizationTransport := third.openCanonical.normalize_reindex
      freeEquality boundEquality sortEquality nestedMapped
    have transportedCombined := congrArg
      (reindexOpenTerm freeEquality boundEquality sortEquality) combined
    have fiberNaturality := normalizationTransport.trans transportedCombined
    let compositeScope : ∀ {depth pattern},
        WellSorted.ReflectiveScopeSafeAt
            first.theory.presentation.presentation.language depth pattern →
          WellSorted.ReflectiveScopeSafeAt
            third.theory.presentation.presentation.language depth
              (mapPattern compositeStructural.symbols pattern) := by
      intro depth pattern safe
      have firstSafe := left.mapsReflectiveScopeSafeAt safe
      have secondSafe := right.mapsReflectiveScopeSafeAt firstSafe
      simpa [compositeStructural, StructuralMorphism.comp,
        mapPattern_comp] using secondSafe
    let compositeMapped := WellSorted.OpenTerm.map compositeStructural
      compositeScope term
    let compositeNormalized := WellSorted.OpenTerm.map compositeStructural
      compositeScope (first.openCanonical.normalize term)
    have inputEquality :
        reindexOpenTerm freeEquality boundEquality sortEquality nestedMapped =
          compositeMapped := by
      apply Subtype.ext
      calc
        (reindexOpenTerm freeEquality boundEquality sortEquality
            nestedMapped).1 = nestedMapped.1 :=
          reindexOpenTerm_pattern _ _ _ _
        _ = mapPattern secondStructural.symbols
            (mapPattern firstStructural.symbols term.1) := rfl
        _ = mapPattern compositeStructural.symbols term.1 := by
          symm
          exact mapPattern_comp firstStructural.symbols
            secondStructural.symbols term.1
        _ = compositeMapped.1 := rfl
    have outputEquality :
        reindexOpenTerm freeEquality boundEquality sortEquality
            nestedNormalized =
          compositeNormalized := by
      apply Subtype.ext
      calc
        (reindexOpenTerm freeEquality boundEquality sortEquality
            nestedNormalized).1 = nestedNormalized.1 :=
          reindexOpenTerm_pattern _ _ _ _
        _ = mapPattern secondStructural.symbols
            (mapPattern firstStructural.symbols
              (first.openCanonical.normalize term).1) := rfl
        _ = mapPattern compositeStructural.symbols
            (first.openCanonical.normalize term).1 := by
          symm
          exact mapPattern_comp firstStructural.symbols
            secondStructural.symbols _
        _ = compositeNormalized.1 := rfl
    rw [inputEquality, outputEquality] at fiberNaturality
    simpa [compositeMapped, compositeNormalized, compositeStructural,
      IGSLT.Morphism.comp, InteractiveMorphism.comp] using fiberNaturality
  quoteFaithful := by
    intro leftKey rightKey equality
    apply left.quoteFaithful
    apply right.quoteFaithful
    rw [← canonicalKeyMap_comp left right,
      ← canonicalKeyMap_comp left right]
    exact equality

end Morphism

/-- Continued interactive GSLTs form a Mathlib category. -/
instance : CategoryTheory.Category CIGSLT where
  Hom := Morphism
  id := Morphism.id
  comp := Morphism.comp
  id_comp morphism := by
    apply Morphism.ext
    apply IGSLT.Morphism.ext
    apply InteractiveMorphism.ext
    rfl
  comp_id morphism := by
    apply Morphism.ext
    apply IGSLT.Morphism.ext
    apply InteractiveMorphism.ext
    rfl
  assoc first second third := by
    apply Morphism.ext
    apply IGSLT.Morphism.ext
    apply InteractiveMorphism.ext
    rfl

/-- Forget the selected cut, section, and wrappability witness. -/
def forget : CategoryTheory.Functor CIGSLT IGSLT where
  obj theory := theory.theory
  map morphism := morphism.underlying
  map_id theory := by
    apply IGSLT.Morphism.ext
    apply InteractiveMorphism.ext
    rfl
  map_comp left right := by
    apply IGSLT.Morphism.ext
    apply InteractiveMorphism.ext
    rfl

/-- Forgetting continued structure loses no information about morphisms. -/
instance forget_faithful : CategoryTheory.Functor.Faithful forget where
  map_injective := by
    intro source target first second equality
    exact Morphism.ext equality

end CIGSLT

end Mettapedia.GSLT.LanguageDef
