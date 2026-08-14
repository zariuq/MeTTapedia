import Mettapedia.GSLT.LanguageDef.CostOneElaboratedObject

/-!
# The normalizer-indexed one-step Cost category

The generated Cost presentation has a forced declaration map: every source
symbol moves under its reserved Cost tag and every Cost apparatus symbol is
fixed.  Behavioral preservation is a separate semantic arrow law, just as it
is for ordinary `IGSLT.Morphism`s.

This file builds that action in layers.  It does not accept an output
`CIGSLT.Morphism` as data: the generated interactive map is constructed from
the source continued morphism, and later layers add only the irreducible laws
needed for reflection, selected-normalizer naturality, and canonical keys.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.GSLT
open Mettapedia.OSLF.MeTTaIL.Syntax

private theorem typeDecl_ext {left right : TypeDecl}
    (names : left.name = right.name)
    (carriers : left.carrier = right.carrier) : left = right := by
  cases left
  cases right
  simp_all

namespace CIGSLT.Morphism

/-- The declaration-derived Cost interaction map.  Its symbol action is
forced by `costPresentationSymbols`; the selected wrapped carrier, contact,
and funded rewrite are transported from their generated declarations. -/
def costWholeInteractive {source target : CIGSLT}
    (morphism : source.Morphism target) :
    InteractiveMorphism source.costWholeInteractivePresentation
      target.costWholeInteractivePresentation where
  structural := morphism.costWholeStructural
  mapsInteractingSort := by
    apply Subtype.ext
    change TypeDecl.mk
        ((costPresentationSymbols
          morphism.underlying.structural.structural.symbols).sort
            costWrappedSortName) .ast =
      TypeDecl.mk costWrappedSortName .ast
    rw [costPresentationSymbols_sort_wrapped]
  mapsContactConstructor := by
    apply Subtype.ext
    simp [costWholeInteractivePresentation, costWholeContactConstructor,
      costWholeStructural, StructuralMorphism.mapConstructor,
      costContactConstructor, mapGrammarRule, mapTermParam, mapTypeExpr,
      costContactConstructorName,
      costPresentationSymbols_constructor_apparatus]
  mapsInteractionRewrite := by
    apply Subtype.ext
    exact morphism.map_costWholeRedexRewrite

/-- The generated interactive action sends identity to identity. -/
@[simp]
theorem costWholeInteractive_id (source : CIGSLT) :
    (CIGSLT.Morphism.id source).costWholeInteractive =
      InteractiveMorphism.id source.costWholeInteractivePresentation := by
  apply InteractiveMorphism.ext
  apply StructuralMorphism.ext
  exact costPresentationSymbols_id

/-- The generated interactive action respects composition. -/
theorem costWholeInteractive_comp {first second third : CIGSLT}
    (left : first.Morphism second) (right : second.Morphism third) :
    (CIGSLT.Morphism.comp left right).costWholeInteractive =
      InteractiveMorphism.comp left.costWholeInteractive
        right.costWholeInteractive := by
  apply InteractiveMorphism.ext
  apply StructuralMorphism.ext
  exact costPresentationSymbols_comp
    left.underlying.structural.structural.symbols
    right.underlying.structural.structural.symbols

/-- The distinguished contact sort of the generated cut is the natural base
copy of the source contact sort. -/
theorem mapsCostCoreSort {source target : CIGSLT}
    (morphism : source.Morphism target) :
    morphism.costWholeStructural.mapSort
        source.costInteractionCut.coreContact.sort =
      target.costInteractionCut.coreContact.sort := by
  apply Subtype.ext
  apply typeDecl_ext
  · change (costPresentationSymbols
      morphism.underlying.structural.structural.symbols).sort
        (costBaseSortName source.cut.coreContact.sort.1.name) =
      costBaseSortName target.cut.coreContact.sort.1.name
    rw [costPresentationSymbols_sort_base]
    exact congrArg (fun name => costBaseSortName name)
      (congrArg TypeDecl.name
        (congrArg Subtype.val morphism.mapsCoreSort))
  · change source.cut.coreContact.sort.1.carrier =
      target.cut.coreContact.sort.1.carrier
    simpa [StructuralMorphism.mapSort, mapTypeDecl] using
      congrArg TypeDecl.carrier
        (congrArg Subtype.val morphism.mapsCoreSort)

/-- The distinguished contact constructor of the generated cut is the
natural base copy of the source contact constructor. -/
theorem mapsCostCoreContactConstructor {source target : CIGSLT}
    (morphism : source.Morphism target) :
    morphism.costWholeStructural.mapConstructor
        source.costInteractionCut.coreContact.constructor =
      target.costInteractionCut.coreContact.constructor := by
  apply Subtype.ext
  change mapGrammarRule
      (costPresentationSymbols
        morphism.underlying.structural.structural.symbols)
      (costBaseConstructor source.cut source.cut.coreContact.constructor.1) =
    costBaseConstructor target.cut target.cut.coreContact.constructor.1
  rw [morphism.mapGrammarRule_costBaseConstructor]
  rw [show mapGrammarRule
      morphism.underlying.structural.structural.symbols
      source.cut.coreContact.constructor.1 =
        target.cut.coreContact.constructor.1 from
    congrArg Subtype.val morphism.mapsCoreContactConstructor]

/-- The generated cut core is natural under the forced Cost symbol action. -/
theorem mapsCostCorePattern {source target : CIGSLT}
    (morphism : source.Morphism target) :
    mapPattern morphism.costWholeStructural.symbols
        source.costInteractionCut.sourceShape.core =
      target.costInteractionCut.sourceShape.core := by
  change mapPattern
      (costPresentationSymbols
        morphism.underlying.structural.structural.symbols)
      source.costBaseInteractionCore = target.costBaseInteractionCore
  exact morphism.map_costBaseInteractionCore

/-- The generated whole-redex envelope is natural independently of the
pattern plugged into its hole. -/
theorem mapsCostSourceEnvelope {source target : CIGSLT}
    (morphism : source.Morphism target) :
    mapOneHoleContext morphism.costWholeStructural.symbols
        source.costInteractionCut.sourceShape.envelope =
      target.costInteractionCut.sourceShape.envelope := by
  change mapOneHoleContext
      (costPresentationSymbols
        morphism.underlying.structural.structural.symbols)
      source.costWholeRedexEnvelope = target.costWholeRedexEnvelope
  exact morphism.map_costWholeRedexEnvelope

/-- Base transport of an operand schema is natural under a continued map. -/
theorem mapCostBaseSchemaPattern {source target : CIGSLT}
    (morphism : source.Morphism target) (pattern : Pattern) :
    mapPattern morphism.costWholeStructural.symbols
        (costBaseSchemaPattern pattern) =
      costBaseSchemaPattern
        (mapPattern morphism.underlying.structural.structural.symbols
          pattern) := by
  unfold costBaseSchemaPattern
  rw [mapPattern_mapPatternSchemaNames]
  apply congrArg (mapPatternSchemaNames costSourceSchemaName)
  change mapPattern
      (costPresentationSymbols
        morphism.underlying.structural.structural.symbols)
      (mapPattern costBasePresentationSymbols pattern) = _
  exact mapPattern_costBasePresentation_natural _ _

/-- The generated program introduction is the natural base copy of the
selected source introduction. -/
theorem mapsCostProgramConstructor {source target : CIGSLT}
    (morphism : source.Morphism target) :
    morphism.costWholeStructural.mapConstructor
        source.costInteractionCut.program.constructor =
      target.costInteractionCut.program.constructor := by
  apply Subtype.ext
  rw [costInteractionCut_program_constructor,
    costInteractionCut_program_constructor]
  change mapGrammarRule morphism.costWholeStructural.symbols
      (costBaseConstructor source.cut source.cut.program.constructor.1) =
    costBaseConstructor target.cut target.cut.program.constructor.1
  change mapGrammarRule
      (costPresentationSymbols
        morphism.underlying.structural.structural.symbols)
      (costBaseConstructor source.cut source.cut.program.constructor.1) = _
  rw [morphism.mapGrammarRule_costBaseConstructor]
  rw [show mapGrammarRule
      morphism.underlying.structural.structural.symbols
      source.cut.program.constructor.1 = target.cut.program.constructor.1 from
    congrArg Subtype.val morphism.mapsProgramConstructor]

/-- The generated environment introduction is natural for the same reason. -/
theorem mapsCostEnvironmentConstructor {source target : CIGSLT}
    (morphism : source.Morphism target) :
    morphism.costWholeStructural.mapConstructor
        source.costInteractionCut.environment.constructor =
      target.costInteractionCut.environment.constructor := by
  apply Subtype.ext
  rw [costInteractionCut_environment_constructor,
    costInteractionCut_environment_constructor]
  change mapGrammarRule morphism.costWholeStructural.symbols
      (costBaseConstructor source.cut source.cut.environment.constructor.1) =
    costBaseConstructor target.cut target.cut.environment.constructor.1
  change mapGrammarRule
      (costPresentationSymbols
        morphism.underlying.structural.structural.symbols)
      (costBaseConstructor source.cut source.cut.environment.constructor.1) = _
  rw [morphism.mapGrammarRule_costBaseConstructor]
  rw [show mapGrammarRule
      morphism.underlying.structural.structural.symbols
      source.cut.environment.constructor.1 =
        target.cut.environment.constructor.1 from
    congrArg Subtype.val morphism.mapsEnvironmentConstructor]

theorem mapsCostProgramSchema {source target : CIGSLT}
    (morphism : source.Morphism target) :
    mapPattern morphism.costWholeStructural.symbols
        source.costInteractionCut.program.schemaTerm =
      target.costInteractionCut.program.schemaTerm := by
  change mapPattern morphism.costWholeStructural.symbols
      source.costProgramOperand.schemaTerm = target.costProgramOperand.schemaTerm
  rw [costProgramOperand_schemaTerm, costProgramOperand_schemaTerm,
    morphism.mapCostBaseSchemaPattern, morphism.mapsProgramSchema]

theorem mapsCostEnvironmentSchema {source target : CIGSLT}
    (morphism : source.Morphism target) :
    mapPattern morphism.costWholeStructural.symbols
        source.costInteractionCut.environment.schemaTerm =
      target.costInteractionCut.environment.schemaTerm := by
  change mapPattern morphism.costWholeStructural.symbols
      source.costEnvironmentOperand.schemaTerm =
        target.costEnvironmentOperand.schemaTerm
  rw [costEnvironmentOperand_schemaTerm,
    costEnvironmentOperand_schemaTerm,
    morphism.mapCostBaseSchemaPattern, morphism.mapsEnvironmentSchema]

theorem mapsCostProgramContinuation {source target : CIGSLT}
    (morphism : source.Morphism target) :
    mapPattern morphism.costWholeStructural.symbols
        source.costInteractionCut.program.continuationPattern =
      target.costInteractionCut.program.continuationPattern := by
  change mapPattern morphism.costWholeStructural.symbols
      source.costProgramOperand.continuationPattern =
        target.costProgramOperand.continuationPattern
  rw [costProgramOperand_continuationPattern,
    costProgramOperand_continuationPattern,
    morphism.mapCostBaseSchemaPattern, morphism.mapsProgramContinuation]

theorem mapsCostEnvironmentContinuation {source target : CIGSLT}
    (morphism : source.Morphism target) :
    mapPattern morphism.costWholeStructural.symbols
        source.costInteractionCut.environment.continuationPattern =
      target.costInteractionCut.environment.continuationPattern := by
  change mapPattern morphism.costWholeStructural.symbols
      source.costEnvironmentOperand.continuationPattern =
        target.costEnvironmentOperand.continuationPattern
  rw [costEnvironmentOperand_continuationPattern,
    costEnvironmentOperand_continuationPattern,
    morphism.mapCostBaseSchemaPattern, morphism.mapsEnvironmentContinuation]

theorem reflectsCostInteractingSort {source target : CIGSLT}
    (morphism : source.Morphism target) (sourceSort : String)
    (mapped : morphism.costWholeStructural.symbols.sort sourceSort =
      target.costIGSLT.presentation.interactingSort.1.name) :
    sourceSort = source.costIGSLT.presentation.interactingSort.1.name := by
  change (costPresentationSymbols
      morphism.underlying.structural.structural.symbols).sort sourceSort =
    costWrappedSortName at mapped
  exact (costPresentationSymbols_sort_eq_wrapped_iff _ _).mp mapped

theorem mapsCostProgramContinuationIndex {source target : CIGSLT}
    (morphism : source.Morphism target) :
    source.costInteractionCut.program.continuation.index =
      target.costInteractionCut.program.continuation.index := by
  rw [costInteractionCut_program_continuation_index,
    costInteractionCut_program_continuation_index]
  exact morphism.mapsProgramContinuationIndex

theorem mapsCostEnvironmentContinuationIndex {source target : CIGSLT}
    (morphism : source.Morphism target) :
    source.costInteractionCut.environment.continuation.index =
      target.costInteractionCut.environment.continuation.index := by
  rw [costInteractionCut_environment_continuation_index,
    costInteractionCut_environment_continuation_index]
  exact morphism.mapsEnvironmentContinuationIndex

theorem mapsCostProgramKind {source target : CIGSLT}
    (morphism : source.Morphism target) :
    source.costInteractionCut.program.kind =
      target.costInteractionCut.program.kind := by
  change source.costProgramOperand.kind = target.costProgramOperand.kind
  rw [costProgramOperand_kind, costProgramOperand_kind]
  exact morphism.mapsProgramKind

theorem mapsCostEnvironmentKind {source target : CIGSLT}
    (morphism : source.Morphism target) :
    source.costInteractionCut.environment.kind =
      target.costInteractionCut.environment.kind := by
  change source.costEnvironmentOperand.kind = target.costEnvironmentOperand.kind
  rw [costEnvironmentOperand_kind, costEnvironmentOperand_kind]
  exact morphism.mapsEnvironmentKind

theorem mapsCostProgramSubject {source target : CIGSLT}
    (morphism : source.Morphism target) :
    mapOptionalPattern morphism.costWholeStructural.symbols
        source.costInteractionCut.program.subject.pattern =
      target.costInteractionCut.program.subject.pattern := by
  change mapOptionalPattern morphism.costWholeStructural.symbols
      source.costProgramOperand.subject.pattern =
    target.costProgramOperand.subject.pattern
  simp [mapOptionalPattern]

theorem mapsCostEnvironmentSubject {source target : CIGSLT}
    (morphism : source.Morphism target) :
    mapOptionalPattern morphism.costWholeStructural.symbols
        source.costInteractionCut.environment.subject.pattern =
      target.costInteractionCut.environment.subject.pattern := by
  change mapOptionalPattern morphism.costWholeStructural.symbols
      source.costEnvironmentOperand.subject.pattern =
    target.costEnvironmentOperand.subject.pattern
  simp [mapOptionalPattern]

end CIGSLT.Morphism

/-- The irreducible behavioral condition for lifting a continued morphism
through the generated Cost iGSLT.  The term action is not supplied: it is the
structural action forced by `CIGSLT.Morphism.costWholeInteractive`. -/
def CostGeneratedBisimPreserving {source target : CIGSLT}
    (morphism : source.Morphism target) : Prop :=
  ∀ {left right : source.costIGSLT.presentation.Term},
    source.costIGSLT.toGSLT.Bisimilar left right →
      target.costIGSLT.toGSLT.Bisimilar
        (IGSLT.mapClosedTerm morphism.costWholeInteractive left)
        (IGSLT.mapClosedTerm morphism.costWholeInteractive right)

/-- Preservation of the generated Cost quotation boundaries.  As for an
ordinary continued morphism, this is stronger than declaration membership:
the target may contain additional reflective presentations, so scope safety
must hold against the entire target profile. -/
def CostGeneratedReflectiveScopePreserving {source target : CIGSLT}
    (morphism : source.Morphism target) : Prop :=
  ∀ {depth pattern},
    ReflectiveWellSorted.ReflectiveScopeSafeAt
        source.costWholeReflectionProfile depth pattern →
      ReflectiveWellSorted.ReflectiveScopeSafeAt
        target.costWholeReflectionProfile depth
        (mapPattern
          (costPresentationSymbols
            morphism.underlying.structural.structural.symbols)
          pattern)

namespace CIGSLT.Morphism

/-- Map one typed open term of the generated Cost presentation. -/
def mapCostOpenTerm {source target : CIGSLT}
    (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    {free bound sort}
    (term : ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage free bound sort) :
    ReflectiveWellSorted.OpenTerm target.costWholeReflectionProfile
      target.costWholeLanguage
      (free.map morphism.costWholeStructural.symbols)
      (bound.map (mapTypeExpr morphism.costWholeStructural.symbols))
      (WellSorted.mapLangSort morphism.costWholeStructural sort) :=
  term.map morphism.costWholeStructural scope

/-- A Cost-behavior-preserving continued map induces the exact generated
iGSLT morphism.  Only the semantic preservation proof is additional; the
interactive declaration map was constructed above. -/
def costIGSLTMorphism {source target : CIGSLT}
    (morphism : source.Morphism target)
    (preserves : CostGeneratedBisimPreserving morphism) :
    IGSLT.Morphism source.costIGSLT target.costIGSLT where
  structural := morphism.costWholeInteractive
  preservesBisim := preserves

end CIGSLT.Morphism

namespace CostGeneratedBisimPreserving

/-- Identity satisfies the generated behavioral obligation. -/
theorem id (source : CIGSLT) :
    CostGeneratedBisimPreserving (CIGSLT.Morphism.id source) := by
  intro left right equivalent
  rw [CIGSLT.Morphism.costWholeInteractive_id]
  simpa [IGSLT.mapClosedTerm, InteractiveMorphism.id,
    StructuralMorphism.id, mapPattern_id] using equivalent

/-- Generated behavioral preservation is closed under composition. -/
theorem comp {first second third : CIGSLT}
    {left : first.Morphism second} {right : second.Morphism third}
    (leftPreserves : CostGeneratedBisimPreserving left)
    (rightPreserves : CostGeneratedBisimPreserving right) :
    CostGeneratedBisimPreserving (CIGSLT.Morphism.comp left right) := by
  intro source target equivalent
  rw [CIGSLT.Morphism.costWholeInteractive_comp]
  exact (IGSLT.Morphism.comp
    (left.costIGSLTMorphism leftPreserves)
    (right.costIGSLTMorphism rightPreserves)).preservesBisim equivalent

end CostGeneratedBisimPreserving

namespace CostGeneratedReflectiveScopePreserving

/-- Identity preserves every generated Cost quotation boundary. -/
theorem id (source : CIGSLT) :
    CostGeneratedReflectiveScopePreserving (CIGSLT.Morphism.id source) := by
  intro depth pattern safe
  change ReflectiveWellSorted.ReflectiveScopeSafeAt
    source.costWholeReflectionProfile depth
      (mapPattern (costPresentationSymbols PresentationSymbols.id) pattern)
  rw [costPresentationSymbols_id, mapPattern_id]
  exact safe

/-- Generated Cost quotation-boundary preservation composes. -/
theorem comp {first second third : CIGSLT}
    {left : first.Morphism second} {right : second.Morphism third}
    (leftPreserves : CostGeneratedReflectiveScopePreserving left)
    (rightPreserves : CostGeneratedReflectiveScopePreserving right) :
    CostGeneratedReflectiveScopePreserving
      (CIGSLT.Morphism.comp left right) := by
  intro depth pattern safe
  have firstSafe := leftPreserves safe
  have secondSafe := rightPreserves firstSafe
  change ReflectiveWellSorted.ReflectiveScopeSafeAt
    third.costWholeReflectionProfile depth
      (mapPattern
        (costPresentationSymbols
          (left.underlying.structural.structural.symbols.comp
            right.underlying.structural.structural.symbols)) pattern)
  rw [costPresentationSymbols_comp, mapPattern_comp]
  exact secondSafe

end CostGeneratedReflectiveScopePreserving

/-- Naturality of two selected Cost normalizers along a generated structural
map.  This is the exact square needed for the `mapsOpenCanonical` field of the
eventual continued Cost morphism. -/
def CostNormalizerNatural {source target : CIGSLT}
    (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    (sourceNormalizer : CostOpenNormalizer source)
    (targetNormalizer : CostOpenNormalizer target) : Prop :=
  ∀ {free bound sort}
    (term : ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage free bound sort),
    targetNormalizer (morphism.mapCostOpenTerm scope term) =
      (sourceNormalizer term).map morphism.costWholeStructural scope

/-- Semantic laws on a source continued morphism that are not forced by the
declaration-derived Cost construction.

No output map is stored.  Generated behavior and reflection are properties
of the forced Cost symbol action; `normalizerNatural` relates the two
normalizers carried by the endpoint objects; `quoteFaithful` is the exact
canonical-key condition required by a continued morphism. -/
structure CostOneMorphismLaws
    (source target : CostOneDomainObject)
    (underlying : OrderedCIGSLT.Morphism source.source target.source) : Prop where
  preservesGeneratedBisim :
    CostGeneratedBisimPreserving underlying.underlying
  preservesGeneratedReflectiveScope :
    CostGeneratedReflectiveScopePreserving underlying.underlying
  reflectsGeneratedProgramConstructor : ∀ constructor,
    mapGrammarRule
        (costPresentationSymbols underlying.underlying.underlying.structural.structural.symbols)
        constructor = target.source.toCIGSLT.costInteractionCut.program.constructor.1 →
      constructor = source.source.toCIGSLT.costInteractionCut.program.constructor.1
  reflectsGeneratedEnvironmentConstructor : ∀ constructor,
    mapGrammarRule
        (costPresentationSymbols underlying.underlying.underlying.structural.structural.symbols)
        constructor =
          target.source.toCIGSLT.costInteractionCut.environment.constructor.1 →
      constructor =
        source.source.toCIGSLT.costInteractionCut.environment.constructor.1
  mapsGeneratedWrappedLabelMembership : ∀ sourceLabel,
    (costPresentationSymbols
        underlying.underlying.underlying.structural.structural.symbols).constructor
          sourceLabel ∈
        target.source.toCIGSLT.costContinuationRetyping.wrappedLabels ↔
      sourceLabel ∈
        source.source.toCIGSLT.costContinuationRetyping.wrappedLabels
  normalizerNatural :
    CostNormalizerNatural underlying.underlying
      preservesGeneratedReflectiveScope source.normalizeOpen
        target.normalizeOpen
  quoteFaithful : Function.Injective
    (fun key : source.compactOutput.toCIGSLT.CanonicalKey =>
      mapPattern
        (costPresentationSymbols
          underlying.underlying.underlying.structural.structural.symbols)
        key.1.1)

namespace CostOneMorphismLaws

/-- Identity satisfies every generated Cost arrow law.  Normalizer
naturality is inherited from the checked continued identity on the selected
compact output. -/
def id (source : CostOneDomainObject) :
    CostOneMorphismLaws source source
      (OrderedCIGSLT.Morphism.id source.source) where
  preservesGeneratedBisim := CostGeneratedBisimPreserving.id _
  preservesGeneratedReflectiveScope :=
    CostGeneratedReflectiveScopePreserving.id _
  reflectsGeneratedProgramConstructor := by
    intro constructor equality
    change mapGrammarRule
      (costPresentationSymbols PresentationSymbols.id) constructor = _
        at equality
    rw [costPresentationSymbols_id, mapGrammarRule_id] at equality
    exact equality
  reflectsGeneratedEnvironmentConstructor := by
    intro constructor equality
    change mapGrammarRule
      (costPresentationSymbols PresentationSymbols.id) constructor = _
        at equality
    rw [costPresentationSymbols_id, mapGrammarRule_id] at equality
    exact equality
  mapsGeneratedWrappedLabelMembership := by
    intro sourceLabel
    change (costPresentationSymbols PresentationSymbols.id).constructor
        sourceLabel ∈ _ ↔ sourceLabel ∈ _
    rw [costPresentationSymbols_id]
    rfl
  normalizerNatural := by
    intro free bound sort term
    let structural :=
      (OrderedCIGSLT.Morphism.id source.source).underlying.costWholeStructural
    have symbolsIdentity : structural.symbols = PresentationSymbols.id := by
      exact costPresentationSymbols_id
    have freeEquality : free = free.map structural.symbols := by
      rw [symbolsIdentity]
      exact (WellSorted.FreeTypeContext.map_id free).symm
    have boundEquality :
        bound = bound.map (mapTypeExpr structural.symbols) := by
      rw [symbolsIdentity]
      symm
      calc
        bound.map (mapTypeExpr PresentationSymbols.id) =
            bound.map _root_.id := by
          apply List.map_congr_left
          intro type membership
          exact mapTypeExpr_id type
        _ = bound := List.map_id bound
    have sortEquality : sort = WellSorted.mapLangSort structural sort := by
      apply Subtype.ext
      change sort.1 = structural.symbols.sort sort.1
      rw [symbolsIdentity]
      rfl
    have naturality :=
      source.compactOutput.toCIGSLT.openCanonical.normalize_reindex
        freeEquality boundEquality sortEquality term
    have mappedInputEquality :
        ReflectiveWellSorted.OpenTerm.map structural
            (CostGeneratedReflectiveScopePreserving.id source.source.toCIGSLT)
            term =
          term.reindex freeEquality boundEquality sortEquality := by
      apply Subtype.ext
      calc
        (ReflectiveWellSorted.OpenTerm.map structural
            (CostGeneratedReflectiveScopePreserving.id
              source.source.toCIGSLT) term).1 =
            mapPattern structural.symbols term.1 := rfl
        _ = term.1 := by rw [symbolsIdentity, mapPattern_id]
        _ = (term.reindex freeEquality boundEquality sortEquality).1 :=
          (ReflectiveWellSorted.OpenTerm.reindex_pattern _ _ _ _).symm
    change source.normalizeOpen
        (ReflectiveWellSorted.OpenTerm.map structural _ term) =
      ReflectiveWellSorted.OpenTerm.map structural _
        (source.normalizeOpen term)
    apply Subtype.ext
    rw [mappedInputEquality]
    have rawNaturality := congrArg Subtype.val naturality
    calc
      (source.normalizeOpen
          (term.reindex freeEquality boundEquality sortEquality)).1 =
        ((source.normalizeOpen term).reindex freeEquality boundEquality
          sortEquality).1 := rawNaturality
      _ = (source.normalizeOpen term).1 :=
        ReflectiveWellSorted.OpenTerm.reindex_pattern _ _ _ _
      _ = mapPattern structural.symbols (source.normalizeOpen term).1 := by
        rw [symbolsIdentity, mapPattern_id]
      _ = (ReflectiveWellSorted.OpenTerm.map structural _
          (source.normalizeOpen term)).1 := rfl
  quoteFaithful := by
    intro left right equality
    apply Subtype.ext
    apply Subtype.ext
    change mapPattern (costPresentationSymbols PresentationSymbols.id)
        left.1.1 =
      mapPattern (costPresentationSymbols PresentationSymbols.id) right.1.1
        at equality
    simpa [costPresentationSymbols_id] using equality

/-- Assemble the unique compact continued Cost map selected by the source
arrow and its explicit semantic admission laws.  No output morphism is
stored in `CostOneMorphismLaws`. -/
def toCompactCIGSLTMorphism
    {source target : CostOneDomainObject}
    {underlying : OrderedCIGSLT.Morphism source.source target.source}
    (laws : CostOneMorphismLaws source target underlying) :
    CIGSLT.Morphism source.compactOutput.toCIGSLT
      target.compactOutput.toCIGSLT where
  underlying := underlying.underlying.costIGSLTMorphism
    laws.preservesGeneratedBisim
  reflectionSymbols :=
    (costReflectiveSymbols underlying.underlying.reflectiveSymbols).reflection
  mapsReflectivePresentations := by
    intro declaration membership
    exact underlying.underlying.mapsCostStaticReflectivePresentations
      declaration membership
  mapsReflectiveRules := by
    intro declaration membership
    exact underlying.underlying.mapsCostInteractionReflectiveRules
      declaration membership
  mapsReflectiveScope := laws.preservesGeneratedReflectiveScope
  mapsCoreSort := underlying.underlying.mapsCostCoreSort
  mapsCoreContactConstructor :=
    underlying.underlying.mapsCostCoreContactConstructor
  mapsCorePattern := underlying.underlying.mapsCostCorePattern
  mapsSourceEnvelope := underlying.underlying.mapsCostSourceEnvelope
  reflectsInteractingSort :=
    underlying.underlying.reflectsCostInteractingSort
  mapsWrappedLabelMembership := laws.mapsGeneratedWrappedLabelMembership
  reflectsProgramConstructor := laws.reflectsGeneratedProgramConstructor
  reflectsEnvironmentConstructor :=
    laws.reflectsGeneratedEnvironmentConstructor
  mapsProgramConstructor := underlying.underlying.mapsCostProgramConstructor
  mapsEnvironmentConstructor :=
    underlying.underlying.mapsCostEnvironmentConstructor
  mapsProgramContinuationIndex :=
    underlying.underlying.mapsCostProgramContinuationIndex
  mapsEnvironmentContinuationIndex :=
    underlying.underlying.mapsCostEnvironmentContinuationIndex
  mapsProgramKind := underlying.underlying.mapsCostProgramKind
  mapsEnvironmentKind := underlying.underlying.mapsCostEnvironmentKind
  mapsProgramSchema := underlying.underlying.mapsCostProgramSchema
  mapsEnvironmentSchema := underlying.underlying.mapsCostEnvironmentSchema
  mapsProgramContinuation :=
    underlying.underlying.mapsCostProgramContinuation
  mapsEnvironmentContinuation :=
    underlying.underlying.mapsCostEnvironmentContinuation
  mapsProgramSubject := underlying.underlying.mapsCostProgramSubject
  mapsEnvironmentSubject := underlying.underlying.mapsCostEnvironmentSubject
  mapsOpenCanonical := laws.normalizerNatural
  quoteFaithful := laws.quoteFaithful

/-- The admissible generated Cost laws are closed under composition.  The
normalizer square is composed in the indexed open-term fibres; the explicit
reindexing below is proof-only and does not alter the represented pattern. -/
def comp {first second third : CostOneDomainObject}
    {left : OrderedCIGSLT.Morphism first.source second.source}
    {right : OrderedCIGSLT.Morphism second.source third.source}
    (leftLaws : CostOneMorphismLaws first second left)
    (rightLaws : CostOneMorphismLaws second third right) :
    CostOneMorphismLaws first third
      (OrderedCIGSLT.Morphism.comp left right) where
  preservesGeneratedBisim := CostGeneratedBisimPreserving.comp
    leftLaws.preservesGeneratedBisim rightLaws.preservesGeneratedBisim
  preservesGeneratedReflectiveScope :=
    CostGeneratedReflectiveScopePreserving.comp
      leftLaws.preservesGeneratedReflectiveScope
      rightLaws.preservesGeneratedReflectiveScope
  reflectsGeneratedProgramConstructor := by
    intro constructor equality
    change mapGrammarRule
        (costPresentationSymbols
          (left.underlying.underlying.structural.structural.symbols.comp
            right.underlying.underlying.structural.structural.symbols))
        constructor = _ at equality
    rw [costPresentationSymbols_comp, mapGrammarRule_comp] at equality
    exact leftLaws.reflectsGeneratedProgramConstructor constructor
      (rightLaws.reflectsGeneratedProgramConstructor _ equality)
  reflectsGeneratedEnvironmentConstructor := by
    intro constructor equality
    change mapGrammarRule
        (costPresentationSymbols
          (left.underlying.underlying.structural.structural.symbols.comp
            right.underlying.underlying.structural.structural.symbols))
        constructor = _ at equality
    rw [costPresentationSymbols_comp, mapGrammarRule_comp] at equality
    exact leftLaws.reflectsGeneratedEnvironmentConstructor constructor
      (rightLaws.reflectsGeneratedEnvironmentConstructor _ equality)
  mapsGeneratedWrappedLabelMembership := by
    intro sourceLabel
    change (costPresentationSymbols
        (left.underlying.underlying.structural.structural.symbols.comp
          right.underlying.underlying.structural.structural.symbols)).constructor
          sourceLabel ∈ _ ↔ sourceLabel ∈ _
    rw [costPresentationSymbols_comp]
    change (costPresentationSymbols
        right.underlying.underlying.structural.structural.symbols).constructor
          ((costPresentationSymbols
            left.underlying.underlying.structural.structural.symbols).constructor
              sourceLabel) ∈ _ ↔ sourceLabel ∈ _
    rw [rightLaws.mapsGeneratedWrappedLabelMembership,
      leftLaws.mapsGeneratedWrappedLabelMembership]
  normalizerNatural := by
    intro free bound sort term
    let firstStructural := left.underlying.costWholeStructural
    let secondStructural := right.underlying.costWholeStructural
    let compositeStructural :=
      (OrderedCIGSLT.Morphism.comp left right).underlying.costWholeStructural
    have symbolsComposite : compositeStructural.symbols =
        firstStructural.symbols.comp secondStructural.symbols := by
      exact costPresentationSymbols_comp
        left.underlying.underlying.structural.structural.symbols
        right.underlying.underlying.structural.structural.symbols
    let firstMapped := term.map firstStructural
      leftLaws.preservesGeneratedReflectiveScope
    let nestedMapped := firstMapped.map secondStructural
      rightLaws.preservesGeneratedReflectiveScope
    let nestedNormalized :=
      ((first.normalizeOpen term).map firstStructural
        leftLaws.preservesGeneratedReflectiveScope).map secondStructural
          rightLaws.preservesGeneratedReflectiveScope
    have rightNaturality := rightLaws.normalizerNatural firstMapped
    have leftNaturality := congrArg
      (fun mapped => mapped.map secondStructural
        rightLaws.preservesGeneratedReflectiveScope)
      (leftLaws.normalizerNatural term)
    have combined : third.normalizeOpen nestedMapped = nestedNormalized :=
      rightNaturality.trans leftNaturality
    have freeEquality :
        (free.map firstStructural.symbols).map secondStructural.symbols =
          free.map compositeStructural.symbols := by
      calc
        (free.map firstStructural.symbols).map secondStructural.symbols =
            free.map
              (firstStructural.symbols.comp secondStructural.symbols) :=
          (WellSorted.FreeTypeContext.map_comp free
            firstStructural.symbols secondStructural.symbols).symm
        _ = free.map compositeStructural.symbols := by
          rw [symbolsComposite]
    have boundCompositeToNested :
        bound.map
            (mapTypeExpr
              (firstStructural.symbols.comp secondStructural.symbols)) =
          (bound.map (mapTypeExpr firstStructural.symbols)).map
            (mapTypeExpr secondStructural.symbols) := by
      induction bound with
      | nil => rfl
      | cons type bound inductionHypothesis =>
          simp [mapTypeExpr_comp]
    have boundEquality :
        (bound.map (mapTypeExpr firstStructural.symbols)).map
            (mapTypeExpr secondStructural.symbols) =
          bound.map (mapTypeExpr compositeStructural.symbols) := by
      calc
        (bound.map (mapTypeExpr firstStructural.symbols)).map
              (mapTypeExpr secondStructural.symbols) =
            bound.map (mapTypeExpr
              (firstStructural.symbols.comp secondStructural.symbols)) :=
          boundCompositeToNested.symm
        _ = bound.map (mapTypeExpr compositeStructural.symbols) := by
          rw [symbolsComposite]
    have sortEquality :
        WellSorted.mapLangSort secondStructural
            (WellSorted.mapLangSort firstStructural sort) =
          WellSorted.mapLangSort compositeStructural sort := by
      apply Subtype.ext
      change secondStructural.symbols.sort
          (firstStructural.symbols.sort sort.1) =
        compositeStructural.symbols.sort sort.1
      rw [symbolsComposite]
      rfl
    have normalizationTransport :=
      third.compactOutput.toCIGSLT.openCanonical.normalize_reindex
        freeEquality boundEquality sortEquality nestedMapped
    change third.normalizeOpen
        (nestedMapped.reindex freeEquality boundEquality sortEquality) =
      (third.normalizeOpen nestedMapped).reindex freeEquality boundEquality
        sortEquality at normalizationTransport
    have transportedCombined := congrArg
      (ReflectiveWellSorted.OpenTerm.reindex freeEquality boundEquality
        sortEquality) combined
    have fiberNaturality := normalizationTransport.trans transportedCombined
    have compositeScope : CostGeneratedReflectiveScopePreserving
        (OrderedCIGSLT.Morphism.comp left right).underlying :=
      CostGeneratedReflectiveScopePreserving.comp
        leftLaws.preservesGeneratedReflectiveScope
        rightLaws.preservesGeneratedReflectiveScope
    let compositeMapped := term.map compositeStructural compositeScope
    let compositeNormalized := (first.normalizeOpen term).map
      compositeStructural compositeScope
    have inputEquality :
        nestedMapped.reindex freeEquality boundEquality sortEquality =
          compositeMapped := by
      apply Subtype.ext
      calc
        (nestedMapped.reindex freeEquality boundEquality sortEquality).1 =
            nestedMapped.1 :=
          ReflectiveWellSorted.OpenTerm.reindex_pattern _ _ _ _
        _ = mapPattern secondStructural.symbols
            (mapPattern firstStructural.symbols term.1) := rfl
        _ = mapPattern
            (firstStructural.symbols.comp secondStructural.symbols)
            term.1 :=
          (mapPattern_comp firstStructural.symbols
            secondStructural.symbols term.1).symm
        _ = mapPattern compositeStructural.symbols term.1 := by
          rw [symbolsComposite]
        _ = compositeMapped.1 := rfl
    have outputEquality :
        nestedNormalized.reindex freeEquality boundEquality sortEquality =
          compositeNormalized := by
      apply Subtype.ext
      calc
        (nestedNormalized.reindex freeEquality boundEquality sortEquality).1 =
            nestedNormalized.1 :=
          ReflectiveWellSorted.OpenTerm.reindex_pattern _ _ _ _
        _ = mapPattern secondStructural.symbols
            (mapPattern firstStructural.symbols
              (first.normalizeOpen term).1) := rfl
        _ = mapPattern
            (firstStructural.symbols.comp secondStructural.symbols)
            (first.normalizeOpen term).1 :=
          (mapPattern_comp firstStructural.symbols
            secondStructural.symbols _).symm
        _ = mapPattern compositeStructural.symbols
            (first.normalizeOpen term).1 := by
          rw [symbolsComposite]
        _ = compositeNormalized.1 := rfl
    change third.normalizeOpen compositeMapped = compositeNormalized
    exact (congrArg third.normalizeOpen inputEquality.symm).trans
      (fiberNaturality.trans outputEquality)
  quoteFaithful := by
    intro leftKey rightKey equality
    apply (CIGSLT.Morphism.comp
      leftLaws.toCompactCIGSLTMorphism
      rightLaws.toCompactCIGSLTMorphism).quoteFaithful
    change mapPattern
        ((costPresentationSymbols
          left.underlying.underlying.structural.structural.symbols).comp
          (costPresentationSymbols
            right.underlying.underlying.structural.structural.symbols))
        leftKey.1.1 =
      mapPattern
        ((costPresentationSymbols
          left.underlying.underlying.structural.structural.symbols).comp
          (costPresentationSymbols
            right.underlying.underlying.structural.structural.symbols))
        rightKey.1.1
    rw [← costPresentationSymbols_comp]
    exact equality

/-- The constructed compact Cost map sends the admissible identity laws to
the continued identity. -/
@[simp]
theorem toCompactCIGSLTMorphism_id (source : CostOneDomainObject) :
    (id source).toCompactCIGSLTMorphism =
      CIGSLT.Morphism.id source.compactOutput.toCIGSLT := by
  apply CIGSLT.Morphism.ext
  · apply IGSLT.Morphism.ext
    exact CIGSLT.Morphism.costWholeInteractive_id source.source.toCIGSLT
  · change (costReflectiveSymbols
        ReflectionExtension.ReflectiveSymbols.id).reflection =
      ReflectionExtension.ReflectionSymbols.id
    exact congrArg ReflectionExtension.ReflectiveSymbols.reflection
      costReflectiveSymbols_id

/-- The constructed compact Cost map sends composed admissible laws to the
composite of the constructed compact maps. -/
theorem toCompactCIGSLTMorphism_comp
    {first second third : CostOneDomainObject}
    {left : OrderedCIGSLT.Morphism first.source second.source}
    {right : OrderedCIGSLT.Morphism second.source third.source}
    (leftLaws : CostOneMorphismLaws first second left)
    (rightLaws : CostOneMorphismLaws second third right) :
    (comp leftLaws rightLaws).toCompactCIGSLTMorphism =
      CIGSLT.Morphism.comp leftLaws.toCompactCIGSLTMorphism
        rightLaws.toCompactCIGSLTMorphism := by
  apply CIGSLT.Morphism.ext
  · apply IGSLT.Morphism.ext
    exact CIGSLT.Morphism.costWholeInteractive_comp left.underlying
      right.underlying
  · change (costReflectiveSymbols
        (left.underlying.reflectiveSymbols.comp
          right.underlying.reflectiveSymbols)).reflection =
      ((costReflectiveSymbols left.underlying.reflectiveSymbols).reflection.comp
        (costReflectiveSymbols
          right.underlying.reflectiveSymbols).reflection)
    exact congrArg ReflectionExtension.ReflectiveSymbols.reflection
      (costReflectiveSymbols_comp left.underlying.reflectiveSymbols
        right.underlying.reflectiveSymbols)

end CostOneMorphismLaws

/-- Ordered admission for a generated compact Cost map.  Monotonicity is an
arrow law rather than object data: an arbitrary injective symbol translation
need not preserve the fixed structural order on canonical keys. -/
structure CostOneOrderedMorphismLaws
    (source target : CostOneDomainObject)
    (underlying : OrderedCIGSLT.Morphism source.source target.source) : Prop
    extends CostOneMorphismLaws source target underlying where
  generatedCanonicalKeyMonotone : Monotone
    (CIGSLT.Morphism.canonicalKeyMap
      toCostOneMorphismLaws.toCompactCIGSLTMorphism)

namespace CostOneOrderedMorphismLaws

/-- Identity is admissible for the generated canonical-key order. -/
def id (source : CostOneDomainObject) :
    CostOneOrderedMorphismLaws source source
      (OrderedCIGSLT.Morphism.id source.source) where
  toCostOneMorphismLaws := CostOneMorphismLaws.id source
  generatedCanonicalKeyMonotone := by
    rw [CostOneMorphismLaws.toCompactCIGSLTMorphism_id]
    intro firstKey secondKey lessOrEqual
    rw [CIGSLT.Morphism.canonicalKeyMap_id,
      CIGSLT.Morphism.canonicalKeyMap_id]
    exact lessOrEqual

/-- Ordered generated Cost admission is closed under composition. -/
def comp {first second third : CostOneDomainObject}
    {left : OrderedCIGSLT.Morphism first.source second.source}
    {right : OrderedCIGSLT.Morphism second.source third.source}
    (leftLaws : CostOneOrderedMorphismLaws first second left)
    (rightLaws : CostOneOrderedMorphismLaws second third right) :
    CostOneOrderedMorphismLaws first third
      (OrderedCIGSLT.Morphism.comp left right) where
  toCostOneMorphismLaws := CostOneMorphismLaws.comp
    leftLaws.toCostOneMorphismLaws rightLaws.toCostOneMorphismLaws
  generatedCanonicalKeyMonotone := by
    rw [CostOneMorphismLaws.toCompactCIGSLTMorphism_comp
      leftLaws.toCostOneMorphismLaws rightLaws.toCostOneMorphismLaws]
    intro firstKey secondKey lessOrEqual
    rw [CIGSLT.Morphism.canonicalKeyMap_comp,
      CIGSLT.Morphism.canonicalKeyMap_comp]
    exact rightLaws.generatedCanonicalKeyMonotone
      (leftLaws.generatedCanonicalKeyMonotone lessOrEqual)

/-- The exact ordered compact-output map constructed from arrow laws. -/
def toCompactOrderedMorphism
    {source target : CostOneDomainObject}
    {underlying : OrderedCIGSLT.Morphism source.source target.source}
    (laws : CostOneOrderedMorphismLaws source target underlying) :
    OrderedCIGSLT.Morphism source.compactOutput target.compactOutput where
  underlying := laws.toCostOneMorphismLaws.toCompactCIGSLTMorphism
  canonicalKeyMonotone := laws.generatedCanonicalKeyMonotone

/-- The constructed ordered output map preserves identity. -/
@[simp]
theorem toCompactOrderedMorphism_id (source : CostOneDomainObject) :
    (id source).toCompactOrderedMorphism =
      OrderedCIGSLT.Morphism.id source.compactOutput := by
  apply OrderedCIGSLT.Morphism.ext
  exact CostOneMorphismLaws.toCompactCIGSLTMorphism_id source

/-- The constructed ordered output map preserves composition. -/
theorem toCompactOrderedMorphism_comp
    {first second third : CostOneDomainObject}
    {left : OrderedCIGSLT.Morphism first.source second.source}
    {right : OrderedCIGSLT.Morphism second.source third.source}
    (leftLaws : CostOneOrderedMorphismLaws first second left)
    (rightLaws : CostOneOrderedMorphismLaws second third right) :
    (comp leftLaws rightLaws).toCompactOrderedMorphism =
      OrderedCIGSLT.Morphism.comp leftLaws.toCompactOrderedMorphism
        rightLaws.toCompactOrderedMorphism := by
  apply OrderedCIGSLT.Morphism.ext
  exact CostOneMorphismLaws.toCompactCIGSLTMorphism_comp
    leftLaws.toCostOneMorphismLaws rightLaws.toCostOneMorphismLaws

end CostOneOrderedMorphismLaws

/-- An arrow between normalizer-indexed Cost₁ objects.  The underlying map is
an ordered continued morphism; every generated Cost field is constructed
from it and the separate law bundle. -/
structure CostOneMorphism (source target : CostOneDomainObject) where
  underlying : OrderedCIGSLT.Morphism source.source target.source
  laws : CostOneOrderedMorphismLaws source target underlying

namespace CostOneMorphism

/-- Cost₁ arrows are determined by their underlying ordered continued map. -/
@[ext]
theorem ext {source target : CostOneDomainObject}
    {first second : CostOneMorphism source target}
    (underlying : first.underlying = second.underlying) : first = second := by
  cases first
  cases second
  cases underlying
  rfl

/-- Identity Cost₁ arrow. -/
def id (source : CostOneDomainObject) : CostOneMorphism source source where
  underlying := OrderedCIGSLT.Morphism.id source.source
  laws := CostOneOrderedMorphismLaws.id source

/-- Composition of Cost₁ arrows. -/
def comp {first second third : CostOneDomainObject}
    (left : CostOneMorphism first second)
    (right : CostOneMorphism second third) : CostOneMorphism first third where
  underlying := OrderedCIGSLT.Morphism.comp left.underlying right.underlying
  laws := CostOneOrderedMorphismLaws.comp left.laws right.laws

/-- Map a Cost₁ arrow to its generated compact-output arrow. -/
def compactOutput {source target : CostOneDomainObject}
    (morphism : CostOneMorphism source target) :
    OrderedCIGSLT.Morphism source.compactOutput target.compactOutput :=
  morphism.laws.toCompactOrderedMorphism

@[simp]
theorem compactOutput_id (source : CostOneDomainObject) :
    (id source).compactOutput =
      OrderedCIGSLT.Morphism.id source.compactOutput :=
  CostOneOrderedMorphismLaws.toCompactOrderedMorphism_id source

theorem compactOutput_comp {first second third : CostOneDomainObject}
    (left : CostOneMorphism first second)
    (right : CostOneMorphism second third) :
    (comp left right).compactOutput =
      OrderedCIGSLT.Morphism.comp left.compactOutput right.compactOutput :=
  CostOneOrderedMorphismLaws.toCompactOrderedMorphism_comp
    left.laws right.laws

end CostOneMorphism

/-- The category on explicitly normalizer-indexed Cost₁ objects and the
arrows along which the generated Cost construction is lawful. -/
instance : CategoryTheory.Category CostOneDomainObject where
  Hom := CostOneMorphism
  id := CostOneMorphism.id
  comp := CostOneMorphism.comp
  id_comp morphism := by
    apply CostOneMorphism.ext
    apply OrderedCIGSLT.Morphism.ext
    apply CIGSLT.Morphism.ext
    · rfl
    · rfl
  comp_id morphism := by
    apply CostOneMorphism.ext
    apply OrderedCIGSLT.Morphism.ext
    apply CIGSLT.Morphism.ext
    · rfl
    · rfl
  assoc first second third := by
    apply CostOneMorphism.ext
    apply OrderedCIGSLT.Morphism.ext
    apply CIGSLT.Morphism.ext
    · rfl
    · rfl

/-- Forget the selected Cost laws while retaining the ordered source. -/
def costOneSourceForget :
    CategoryTheory.Functor CostOneDomainObject OrderedCIGSLT where
  obj source := source.source
  map morphism := morphism.underlying
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Genuine nondegenerate one-step compact Cost functor.  Its codomain is
the ordered continued category, not the Cost₁ domain: closure under a second
compact Cost step is independently refuted for rho. -/
def compactCostOneFunctor :
    CategoryTheory.Functor CostOneDomainObject OrderedCIGSLT where
  obj source := source.compactOutput
  map morphism := morphism.compactOutput
  map_id source := CostOneMorphism.compactOutput_id source
  map_comp left right := CostOneMorphism.compactOutput_comp left right

end Mettapedia.GSLT.LanguageDef
