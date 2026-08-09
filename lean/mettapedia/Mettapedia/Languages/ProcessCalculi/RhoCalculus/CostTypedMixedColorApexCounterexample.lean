import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostKeyedFixedPointFalsifier

/-!
# A typed mixed-colour boundary for common restoration

Typing the endpoint patterns is not by itself enough to synchronize the
semantic-key depth used below a foreign quote.  This module strengthens the
proof-free depth counterexample to genuine typed semantic atoms and typed rho
Cost patterns.  The positive theorem required by hereditary normalization
must therefore use the actual same-colour static-region decomposition, which
makes a foreign-colour static subtree opaque before ordering its parent.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.GSLT.LanguageDef.CostStaticAtomKeyCospan

namespace CostTypedMixedColorApexCounterexample

private def processType : TypeExpr := .base (costBaseSortName "Proc")

/-- Target context used to type the depth-stable restored atom. -/
def typedApexTargetFree : FreeTypeContext :=
  FreeTypeContext.ofList [("", processType)]

/-- A typed atom retaining one process binder.  Restoring it at different
visible depths shifts its bound variable by different amounts. -/
def typedApexShiftingAtom :
    TypedCostStaticAtom rhoCIGSLT .base typedApexTargetFree where
  key :=
    { sourceType := processType
      sourceSupport := [processType]
      targetType := processType
      targetSupport := [processType]
      normal := .bvar 0 }
  normalWellSorted := by
    refine ⟨⟨.bvar (by simp [processType]), ?_, ?_, rfl⟩, ?_⟩
    · simp [Pattern.hasCanonicalBinderMetadata]
    · simp [isObjectPattern]
    · intro presentation membership
      simp [Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeAt]

/-- A typed process atom whose restored value is independent of depth. -/
def typedApexStableAtom :
    TypedCostStaticAtom rhoCIGSLT .base typedApexTargetFree where
  key :=
    { sourceType := processType
      sourceSupport := []
      targetType := processType
      targetSupport := []
      normal := .fvar "" }
  normalWellSorted := by
    refine ⟨⟨.fvar (by simp [typedApexTargetFree, processType,
      FreeTypeContext.ofList]), ?_, ?_, rfl⟩, ?_⟩
    · simp [Pattern.hasCanonicalBinderMetadata]
    · simp [isObjectPattern]
    · intro presentation membership
      simp [Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeAt]

/-- The two proof-relevant typed keys, exposed as a finite endpoint family. -/
def typedApexEndpointKey (slot : Fin 2) : CostStaticAtomKey :=
  if slot.1 = 0 then typedApexShiftingAtom.key else typedApexStableAtom.key

/-- Identity cospan on the two typed semantic keys. -/
def typedApexCospan :
    CostStaticAtomKeyCospan typedApexEndpointKey typedApexEndpointKey where
  commonKeys := [typedApexShiftingAtom.key, typedApexStableAtom.key]
  commonNodup := by
    simp [typedApexShiftingAtom, typedApexStableAtom, processType]
  leftSlot := fun slot => slot
  rightSlot := fun slot => slot
  leftCommutes := by
    intro slot
    fin_cases slot <;> rfl
  rightCommutes := by
    intro slot
    fin_cases slot <;> rfl
  leftExtensional := by
    intro first second
    constructor
    · exact congrArg typedApexEndpointKey
    · intro equality
      fin_cases first <;> fin_cases second <;>
        simp [typedApexEndpointKey, typedApexShiftingAtom,
          typedApexStableAtom, processType] at equality ⊢
  rightExtensional := by
    intro first second
    constructor
    · exact congrArg typedApexEndpointKey
    · intro equality
      fin_cases first <;> fin_cases second <;>
        simp [typedApexEndpointKey, typedApexShiftingAtom,
          typedApexStableAtom, processType] at equality ⊢
  crossExtensional := by
    intro left right
    constructor
    · exact congrArg typedApexEndpointKey
    · intro equality
      fin_cases left <;> fin_cases right <;>
        simp [typedApexEndpointKey, typedApexShiftingAtom,
          typedApexStableAtom, processType] at equality ⊢

/-- Common spelling of the binder-sensitive typed atom. -/
def typedApexFirstAtom : Pattern :=
  .fvar (typedApexCospan.commonAtomName (typedApexCospan.leftSlot 0))

/-- Common spelling of the stable typed atom. -/
def typedApexSecondAtom : Pattern :=
  .fvar (typedApexCospan.commonAtomName (typedApexCospan.leftSlot 1))

/-- A typed base-process parallel whose semantic order changes with depth. -/
def typedApexRaw : Pattern :=
  .collection .hashBag [typedApexFirstAtom, typedApexSecondAtom] none

private theorem rhoRuleThree_mem : rhoCalc.terms[3] ∈ rhoCalc.terms :=
  List.getElem_mem _

private theorem typedApexFirstAtom_typed :
    HasType rhoCIGSLT.costWholeLanguage typedApexCospan.commonTargetFreeContext
      [] typedApexFirstAtom processType := by
  apply HasType.fvar
  simp [typedApexCospan, typedApexShiftingAtom, processType]

private theorem typedApexSecondAtom_typed :
    HasType rhoCIGSLT.costWholeLanguage typedApexCospan.commonTargetFreeContext
      [] typedApexSecondAtom processType := by
  apply HasType.fvar
  simp [typedApexCospan, typedApexStableAtom, processType]

/-- The depth-sensitive frame is a genuine base rho process. -/
theorem typedApexRaw_typed :
    HasType rhoCIGSLT.costWholeLanguage typedApexCospan.commonTargetFreeContext
      [] typedApexRaw processType := by
  apply HasType.collectionConstructor
      (rule := costBaseConstructor rhoInteractionCut rhoCalc.terms[3])
      (parameterName := "ps") (elementType := processType)
  · exact rhoCIGSLT.costBaseConstructor_mem_costWhole _ rhoRuleThree_mem
  · simp [processType, rho_costBaseParallelConstructor_params]
  · exact .cons typedApexFirstAtom_typed
      (.cons typedApexSecondAtom_typed (.nil [] _))

private def wrappedDeclaration : ReflectivePresentationDecl :=
  costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
    rhoReflectivePresentation.toReflectivePresentationDecl

/-- Canonicalize the typed process frame at its visible semantic-key depth. -/
def typedApexKeyed (depth : Nat) : Pattern :=
  canonicalizeByAt (typedApexCospan.commonSemanticPatternKeyAt rhoCIGSLT)
    wrappedDeclaration depth typedApexRaw

/-- Restore one keyed representative at the root comparison depth. -/
def typedApexRestored (keyDepth restoreDepth : Nat) : Pattern :=
  ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeReflectionProfile
    typedApexCospan.commonSupport typedApexCospan.commonAssignment restoreDepth
    (typedApexKeyed keyDepth)

@[simp] theorem typedApex_commonSupport_first :
    typedApexCospan.commonSupport
      (typedApexCospan.commonAtomName (typedApexCospan.leftSlot 0)) =
        [processType] := by
  rw [typedApexCospan.commonSupport_commonAtomName,
    typedApexCospan.leftCommutes]
  rfl

@[simp] theorem typedApex_commonSupport_second :
    typedApexCospan.commonSupport
      (typedApexCospan.commonAtomName (typedApexCospan.leftSlot 1)) = [] := by
  rw [typedApexCospan.commonSupport_commonAtomName,
    typedApexCospan.leftCommutes]
  rfl

@[simp] theorem typedApex_commonAssignment_first :
    typedApexCospan.commonAssignment
      (typedApexCospan.commonAtomName (typedApexCospan.leftSlot 0)) =
        .bvar 0 := by
  rw [typedApexCospan.commonAssignment_commonAtomName,
    typedApexCospan.leftCommutes]
  rfl

@[simp] theorem typedApex_commonAssignment_second :
    typedApexCospan.commonAssignment
      (typedApexCospan.commonAtomName (typedApexCospan.leftSlot 1)) =
        .fvar "" := by
  rw [typedApexCospan.commonAssignment_commonAtomName,
    typedApexCospan.leftCommutes]
  rfl

theorem typedApex_restore_first_zero :
    ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeReflectionProfile
      typedApexCospan.commonSupport typedApexCospan.commonAssignment 0
      typedApexFirstAtom = .bvar 0 := by
  simp only [typedApexFirstAtom, ReflectiveContextSupport.substituteAt]
  rw [typedApex_commonSupport_first, typedApex_commonAssignment_first]
  simp [processType, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]

theorem typedApex_restore_first_three :
    ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeReflectionProfile
      typedApexCospan.commonSupport typedApexCospan.commonAssignment 3
      typedApexFirstAtom = .bvar 2 := by
  simp only [typedApexFirstAtom, ReflectiveContextSupport.substituteAt]
  rw [typedApex_commonSupport_first, typedApex_commonAssignment_first]
  simp [processType, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]

theorem typedApex_restore_second (depth : Nat) :
    ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeReflectionProfile
      typedApexCospan.commonSupport typedApexCospan.commonAssignment depth
      typedApexSecondAtom = .fvar "" := by
  simp only [typedApexSecondAtom, ReflectiveContextSupport.substituteAt]
  rw [typedApex_commonSupport_second, typedApex_commonAssignment_second]
  simp [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]

theorem typedApex_key_zero_first :
    typedApexCospan.commonSemanticPatternKeyAt rhoCIGSLT 0
      typedApexFirstAtom = 0 := by
  simp [CostStaticAtomKeyCospan.commonSemanticPatternKeyAt,
    typedApex_restore_first_zero,
    Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode, Nat.pair]

theorem typedApex_key_zero_second :
    typedApexCospan.commonSemanticPatternKeyAt rhoCIGSLT 0
      typedApexSecondAtom = 2 := by
  simp [CostStaticAtomKeyCospan.commonSemanticPatternKeyAt,
    typedApex_restore_second,
    Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode,
    Mettapedia.OSLF.MeTTaIL.PatternCode.stringCode,
    Mettapedia.OSLF.MeTTaIL.PatternCode.charListCode, Nat.pair]

theorem typedApex_key_three_first :
    typedApexCospan.commonSemanticPatternKeyAt rhoCIGSLT 3
      typedApexFirstAtom = 4 := by
  simp [CostStaticAtomKeyCospan.commonSemanticPatternKeyAt,
    typedApex_restore_first_three,
    Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode, Nat.pair]

theorem typedApex_key_three_second :
    typedApexCospan.commonSemanticPatternKeyAt rhoCIGSLT 3
      typedApexSecondAtom = 2 := by
  simp [CostStaticAtomKeyCospan.commonSemanticPatternKeyAt,
    typedApex_restore_second,
    Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode,
    Mettapedia.OSLF.MeTTaIL.PatternCode.stringCode,
    Mettapedia.OSLF.MeTTaIL.PatternCode.charListCode, Nat.pair]

theorem typedApex_sorted_zero :
    Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy
        (typedApexCospan.commonSemanticPatternKeyAt rhoCIGSLT 0)
        [typedApexFirstAtom, typedApexSecondAtom] =
      [typedApexFirstAtom, typedApexSecondAtom] := by
  apply Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_pair_eq_of_le
  simp [typedApex_key_zero_first, typedApex_key_zero_second]

theorem typedApex_sorted_three :
    Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy
        (typedApexCospan.commonSemanticPatternKeyAt rhoCIGSLT 3)
        [typedApexFirstAtom, typedApexSecondAtom] =
      [typedApexSecondAtom, typedApexFirstAtom] := by
  simp [Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy, List.mergeSort,
    typedApex_key_three_first, typedApex_key_three_second]

@[simp] theorem typedApex_canonicalize_first (depth : Nat) :
    canonicalizeByAt (typedApexCospan.commonSemanticPatternKeyAt rhoCIGSLT)
        wrappedDeclaration depth typedApexFirstAtom = typedApexFirstAtom := by
  simp [typedApexFirstAtom, canonicalizeByAt]

@[simp] theorem typedApex_canonicalize_second (depth : Nat) :
    canonicalizeByAt (typedApexCospan.commonSemanticPatternKeyAt rhoCIGSLT)
        wrappedDeclaration depth typedApexSecondAtom = typedApexSecondAtom := by
  simp [typedApexSecondAtom, canonicalizeByAt]

theorem typedApex_keyed_zero_eq :
    typedApexKeyed 0 = .collection .hashBag
      [typedApexFirstAtom, typedApexSecondAtom] none := by
  unfold typedApexKeyed typedApexRaw
  change collapseParallel wrappedDeclaration
      (normalizeParallelElementsBy
        (typedApexCospan.commonSemanticPatternKeyAt rhoCIGSLT 0)
        wrappedDeclaration
        (canonicalizeListByAt
          (typedApexCospan.commonSemanticPatternKeyAt rhoCIGSLT)
          wrappedDeclaration 0
          [typedApexFirstAtom, typedApexSecondAtom])) = _
  rw [show canonicalizeListByAt
      (typedApexCospan.commonSemanticPatternKeyAt rhoCIGSLT)
      wrappedDeclaration 0 [typedApexFirstAtom, typedApexSecondAtom] =
        [typedApexFirstAtom, typedApexSecondAtom] by
    simp [canonicalizeListByAt]]
  rw [show normalizeParallelElementsBy
      (typedApexCospan.commonSemanticPatternKeyAt rhoCIGSLT 0)
      wrappedDeclaration [typedApexFirstAtom, typedApexSecondAtom] =
        [typedApexFirstAtom, typedApexSecondAtom] by
    simpa [normalizeParallelElementsBy, parallelSplice,
      typedApexFirstAtom, typedApexSecondAtom] using typedApex_sorted_zero]
  rfl

theorem typedApex_keyed_three_eq :
    typedApexKeyed 3 = .collection .hashBag
      [typedApexSecondAtom, typedApexFirstAtom] none := by
  unfold typedApexKeyed typedApexRaw
  change collapseParallel wrappedDeclaration
      (normalizeParallelElementsBy
        (typedApexCospan.commonSemanticPatternKeyAt rhoCIGSLT 3)
        wrappedDeclaration
        (canonicalizeListByAt
          (typedApexCospan.commonSemanticPatternKeyAt rhoCIGSLT)
          wrappedDeclaration 3
          [typedApexFirstAtom, typedApexSecondAtom])) = _
  rw [show canonicalizeListByAt
      (typedApexCospan.commonSemanticPatternKeyAt rhoCIGSLT)
      wrappedDeclaration 3 [typedApexFirstAtom, typedApexSecondAtom] =
        [typedApexFirstAtom, typedApexSecondAtom] by
    simp [canonicalizeListByAt]]
  rw [show normalizeParallelElementsBy
      (typedApexCospan.commonSemanticPatternKeyAt rhoCIGSLT 3)
      wrappedDeclaration [typedApexFirstAtom, typedApexSecondAtom] =
        [typedApexSecondAtom, typedApexFirstAtom] by
    simpa [normalizeParallelElementsBy, parallelSplice,
      typedApexFirstAtom, typedApexSecondAtom] using typedApex_sorted_three]
  rfl

theorem typedApex_restored_zero_eq :
    typedApexRestored 0 0 =
      .collection .hashBag [.bvar 0, .fvar ""] none := by
  rw [typedApexRestored, typedApex_keyed_zero_eq]
  simp [ReflectiveContextSupport.substituteAt,
    typedApex_restore_first_zero, typedApex_restore_second]

theorem typedApex_restored_three_eq :
    typedApexRestored 3 0 =
      .collection .hashBag [.fvar "", .bvar 0] none := by
  rw [typedApexRestored, typedApex_keyed_three_eq]
  simp [ReflectiveContextSupport.substituteAt,
    typedApex_restore_first_zero, typedApex_restore_second]

/-- Typed semantic atoms do not by themselves synchronize independently
chosen semantic-key depths at a parallel root. -/
theorem typedApex_unequalKeyDepths_no_commonApex :
    ¬ CommonRestorationApex rhoCIGSLT typedApexCospan wrappedDeclaration 0
      (typedApexKeyed 0) (typedApexKeyed 3) := by
  intro apex
  have restored := apex.restored_eq
  change typedApexRestored 0 0 = typedApexRestored 3 0 at restored
  rw [typedApex_restored_zero_eq, typedApex_restored_three_eq] at restored
  simp at restored

/-- The other colour's quote embeds the depth-sensitive base process in the
shared rho name fibre. -/
def typedApexForeignQuote : Pattern :=
  .apply (costBaseConstructorName "NQuote") [typedApexRaw]

/-- The selected wrapped Quote/Drop shell around the foreign quote. -/
def typedApexSelectedQuoteDrop : Pattern :=
  .apply (costWrappedConstructorName "NQuote")
    [.apply (costWrappedConstructorName "PDrop") [typedApexForeignQuote]]

private def nameType : TypeExpr := .base (costBaseSortName "Name")

private def typedApexDropConstructor :
    StructuralMorphism.AuthoredConstructor rhoIGSLT.presentation.presentation :=
  ⟨rhoCalc.terms[1], List.getElem_mem _⟩

private theorem typedApexDrop_selected :
    typedApexDropConstructor ∈
      rhoContinuationRetyping.wrappedConstructors := by
  apply (rhoContinuationRetyping.mem_wrappedConstructors_iff
    typedApexDropConstructor).2
  constructor <;> decide

private def typedApexQuoteConstructor :
    StructuralMorphism.AuthoredConstructor rhoIGSLT.presentation.presentation :=
  ⟨rhoCalc.terms[2], List.getElem_mem _⟩

private theorem typedApexQuote_selected :
    typedApexQuoteConstructor ∈
      rhoContinuationRetyping.wrappedConstructors := by
  apply (rhoContinuationRetyping.mem_wrappedConstructors_iff
    typedApexQuoteConstructor).2
  constructor <;> decide

private theorem typedApexWrappedDrop_mem :
    costWrappedConstructor (theory := rhoIGSLT) rhoCalc.terms[1] ∈
      rhoCIGSLT.costWholeLanguage.terms := by
  change costWrappedConstructor (theory := rhoCIGSLT.theory)
      typedApexDropConstructor.1 ∈ rhoCIGSLT.costWholeLanguage.terms
  exact rhoCIGSLT.costWrappedConstructor_mem_costWhole
    typedApexDropConstructor typedApexDrop_selected

private theorem typedApexWrappedQuote_mem :
    costWrappedConstructor (theory := rhoIGSLT) rhoCalc.terms[2] ∈
      rhoCIGSLT.costWholeLanguage.terms := by
  change costWrappedConstructor (theory := rhoCIGSLT.theory)
      typedApexQuoteConstructor.1 ∈ rhoCIGSLT.costWholeLanguage.terms
  exact rhoCIGSLT.costWrappedConstructor_mem_costWhole
    typedApexQuoteConstructor typedApexQuote_selected

/-- The exposed foreign quote is well typed in the shared name fibre. -/
theorem typedApexForeignQuote_typed :
    HasType rhoCIGSLT.costWholeLanguage typedApexCospan.commonTargetFreeContext
      [] typedApexForeignQuote nameType := by
  apply HasType.constructor
      (rule := costBaseConstructor rhoInteractionCut rhoCalc.terms[2])
  · exact rhoCIGSLT.costBaseConstructor_mem_costWhole _
      (List.getElem_mem _)
  · rw [usesBareCollection_costBaseConstructor_iff]
    simp [UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
      TypeExpr.baseType]
  · rw [rho_costBaseQuoteConstructor_params]
    exact .cons (by trivial) rfl typedApexRaw_typed .nil

private theorem typedApexWrappedDrop_typed :
    HasType rhoCIGSLT.costWholeLanguage typedApexCospan.commonTargetFreeContext
      [] (.apply (costWrappedConstructorName "PDrop") [typedApexForeignQuote])
        (.base costWrappedSortName) := by
  apply HasType.constructor
      (rule := costWrappedConstructor (theory := rhoIGSLT) rhoCalc.terms[1])
  · exact typedApexWrappedDrop_mem
  · rw [usesBareCollection_costWrappedConstructor_iff]
    simp [UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
      TypeExpr.baseType]
  · rw [rho_costWrappedDropConstructor_params]
    exact .cons (by trivial) rfl typedApexForeignQuote_typed .nil

/-- The selected Quote/Drop endpoint inhabits the same shared name fibre. -/
theorem typedApexSelectedQuoteDrop_typed :
    HasType rhoCIGSLT.costWholeLanguage typedApexCospan.commonTargetFreeContext
      [] typedApexSelectedQuoteDrop nameType := by
  apply HasType.constructor
      (rule := costWrappedConstructor (theory := rhoIGSLT) rhoCalc.terms[2])
  · exact typedApexWrappedQuote_mem
  · rw [usesBareCollection_costWrappedConstructor_iff]
    simp [UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
      TypeExpr.baseType]
  · rw [rho_costWrappedQuoteConstructor_params]
    exact .cons (by trivial) rfl typedApexWrappedDrop_typed .nil

/-- Ordinary selected-colour canonicalization identifies the two typed
mixed-colour endpoints. -/
theorem typedApexMixedColor_canonical_eq :
    canonicalize wrappedDeclaration typedApexSelectedQuoteDrop =
      canonicalize wrappedDeclaration typedApexForeignQuote := by
  unfold typedApexSelectedQuoteDrop
  exact canonicalize_quote_drop wrappedDeclaration (by decide)
    typedApexForeignQuote

/-- The selected Quote/Drop shell resets its foreign payload to key depth
zero before exposing it. -/
theorem typedApexSelectedQuoteDrop_keyed_three_eq :
    canonicalizeByAt (typedApexCospan.commonSemanticPatternKeyAt rhoCIGSLT)
        wrappedDeclaration 3 typedApexSelectedQuoteDrop =
      .apply (costBaseConstructorName "NQuote") [typedApexKeyed 0] := by
  unfold typedApexSelectedQuoteDrop typedApexForeignQuote typedApexKeyed
  simp [canonicalizeByAt, canonicalizeListByAt, wrappedDeclaration,
    costStaticReflectivePresentationDecl, costWrappedReflectivePresentationDecl,
    ReflectionExtension.mapReflectivePresentation,
    costWrappedStaticReflectiveSymbols, costWrappedStaticSymbols,
    rhoReflectivePresentation, rhoCIGSLT, rhoIGSLT,
    rhoInteractivePresentation, rhoValidatedLanguageDef, rhoCalc,
    costBaseConstructorName, costBaseConstructorTag,
    costWrappedConstructorName, costWrappedConstructorTag,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply]

/-- Without the selected shell, the foreign quote preserves the ambient key
depth under selected-colour canonicalization. -/
theorem typedApexForeignQuote_keyed_three_eq :
    canonicalizeByAt (typedApexCospan.commonSemanticPatternKeyAt rhoCIGSLT)
        wrappedDeclaration 3 typedApexForeignQuote =
      .apply (costBaseConstructorName "NQuote") [typedApexKeyed 3] := by
  unfold typedApexForeignQuote typedApexKeyed
  simp [canonicalizeByAt, canonicalizeListByAt, wrappedDeclaration,
    costStaticReflectivePresentationDecl, costWrappedReflectivePresentationDecl,
    ReflectionExtension.mapReflectivePresentation,
    costWrappedStaticReflectiveSymbols, costWrappedStaticSymbols,
    rhoReflectivePresentation, rhoCIGSLT, rhoIGSLT,
    rhoInteractivePresentation, rhoValidatedLanguageDef, rhoCalc,
    costBaseConstructorName, costBaseConstructorTag,
    costWrappedConstructorName, costWrappedConstructorTag,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply]

/-- Fully typed counterexample to the broad typed-term apex theorem.

Both endpoints inhabit the same generated rho Cost name fibre and have the
same ordinary selected-colour canonical form.  Nevertheless the selected
Quote/Drop shell and the exposed foreign quote key their common base-process
payload at depths zero and three respectively, producing restorations with
opposite parallel order. -/
theorem typedApex_mixedColor_no_commonApex :
    ¬ CommonRestorationApex rhoCIGSLT typedApexCospan wrappedDeclaration 0
      (canonicalizeByAt
        (typedApexCospan.commonSemanticPatternKeyAt rhoCIGSLT)
        wrappedDeclaration 3 typedApexSelectedQuoteDrop)
      (canonicalizeByAt
        (typedApexCospan.commonSemanticPatternKeyAt rhoCIGSLT)
        wrappedDeclaration 3 typedApexForeignQuote) := by
  rw [typedApexSelectedQuoteDrop_keyed_three_eq,
    typedApexForeignQuote_keyed_three_eq]
  intro apex
  have restored := apex.restored_eq
  simp only [ReflectiveContextSupport.substituteAt, Pattern.apply.injEq,
    true_and, ite_self, List.map_cons, List.map_nil, List.cons.injEq,
    and_true] at restored
  change typedApexRestored 0 0 = typedApexRestored 3 0 at restored
  rw [typedApex_restored_zero_eq, typedApex_restored_three_eq] at restored
  simp at restored

end CostTypedMixedColorApexCounterexample

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
