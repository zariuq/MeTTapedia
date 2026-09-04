import Mathlib.Tactic
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostKeyedFixedPointFalsifier

namespace Scratch.CostDepthApexProbe

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

def shiftingKey : CostStaticAtomKey where
  sourceType := .base "T"
  sourceSupport := []
  targetType := .base "T"
  targetSupport := []
  normal := .bvar 0

def stableKey : CostStaticAtomKey where
  sourceType := .base "T"
  sourceSupport := []
  targetType := .base "T"
  targetSupport := []
  normal := .fvar ""

def endpointKey (slot : Fin 2) : CostStaticAtomKey :=
  if slot.1 = 0 then shiftingKey else stableKey

def cospan : CostStaticAtomKeyCospan endpointKey endpointKey where
  commonKeys := [shiftingKey, stableKey]
  commonNodup := by
    simp [shiftingKey, stableKey]
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
    · intro equality
      exact congrArg endpointKey equality
    · intro equality
      fin_cases first <;> fin_cases second <;>
        simp [endpointKey, shiftingKey, stableKey] at equality ⊢
  rightExtensional := by
    intro first second
    constructor
    · intro equality
      exact congrArg endpointKey equality
    · intro equality
      fin_cases first <;> fin_cases second <;>
        simp [endpointKey, shiftingKey, stableKey] at equality ⊢
  crossExtensional := by
    intro left right
    constructor
    · intro equality
      exact congrArg endpointKey equality
    · intro equality
      fin_cases left <;> fin_cases right <;>
        simp [endpointKey, shiftingKey, stableKey] at equality ⊢

def firstAtom : Pattern :=
  .fvar (cospan.commonAtomName (cospan.leftSlot 0))

def secondAtom : Pattern :=
  .fvar (cospan.commonAtomName (cospan.leftSlot 1))

def raw : Pattern := .collection .hashBag [firstAtom, secondAtom] none

def keyed (depth : Nat) : Pattern :=
  canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
    rhoReflectivePresentation.toReflectivePresentationDecl depth raw

def restored (keyDepth restoreDepth : Nat) : Pattern :=
  ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeLanguage
    cospan.commonSupport cospan.commonAssignment restoreDepth (keyed keyDepth)

@[simp] theorem commonSupport_first :
    cospan.commonSupport (cospan.commonAtomName (cospan.leftSlot 0)) = [] := by
  rw [cospan.commonSupport_commonAtomName, cospan.leftCommutes]
  rfl

@[simp] theorem commonSupport_second :
    cospan.commonSupport (cospan.commonAtomName (cospan.leftSlot 1)) = [] := by
  rw [cospan.commonSupport_commonAtomName, cospan.leftCommutes]
  rfl

@[simp] theorem commonAssignment_first :
    cospan.commonAssignment (cospan.commonAtomName (cospan.leftSlot 0)) =
      .bvar 0 := by
  rw [cospan.commonAssignment_commonAtomName, cospan.leftCommutes]
  rfl

@[simp] theorem commonAssignment_second :
    cospan.commonAssignment (cospan.commonAtomName (cospan.leftSlot 1)) =
      .fvar "" := by
  rw [cospan.commonAssignment_commonAtomName, cospan.leftCommutes]
  rfl

theorem restore_first_zero :
    ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeLanguage
      cospan.commonSupport cospan.commonAssignment 0 firstAtom = .bvar 0 := by
  simp only [firstAtom, ReflectiveContextSupport.substituteAt]
  rw [commonSupport_first, commonAssignment_first]
  simp [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]

theorem restore_first_two :
    ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeLanguage
      cospan.commonSupport cospan.commonAssignment 2 firstAtom = .bvar 2 := by
  simp only [firstAtom, ReflectiveContextSupport.substituteAt]
  rw [commonSupport_first, commonAssignment_first]
  simp [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]

theorem restore_second (depth : Nat) :
    ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeLanguage
      cospan.commonSupport cospan.commonAssignment depth secondAtom =
        .fvar "" := by
  simp only [secondAtom, ReflectiveContextSupport.substituteAt]
  rw [commonSupport_second, commonAssignment_second]
  simp [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]

theorem key_zero_first :
    cospan.commonSemanticPatternKeyAt rhoCIGSLT 0 firstAtom = 0 := by
  simp [CostStaticAtomKeyCospan.commonSemanticPatternKeyAt,
    restore_first_zero, Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode,
    Nat.pair]

theorem key_zero_second :
    cospan.commonSemanticPatternKeyAt rhoCIGSLT 0 secondAtom = 2 := by
  simp [CostStaticAtomKeyCospan.commonSemanticPatternKeyAt,
    restore_second, Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode,
    Mettapedia.OSLF.MeTTaIL.PatternCode.stringCode,
    Mettapedia.OSLF.MeTTaIL.PatternCode.charListCode, Nat.pair]

theorem key_two_first :
    cospan.commonSemanticPatternKeyAt rhoCIGSLT 2 firstAtom = 4 := by
  simp [CostStaticAtomKeyCospan.commonSemanticPatternKeyAt,
    restore_first_two, Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode,
    Nat.pair]

theorem key_two_second :
    cospan.commonSemanticPatternKeyAt rhoCIGSLT 2 secondAtom = 2 := by
  simp [CostStaticAtomKeyCospan.commonSemanticPatternKeyAt,
    restore_second, Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode,
    Mettapedia.OSLF.MeTTaIL.PatternCode.stringCode,
    Mettapedia.OSLF.MeTTaIL.PatternCode.charListCode, Nat.pair]

theorem sorted_zero :
    Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy
        (cospan.commonSemanticPatternKeyAt rhoCIGSLT 0)
        [firstAtom, secondAtom] = [firstAtom, secondAtom] := by
  apply Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_pair_eq_of_le
  simp [key_zero_first, key_zero_second]

theorem sorted_two :
    Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy
        (cospan.commonSemanticPatternKeyAt rhoCIGSLT 2)
        [firstAtom, secondAtom] = [secondAtom, firstAtom] := by
  simp [Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy, List.mergeSort,
    key_two_first, key_two_second]

@[simp] theorem canonicalize_first (depth : Nat) :
    canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
      rhoReflectivePresentation.toReflectivePresentationDecl depth firstAtom =
        firstAtom := by
  simp [firstAtom, canonicalizeByAt]

@[simp] theorem canonicalize_second (depth : Nat) :
    canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
      rhoReflectivePresentation.toReflectivePresentationDecl depth secondAtom =
        secondAtom := by
  simp [secondAtom, canonicalizeByAt]

theorem keyed_zero_eq :
    keyed 0 = .collection .hashBag [firstAtom, secondAtom] none := by
  unfold keyed raw
  change collapseParallel rhoReflectivePresentation.toReflectivePresentationDecl
      (normalizeParallelElementsBy
        (cospan.commonSemanticPatternKeyAt rhoCIGSLT 0)
        rhoReflectivePresentation.toReflectivePresentationDecl
        (canonicalizeListByAt
          (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
          rhoReflectivePresentation.toReflectivePresentationDecl 0
          [firstAtom, secondAtom])) = _
  rw [show canonicalizeListByAt
      (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
      rhoReflectivePresentation.toReflectivePresentationDecl 0
      [firstAtom, secondAtom] = [firstAtom, secondAtom] by
    simp [canonicalizeListByAt]]
  rw [show normalizeParallelElementsBy
      (cospan.commonSemanticPatternKeyAt rhoCIGSLT 0)
      rhoReflectivePresentation.toReflectivePresentationDecl
      [firstAtom, secondAtom] = [firstAtom, secondAtom] by
    simpa [normalizeParallelElementsBy, parallelSplice, firstAtom, secondAtom]
      using sorted_zero]
  rfl

theorem keyed_two_eq :
    keyed 2 = .collection .hashBag [secondAtom, firstAtom] none := by
  unfold keyed raw
  change collapseParallel rhoReflectivePresentation.toReflectivePresentationDecl
      (normalizeParallelElementsBy
        (cospan.commonSemanticPatternKeyAt rhoCIGSLT 2)
        rhoReflectivePresentation.toReflectivePresentationDecl
        (canonicalizeListByAt
          (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
          rhoReflectivePresentation.toReflectivePresentationDecl 2
          [firstAtom, secondAtom])) = _
  rw [show canonicalizeListByAt
      (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
      rhoReflectivePresentation.toReflectivePresentationDecl 2
      [firstAtom, secondAtom] = [firstAtom, secondAtom] by
    simp [canonicalizeListByAt]]
  rw [show normalizeParallelElementsBy
      (cospan.commonSemanticPatternKeyAt rhoCIGSLT 2)
      rhoReflectivePresentation.toReflectivePresentationDecl
      [firstAtom, secondAtom] = [secondAtom, firstAtom] by
    simpa [normalizeParallelElementsBy, parallelSplice, firstAtom, secondAtom]
      using sorted_two]
  rfl

theorem restored_zero_eq :
    restored 0 0 = .collection .hashBag [.bvar 0, .fvar ""] none := by
  rw [restored, keyed_zero_eq]
  simp [ReflectiveContextSupport.substituteAt, restore_first_zero,
    restore_second]

theorem restored_two_eq :
    restored 2 0 = .collection .hashBag [.fvar "", .bvar 0] none := by
  rw [restored, keyed_two_eq]
  simp [ReflectiveContextSupport.substituteAt, restore_first_zero,
    restore_second]

theorem restored_depths_ne : restored 0 0 ≠ restored 2 0 := by
  rw [restored_zero_eq, restored_two_eq]
  intro equality
  simp at equality

theorem unequal_key_depths_no_common_apex :
    ¬ CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
      rhoReflectivePresentation.toReflectivePresentationDecl 0
      (keyed 0) (keyed 2) := by
  intro apex
  exact restored_depths_ne apex.restored_eq

#eval cospan.commonKeys
#eval firstAtom
#eval secondAtom
#eval cospan.commonSemanticPatternKeyAt rhoCIGSLT 0 firstAtom
#eval cospan.commonSemanticPatternKeyAt rhoCIGSLT 0 secondAtom
#eval cospan.commonSemanticPatternKeyAt rhoCIGSLT 2 firstAtom
#eval cospan.commonSemanticPatternKeyAt rhoCIGSLT 2 secondAtom
#eval keyed 0
#eval keyed 2
#eval restored 0 0
#eval restored 2 0

end Scratch.CostDepthApexProbe
