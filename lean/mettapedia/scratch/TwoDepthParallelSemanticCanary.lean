import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryParallelFrontier

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace TwoDepthParallelSemanticCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

def nameType : TypeExpr := .base (costBaseSortName "Name")

def supportedKey : CostStaticAtomKey where
  sourceType := nameType
  sourceSupport := []
  targetType := nameType
  targetSupport := [nameType]
  normal := .bvar 0

def closedKey : CostStaticAtomKey where
  sourceType := nameType
  sourceSupport := []
  targetType := nameType
  targetSupport := []
  normal := .bvar 0

def endpointKey (slot : Fin 2) : CostStaticAtomKey :=
  if slot = 0 then supportedKey else closedKey

def cospan : CostStaticAtomKeyCospan endpointKey endpointKey :=
  CostStaticAtomKeyCospan.ofFunctions endpointKey endpointKey

def firstName : String := cospan.commonAtomName (cospan.leftSlot 0)
def secondName : String := cospan.commonAtomName (cospan.leftSlot 1)

def first : Pattern := .fvar firstName
def second : Pattern := .fvar secondName

def declaration : ReflectivePresentationDecl :=
  costStaticReflectivePresentationDecl rhoCIGSLT .base
    rhoReflectivePresentation

theorem first_support : cospan.commonSupport firstName = [nameType] := by
  unfold firstName
  rw [CostStaticAtomKeyCospan.commonSupport_commonAtomName,
    cospan.leftCommutes]
  simp [endpointKey, supportedKey]

theorem second_support : cospan.commonSupport secondName = [] := by
  unfold secondName
  rw [CostStaticAtomKeyCospan.commonSupport_commonAtomName,
    cospan.leftCommutes]
  simp [endpointKey, closedKey]

theorem first_assignment : cospan.commonAssignment firstName = .bvar 0 := by
  unfold firstName
  rw [CostStaticAtomKeyCospan.commonAssignment_commonAtomName,
    cospan.leftCommutes]
  simp [endpointKey, supportedKey]

theorem second_assignment : cospan.commonAssignment secondName = .bvar 0 := by
  unfold secondName
  rw [CostStaticAtomKeyCospan.commonAssignment_commonAtomName,
    cospan.leftCommutes]
  simp [endpointKey, closedKey]

theorem key_zero_eq :
    cospan.commonSemanticPatternKeyAt rhoCIGSLT 0 first =
      cospan.commonSemanticPatternKeyAt rhoCIGSLT 0 second := by
  rw [cospan.commonSemanticPatternKeyAt_eq_iff]
  simp [first, second, first_support, second_support, first_assignment,
    second_assignment, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]

theorem restore_one_first :
    ReflectiveContextSupport.substituteAt
        rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
        cospan.commonAssignment 1 first = .bvar 0 := by
  simp [first, first_support, first_assignment,
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]

theorem restore_one_second :
    ReflectiveContextSupport.substituteAt
        rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
        cospan.commonAssignment 1 second = .bvar 1 := by
  simp [second, second_support, second_assignment,
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]

theorem canonical_left :
    canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        declaration 0
        (.collection declaration.parallelCollection [first, second] none) =
      .collection declaration.parallelCollection [first, second] none := by
  simp only [canonicalizeByAt, canonicalizeListByAt]
  change collapseParallel declaration
      (normalizeParallelElementsBy
        (cospan.commonSemanticPatternKeyAt rhoCIGSLT 0) declaration
        [first, second]) = _
  rw [show normalizeParallelElementsBy
      (cospan.commonSemanticPatternKeyAt rhoCIGSLT 0) declaration
        [first, second] = [first, second] by
    change Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy
      (cospan.commonSemanticPatternKeyAt rhoCIGSLT 0) [first, second] =
        [first, second]
    exact Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_pair_eq_of_le _ _ _
      (Nat.le_of_eq key_zero_eq)]
  exact collapseParallel_eq_collection_of_length_ge_two declaration (by simp)

theorem canonical_right :
    canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        declaration 0
        (.collection declaration.parallelCollection [second, first] none) =
      .collection declaration.parallelCollection [second, first] none := by
  simp only [canonicalizeByAt, canonicalizeListByAt]
  change collapseParallel declaration
      (normalizeParallelElementsBy
        (cospan.commonSemanticPatternKeyAt rhoCIGSLT 0) declaration
        [second, first]) = _
  rw [show normalizeParallelElementsBy
      (cospan.commonSemanticPatternKeyAt rhoCIGSLT 0) declaration
        [second, first] = [second, first] by
    change Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy
      (cospan.commonSemanticPatternKeyAt rhoCIGSLT 0) [second, first] =
        [second, first]
    exact Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_pair_eq_of_le _ _ _
      (Nat.le_of_eq key_zero_eq.symm)]
  exact collapseParallel_eq_collection_of_length_ge_two declaration (by simp)

noncomputable def separatedParallel :
    CostStaticAtomKeyCospan.TwoDepthApex rhoCIGSLT cospan declaration 1 0
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        declaration 0
        (.collection declaration.parallelCollection [first, second] none))
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        declaration 0
        (.collection declaration.parallelCollection [second, first] none)) := by
  apply CostStaticAtomKeyCospan.TwoDepthApex.parallel
  · simpa [canonicalizeListByAt, canonicalizeByAt, parallelContents,
      parallelSplice, first, second] using
      (CostStaticAtomKeyCospan.TwoDepthApex.reflList cospan declaration 1 0
        [first, second])
  · simpa [canonicalizeListByAt, canonicalizeByAt, parallelContents,
      parallelSplice, first, second] using
      (List.Perm.swap first second []).symm

theorem separatedParallel_not_restored_equal :
    ReflectiveContextSupport.substituteAt
        rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
        cospan.commonAssignment 1
        (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
          declaration 0
          (.collection declaration.parallelCollection [first, second] none)) ≠
      ReflectiveContextSupport.substituteAt
        rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
        cospan.commonAssignment 1
        (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
          declaration 0
          (.collection declaration.parallelCollection [second, first] none)) := by
  rw [canonical_left, canonical_right]
  simp [ReflectiveContextSupport.substituteAt, restore_one_first,
    restore_one_second]

end TwoDepthParallelSemanticCanary
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
