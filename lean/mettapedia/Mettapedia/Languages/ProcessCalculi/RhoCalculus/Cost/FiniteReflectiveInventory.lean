import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.FiniteWhole
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalInventorySubstitution

/-!
# Actual synchronous generated Name-result inventory

The complete generated declaration list, including synchronous output and
all apparatus constructors, has exactly two Name-result rows. Both are
quotation boundaries. The source Drop-support law is constructed separately
from the source inventory; it is not asserted for arbitrary mixed-color
normalization in the target.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.FiniteReflectiveInventory
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Reflection
open ContinuationDecorationProfile ReflectionExtension

/-- Executable filtering covers the entire actual generated grammar. -/
theorem name_rows : communicationDecoration.costWholeLanguage.terms.filter
    (fun rule => rule.category == costBaseSortName "Name") =
    [communicationDecoration.baseConstructor rhoCalc.terms[2],
      costWrappedConstructor (theory := rhoSyncIGSLT) rhoCalc.terms[2]] := by
  decide +kernel

theorem nameResultsQuoted : ReflectiveNameResultsQuoted
    (profile := communicationDecoration.costWholeReflectionProfile FiniteWhole.sourceReflection.1)
    communicationDecoration.costWholeLanguage := by
  intro declaration selected rule member category
  have nameSort : declaration.nameSort = costBaseSortName "Name" := by
    simp only [FiniteWhole.sourceReflection, costWholeReflectionProfile,
      costStaticReflectivePresentations, rhoReflectionProfile, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at selected
    rcases selected with rfl | rfl <;> rfl
  have selectedRow : rule ∈ communicationDecoration.costWholeLanguage.terms.filter
      (fun row => row.category == costBaseSortName "Name") :=
    List.mem_filter.mpr ⟨member, beq_iff_eq.mpr (category.trans nameSort)⟩
  rw [name_rows] at selectedRow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at selectedRow
  rcases selectedRow with rfl | rfl
  · constructor
    · decide +kernel
    · have params : (communicationDecoration.baseConstructor rhoCalc.terms[2]).params =
          [.simple "p" (.base (costBaseSortName "Proc"))] := by decide +kernel
      simp only [UsesBareCollection, params, List.cons.injEq, TermParam.simple.injEq,
        reduceCtorEq, and_false, false_and]
      simp
  · constructor
    · decide +kernel
    · have params : (costWrappedConstructor (theory := rhoSyncIGSLT) rhoCalc.terms[2]).params =
          [.simple "p" (.base costWrappedSortName)] := by decide +kernel
      simp only [UsesBareCollection, params, List.cons.injEq, TermParam.simple.injEq,
        reduceCtorEq, and_false, false_and]
      simp

/-- Synchronous source canonicalization exposes only a typed supported Name
through Drop, including when other source syntax uses POutputK. -/
theorem sourceDropCanonicalSupportStable :
    ReflectiveDropCanonicalSupportStable (profile := rhoReflectionProfile) rhoSyncCalc :=
  CanonicalInventory.synchronous.dropCanonicalSupportStable

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.FiniteReflectiveInventory
