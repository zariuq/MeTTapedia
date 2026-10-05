import Mettapedia.Languages.ProcessCalculi.CCS.Section
import Mettapedia.GSLT.LanguageDef.Continued.Presentation

/-!
# CCS is a continued interactive GSLT in the sense of the three clauses

Synchronisation is an interaction cut; the bag normal form is a section of
the static equivalence; and the contractum, the two continuations side by
side, is covered by the continuation signature and has the wrapped sort.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.CCS

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.GSLT.LanguageDef.ContinuationRetypingPlan
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Parallel composition is neither of the two prefixes. -/
theorem contact_mem_continuationConstructors :
    ccsParallelConstructor ∈ continuationConstructors ccsInteractionCut := by
  apply (mem_continuationConstructors_iff ccsInteractionCut ccsParallelConstructor).2
  constructor
  · intro equality
    have labels := congrArg (fun constructor => constructor.1.label) equality
    exact absurd labels (by decide : ("CPar" : String) ≠ "CAct")
  · intro equality
    have labels := congrArg (fun constructor => constructor.1.label) equality
    exact absurd labels (by decide : ("CPar" : String) ≠ "CCoAct")

/-- The contractum is covered by the continuation signature. -/
theorem ccsRetyping : ContinuationRetypingPlan ccsInteractionCut :=
  ⟨contact_mem_continuationConstructors⟩

@[simp]
theorem ccs_costBasePar_params :
    (costBaseConstructor ccsInteractionCut ccsCalc.terms[1]).params =
      [.simple "ps" (.collection .hashBag (.base (costBaseSortName "Proc")))] := by
  decide +kernel

@[simp]
theorem ccs_costBaseAct_params :
    (costBaseConstructor ccsInteractionCut ccsCalc.terms[2]).params =
      [.simple "a" (.base (costBaseSortName "Name")),
        .simple "p" (.base costWrappedSortName)] := by
  decide +kernel

@[simp]
theorem ccs_costBaseCoAct_params :
    (costBaseConstructor ccsInteractionCut ccsCalc.terms[3]).params =
      [.simple "a" (.base (costBaseSortName "Name")),
        .simple "p" (.base costWrappedSortName)] := by
  decide +kernel

/-- The left side of synchronisation stays sorted when the two continuations
are moved to the wrapped fibre. -/
theorem ccsRetyping_redexRetypable : ccsRetyping.RedexRetypable := by
  rw [ContinuationRetypingPlan.redexRetypable_def]
  change HasType ccsRetyping.generatedLanguage ccsRetyping.generatedFreeContext []
    (.collection .hashBag
      [.apply (costBaseConstructorName "CAct") [.fvar "a", .fvar "p"],
        .apply (costBaseConstructorName "CCoAct") [.fvar "a", .fvar "q"]] (some "rest"))
    (.base (costBaseSortName "Proc"))
  apply HasType.collectionConstructor
    (rule := costBaseConstructor ccsInteractionCut ccsCalc.terms[1]) (parameterName := "ps")
  · exact ccsRetyping.costBaseConstructor_mem_generated ccsCalc.terms[1]
      ccsParallelConstructor.2
  · exact ccs_costBasePar_params
  · apply ElementsHaveType.cons
    · apply HasType.constructor
        (rule := costBaseConstructor ccsInteractionCut ccsCalc.terms[2])
      · exact ccsRetyping.costBaseConstructor_mem_generated ccsCalc.terms[2]
          ccsActionConstructor.2
      · simp [UsesBareCollection, ccs_costBaseAct_params]
      · rw [ccs_costBaseAct_params]
        exact .cons trivial rfl (HasType.fvar rfl) (.cons trivial rfl (HasType.fvar rfl) .nil)
    · apply ElementsHaveType.cons
      · apply HasType.constructor
          (rule := costBaseConstructor ccsInteractionCut ccsCalc.terms[3])
        · exact ccsRetyping.costBaseConstructor_mem_generated ccsCalc.terms[3]
            ccsCoActionConstructor.2
        · simp [UsesBareCollection, ccs_costBaseCoAct_params]
        · rw [ccs_costBaseCoAct_params]
          exact .cons trivial rfl (HasType.fvar rfl)
            (.cons trivial rfl (HasType.fvar rfl) .nil)
      · exact .nil _ _

/-- The contractum has the wrapped sort. -/
theorem ccsRetyping_wrappable : ccsRetyping.Wrappable := by
  rw [ContinuationRetypingPlan.wrappable_def]
  change HasType ccsRetyping.generatedLanguage ccsRetyping.generatedFreeContext []
    (.collection .hashBag [.fvar "p", .fvar "q"] (some "rest")) (.base costWrappedSortName)
  exact HasType.collectionConstructor
    (rule := costWrappedConstructor (theory := ccsIGSLT) ccsCalc.terms[1])
    (parameterName := "ps")
    (ccsRetyping.costWrappedConstructor_mem_generated ccsParallelConstructor
      contact_mem_continuationConstructors)
    (by rfl)
    (.cons (HasType.fvar rfl) (.cons (HasType.fvar rfl) (.nil _ _)))

/-- The three clauses for CCS. -/
def ccsContinuedPresentation : ContinuedPresentation ccsIGSLT where
  cut := ccsInteractionCut
  canonical := ccsCanonicalSection
  retyping := ContinuationDecorationProfile.ofRetypingPlan ccsRetyping
  redexRetypable :=
    (ContinuationDecorationProfile.ofRetypingPlan_redexRetypable_iff _).mpr
      ccsRetyping_redexRetypable
  wrappable :=
    (ContinuationDecorationProfile.ofRetypingPlan_wrappable_iff _).mpr ccsRetyping_wrappable

/-- **CCS is continued.** -/
theorem ccs_isContinued : IsContinued ccsIGSLT := ⟨ccsContinuedPresentation⟩

end Mettapedia.Languages.ProcessCalculi.CCS
