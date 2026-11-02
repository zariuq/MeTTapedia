import Mettapedia.Languages.ProcessCalculi.CCS.Section
import Mettapedia.GSLT.LanguageDef.Continued.Presentation

/-!
# CCS is a continued interactive GSLT in the sense of the three clauses

The reaction is an interaction cut whose operands are summands of sums; the canonical form of the restriction blocks
is a section of the static equivalence; and the contractum, the two continuations side by side, is covered by the
continuation signature and has the wrapped sort. The reaction's source stays sorted when the two continuations move to
the wrapped fibre: each prefix, a guard, sits in the base copy of its sum.
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
theorem ccs_costBaseSum_params :
    (costBaseConstructor ccsInteractionCut ccsCalc.terms[2]).params =
      [.simple "gs" (.collection .hashBag (.base (costBaseSortName "Guard")))] := by
  decide +kernel

@[simp]
theorem ccs_costBaseAct_params :
    (costBaseConstructor ccsInteractionCut ccsCalc.terms[4]).params =
      [.simple "a" (.base (costBaseSortName "Name")),
        .simple "p" (.base costWrappedSortName)] := by
  decide +kernel

@[simp]
theorem ccs_costBaseCoAct_params :
    (costBaseConstructor ccsInteractionCut ccsCalc.terms[5]).params =
      [.simple "a" (.base (costBaseSortName "Name")),
        .simple "p" (.base costWrappedSortName)] := by
  decide +kernel

/-- The sum in the base copy, around one guard and the other summands, is a process of the base copy. -/
theorem ccsRetyping_sum_typed {guard : Pattern} {others : String}
    (guardTyped : HasType ccsRetyping.generatedLanguage ccsRetyping.generatedFreeContext [] guard
      (.base (costBaseSortName "Guard"))) :
    HasType ccsRetyping.generatedLanguage ccsRetyping.generatedFreeContext []
      (.apply (costBaseConstructorName "CSum") [.collection .hashBag [guard] (some others)])
      (.base (costBaseSortName "Proc")) := by
  apply HasType.constructor (rule := costBaseConstructor ccsInteractionCut ccsCalc.terms[2])
  · exact ccsRetyping.costBaseConstructor_mem_generated ccsCalc.terms[2] ccsSumConstructor.2
  · rintro ⟨parameterName, collectionType, elementType, shape⟩
    change ([] : List TermParam) = _ at shape
    simp at shape
  · rw [ccs_costBaseSum_params]
    exact .cons trivial rfl (HasType.collection (.cons guardTyped (.nil _ _))) .nil

/-- The left side of the reaction stays sorted when the two continuations are moved to the wrapped fibre. -/
theorem ccsRetyping_redexRetypable : ccsRetyping.RedexRetypable := by
  rw [ContinuationRetypingPlan.redexRetypable_def]
  change HasType ccsRetyping.generatedLanguage ccsRetyping.generatedFreeContext []
    (.collection .hashBag
      [.apply (costBaseConstructorName "CSum")
          [.collection .hashBag [.apply (costBaseConstructorName "CAct") [.fvar "a", .fvar "p"]] (some "m")],
        .apply (costBaseConstructorName "CSum")
          [.collection .hashBag [.apply (costBaseConstructorName "CCoAct") [.fvar "a", .fvar "q"]] (some "n")]]
      (some "rest"))
    (.base (costBaseSortName "Proc"))
  apply HasType.collectionConstructor
    (rule := costBaseConstructor ccsInteractionCut ccsCalc.terms[1]) (parameterName := "ps")
  · exact ccsRetyping.costBaseConstructor_mem_generated ccsCalc.terms[1]
      ccsParallelConstructor.2
  · exact ccs_costBasePar_params
  · apply ElementsHaveType.cons
    · apply ccsRetyping_sum_typed
      apply HasType.constructor
        (rule := costBaseConstructor ccsInteractionCut ccsCalc.terms[4])
      · exact ccsRetyping.costBaseConstructor_mem_generated ccsCalc.terms[4]
          ccsActionConstructor.2
      · simp [UsesBareCollection, GrammarRule.bareParams_cons_iff, ccs_costBaseAct_params]
      · rw [ccs_costBaseAct_params]
        exact .cons trivial rfl (HasType.fvar rfl) (.cons trivial rfl (HasType.fvar rfl) .nil)
    · apply ElementsHaveType.cons
      · apply ccsRetyping_sum_typed
        apply HasType.constructor
          (rule := costBaseConstructor ccsInteractionCut ccsCalc.terms[5])
        · exact ccsRetyping.costBaseConstructor_mem_generated ccsCalc.terms[5]
            ccsCoActionConstructor.2
        · simp [UsesBareCollection, GrammarRule.bareParams_cons_iff, ccs_costBaseCoAct_params]
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
