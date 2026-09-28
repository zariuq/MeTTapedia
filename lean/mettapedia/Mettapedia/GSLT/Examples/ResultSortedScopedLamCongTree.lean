import Mettapedia.GSLT.Examples.SortIndexedScopedLamCong
import Mettapedia.GSLT.Examples.ScopedLamCongExactFrame

/-!
# Complete result-sorted LamCong firing under its binder

The selected two-layer authored execution has one recursive premise at the
open beta judgment. The source declaration fixes that premise's binder and
result sorts. The corresponding beta tree therefore fills the exact child
position of a checked LamCong constructor in the result-sorted free model.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Examples.ResultSortedScopedLamCongTree

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.GSLT.Examples.ScopedLamCongExecution
open Mettapedia.GSLT.Examples.ScopedLamCongExactFrame
open Mettapedia.GSLT.Examples.SortIndexedScopedLamCong

private abbrev term : TypeExpr := .base "Term"

/-- The exact authored parent constructor has precisely the canonical
result-sorted child needed by its selected beta premise. The endpoint
comparison uses the previously proved depth and result-sort erasures. -/
theorem canonical_exact_child
    (raw : Mettapedia.OSLF.Binding.ScopedOperationalPresentation.RuleSkeleton
      Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.RuleHistory
      RelationEnv.empty language 0 wrappedRedex wrappedTarget)
    (indexEq : raw.ruleIndex = 1)
    (exactChild : raw.children = [(1, openRedex, .bvar 0)]) :
    Mettapedia.OSLF.Binding.ResultSortedScopedPremises.RuleSkeleton.canonicalResultChildren?
      [] raw = some [⟨[term], term, openRedex, .bvar 0⟩] := by
  have ruleEq : raw.rule = lamCongRule := by
    have listed := raw.listed
    simp [language, indexEq] at listed
    exact listed
  have single : raw.rule.premises = [.scopedStep localStep] := by
    rw [ruleEq]
    rfl
  obtain ⟨childSource, childTarget, sorted⟩ :=
    Mettapedia.OSLF.Binding.ResultSortedScopedPremises.RuleSkeleton.single_scoped_result_child
      []
      (Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise.freeFromRuleContext
        raw.rule.typeContext) raw single (by
          rw [ruleEq]
          decide +kernel)
  have unique : (raw.rule.typeContext.map Prod.fst).Nodup := by
    rw [ruleEq]
    decide
  have compiled :
      Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise.compileList?
        language
        (Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise.freeFromRuleContext
          raw.rule.typeContext) [] raw.rule.premises =
        some [.step localStep] := by
    rw [ruleEq]
    decide +kernel
  have canonical :=
    Mettapedia.OSLF.Binding.ResultSortedScopedPremises.RuleSkeleton.canonicalResultChildren?_of_compiled
      [] raw unique [.step localStep] compiled
  have accepted :
      Mettapedia.OSLF.Binding.ResultSortedScopedPremises.RuleSkeleton.canonicalResultChildren?
        [] raw =
          some [⟨localStep.binders, localStep.resultType,
            childSource, childTarget⟩] := by
    rw [canonical]
    simpa only [List.append_nil] using sorted
  have erasure :=
    Mettapedia.OSLF.Binding.ResultSortedScopedPremises.RuleSkeleton.canonicalResultChildren?_erase
      [] raw [⟨localStep.binders, localStep.resultType,
        childSource, childTarget⟩] accepted
  have depth :=
    Mettapedia.OSLF.Binding.SortIndexedScopedOperationalPresentation.RuleSkeleton.sortedChildren_depth
      [] raw
  rw [← erasure, exactChild] at depth
  have endpoints : childSource = openRedex ∧
      childTarget = Pattern.bvar 0 := by
    simpa [Mettapedia.OSLF.Binding.ResultSortedScopedPremises.ResultSortedChild.eraseResult,
      Mettapedia.OSLF.Binding.SortIndexedScopedOperationalPresentation.childDepth,
      localStep] using depth
  rw [endpoints.1, endpoints.2] at accepted
  exact accepted

private def root :
    Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation.Judgment :=
  ⟨2, [], term, wrappedRedex, wrappedTarget⟩

/-- The actual two-layer authored LamCong execution enters the complete
result-sorted free rule algebra. Its child is the open beta tree under the
declared `Term` binder; the outer reduct remains a closed lambda. -/
theorem authored_lamCong_result_sorted_tree :
    Nonempty
      ((Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation.presentation
        RelationEnv.empty language
        Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty).Derivation
        () root) := by
  obtain ⟨raw, indexEq, exactChild⟩ := raw_exact_shape
  have sourceTyped : Mettapedia.GSLT.LanguageDef.WellSorted.HasType
      language Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
      [] wrappedRedex term := by
    apply Mettapedia.GSLT.LanguageDef.WellSorted.checkHasType_sound
    decide +kernel
  have targetTyped : Mettapedia.GSLT.LanguageDef.WellSorted.HasType
      language Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
      [] wrappedTarget term := by
    apply Mettapedia.GSLT.LanguageDef.WellSorted.checkHasType_sound
    decide +kernel
  let shape : Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation.RuleShape
      RelationEnv.empty language
      Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
      [] term wrappedRedex wrappedTarget :=
    ⟨raw, [⟨[term], term, openRedex, .bvar 0⟩],
      canonical_exact_child raw indexEq exactChild,
      sourceTyped, targetTyped⟩
  obtain ⟨_, betaTree, _⟩ := authored_beta_result_sorted_tree
  refine ⟨Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll shape ?_⟩
  intro position
  change Fin 1 at position
  have positionZero : position = 0 := Fin.eq_zero position
  subst position
  change
    (Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation.presentation
      RelationEnv.empty language
      Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty).Derivation
      () ⟨1, [term], term, openRedex, Pattern.bvar 0⟩
  exact betaTree

#print axioms canonical_exact_child
#print axioms authored_lamCong_result_sorted_tree

end Mettapedia.GSLT.Examples.ResultSortedScopedLamCongTree
