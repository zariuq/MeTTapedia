import Mettapedia.OSLF.Syntax.SortIndexedScopedOperationalPresentation
import Mettapedia.OSLF.Syntax.SortIndexedScopedTreeLifting
import Mettapedia.OSLF.Syntax.SortIndexedScopedFreeModel
import Mettapedia.GSLT.Examples.ScopedLamCongFreeModel
import Mettapedia.GSLT.Examples.CanonicalContextOracle
import Mettapedia.GSLT.LanguageDef.WellSorted
import Mettapedia.OSLF.Syntax.SortIndexedScopedTypingAdmission
import Mettapedia.OSLF.Syntax.ResultSortedScopedPremises
import Mettapedia.OSLF.Syntax.ResultSortedScopedOperationalPresentation
import Mettapedia.OSLF.Syntax.ResultSortedScopedFreeModel

/-!
# The authored LamCong constructor in the sort-indexed presentation

The recursive child of LamCong is a step with the lambda's `Term` binder in
scope. Its free-rule constructor retains that full sort context at the child
judgment, and the established projection returns the previous depth-one
judgment at the same premise position.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Examples.SortIndexedScopedLamCong

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.Binding.SortIndexedScopedOperationalPresentation
open Mettapedia.OSLF.Binding.ResultSortedScopedPremises
open Mettapedia.OSLF.Binding.SortIndexedScopedTreeLifting
open Mettapedia.OSLF.Binding.SortIndexedScopedTypingAdmission
  (EndpointsHaveType admit_one_fuel_nonempty admit_one_fuel_tree
    admit_one_fuel_toRaw toRawFree)
open Mettapedia.GSLT.Examples.ScopedLamCongExecution
open Mettapedia.GSLT.Examples.ScopedLamCongFreeModel

private def rootJudgment : Judgment :=
  ⟨2, [], wrappedRedex, wrappedTarget⟩

/-- The actual authored LamCong constructor has exactly one recursive
child, whose context contains the declared `Term` binder. -/
theorem authored_lamCong_sorted_child :
    ∃ shape : (presentation RelationEnv.empty language).Shape ()
        rootJudgment,
      ∃ childSource childTarget,
        (presentation RelationEnv.empty language).premises ()
          rootJudgment shape =
          [⟨1, [.base "Term"], childSource, childTarget⟩] := by
  obtain ⟨shape, ruleIndex, _, _, _⟩ :=
    authored_lamCong_constructor_has_scoped_child
  have ruleEq : shape.rule = lamCongRule := by
    have listed := shape.listed
    simp [language, ruleIndex] at listed
    exact listed
  have single : shape.rule.premises = [.scopedStep localStep] := by
    rw [ruleEq]
    rfl
  obtain ⟨childSource, childTarget, sorted⟩ :=
    RuleSkeleton.single_scoped_sorted_child [] shape single
  refine ⟨shape, childSource, childTarget, ?_⟩
  change (RuleSkeleton.sortedChildren [] shape).map
      (fun child => (⟨1, child.1, child.2.1, child.2.2⟩ : Judgment)) = _
  rw [sorted]
  rfl

/-- The actual authored LamCong constructor carries both the local binder
sort and the recursive premise's own declared result sort. -/
theorem authored_lamCong_result_sorted_child :
    ∃ shape : (presentation RelationEnv.empty language).Shape ()
        rootJudgment,
      ∃ childSource childTarget,
        Mettapedia.OSLF.Binding.ResultSortedScopedPremises.RuleSkeleton.canonicalResultChildren?
          [] shape =
          some [⟨localStep.binders, localStep.resultType, childSource,
            childTarget⟩] := by
  obtain ⟨shape, ruleIndex, _, _, _⟩ :=
    authored_lamCong_constructor_has_scoped_child
  have ruleEq : shape.rule = lamCongRule := by
    have listed := shape.listed
    simp [language, ruleIndex] at listed
    exact listed
  have single : shape.rule.premises = [.scopedStep localStep] := by
    rw [ruleEq]
    rfl
  obtain ⟨childSource, childTarget, sorted⟩ :=
    Mettapedia.OSLF.Binding.ResultSortedScopedPremises.RuleSkeleton.single_scoped_result_child
      [] (Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise.freeFromRuleContext
        lamCongRule.typeContext)
      shape single (by decide +kernel)
  have unique : (shape.rule.typeContext.map Prod.fst).Nodup := by
    rw [ruleEq]
    decide
  have compiled :
      Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise.compileList?
        language
        (Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise.freeFromRuleContext
          shape.rule.typeContext) [] shape.rule.premises =
        some [.step localStep] := by
    rw [ruleEq]
    decide +kernel
  have canonical :=
    Mettapedia.OSLF.Binding.ResultSortedScopedPremises.RuleSkeleton.canonicalResultChildren?_of_compiled
      [] shape unique [.step localStep] compiled
  refine ⟨shape, childSource, childTarget, ?_⟩
  change
    Mettapedia.OSLF.Binding.ResultSortedScopedPremises.RuleSkeleton.canonicalResultChildren?
      [] shape = _
  rw [canonical]
  simpa only [ruleEq, List.append_nil] using sorted

private def resultRootJudgment :
    Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation.Judgment :=
  ⟨2, [], .base "Term", wrappedRedex, wrappedTarget⟩

/-- The authored LamCong rule supplies a genuine checked constructor of
the result-sorted operational presentation. -/
theorem authored_lamCong_result_sorted_shape :
    Nonempty
      ((Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation.presentation
        RelationEnv.empty language
        Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty).Shape
        () resultRootJudgment) := by
  obtain ⟨raw, ruleIndex, _, _, _⟩ :=
    authored_lamCong_constructor_has_scoped_child
  have ruleEq : raw.rule = lamCongRule := by
    have listed := raw.listed
    simp [language, ruleIndex] at listed
    exact listed
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
  have sourceTyped : Mettapedia.GSLT.LanguageDef.WellSorted.HasType
      language Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
      [] wrappedRedex (.base "Term") := by
    apply Mettapedia.GSLT.LanguageDef.WellSorted.checkHasType_sound
    decide +kernel
  have targetTyped : Mettapedia.GSLT.LanguageDef.WellSorted.HasType
      language Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
      [] wrappedTarget (.base "Term") := by
    apply Mettapedia.GSLT.LanguageDef.WellSorted.checkHasType_sound
    decide +kernel
  change Nonempty
    (Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation.RuleShape
      RelationEnv.empty language
      Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
      [] (.base "Term") wrappedRedex wrappedTarget)
  exact ⟨Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation.RuleShape.ofCompiled
    Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
    [] (.base "Term") raw unique [.step localStep] compiled
    sourceTyped targetTyped⟩

/-- The actual two-layer authored firing lifts to a complete derivation in
the sort-indexed free rule presentation at the closed root context. -/
theorem authored_lamCong_sorted_derivation :
    Nonempty ((presentation RelationEnv.empty language).Derivation ()
      rootJudgment) := by
  exact depth_derivation_has_sorted_lift RelationEnv.empty language
    rootJudgment authored_lamCong_has_free_derivation

/-- Sorting the actual authored two-layer LamCong firing and erasing its
sort annotations recovers the same free proof tree and nested beta history. -/
theorem authored_lamCong_exact_history_survives_sort_lift :
    ∃ tree :
        (Mettapedia.OSLF.Binding.ScopedOperationalPresentation.presentation
          RelationEnv.empty language).Derivation () rootJudgment.depth,
      eraseTree RelationEnv.empty language rootJudgment
        (liftTreeAt RelationEnv.empty language rootJudgment tree) = tree ∧
      Mettapedia.OSLF.Binding.ScopedOperationalHistory.decodeHistory?
        RelationEnv.empty language _
        (eraseTree RelationEnv.empty language rootJudgment
          (liftTreeAt RelationEnv.empty language rootJudgment tree)) =
        some (.fire 1 [.step 0 0 (.fire 0 [])]) := by
  obtain ⟨tree, history⟩ := authored_lamCong_exact_history_derivation
  have roundtrip := erase_liftTreeAt RelationEnv.empty language
    rootJudgment tree
  refine ⟨tree, roundtrip, ?_⟩
  calc
    Mettapedia.OSLF.Binding.ScopedOperationalHistory.decodeHistory?
        RelationEnv.empty language _
        (eraseTree RelationEnv.empty language rootJudgment
          (liftTreeAt RelationEnv.empty language rootJudgment tree)) =
        Mettapedia.OSLF.Binding.ScopedOperationalHistory.decodeHistory?
          RelationEnv.empty language _ tree :=
      congrArg
        (Mettapedia.OSLF.Binding.ScopedOperationalHistory.decodeHistory?
          RelationEnv.empty language rootJudgment.depth) roundtrip
    _ = some (.fire 1 [.step 0 0 (.fire 0 [])]) := by
      simpa only [rootJudgment] using history

/-- The actual authored sorted LamCong tree also survives erasure followed
by sort reconstruction, while its depth projection decodes the same nested
beta history. -/
theorem authored_lamCong_sorted_tree_roundtrips :
    ∃ tree : (presentation RelationEnv.empty language).Derivation ()
        rootJudgment,
      liftTreeAt RelationEnv.empty language rootJudgment
        (eraseTree RelationEnv.empty language rootJudgment tree) = tree ∧
      Mettapedia.OSLF.Binding.ScopedOperationalHistory.decodeHistory?
        RelationEnv.empty language _
        (eraseTree RelationEnv.empty language rootJudgment tree) =
        some (.fire 1 [.step 0 0 (.fire 0 [])]) := by
  obtain ⟨oldTree, _, history⟩ :=
    authored_lamCong_exact_history_survives_sort_lift
  let sortedTree := liftTreeAt RelationEnv.empty language rootJudgment oldTree
  refine ⟨sortedTree, lift_eraseTree RelationEnv.empty language
    rootJudgment sortedTree, ?_⟩
  exact history

/-- Every interpretation of the depth-indexed free operational algebra
agrees on the authored two-level LamCong firing after sort annotation. The
same witness still decodes the exact nested beta history. -/
theorem authored_lamCong_interpretation_agrees
    (target : Mettapedia.OSLF.Binding.IndexedOperationalPresentationCategory.Equipped
      Unit)
    (interpretation :
      Mettapedia.OSLF.Binding.ScopedOperationalFreeModel.freeAuthoredRules
        RelationEnv.empty language ⟶ target) :
    ∃ tree :
        (Mettapedia.OSLF.Binding.ScopedOperationalPresentation.presentation
          RelationEnv.empty language).Derivation () rootJudgment.depth,
      (Mettapedia.OSLF.Binding.SortIndexedScopedFreeModel.toDepthFreeModel
        RelationEnv.empty language ≫ interpretation).toFun () rootJudgment
          (liftTreeAt RelationEnv.empty language rootJudgment tree) =
        interpretation.toFun () rootJudgment.depth tree ∧
      Mettapedia.OSLF.Binding.ScopedOperationalHistory.decodeHistory?
        RelationEnv.empty language _ tree =
        some (.fire 1 [.step 0 0 (.fire 0 [])]) := by
  obtain ⟨tree, history⟩ := authored_lamCong_exact_history_derivation
  refine ⟨tree, ?_, ?_⟩
  · exact Mettapedia.OSLF.Binding.SortIndexedScopedFreeModel.restricted_interpretation_lift
      RelationEnv.empty language target interpretation rootJudgment tree
  · simpa [rootJudgment, Judgment.depth] using history

/-- The actual authored beta execution generates a depth-indexed free
derivation at its open-variable result. -/
theorem authored_beta_open_depth_derivation :
    Nonempty
      ((Mettapedia.OSLF.Binding.ScopedOperationalPresentation.presentation
        RelationEnv.empty language).Derivation ()
        ⟨1, 1, openRedex, .bvar 0⟩) := by
  have output : Pattern.bvar 0 ∈
      (Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.rewriteAt
        RelationEnv.empty language 1 1 openRedex).map Prod.snd := by
    decide +kernel
  obtain ⟨⟨history, target⟩, firing, targetEq⟩ :=
    List.mem_map.mp output
  dsimp at targetEq
  subst target
  exact
    Mettapedia.OSLF.Binding.ScopedOperationalFreeModel.runtime_to_free_derivation
      RelationEnv.empty language 1 1 openRedex (.bvar 0) history firing

/-- Retaining sort names as indices is not yet sort-checked constructor
admission. The raw beta tree exists under an `Other` binder even though the
sort-sensitive oracle refuses that same beta query. This is a concrete
boundary for the next authored-to-semantic classifier comparison. -/
theorem raw_beta_tree_wrong_sort_boundary :
    Nonempty ((presentation RelationEnv.empty language).Derivation ()
      ⟨1, [.base "Other"], openRedex, .bvar 0⟩) ∧
    Mettapedia.GSLT.Examples.CanonicalContextOracle.sortedBetaOracle
      [.base "Other"] openRedex = [] := by
  exact ⟨depth_derivation_has_sorted_lift RelationEnv.empty language
      ⟨1, [.base "Other"], openRedex, .bvar 0⟩
      authored_beta_open_depth_derivation,
    Mettapedia.GSLT.Examples.CanonicalContextOracle.sorted_beta_other_sort⟩

/-- The mismatch is a typing failure, not only an oracle-policy difference:
the raw free model derives a reduct whose bound variable has sort `Other`,
while the authored lambda term sort is `Term`. -/
theorem raw_beta_tree_untyped_target :
    Nonempty ((presentation RelationEnv.empty language).Derivation ()
      ⟨1, [.base "Other"], openRedex, .bvar 0⟩) ∧
    ¬ Mettapedia.GSLT.LanguageDef.WellSorted.HasType language
      Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
      [.base "Other"] (.bvar 0) (.base "Term") := by
  refine ⟨raw_beta_tree_wrong_sort_boundary.1, ?_⟩
  intro typed
  cases typed with
  | bvar lookup => simp at lookup

/-- The result-sorted presentation itself rejects the raw beta constructor
under an `Other` binder when its conclusion claims result sort `Term`. -/
theorem wrong_sort_no_result_sorted_shape :
    ¬ Nonempty
      ((Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation.presentation
        RelationEnv.empty language
        Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty).Shape
        () ⟨1, [.base "Other"], .base "Term", openRedex,
          .bvar 0⟩) := by
  rintro ⟨shape⟩
  exact raw_beta_tree_untyped_target.2 shape.targetTyped

private def betaJudgment : Judgment :=
  ⟨1, [.base "Term"], openRedex, .bvar 0⟩

/-- The same authored beta firing is well typed when the available binder
really has the declared term sort. -/
theorem beta_endpoints_typed :
    EndpointsHaveType language
      Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
      (.base "Term") betaJudgment := by
  constructor
  · apply Mettapedia.GSLT.LanguageDef.WellSorted.checkHasType_sound
    decide +kernel
  · apply Mettapedia.GSLT.LanguageDef.WellSorted.checkHasType_sound
    decide +kernel

private theorem beta_shape_rule_cases
    (shape : Mettapedia.OSLF.Binding.ScopedOperationalPresentation.RuleSkeleton
      Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.RuleHistory
      RelationEnv.empty language 1 openRedex (.bvar 0)) :
    shape.rule = betaRule ∨ shape.rule = lamCongRule := by
  have listed := shape.listed
  simp [language] at listed
  rcases listed with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

/-- Every raw constructor that could occur at the authored beta judgment
has canonically compilable premises in that binder context. -/
private theorem beta_shape_canonical
    (shape : Mettapedia.OSLF.Binding.ScopedOperationalPresentation.RuleSkeleton
      Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.RuleHistory
      RelationEnv.empty language 1 openRedex (.bvar 0)) :
    ∃ children,
      Mettapedia.OSLF.Binding.ResultSortedScopedPremises.RuleSkeleton.canonicalResultChildren?
        [.base "Term"] shape = some children := by
  rcases beta_shape_rule_cases shape with beta | congruence
  · have unique : (shape.rule.typeContext.map Prod.fst).Nodup := by
      rw [beta]
      decide
    have compiled :
        Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise.compileList?
          language
          (Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise.freeFromRuleContext
            shape.rule.typeContext)
          [.base "Term"] shape.rule.premises = some [] := by
      rw [beta]
      rfl
    exact Mettapedia.OSLF.Binding.ResultSortedScopedPremises.RuleSkeleton.canonicalResultChildren?_exists_of_compiled
      [.base "Term"] shape unique [] compiled
  · have unique : (shape.rule.typeContext.map Prod.fst).Nodup := by
      rw [congruence]
      decide
    have compiled :
        Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise.compileList?
          language
          (Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise.freeFromRuleContext
            shape.rule.typeContext)
          [.base "Term"] shape.rule.premises =
            some [.step localStep] := by
      rw [congruence]
      decide +kernel
    exact Mettapedia.OSLF.Binding.ResultSortedScopedPremises.RuleSkeleton.canonicalResultChildren?_exists_of_compiled
      [.base "Term"] shape unique [.step localStep] compiled

private def resultBetaJudgment :
    Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation.Judgment :=
  ⟨1, [.base "Term"], .base "Term", openRedex, .bvar 0⟩

/-- The actual open-variable beta firing enters the new result-sorted free
algebra. Its certificate erases to the same selected raw firing tree, with
the outer lambda's variable still present as the reduct. -/
theorem authored_beta_result_sorted_tree :
    ∃ rawTree : (presentation RelationEnv.empty language).Derivation ()
        betaJudgment,
      ∃ sortedTree :
        (Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation.presentation
          RelationEnv.empty language
          Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty).Derivation
          () resultBetaJudgment,
        (Mettapedia.OSLF.Binding.ResultSortedScopedFreeModel.toContextSortedFree
          RelationEnv.empty language
          Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty).toFun
          () resultBetaJudgment sortedTree = rawTree := by
  obtain ⟨rawTree⟩ := depth_derivation_has_sorted_lift
    RelationEnv.empty language betaJudgment
      authored_beta_open_depth_derivation
  have canonical :
      Mettapedia.OSLF.Binding.ResultSortedScopedFreeModel.OneFuelCanonical
        RelationEnv.empty language [.base "Term"] openRedex (.bvar 0)
        rawTree := by
    match rawTree with
    | .roll shape _ => exact beta_shape_canonical shape
  let sortedTree :=
    Mettapedia.OSLF.Binding.ResultSortedScopedFreeModel.admitOneFuelTree
      RelationEnv.empty language
      Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
      [.base "Term"] (.base "Term") openRedex (.bvar 0)
      beta_endpoints_typed.1 beta_endpoints_typed.2 rawTree canonical
  refine ⟨rawTree, sortedTree, ?_⟩
  exact Mettapedia.OSLF.Binding.ResultSortedScopedFreeModel.admitOneFuelTree_erase
    RelationEnv.empty language
    Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
    [.base "Term"] (.base "Term") openRedex (.bvar 0)
    beta_endpoints_typed.1 beta_endpoints_typed.2 rawTree canonical

/-- This is a genuine inhabitant of the endpoint-admitted authored free
rule algebra, obtained from the running beta execution and its checked
source/result typing derivations. -/
theorem authored_beta_typed_free_derivation :
    Nonempty
      ((Mettapedia.OSLF.Binding.SortIndexedScopedTypingAdmission.presentation
        RelationEnv.empty language
        Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
        (.base "Term")).rules.Fix ()
        ⟨betaJudgment, beta_endpoints_typed⟩) := by
  exact admit_one_fuel_nonempty RelationEnv.empty language
    Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
    (.base "Term") [.base "Term"] openRedex (.bvar 0)
    beta_endpoints_typed
    (depth_derivation_has_sorted_lift RelationEnv.empty language
      betaJudgment authored_beta_open_depth_derivation)

/-- For the running authored beta step, endpoint admission retains a
specific complete free firing tree exactly when certificates are erased. -/
theorem authored_beta_admission_preserves_tree :
    ∃ rawTree : (presentation RelationEnv.empty language).Derivation ()
        betaJudgment,
      ∃ typedTree :
        (Mettapedia.OSLF.Binding.SortIndexedScopedTypingAdmission.presentation
          RelationEnv.empty language
          Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
          (.base "Term")).rules.Fix ()
          ⟨betaJudgment, beta_endpoints_typed⟩,
        (toRawFree RelationEnv.empty language
          Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
          (.base "Term")).toFun ()
          ⟨betaJudgment, beta_endpoints_typed⟩ typedTree = rawTree := by
  obtain ⟨rawTree⟩ := depth_derivation_has_sorted_lift
    RelationEnv.empty language betaJudgment
      authored_beta_open_depth_derivation
  refine ⟨rawTree, admit_one_fuel_tree RelationEnv.empty language
    Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
    (.base "Term") [.base "Term"] openRedex (.bvar 0)
    beta_endpoints_typed rawTree, ?_⟩
  exact admit_one_fuel_toRaw RelationEnv.empty language
    Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
    (.base "Term") [.base "Term"] openRedex (.bvar 0)
    beta_endpoints_typed rawTree

/-- The `Other`-binder raw judgment has no endpoint-admitted index at the
selected authored `Term` result type. -/
theorem wrong_sort_no_typed_index :
    ¬ ∃ admitted :
      (Mettapedia.OSLF.Binding.SortIndexedScopedTypingAdmission.presentation
        RelationEnv.empty language
        Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
        (.base "Term")).Judgment (),
      admitted.1 =
        (⟨1, [.base "Other"], openRedex, .bvar 0⟩ : Judgment) := by
  rintro ⟨⟨judgment, typed⟩, equality⟩
  change judgment =
    (⟨1, [.base "Other"], openRedex, .bvar 0⟩ : Judgment) at equality
  subst judgment
  exact raw_beta_tree_untyped_target.2 typed.2

#print axioms authored_lamCong_sorted_child
#print axioms authored_lamCong_result_sorted_child
#print axioms authored_lamCong_result_sorted_shape
#print axioms authored_lamCong_sorted_derivation
#print axioms authored_lamCong_exact_history_survives_sort_lift
#print axioms authored_lamCong_sorted_tree_roundtrips
#print axioms authored_lamCong_interpretation_agrees
#print axioms raw_beta_tree_wrong_sort_boundary
#print axioms raw_beta_tree_untyped_target
#print axioms wrong_sort_no_result_sorted_shape
#print axioms authored_beta_typed_free_derivation
#print axioms authored_beta_result_sorted_tree
#print axioms authored_beta_admission_preserves_tree
#print axioms wrong_sort_no_typed_index

end Mettapedia.GSLT.Examples.SortIndexedScopedLamCong
