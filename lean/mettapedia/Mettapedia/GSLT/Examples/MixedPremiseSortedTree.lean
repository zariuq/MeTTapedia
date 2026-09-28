import Mettapedia.GSLT.Examples.MixedPremiseExactChild
import Mettapedia.OSLF.Syntax.ResultSortedScopedFreeModel
import Mettapedia.OSLF.Syntax.SortIndexedScopedTreeLifting
import Mettapedia.OSLF.Syntax.ScopedOperationalFreeModel
import Mettapedia.OSLF.Syntax.ScopedOperationalCertification
import Mettapedia.OSLF.Syntax.ScopedOperationalHistory
import Mettapedia.OSLF.Syntax.SortIndexedScopedFreeModel
import Mettapedia.OSLF.Syntax.ResultSortedScopedHistory

/-!
# Complete sorted trees for the mixed authored firing

The actual two-premise recursive rule selects a beta step under two local
binders. Its root query supplies an event but no recursive child; the scoped
step supplies exactly one child. Both observed root firings therefore admit
complete result-sorted trees whose child is an actual selected beta firing.

Both the beta subtree and the complete root tree preserve their exact
selected runtime histories under the two categorical erasures.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Examples.MixedPremiseSortedClassifier

open Mettapedia.GSLT.Examples.TypedMixedPremiseHistory
open Mettapedia.GSLT.Examples.TypedPartialSpinePremise (wrapped expected step)
open Mettapedia.GSLT.Examples.ScopedLamCongExecution (openRedex betaRule)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.Binding.ScopedOperationalPresentation
open Mettapedia.OSLF.Binding.SortIndexedScopedTreeLifting
open Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation
open Mettapedia.OSLF.Binding.ResultSortedScopedFreeModel
open Mettapedia.OSLF.Binding.ResultSortedScopedHistory
open Mettapedia.OSLF.Binding.ScopedOperationalCertification
open Mettapedia.OSLF.Binding.ScopedOperationalHistory
open Mettapedia.OSLF.Binding.ResultSortedMixedPremises
open Mettapedia.OSLF.Binding.ScopedRuleConstructorFrame
open Mettapedia.TypeTheory

private def term : TypeExpr := .base "Term"

private theorem beta_source_typed :
    HasType recursiveLanguage FreeTypeContext.empty [term, term]
      openRedex term := by
  apply checkHasType_sound
  decide +kernel

private theorem beta_target_typed :
    HasType recursiveLanguage FreeTypeContext.empty [term, term]
      (.bvar 0) term := by
  exact HasType.bvar (by decide)

private theorem beta_shape_canonical
    (raw : RuleSkeleton RuleHistory RelationEnv.empty recursiveLanguage
      2 openRedex (.bvar 0)) :
    ∃ children,
      Mettapedia.OSLF.Binding.ResultSortedScopedPremises.RuleSkeleton.canonicalResultChildren?
        [term, term] raw = some children := by
  have listed := raw.listed
  simp [recursiveLanguage] at listed
  rcases listed with beta | mixed
  · have ruleEq : raw.rule = betaRule := beta.1
    have unique : (raw.rule.typeContext.map Prod.fst).Nodup := by
      rw [ruleEq]
      decide
    have compiled : compileList? recursiveLanguage
        (freeFromRuleContext raw.rule.typeContext) [term, term]
        raw.rule.premises = some [] := by
      rw [ruleEq]
      rfl
    exact Mettapedia.OSLF.Binding.ResultSortedScopedPremises.RuleSkeleton.canonicalResultChildren?_exists_of_compiled
      [term, term] raw unique [] compiled
  · have ruleEq : raw.rule = mixedRule := mixed.1
    have unique : (raw.rule.typeContext.map Prod.fst).Nodup := by
      rw [ruleEq]
      decide
    have compiled : compileList? recursiveLanguage
        (freeFromRuleContext raw.rule.typeContext) [term, term]
        raw.rule.premises =
          some [.relationQuery "eq" [closedIdentity, closedIdentity],
            .step step] := by
      rw [ruleEq]
      decide +kernel
    exact Mettapedia.OSLF.Binding.ResultSortedScopedPremises.RuleSkeleton.canonicalResultChildren?_exists_of_compiled
      [term, term] raw unique _ compiled

/-- Each one-fuel beta firing under the two binders admits a result-sorted
tree whose erasure decodes to that exact selected history. -/
theorem beta_sorted_tree_decodes_execution (history : RuleHistory)
    (selected : (history, .bvar 0) ∈
      rewriteAt RelationEnv.empty recursiveLanguage 1 2 openRedex) :
    ∃ tree :
      (Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation.presentation
        RelationEnv.empty recursiveLanguage FreeTypeContext.empty).Derivation
        () ⟨1, [term, term], term, openRedex, .bvar 0⟩,
      decodeHistory? RelationEnv.empty recursiveLanguage _
        ((Mettapedia.OSLF.Binding.SortIndexedScopedFreeModel.toDepthFreeModel RelationEnv.empty recursiveLanguage).toFun
          () ⟨1, [term, term], openRedex, .bvar 0⟩
          ((toContextSortedFree RelationEnv.empty recursiveLanguage FreeTypeContext.empty).toFun
            () ⟨1, [term, term], term, openRedex, .bvar 0⟩ tree)) =
        some history := by
  obtain ⟨rawDepth, _, decoded⟩ :=
    runtime_to_certified_tree RelationEnv.empty recursiveLanguage
      1 2 openRedex (.bvar 0) history selected
  let sorted := liftTreeAt RelationEnv.empty recursiveLanguage
    ⟨1, [term, term], openRedex, .bvar 0⟩ rawDepth
  have canonical : OneFuelCanonical RelationEnv.empty recursiveLanguage
      [term, term] openRedex (.bvar 0) sorted := by
    match sorted with
    | .roll shape _ => exact beta_shape_canonical shape
  let result := admitOneFuelTree RelationEnv.empty recursiveLanguage
    FreeTypeContext.empty [term, term] term openRedex (.bvar 0)
      beta_source_typed beta_target_typed sorted canonical
  refine ⟨result, ?_⟩
  dsimp only [result]
  rw [admitOneFuelTree_erase, Mettapedia.OSLF.Binding.SortIndexedScopedFreeModel.toDepthFreeModel_tree]
  change decodeHistory? RelationEnv.empty recursiveLanguage
    ⟨1, 2, openRedex, .bvar 0⟩
    (Mettapedia.OSLF.Binding.SortIndexedScopedOperationalPresentation.eraseTree RelationEnv.empty recursiveLanguage
      ⟨1, [term, term], openRedex, .bvar 0⟩
      (liftTreeAt RelationEnv.empty recursiveLanguage
        ⟨1, [term, term], openRedex, .bvar 0⟩ rawDepth)) = some history
  have erased :
      Mettapedia.OSLF.Binding.SortIndexedScopedOperationalPresentation.eraseTree
        RelationEnv.empty recursiveLanguage
          ⟨1, [term, term], openRedex, .bvar 0⟩
          (liftTreeAt RelationEnv.empty recursiveLanguage
            ⟨1, [term, term], openRedex, .bvar 0⟩ rawDepth) = rawDepth := by
    exact erase_liftTreeAt RelationEnv.empty recursiveLanguage
      ⟨1, [term, term], openRedex, .bvar 0⟩ rawDepth
  rw [erased]
  exact decoded

private theorem canonical_mixed_exact_child
    (raw : RuleSkeleton RuleHistory RelationEnv.empty recursiveLanguage
      0 wrapped expected)
    (ruleEq : raw.rule = mixedRule)
    (exactChild : raw.children = [(2, openRedex, .bvar 0)]) :
    Mettapedia.OSLF.Binding.ResultSortedScopedPremises.RuleSkeleton.canonicalResultChildren?
      [] raw = some [⟨[term, term], term, openRedex, .bvar 0⟩] := by
  have premises : raw.rule.premises =
      [.relationQuery "eq" [closedIdentity, closedIdentity],
       .scopedStep step] := by
    rw [ruleEq]
    rfl
  obtain ⟨childSource, childTarget, sorted⟩ :=
    RuleSkeleton.relationQuery_then_scopedStep_result_child
      [] (freeFromRuleContext raw.rule.typeContext) raw premises (by
        rw [ruleEq]
        decide +kernel)
  have unique : (raw.rule.typeContext.map Prod.fst).Nodup := by
    rw [ruleEq]
    decide
  have compiled : compileList? recursiveLanguage
      (freeFromRuleContext raw.rule.typeContext) [] raw.rule.premises =
      some [.relationQuery "eq" [closedIdentity, closedIdentity],
        .step step] := by
    rw [ruleEq]
    decide +kernel
  have canonical :=
    Mettapedia.OSLF.Binding.ResultSortedScopedPremises.RuleSkeleton.canonicalResultChildren?_of_compiled
      [] raw unique _ compiled
  have accepted :
      Mettapedia.OSLF.Binding.ResultSortedScopedPremises.RuleSkeleton.canonicalResultChildren?
        [] raw = some [⟨step.binders, step.resultType,
          childSource, childTarget⟩] := by
    rw [canonical]
    simpa only [List.append_nil] using sorted
  have erasure :=
    Mettapedia.OSLF.Binding.ResultSortedScopedPremises.RuleSkeleton.canonicalResultChildren?_erase
      [] raw [⟨step.binders, step.resultType,
        childSource, childTarget⟩] accepted
  have depth :=
    Mettapedia.OSLF.Binding.SortIndexedScopedOperationalPresentation.RuleSkeleton.sortedChildren_depth
      [] raw
  rw [← erasure, exactChild] at depth
  have endpoints : childSource = openRedex ∧
      childTarget = Pattern.bvar 0 := by
    simpa [Mettapedia.OSLF.Binding.ResultSortedScopedPremises.ResultSortedChild.eraseResult,
      Mettapedia.OSLF.Binding.SortIndexedScopedOperationalPresentation.childDepth,
      step] using depth
  rw [endpoints.1, endpoints.2] at accepted
  have bindersEq : step.binders = [term, term] := by rfl
  have resultEq : step.resultType = term := by rfl
  simpa only [bindersEq, resultEq] using accepted

/-- An actual selected mixed-rule execution has a complete canonical
result-sorted tree that decodes to its exact runtime history. Its sole
recursive branch is the selected one-fuel beta firing at the declared
binder context and result sort. -/
theorem mixed_sorted_tree_decodes_execution
    (history : RuleHistory)
    (selected : (history, expected) ∈
      rewriteAt RelationEnv.empty recursiveLanguage 2 0 wrapped)
    (observedIndex : historyRuleIndex history = 1) :
    ∃ tree :
      (Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation.presentation
        RelationEnv.empty recursiveLanguage FreeTypeContext.empty).Derivation
        () ⟨2, [], term, wrapped, expected⟩,
      decodeSorted? RelationEnv.empty recursiveLanguage
        FreeTypeContext.empty ⟨2, [], term, wrapped, expected⟩ tree =
          some history := by
  obtain ⟨rule, index, listed, firing, ⟨frame⟩,
      historyEq, targetEq⟩ :=
    (mem_rewriteAt_succ_iff_frames RelationEnv.empty recursiveLanguage
      1 0 wrapped expected history).mp selected
  have indexEq : index = 1 := by
    have projected := congrArg historyRuleIndex historyEq
    have observed : historyRuleIndex history = index := by
      simpa [historyRuleIndex] using projected
    exact observed.symm.trans observedIndex
  have ruleEq : rule = mixedRule := by
    have membership := listed
    simp [recursiveLanguage, indexEq] at membership
    exact membership
  cases ruleEq
  cases indexEq
  cases firing with
  | mk captured completed premiseHistory target =>
      dsimp at targetEq
      subst target
      let raw := RuleConstructorFrame.toSkeleton 1 listed frame
      obtain ⟨child, requests, childAmbient, childSource,
          childTarget, _, childSelected⟩ :=
        exact_mixed_frame_child _ frame
      have exactChild : raw.children = [(2, openRedex, .bvar 0)] := by
        rw [RuleConstructorFrame.toSkeleton_children_eq_requests
          1 listed frame, requests]
        simp [childAmbient, childSource, childTarget]
      have canonical := canonical_mixed_exact_child raw rfl exactChild
      have sourceTyped : HasType recursiveLanguage FreeTypeContext.empty
          [] wrapped term := by
        apply checkHasType_sound
        decide +kernel
      have targetTyped : HasType recursiveLanguage FreeTypeContext.empty
          [] expected term := by
        apply checkHasType_sound
        decide +kernel
      let rootShape : RuleShape RelationEnv.empty recursiveLanguage
          FreeTypeContext.empty [] term wrapped expected :=
        ⟨raw, [⟨[term, term], term, openRedex, .bvar 0⟩],
          canonical, sourceTyped, targetTyped⟩
      have betaSelected : (child.evidence, .bvar 0) ∈
          rewriteAt RelationEnv.empty recursiveLanguage 1 2
            openRedex := by
        simpa only [childAmbient, childSource, childTarget]
          using childSelected
      obtain ⟨betaTree, betaDecoded⟩ :=
        beta_sorted_tree_decodes_execution child.evidence betaSelected
      have betaDecoded' : decodeSorted? RelationEnv.empty recursiveLanguage
          FreeTypeContext.empty
            ⟨1, [term, term], term, openRedex, .bvar 0⟩ betaTree =
              some child.evidence := by
        exact betaDecoded
      let rootChildren :
          (position :
            (Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation.presentation
              RelationEnv.empty recursiveLanguage FreeTypeContext.empty).polynomial.Position
                (base := ())
                (index := ⟨2, [], term, wrapped, expected⟩) rootShape) →
          (Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation.presentation
            RelationEnv.empty recursiveLanguage FreeTypeContext.empty).Derivation
            () ((Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation.presentation
              RelationEnv.empty recursiveLanguage FreeTypeContext.empty).polynomial.next
                (base := ()) (index := ⟨2, [], term, wrapped, expected⟩)
                  rootShape position) := fun position => by
        change Fin 1 at position
        have zero : position = 0 := Fin.eq_zero position
        subst position
        change
          (Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation.presentation
            RelationEnv.empty recursiveLanguage FreeTypeContext.empty).Derivation
              () ⟨1, [term, term], term, openRedex, .bvar 0⟩
        exact betaTree
      let rootTree :
          (Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation.presentation
            RelationEnv.empty recursiveLanguage FreeTypeContext.empty).Derivation
            () ⟨2, [], term, wrapped, expected⟩ :=
        IndexedPolynomial.Fix.roll rootShape rootChildren
      refine ⟨rootTree, ?_⟩
      rw [historyEq]
      dsimp only [rootTree]
      have rolled := decodeSorted_roll RelationEnv.empty recursiveLanguage
        FreeTypeContext.empty ⟨2, [], term, wrapped, expected⟩
          rootShape rootChildren
      apply rolled.trans
      have childPoint (position :
          (Mettapedia.OSLF.Binding.ScopedOperationalPresentation.presentation
            RelationEnv.empty recursiveLanguage).polynomial.Position
              (base := ()) (index := ⟨2, 0, wrapped, expected⟩) raw) :
          decodeSorted? RelationEnv.empty recursiveLanguage
            FreeTypeContext.empty
            ((Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation.presentation
              RelationEnv.empty recursiveLanguage FreeTypeContext.empty).polynomial.next
                (base := ()) (index := ⟨2, [], term, wrapped, expected⟩)
                  rootShape
                ((eraseToDepthMap RelationEnv.empty recursiveLanguage
                  FreeTypeContext.empty).onPosition ()
                    ⟨2, [], term, wrapped, expected⟩ rootShape position))
            (rootChildren
              ((eraseToDepthMap RelationEnv.empty recursiveLanguage
                FreeTypeContext.empty).onPosition ()
                  ⟨2, [], term, wrapped, expected⟩ rootShape position)) =
            some child.evidence := by
        let typedPosition :=
          (eraseToDepthMap RelationEnv.empty recursiveLanguage
            FreeTypeContext.empty).onPosition ()
              ⟨2, [], term, wrapped, expected⟩ rootShape position
        have zero : typedPosition = (0 : Fin 1) := by
          change Fin 1 at typedPosition
          exact Fin.eq_zero typedPosition
        change decodeSorted? RelationEnv.empty recursiveLanguage
          FreeTypeContext.empty
          ((Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation.presentation
            RelationEnv.empty recursiveLanguage FreeTypeContext.empty).polynomial.next
              (base := ()) (index := ⟨2, [], term, wrapped, expected⟩)
                rootShape typedPosition)
          (rootChildren typedPosition) = some child.evidence
        rw [zero]
        change decodeSorted? RelationEnv.empty recursiveLanguage
          FreeTypeContext.empty
            ⟨1, [term, term], term, openRedex, .bvar 0⟩ betaTree =
              some child.evidence
        exact betaDecoded'
      let decodedChildren :
          (position :
            (Mettapedia.OSLF.Binding.ScopedOperationalPresentation.presentation
              RelationEnv.empty recursiveLanguage).polynomial.Position
                (base := ()) (index := ⟨2, 0, wrapped, expected⟩) raw) →
            Option RuleHistory := fun position =>
        decodeSorted? RelationEnv.empty recursiveLanguage
          FreeTypeContext.empty
            ((Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation.presentation
              RelationEnv.empty recursiveLanguage FreeTypeContext.empty).polynomial.next
                (base := ()) (index := ⟨2, [], term, wrapped, expected⟩)
                  rootShape
                  ((eraseToDepthMap RelationEnv.empty recursiveLanguage
                    FreeTypeContext.empty).onPosition ()
                      ⟨2, [], term, wrapped, expected⟩ rootShape position))
            (rootChildren
              ((eraseToDepthMap RelationEnv.empty recursiveLanguage
                FreeTypeContext.empty).onPosition ()
                  ⟨2, [], term, wrapped, expected⟩ rootShape position))
      have aligned : List.ofFn decodedChildren =
          (RuleConstructorFrame.childRequests frame).map
            (fun request => some request.evidence) := by
        calc
          List.ofFn decodedChildren =
              List.ofFn (fun _ :
                (Mettapedia.OSLF.Binding.ScopedOperationalPresentation.presentation
                  RelationEnv.empty recursiveLanguage).polynomial.Position
                    (base := ()) (index := ⟨2, 0, wrapped, expected⟩) raw =>
                    some child.evidence) := by
                congr 1
                funext position
                exact childPoint position
          _ = [some child.evidence] := by
                have count :
                    ((Mettapedia.OSLF.Binding.ScopedOperationalPresentation.presentation
                      RelationEnv.empty recursiveLanguage).premises ()
                        ⟨2, 0, wrapped, expected⟩ raw).length = 1 := by
                  change (raw.children.map fun next =>
                    (⟨1, next.1, next.2.1, next.2.2⟩ :
                      Mettapedia.OSLF.Binding.ScopedOperationalPresentation.Judgment)).length = 1
                  simp [exactChild]
                change List.ofFn (fun _ : Fin
                    ((Mettapedia.OSLF.Binding.ScopedOperationalPresentation.presentation
                      RelationEnv.empty recursiveLanguage).premises ()
                        ⟨2, 0, wrapped, expected⟩ raw).length =>
                          some child.evidence) = [some child.evidence]
                conv_lhs => rw [List.ofFn_congr count]
                rfl
          _ = (RuleConstructorFrame.childRequests frame).map
                (fun request => some request.evidence) := by
                rw [requests]
                rfl
      exact Mettapedia.OSLF.Binding.ScopedOperationalHistory.decodeLayer_selected_rule
        RelationEnv.empty recursiveLanguage 1 0 mixedRule 1 listed wrapped
        (⟨captured, completed, premiseHistory, expected⟩ : RuleFiring RuleHistory)
        frame decodedChildren aligned

/-- The earlier existence interface follows from the exact decoder theorem. -/
theorem mixed_sorted_tree_of_execution
    (history : RuleHistory)
    (selected : (history, expected) ∈
      rewriteAt RelationEnv.empty recursiveLanguage 2 0 wrapped)
    (observedIndex : historyRuleIndex history = 1) :
    Nonempty
      ((Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation.presentation
        RelationEnv.empty recursiveLanguage FreeTypeContext.empty).Derivation
        () ⟨2, [], term, wrapped, expected⟩) := by
  obtain ⟨tree, _⟩ :=
    mixed_sorted_tree_decodes_execution history selected observedIndex
  exact ⟨tree⟩

/-- The first root-query choice admits a complete typed firing tree. -/
theorem first_recursive_firing_has_complete_sorted_tree :
    Nonempty
      ((Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation.presentation
        RelationEnv.empty recursiveLanguage FreeTypeContext.empty).Derivation
        () ⟨2, [], term, wrapped, expected⟩) :=
  mixed_sorted_tree_of_execution firstResult.1 first_recursive_firing
    first_result_observation.2.1

/-- The second root-query choice also admits a complete typed firing tree. -/
theorem second_recursive_firing_has_complete_sorted_tree :
    Nonempty
      ((Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation.presentation
        RelationEnv.empty recursiveLanguage FreeTypeContext.empty).Derivation
        () ⟨2, [], term, wrapped, expected⟩) :=
  mixed_sorted_tree_of_execution secondResult.1 second_recursive_firing
    second_result_observation.2.1

/-- The two root-query choices yield distinct complete typed trees at the
same endpoints, since decoding recovers their distinct selected histories. -/
theorem distinct_complete_sorted_firings :
    ∃ first second :
      (Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation.presentation
        RelationEnv.empty recursiveLanguage FreeTypeContext.empty).Derivation
        () ⟨2, [], term, wrapped, expected⟩,
      decodeSorted? RelationEnv.empty recursiveLanguage FreeTypeContext.empty
        ⟨2, [], term, wrapped, expected⟩ first = some firstResult.1 ∧
      decodeSorted? RelationEnv.empty recursiveLanguage FreeTypeContext.empty
        ⟨2, [], term, wrapped, expected⟩ second = some secondResult.1 ∧
      first ≠ second := by
  obtain ⟨first, firstDecodes⟩ := mixed_sorted_tree_decodes_execution
    firstResult.1 first_recursive_firing first_result_observation.2.1
  obtain ⟨second, secondDecodes⟩ := mixed_sorted_tree_decodes_execution
    secondResult.1 second_recursive_firing second_result_observation.2.1
  refine ⟨first, second, firstDecodes, secondDecodes, ?_⟩
  intro equalTrees
  have equalHistories : some firstResult.1 = some secondResult.1 := by
    calc
      some firstResult.1 =
          decodeSorted? RelationEnv.empty recursiveLanguage FreeTypeContext.empty
            ⟨2, [], term, wrapped, expected⟩ first := firstDecodes.symm
      _ = decodeSorted? RelationEnv.empty recursiveLanguage FreeTypeContext.empty
            ⟨2, [], term, wrapped, expected⟩ second := by rw [equalTrees]
      _ = some secondResult.1 := secondDecodes
  exact distinct_recursive_histories (Option.some.inj equalHistories)

/-- Zero fuel cannot fabricate a typed firing tree at these endpoints. -/
theorem no_zero_fuel_sorted_tree :
    ¬ Nonempty
      ((Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation.presentation
        RelationEnv.empty recursiveLanguage FreeTypeContext.empty).Derivation
        () ⟨0, [], term, wrapped, expected⟩) := by
  rintro ⟨tree⟩
  apply Mettapedia.OSLF.Binding.SortIndexedScopedFreeModel.no_zero_fuel_derivation
    RelationEnv.empty recursiveLanguage [] wrapped expected
  exact ⟨(toContextSortedFree RelationEnv.empty recursiveLanguage
    FreeTypeContext.empty).toFun ()
      ⟨0, [], term, wrapped, expected⟩ tree⟩

#print axioms beta_sorted_tree_decodes_execution
#print axioms canonical_mixed_exact_child
#print axioms mixed_sorted_tree_decodes_execution
#print axioms mixed_sorted_tree_of_execution
#print axioms first_recursive_firing_has_complete_sorted_tree
#print axioms second_recursive_firing_has_complete_sorted_tree
#print axioms distinct_complete_sorted_firings
#print axioms no_zero_fuel_sorted_tree

end Mettapedia.GSLT.Examples.MixedPremiseSortedClassifier
