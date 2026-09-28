import Mettapedia.GSLT.Examples.MixedPremiseSortedClassifier

/-!
# Exact beta child of the mixed authored rule

Every executable mixed-rule frame selects the same binder-local beta
judgment as its recursive premise. The root equality query may have two
different selected events, but it leaves the assignment empty. The inner
step then has a fixed open source and the one-fuel beta evaluator returns
only the bound variable. This proves the endpoint needed to fill the
canonical sorted child's position without inventing a replacement event.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Examples.MixedPremiseSortedClassifier

open Mettapedia.GSLT.Examples.TypedMixedPremiseHistory
open Mettapedia.GSLT.Examples.TypedPartialSpinePremise (wrapped step)
open Mettapedia.GSLT.Examples.ScopedLamCongExecution (openRedex)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.Binding.ScopedStepConstructorFrame
open Mettapedia.OSLF.Binding.ScopedPremiseFrameLists
open Mettapedia.OSLF.Binding.ScopedRuleConstructorFrame
open Mettapedia.OSLF.Binding.ScopedOperationalPresentation

/-- The selected mixed-rule frame has exactly one child request at the
two-binder open beta judgment. Its oracle result has ordinal zero, while
the root-query ordinal remains available to distinguish whole firings. -/
theorem exact_mixed_frame_child (firing : RuleFiring RuleHistory)
    (frame : RuleConstructorFrame
      (rewriteAt RelationEnv.empty recursiveLanguage 1)
      RelationEnv.empty recursiveLanguage 0 mixedRule wrapped firing) :
    ∃ child : ChildRequest RuleHistory,
      Mettapedia.OSLF.Binding.ScopedOperationalPresentation.RuleConstructorFrame.childRequests
        frame = [child] ∧
      child.ambient = 2 ∧ child.source = openRedex ∧
      child.target = .bvar 0 ∧ child.ordinal = 0 ∧
      (child.evidence, child.target) ∈
        rewriteAt RelationEnv.empty recursiveLanguage 1
          child.ambient child.source := by
  rcases frame with ⟨spec, declared, admitted, captured,
    selected, completed, history, run, finished⟩
  have specEq : spec = mixedSpec := by
    have same : some mixedSpec = some spec := by
      simpa [mixedRule] using declared
    exact (Option.some.inj same).symm
  have captureEq : captured = [] := by
    have onlyEmpty : matchRuleAt mixedRule mixedSpec 0 wrapped = [[]] := by
      decide +kernel
    rw [specEq, onlyEmpty] at selected
    simpa using selected
  cases run with
  | cons query rest =>
      rename_i intermediate rootEvent tailHistory
      cases query with
      | relationQuery querySelected =>
          cases rest with
          | cons head tail =>
              cases tail with
              | nil =>
                  cases head with
                  | scopedStep wellScoped child admittedChild =>
                      have rootRows :
                          rootResults (Evidence := RuleHistory)
                            RelationEnv.empty recursiveLanguage mixedSpec
                            0 0 (.relationQuery "eq"
                              [closedIdentity, closedIdentity]) [] =
                            [(.root 0 0, []), (.root 0 1, [])] := by
                        have hRows : premiseStepWithEnv RelationEnv.empty
                            recursiveLanguage [] (.relationQuery "eq"
                              [closedIdentity, closedIdentity]) = [[], []] := by
                          decide +kernel
                        simp [rootResults, mixedSpec, hasOccurrenceAt,
                          projectRoot?, extendRoot?]
                        rw [hRows]
                        rfl
                      have middleEq : intermediate = [] := by
                        rw [specEq, captureEq, rootRows] at querySelected
                        simp at querySelected
                        rcases querySelected with left | right
                        · exact left.2
                        · exact right.2
                      have childAmbient : child.ambient = 2 := by
                        simpa [step] using admittedChild.1
                      have childSource : child.source = openRedex := by
                        have instantiated := admittedChild.2.1
                        rw [specEq, middleEq] at instantiated
                        change instantiateAt? mixedRule mixedSpec
                          0 (.premise 1 0 0) [] 2 [] step.source =
                            some child.source at instantiated
                        have expectedInst : instantiateAt? mixedRule mixedSpec
                            0 (.premise 1 0 0) [] 2 [] step.source =
                              some openRedex := by
                          decide +kernel
                        rw [expectedInst] at instantiated
                        exact (Option.some.inj instantiated).symm
                      have betaTargets :
                          (rewriteAt RelationEnv.empty recursiveLanguage
                            1 2 openRedex).map Prod.snd = [.bvar 0] := by
                        decide +kernel
                      have betaLength :
                          (rewriteAt RelationEnv.empty recursiveLanguage
                            1 2 openRedex).length = 1 := by
                        decide +kernel
                      have selectedChild := admittedChild.2.2.2.1
                      rw [childAmbient, childSource] at selectedChild
                      obtain ⟨bound, equality⟩ :=
                        List.mem_zipIdx' selectedChild
                      have ordinalEq : child.ordinal = 0 := by
                        rw [betaLength] at bound
                        omega
                      have member : (child.evidence, child.target) ∈
                          rewriteAt RelationEnv.empty recursiveLanguage
                            1 2 openRedex := by
                        rw [equality]
                        exact List.getElem_mem bound
                      have targetMember : child.target ∈
                          (rewriteAt RelationEnv.empty recursiveLanguage
                            1 2 openRedex).map Prod.snd :=
                        List.mem_map.mpr
                          ⟨(child.evidence, child.target), member, rfl⟩
                      rw [betaTargets] at targetMember
                      have targetEq : child.target = Pattern.bvar 0 := by
                        simpa using targetMember
                      refine ⟨child, ?_, childAmbient, childSource,
                        targetEq, ordinalEq, ?_⟩
                      · rfl
                      · simpa only [childAmbient, childSource] using member

#print axioms exact_mixed_frame_child

end Mettapedia.GSLT.Examples.MixedPremiseSortedClassifier
