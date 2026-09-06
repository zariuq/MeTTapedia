import Mettapedia.GraphTheory.Walk.Examples
import Mettapedia.GraphTheory.Walk.ProofTheory

/-!
# Positive and negative examples for graph-walk native types

The three-vertex path example now exercises all three layers together:
Mathlib reachability proofs, generated native certificates, and exact GSLT
executions.  The negative examples distinguish endpoint indexing from the
dynamic adjacency guard.
-/

namespace Mettapedia.GraphTheory.Walk.NativeTypeExamples

open Mettapedia.GSLT
open Mettapedia.GraphTheory.Walk.Examples
open Mettapedia.GraphTheory.Walk.LanguageDef
open Mettapedia.GraphTheory.Walk.NativeTypeTheory
open Mettapedia.GraphTheory.Walk.Operational
open Mettapedia.GraphTheory.Walk.ProofTheory
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.PathTypeSynthesis
open Mettapedia.OSLF.MeTTaIL.Syntax
open SimpleGraph

set_option autoImplicit false

def native01 : NativeProof pathGraph vertex0 vertex1 :=
  NativeProof.ofWalk pathGraph walk01

def native12 : NativeProof pathGraph vertex1 vertex2 :=
  NativeProof.ofWalk pathGraph walk12

def native02 : NativeProof pathGraph vertex0 vertex2 :=
  native01.comp native12

theorem native02_witness : native02.walk = walk02 := rfl

theorem native02_is_generated :
    NativeWalk pathGraph pathGraph Hom.id vertex0 vertex2 native02.term :=
  native02.native

theorem native_composition_executes :
    gradedPathDiamond (theory pathGraph pathGraph Hom.id) 5
      (saturatePredicate
        (gradedPathGSLT (theory pathGraph pathGraph Hom.id) 5)
        (fun candidate => candidate = donePattern walk02))
      (appendRequestPattern walk01 walk12) := by
  simpa [walk01, walk12, walk02] using
    (append_inhabits_exact_work_type pathGraph pathGraph Hom.id walk01 walk12)

theorem native_inverse_executes :
    gradedPathDiamond (theory pathGraph pathGraph Hom.id) 4
      (saturatePredicate
        (gradedPathGSLT (theory pathGraph pathGraph Hom.id) 4)
        (fun candidate => candidate = donePattern walk02.reverse))
      (reverseRequestPattern walk02) := by
  simpa [walk02] using
    (reverse_inhabits_exact_work_type pathGraph pathGraph Hom.id walk02)

/-- A valid closed walk occupies the diagonal native fiber. -/
def closedAtOne : NativeClosedWalk pathGraph pathGraph Hom.id vertex1 :=
  closedWalkInhabitant pathGraph pathGraph Hom.id vertex1
    (walk12.append walk12.reverse)

/-- Endpoint indexing is load-bearing independently of execution: the empty
walk at vertex 0 cannot inhabit the `0 → 1` native fiber. -/
theorem wrong_endpoint_not_native :
    ¬ NativeWalk pathGraph pathGraph Hom.id vertex0 vertex1
      (walkPattern (Walk.nil : pathGraph.Walk vertex0 vertex0)) := by
  intro native
  have indexed :=
    (nativeWalk_iff pathGraph pathGraph Hom.id vertex0 vertex1 _).1 native |>.2.1
  rcases indexed with ⟨node, equality⟩
  have endpoints : finPattern vertex0 = finPattern vertex1 := by
    simp only [walkPattern, walkNodePattern, Pattern.apply.injEq,
      List.cons.injEq] at equality
    aesop
  exact (finPattern_ne (by decide)) endpoints

/-- A syntactically formed recursive node that claims the absent edge
`0--2`.  It is intentionally not constructed through `SimpleGraph.Walk`. -/
def forgedWalk02 : Pattern :=
  .apply "WalkValue"
    [finPattern vertex0, finPattern vertex2,
      .apply "WalkCons"
        [finPattern vertex0, finPattern vertex2, finPattern vertex2,
          walkPattern (Walk.nil : pathGraph.Walk vertex2 vertex2)]]

/-- The generated static grammar accepts the forged term: all constructor
sorts are correct.  Its later rejection is therefore genuinely due to the
dynamic adjacency premise. -/
theorem forgedWalk02_has_static_type : grammarWalk forgedWalk02 := by
  unfold grammarWalk
  apply
    Mettapedia.GSLT.LanguageDef.CarrierWellSorted.checkHasType_complete_of_object
  · unfold forgedWalk02
    have startTyped := vertexPattern_typed vertex0.val
    have nextTyped := vertexPattern_typed vertex2.val
    have targetTyped := vertexPattern_typed vertex2.val
    have tailTyped :=
      (walkPattern_and_node_typed
        (Walk.nil : pathGraph.Walk vertex2 vertex2)).1
    have nodeTyped :
        Mettapedia.GSLT.LanguageDef.CarrierWellSorted.HasType language
          Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty []
          (.apply "WalkCons"
            [finPattern vertex0, finPattern vertex2, finPattern vertex2,
              walkPattern (Walk.nil : pathGraph.Walk vertex2 vertex2)])
          (.base "WalkNode") := by
      apply Mettapedia.GSLT.LanguageDef.CarrierWellSorted.HasType.constructor
        (rule := constructor "WalkCons" "WalkNode"
          [parameter "source" "Vertex", parameter "next" "Vertex",
            parameter "target" "Vertex", parameter "tail" "Walk"])
      · simp [language, terms, LanguageDef.ofCore]
      · simp [Mettapedia.GSLT.LanguageDef.WellSorted.UsesBareCollection,
          constructor, parameter]
      · apply
          Mettapedia.GSLT.LanguageDef.CarrierWellSorted.ArgumentsHaveTypes.cons
        · simp [Mettapedia.GSLT.LanguageDef.WellSorted.MatchesParameterRepresentation,
            parameter]
        · rfl
        · exact startTyped
        · apply
            Mettapedia.GSLT.LanguageDef.CarrierWellSorted.ArgumentsHaveTypes.cons
          · simp [Mettapedia.GSLT.LanguageDef.WellSorted.MatchesParameterRepresentation,
              parameter]
          · rfl
          · exact nextTyped
          · apply
              Mettapedia.GSLT.LanguageDef.CarrierWellSorted.ArgumentsHaveTypes.cons
            · simp [Mettapedia.GSLT.LanguageDef.WellSorted.MatchesParameterRepresentation,
                parameter]
            · rfl
            · exact targetTyped
            · apply
                Mettapedia.GSLT.LanguageDef.CarrierWellSorted.ArgumentsHaveTypes.cons
              · simp [Mettapedia.GSLT.LanguageDef.WellSorted.MatchesParameterRepresentation,
                  parameter]
              · rfl
              · exact tailTyped
              · exact
                  Mettapedia.GSLT.LanguageDef.CarrierWellSorted.ArgumentsHaveTypes.nil
    apply Mettapedia.GSLT.LanguageDef.CarrierWellSorted.HasType.constructor
      (rule := constructor "WalkValue" "Walk"
        [parameter "source" "Vertex", parameter "target" "Vertex",
          parameter "node" "WalkNode"])
    · simp [language, terms, LanguageDef.ofCore]
    · simp [Mettapedia.GSLT.LanguageDef.WellSorted.UsesBareCollection,
        constructor, parameter]
    · apply Mettapedia.GSLT.LanguageDef.CarrierWellSorted.ArgumentsHaveTypes.cons
      · simp [Mettapedia.GSLT.LanguageDef.WellSorted.MatchesParameterRepresentation,
          parameter]
      · rfl
      · exact startTyped
      · apply
          Mettapedia.GSLT.LanguageDef.CarrierWellSorted.ArgumentsHaveTypes.cons
        · simp [Mettapedia.GSLT.LanguageDef.WellSorted.MatchesParameterRepresentation,
            parameter]
        · rfl
        · exact targetTyped
        · apply
            Mettapedia.GSLT.LanguageDef.CarrierWellSorted.ArgumentsHaveTypes.cons
          · simp [Mettapedia.GSLT.LanguageDef.WellSorted.MatchesParameterRepresentation,
              parameter]
          · rfl
          · exact nodeTyped
          · exact
              Mettapedia.GSLT.LanguageDef.CarrierWellSorted.ArgumentsHaveTypes.nil
  · simp [forgedWalk02, walkPattern, walkNodePattern, finPattern,
      Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPattern,
      Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPatternList,
      vertexPattern_object]

theorem forgedWalk02_reverse_start :
    rewriteOnce pathGraph pathGraph Hom.id
      (.apply "ReverseRequest" [forgedWalk02]) =
      [uncheckedReverseScanPattern
        (Walk.nil : pathGraph.Walk vertex2 vertex2)
        (Walk.nil : pathGraph.Walk vertex0 vertex0)] := by
  simpa [forgedWalk02, uncheckedReverseScanPattern, walkPattern,
    walkNodePattern] using
    (reverse_raw_start_exact pathGraph pathGraph Hom.id vertex0 vertex2
      (.apply "WalkCons"
        [finPattern vertex0, finPattern vertex2, finPattern vertex2,
          walkPattern (Walk.nil : pathGraph.Walk vertex2 vertex2)]))

/-- The dynamic half of the native type rejects a forged non-edge.  The proof
decomposes the retained path twice: the request reaches the scanner, and the
scanner has no licensed successor because its adjacency premise fails. -/
theorem forged_nonedge_not_native :
    ¬ NativeWalk pathGraph pathGraph Hom.id vertex0 vertex2 forgedWalk02 := by
  intro native
  rcases
      (nativeWalk_iff pathGraph pathGraph Hom.id vertex0 vertex2
        forgedWalk02).1 native with
    ⟨grammar, indexed, result, ⟨path⟩, done⟩
  rcases Mettapedia.GSLT.GSLT.rewritePath_eq_or_first
      (theory pathGraph pathGraph Hom.id) path with
    endpointEquality | ⟨next, first, ⟨rest⟩⟩
  · rw [← endpointEquality] at done
    rcases done with ⟨node, impossible⟩
    simp [forgedWalk02] at impossible
  · have firstMember :=
      (step_iff_mem_rewriteOnce pathGraph pathGraph Hom.id _ _).1 first
    rw [forgedWalk02_reverse_start] at firstMember
    simp only [List.mem_singleton] at firstMember
    subst next
    rcases Mettapedia.GSLT.GSLT.rewritePath_eq_or_first
        (theory pathGraph pathGraph Hom.id) rest with
      endpointEquality | ⟨next, second, suffix⟩
    · rw [← endpointEquality] at done
      rcases done with ⟨node, impossible⟩
      simp [uncheckedReverseScanPattern] at impossible
    · have secondMember :=
        (step_iff_mem_rewriteOnce pathGraph pathGraph Hom.id _ _).1 second
      rw [reverse_nonedge_scan_rejected pathGraph pathGraph Hom.id
        (Walk.nil : pathGraph.Walk vertex2 vertex2)
        (Walk.nil : pathGraph.Walk vertex0 vertex0) nonedge02] at secondMember
      simp at secondMember

section AxiomAudit

#print axioms native02_is_generated
#print axioms native_composition_executes
#print axioms native_inverse_executes
#print axioms wrong_endpoint_not_native
#print axioms forgedWalk02_has_static_type
#print axioms forged_nonedge_not_native

end AxiomAudit

end Mettapedia.GraphTheory.Walk.NativeTypeExamples
