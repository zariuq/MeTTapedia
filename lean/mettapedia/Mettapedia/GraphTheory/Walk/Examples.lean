import Mettapedia.GraphTheory.Walk.Operational

/-!
# Positive and negative examples for operational graph walks

The three-vertex path `0--1--2` is small enough to inspect completely while
still distinguishing a real two-edge walk from a non-edge.  The examples show
successful append, reverse, and homomorphic map executions, together with
fail-closed endpoint and adjacency controls.
-/

namespace Mettapedia.GraphTheory.Walk.Examples

open Mettapedia.GraphTheory.Walk.LanguageDef
open Mettapedia.GraphTheory.Walk.Operational
open Mettapedia.OSLF.MeTTaIL.Syntax
open SimpleGraph

set_option autoImplicit false

def vertex0 : Fin 3 := ⟨0, by omega⟩
def vertex1 : Fin 3 := ⟨1, by omega⟩
def vertex2 : Fin 3 := ⟨2, by omega⟩

def pathRelation (source target : Fin 3) : Prop :=
  (source = vertex0 ∧ target = vertex1) ∨
  (source = vertex1 ∧ target = vertex2)

instance : DecidableRel pathRelation := fun source target => by
  unfold pathRelation
  infer_instance

def pathGraph : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel pathRelation

instance : DecidableRel pathGraph.Adj := fun source target => by
  simp only [pathGraph, SimpleGraph.fromRel_adj]
  infer_instance

def edge01 : pathGraph.Adj vertex0 vertex1 := by
  simp [pathGraph, pathRelation, vertex0, vertex1]

def edge12 : pathGraph.Adj vertex1 vertex2 := by
  simp [pathGraph, pathRelation, vertex1, vertex2]

def nonedge02 : ¬ pathGraph.Adj vertex0 vertex2 := by
  simp [pathGraph, pathRelation, vertex0, vertex1, vertex2]

def walk01 : pathGraph.Walk vertex0 vertex1 :=
  .cons edge01 .nil

def walk12 : pathGraph.Walk vertex1 vertex2 :=
  .cons edge12 .nil

def walk02 : pathGraph.Walk vertex0 vertex2 :=
  .cons edge01 (.cons edge12 .nil)

theorem append_result_is_walk02 : walk01.append walk12 = walk02 := rfl

theorem append_example_steps :
    (appendPath pathGraph pathGraph Hom.id walk01 walk12).length = 5 := by
  simpa [walk01] using
    appendPath_length pathGraph pathGraph Hom.id walk01 walk12

theorem reverse_example_steps :
    (reversePath pathGraph pathGraph Hom.id walk02).length = 4 := by
  simp [walk02]

theorem map_identity_result : walk02.map Hom.id = walk02 := by
  simp

theorem map_example_steps :
    (mapPath pathGraph pathGraph Hom.id walk02).length = 7 := by
  simpa [walk02] using
    mapPath_length pathGraph pathGraph Hom.id walk02

/-- The left walk ends at vertex 1 while the right walk begins at vertex 2.
The repeated endpoint in `AppendStart` prevents the request from advancing. -/
theorem mismatched_append_rejected :
    rewriteOnce pathGraph pathGraph Hom.id
      (endpointMismatchedAppendPattern walk01
        (Walk.nil : pathGraph.Walk vertex2 vertex2)) = [] := by
  apply endpoint_mismatch_rejected
  decide

/-- Even a manually forged recursive node cannot cross the missing edge
`0--2`: the `SourceAdjacent` premise makes the scan fail closed. -/
theorem forged_nonedge_rejected :
    rewriteOnce pathGraph pathGraph Hom.id
      (uncheckedAppendScanPattern
        (Walk.nil : pathGraph.Walk vertex2 vertex2)
        (Walk.nil : pathGraph.Walk vertex2 vertex2)
        (Walk.nil : pathGraph.Walk vertex0 vertex0)) = [] := by
  exact nonedge_scan_rejected pathGraph pathGraph Hom.id
    (Walk.nil : pathGraph.Walk vertex2 vertex2)
    (Walk.nil : pathGraph.Walk vertex2 vertex2)
    (Walk.nil : pathGraph.Walk vertex0 vertex0) nonedge02

#print axioms append_example_steps
#print axioms reverse_example_steps
#print axioms map_example_steps
#print axioms mismatched_append_rejected
#print axioms forged_nonedge_rejected

end Mettapedia.GraphTheory.Walk.Examples
