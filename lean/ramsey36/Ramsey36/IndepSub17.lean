/-
# Independence Sub-lemmas for the 17-Vertex Graph

Splits the `hasIndepSet 17 adj17Bool 6 = false` computation into 12 sub-problems
by first-vertex choice. Each sub-problem has ≤970 search nodes, keeping kernel
memory low.

This file imports ONLY IndepSetFunc.lean (no Mathlib!) so that the kernel
evaluation runs with ~100MB virtual memory instead of 5+GB from Mathlib .oleans.

The combination of sub-lemmas into the final theorem happens in Critical17.lean.
-/

import Algorithms.Graph.IndepSetFunc

/-- Direct Bool adjacency for the Graver-Yackel 17-vertex graph.
    Avoids the Prop → decide → Finset.mem chain. -/
def adj17Bool (v w : Fin 17) : Bool :=
  match v.val, w.val with
  | 0, 9 | 0, 14 | 0, 15 | 0, 16 => true
  | 1, 7 | 1, 11 | 1, 13 | 1, 16 => true
  | 2, 8 | 2, 10 | 2, 12 | 2, 15 => true
  | 3, 6 | 3, 8 | 3, 13 | 3, 15 | 3, 16 => true
  | 4, 5 | 4, 7 | 4, 12 | 4, 14 | 4, 16 => true
  | 5, 4 | 5, 9 | 5, 10 | 5, 11 | 5, 13 => true
  | 6, 3 | 6, 10 | 6, 11 | 6, 12 | 6, 14 => true
  | 7, 1 | 7, 4 | 7, 9 | 7, 10 | 7, 15 => true
  | 8, 2 | 8, 3 | 8, 9 | 8, 11 | 8, 14 => true
  | 9, 0 | 9, 5 | 9, 7 | 9, 8 | 9, 12 => true
  | 10, 2 | 10, 5 | 10, 6 | 10, 7 | 10, 16 => true
  | 11, 1 | 11, 5 | 11, 6 | 11, 8 | 11, 15 => true
  | 12, 2 | 12, 4 | 12, 6 | 12, 9 | 12, 13 => true
  | 13, 1 | 13, 3 | 13, 5 | 13, 12 | 13, 14 => true
  | 14, 0 | 14, 4 | 14, 6 | 14, 8 | 14, 13 => true
  | 15, 0 | 15, 2 | 15, 3 | 15, 7 | 15, 11 => true
  | 16, 0 | 16, 1 | 16, 3 | 16, 4 | 16, 10 => true
  | _, _ => false

/-! ## Sub-problems by first vertex choice (0..11) -/

set_option maxHeartbeats 800000 in
theorem sub17_0 :
    hasIndepSetAux 17 adj17Bool 5 1 [⟨0, by omega⟩] 17 = false := by decide

set_option maxHeartbeats 800000 in
theorem sub17_1 :
    hasIndepSetAux 17 adj17Bool 5 2 [⟨1, by omega⟩] 16 = false := by decide

set_option maxHeartbeats 800000 in
theorem sub17_2 :
    hasIndepSetAux 17 adj17Bool 5 3 [⟨2, by omega⟩] 15 = false := by decide

set_option maxHeartbeats 400000 in
theorem sub17_3 :
    hasIndepSetAux 17 adj17Bool 5 4 [⟨3, by omega⟩] 14 = false := by decide

set_option maxHeartbeats 400000 in
theorem sub17_4 :
    hasIndepSetAux 17 adj17Bool 5 5 [⟨4, by omega⟩] 13 = false := by decide

set_option maxHeartbeats 400000 in
theorem sub17_5 :
    hasIndepSetAux 17 adj17Bool 5 6 [⟨5, by omega⟩] 12 = false := by decide

set_option maxHeartbeats 200000 in
theorem sub17_6 :
    hasIndepSetAux 17 adj17Bool 5 7 [⟨6, by omega⟩] 11 = false := by decide

set_option maxHeartbeats 200000 in
theorem sub17_7 :
    hasIndepSetAux 17 adj17Bool 5 8 [⟨7, by omega⟩] 10 = false := by decide

set_option maxHeartbeats 200000 in
theorem sub17_8 :
    hasIndepSetAux 17 adj17Bool 5 9 [⟨8, by omega⟩] 9 = false := by decide

set_option maxHeartbeats 200000 in
theorem sub17_9 :
    hasIndepSetAux 17 adj17Bool 5 10 [⟨9, by omega⟩] 8 = false := by decide

set_option maxHeartbeats 200000 in
theorem sub17_10 :
    hasIndepSetAux 17 adj17Bool 5 11 [⟨10, by omega⟩] 7 = false := by decide

set_option maxHeartbeats 200000 in
theorem sub17_11 :
    hasIndepSetAux 17 adj17Bool 5 12 [⟨11, by omega⟩] 6 = false := by decide

