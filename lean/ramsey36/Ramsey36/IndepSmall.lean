/-
# Computational Sub-lemmas for Small Ramsey Graphs

Mathlib-free computation of independence and triangle-free checks for:
- R(3,3): Fin 5, k=3
- R(3,4): Fin 8, k=4
- R(3,5): Fin 13, k=5

Triangle-free is proved via complement adjacency: a k-clique in G is
a k-independent set in `!adj`. So `hasIndepSet n adjNot 3 = false`
proves no 3-clique (triangle-free).

Imports only IndepSetFunc.lean (no Mathlib) to keep virtual memory low.
-/

import Algorithms.Graph.IndepSetFunc
import Ramsey36.IndepSub17

/-! ## R(3,3): Fin 5, C5 cycle -/

def adj5Bool (v w : Fin 5) : Bool :=
  match v.val, w.val with
  | 0, 1 | 0, 4 => true
  | 1, 0 | 1, 2 => true
  | 2, 1 | 2, 3 => true
  | 3, 2 | 3, 4 => true
  | 4, 3 | 4, 0 => true
  | _, _ => false

def adj5NotBool (v w : Fin 5) : Bool := !adj5Bool v w

theorem hasIndepSet_5_adj5Bool_3_false :
    hasIndepSet 5 adj5Bool 3 = false := by decide

theorem hasIndepSet_5_adj5NotBool_3_false :
    hasIndepSet 5 adj5NotBool 3 = false := by decide

/-! ## R(3,4): Fin 8, C8(1,4) -/

def adj8Bool (v w : Fin 8) : Bool :=
  match v.val, w.val with
  | 0, 1 | 0, 7 | 0, 4 => true
  | 1, 0 | 1, 2 | 1, 5 => true
  | 2, 1 | 2, 3 | 2, 6 => true
  | 3, 2 | 3, 4 | 3, 7 => true
  | 4, 3 | 4, 5 | 4, 0 => true
  | 5, 4 | 5, 6 | 5, 1 => true
  | 6, 5 | 6, 7 | 6, 2 => true
  | 7, 6 | 7, 0 | 7, 3 => true
  | _, _ => false

def adj8NotBool (v w : Fin 8) : Bool := !adj8Bool v w

theorem hasIndepSet_8_adj8Bool_4_false :
    hasIndepSet 8 adj8Bool 4 = false := by decide

theorem hasIndepSet_8_adj8NotBool_3_false :
    hasIndepSet 8 adj8NotBool 3 = false := by decide

/-! ## R(3,5): Fin 13, Paley(13) -/

def adj13Bool (v w : Fin 13) : Bool :=
  match v.val, w.val with
  | 0, 1 | 0, 5 | 0, 8 | 0, 12 => true
  | 1, 0 | 1, 2 | 1, 6 | 1, 9 => true
  | 2, 1 | 2, 3 | 2, 7 | 2, 10 => true
  | 3, 2 | 3, 4 | 3, 8 | 3, 11 => true
  | 4, 3 | 4, 5 | 4, 9 | 4, 12 => true
  | 5, 0 | 5, 4 | 5, 6 | 5, 10 => true
  | 6, 1 | 6, 5 | 6, 7 | 6, 11 => true
  | 7, 2 | 7, 6 | 7, 8 | 7, 12 => true
  | 8, 0 | 8, 3 | 8, 7 | 8, 9 => true
  | 9, 1 | 9, 4 | 9, 8 | 9, 10 => true
  | 10, 2 | 10, 5 | 10, 9 | 10, 11 => true
  | 11, 3 | 11, 6 | 11, 10 | 11, 12 => true
  | 12, 0 | 12, 4 | 12, 7 | 12, 11 => true
  | _, _ => false

def adj13NotBool (v w : Fin 13) : Bool := !adj13Bool v w

set_option maxHeartbeats 400000 in
theorem hasIndepSet_13_adj13Bool_5_false :
    hasIndepSet 13 adj13Bool 5 = false := by decide

theorem hasIndepSet_13_adj13NotBool_3_false :
    hasIndepSet 13 adj13NotBool 3 = false := by decide

/-! ## R(3,6): Fin 17, triangle-free check -/

def adj17NotBool (v w : Fin 17) : Bool := !adj17Bool v w

theorem hasIndepSet_17_adj17NotBool_3_false :
    hasIndepSet 17 adj17NotBool 3 = false := by decide
