/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Your Name

# Ramsey Number R(3,6) = 18

Formalization of David Cariolaro's elementary proof that R(3,6) = 18.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## Ramsey Number Definition -/

def HasRamseyProperty (k l : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  (∃ s : Finset (Fin n), G.IsNClique k s) ∨ (∃ s : Finset (Fin n), G.IsNIndepSet l s)

noncomputable def ramseyNumber (k l : ℕ) : ℕ :=
  sInf {n : ℕ | n > 0 ∧ ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], HasRamseyProperty k l G}

/-! ## Known Ramsey Numbers (Axioms) -/
axiom ramsey_three_four : ramseyNumber 3 4 = 9
axiom ramsey_three_five : ramseyNumber 3 5 = 14

/-! ## Basic Graph Properties -/
abbrev TriangleFree (G : SimpleGraph α) : Prop := G.CliqueFree 3
abbrev NoKIndepSet (k : ℕ) (G : SimpleGraph α) : Prop := G.IndepSetFree k

def commonNeighborsCard (G : SimpleGraph α) [DecidableRel G.Adj] (v w : α) : ℕ :=
  (G.neighborFinset v ∩ G.neighborFinset w).card

/-! ## Helper Lemmas -/

lemma triangleFree_iff_cliqueFree_three {G : SimpleGraph α} :
    TriangleFree G ↔ G.CliqueFree 3 := by rfl

lemma neighborSet_indep_of_triangleFree {G : SimpleGraph α} (h : TriangleFree G) (v : α) :
    G.IsIndepSet (G.neighborSet v) := by sorry

lemma degree_le_of_triangleFree_no_indep {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (h_tri : TriangleFree G) (h_no_indep : NoKIndepSet k G) (v : Fin n) :
    G.degree v ≤ k - 1 := by sorry

/-! ## Regularity Axiom -/

abbrev IsKRegular (G : SimpleGraph α) [DecidableRel G.Adj] (k : ℕ) : Prop :=
  G.IsRegularOfDegree k

axiom r35_critical_is_4_regular (G : SimpleGraph (Fin 13)) :
  TriangleFree G → NoKIndepSet 5 G → ∀ [DecidableRel G.Adj], IsKRegular G 4

/-! ## Claim 1 -/

lemma claim1_five_regular {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G) :
    IsKRegular G 5 := by sorry

/-! ## Claims 2 & 3 & Final -/

lemma claim2_neighbor_structure {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_reg : IsKRegular G 5) (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G) (v : Fin 18) :
    ∃ (P Q : Finset (Fin 18)),
      P.card = 4 ∧ Q.card = 8 ∧
      (∀ p ∈ P, ¬G.Adj v p ∧ commonNeighborsCard G v p = 1) ∧
      (∀ q ∈ Q, ¬G.Adj v q ∧ commonNeighborsCard G v q = 2) := by
  sorry

lemma claim3_four_cycle {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_reg : IsKRegular G 5) (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G)
    (v : Fin 18) (P : Finset (Fin 18))
    (hP : P.card = 4 ∧ ∀ p ∈ P, ¬G.Adj v p ∧ commonNeighborsCard G v p = 1) :
    ∃ (p1 p2 p3 p4 : Fin 18), P = {p1, p2, p3, p4} ∧ G.Adj p1 p2 := by
  sorry

lemma final_contradiction {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_reg : IsKRegular G 5) (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G) :
    False := by
  sorry

/-! ## Upper Bound Theorem -/

theorem ramsey_three_six_upper : ramseyNumber 3 6 ≤ 18 := by
  sorry
