/-
# Classic Bayesian Network Examples

This file provides standard examples to verify the Bayesian network formalization.
We demonstrate the three fundamental structures:

1. **Chain**: A → B → C
2. **Fork**: A ← B → C (common cause)
3. **Collider**: A → C ← B (v-structure)

## References

- Pearl, "Probabilistic Reasoning in Intelligent Systems" (1988)
- Koller & Friedman, "Probabilistic Graphical Models" (2009), Chapter 3
-/

import Mettapedia.ProbabilityTheory.BayesianNetworks.DirectedGraph
import Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
import Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation

namespace Mettapedia.ProbabilityTheory.BayesianNetworks.Examples

open DirectedGraph BayesianNetwork DSeparation

/-! ## Three-Node Networks -/

/-- Three-node vertex type. -/
inductive Three : Type
  | A | B | C
  deriving DecidableEq, Repr

instance : Fintype Three where
  elems := {Three.A, Three.B, Three.C}
  complete := by intro x; cases x <;> simp

/-! ### Chain: A → B → C -/

/-- The chain graph: A → B → C -/
def chainGraph : DirectedGraph Three where
  edges u v := (u = Three.A ∧ v = Three.B) ∨ (u = Three.B ∧ v = Three.C)

/-- Helper: no path from C in chain graph (C is a sink). -/
private theorem chainGraph_no_path_from_C (v : Three) (h : chainGraph.Path Three.C v) :
    v = Three.C := by
  generalize hc : Three.C = c at h
  induction h with
  | refl => rfl
  | step hedge _ ih =>
    simp only [chainGraph] at hedge
    rcases hedge with ⟨hu, _⟩ | ⟨hu, _⟩
    · subst hc; exact absurd hu (by decide)
    · subst hc; exact absurd hu (by decide)

/-- Helper: no path from B to A in chain graph. -/
private theorem chainGraph_no_path_B_to_A (h : chainGraph.Path Three.B Three.A) : False := by
  -- Three.B ≠ Three.A, so refl is impossible; must be step
  cases h with
  | step hedge htail =>
    simp only [chainGraph] at hedge
    rcases hedge with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · -- Edge from A to something, but we start from B
      exact absurd hu (by decide)
    · -- Edge B → C, then path from C to A
      subst hv
      have := chainGraph_no_path_from_C Three.A htail
      exact absurd this (by decide)

/-- The chain graph is acyclic. -/
theorem chainGraph_acyclic : chainGraph.IsAcyclic := by
  intro v ⟨w, hedge, hreach⟩
  simp only [chainGraph] at hedge
  rcases hedge with ⟨hv, hw⟩ | ⟨hv, hw⟩
  · -- Edge A → B, need: no path B → A
    subst hv hw
    exact chainGraph_no_path_B_to_A hreach
  · -- Edge B → C, need: no path C → B
    subst hv hw
    have := chainGraph_no_path_from_C Three.B hreach
    exact absurd this (by decide)

/-- The chain Bayesian network. -/
noncomputable def chainBN : BayesianNetwork Three where
  graph := chainGraph
  acyclic := chainGraph_acyclic
  stateSpace := fun _ => Bool
  measurableSpace := fun _ => ⊤

/-! ### Fork: A ← B → C -/

/-- The fork graph: A ← B → C -/
def forkGraph : DirectedGraph Three where
  edges u v := (u = Three.B ∧ v = Three.A) ∨ (u = Three.B ∧ v = Three.C)

/-- Helper: no path from A or C in fork graph (they are sinks). -/
private theorem forkGraph_no_path_from_sink (u v : Three) (hu : u = Three.A ∨ u = Three.C)
    (h : forkGraph.Path u v) : v = u := by
  generalize hs : u = s at h
  induction h with
  | refl => rfl
  | step hedge _ _ =>
    simp only [forkGraph] at hedge
    rcases hedge with ⟨hb, _⟩ | ⟨hb, _⟩ <;>
    · subst hs; rcases hu with rfl | rfl <;> exact absurd hb (by decide)

/-- The fork graph is acyclic. -/
theorem forkGraph_acyclic : forkGraph.IsAcyclic := by
  intro v ⟨w, hedge, hreach⟩
  simp only [forkGraph] at hedge
  rcases hedge with ⟨hv, hw⟩ | ⟨hv, hw⟩
  · -- Edge B → A, need: no path A → B
    subst hv hw
    have := forkGraph_no_path_from_sink Three.A Three.B (Or.inl rfl) hreach
    exact absurd this (by decide)
  · -- Edge B → C, need: no path C → B
    subst hv hw
    have := forkGraph_no_path_from_sink Three.C Three.B (Or.inr rfl) hreach
    exact absurd this (by decide)

/-- The fork Bayesian network. -/
noncomputable def forkBN : BayesianNetwork Three where
  graph := forkGraph
  acyclic := forkGraph_acyclic
  stateSpace := fun _ => Bool
  measurableSpace := fun _ => ⊤

/-! ### Collider: A → C ← B -/

/-- The collider graph: A → C ← B -/
def colliderGraph : DirectedGraph Three where
  edges u v := (u = Three.A ∧ v = Three.C) ∨ (u = Three.B ∧ v = Three.C)

/-- Helper: no path from C in collider graph (C is a sink). -/
private theorem colliderGraph_no_path_from_C (v : Three) (h : colliderGraph.Path Three.C v) :
    v = Three.C := by
  generalize hc : Three.C = c at h
  induction h with
  | refl => rfl
  | step hedge _ _ =>
    simp only [colliderGraph] at hedge
    rcases hedge with ⟨hu, _⟩ | ⟨hu, _⟩ <;>
    · subst hc; exact absurd hu (by decide)

/-- The collider graph is acyclic. -/
theorem colliderGraph_acyclic : colliderGraph.IsAcyclic := by
  intro v ⟨w, hedge, hreach⟩
  simp only [colliderGraph] at hedge
  rcases hedge with ⟨hv, hw⟩ | ⟨hv, hw⟩
  · -- Edge A → C, need: no path C → A
    subst hv hw
    have := colliderGraph_no_path_from_C Three.A hreach
    exact absurd this (by decide)
  · -- Edge B → C, need: no path C → B
    subst hv hw
    have := colliderGraph_no_path_from_C Three.B hreach
    exact absurd this (by decide)

/-- The collider Bayesian network. -/
noncomputable def colliderBN : BayesianNetwork Three where
  graph := colliderGraph
  acyclic := colliderGraph_acyclic
  stateSpace := fun _ => Bool
  measurableSpace := fun _ => ⊤

/-! ## Parent Theorems (WIP) -/

/-- In a chain A → B → C, B's parent is A. -/
theorem chain_parents_B : chainBN.parents Three.B = {Three.A} := by
  ext u
  unfold BayesianNetwork.parents DirectedGraph.parents chainBN chainGraph
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h; rcases h with ⟨rfl, _⟩ | ⟨_, h⟩ <;> [rfl; exact absurd h (by decide)]
  · intro rfl; left; exact ⟨rfl, trivial⟩

/-- In a chain A → B → C, C's parent is B. -/
theorem chain_parents_C : chainBN.parents Three.C = {Three.B} := by
  ext u
  unfold BayesianNetwork.parents DirectedGraph.parents chainBN chainGraph
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h; rcases h with ⟨_, h⟩ | ⟨rfl, _⟩ <;> [exact absurd h (by decide); rfl]
  · intro rfl; right; exact ⟨rfl, trivial⟩

/-- In a chain, A has no parents. -/
theorem chain_parents_A : chainBN.parents Three.A = ∅ := by
  ext u
  unfold BayesianNetwork.parents DirectedGraph.parents chainBN chainGraph
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> exact absurd h (by decide)

/-- In a fork A ← B → C, B has no parents. -/
theorem fork_parents_B : forkBN.parents Three.B = ∅ := by
  ext u
  unfold BayesianNetwork.parents DirectedGraph.parents forkBN forkGraph
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> exact absurd h (by decide)

/-- In a collider A → C ← B, C has parents {A, B}. -/
theorem collider_parents_C : colliderBN.parents Three.C = {Three.A, Three.B} := by
  ext u
  unfold BayesianNetwork.parents DirectedGraph.parents colliderBN colliderGraph
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · left; rfl
    · right; rfl
  · intro h
    rcases h with rfl | rfl
    · left; exact ⟨rfl, trivial⟩
    · right; exact ⟨rfl, trivial⟩

/-! ## D-Separation Examples (WIP) -/

/-- In a chain A → B → C, A and C are d-separated given {B}. -/
theorem chain_dsep_A_C_given_B :
    DSeparated chainGraph {Three.A} {Three.C} {Three.B} := by
  intro x hx y hy hne hpath
  sorry

/-- In a collider A → C ← B, A and B are d-separated given ∅. -/
theorem collider_dsep_A_B_given_empty :
    DSeparated colliderGraph {Three.A} {Three.B} ∅ := by
  intro x hx y hy hne hpath
  sorry

/-! ## Alarm Network (WIP) -/

/-- Five-node type for the Alarm network. -/
inductive Five : Type
  | Burglary | Earthquake | Alarm | JohnCalls | MaryCalls
  deriving DecidableEq, Repr

instance : Fintype Five where
  elems := {Five.Burglary, Five.Earthquake, Five.Alarm, Five.JohnCalls, Five.MaryCalls}
  complete := by intro x; cases x <;> simp

/-- The Alarm network graph. -/
def alarmGraph : DirectedGraph Five where
  edges u v :=
    (u = Five.Burglary ∧ v = Five.Alarm) ∨
    (u = Five.Earthquake ∧ v = Five.Alarm) ∨
    (u = Five.Alarm ∧ v = Five.JohnCalls) ∨
    (u = Five.Alarm ∧ v = Five.MaryCalls)

/-- The alarm graph is acyclic. -/
theorem alarmGraph_acyclic : alarmGraph.IsAcyclic := by
  sorry -- TODO: case analysis

/-- The Alarm Bayesian network. -/
noncomputable def alarmBN : BayesianNetwork Five where
  graph := alarmGraph
  acyclic := alarmGraph_acyclic
  stateSpace := fun _ => Bool
  measurableSpace := fun _ => ⊤

/-! ## Summary

This file demonstrates the three fundamental BN structures:
- **Chain**: A → B → C (acyclicity proven ✓)
- **Fork**: A ← B → C (acyclicity proven ✓)
- **Collider**: A → C ← B (acyclicity proven ✓)

Remaining work:
- Parent set computations (simp issues with equality evaluation)
- D-separation proofs (path enumeration)
- Alarm network acyclicity
-/

end Mettapedia.ProbabilityTheory.BayesianNetworks.Examples
