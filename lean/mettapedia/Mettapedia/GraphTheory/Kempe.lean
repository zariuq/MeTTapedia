import Mathlib.Logic.Relation
import Mettapedia.GraphTheory.Coloring

set_option linter.unusedSectionVars false

namespace SimpleGraph

namespace Coloring

variable {V α : Type*} {G : SimpleGraph V} [DecidableEq α]

/-- Swapping colors on a Kempe component preserves the underlying two-color support. -/
lemma mem_bicoloredSet_swapOnKempeComponent_iff (C : G.Coloring α) (a b : α)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) (v : V) :
    v ∈ (C.swapOnKempeComponent a b K).bicoloredSet a b ↔
      v ∈ C.bicoloredSet a b := by
  by_cases hv : v ∈ C.kempeComponentSet a b K
  · have hmemC : v ∈ C.bicoloredSet a b :=
      C.mem_bicoloredSet_of_mem_kempeComponentSet hv
    have hmemSwap : v ∈ (C.swapOnKempeComponent a b K).bicoloredSet a b := by
      rcases hmemC with hca | hcb
      · simp [Coloring.bicoloredSet, C.swapOnKempeComponent_apply_of_mem hv, hca]
      · simp [Coloring.bicoloredSet, C.swapOnKempeComponent_apply_of_mem hv, hcb]
    exact ⟨fun _ => hmemC, fun _ => hmemSwap⟩
  · simp [Coloring.bicoloredSet, C.swapOnKempeComponent_apply_of_not_mem hv]

/-- Swapping colors on a Kempe component preserves the selected two-color vertex set. -/
theorem bicoloredSet_swapOnKempeComponent (C : G.Coloring α) (a b : α)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    (C.swapOnKempeComponent a b K).bicoloredSet a b = C.bicoloredSet a b := by
  ext v
  exact C.mem_bicoloredSet_swapOnKempeComponent_iff a b K v

end Coloring

variable {V α : Type*} (G : SimpleGraph V) [DecidableEq α]

/-- One Kempe move swaps two colors on one connected component of the
corresponding bicolored subgraph. -/
def KempeStep : G.Coloring α → G.Coloring α → Prop :=
  fun C C' => ∃ a, ∃ b, ∃ K : (C.bicoloredSubgraph a b).ConnectedComponent,
    C' = C.swapOnKempeComponent a b K

/-- The Kempe closure of a base coloring consists of the colorings reachable
by finitely many Kempe moves. -/
def KempeClosure (C₀ : G.Coloring α) : Set (G.Coloring α) :=
  {C | Relation.ReflTransGen G.KempeStep C₀ C}

variable {G}

theorem kempeStep_swapOnKempeComponent (C : G.Coloring α) (a b : α)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    G.KempeStep C (C.swapOnKempeComponent a b K) :=
  ⟨a, b, K, rfl⟩

theorem mem_kempeClosure_self (C₀ : G.Coloring α) :
    C₀ ∈ G.KempeClosure C₀ :=
  Relation.ReflTransGen.refl

theorem mem_kempeClosure_of_step {C₀ C C' : G.Coloring α}
    (hC : C ∈ G.KempeClosure C₀) (hstep : G.KempeStep C C') :
    C' ∈ G.KempeClosure C₀ :=
  Relation.ReflTransGen.tail hC hstep

theorem mem_kempeClosure_of_mem_of_step {C₀ C : G.Coloring α}
    (hC : C ∈ G.KempeClosure C₀) (a b : α)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    C.swapOnKempeComponent a b K ∈ G.KempeClosure C₀ :=
  mem_kempeClosure_of_step hC (G.kempeStep_swapOnKempeComponent C a b K)

theorem kempeClosure_subset_of_mem {C₀ C₁ : G.Coloring α}
    (hC₁ : C₁ ∈ G.KempeClosure C₀) :
    G.KempeClosure C₁ ⊆ G.KempeClosure C₀ := by
  intro C hC
  exact Relation.ReflTransGen.trans hC₁ hC

theorem kempeClosure_eq_of_mem_of_mem {C₀ C₁ : G.Coloring α}
    (h₀₁ : C₁ ∈ G.KempeClosure C₀) (h₁₀ : C₀ ∈ G.KempeClosure C₁) :
    G.KempeClosure C₀ = G.KempeClosure C₁ := by
  ext C
  constructor
  · intro hC
    exact G.kempeClosure_subset_of_mem h₁₀ hC
  · intro hC
    exact G.kempeClosure_subset_of_mem h₀₁ hC

end SimpleGraph
