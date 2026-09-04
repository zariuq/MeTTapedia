import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

open Classical

namespace SimpleGraph

namespace Coloring

variable {V α : Type*} {G H : SimpleGraph V}

/-- Restrict a proper coloring to a subgraph on the same vertex type. -/
def restrict (C : G.Coloring α) (hHG : H ≤ G) : H.Coloring α :=
  C.comp (.ofLE hHG)

@[simp] lemma restrict_apply (C : G.Coloring α) (hHG : H ≤ G) (v : V) :
    C.restrict hHG v = C v :=
  rfl

@[simp] lemma colorClass_restrict (C : G.Coloring α) (hHG : H ≤ G) (c : α) :
    (C.restrict hHG).colorClass c = C.colorClass c := by
  ext v
  rfl

/-- The vertices carrying one of the two selected colors. -/
def bicoloredSet (C : G.Coloring α) (a b : α) : Set V :=
  {v | C v = a ∨ C v = b}

@[simp] lemma mem_bicoloredSet (C : G.Coloring α) (a b : α) (v : V) :
    v ∈ C.bicoloredSet a b ↔ C v = a ∨ C v = b :=
  Iff.rfl

/-- The induced subgraph on the vertices colored `a` or `b`. -/
abbrev bicoloredSubgraph (C : G.Coloring α) (a b : α) :
    SimpleGraph ↥(C.bicoloredSet a b) :=
  G.induce (C.bicoloredSet a b)

/-- The vertex set of a connected component of the `a`/`b`-subgraph. -/
def kempeComponentSet (C : G.Coloring α) (a b : α)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) : Set V :=
  {v | ∃ hv : v ∈ C.bicoloredSet a b,
      (C.bicoloredSubgraph a b).connectedComponentMk ⟨v, hv⟩ = K}

lemma mem_bicoloredSet_of_mem_kempeComponentSet (C : G.Coloring α) {a b : α}
    {K : (C.bicoloredSubgraph a b).ConnectedComponent} {v : V}
    (hv : v ∈ C.kempeComponentSet a b K) :
    C v = a ∨ C v = b := by
  exact hv.choose

lemma mem_kempeComponentSet_self (C : G.Coloring α) {a b : α} {v : V}
    (hv : v ∈ C.bicoloredSet a b) :
    v ∈ C.kempeComponentSet a b
      ((C.bicoloredSubgraph a b).connectedComponentMk ⟨v, hv⟩) := by
  exact ⟨hv, rfl⟩

lemma mem_kempeComponentSet_of_adj (C : G.Coloring α) {a b : α}
    {K : (C.bicoloredSubgraph a b).ConnectedComponent} {u v : V}
    (hu : u ∈ C.kempeComponentSet a b K) (hadj : G.Adj u v)
    (hv : v ∈ C.bicoloredSet a b) :
    v ∈ C.kempeComponentSet a b K := by
  rcases hu with ⟨hu', hK⟩
  refine ⟨hv, ?_⟩
  have hadj' : (C.bicoloredSubgraph a b).Adj ⟨u, hu'⟩ ⟨v, hv⟩ := hadj
  have hcomp :
      (C.bicoloredSubgraph a b).connectedComponentMk ⟨u, hu'⟩ =
        (C.bicoloredSubgraph a b).connectedComponentMk ⟨v, hv⟩ := by
    exact ConnectedComponent.connectedComponentMk_eq_of_adj hadj'
  rw [← hcomp, hK]

lemma color_ne_of_adj_of_mem_kempeComponentSet_of_not_mem
    (C : G.Coloring α) {a b : α}
    {K : (C.bicoloredSubgraph a b).ConnectedComponent} {u v : V}
    (hu : u ∈ C.kempeComponentSet a b K) (hadj : G.Adj u v)
    (hv : v ∉ C.kempeComponentSet a b K) :
    C v ≠ a ∧ C v ≠ b := by
  constructor
  · intro hva
    apply hv
    exact C.mem_kempeComponentSet_of_adj hu hadj
      (by simpa [bicoloredSet] using Or.inl hva)
  · intro hvb
    apply hv
    exact C.mem_kempeComponentSet_of_adj hu hadj
      (by simpa [bicoloredSet] using Or.inr hvb)

/-- Swap two colors on one connected component of their bicolored subgraph. -/
noncomputable def swapOnKempeComponent [DecidableEq α] (C : G.Coloring α) (a b : α)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    G.Coloring α :=
  Coloring.mk
    (fun v =>
      if hv : v ∈ C.kempeComponentSet a b K then
        Equiv.swap a b (C v)
      else
        C v)
    (by
      intro u v hadj
      by_cases hu : u ∈ C.kempeComponentSet a b K
      · by_cases hv : v ∈ C.kempeComponentSet a b K
        · simpa [hu, hv] using fun hEq =>
            C.valid hadj ((Equiv.swap a b).injective hEq)
        · have hcv :=
            C.color_ne_of_adj_of_mem_kempeComponentSet_of_not_mem hu hadj hv
          rcases C.mem_bicoloredSet_of_mem_kempeComponentSet hu with hcu | hcu
          · simpa [hu, hv, hcu] using hcv.2.symm
          · simpa [hu, hv, hcu] using hcv.1.symm
      · by_cases hv : v ∈ C.kempeComponentSet a b K
        · have hcu :=
            C.color_ne_of_adj_of_mem_kempeComponentSet_of_not_mem hv hadj.symm hu
          rcases C.mem_bicoloredSet_of_mem_kempeComponentSet hv with hcv | hcv
          · simpa [hu, hv, hcv] using hcu.2
          · simpa [hu, hv, hcv] using hcu.1
        · simpa [hu, hv] using C.valid hadj)

@[simp] lemma swapOnKempeComponent_apply_of_mem [DecidableEq α]
    (C : G.Coloring α) {a b : α}
    {K : (C.bicoloredSubgraph a b).ConnectedComponent} {v : V}
    (hv : v ∈ C.kempeComponentSet a b K) :
    C.swapOnKempeComponent a b K v = Equiv.swap a b (C v) := by
  change (if v ∈ C.kempeComponentSet a b K then Equiv.swap a b (C v) else C v) =
    Equiv.swap a b (C v)
  simp [hv]

@[simp] lemma swapOnKempeComponent_apply_of_not_mem [DecidableEq α]
    (C : G.Coloring α) {a b : α}
    {K : (C.bicoloredSubgraph a b).ConnectedComponent} {v : V}
    (hv : v ∉ C.kempeComponentSet a b K) :
    C.swapOnKempeComponent a b K v = C v := by
  change (if v ∈ C.kempeComponentSet a b K then Equiv.swap a b (C v) else C v) = C v
  simp [hv]

end Coloring

end SimpleGraph
