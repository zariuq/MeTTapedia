/-
Copyright (c) 2026 Mettapedia Authors. All rights reserved.
SPDX-License-Identifier: MIT
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Order.KonigLemma

/-!
# Rays and König's infinity lemma

König's infinity lemma in its graph form (Diestel, *Graph Theory*, Lemma 8.1.2): if
`V₀, V₁, …` are disjoint non-empty finite sets of vertices and every vertex of `Vₙ₊₁` has a
neighbour in `Vₙ`, then the graph has a ray `v₀ v₁ v₂ …` with `vₙ ∈ Vₙ`. It follows from
Mathlib's order-theoretic König lemma (`exists_seq_forall_proj_of_forall_finite`) applied to the
finite chains through the first layers.

## Main results

* `SimpleGraph.IsRay`: an injective sequence of adjacent vertices.
* `SimpleGraph.exists_isRay_of_layers`: König's infinity lemma.
-/

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

private structure LayerChain (layer : ℕ → Finset V) (n : ℕ) where
  verts : Fin (n + 1) → V
  mem_layer : ∀ i : Fin (n + 1), verts i ∈ layer i.1
  step : ∀ i : Fin n, G.Adj (verts i.castSucc) (verts i.succ)

namespace LayerChain

variable {G} {layer : ℕ → Finset V}

@[ext] private theorem ext {n : ℕ} {c d : LayerChain (G := G) layer n}
    (hverts : c.verts = d.verts) : c = d := by
  cases c
  cases d
  cases hverts
  rfl

private def top {n : ℕ} (c : LayerChain (G := G) layer n) : V :=
  c.verts (Fin.last n)

private theorem top_mem {n : ℕ} (c : LayerChain (G := G) layer n) :
    c.top ∈ layer n :=
  by simpa [top] using c.mem_layer (Fin.last n)

private def extend {n : ℕ} (c : LayerChain (G := G) layer n) {v : V}
    (hv : v ∈ layer (n + 1)) (hcv : G.Adj c.top v) : LayerChain (G := G) layer (n + 1) where
  verts := Fin.snoc c.verts v
  mem_layer i := by
    cases i using Fin.lastCases with
    | last =>
        simpa using hv
    | cast i =>
        simpa using c.mem_layer i
  step i := by
    cases i using Fin.lastCases with
    | last =>
        simpa [LayerChain.top] using hcv
    | cast i =>
        simpa [Fin.snoc_castSucc, ← Fin.castSucc_succ] using c.step i

private def truncate {i j : ℕ} (hij : i ≤ j) (c : LayerChain (G := G) layer j) :
    LayerChain (G := G) layer i where
  verts := Fin.take (i + 1) (Nat.succ_le_succ hij) c.verts
  mem_layer k := by
    simpa using c.mem_layer (Fin.castLE (Nat.succ_le_succ hij) k)
  step k := by
    simpa [Fin.take] using c.step (Fin.castLE hij k)

@[simp] private theorem truncate_refl {i : ℕ} (c : LayerChain (G := G) layer i) :
    truncate (G := G) (layer := layer) (le_refl i) c = c := by
  apply ext
  funext k
  simp [truncate]

@[simp] private theorem truncate_trans {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (c : LayerChain (G := G) layer k) :
    truncate (G := G) (layer := layer) hij (truncate (G := G) (layer := layer) hjk c) =
      truncate (G := G) (layer := layer) (hij.trans hjk) c := by
  apply ext
  funext x
  simp [truncate, Fin.take]

private theorem exists_chain_ending_at
    (layer : ℕ → Finset V)
    (hback : ∀ n, ∀ v ∈ layer (n + 1), ∃ u ∈ layer n, G.Adj v u)
    : ∀ n, ∀ v, v ∈ layer n → ∃ c : LayerChain (G := G) layer n, c.top = v
  | 0, v, hv => by
      refine ⟨⟨fun _ => v, ?_, ?_⟩, ?_⟩
      · intro i
        have : i = 0 := Fin.eq_zero i
        subst i
        simpa using hv
      · intro i
        exact Fin.elim0 i
      · simp [LayerChain.top]
  | n + 1, v, hv => by
      obtain ⟨u, hu, hvu⟩ := hback n v hv
      obtain ⟨c, hc⟩ := exists_chain_ending_at layer hback n u hu
      refine ⟨c.extend hv ?_, ?_⟩
      · exact hc.symm ▸ hvu.symm
      · simp [LayerChain.top, LayerChain.extend]

end LayerChain

/-! ### König's infinity lemma

> "Let V₀, V₁, … be an infinite sequence of disjoint non-empty finite
>  sets, and let G be a graph on their union. If every vertex in Vₙ₊₁
>  has a neighbour in Vₙ, then G contains a ray v₀ v₁ v₂ … with
>  vₙ ∈ Vₙ for all n."
-/

/-- A **ray** in G is an injective infinite walk v₀ v₁ v₂ … such that
    consecutive vertices are adjacent. -/
def IsRay (f : ℕ → V) : Prop :=
  Function.Injective f ∧ ∀ n, G.Adj (f n) (f (n + 1))

/-- König's infinity lemma (Diestel, Lemma 8.1.2): given a layered graph
    with finite layers and each vertex in layer n+1 adjacent to some
    vertex in layer n, there exists an infinite ray through the layers.
    -/
theorem exists_isRay_of_layers
    (layer : ℕ → Finset V)
    (hnonempty : ∀ n, (layer n).Nonempty)
    (hdisjoint : ∀ m n, m ≠ n → Disjoint (layer m) (layer n))
    (hback : ∀ n, ∀ v ∈ layer (n + 1), ∃ u ∈ layer n, G.Adj v u) :
    ∃ f : ℕ → V, (∀ n, f n ∈ layer n) ∧ IsRay G f := by
  classical
  let α : ℕ → Type _ := LayerChain (G := G) layer
  let : Finite (α 0) := by
    refine Finite.of_injective
      (fun c : α 0 => (⟨c.top, by simpa [α, LayerChain.top] using c.top_mem⟩ :
        {v // v ∈ layer 0})) ?_
    intro c d hcd
    apply LayerChain.ext
    funext i
    have : i = 0 := Fin.eq_zero i
    subst i
    exact congrArg Subtype.val hcd
  let : ∀ n, Nonempty (α n) := fun n => by
    obtain ⟨v, hv⟩ := hnonempty n
    obtain ⟨c, _⟩ := LayerChain.exists_chain_ending_at (G := G) layer hback n v hv
    exact ⟨c⟩
  let π : {i j : ℕ} → (hij : i ≤ j) → α j → α i :=
    fun {_ _} hij c => LayerChain.truncate (G := G) (layer := layer) hij c
  have π_refl : ∀ ⦃i⦄ (a : α i), π rfl.le a = a := by
    intro i a
    simp [π]
  have π_trans : ∀ ⦃i j k⦄ (hij : i ≤ j) (hjk : j ≤ k) a,
      π hij (π hjk a) = π (hij.trans hjk) a := by
    intro i j k hij hjk a
    exact LayerChain.truncate_trans (G := G) (layer := layer) hij hjk a
  have hfin : ∀ i (a : α i), {b : α (i + 1) | π (Nat.le_add_right i 1) b = a}.Finite := by
    intro i a
    refine Finite.of_injective
      (fun b : {b : α (i + 1) | π (Nat.le_add_right i 1) b = a} =>
        (⟨b.1.top, by simpa [α, LayerChain.top] using b.1.top_mem⟩ :
          {v // v ∈ layer (i + 1)})) ?_
    intro b₁ b₂ htop
    have htop' : b₁.1.top = b₂.1.top := congrArg Subtype.val htop
    have hinit₁ : Fin.init b₁.1.verts = a.verts := by
      simpa [π, LayerChain.truncate] using congrArg LayerChain.verts b₁.2
    have hinit₂ : Fin.init b₂.1.verts = a.verts := by
      simpa [π, LayerChain.truncate] using congrArg LayerChain.verts b₂.2
    apply Subtype.ext
    apply LayerChain.ext
    calc
      b₁.1.verts = Fin.snoc (Fin.init b₁.1.verts) b₁.1.top := by
        exact (Fin.snoc_init_self b₁.1.verts).symm
      _ = Fin.snoc a.verts b₂.1.top := by
        simp [hinit₁, htop']
      _ = b₂.1.verts := by
        simpa [LayerChain.top, hinit₂] using Fin.snoc_init_self b₂.1.verts
  obtain ⟨chains, hchains⟩ :=
    exists_seq_forall_proj_of_forall_finite (α := α) π π_refl π_trans hfin
  let f : ℕ → V := fun n => (chains n).top
  refine ⟨f, ?_, ?_⟩
  · intro n
    exact (chains n).top_mem
  · refine ⟨?_, ?_⟩
    · intro m n hmn
      by_cases h : m = n
      · exact h
      · have hdis := Finset.disjoint_left.mp (hdisjoint m n h)
        have hm : f m ∈ layer m := by simpa [f] using (chains m).top_mem
        have hn : f n ∈ layer n := by simpa [f] using (chains n).top_mem
        exact (hdis hm (hmn ▸ hn)).elim
    · intro n
      have hprefix :
          (chains (n + 1)).verts (Fin.castSucc (Fin.last n)) = (chains n).top := by
        simpa [π, LayerChain.truncate, f, LayerChain.top, Fin.init] using
          congrFun (congrArg LayerChain.verts (hchains (Nat.le_succ n))) (Fin.last n)
      have hstep := (chains (n + 1)).step (Fin.last n)
      simpa [f, LayerChain.top, hprefix] using hstep

end SimpleGraph
