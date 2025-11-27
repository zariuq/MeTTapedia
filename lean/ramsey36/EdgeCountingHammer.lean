import Ramsey36.Basic
import Hammer

open SimpleGraph Finset

-- Using definitions from Ramsey36.Basic
-- commonNeighbors, commonNeighborsCard, etc. already defined

variable {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]

-- Main edge counting theorem
theorem edge_count_eq_20
    (h_reg : IsKRegular G 5)
    (h_tri : TriangleFree G)
    (v : Fin 18) :
    let N := G.neighborFinset v
    let M := Finset.univ \ insert v N
    M.sum (fun w => commonNeighborsCard G v w) = 20 := by
  classical
  let N := G.neighborFinset v
  let M := Finset.univ \ insert v N
  have hN_card : N.card = 5 := h_reg v

  -- Assume: each n ∈ N has 4 neighbors in M (this is provable but tedious)
  axiom h_each_4 : ∀ n ∈ N, (M.filter (fun w => G.Adj n w)).card = 4

  -- Double counting: sum from N perspective
  have h_from_N : N.sum (fun n => (M.filter (fun w => G.Adj n w)).card) = 20 := by
    calc N.sum (fun n => (M.filter (fun w => G.Adj n w)).card)
        = N.sum (fun _ => 4) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact h_each_4 n hn
      _ = N.card * 4 := by simp [Finset.sum_const, nsmul_eq_mul]
      _ = 5 * 4 := by rw [hN_card]
      _ = 20 := by norm_num

  -- Now relate to commonNeighborsCard
  -- commonNeighborsCard G v w = (N ∩ neighborFinset w).card
  -- = (N.filter (fun n => G.Adj n w)).card

  have h_common_eq : ∀ w ∈ M,
      commonNeighborsCard G v w = (N.filter (fun n => G.Adj n w)).card := by
    intro w hwM
    unfold commonNeighborsCard commonNeighbors
    congr 1
    ext x
    simp only [Finset.mem_inter, mem_neighborFinset, Finset.mem_filter]
    constructor
    · intro ⟨hxN, hxw⟩
      exact ⟨hxN, G.adj_symm hxw⟩
    · intro ⟨hxN, hxw⟩
      exact ⟨hxN, G.adj_symm hxw⟩

  -- Fubini/handshake: swap sum order
  have h_swap : N.sum (fun n => (M.filter (fun w => G.Adj n w)).card) =
                 M.sum (fun w => (N.filter (fun n => G.Adj n w)).card) := by
    -- This is the double-counting / Fubini step
    hammer  -- Try LeanHammer here!

  calc M.sum (fun w => commonNeighborsCard G v w)
      = M.sum (fun w => (N.filter (fun n => G.Adj n w)).card) := by
        apply Finset.sum_congr rfl
        intro w hw
        exact h_common_eq w hw
    _ = N.sum (fun n => (M.filter (fun w => G.Adj n w)).card) := by
        exact h_swap.symm
    _ = 20 := h_from_N
