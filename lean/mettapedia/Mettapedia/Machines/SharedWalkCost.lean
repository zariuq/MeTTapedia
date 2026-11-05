import Mathlib.Tactic

/-!
# Walking a shared term: once per subterm, not once per path

An admission walk reads a term and joins what it finds (flags) in a
semilattice: finding something twice is finding it once.  A term shares
subterms, so a walk that follows every path reads a shared subterm once per
path to it: a term doubling at each of `n` levels has `2 ^ n` paths to its
leaf.  A walk that keeps a table of what each subterm found (under the scope
it holds fixed while reading one term) reads each subterm once and finds the
same.

The model: nodes are numbers, `kids k` the children of node `k`, each child
smaller than its parent (a term is finite and acyclic), and `own k` what
reading node `k` itself finds.  The per-path walk runs with fuel; the table
is filled in increasing order of nodes, which reads every child before its
parent.  This file proves:
* `pathFound_eq_table`: with enough fuel the per-path walk finds, at every
  node, what the table holds for it;
* `doubling_visits`: on the doubling term (node `k + 1` has two edges to node
  `k`) the per-path walk reads `2 ^ (n + 1) - 1` nodes under node `n`, where
  the table reads the `n + 1` nodes once each (`doubling_gap`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SharedWalkCost

variable {α : Type} [SemilatticeSup α] [OrderBot α]

/-- The per-path walk under node `k`, with `fuel` levels left. -/
def pathFound (kids : ℕ → List ℕ) (own : ℕ → α) : ℕ → ℕ → α
  | 0, k => own k
  | fuel + 1, k => own k ⊔ ((kids k).map (pathFound kids own fuel)).foldr (· ⊔ ·) ⊥

/-- The table after reading nodes `0 … k` in order: entry `j` is what node
`j` and everything below it finds. -/
def table (kids : ℕ → List ℕ) (own : ℕ → α) : ℕ → ℕ → α
  | 0 => fun j => if j = 0 then own 0 ⊔ ((kids 0).map (fun _ => (⊥ : α))).foldr (· ⊔ ·) ⊥
      else ⊥
  | k + 1 => fun j => if j = k + 1
      then own (k + 1) ⊔ ((kids (k + 1)).map (table kids own k)).foldr (· ⊔ ·) ⊥
      else table kids own k j

/-- Reading later nodes leaves an entry as it was. -/
theorem table_stable (kids : ℕ → List ℕ) (own : ℕ → α) (j k : ℕ) (hj : j ≤ k) :
    ∀ m, k ≤ m → table kids own m j = table kids own k j := by
  intro m hm
  induction m with
  | zero =>
    have : k = 0 := by omega
    subst this; rfl
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le hm with h | h
    · rw [h]
    · simp only [table]
      rw [if_neg (by omega)]
      exact ih (by omega)

theorem pathFound_eq_table (kids : ℕ → List ℕ) (hk : ∀ k c, c ∈ kids k → c < k)
    (own : ℕ → α) : ∀ k fuel, k < fuel → pathFound kids own fuel k = table kids own k k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro fuel hfuel
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    cases k with
    | zero =>
      have hnil : kids 0 = [] := by
        rcases h : kids 0 with _ | ⟨c, rest⟩
        · rfl
        · exact absurd (hk 0 c (by simp [h])) (by omega)
      simp [pathFound, table, hnil]
    | succ k =>
      simp only [pathFound, table, if_true]
      congr 2
      apply List.map_congr_left
      intro c hc
      have hck : c < k + 1 := hk (k + 1) c hc
      rw [ih c hck fuel (by omega)]
      exact (table_stable kids own c c le_rfl k (by omega)).symm

/-- How many nodes the per-path walk reads under node `k`. -/
def pathVisits (kids : ℕ → List ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | fuel + 1, k => 1 + ((kids k).map (pathVisits kids fuel)).sum

/-- The doubling term: node `k + 1` has two edges to node `k`. -/
def doubling : ℕ → List ℕ
  | 0 => []
  | k + 1 => [k, k]

theorem doubling_lt : ∀ k c, c ∈ doubling k → c < k := by
  intro k c hc
  cases k with
  | zero => simp [doubling] at hc
  | succ k =>
    simp only [doubling, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> omega

theorem doubling_visits (n : ℕ) : pathVisits doubling (n + 1) n + 1 = 2 ^ (n + 1) := by
  induction n with
  | zero => simp [pathVisits, doubling]
  | succ n ih =>
    have h : pathVisits doubling (n + 2) (n + 1) =
        1 + (pathVisits doubling (n + 1) n + pathVisits doubling (n + 1) n) := by
      simp [pathVisits, doubling]
    rw [h, pow_succ]
    omega

theorem pow_succ_ge (n : ℕ) (hn : 2 ≤ n) : n + 3 ≤ 2 ^ (n + 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m _ ihm =>
    rw [pow_succ]
    omega

/-- From three levels on, the per-path walk reads more than the `n + 1`
distinct nodes the table reads once each, and the gap doubles per level. -/
theorem doubling_gap (n : ℕ) (hn : 2 ≤ n) : n + 1 < pathVisits doubling (n + 1) n := by
  have h := doubling_visits n
  have hpow := pow_succ_ge n hn
  omega

end Mettapedia.Machines.SharedWalkCost
