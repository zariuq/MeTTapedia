/-!
# Fair merging of batched query results

A batch of queries returns one ranked result list per query. The merge reads
them in rounds, taking the rank-0 result of every query in query order, then
every rank-1 result, and so on. It keeps the first result with each key (a
URL, say) and drops later results with a key already kept.

- `merge_keys_nodup`: no key is kept twice.
- `merge_complete`: every result of every query has its key in the merge.
- `merge_fair`: with `n` queries, every query's top `r` results have their keys
  among the first `n * r` merged results. So truncating the merge to a budget
  of `n * r` results starves no query of its top `r`.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Retrieval.BatchedQueryMerge

universe u v
variable {α : Type u} {K : Type v} [DecidableEq K]

/-- The first element of every nonempty list, in list order. -/
def heads : List (List α) → List α
  | [] => []
  | [] :: rest => heads rest
  | (x :: _) :: rest => x :: heads rest

/-- Every list without its first element. -/
def tails : List (List α) → List (List α)
  | [] => []
  | l :: rest => l.drop 1 :: tails rest

/-- Total number of results. -/
def total : List (List α) → Nat
  | [] => 0
  | l :: rest => l.length + total rest

/-- The round-robin order: `fuel` rounds; `total ls` rounds take every result. -/
def rounds : Nat → List (List α) → List α
  | 0, _ => []
  | f + 1, ls => heads ls ++ rounds f (tails ls)

def interleave (ls : List (List α)) : List α := rounds (total ls) ls

/-- `tails` applied `n` times. -/
def tailsN : Nat → List (List α) → List (List α)
  | 0, ls => ls
  | n + 1, ls => tailsN n (tails ls)

/-- Keep the first element with each key. -/
def dedupKeep (key : α → K) : List K → List α → List α
  | _, [] => []
  | seen, x :: xs =>
    if key x ∈ seen then dedupKeep key seen xs
    else x :: dedupKeep key (key x :: seen) xs

def merge (key : α → K) (ls : List (List α)) : List α :=
  dedupKeep key [] (interleave ls)

/-! ## Rounds -/

theorem heads_length_le : ∀ ls : List (List α), (heads ls).length ≤ ls.length
  | [] => Nat.le_refl 0
  | [] :: rest => Nat.le_succ_of_le (heads_length_le rest)
  | (_ :: _) :: rest => Nat.succ_le_succ (heads_length_le rest)

theorem tails_length : ∀ ls : List (List α), (tails ls).length = ls.length
  | [] => rfl
  | _ :: rest => congrArg Nat.succ (tails_length rest)

theorem rounds_length_le : ∀ (f : Nat) (ls : List (List α)), (rounds f ls).length ≤ ls.length * f
  | 0, _ => Nat.le_refl 0
  | f + 1, ls => by
    show (heads ls ++ rounds f (tails ls)).length ≤ ls.length * (f + 1)
    rw [List.length_append, Nat.mul_succ, Nat.add_comm (ls.length * f)]
    have h := rounds_length_le f (tails ls)
    rw [tails_length] at h
    exact Nat.add_le_add (heads_length_le ls) h

/-- The `j`-th list after `r` rounds of `tails` has lost its first `r` results. -/
theorem tails_iter_get : ∀ (r : Nat) (ls : List (List α)) (i : Nat) (l : List α),
    ls[i]? = some l → (tailsN r ls)[i]? = some (l.drop r)
  | 0, _, _, _, h => by simpa [tailsN] using h
  | r + 1, ls, i, l, h => by
    show (tailsN r (tails ls))[i]? = some (l.drop (r + 1))
    have ht : (tails ls)[i]? = some (l.drop 1) := by
      induction ls generalizing i with
      | nil => simp at h
      | cons m rest ih =>
        cases i with
        | zero =>
          simp at h
          subst h
          rfl
        | succ i => exact ih i (by simpa using h)
    rw [tails_iter_get r (tails ls) i (l.drop 1) ht, List.drop_drop, Nat.add_comm]

/-- An element at the head of a list among `ls` is one of `heads ls`. -/
theorem head_mem_heads : ∀ (ls : List (List α)) (i : Nat) (x : α) (l : List α),
    ls[i]? = some (x :: l) → x ∈ heads ls
  | [], _, _, _, h => by simp at h
  | m :: rest, 0, x, l, h => by
    simp at h
    subst h
    exact List.mem_cons_self
  | m :: rest, i + 1, x, l, h => by
    have hr : rest[i]? = some (x :: l) := by simpa using h
    cases m with
    | nil => exact head_mem_heads rest i x l hr
    | cons y ys => exact List.mem_cons_of_mem y (head_mem_heads rest i x l hr)

/-- `r` rounds after `s` rounds of `tails`: the results of ranks `s .. s+r-1`
of every list. -/
theorem mem_rounds : ∀ (f : Nat) (ls : List (List α)) (i k : Nat) (l : List α) (x : α),
    ls[i]? = some l → l[k]? = some x → k < f → x ∈ rounds f ls
  | 0, _, _, _, _, _, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | f + 1, ls, i, k, l, x, hl, hx, hk => by
    show x ∈ heads ls ++ rounds f (tails ls)
    cases k with
    | zero =>
      cases l with
      | nil => simp at hx
      | cons y ys =>
        simp at hx
        subst hx
        exact List.mem_append_left _ (head_mem_heads ls i y ys hl)
    | succ k =>
      apply List.mem_append_right
      have ht : (tails ls)[i]? = some (l.drop 1) := by
        simpa [tailsN] using tails_iter_get 1 ls i l hl
      exact mem_rounds f (tails ls) i k (l.drop 1) x ht (by simpa [List.getElem?_drop, Nat.add_comm] using hx)
        (Nat.lt_of_succ_lt_succ hk)

theorem rounds_prefix : ∀ (a b : Nat) (ls : List (List α)),
    rounds (a + b) ls = rounds a ls ++ rounds b (tailsN a ls)
  | 0, b, ls => by simp [rounds, tailsN]
  | a + 1, b, ls => by
    rw [Nat.succ_add]
    show heads ls ++ rounds (a + b) (tails ls) =
      (heads ls ++ rounds a (tails ls)) ++ rounds b (tailsN a (tails ls))
    rw [rounds_prefix a b (tails ls), List.append_assoc]

theorem length_le_total : ∀ (ls : List (List α)) (i : Nat) (l : List α),
    ls[i]? = some l → l.length ≤ total ls
  | [], _, _, h => by simp at h
  | m :: rest, 0, l, h => by
    simp at h
    subst h
    exact Nat.le_add_right _ _
  | m :: rest, i + 1, l, h =>
    Nat.le_trans (length_le_total rest i l (by simpa using h)) (Nat.le_add_left _ _)

/-! ## Keeping the first of each key -/

theorem dedupKeep_keys_nodup (key : α → K) :
    ∀ (seen : List K) (xs : List α),
      ((dedupKeep key seen xs).map key).Nodup ∧ ∀ y ∈ dedupKeep key seen xs, key y ∉ seen
  | _, [] => ⟨List.nodup_nil, fun _ h => by simp [dedupKeep] at h⟩
  | seen, x :: xs => by
    by_cases hx : key x ∈ seen
    · simp only [dedupKeep, hx, if_true]
      exact dedupKeep_keys_nodup key seen xs
    · simp only [dedupKeep, hx, if_false]
      obtain ⟨hn, hs⟩ := dedupKeep_keys_nodup key (key x :: seen) xs
      refine ⟨?_, ?_⟩
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨?_, hn⟩
        intro hmem
        obtain ⟨y, hy, hyk⟩ := List.mem_map.mp hmem
        exact hs y hy (hyk ▸ List.mem_cons_self)
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hx
        · exact fun h => hs y hy (List.mem_cons_of_mem _ h)

/-- Every element's key is either already seen or kept. -/
theorem dedupKeep_covers (key : α → K) :
    ∀ (seen : List K) (xs : List α) (x : α), x ∈ xs →
      key x ∈ seen ∨ ∃ y ∈ dedupKeep key seen xs, key y = key x
  | _, [], _, h => absurd h List.not_mem_nil
  | seen, z :: zs, x, h => by
    by_cases hz : key z ∈ seen
    · simp only [dedupKeep, hz, if_true]
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl hz
      · exact dedupKeep_covers key seen zs x h
    · simp only [dedupKeep, hz, if_false]
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr ⟨x, List.mem_cons_self, rfl⟩
      · rcases dedupKeep_covers key (key z :: seen) zs x h with hs | ⟨y, hy, hyk⟩
        · rcases List.mem_cons.mp hs with he | hs
          · exact Or.inr ⟨z, List.mem_cons_self, he.symm⟩
          · exact Or.inl hs
        · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, hyk⟩

/-- Deduplicating a prefix gives a prefix of the deduplicated whole. -/
theorem dedupKeep_append (key : α → K) :
    ∀ (seen : List K) (as bs : List α),
      ∃ rest, dedupKeep key seen (as ++ bs) = dedupKeep key seen as ++ rest
  | seen, [], bs => ⟨dedupKeep key seen bs, by simp [dedupKeep]⟩
  | seen, a :: as, bs => by
    by_cases ha : key a ∈ seen
    · simp only [List.cons_append, dedupKeep, ha, if_true]
      exact dedupKeep_append key seen as bs
    · simp only [List.cons_append, dedupKeep, ha, if_false]
      obtain ⟨rest, h⟩ := dedupKeep_append key (key a :: seen) as bs
      exact ⟨rest, by simp [h]⟩

theorem dedupKeep_length_le (key : α → K) :
    ∀ (seen : List K) (xs : List α), (dedupKeep key seen xs).length ≤ xs.length
  | _, [] => Nat.le_refl 0
  | seen, x :: xs => by
    by_cases hx : key x ∈ seen
    · simp only [dedupKeep, hx, if_true]
      exact Nat.le_succ_of_le (dedupKeep_length_le key seen xs)
    · simp only [dedupKeep, hx, if_false, List.length_cons]
      exact Nat.succ_le_succ (dedupKeep_length_le key _ xs)

/-! ## The merge -/

theorem merge_keys_nodup (key : α → K) (ls : List (List α)) :
    ((merge key ls).map key).Nodup :=
  (dedupKeep_keys_nodup key [] _).1

theorem merge_complete (key : α → K) (ls : List (List α)) (i k : Nat) (l : List α) (x : α)
    (hl : ls[i]? = some l) (hx : l[k]? = some x) :
    ∃ y ∈ merge key ls, key y = key x := by
  have hk : k < total ls :=
    Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hx).1 (length_le_total ls i l hl)
  rcases dedupKeep_covers key [] _ x (mem_rounds (total ls) ls i k l x hl hx hk) with h | h
  · exact absurd h List.not_mem_nil
  · exact h

/-- Fairness: with `n` queries, every query's result of rank `k < r` has its key
among the first `n * r` merged results. -/
theorem merge_fair (key : α → K) (ls : List (List α)) (i k r : Nat) (l : List α) (x : α)
    (hl : ls[i]? = some l) (hx : l[k]? = some x) (hk : k < r) (hr : r ≤ total ls) :
    ∃ y ∈ (merge key ls).take (ls.length * r), key y = key x := by
  obtain ⟨d, hd⟩ : ∃ d, total ls = r + d := ⟨total ls - r, by omega⟩
  have hsplit : interleave ls = rounds r ls ++ rounds d (tailsN r ls) := by
    unfold interleave; rw [hd, rounds_prefix]
  obtain ⟨rest, hrest⟩ := dedupKeep_append key [] (rounds r ls) (rounds d (tailsN r ls))
  have hfirst := dedupKeep_covers key [] (rounds r ls) x (mem_rounds r ls i k l x hl hx hk)
  rcases hfirst with h | ⟨y, hy, hyk⟩
  · exact absurd h List.not_mem_nil
  · refine ⟨y, ?_, hyk⟩
    have hlen : (dedupKeep key [] (rounds r ls)).length ≤ ls.length * r :=
      Nat.le_trans (dedupKeep_length_le key [] _) (rounds_length_le r ls)
    unfold merge
    rw [hsplit, hrest, List.take_append, List.take_of_length_le hlen]
    exact List.mem_append_left _ hy

end Mettapedia.Algorithms.Retrieval.BatchedQueryMerge
