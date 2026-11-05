/-!
# RecallProvenance — recall ranks one candidate per distinct memory text

Two memories with byte-identical text are one piece of evidence, recorded
twice. Recall that ranks memory identifiers lets the copies take several of
the `k` result slots, and gives each copy its own share of every normalized
seed. This file states what recall needs instead and proves it for a model:

* `dedup` keeps the first candidate of each text from a score-ordered list.
  Its texts are distinct (`dedup_keys_nodup`), and a copy placed after its
  original changes nothing (`dedup_ignores_later_copy`).
* The dedupe of a prefix is a prefix of the dedupe of the whole list
  (`dedup_take_prefix`). A fetch that grows until it yields `k` distinct texts,
  or reaches the end of the ranking, therefore returns exactly the first `k`
  distinct texts of the complete ranking (`refetch_exact`).
* Merging the masses of copies by `max` is idempotent (`mergeMax_idem`), while
  summing them is not (`sum_counts_copies`), and the representative of a group
  — its oldest copy — does not move when a newer copy arrives
  (`rep_stable_under_newer_copy`).
* Ranking identifiers instead lets one copy displace a distinct candidate from
  the top two (`per_id_top_k_loses_a_slot`).

The model covers the ranking discipline only. It does not claim that a text
equality is the right notion of identity for every memory, nor that the scores
are good.
-/

namespace RecallProvenance

/-- A recall candidate: its identifier, the identity of its text, and its
creation time. Scores are implicit in the list order (best first). -/
structure Cand where
  id : Nat
  key : Nat
  time : Nat
  deriving DecidableEq, Repr

/-- First occurrence of each text, scanning best first. -/
def dedupFrom : List Nat → List Cand → List Cand
  | _, [] => []
  | seen, c :: cs =>
      if c.key ∈ seen then dedupFrom seen cs
      else c :: dedupFrom (c.key :: seen) cs

def dedup (l : List Cand) : List Cand := dedupFrom [] l

/-! ## Distinct texts -/

/-- Every kept candidate's text is new to the texts seen before it. -/
theorem dedupFrom_fresh (seen : List Nat) (l : List Cand) :
    ∀ c ∈ dedupFrom seen l, c.key ∉ seen := by
  induction l generalizing seen with
  | nil => intro c h; simp [dedupFrom] at h
  | cons x xs ih =>
    intro c h
    unfold dedupFrom at h
    split at h
    · exact ih seen c h
    · rename_i hx
      cases h with
      | head => exact hx
      | tail _ h' =>
        have := ih (x.key :: seen) c h'
        intro hc; exact this (List.mem_cons_of_mem _ hc)

/-- The kept texts are pairwise distinct. -/
theorem dedupFrom_keys_nodup (seen : List Nat) (l : List Cand) :
    ((dedupFrom seen l).map Cand.key).Pairwise (· ≠ ·) := by
  induction l generalizing seen with
  | nil => simp [dedupFrom]
  | cons x xs ih =>
    unfold dedupFrom
    split
    · exact ih seen
    · simp only [List.map_cons, List.pairwise_cons]
      refine ⟨?_, ih (x.key :: seen)⟩
      intro k hk heq
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hk
      exact dedupFrom_fresh (x.key :: seen) xs c hc (heq ▸ List.mem_cons_self ..)

theorem dedup_keys_nodup (l : List Cand) :
    ((dedup l).map Cand.key).Pairwise (· ≠ ·) :=
  dedupFrom_keys_nodup [] l

/-! ## Copies never take a slot -/

/-- The texts seen after scanning a list. -/
def seenAfter : List Nat → List Cand → List Nat
  | seen, [] => seen
  | seen, c :: cs => if c.key ∈ seen then seenAfter seen cs else seenAfter (c.key :: seen) cs

theorem seenAfter_mono (seen : List Nat) (l : List Cand) :
    ∀ k ∈ seen, k ∈ seenAfter seen l := by
  induction l generalizing seen with
  | nil => intro k h; exact h
  | cons x xs ih =>
    intro k h
    unfold seenAfter
    split
    · exact ih seen k h
    · exact ih (x.key :: seen) k (List.mem_cons_of_mem _ h)

theorem seenAfter_has (seen : List Nat) (l : List Cand) :
    ∀ c ∈ l, c.key ∈ seenAfter seen l := by
  induction l generalizing seen with
  | nil => intro c h; simp at h
  | cons x xs ih =>
    intro c h
    unfold seenAfter
    cases h with
    | head =>
      split
      · rename_i hx; exact seenAfter_mono seen xs _ hx
      · exact seenAfter_mono _ xs _ (List.mem_cons_self ..)
    | tail _ h' =>
      split
      · exact ih seen c h'
      · exact ih (x.key :: seen) c h'

theorem dedupFrom_append (seen : List Nat) (l₁ l₂ : List Cand) :
    dedupFrom seen (l₁ ++ l₂) = dedupFrom seen l₁ ++ dedupFrom (seenAfter seen l₁) l₂ := by
  induction l₁ generalizing seen with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, dedupFrom, seenAfter]
    split
    · exact ih seen
    · simp only [List.cons_append]; exact congrArg _ (ih (x.key :: seen))

/-- A candidate whose text already appeared earlier in the ranking changes
nothing: copies never take a slot, wherever they rank. -/
theorem dedup_ignores_later_copy (l₁ l₂ : List Cand) (c c' : Cand)
    (hc : c ∈ l₁) (hkey : c'.key = c.key) :
    dedup (l₁ ++ c' :: l₂) = dedup (l₁ ++ l₂) := by
  unfold dedup
  rw [dedupFrom_append, dedupFrom_append]
  congr 1
  have hseen : c'.key ∈ seenAfter [] l₁ := hkey ▸ seenAfter_has [] l₁ c hc
  simp [dedupFrom, hseen]

/-! ## Refetching until `k` distinct texts is exact -/

/-- The dedupe of a prefix of the ranking is a prefix of the dedupe of the
whole ranking. -/
theorem dedupFrom_take_prefix (seen : List Nat) (l : List Cand) (n : Nat) :
    ∃ t, dedupFrom seen (l.take n) ++ t = dedupFrom seen l := by
  have h := dedupFrom_append seen (l.take n) (l.drop n)
  rw [List.take_append_drop] at h
  exact ⟨_, h.symm⟩

theorem dedup_take_prefix (l : List Cand) (n : Nat) :
    ∃ t, dedup (l.take n) ++ t = dedup l :=
  dedupFrom_take_prefix [] l n

theorem take_of_prefix {α} (a t : List α) (k : Nat) (hk : k ≤ a.length) :
    (a ++ t).take k = a.take k := by
  rw [List.take_append_of_le_length hk]

/-- A fetch of the best `n` candidates that already yields `k` distinct texts,
or that covers the whole ranking, gives exactly the first `k` distinct texts
of the complete ranking. Growing the fetch until one of the two holds is
therefore an exact top-`k` over distinct texts. -/
theorem refetch_exact (l : List Cand) (n k : Nat)
    (h : k ≤ (dedup (l.take n)).length ∨ l.length ≤ n) :
    (dedup (l.take n)).take k = (dedup l).take k := by
  cases h with
  | inl hk =>
    obtain ⟨t, ht⟩ := dedup_take_prefix l n
    rw [← ht, take_of_prefix _ _ _ hk]
  | inr hn =>
    rw [List.take_of_length_le hn]

/-! ## Merging copies -/

/-- Masses of copies merge by `max`: the group keeps its strongest reading. -/
def mergeMax (xs : List Nat) : Nat := xs.foldl max 0

theorem foldl_max_ge (xs : List Nat) (a : Nat) : a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => exact Nat.le_refl _
  | cons x xs ih => exact Nat.le_trans (Nat.le_max_left a x) (ih (max a x))

theorem foldl_max_mem (xs : List Nat) (a : Nat) :
    ∀ x ∈ xs, x ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => intro x h; simp at h
  | cons y ys ih =>
    intro x h
    cases h with
    | head => exact Nat.le_trans (Nat.le_max_right a _) (foldl_max_ge ys _)
    | tail _ h' => exact ih (max a y) x h'

theorem foldl_max_le (xs : List Nat) (a b : Nat) (ha : a ≤ b) (hx : ∀ x ∈ xs, x ≤ b) :
    xs.foldl max a ≤ b := by
  induction xs generalizing a with
  | nil => exact ha
  | cons y ys ih =>
    exact ih (max a y) (Nat.max_le.mpr ⟨ha, hx y (List.mem_cons_self ..)⟩)
      (fun x h => hx x (List.mem_cons_of_mem _ h))

/-- Recording every copy twice leaves the merged mass unchanged. -/
theorem mergeMax_idem (xs : List Nat) : mergeMax (xs ++ xs) = mergeMax xs := by
  apply Nat.le_antisymm
  · apply foldl_max_le _ 0 _ (Nat.zero_le _)
    intro x hx
    cases List.mem_append.mp hx with
    | inl h => exact foldl_max_mem xs 0 x h
    | inr h => exact foldl_max_mem xs 0 x h
  · apply foldl_max_le _ 0 _ (Nat.zero_le _)
    intro x hx
    exact foldl_max_mem (xs ++ xs) 0 x (List.mem_append_left _ hx)

/-- Summing instead counts the copy: one memory recorded twice doubles its
weight. -/
theorem sum_counts_copies : ([3] ++ [3]).foldl (· + ·) 0 ≠ [3].foldl (· + ·) 0 := by decide

/-! ## A stable representative -/

/-- The earlier of two copies by creation time, then identifier. -/
def older (a b : Cand) : Cand :=
  if a.time < b.time ∨ (a.time = b.time ∧ a.id ≤ b.id) then a else b

/-- A group's representative: its oldest copy. -/
def rep : Cand → List Cand → Cand
  | r, [] => r
  | r, c :: cs => rep (older r c) cs

/-- A copy created later than the representative does not move it, so the
attention a memory has accrued stays on one identifier. -/
theorem rep_stable_under_newer_copy (r : Cand) (cs : List Cand) (c : Cand)
    (hnew : (rep r cs).time < c.time) :
    rep r (cs ++ [c]) = rep r cs := by
  induction cs generalizing r with
  | nil =>
    simp only [List.nil_append, rep, older]
    simp [rep] at hnew
    simp [hnew]
  | cons x xs ih =>
    simp only [List.cons_append, rep]
    exact ih (older r x) hnew

/-! ## Ranking identifiers loses slots -/

def a : Cand := ⟨1, 10, 0⟩
def a₂ : Cand := ⟨2, 10, 5⟩   -- a copy of `a`, written five seconds later
def b : Cand := ⟨3, 20, 0⟩

/-- Top two by identifier returns the memory and its copy; top two by text
returns the memory and the distinct runner-up. -/
theorem per_id_top_k_loses_a_slot :
    [a, a₂, b].take 2 = [a, a₂] ∧ (dedup [a, a₂, b]).take 2 = [a, b] := by
  decide

end RecallProvenance

#print axioms RecallProvenance.dedup_keys_nodup
#print axioms RecallProvenance.dedup_ignores_later_copy
#print axioms RecallProvenance.refetch_exact
#print axioms RecallProvenance.mergeMax_idem
#print axioms RecallProvenance.rep_stable_under_newer_copy
#print axioms RecallProvenance.per_id_top_k_loses_a_slot
