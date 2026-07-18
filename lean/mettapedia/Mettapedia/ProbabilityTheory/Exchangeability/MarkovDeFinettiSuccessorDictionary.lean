/-
Copyright-free formalization module of Mettapedia.

# The word ↔ successor-array dictionary (Fortini–Ladelli–Petris–Regazzini, Lemma 1)

Combinatorial core for the Markov de Finetti PE bridge, following
Fortini, Ladelli, Petris, Regazzini, "On mixtures of distributions of Markov
chains", Stochastic Process. Appl. 100 (2002) 147-165, Lemma 1 and Example 1.

A finite word `a :: rest` over `Fin k` determines, for each state `i`, the list
of successor states read off at the successive visits to `i` (`rowSuccessors`).
Conversely, a start state plus per-row successor lists determine a word by
greedy decoding (`decode`): at each step, consume the head of the current
state's row. This file proves the exact dictionary:

* `decode_encode` : decoding the rows of a word reproduces the word;
* `sum_rowSuccessors_length` : total row mass = number of transitions;
* `transCountL_eq_count` : transition counts are row-wise value counts, so
  row-wise permutations preserve Markov evidence (`transCountL_eq_of_rowPerms`).

The LLM primer for this file: the delicate direction (row-permuted successor
lists decode to a full-length word when each permutation fixes its row's LAST
entry — FLPR Lemma 1(b)) is developed in later sections; the failure of
arbitrary permutations is witnessed here concretely by `exampleOne` (FLPR's
Example 1): a non-last-fixing swap deadlocks the decoder at length 10 < 11.
-/

import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases

namespace Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiSuccessorDictionary

variable {k : ℕ}

/-! ## Encoding: reading the successor rows off a word -/

/-- Successor list of state `i` along a word: the states immediately following
each occurrence of `i`, except a final occurrence with no successor. -/
def rowSuccessors (i : Fin k) : List (Fin k) → List (Fin k)
  | [] => []
  | [_] => []
  | a :: b :: rest =>
      if a = i then b :: rowSuccessors i (b :: rest) else rowSuccessors i (b :: rest)

@[simp] theorem rowSuccessors_nil (i : Fin k) : rowSuccessors i ([] : List (Fin k)) = [] := rfl

@[simp] theorem rowSuccessors_singleton (i a : Fin k) :
    rowSuccessors i [a] = [] := rfl

theorem rowSuccessors_cons_cons (i a b : Fin k) (rest : List (Fin k)) :
    rowSuccessors i (a :: b :: rest) =
      if a = i then b :: rowSuccessors i (b :: rest) else rowSuccessors i (b :: rest) := rfl

/-- List-level transition count: occurrences of the adjacent pair `(a, b)`. -/
def transCountL : List (Fin k) → Fin k → Fin k → ℕ
  | [], _, _ => 0
  | [_], _, _ => 0
  | x :: y :: rest, a, b =>
      (if x = a ∧ y = b then 1 else 0) + transCountL (y :: rest) a b

/-- Transitions out of `a` valued `b` are exactly the `b`-entries of row `a`. -/
theorem transCountL_eq_count (w : List (Fin k)) (a b : Fin k) :
    transCountL w a b = (rowSuccessors a w).count b := by
  induction w with
  | nil => rfl
  | cons x rest ih =>
      cases rest with
      | nil => rfl
      | cons y t =>
          rw [transCountL, rowSuccessors_cons_cons, ih]
          by_cases hx : x = a <;> by_cases hy : y = b <;>
            simp [hx, hy, Nat.add_comm]

/-- Row-wise permutations of the successor lists preserve all transition
counts, hence Markov evidence. -/
theorem transCountL_eq_of_rowPerms {w w' : List (Fin k)}
    (h : ∀ i, (rowSuccessors i w).Perm (rowSuccessors i w')) (a b : Fin k) :
    transCountL w a b = transCountL w' a b := by
  rw [transCountL_eq_count, transCountL_eq_count]
  exact ((h a).count_eq b)

/-- Total successor mass equals the number of transitions in the word. -/
theorem sum_rowSuccessors_length [NeZero k] (a : Fin k) (rest : List (Fin k)) :
    (∑ i, (rowSuccessors i (a :: rest)).length) = rest.length := by
  induction rest generalizing a with
  | nil => simp
  | cons b t ih =>
      have hsplit :
          ∀ i, (rowSuccessors i (a :: b :: t)).length =
            (if a = i then 1 else 0) + (rowSuccessors i (b :: t)).length := by
        intro i
        rw [rowSuccessors_cons_cons]
        by_cases hai : a = i
        · simp [hai, Nat.add_comm]
        · simp [hai]
      simp only [hsplit, Finset.sum_add_distrib]
      rw [Finset.sum_ite_eq Finset.univ a (fun _ => 1)]
      simp only [Finset.mem_univ, if_true, ih b, List.length_cons]
      omega

/-! ## Decoding: greedy word reconstruction from rows -/

/-- One-state-at-a-time greedy decoder: consume the head of the current
state's row, move there, repeat while fuel lasts. Halts early (deadlock) if
the current row is exhausted. -/
def decodeAux [DecidableEq (Fin k)] (rows : Fin k → List (Fin k)) (s : Fin k) :
    ℕ → List (Fin k)
  | 0 => []
  | fuel + 1 =>
      match rows s with
      | [] => []
      | v :: rest => v :: decodeAux (Function.update rows s rest) v fuel

/-- Greedy decode of a start state and per-row successor lists. -/
def decode [NeZero k] (s : Fin k) (rows : Fin k → List (Fin k)) : List (Fin k) :=
  s :: decodeAux rows s (∑ i, (rows i).length)

/-- Peeling the head of a word peels the head of its start row and leaves all
other rows unchanged. -/
theorem rowSuccessors_tail (a b : Fin k) (t : List (Fin k)) :
    (fun i => rowSuccessors i (a :: b :: t)) =
      Function.update (fun i => rowSuccessors i (b :: t)) a
        (b :: rowSuccessors a (b :: t)) := by
  funext i
  rw [rowSuccessors_cons_cons]
  by_cases hia : a = i
  · subst hia
    simp [Function.update_self]
  · rw [Function.update_of_ne (Ne.symm hia)]
    simp [hia]

/-- Decoding the rows of a word reproduces the word (auxiliary form with
exact fuel). -/
theorem decodeAux_encode (a : Fin k) (rest : List (Fin k)) :
    decodeAux (fun i => rowSuccessors i (a :: rest)) a rest.length = rest := by
  induction rest generalizing a with
  | nil => rfl
  | cons b t ih =>
      have hrow : rowSuccessors a (a :: b :: t) = b :: rowSuccessors a (b :: t) := by
        rw [rowSuccessors_cons_cons, if_pos rfl]
      have hupdate :
          Function.update (fun i => rowSuccessors i (a :: b :: t)) a
              (rowSuccessors a (b :: t)) =
            fun i => rowSuccessors i (b :: t) := by
        rw [rowSuccessors_tail a b t]
        rw [Function.update_idem]
        funext i
        by_cases hia : i = a
        · subst hia; simp [Function.update_self]
        · rw [Function.update_of_ne hia]
      show decodeAux (fun i => rowSuccessors i (a :: b :: t)) a (t.length + 1) = b :: t
      rw [decodeAux]
      simp only [hrow]
      rw [hupdate]
      exact congrArg (b :: ·) (ih b)

/-- **The encode side of FLPR Lemma 1(a)**: greedy decoding of the successor
rows of a word reproduces the word exactly. -/
theorem decode_encode [NeZero k] (a : Fin k) (rest : List (Fin k)) :
    decode a (fun i => rowSuccessors i (a :: rest)) = a :: rest := by
  unfold decode
  rw [sum_rowSuccessors_length a rest]
  rw [decodeAux_encode a rest]

/-! ## FLPR Example 1 (S = {0,1}) — positive and negative canaries

The word `w₀ = 00101001101` has successor rows `V₀ = [0,1,1,0,1,1]` and
`V₁ = [0,0,1,0]`.

* Positive: the row-wise permutation `V₀' = [1,0,0,1,1,1]`, `V₁' = [0,1,0,0]`
  FIXES each row's last entry; the decoder produces the full-length word
  `01000110101`, which has the same transition counts (Markov evidence).
* Negative: interchanging `V₀,₄` and `V₀,₆` (positions 4 and 6, 1-indexed) does
  NOT fix the last entry, and the decoder deadlocks at length 10 < 11: the
  permuted array is not the array of any word of the original length. This is
  the concrete failure that the last-entry-fixing hypothesis of FLPR
  Lemma 1(b) rules out.
-/

namespace ExampleOne

def w₀ : List (Fin 2) := [0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1]

example : rowSuccessors (0 : Fin 2) w₀ = [0, 1, 1, 0, 1, 1] := by decide
example : rowSuccessors (1 : Fin 2) w₀ = [0, 0, 1, 0] := by decide

/-- Row-permuted successor lists, fixing each row's last entry. -/
def rowsGood : Fin 2 → List (Fin 2) :=
  fun i => if i = 0 then [1, 0, 0, 1, 1, 1] else [0, 1, 0, 0]

example : (rowsGood 0).Perm (rowSuccessors (0 : Fin 2) w₀) := by decide
example : (rowsGood 1).Perm (rowSuccessors (1 : Fin 2) w₀) := by decide

/-- The last-fixing permuted rows decode to a FULL-length word. -/
example : decode (0 : Fin 2) rowsGood = [0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1] := by decide

/-- The decoded word is Markov-evidence-equivalent to the original. -/
example : ∀ a b : Fin 2,
    transCountL (decode (0 : Fin 2) rowsGood) a b = transCountL w₀ a b := by decide

/-- Non-last-fixing swap (`V₀,₄ ↔ V₀,₆`): still a row permutation... -/
def rowsBad : Fin 2 → List (Fin 2) :=
  fun i => if i = 0 then [0, 1, 1, 1, 1, 0] else [0, 0, 1, 0]

example : (rowsBad 0).Perm (rowSuccessors (0 : Fin 2) w₀) := by decide

/-- ...but the decoder DEADLOCKS: only 10 of 11 symbols are produced. The
permuted array is not the successor array of any word of length 11. -/
example : (decode (0 : Fin 2) rowsBad).length = 10 := by decide

end ExampleOne

/-! ## Counting infrastructure for the no-deadlock theorem -/

/-- Each transition contributes its target once: summing the `v`-counts of all
successor rows counts the occurrences of `v` in the tail of the word. -/
theorem sum_rowSuccessors_count [NeZero k] (w : List (Fin k)) (v : Fin k) :
    (∑ i, ((rowSuccessors i w).count v)) = w.tail.count v := by
  induction w with
  | nil => simp
  | cons a rest ih =>
      cases rest with
      | nil => simp
      | cons b t =>
          have hsplit :
              ∀ i, ((rowSuccessors i (a :: b :: t)).count v) =
                (if a = i then (if b = v then 1 else 0) else 0) +
                  ((rowSuccessors i (b :: t)).count v) := by
            intro i
            rw [rowSuccessors_cons_cons]
            by_cases hai : a = i
            · by_cases hbv : b = v <;> simp [hai, hbv, Nat.add_comm]
            · simp [hai]
          simp only [hsplit, Finset.sum_add_distrib]
          rw [Finset.sum_ite_eq Finset.univ a (fun _ => if b = v then 1 else 0)]
          simp only [Finset.mem_univ, if_true, ih, List.tail_cons]
          by_cases hbv : b = v <;> simp [hbv, Nat.add_comm]

/-- Occurrence count split at the last element: all-but-last plus the last. -/
theorem count_dropLast_add_ite (w : List (Fin k)) (hw : w ≠ []) (s : Fin k) :
    w.dropLast.count s + (if w.getLast hw = s then 1 else 0) = w.count s := by
  conv_rhs => rw [← List.dropLast_append_getLast hw]
  simp [List.count_append, List.count_cons]

/-- Occurrence count split at the head: the head plus the tail. -/
theorem count_tail_add_ite (w : List (Fin k)) (hw : w ≠ []) (s : Fin k) :
    w.tail.count s + (if w.head hw = s then 1 else 0) = w.count s := by
  cases w with
  | nil => exact absurd rfl hw
  | cons a t => by_cases has : a = s <;> simp [has]

/-- Out-degree at `i` equals the occurrences of `i` among all-but-last:
every occurrence except a final one emits exactly one successor. -/
theorem rowSuccessors_length_eq_count_dropLast (i : Fin k) (w : List (Fin k)) :
    (rowSuccessors i w).length = w.dropLast.count i := by
  induction w with
  | nil => rfl
  | cons a rest ih =>
      cases rest with
      | nil => rfl
      | cons b t =>
          rw [rowSuccessors_cons_cons,
            List.dropLast_cons_of_ne_nil (List.cons_ne_nil b t)]
          by_cases hai : a = i
          · simp [hai, ih]
          · simp [hai, ih]

/-- Canary for `sum_rowSuccessors_count` on FLPR's Example 1. -/
example : (∑ i, ((rowSuccessors i ExampleOne.w₀).count 1)) =
    ExampleOne.w₀.tail.count 1 := by decide

/-- Canary for `rowSuccessors_length_eq_count_dropLast` on FLPR's Example 1. -/
example : (rowSuccessors (0 : Fin 2) ExampleOne.w₀).length =
    ExampleOne.w₀.dropLast.count 0 := by decide

/-! ## Decode partial-correctness: prefix consumption and halt-by-exhaustion -/

/-- The decoder consumes each row in queue order: the row-`i` successors of a
decoded word form a prefix of the supplied row `i`. -/
theorem decodeAux_rowSuccessors_isPrefix [NeZero k] (rows : Fin k → List (Fin k))
    (s : Fin k) (fuel : ℕ) (i : Fin k) :
    (rowSuccessors i (s :: decodeAux rows s fuel)) <+: rows i := by
  induction fuel generalizing rows s with
  | zero => simp [decodeAux]
  | succ fuel ih =>
      rcases hrows : rows s with _ | ⟨v, rest⟩
      · have hstep : decodeAux rows s (fuel + 1) = [] := by
          rw [decodeAux]
          simp only [hrows]
        rw [hstep]
        simp
      · have hstep : decodeAux rows s (fuel + 1)
            = v :: decodeAux (Function.update rows s rest) v fuel := by
          rw [decodeAux]
          simp only [hrows]
        rw [hstep, rowSuccessors_cons_cons]
        by_cases his : s = i
        · subst his
          rw [if_pos rfl, hrows]
          have h := ih (Function.update rows s rest) v
          rw [Function.update_self] at h
          obtain ⟨t, ht⟩ := h
          exact ⟨t, by rw [List.cons_append, ht]⟩
        · rw [if_neg his]
          have h := ih (Function.update rows s rest) v
          rwa [Function.update_of_ne (Ne.symm his)] at h

/-- With sufficient fuel the decoder halts only by exhaustion: at the final
state of the decoded word, the consumed successors are ALL of that state's
row. Combined with `decodeAux_rowSuccessors_isPrefix` (prefix + equality),
the halt state's row is fully consumed. -/
theorem decodeAux_halt_exhausted [NeZero k] (rows : Fin k → List (Fin k)) (s : Fin k)
    (fuel : ℕ) (hfuel : (∑ i, (rows i).length) ≤ fuel) :
    rowSuccessors ((s :: decodeAux rows s fuel).getLast (List.cons_ne_nil s _))
        (s :: decodeAux rows s fuel)
      = rows ((s :: decodeAux rows s fuel).getLast (List.cons_ne_nil s _)) := by
  induction fuel generalizing rows s with
  | zero =>
      have hzero : ∀ j, rows j = [] := by
        intro j
        have hsplit : ∀ i, (rows i).length
            = (if j = i then (rows j).length else 0)
              + (if j = i then 0 else (rows i).length) := by
          intro i
          by_cases hji : j = i
          · subst hji; simp
          · simp [hji]
        have hsum := Nat.le_zero.mp hfuel
        rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib,
          Finset.sum_ite_eq Finset.univ j (fun _ => (rows j).length)] at hsum
        simp only [Finset.mem_univ, if_true] at hsum
        have hlen : (rows j).length = 0 := by omega
        exact List.length_eq_zero_iff.mp hlen
      simp [decodeAux, hzero]
  | succ fuel ih =>
      rcases hrows : rows s with _ | ⟨v, rest⟩
      · have hstep : decodeAux rows s (fuel + 1) = [] := by
          rw [decodeAux]
          simp only [hrows]
        simp [hstep, hrows]
      · have hstep : decodeAux rows s (fuel + 1)
            = v :: decodeAux (Function.update rows s rest) v fuel := by
          rw [decodeAux]
          simp only [hrows]
        have hfuel' : (∑ i, ((Function.update rows s rest) i).length) ≤ fuel := by
          have hsplit : ∀ i, (rows i).length
              = (if s = i then 1 else 0) + ((Function.update rows s rest) i).length := by
            intro i
            by_cases his : s = i
            · subst his
              simp [hrows, Nat.add_comm]
            · rw [Function.update_of_ne (Ne.symm his)]
              simp [his]
          simp only [hsplit, Finset.sum_add_distrib] at hfuel
          rw [Finset.sum_ite_eq Finset.univ s (fun _ => 1)] at hfuel
          simp only [Finset.mem_univ, if_true] at hfuel
          omega
        have key : ∀ y : Fin k,
            rowSuccessors y (v :: decodeAux (Function.update rows s rest) v fuel)
              = Function.update rows s rest y →
            rowSuccessors y (s :: v :: decodeAux (Function.update rows s rest) v fuel)
              = rows y := by
          intro y hy
          rw [rowSuccessors_cons_cons]
          by_cases hsy : s = y
          · subst hsy
            rw [if_pos rfl, hy, Function.update_self, hrows]
          · rw [if_neg hsy, hy, Function.update_of_ne (Ne.symm hsy)]
        simp only [hstep]
        exact key _ (ih (Function.update rows s rest) v hfuel')

/-- Canary: even the DEADLOCKED decode of FLPR's Example 1 consumed row 0 in
queue order — a (strict) prefix of `rowsBad 0`. -/
example : (rowSuccessors (0 : Fin 2) (decode (0 : Fin 2) ExampleOne.rowsBad))
    <+: ExampleOne.rowsBad 0 := by decide

/-- Canary: the deadlocked decode halts at state `1`, whose row is fully
exhausted — its consumed successors are ALL of `rowsBad 1`. -/
example : (rowSuccessors (1 : Fin 2) (decode (0 : Fin 2) ExampleOne.rowsBad))
    = ExampleOne.rowsBad 1 := by decide

/-! ## Keystone support: flow identity, prefix counts, last-occurrence splitting -/

/-- Flow identity at state `z`: entries counted through the head equal entries
counted through the last element — both sides are `w.count z`. -/
theorem tail_count_add_head_eq_dropLast_count_add_getLast (w : List (Fin k)) (hw : w ≠ [])
    (z : Fin k) :
    w.tail.count z + (if w.head hw = z then 1 else 0)
      = w.dropLast.count z + (if w.getLast hw = z then 1 else 0) := by
  rw [count_tail_add_ite w hw z, count_dropLast_add_ite w hw z]

/-- Counts are monotone along prefixes (alias for `List.Sublist.count_le`). -/
theorem count_le_of_prefix {l l' : List (Fin k)} (h : l' <+: l) (v : Fin k) :
    l'.count v ≤ l.count v :=
  h.sublist.count_le v

/-- A PROPER prefix misses at least the final element of the full list. -/
theorem count_lt_of_proper_prefix_getLast {l l' : List (Fin k)} (h : l' <+: l)
    (hlt : l'.length < l.length) (hne : l ≠ []) :
    l'.count (l.getLast hne) < l.count (l.getLast hne) := by
  obtain ⟨t, rfl⟩ := h
  have ht : t ≠ [] := by
    rintro rfl
    rw [List.append_nil] at hlt
    omega
  rw [List.getLast_append_of_ne_nil hne ht, List.count_append]
  have hpos : 0 < t.count (t.getLast ht) := List.count_pos_iff.mpr (List.getLast_mem ht)
  omega

/-- Splitting a list at the LAST element violating `p`: everything after it
satisfies `p`. -/
theorem exists_split_last_not_mem {p : Fin k → Prop} [DecidablePred p] {l : List (Fin k)}
    {x₀ : Fin k} (hx : x₀ ∈ l) (hpx : ¬ p x₀) :
    ∃ u x v, l = u ++ x :: v ∧ ¬ p x ∧ ∀ y ∈ v, p y := by
  induction l generalizing x₀ with
  | nil => cases hx
  | cons a l' ih =>
      by_cases hex : ∃ y, y ∈ l' ∧ ¬ p y
      · obtain ⟨y₀, hy₀, hpy₀⟩ := hex
        obtain ⟨u, x, v, hsplit, hpxx, hall⟩ := ih (x₀ := y₀) hy₀ hpy₀
        exact ⟨a :: u, x, v, by rw [List.cons_append, hsplit], hpxx, hall⟩
      · rcases List.mem_cons.mp hx with h | h
        · subst h
          refine ⟨[], x₀, l', by simp, hpx, ?_⟩
          intro y hy
          by_contra hpy
          exact hex ⟨y, hy, hpy⟩
        · exact absurd ⟨x₀, h, hpx⟩ hex

/-- A state absent from all-but-last has an empty successor row. -/
theorem rowSuccessors_eq_nil_of_not_mem_dropLast (x : Fin k) (w : List (Fin k))
    (h : x ∉ w.dropLast) : rowSuccessors x w = [] := by
  induction w with
  | nil => rfl
  | cons a rest ih =>
      cases rest with
      | nil => rfl
      | cons b t =>
          rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil b t)] at h
          have hax : ¬ (a = x) := fun hax => h (by simp [hax])
          rw [rowSuccessors_cons_cons, if_neg hax]
          exact ih (fun hmem => h (List.mem_cons_of_mem a hmem))

/-- At the LAST occurrence of `x` in the all-but-last part of a word, the LAST
entry of row `x` is the symbol immediately following that occurrence. -/
theorem rowSuccessors_getLast_of_last_occurrence (x : Fin k) (u v : List (Fin k)) (b : Fin k)
    (hxv : x ∉ v) :
    (rowSuccessors x (u ++ x :: (v ++ [b]))).getLast?
      = some ((v ++ [b]).head (by simp)) := by
  induction u with
  | nil =>
      cases v with
      | nil =>
          simp only [List.nil_append]
          rw [rowSuccessors_cons_cons, if_pos rfl]
          simp
      | cons c v' =>
          have hdrop : (c :: (v' ++ [b])).dropLast = c :: v' := by
            rw [List.dropLast_cons_of_ne_nil (by simp), List.dropLast_concat]
          have hnil : rowSuccessors x (c :: (v' ++ [b])) = [] :=
            rowSuccessors_eq_nil_of_not_mem_dropLast x _ (by rw [hdrop]; exact hxv)
          simp only [List.nil_append, List.cons_append]
          rw [rowSuccessors_cons_cons, if_pos rfl, hnil]
          simp
  | cons a u' ih =>
      rcases hu : u' ++ x :: (v ++ [b]) with _ | ⟨d, rest⟩
      · simp at hu
      · have hword : (a :: u') ++ x :: (v ++ [b]) = a :: d :: rest := by
          rw [List.cons_append, hu]
        rw [hword, rowSuccessors_cons_cons]
        have hR : rowSuccessors x (d :: rest) = rowSuccessors x (u' ++ x :: (v ++ [b])) := by
          rw [hu]
        by_cases hax : a = x
        · rw [if_pos hax, hR]
          rcases hRl : rowSuccessors x (u' ++ x :: (v ++ [b])) with _ | ⟨e, R'⟩
          · rw [hRl] at ih
            simp at ih
          · rw [hRl] at ih
            rw [List.getLast?_cons_cons]
            exact ih
        · rw [if_neg hax, hR]
          exact ih

/-- Canary: the last entry of row 0 of `w₀` is `1`. -/
example : (rowSuccessors (0 : Fin 2) ExampleOne.w₀).getLast? = some 1 := by decide

/-- Canary: the last-occurrence split shape of `w₀` at state 0:
`u = [0,0,1,0,1,0,0,1,1]`, `x = 0`, `v = []`, `b = 1`. -/
example : ExampleOne.w₀ = [0, 0, 1, 0, 1, 0, 0, 1, 1] ++ (0 : Fin 2) :: ([] ++ [1]) := by
  decide

/-- Canary: `rowSuccessors_getLast_of_last_occurrence` on the `w₀` split —
row 0's last entry is the symbol after the last occurrence of 0. -/
example : (rowSuccessors (0 : Fin 2)
      ([0, 0, 1, 0, 1, 0, 0, 1, 1] ++ (0 : Fin 2) :: ([] ++ [1]))).getLast?
    = some ((([] : List (Fin 2)) ++ [1]).head (by simp)) := by decide

/-! ## The keystone: last-fixing row permutations decode fully (FLPR Lemma 1(b)) -/

/-- Elementary split of a `Fin k`-indexed sum at one coordinate (built from
`Finset.sum_add_distrib`/`Finset.sum_ite_eq` only). -/
theorem sum_split_at (f : Fin k → ℕ) (x : Fin k) :
    (∑ i, f i) = f x + ∑ i, (if x = i then 0 else f i) := by
  have hsplit : ∀ i, f i = (if x = i then f x else 0) + (if x = i then 0 else f i) := by
    intro i
    by_cases hxi : x = i
    · subst hxi
      simp
    · simp [hxi]
  rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib,
    Finset.sum_ite_eq Finset.univ x (fun _ => f x)]
  simp

/-- Pointwise `≤` implies `≤` of `Fin k`-indexed sums (elementary version). -/
theorem sum_le_sum_pointwise {f g : Fin k → ℕ} (h : ∀ i, f i ≤ g i) :
    (∑ i, f i) ≤ ∑ i, g i := by
  have hsplit : ∀ i, g i = f i + (g i - f i) := by
    intro i
    have := h i
    omega
  rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib]
  exact Nat.le_add_right _ _

/-- Pointwise `≤` with one strict coordinate gives `<` of sums. -/
theorem sum_lt_sum_pointwise {f g : Fin k → ℕ} (h : ∀ i, f i ≤ g i) (x : Fin k)
    (hx : f x < g x) : (∑ i, f i) < ∑ i, g i := by
  have hsplit : ∀ i, g i = f i + (g i - f i) := by
    intro i
    have := h i
    omega
  rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib]
  have hres := sum_split_at (fun i => g i - f i) x
  omega

/-- **Halt state = last symbol.** Decoding row-permuted successor lists of
`a :: rest` (no last-fixing needed) halts at the last symbol of the original
word: counting flow in/out of every state forces the deficit onto
`(a :: rest).getLast`. -/
theorem decode_getLast_eq [NeZero k] (a : Fin k) (rest : List (Fin k))
    (R' : Fin k → List (Fin k))
    (hperm : ∀ i, (R' i).Perm (rowSuccessors i (a :: rest))) :
    (decode a R').getLast (by simp [decode])
      = (a :: rest).getLast (List.cons_ne_nil a rest) := by
  obtain ⟨D, hD⟩ : ∃ D, decodeAux R' a (∑ i, (R' i).length) = D := ⟨_, rfl⟩
  have hζcons : decode a R' = a :: D := by simp only [decode, hD]
  have hpre : ∀ i, rowSuccessors i (a :: D) <+: R' i := by
    intro i
    have h := decodeAux_rowSuccessors_isPrefix R' a (∑ j, (R' j).length) i
    rwa [hD] at h
  have F2 := decodeAux_halt_exhausted R' a (∑ j, (R' j).length) le_rfl
  simp only [hD] at F2
  obtain ⟨y, hy⟩ : ∃ y, (a :: D).getLast (List.cons_ne_nil a D) = y := ⟨_, rfl⟩
  rw [hy] at F2
  simp only [hζcons]
  rw [hy]
  -- (A) dropLast counts agree at `y` (full consumption of row `y`).
  have h1 := rowSuccessors_length_eq_count_dropLast y (a :: D)
  rw [F2] at h1
  have h2 := rowSuccessors_length_eq_count_dropLast y (a :: rest)
  have h3 : (R' y).length = (rowSuccessors y (a :: rest)).length := (hperm y).length_eq
  -- (B) tail counts at `y`: consumed rows are prefixes.
  have hsum1 := sum_rowSuccessors_count (a :: D) y
  have hsum2 := sum_rowSuccessors_count (a :: rest) y
  have hle : (∑ i, ((rowSuccessors i (a :: D)).count y))
      ≤ ∑ i, ((rowSuccessors i (a :: rest)).count y) := by
    apply sum_le_sum_pointwise
    intro i
    have hp := count_le_of_prefix (hpre i) y
    have hc := (hperm i).count_eq y
    omega
  -- (C)(D) flow identities at `y` on both words (both start at `a`); the
  -- head-ite reductions below are definitional (`head (a :: l) ≡ a`).
  have hCflow0 := tail_count_add_head_eq_dropLast_count_add_getLast (a :: D)
      (List.cons_ne_nil a D) y
  rw [hy, if_pos rfl] at hCflow0
  have hCflow : (a :: D).tail.count y + (if a = y then 1 else 0)
      = (a :: D).dropLast.count y + 1 := hCflow0
  have hDflow0 := tail_count_add_head_eq_dropLast_count_add_getLast (a :: rest)
      (List.cons_ne_nil a rest) y
  have hDflow : (a :: rest).tail.count y + (if a = y then 1 else 0)
      = (a :: rest).dropLast.count y
        + (if (a :: rest).getLast (List.cons_ne_nil a rest) = y then 1 else 0) := hDflow0
  by_cases hgl : (a :: rest).getLast (List.cons_ne_nil a rest) = y
  · exact hgl.symm
  · exfalso
    rw [if_neg hgl] at hDflow
    obtain ⟨c, hc⟩ : ∃ n, (if a = y then 1 else 0) = n := ⟨_, rfl⟩
    rw [hc] at hCflow hDflow
    omega

/-- **The keystone (FLPR Lemma 1(b), full consumption).** If the rows `R'` are
row-wise permutations of the successor rows of `a :: rest` that FIX each row's
last entry, then greedy decoding consumes every row completely: the decoded
word's successor rows are exactly `R'`. -/
theorem decode_lastFixed_rowSuccessors [NeZero k] (a : Fin k) (rest : List (Fin k))
    (R' : Fin k → List (Fin k))
    (hperm : ∀ i, (R' i).Perm (rowSuccessors i (a :: rest)))
    (hlast : ∀ i, (R' i).getLast? = (rowSuccessors i (a :: rest)).getLast?) :
    ∀ i, rowSuccessors i (decode a R') = R' i := by
  obtain ⟨D, hD⟩ : ∃ D, decodeAux R' a (∑ i, (R' i).length) = D := ⟨_, rfl⟩
  have hζcons : decode a R' = a :: D := by simp only [decode, hD]
  have hpre : ∀ i, rowSuccessors i (a :: D) <+: R' i := by
    intro i
    have h := decodeAux_rowSuccessors_isPrefix R' a (∑ j, (R' j).length) i
    rwa [hD] at h
  suffices hlen : ∀ i, (rowSuccessors i (a :: D)).length = (R' i).length by
    intro i
    rw [hζcons]
    exact (hpre i).eq_of_length (hlen i)
  by_contra hcon
  obtain ⟨s₁, hs₁⟩ := not_forall.mp hcon
  -- Halt state is `b`, the last symbol of the word (`decode_getLast_eq`).
  have hgl := decode_getLast_eq a rest R' hperm
  simp only [hζcons] at hgl
  have F2 := decodeAux_halt_exhausted R' a (∑ j, (R' j).length) le_rfl
  simp only [hD] at F2
  rw [hgl] at F2
  obtain ⟨b, hb⟩ : ∃ b, (a :: rest).getLast (List.cons_ne_nil a rest) = b := ⟨_, rfl⟩
  rw [hb] at F2
  -- Row `b` is fully consumed; row `s₁` is not.
  have hpb : (rowSuccessors b (a :: D)).length = (R' b).length := by rw [F2]
  have hps₁ : ¬ ((rowSuccessors s₁ (a :: D)).length = (R' s₁).length) := hs₁
  have hs₁mem : s₁ ∈ (a :: rest).dropLast := by
    have h1 := rowSuccessors_length_eq_count_dropLast s₁ (a :: rest)
    have h2 : (R' s₁).length = (rowSuccessors s₁ (a :: rest)).length := (hperm s₁).length_eq
    have h3 : (rowSuccessors s₁ (a :: D)).length < (R' s₁).length :=
      Nat.lt_of_le_of_ne (hpre s₁).length_le hs₁
    have hpos : 0 < (a :: rest).dropLast.count s₁ := by omega
    exact List.count_pos_iff.mp hpos
  -- Split at the LAST unconsumed state `x` along `w.dropLast`.
  obtain ⟨u, x, v, hsplit, hpx, hvA⟩ :=
    exists_split_last_not_mem
      (p := fun i => (rowSuccessors i (a :: D)).length = (R' i).length) hs₁mem hps₁
  have hxv : x ∉ v := fun hmem => hpx (hvA x hmem)
  have hwshape : a :: rest = u ++ x :: (v ++ [b]) := by
    have hcat := List.dropLast_concat_getLast (List.cons_ne_nil a rest)
    rw [hsplit, hb] at hcat
    rw [← hcat]
    simp
  -- The missed entry of row `x` is `v* := (v ++ [b]).head` — a fully consumed state.
  obtain ⟨vs, hvs⟩ : ∃ z, (v ++ [b]).head (by simp) = z := ⟨_, rfl⟩
  have hRx : (rowSuccessors x (a :: rest)).getLast? = some vs := by
    rw [hwshape, rowSuccessors_getLast_of_last_occurrence x u v b hxv, hvs]
  have hR'x : (R' x).getLast? = some vs := (hlast x).trans hRx
  have hvsA : (rowSuccessors vs (a :: D)).length = (R' vs).length := by
    cases v with
    | nil =>
        have hvb : vs = b := by rw [← hvs]; simp
        rw [hvb]
        exact hpb
    | cons z v' =>
        have hvz : vs = z := by rw [← hvs]; simp
        rw [hvz]
        exact hvA z (by simp)
  have hR'x_ne : R' x ≠ [] := by
    intro h0
    rw [h0] at hR'x
    simp at hR'x
  have hglx : (R' x).getLast hR'x_ne = vs := by
    have h := List.getLast?_eq_some_getLast (l := R' x) hR'x_ne
    rw [h] at hR'x
    exact Option.some.inj hR'x
  -- Row `x` is a PROPER prefix, so it misses its last entry `v*` at least once.
  have hxlt : (rowSuccessors x (a :: D)).length < (R' x).length :=
    Nat.lt_of_le_of_ne (hpre x).length_le hpx
  have hstrict : (rowSuccessors x (a :: D)).count vs < (R' x).count vs := by
    have h := count_lt_of_proper_prefix_getLast (hpre x) hxlt hR'x_ne
    rwa [hglx] at h
  -- Sum the strict deficit over all rows: the decode enters `v*` strictly less.
  have hsum : (∑ i, ((rowSuccessors i (a :: D)).count vs)) < ∑ i, ((R' i).count vs) :=
    sum_lt_sum_pointwise (fun i => count_le_of_prefix (hpre i) vs) x hstrict
  have hflank : (∑ i, ((R' i).count vs)) = (a :: rest).tail.count vs := by
    rw [Finset.sum_congr rfl (fun i _ => (hperm i).count_eq vs)]
    exact sum_rowSuccessors_count (a :: rest) vs
  have hsumζ := sum_rowSuccessors_count (a :: D) vs
  -- But `v*` is fully consumed, so its OUT-flow (dropLast count) agrees...
  have hdropEq : (a :: D).dropLast.count vs = (a :: rest).dropLast.count vs := by
    have h1 := rowSuccessors_length_eq_count_dropLast vs (a :: D)
    have h2 := rowSuccessors_length_eq_count_dropLast vs (a :: rest)
    have h3 : (R' vs).length = (rowSuccessors vs (a :: rest)).length := (hperm vs).length_eq
    omega
  -- ...and both words start at `a` and end at `b`: flow forces IN-flows equal.
  -- (Head-ite reductions are definitional; getLast rewritten to `b` first.)
  have hflowζ0 := tail_count_add_head_eq_dropLast_count_add_getLast (a :: D)
      (List.cons_ne_nil a D) vs
  rw [hgl, hb] at hflowζ0
  have hflowζ : (a :: D).tail.count vs + (if a = vs then 1 else 0)
      = (a :: D).dropLast.count vs + (if b = vs then 1 else 0) := hflowζ0
  have hflowW0 := tail_count_add_head_eq_dropLast_count_add_getLast (a :: rest)
      (List.cons_ne_nil a rest) vs
  rw [hb] at hflowW0
  have hflowW : (a :: rest).tail.count vs + (if a = vs then 1 else 0)
      = (a :: rest).dropLast.count vs + (if b = vs then 1 else 0) := hflowW0
  obtain ⟨c₁, hc₁⟩ : ∃ n, (if a = vs then 1 else 0) = n := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ n, (if b = vs then 1 else 0) = n := ⟨_, rfl⟩
  rw [hc₁, hc₂] at hflowζ hflowW
  omega

/-- Last-fixing row permutations decode to a FULL-length word
(FLPR Lemma 1(b), length form). -/
theorem decode_lastFixed_length [NeZero k] (a : Fin k) (rest : List (Fin k))
    (R' : Fin k → List (Fin k))
    (hperm : ∀ i, (R' i).Perm (rowSuccessors i (a :: rest)))
    (hlast : ∀ i, (R' i).getLast? = (rowSuccessors i (a :: rest)).getLast?) :
    (decode a R').length = (a :: rest).length := by
  have hfull := decode_lastFixed_rowSuccessors a rest R' hperm hlast
  obtain ⟨D, hD⟩ : ∃ D, decodeAux R' a (∑ i, (R' i).length) = D := ⟨_, rfl⟩
  have hζcons : decode a R' = a :: D := by simp only [decode, hD]
  rw [hζcons] at hfull ⊢
  have h1 := sum_rowSuccessors_length a D
  rw [Finset.sum_congr rfl (fun i _ => congrArg List.length (hfull i))] at h1
  have h2 : (∑ i, (R' i).length) = rest.length := by
    rw [Finset.sum_congr rfl (fun i _ => (hperm i).length_eq)]
    exact sum_rowSuccessors_length a rest
  simp only [List.length_cons]
  omega

/-- Last-fixing row permutations preserve ALL transition counts of the decoded
word (Markov-evidence equivalence, FLPR Lemma 1(b)). -/
theorem decode_lastFixed_transCountL [NeZero k] (a : Fin k) (rest : List (Fin k))
    (R' : Fin k → List (Fin k))
    (hperm : ∀ i, (R' i).Perm (rowSuccessors i (a :: rest)))
    (hlast : ∀ i, (R' i).getLast? = (rowSuccessors i (a :: rest)).getLast?) :
    ∀ p q, transCountL (decode a R') p q = transCountL (a :: rest) p q := by
  intro p q
  have hfull := decode_lastFixed_rowSuccessors a rest R' hperm hlast
  refine transCountL_eq_of_rowPerms (fun i => ?_) p q
  rw [hfull i]
  exact hperm i

/-- Canary: full consumption of row 0 on the GOOD (last-fixing) permutation. -/
example : rowSuccessors (0 : Fin 2) (decode (0 : Fin 2) ExampleOne.rowsGood)
    = ExampleOne.rowsGood 0 := by decide

/-- Canary: full consumption of row 1 on the GOOD (last-fixing) permutation. -/
example : rowSuccessors (1 : Fin 2) (decode (0 : Fin 2) ExampleOne.rowsGood)
    = ExampleOne.rowsGood 1 := by decide

/-! ## Positional list permutation under a support bound -/

/-- Positional permutation of a list by a permutation of `ℕ`, with a junk
guard for out-of-range images (the guard never fires when `σ` is supported
below the length). -/
def permuteList (σ : Equiv.Perm ℕ) (l : List (Fin k)) : List (Fin k) :=
  List.ofFn (fun t : Fin l.length =>
    if h : σ t.1 < l.length then l.get ⟨σ t.1, h⟩ else l.get t)

theorem permuteList_length (σ : Equiv.Perm ℕ) (l : List (Fin k)) :
    (permuteList σ l).length = l.length := by
  simp [permuteList]

/-- A permutation fixing everything above `L` maps `[0, L)` into itself. -/
theorem perm_lt_of_support_lt (σ : Equiv.Perm ℕ) {L : ℕ}
    (hsupp : ∀ n, L ≤ n → σ n = n) : ∀ n < L, σ n < L := by
  intro n hn
  by_contra hge
  have hL : L ≤ σ n := Nat.le_of_not_lt hge
  have hfix : σ (σ n) = σ n := hsupp (σ n) hL
  have heq : σ n = n := σ.injective hfix
  omega

/-- The inverse inherits the support bound. -/
theorem perm_symm_support (σ : Equiv.Perm ℕ) {L : ℕ}
    (hsupp : ∀ n, L ≤ n → σ n = n) : ∀ n, L ≤ n → σ.symm n = n := by
  intro n hn
  have h := hsupp n hn
  calc σ.symm n = σ.symm (σ n) := by rw [h]
  _ = n := σ.symm_apply_apply n

/-- Restriction of a support-bounded permutation of `ℕ` to `Fin L`. -/
def permFinOfSupport (σ : Equiv.Perm ℕ) {L : ℕ}
    (hsupp : ∀ n, L ≤ n → σ n = n) : Equiv.Perm (Fin L) where
  toFun t := ⟨σ t.1, perm_lt_of_support_lt σ hsupp t.1 t.isLt⟩
  invFun t := ⟨σ.symm t.1,
    perm_lt_of_support_lt σ.symm (perm_symm_support σ hsupp) t.1 t.isLt⟩
  left_inv t := by
    apply Fin.ext
    simp
  right_inv t := by
    apply Fin.ext
    simp

/-- Reading a list off by positions is the identity. -/
theorem ofFn_get_self (l : List (Fin k)) : List.ofFn l.get = l :=
  List.ofFn_getElem

/-- The permuted list reads the source at the permuted position (`getElem`
form). -/
theorem permuteList_getElem (σ : Equiv.Perm ℕ) (l : List (Fin k))
    (hsupp : ∀ n, l.length ≤ n → σ n = n) (m : ℕ) (hm : m < l.length)
    (hm' : m < (permuteList σ l).length) :
    (permuteList σ l)[m] = l[σ m]'(perm_lt_of_support_lt σ hsupp m hm) := by
  simp only [permuteList, List.getElem_ofFn]
  rw [dif_pos (perm_lt_of_support_lt σ hsupp m hm)]
  rfl

/-- The permuted list reads the source at the permuted position (`get`/
`Fin.cast` form). -/
theorem permuteList_get (σ : Equiv.Perm ℕ) (l : List (Fin k))
    (hsupp : ∀ n, l.length ≤ n → σ n = n) (t : Fin l.length) :
    (permuteList σ l).get (Fin.cast (permuteList_length σ l).symm t)
      = l.get ⟨σ t.1, perm_lt_of_support_lt σ hsupp t.1 t.isLt⟩ := by
  rw [List.get_eq_getElem]
  simp only [Fin.val_cast]
  rw [permuteList_getElem σ l hsupp t.1 t.isLt
    (by rw [permuteList_length]; exact t.isLt)]
  rfl

/-- Positional permutation preserves the multiset: `permuteList σ l ~ l`. -/
theorem permuteList_perm (σ : Equiv.Perm ℕ) (l : List (Fin k))
    (hsupp : ∀ n, l.length ≤ n → σ n = n) : (permuteList σ l).Perm l := by
  have hofn : permuteList σ l
      = List.ofFn (l.get ∘ (permFinOfSupport σ hsupp)) := by
    unfold permuteList
    congr 1
    funext t
    rw [dif_pos (perm_lt_of_support_lt σ hsupp t.1 t.isLt)]
    rfl
  have h := Equiv.Perm.ofFn_comp_perm (permFinOfSupport σ hsupp) l.get
  rw [ofFn_get_self] at h
  rw [hofn]
  exact h

/-- If `σ` additionally FIXES the last position, the permuted list keeps its
last entry. -/
theorem permuteList_getLast? (σ : Equiv.Perm ℕ) (l : List (Fin k))
    (hsupp : ∀ n, l.length ≤ n → σ n = n)
    (hlast : σ (l.length - 1) = l.length - 1) :
    (permuteList σ l).getLast? = l.getLast? := by
  rcases l with _ | ⟨x, l'⟩
  · simp [permuteList]
  · rw [List.getLast?_eq_getElem?, List.getLast?_eq_getElem?, permuteList_length]
    have hidx : (x :: l').length - 1 < (x :: l').length := by
      simp
    rw [List.getElem?_eq_getElem (by rw [permuteList_length]; exact hidx),
      List.getElem?_eq_getElem hidx]
    congr 1
    rw [permuteList_getElem σ (x :: l') hsupp ((x :: l').length - 1) hidx
      (by rw [permuteList_length]; exact hidx)]
    simp only [hlast]

/-- The identity permutation permutes nothing. -/
theorem permuteList_id (l : List (Fin k)) : permuteList (Equiv.refl ℕ) l = l := by
  have h : permuteList (Equiv.refl ℕ) l = List.ofFn l.get := by
    unfold permuteList
    congr 1
    funext t
    rw [dif_pos (show (Equiv.refl ℕ) t.1 < l.length from t.isLt)]
    rfl
  rw [h, ofFn_get_self]

/-- **Round-trip**: permuting by `σ` then by `σ.symm` restores the list. -/
theorem permuteList_symm_cancel (σ : Equiv.Perm ℕ) (l : List (Fin k))
    (hsupp : ∀ n, l.length ≤ n → σ n = n) :
    permuteList σ.symm (permuteList σ l) = l := by
  have hsupp' : ∀ n, (permuteList σ l).length ≤ n → σ.symm n = n := by
    intro n hn
    rw [permuteList_length] at hn
    exact perm_symm_support σ hsupp n hn
  apply List.ext_getElem
  · rw [permuteList_length, permuteList_length]
  · intro m h₁ h₂
    have hm1 : m < (permuteList σ l).length := by
      rw [permuteList_length]
      exact h₂
    have hs : σ.symm m < l.length :=
      perm_lt_of_support_lt σ.symm (perm_symm_support σ hsupp) m h₂
    rw [permuteList_getElem σ.symm (permuteList σ l) hsupp' m hm1 h₁,
      permuteList_getElem σ l hsupp (σ.symm m) hs
        (by rw [permuteList_length]; exact hs)]
    simp only [Equiv.apply_symm_apply]

/-- Canary: a concrete positional swap. -/
example : permuteList (Equiv.swap 0 1) ([0, 1, 1] : List (Fin 2)) = [1, 0, 1] := by
  decide

/-- Canary: a swap of the first two entries of row 0 of `w₀` is a permutation
of the row. -/
example : (permuteList (Equiv.swap 0 1) (rowSuccessors (0 : Fin 2) ExampleOne.w₀)).Perm
    (rowSuccessors (0 : Fin 2) ExampleOne.w₀) := by decide

/-! ## Concatenation evidence -/

/-- Transitions of a concatenation: in-`w` transitions plus the junction-and-
`u` transitions read from the last symbol of `w`. -/
theorem transCountL_append (w u : List (Fin k)) (hw : w ≠ []) (a b : Fin k) :
    transCountL (w ++ u) a b
      = transCountL w a b + transCountL (w.getLast hw :: u) a b := by
  induction w with
  | nil => exact absurd rfl hw
  | cons x rest ih =>
      cases rest with
      | nil => simp [transCountL]
      | cons y t =>
          simp only [List.cons_append]
          rw [transCountL]
          have ih' := ih (List.cons_ne_nil y t)
          simp only [List.cons_append] at ih'
          rw [ih', transCountL, List.getLast_cons (List.cons_ne_nil y t)]
          omega

/-- Words with equal last symbol and equal transition counts keep equal
transition counts under any common extension. -/
theorem transCountL_eq_of_evidence_extend {w w' : List (Fin k)}
    (hw : w ≠ []) (hw' : w' ≠ [])
    (hlast : w.getLast hw = w'.getLast hw')
    (htc : ∀ a b, transCountL w a b = transCountL w' a b) (u : List (Fin k)) :
    ∀ a b, transCountL (w ++ u) a b = transCountL (w' ++ u) a b := by
  intro a b
  rw [transCountL_append w u hw a b, transCountL_append w' u hw' a b, htc a b, hlast]

end Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiSuccessorDictionary
