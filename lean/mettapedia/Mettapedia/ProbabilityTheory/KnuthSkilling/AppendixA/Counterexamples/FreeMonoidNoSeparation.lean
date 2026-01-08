import Mathlib.Data.List.Lex
import Mathlib.Data.Prod.Lex
import Mettapedia.ProbabilityTheory.KnuthSkilling.Algebra
import Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Counterexamples.RankObstructionLinear

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Counterexamples

open Classical
open KnuthSkillingAlgebra

/-!
# Noncommutative `KnuthSkillingAlgebra` from shortlex words, but `KSSeparation` fails

This is a clean “countermodel probe” in the same spirit as `SemidirectNoSeparation.lean`:

- We build a noncommutative `KnuthSkillingAlgebra` whose elements are words over a finite alphabet,
  ordered by **shortlex** (length first, then lexicographic order).
- We then show `KSSeparation` fails using the general `RankObstructionLinear` lemma with
  `rank := length`.

This does **not** refute K&S Appendix A (which assumes/proves `KSSeparation` as a separate step).
It does give another robust example showing that noncommutative models satisfying the *base*
`KnuthSkillingAlgebra` axioms can still fail `KSSeparation`.
-/

/-! ## Words with shortlex order

We represent a word as a pair `(n, w)` with `n = w.length`, and order by lex on the pair:
first compare `n`, then compare `w` lexicographically. This is definitionally the shortlex order.
-/

abbrev WordBase := Nat ×ₗ List (Fin 3)

abbrev Word := { p : WordBase // (ofLex p).1 = (ofLex p).2.length }

namespace Word

def len (w : Word) : Nat := (ofLex w.1).1
def letters (w : Word) : List (Fin 3) := (ofLex w.1).2

theorem len_eq_length (w : Word) : len w = (letters w).length := by
  simpa [len, letters] using w.2

noncomputable def ident : Word :=
  ⟨toLex (0, []), by simp⟩

@[simp] theorem len_ident : len ident = 0 := by
  simp [ident, len]

@[simp] theorem letters_ident : letters ident = [] := by
  simp [ident, letters]

noncomputable def op (x y : Word) : Word :=
  ⟨toLex (len x + len y, letters x ++ letters y), by
    -- Unfold the `Lex`/`ofLex` wrapper and use the invariant `len = length`.
    have hx : len x = (letters x).length := len_eq_length x
    have hy : len y = (letters y).length := len_eq_length y
    -- The invariant reduces to `len x + len y = (letters x ++ letters y).length`.
    calc len x + len y
        = (letters x).length + (letters y).length := by simpa [hx, hy]
      _ = (letters x ++ letters y).length := by
          simpa using (List.length_append (as := letters x) (bs := letters y)).symm⟩

theorem op_assoc (x y z : Word) : op (op x y) z = op x (op y z) := by
  ext <;> simp [op, len, letters, List.append_assoc, Nat.add_assoc]

@[simp] theorem len_op (x y : Word) : len (op x y) = len x + len y := by
  simp [op, len, letters]

theorem op_ident_right (x : Word) : op x ident = x := by
  ext <;> simp [op, ident, len, letters]

theorem op_ident_left (x : Word) : op ident x = x := by
  ext <;> simp [op, ident, len, letters]

/-! ### Strict monotonicity of concatenation in shortlex

Because the order compares length first, appending a fixed word preserves strict inequalities.
For the tie-break case (equal lengths), we use `List.Lex.append_left` and a small lemma showing
that appending a fixed suffix preserves `List.Lex` when the two lists have the same length.
-/

private theorem lex_append_right_of_length_eq
    {α : Type*} {r : α → α → Prop} {s t : List α}
    (h : List.Lex r s t) (hlen : s.length = t.length) (u : List α) :
    List.Lex r (s ++ u) (t ++ u) := by
  -- With equal lengths, the `nil` constructor is impossible; lex order is decided at a
  -- finite position, so appending a common suffix preserves the relation.
  cases s with
  | nil =>
    cases t with
    | nil => cases h
    | cons _ _ => cases hlen
  | cons a s =>
    cases t with
    | nil => cases hlen
    | cons b t =>
      cases h with
      | rel hab =>
        simpa [List.cons_append] using (List.Lex.rel hab)
      | cons hst =>
        have hlen' : s.length = t.length := by
          simpa using Nat.succ.inj hlen
        simpa [List.cons_append] using List.Lex.cons (lex_append_right_of_length_eq hst hlen' u)

theorem op_strictMono_left (y : Word) : StrictMono (fun x => op x y) := by
  intro x₁ x₂ hx
  -- Unfold the lex order on `Nat ×ₗ List (Fin 3)`.
  have hx' :
      (len x₁ < len x₂) ∨ (len x₁ = len x₂ ∧ (letters x₁ < letters x₂)) := by
    -- Convert `x₁ < x₂` in the subtype to the underlying lex comparison.
    have := (Prod.Lex.toLex_lt_toLex (x := (ofLex x₁.1 : Nat × List (Fin 3)))
      (y := (ofLex x₂.1 : Nat × List (Fin 3)))).1 (by simpa [len, letters] using hx)
    simpa [len, letters, List.lt_iff_lex_lt] using this
  cases hx' with
  | inl hlen_lt =>
    -- Length strictly increases, so the concatenated length strictly increases.
    have : len (op x₁ y) < len (op x₂ y) := by
      simpa [op, len] using Nat.add_lt_add_right hlen_lt (len y)
    -- Back to lex order on the subtype.
    refine (Prod.Lex.toLex_lt_toLex (x := (ofLex (op x₁ y).1 : Nat × List (Fin 3)))
      (y := (ofLex (op x₂ y).1 : Nat × List (Fin 3)))).2 ?_
    exact Or.inl this
  | inr hEq =>
    rcases hEq with ⟨hlen_eq, hlex⟩
    -- Equal lengths; use lex order on the word part and append a fixed suffix.
    have hlex' : List.Lex (· < ·) (letters x₁) (letters x₂) := by
      -- `letters x₁ < letters x₂` is list-lex `<` by `List.lt_iff_lex_lt`.
      simpa [List.lt_iff_lex_lt] using hlex
    have hlen_lists : (letters x₁).length = (letters x₂).length := by
      simpa [len_eq_length] using hlen_eq
    have hlex_app : List.Lex (· < ·) (letters x₁ ++ letters y) (letters x₂ ++ letters y) :=
      lex_append_right_of_length_eq hlex' hlen_lists (letters y)
    -- Package back into the pair-lex order.
    refine (Prod.Lex.toLex_lt_toLex (x := (ofLex (op x₁ y).1 : Nat × List (Fin 3)))
      (y := (ofLex (op x₂ y).1 : Nat × List (Fin 3)))).2 ?_
    refine Or.inr ?_
    refine ⟨by simpa [op, len] using congrArg (fun n => n + len y) hlen_eq, ?_⟩
    -- Convert `List.Lex` back to list `<`.
    simpa [op, letters, List.lt_iff_lex_lt] using hlex_app

theorem op_strictMono_right (x : Word) : StrictMono (fun y => op x y) := by
  intro y₁ y₂ hy
  have hy' :
      (len y₁ < len y₂) ∨ (len y₁ = len y₂ ∧ (letters y₁ < letters y₂)) := by
    have := (Prod.Lex.toLex_lt_toLex (x := (ofLex y₁.1 : Nat × List (Fin 3)))
      (y := (ofLex y₂.1 : Nat × List (Fin 3)))).1 (by simpa [len, letters] using hy)
    simpa [len, letters, List.lt_iff_lex_lt] using this
  cases hy' with
  | inl hlen_lt =>
    have : len (op x y₁) < len (op x y₂) := by
      simpa [op, len] using Nat.add_lt_add_left hlen_lt (len x)
    refine (Prod.Lex.toLex_lt_toLex (x := (ofLex (op x y₁).1 : Nat × List (Fin 3)))
      (y := (ofLex (op x y₂).1 : Nat × List (Fin 3)))).2 ?_
    exact Or.inl this
  | inr hEq =>
    rcases hEq with ⟨hlen_eq, hlex⟩
    have hlex' : List.Lex (· < ·) (letters y₁) (letters y₂) := by
      simpa [List.lt_iff_lex_lt] using hlex
    have hlex_pref : List.Lex (· < ·) (letters x ++ letters y₁) (letters x ++ letters y₂) :=
      List.Lex.append_left (· < ·) hlex' (letters x)
    refine (Prod.Lex.toLex_lt_toLex (x := (ofLex (op x y₁).1 : Nat × List (Fin 3)))
      (y := (ofLex (op x y₂).1 : Nat × List (Fin 3)))).2 ?_
    refine Or.inr ?_
    refine ⟨by simpa [op, len] using congrArg (fun n => len x + n) hlen_eq, ?_⟩
    simpa [op, letters, List.lt_iff_lex_lt] using hlex_pref

private theorem len_iterate_op (x : Word) :
    ∀ n : ℕ, len (Nat.iterate (op x) n x) = (n + 1) * len x := by
  intro n
  -- Helper: length adds under concatenation.
  have len_op : ∀ u v : Word, len (op u v) = len u + len v := by
    intro u v
    simp [op, len, letters, len_eq_length u, len_eq_length v]
  induction n with
  | zero =>
    simp [len]
  | succ n ih =>
    -- Prefer `iterate_succ_apply'` to expand as `f (f^[n] x)` (not `f^[n] (f x)`).
    -- Here `f := op x`, so this becomes `op x (iterate n x)`.
    calc
      len (Nat.iterate (op x) (n + 1) x)
          = len (op x (Nat.iterate (op x) n x)) := by
              simp [Function.iterate_succ_apply', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      _ = len x + len (Nat.iterate (op x) n x) := by
            simpa using (len_op x (Nat.iterate (op x) n x))
      _ = len x + (n + 1) * len x := by rw [ih]
      _ = (n + 1) * len x + len x := by simpa [Nat.add_comm]
      _ = (n + 2) * len x := by
            -- `(n+2) * L = (n+1) * L + L`
            simpa [Nat.add_assoc, Nat.succ_eq_add_one] using (Nat.succ_mul (n + 1) (len x)).symm

theorem op_archimedean (x y : Word) (hx : ident < x) : ∃ n : ℕ, y < Nat.iterate (op x) n x := by
  -- Any `x > ident` must have positive length (since `ident` is the unique length-0 word).
  have hx_len : 0 < len x := by
    have hx' := (Prod.Lex.toLex_lt_toLex (x := (ofLex ident.1 : Nat × List (Fin 3)))
      (y := (ofLex x.1 : Nat × List (Fin 3)))).1 (by simpa [ident, len, letters] using hx)
    rcases hx' with hlen_lt | ⟨hlen_eq, _⟩
    · simpa [ident, len] using hlen_lt
    · -- `ident` has length 0, so equal length forces `x = ident`, contradicting strictness.
      have hx0 : len x = 0 := by simpa [ident, len] using hlen_eq.symm
      have : letters x = [] := by
        apply List.eq_nil_of_length_eq_zero
        exact (len_eq_length x).symm.trans hx0
      have hx_ident : x = ident := by
        -- Equality in the subtype reduces to equality of the underlying `WordBase`.
        apply Subtype.ext
        calc (x : WordBase)
            = toLex (ofLex (x : WordBase)) := (toLex_ofLex (x : WordBase)).symm
          _ = toLex (len x, letters x) := by simp [len, letters]
          _ = toLex (0, []) := by simp [hx0, this]
          _ = (ident : WordBase) := rfl
      exfalso
      exact (lt_irrefl (ident : Word)) (hx_ident ▸ hx)
  -- Choose `n = len y`, so the iterate has length ≥ (len y + 1) * len x > len y.
  refine ⟨len y, ?_⟩
  have hlen_lt :
      len y < len (Nat.iterate (op x) (len y) x) := by
    have hx1 : 1 ≤ len x := Nat.succ_le_iff.mp hx_len
    calc len y < (len y + 1) := Nat.lt_succ_self _
      _ ≤ (len y + 1) * len x := by
        simpa [Nat.one_mul] using Nat.mul_le_mul_left (len y + 1) hx1
      _ = len (Nat.iterate (op x) (len y) x) := by
        simpa [len_iterate_op] using (len_iterate_op x (len y)).symm
  -- In shortlex, a strict length inequality implies a strict order inequality.
  refine (Prod.Lex.toLex_lt_toLex (x := (ofLex y.1 : Nat × List (Fin 3)))
    (y := (ofLex (Nat.iterate (op x) (len y) x).1 : Nat × List (Fin 3)))).2 ?_
  exact Or.inl hlen_lt

theorem ident_le (x : Word) : ident ≤ x := by
  -- `ident` has the minimal length 0 and is the only word of length 0.
  by_cases hx : x = ident
  · simpa [hx]
  · have hx' : len ident < len x := by
      -- If `x ≠ ident`, then `len x ≠ 0`, hence `0 < len x`.
      have : len x ≠ 0 := by
        intro h0
        have hx_letters_nil : letters x = [] := by
          apply List.eq_nil_of_length_eq_zero
          exact (len_eq_length x).symm.trans h0
        have : x = ident := by
          apply Subtype.ext
          calc (x : WordBase)
              = toLex (ofLex (x : WordBase)) := (toLex_ofLex (x : WordBase)).symm
            _ = toLex (len x, letters x) := by simp [len, letters]
            _ = toLex (0, []) := by simp [h0, hx_letters_nil]
            _ = (ident : WordBase) := rfl
        exact hx this
      exact Nat.pos_of_ne_zero this
    exact le_of_lt (show ident < x from (Prod.Lex.toLex_lt_toLex
      (x := (ofLex ident.1 : Nat × List (Fin 3))) (y := (ofLex x.1 : Nat × List (Fin 3)))).2
        (Or.inl (by simpa [ident, len] using hx')))

noncomputable instance : KnuthSkillingAlgebra Word where
  op := op
  ident := ident
  op_assoc := op_assoc
  op_ident_right := op_ident_right
  op_ident_left := op_ident_left
  op_strictMono_left := op_strictMono_left
  op_strictMono_right := op_strictMono_right
  op_archimedean := op_archimedean
  ident_le := ident_le

@[simp] theorem len_KS_ident : (KnuthSkillingAlgebra.ident (α := Word)).len = 0 := by
  rfl

@[simp] theorem len_KS_op (x y : Word) :
    (KnuthSkillingAlgebra.op x y).len = x.len + y.len := by
  rfl

/-! ## Noncommutativity and failure of `KSSeparation` -/

theorem op_not_comm : ∃ x y : Word, op x y ≠ op y x := by
  -- Words `[0]` and `[1]` do not commute under concatenation.
  let w0 : Word := ⟨toLex (1, [0]), by simp⟩
  let w1 : Word := ⟨toLex (1, [1]), by simp⟩
  refine ⟨w0, w1, ?_⟩
  -- Compare the underlying lists.
  intro hEq
  have : letters (op w0 w1) = letters (op w1 w0) := by simpa [hEq]
  simp [op, w0, w1, letters] at this

theorem not_KSSeparation : ¬ KSSeparation Word := by
  -- Apply the rank obstruction with `rank := length`.
  classical
  let R : RankDataLinear (α := Word) ℕ :=
    { rk := fun w => len w
      rk_le_of_le := by
        intro x y hxy
        -- `x ≤ y` in shortlex implies `len x ≤ len y`.
        rcases le_iff_lt_or_eq.mp hxy with hlt | rfl
        · have := (Prod.Lex.toLex_lt_toLex (x := (ofLex x.1 : Nat × List (Fin 3)))
            (y := (ofLex y.1 : Nat × List (Fin 3)))).1 (by simpa [len, letters] using hlt)
          rcases this with hlen_lt | ⟨hlen_eq, _⟩
          · exact le_of_lt (by simpa [len] using hlen_lt)
          · simpa [len] using le_of_eq hlen_eq
        · rfl
      rk_iterate := by
        intro x n
        -- In this model, `iterate_op` concatenates `x` with itself `n` times, so lengths add.
        induction n with
        | zero =>
          simp [KnuthSkillingAlgebra.iterate_op]
        | succ n ih =>
          -- `iterate_op x (n+1) = op x (iterate_op x n)`
          calc
            len (iterate_op x (n + 1))
                = len x + len (iterate_op x n) := by
                    simpa [KnuthSkillingAlgebra.iterate_op] using len_KS_op x (iterate_op x n)
            _ = len x + n • len x := by rw [ih]
            _ = n • len x + len x := by simpa [Nat.add_comm]
            _ = (n + 1) • len x := by
                    -- `nsmul` on `ℕ` is multiplication, so this is `n*L + L = (n+1)*L`.
                    simpa [nsmul_eq_mul, Nat.succ_eq_add_one] using (Nat.succ_mul n (len x)).symm
      rk_pos_of_ident_lt := by
        intro x hx
        -- Same idea as in `op_archimedean`: either the length increases, or equal length
        -- would force `x = ident` (impossible under strict inequality).
        have hx' := (Prod.Lex.toLex_lt_toLex (x := (ofLex ident.1 : Nat × List (Fin 3)))
          (y := (ofLex x.1 : Nat × List (Fin 3)))).1 (by simpa [ident, len, letters] using hx)
        rcases hx' with hlen_lt | ⟨hlen_eq, _⟩
        · simpa [ident, len] using hlen_lt
        · have hx0 : len x = 0 := by simpa [ident, len] using hlen_eq.symm
          have hx_letters_nil : letters x = [] := by
            apply List.eq_nil_of_length_eq_zero
            exact (len_eq_length x).symm.trans hx0
          have hx_ident : x = ident := by
            apply Subtype.ext
            calc (x : WordBase)
                = toLex (ofLex (x : WordBase)) := (toLex_ofLex (x : WordBase)).symm
              _ = toLex (len x, letters x) := by simp [len, letters]
              _ = toLex (0, []) := by simp [hx0, hx_letters_nil]
              _ = (ident : WordBase) := rfl
          exfalso
          exact (ne_of_lt hx) hx_ident.symm }
  -- Pick three length-1 words `[0] < [1] < [2]`.
  let a : Word := ⟨toLex (1, [0]), by simp⟩
  let x : Word := ⟨toLex (1, [1]), by simp⟩
  let y : Word := ⟨toLex (1, [2]), by simp⟩
  have ha_pos : ident < a := by
    -- length increases from 0 to 1
    refine (Prod.Lex.toLex_lt_toLex (x := (ofLex ident.1 : Nat × List (Fin 3)))
      (y := (ofLex a.1 : Nat × List (Fin 3)))).2 ?_
    exact Or.inl (by simp [ident, a, len])
  have hx_pos : ident < x := by
    refine (Prod.Lex.toLex_lt_toLex (x := (ofLex ident.1 : Nat × List (Fin 3)))
      (y := (ofLex x.1 : Nat × List (Fin 3)))).2 ?_
    exact Or.inl (by simp [ident, x, len])
  have hy_pos : ident < y := by
    refine (Prod.Lex.toLex_lt_toLex (x := (ofLex ident.1 : Nat × List (Fin 3)))
      (y := (ofLex y.1 : Nat × List (Fin 3)))).2 ?_
    exact Or.inl (by simp [ident, y, len])
  have hax : a < x := by
    refine (Prod.Lex.toLex_lt_toLex (x := (ofLex a.1 : Nat × List (Fin 3)))
      (y := (ofLex x.1 : Nat × List (Fin 3)))).2 ?_
    refine Or.inr ?_
    refine ⟨by simp [a, x, len], ?_⟩
    -- `[0] < [1]` in list lex
    simpa [List.lt_iff_lex_lt] using (List.Lex.rel (by decide : (0 : Fin 3) < 1))
  have hxy : x < y := by
    refine (Prod.Lex.toLex_lt_toLex (x := (ofLex x.1 : Nat × List (Fin 3)))
      (y := (ofLex y.1 : Nat × List (Fin 3)))).2 ?_
    refine Or.inr ?_
    refine ⟨by simp [x, y, len], ?_⟩
    simpa [List.lt_iff_lex_lt] using (List.Lex.rel (by decide : (1 : Fin 3) < 2))
  have h_rk_eq : R.rk a = R.rk x ∧ R.rk x = R.rk y := by
    simp [R, a, x, y, len]
  have hChain :
      ∃ a0 x0 y0 : Word,
        ident < a0 ∧ ident < x0 ∧ ident < y0 ∧ a0 < x0 ∧ x0 < y0 ∧
        R.rk a0 = R.rk x0 ∧ R.rk x0 = R.rk y0 := by
    refine ⟨a, x, y, ha_pos, hx_pos, hy_pos, hax, hxy, h_rk_eq.1, h_rk_eq.2⟩
  exact not_KSSeparation_of_same_rank_linear (α := Word) (β := ℕ) R hChain

end Word

end Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Counterexamples
