import Mathlib.Tactic

/-!
# Prefix intervals of a lexicographic order over term keys

A priority space orders its rows by the standard order of terms, which reads a
term's nodes in preorder and compares them in turn, a shorter key that is a
beginning of a longer one standing first. In the abstract that is the
lexicographic order of token strings. This file proves the laws the order's
searches rely on, for keys that are lists over any linear order of tokens:

* `lexLe` is a total order (`lexLe_refl`, `lexLe_antisymm`, `lexLe_trans`,
  `lexLe_total`);
* `prefix_convex`: the keys that begin with a given string stand together, so a
  read of a pattern's ground front is one interval of the order, however long
  the front is;
* `take_prefix_of_prefix`: cutting the front short gives an interval that holds
  the full front's, which is sound but wider;
* `lcp_resume`: every key between two keys shares with a probe at least the
  shorter of the probe's common prefixes with those two, so a search may resume
  each comparison past them;
* `flat_cover`: a row that a flat pattern matches either begins with the
  pattern's front or holds a variable at some place of the front and begins
  with the front before that place: one interval for the front and one for each
  place where some row's first variable stands.

The term encoding itself (preorder tokens, a variable as the least token) is
described in the design note; here keys are lists of tokens.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Order.PrefixInterval

variable {α : Type*} [LinearOrder α]

/-- The lexicographic order on token strings: a string that is a beginning of
another stands before it. -/
def lexLe : List α → List α → Prop
  | [], _ => True
  | _ :: _, [] => False
  | a :: as, b :: bs => a < b ∨ (a = b ∧ lexLe as bs)

@[simp] theorem lexLe_nil (b : List α) : lexLe [] b := by simp [lexLe]

@[simp] theorem lexLe_cons_nil (a : α) (as : List α) : ¬ lexLe (a :: as) [] := by
  simp [lexLe]

@[simp] theorem lexLe_cons_cons (a b : α) (as bs : List α) :
    lexLe (a :: as) (b :: bs) ↔ a < b ∨ (a = b ∧ lexLe as bs) := by
  simp [lexLe]

theorem lexLe_refl : ∀ a : List α, lexLe a a
  | [] => by simp
  | x :: xs => by simp [lexLe_refl xs]

theorem lexLe_antisymm : ∀ a b : List α, lexLe a b → lexLe b a → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: xs, y :: ys, h₁, h₂ => by
    simp only [lexLe_cons_cons] at h₁ h₂
    rcases h₁ with h₁ | ⟨rfl, h₁⟩
    · rcases h₂ with h₂ | ⟨h₂, _⟩
      · exact absurd (h₁.trans h₂) (lt_irrefl _)
      · exact absurd h₁ (by rw [h₂]; exact lt_irrefl _)
    · rcases h₂ with h₂ | ⟨_, h₂⟩
      · exact absurd h₂ (lt_irrefl _)
      · rw [lexLe_antisymm xs ys h₁ h₂]

theorem lexLe_trans : ∀ a b c : List α, lexLe a b → lexLe b c → lexLe a c
  | [], _, _, _, _ => by simp
  | _ :: _, [], _, h, _ => by simp at h
  | _ :: _, _ :: _, [], _, h => by simp at h
  | x :: xs, y :: ys, z :: zs, h₁, h₂ => by
    simp only [lexLe_cons_cons] at h₁ h₂ ⊢
    rcases h₁ with h₁ | ⟨rfl, h₁⟩
    · rcases h₂ with h₂ | ⟨rfl, _⟩
      · exact Or.inl (h₁.trans h₂)
      · exact Or.inl h₁
    · rcases h₂ with h₂ | ⟨rfl, h₂⟩
      · exact Or.inl h₂
      · exact Or.inr ⟨rfl, lexLe_trans xs ys zs h₁ h₂⟩

theorem lexLe_total : ∀ a b : List α, lexLe a b ∨ lexLe b a
  | [], _ => Or.inl (by simp)
  | _ :: _, [] => Or.inr (by simp)
  | x :: xs, y :: ys => by
    simp only [lexLe_cons_cons]
    rcases lt_trichotomy x y with h | rfl | h
    · exact Or.inl (Or.inl h)
    · rcases lexLe_total xs ys with h | h
      · exact Or.inl (Or.inr ⟨rfl, h⟩)
      · exact Or.inr (Or.inr ⟨rfl, h⟩)
    · exact Or.inr (Or.inl h)

/-- The keys that begin with `w` form an interval: a key standing between two
keys that begin with `w` begins with `w`. No length of `w` is special. -/
theorem prefix_convex :
    ∀ (w a b c : List α), lexLe a b → lexLe b c → w <+: a → w <+: c → w <+: b
  | [], _, _, _, _, _, _, _ => List.nil_prefix
  | x :: w, a, b, c, hab, hbc, ha, hc => by
    obtain ⟨a', rfl⟩ : ∃ a', a = x :: (w ++ a') := by
      obtain ⟨t, rfl⟩ := ha; exact ⟨t, rfl⟩
    obtain ⟨c', rfl⟩ : ∃ c', c = x :: (w ++ c') := by
      obtain ⟨t, rfl⟩ := hc; exact ⟨t, rfl⟩
    cases b with
    | nil => simp at hab
    | cons y b =>
      simp only [lexLe_cons_cons] at hab hbc
      have hy : x = y ∧ lexLe (w ++ a') b ∧ lexLe b (w ++ c') := by
        rcases hab with hab | ⟨rfl, hab⟩
        · rcases hbc with hbc | ⟨hbc, _⟩
          · exact absurd (hab.trans hbc) (lt_irrefl _)
          · exact absurd hab (by rw [hbc]; exact lt_irrefl _)
        · rcases hbc with hbc | ⟨_, hbc⟩
          · exact absurd hbc (lt_irrefl _)
          · exact ⟨rfl, hab, hbc⟩
      obtain ⟨rfl, hab', hbc'⟩ := hy
      exact List.cons_prefix_cons.mpr
        ⟨rfl, prefix_convex w (w ++ a') b (w ++ c') hab' hbc'
          (List.prefix_append w a') (List.prefix_append w c')⟩

omit [LinearOrder α] in
/-- Cutting a front short keeps every key the full front selects: the shorter
front's interval holds the longer one's. -/
theorem take_prefix_of_prefix (w x : List α) (m : ℕ) (h : w <+: x) :
    w.take m <+: x :=
  (List.take_prefix m w).trans h

/-- The longest common prefix of two keys, counted in tokens. -/
def lcp : List α → List α → ℕ
  | a :: as, b :: bs => if a = b then lcp as bs + 1 else 0
  | _, _ => 0

theorem lcp_le_length_left : ∀ f x : List α, lcp f x ≤ f.length
  | [], _ => by simp [lcp]
  | _ :: _, [] => by simp [lcp]
  | a :: as, b :: bs => by
    unfold lcp
    split_ifs
    · simp only [List.length_cons]; have := lcp_le_length_left as bs; omega
    · omega

/-- The first `lcp f x` tokens of `f` begin `x`. -/
theorem take_lcp_prefix : ∀ f x : List α, f.take (lcp f x) <+: x
  | [], _ => by simp [lcp]
  | _ :: _, [] => by simp [lcp]
  | a :: as, b :: bs => by
    unfold lcp
    split_ifs with h
    · subst h
      simp only [List.take_succ_cons]
      exact List.cons_prefix_cons.mpr ⟨rfl, take_lcp_prefix as bs⟩
    · simp

/-- If the first `m` tokens of `f` begin `x`, the two share at least `m`. -/
theorem le_lcp_of_take_prefix :
    ∀ (f x : List α) (m : ℕ), m ≤ f.length → f.take m <+: x → m ≤ lcp f x
  | _, _, 0, _, _ => Nat.zero_le _
  | [], _, _ + 1, hm, _ => by simp at hm
  | a :: as, [], m + 1, _, h => by
    simp only [List.take_succ_cons] at h
    exact absurd h (by simp)
  | a :: as, b :: bs, m + 1, hm, h => by
    simp only [List.take_succ_cons, List.cons_prefix_cons] at h
    obtain ⟨rfl, h⟩ := h
    have hl : lcp (a :: as) (a :: bs) = lcp as bs + 1 := by simp [lcp]
    rw [hl]
    simp only [List.length_cons] at hm
    have := le_lcp_of_take_prefix as bs m (by omega) h
    omega

/-- Resuming a comparison: a probe shares with any key between `a` and `c` at
least the smaller of what it shares with `a` and with `c`. A search that knows
the probe's common prefix with the rows bounding the subtree it descends may
begin every comparison past the smaller of the two. -/
theorem lcp_resume (f a b c : List α) (hab : lexLe a b) (hbc : lexLe b c) :
    min (lcp f a) (lcp f c) ≤ lcp f b := by
  set m := min (lcp f a) (lcp f c)
  have hmf : m ≤ f.length := le_trans (min_le_left _ _) (lcp_le_length_left f a)
  have ha : f.take m <+: a :=
    (List.take_prefix_take_left (min_le_left _ _)).trans (take_lcp_prefix f a)
  have hc : f.take m <+: c :=
    (List.take_prefix_take_left (min_le_right _ _)).trans (take_lcp_prefix f c)
  exact le_lcp_of_take_prefix f b m hmf (prefix_convex _ a b c hab hbc ha hc)

/-! ## The cover of a flat pattern

A flat expression is a string of places; a place of a pattern or of a row holds
a ground token or a variable (`none`). A pattern matches a row of its length
when at each place one of the two holds a variable or both hold the same token.
The pattern's front is its tokens before its first variable. -/

section Flat

variable {β : Type*}

/-- A flat pattern matches a flat row. -/
def Matches : List (Option β) → List (Option β) → Prop
  | [], [] => True
  | p :: ps, x :: xs => (p = none ∨ x = none ∨ p = x) ∧ Matches ps xs
  | _, _ => False

/-- The pattern's ground front: its tokens before its first variable. -/
def front : List (Option β) → List β
  | some a :: ps => a :: front ps
  | _ => []

/-- A row a flat pattern matches either begins with the pattern's front, or
holds a variable at some place `t` of the front and begins with the front's
first `t` tokens. So the rows a pattern may match stand in at most one interval
per place of the front at which some row's first variable stands, and the
front's own interval. -/
theorem flat_cover :
    ∀ (p x : List (Option β)), Matches p x →
      (front p).map some <+: x ∨
        ∃ t < (front p).length, x[t]? = some none ∧
          ((front p).take t).map some <+: x
  | [], [], _ => Or.inl (by simp [front])
  | [], _ :: _, h => by simp [Matches] at h
  | _ :: _, [], h => by simp [Matches] at h
  | none :: ps, x :: xs, _ => Or.inl (by simp [front])
  | some a :: ps, x :: xs, h => by
    simp only [Matches] at h
    obtain ⟨hhead, htail⟩ := h
    rcases x with _ | b
    · -- the row holds a variable at the front's first place
      exact Or.inr ⟨0, by simp [front], by simp, by simp⟩
    · have hab : b = a := by
        rcases hhead with h | h | h
        · exact absurd h (by simp)
        · exact absurd h (by simp)
        · exact (Option.some.inj h).symm
      subst hab
      rcases flat_cover ps xs htail with h | ⟨t, ht, hvar, hpre⟩
      · exact Or.inl (by simpa [front] using h)
      · refine Or.inr ⟨t + 1, by simp [front]; omega, by simpa using hvar, ?_⟩
        simpa [front] using hpre

end Flat

/-! ## A front cut short

In a store whose rows all begin with the same `m` tokens, a search by a front
cut to `m` tokens finds every row, and a reader that stops at its one answer
walks to that answer's rank. Reading `n` keys in turn then walks
`1 + 2 + ... + n` rows, where the whole front finds each answer at once. -/

/-- Rows walked by `n` reads that each start at the least row and stop at
the row of rank `i`: the triangle number. -/
theorem truncated_walks (n : ℕ) :
    (∑ i ∈ Finset.range n, (i + 1)) * 2 = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    ring

end Mettapedia.Machines.Order.PrefixInterval
