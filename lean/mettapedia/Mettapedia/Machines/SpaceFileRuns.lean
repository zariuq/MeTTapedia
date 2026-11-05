import Mathlib.Tactic

/-!
# Space file v1: a lookup on any column order reads one run

A relation's facts are kept in indexes, each sorted by a column order: a
fact's key is its columns read in that order, compared lexicographically.
A lookup binds the first columns of an order to values `p`.

This file proves, for every column order and every bound prefix:
* `prefix_between`: whatever lies, in lexicographic order, between two keys
  that start with `p` starts with `p` too;
* `filter_eq_run`: in a sorted list, the holders of such a convex test are
  one run, reached by skipping the leading non-holders and read while the
  test holds;
* `lookup_eq_filter`, `lookup_perm_scan`: the index's run for `p` is exactly
  the facts a scan of the relation selects, as a bag;
* `seekRun_eq_run`, `seek_perm_scan`: the cursor's read (seek to the first
  key not below `p`, then read while keys start with `p`) is that run.

So a lookup on a bound prefix of any column order reads one contiguous range
of the file, and answers what a scan answers.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SpaceFileRuns

/-! ## Keys in lexicographic order -/

/-- Lexicographic order on keys, a proper prefix first: the order of byte
keys compared by `memcmp` and then by length. -/
def lexLE : List ℕ → List ℕ → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: x, b :: y => decide (a < b) || (decide (a = b) && lexLE x y)

theorem lexLE_trans :
    ∀ x y z : List ℕ, lexLE x y = true → lexLE y z = true → lexLE x z = true := by
  intro x
  induction x with
  | nil => intro _ _ _ _; rfl
  | cons a x ih =>
    intro y z hxy hyz
    rcases y with _ | ⟨b, y⟩
    · simp [lexLE] at hxy
    rcases z with _ | ⟨c, z⟩
    · simp [lexLE] at hyz
    simp only [lexLE, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hxy hyz ⊢
    rcases hxy with h1 | ⟨rfl, h1⟩
    · rcases hyz with h2 | ⟨rfl, _⟩
      · exact Or.inl (lt_trans h1 h2)
      · exact Or.inl h1
    · rcases hyz with h2 | ⟨rfl, h2⟩
      · exact Or.inl h2
      · exact Or.inr ⟨rfl, ih y z h1 h2⟩

theorem lexLE_total : ∀ x y : List ℕ, (lexLE x y || lexLE y x) = true := by
  intro x
  induction x with
  | nil => intro _; simp [lexLE]
  | cons a x ih =>
    intro y
    rcases y with _ | ⟨b, y⟩
    · simp [lexLE]
    have hxy := ih y
    simp only [lexLE, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hxy ⊢
    rcases lt_trichotomy a b with h | rfl | h
    · exact Or.inl (Or.inl h)
    · rcases hxy with h' | h'
      · exact Or.inl (Or.inr ⟨rfl, h'⟩)
      · exact Or.inr (Or.inr ⟨rfl, h'⟩)
    · exact Or.inr (Or.inl h)

/-- Whatever lies between two keys that start with `p` starts with `p`. -/
theorem prefix_between (p : List ℕ) :
    ∀ x y z : List ℕ, lexLE x y = true → lexLE y z = true →
      p <+: x → p <+: z → p <+: y := by
  induction p with
  | nil => intro _ _ _ _ _ _ _; exact List.nil_prefix
  | cons a p ih =>
    intro x y z hxy hyz hx hz
    rcases x with _ | ⟨b, x⟩
    · simp at hx
    rcases z with _ | ⟨c, z⟩
    · simp at hz
    rw [List.cons_prefix_cons] at hx hz
    obtain ⟨rfl, hx⟩ := hx
    obtain ⟨rfl, hz⟩ := hz
    rcases y with _ | ⟨d, y⟩
    · simp [lexLE] at hxy
    simp only [lexLE, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hxy hyz
    rcases hxy with h1 | ⟨rfl, h1⟩
    · rcases hyz with h2 | ⟨rfl, _⟩ <;> omega
    · rcases hyz with h2 | ⟨_, h2⟩
      · omega
      · rw [List.cons_prefix_cons]
        exact ⟨rfl, ih x y z h1 h2 hx hz⟩

/-! ## Convex tests select one run of a sorted list -/

variable {α : Type*}

/-- A test whose holders are convex for a relation: whatever lies between
two holders holds it too. -/
def Convex (r : α → α → Prop) (P : α → Bool) : Prop :=
  ∀ x y z, r x y → r y z → P x = true → P z = true → P y = true

/-- After a holder `x`, in a sorted list above `x`, the holders are exactly
the leading ones. -/
theorem filter_eq_takeWhile (r : α → α → Prop) (P : α → Bool) (hP : Convex r P)
    (x : α) (hx : P x = true) :
    ∀ l : List α, l.Pairwise r → (∀ y ∈ l, r x y) → l.filter P = l.takeWhile P := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons y ys ih =>
    intro hs hxl
    have hys : ys.Pairwise r := hs.of_cons
    by_cases hy : P y = true
    · rw [List.filter_cons_of_pos hy, List.takeWhile_cons_of_pos hy,
        ih hys (fun z hz => hxl z (List.mem_cons_of_mem _ hz))]
    · have hnone : ys.filter P = [] := by
        rw [List.filter_eq_nil_iff]
        intro z hz hPz
        exact hy (hP x y z (hxl y List.mem_cons_self)
          (List.rel_of_pairwise_cons hs hz) hx hPz)
      rw [List.filter_cons_of_neg hy, hnone, List.takeWhile_cons_of_neg hy]

/-- In a sorted list, a convex test's holders form one run: skip the
non-holders, then read while the test holds. -/
theorem filter_eq_run (r : α → α → Prop) (P : α → Bool) (hP : Convex r P) :
    ∀ l : List α, l.Pairwise r →
      l.filter P = (l.dropWhile (fun a => !P a)).takeWhile P := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons y ys ih =>
    intro hs
    by_cases hy : P y = true
    · have hdrop : (y :: ys).dropWhile (fun a => !P a) = y :: ys := by
        simp [hy]
      rw [hdrop, List.filter_cons_of_pos hy, List.takeWhile_cons_of_pos hy,
        filter_eq_takeWhile r P hP y hy ys hs.of_cons
          (fun z hz => List.rel_of_pairwise_cons hs hz)]
    · have hdrop : (y :: ys).dropWhile (fun a => !P a) = ys.dropWhile (fun a => !P a) := by
        simp [hy]
      rw [hdrop, List.filter_cons_of_neg hy]
      exact ih hs.of_cons

/-! ## The relation index -/

/-- A fact as the codes of its columns. -/
abbrev Fact := List ℕ

/-- A fact's key for a column order: its columns read in that order. -/
def key (order : List ℕ) (f : Fact) : List ℕ := order.map (fun i => f.getD i 0)

/-- The index for a column order: the facts sorted by their keys. -/
def index (order : List ℕ) (facts : List Fact) : List Fact :=
  facts.mergeSort (fun f g => lexLE (key order f) (key order g))

/-- A lookup binding the first columns of the order to `p`. -/
def bound (order p : List ℕ) (f : Fact) : Bool := decide (p <+: key order f)

/-- What a scan of the relation answers. -/
def scan (order p : List ℕ) (facts : List Fact) : List Fact :=
  facts.filter (bound order p)

/-- What the file answers: one run of the index. -/
def lookup (order p : List ℕ) (facts : List Fact) : List Fact :=
  ((index order facts).dropWhile (fun f => !bound order p f)).takeWhile (bound order p)

theorem index_sorted (order : List ℕ) (facts : List Fact) :
    (index order facts).Pairwise (fun f g => lexLE (key order f) (key order g) = true) :=
  List.pairwise_mergeSort (le := fun f g => lexLE (key order f) (key order g))
    (fun a b c hab hbc => lexLE_trans (key order a) (key order b) (key order c) hab hbc)
    (fun a b => lexLE_total (key order a) (key order b)) facts

theorem bound_convex (order p : List ℕ) :
    Convex (fun f g => lexLE (key order f) (key order g) = true) (bound order p) := by
  intro x y z hxy hyz hx hz
  simp only [bound, decide_eq_true_eq] at *
  exact prefix_between p _ _ _ hxy hyz hx hz

/-- The run is the facts of the index the lookup binds. -/
theorem lookup_eq_filter (order p : List ℕ) (facts : List Fact) :
    lookup order p facts = (index order facts).filter (bound order p) :=
  (filter_eq_run _ _ (bound_convex order p) _ (index_sorted order facts)).symm

/-- The run holds exactly the facts a scan selects, as a bag. -/
theorem lookup_perm_scan (order p : List ℕ) (facts : List Fact) :
    (lookup order p facts).Perm (scan order p facts) := by
  rw [lookup_eq_filter]
  exact (List.mergeSort_perm _ _).filter _

/-! ## Seeking: the run starts at the first key not below `p` -/

/-- A key strictly below another. -/
def lexLT (x y : List ℕ) : Bool := !lexLE y x

/-- Skipping while a test holds of every element leaves nothing. -/
theorem dropWhile_of_all {β : Type*} (P : β → Bool) :
    ∀ l : List β, (∀ z ∈ l, P z = true) → l.dropWhile P = [] := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons y ys ih =>
    intro h
    rw [List.dropWhile_cons_of_pos (h y List.mem_cons_self)]
    exact ih (fun z hz => h z (List.mem_cons_of_mem _ hz))

/-- A key starting with `p` is not below `p`. -/
theorem lexLE_of_prefix : ∀ p k : List ℕ, p <+: k → lexLE p k = true := by
  intro p
  induction p with
  | nil => intro _ _; rfl
  | cons a p ih =>
    intro k hk
    rcases k with _ | ⟨b, k⟩
    · simp at hk
    rw [List.cons_prefix_cons] at hk
    obtain ⟨rfl, hk⟩ := hk
    simp [lexLE, ih k hk]

/-- What the cursor reads: seek to the first fact whose key is not below
`p` (a binary search in the file), then read while the facts start with
`p`. -/
def seekRun (order p : List ℕ) (l : List Fact) : List Fact :=
  (l.dropWhile (fun f => lexLT (key order f) p)).takeWhile (bound order p)

theorem seekRun_eq_run (order p : List ℕ) :
    ∀ l : List Fact, l.Pairwise (fun f g => lexLE (key order f) (key order g) = true) →
      seekRun order p l = (l.dropWhile (fun f => !bound order p f)).takeWhile (bound order p) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons y ys ih =>
    intro hs
    by_cases hlt : lexLT (key order y) p = true
    · -- below `p`: the seek passes it, and no key below `p` starts with `p`
      have hnb : bound order p y = false := by
        by_contra hb
        simp only [bound, Bool.not_eq_false, decide_eq_true_eq] at hb
        have := lexLE_of_prefix p _ hb
        simp [lexLT, this] at hlt
      have hl : seekRun order p (y :: ys) = seekRun order p ys := by
        simp [seekRun, hlt]
      rw [hl, ih hs.of_cons]
      simp [hnb]
    · have hge : lexLE p (key order y) = true := by
        simpa [lexLT] using hlt
      have hl : seekRun order p (y :: ys) = (y :: ys).takeWhile (bound order p) := by
        simp [seekRun, hlt]
      rw [hl]
      by_cases hb : bound order p y = true
      · simp [hb]
      · -- past `p` without it: nothing later starts with `p`
        have hnone : ∀ z ∈ ys, bound order p z = false := by
          intro z hz
          by_contra hzb
          simp only [bound, Bool.not_eq_false, decide_eq_true_eq] at hzb hb
          exact hb (prefix_between p p (key order y) (key order z) hge
            (List.rel_of_pairwise_cons hs hz) (List.prefix_refl p) hzb)
        have hdrop : ys.dropWhile (fun f => !bound order p f) = [] :=
          dropWhile_of_all _ ys (fun z hz => by simp [hnone z hz])
        simp [hb, hdrop]

/-- The cursor's read, on the index, answers exactly what a scan answers. -/
theorem seek_perm_scan (order p : List ℕ) (facts : List Fact) :
    (seekRun order p (index order facts)).Perm (scan order p facts) := by
  rw [seekRun_eq_run order p _ (index_sorted order facts)]
  exact lookup_perm_scan order p facts

end Mettapedia.Machines.SpaceFileRuns
