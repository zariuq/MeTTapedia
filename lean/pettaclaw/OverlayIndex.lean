/-!
# OverlayIndex — a transaction's own edits, read through an index

A transaction overlays its own edits on the stored rows: the rows it added (a
log; slot `i` holds the `i`-th addition) and the rows it removed. A cursor
opened in the transaction yields the stored rows not removed, then the added
rows in slot order, as they were when it opened. Reading every added row made
each read cost the number of edits so far, and a transaction of k edits cost
k². The overlay now keeps:

* for the added rows, per (length, position) of an expression: the slots whose
  element there has a given exact key (a symbol or a string), the slots whose
  element there has no key, and, once, the slots that hold a bare variable;
* removed added rows marked with the version of their removal, instead of
  erased from the log;
* removed stored rows in a hash set that keeps the first removal of each
  identity.

A pattern holding an internal tag anywhere (a list, a list pattern with a
rest, a braces node) is not narrowed: a list pattern with a rest meets lists of
other lengths. For every other pattern, matching is unification, which is what
this file uses. It proves the new representation changes only the cost:

* `candidate_of_unifies`: a row that unifies with a pattern whose element `p`
  has an exact key is a bare variable, or an expression of the pattern's length
  whose element `p` has no key or the same key. The three slot lists hold every
  row the pattern can match.
* `walk_spec`: the cursor's walk (take the least head of the three lists,
  advance every list it heads, stop at the snapshot's length, skip a row
  removed by the snapshot's version) yields, in slot order, exactly the visible
  slots of the three lists below the snapshot's length.
* `cursor_eq_scan`: so the rows the cursor yields that the pattern matches are
  the rows the scan yields that it matches, in the same order, whichever exact
  position is used (`any_position_same`).
* `open_cursor_unchanged`: read after any later additions and removals, a
  cursor yields what the scan yielded when it opened. The lists grow only at
  their ends, by slots at or past the cursor's length (`slots_append`), so the
  positions a cursor holds in them keep their slots.
* `tombstone_eq_scan`: the hash set's answer is the old scan of the removed
  stored rows the cursor had copied when it opened.
* `lazy_eq_eager`: the added rows reported at commit (the unremoved rows in
  slot order) are the rows the old array kept by erasing each removed row.
* `ground_rows_read_bucket`: when the added rows are ground expressions with a
  key at the position, a read visits only the rows with the pattern's key
  there; its work does not grow with the transaction's other edits.
-/

namespace OverlayIndex

/-! ## Atoms, keys and unification -/

inductive Atom where
  | var (n : Nat)
  | sym (s : String)
  | str (s : String)
  | val (n : Nat)
  | expr (es : List Atom)

/-- The exact key of an element: symbols and strings, kept apart. Numbers,
other grounded values, variables and expressions have none. -/
def key : Atom → Option (Bool × String)
  | .sym s => some (false, s)
  | .str s => some (true, s)
  | _ => none

def subst (σ : Nat → Atom) : Atom → Atom
  | .var n => σ n
  | .sym s => .sym s
  | .str s => .str s
  | .val n => .val n
  | .expr es => .expr (es.map (subst σ))

/-- A row can meet a pattern when one substitution makes them equal. A sound matcher answers
"matched" only then (a row's variables renamed apart are part of the substitution). -/
def Unifies (pat row : Atom) : Prop := ∃ σ, subst σ pat = subst σ row

def keyAt (es : List Atom) (p : Nat) : Option (Bool × String) := (es[p]?).bind key

/-- The slot lists a row of the log belongs to, for length `n` and position `p`. -/
def isExact (n p : Nat) (k : Bool × String) : Atom → Bool
  | .expr es => decide (es.length = n) && decide (keyAt es p = some k)
  | _ => false

def isAny (n p : Nat) : Atom → Bool
  | .expr es => decide (es.length = n) && decide (keyAt es p = none)
  | _ => false

def isVar : Atom → Bool
  | .var _ => true
  | _ => false

def candidate (n p : Nat) (k : Bool × String) (a : Atom) : Bool :=
  isExact n p k a || isAny n p a || isVar a

theorem subst_keyed {a : Atom} {k} (σ : Nat → Atom) (h : key a = some k) : subst σ a = a := by
  cases a <;> simp [key, subst] at h ⊢

theorem keyed_preimage {a b : Atom} {k} (σ : Nat → Atom) (h : key a = some k)
    (e : subst σ b = a) : key b = none ∨ key b = some k := by
  cases b with
  | var n => exact Or.inl rfl
  | sym s => simp only [subst] at e; subst e; exact Or.inr h
  | str s => simp only [subst] at e; subst e; exact Or.inr h
  | val n => simp only [subst] at e; subst e; simp [key] at h
  | expr es => simp only [subst] at e; subst e; simp [key] at h

theorem candidate_of_unifies {ps : List Atom} {p : Nat} {k} (hp : p < ps.length)
    (hk : keyAt ps p = some k) {row : Atom} (h : Unifies (.expr ps) row) :
    candidate ps.length p k row = true := by
  obtain ⟨σ, hσ⟩ := h
  cases row with
  | var n => simp [candidate, isVar]
  | sym s => simp [subst] at hσ
  | str s => simp [subst] at hσ
  | val n => simp [subst] at hσ
  | expr es =>
    simp only [subst, Atom.expr.injEq] at hσ
    have hlen : ps.length = es.length := by simpa using congrArg List.length hσ
    have hpe : p < es.length := hlen ▸ hp
    have hget : subst σ ps[p] = subst σ es[p] := by
      have := congrArg (fun l => l[p]?) hσ
      simpa [List.getElem?_eq_getElem hp, List.getElem?_eq_getElem hpe] using this
    have hk' : key ps[p] = some k := by simpa [keyAt, List.getElem?_eq_getElem hp] using hk
    rw [subst_keyed σ hk'] at hget
    rcases keyed_preimage σ hk' hget.symm with h0 | h1
    · simp [candidate, isAny, keyAt, List.getElem?_eq_getElem hpe, h0, hlen]
    · simp [candidate, isExact, keyAt, List.getElem?_eq_getElem hpe, h1, hlen]

/-! ## Slot lists -/

/-- The slots of the log whose row satisfies `q`, in slot order. -/
def slots (q : Atom → Bool) (rows : List Atom) : List Nat :=
  (List.range rows.length).filter (fun i => (rows[i]?).any q)

theorem mem_slots {q : Atom → Bool} {rows : List Atom} {i : Nat} :
    i ∈ slots q rows ↔ ∃ h : i < rows.length, q rows[i] = true := by
  simp only [slots, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hi, hq⟩; exact ⟨hi, by simpa [List.getElem?_eq_getElem hi] using hq⟩
  · rintro ⟨hi, hq⟩; exact ⟨hi, by simpa [List.getElem?_eq_getElem hi] using hq⟩

theorem range_sorted : ∀ n : Nat, (List.range n).Pairwise (· < ·)
  | 0 => List.Pairwise.nil
  | n + 1 => by
    rw [List.range_succ, List.pairwise_append]
    refine ⟨range_sorted n, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb; subst hb; exact List.mem_range.mp ha

theorem slots_sorted (q : Atom → Bool) (rows : List Atom) : (slots q rows).Pairwise (· < ·) :=
  (range_sorted _).filter _

/-- Adding a row pushes its slot onto every list it belongs to. -/
theorem slots_push (q : Atom → Bool) (rows : List Atom) (a : Atom) :
    slots q (rows ++ [a]) = slots q rows ++ (if q a then [rows.length] else []) := by
  simp only [slots, List.length_append, List.length_singleton, List.range_succ, List.filter_append]
  congr 1
  · apply List.filter_congr
    intro i hi
    rw [List.getElem?_append_left (List.mem_range.mp hi)]
  · by_cases hq : q a <;> simp [hq]

/-! ## Two sorted lists with the same members are equal -/

theorem eq_of_sorted_mem : ∀ {l₁ l₂ : List Nat}, l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) →
    (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], y :: _, _, _, h => absurd ((h y).mpr (List.mem_cons_self ..)) (List.not_mem_nil)
  | x :: _, [], _, _, h => absurd ((h x).mp (List.mem_cons_self ..)) (List.not_mem_nil)
  | x :: xs, y :: ys, s₁, s₂, h => by
    rw [List.pairwise_cons] at s₁ s₂
    have hxy : x = y := by
      have hx := (h x).mp (List.mem_cons_self ..)
      have hy := (h y).mpr (List.mem_cons_self ..)
      rcases List.mem_cons.mp hx with e | hx
      · exact e
      rcases List.mem_cons.mp hy with e | hy
      · exact e.symm
      have := s₂.1 x hx; have := s₁.1 y hy; omega
    subst hxy
    have : xs = ys := eq_of_sorted_mem s₁.2 s₂.2 (fun z => by
      constructor
      · intro hz
        have hz' := (h z).mp (List.mem_cons_of_mem _ hz)
        rcases List.mem_cons.mp hz' with e | e
        · have := s₁.1 z hz; omega
        · exact e
      · intro hz
        have hz' := (h z).mpr (List.mem_cons_of_mem _ hz)
        rcases List.mem_cons.mp hz' with e | e
        · have := s₂.1 z hz; omega
        · exact e)
    rw [this]

/-- A failed admission rolls the lists back to the slots below the old length. -/
theorem slots_take (q : Atom → Bool) (rows : List Atom) (m : Nat) (hm : m ≤ rows.length) :
    slots q (rows.take m) = (slots q rows).filter (fun i => decide (i < m)) := by
  simp only [slots, List.filter_filter, List.length_take, Nat.min_eq_left hm]
  apply eq_of_sorted_mem ((range_sorted _).filter _) ((range_sorted _).filter _)
  intro i
  simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hi, hq⟩
    refine ⟨Nat.lt_of_lt_of_le hi hm, hi, ?_⟩
    rwa [List.getElem?_take_of_lt hi] at hq
  · rintro ⟨_, hi, hq⟩
    exact ⟨hi, by rwa [List.getElem?_take_of_lt hi]⟩

/-! ## The cursor's walk over the three lists -/

def minOpt : Option Nat → Option Nat → Option Nat
  | none, b => b
  | a, none => a
  | some x, some y => some (if x ≤ y then x else y)

/-- Advance a list past slot `s` when `s` is its head. -/
def adv (s : Nat) : List Nat → List Nat
  | x :: xs => if x = s then xs else x :: xs
  | [] => []

/-- Take the least head of the three lists, advance every list it heads; stop once it reaches the
snapshot's length `lim`; yield it when the row is visible (`vis`: not removed by the snapshot's
version). -/
def walk (lim : Nat) (vis : Nat → Bool) : Nat → List Nat → List Nat → List Nat → List Nat
  | 0, _, _, _ => []
  | fuel + 1, e, a, v =>
    match minOpt (minOpt e.head? a.head?) v.head? with
    | none => []
    | some s =>
      if lim ≤ s then [] else
        if vis s then s :: walk lim vis fuel (adv s e) (adv s a) (adv s v)
        else walk lim vis fuel (adv s e) (adv s a) (adv s v)

/-- Every member of a sorted list is at least its head. -/
theorem head_le {l : List Nat} (hs : l.Pairwise (· < ·)) {h x : Nat} (hh : l.head? = some h)
    (hx : x ∈ l) : h ≤ x := by
  cases l with
  | nil => simp at hh
  | cons y ys =>
    simp at hh; subst hh
    rcases List.mem_cons.mp hx with e | hx
    · omega
    · exact Nat.le_of_lt ((List.pairwise_cons.mp hs).1 x hx)

theorem adv_sorted (s : Nat) {l : List Nat} (hs : l.Pairwise (· < ·)) : (adv s l).Pairwise (· < ·) := by
  cases l with
  | nil => exact List.Pairwise.nil
  | cons y ys => simp only [adv]; split
                 · exact (List.pairwise_cons.mp hs).2
                 · exact hs

theorem adv_length_le (s : Nat) (l : List Nat) : (adv s l).length ≤ l.length := by
  cases l with
  | nil => simp [adv]
  | cons y ys => simp only [adv]; split <;> simp

theorem adv_length_lt {s : Nat} {l : List Nat} (h : l.head? = some s) :
    (adv s l).length < l.length := by
  cases l with
  | nil => simp at h
  | cons y ys => simp at h; subst h; simp [adv]

/-- When every member is at least `s`, advancing past `s` removes `s` and nothing else. -/
theorem mem_adv {s : Nat} {l : List Nat} (hs : l.Pairwise (· < ·)) (hge : ∀ y ∈ l, s ≤ y) (x : Nat) :
    x ∈ adv s l ↔ x ∈ l ∧ x ≠ s := by
  cases l with
  | nil => simp [adv]
  | cons y ys =>
    have hlt := (List.pairwise_cons.mp hs).1
    simp only [adv]
    split
    · rename_i e; subst e
      constructor
      · intro hx; exact ⟨List.mem_cons_of_mem _ hx, by have := hlt x hx; omega⟩
      · rintro ⟨hx, hne⟩
        rcases List.mem_cons.mp hx with e | hx
        · exact absurd e hne
        · exact hx
    · rename_i e
      constructor
      · intro hx
        refine ⟨hx, fun hxs => ?_⟩
        subst hxs
        have hy := hge y (List.mem_cons_self ..)
        rcases List.mem_cons.mp hx with e' | hx
        · exact e e'.symm
        · have := hlt _ hx; omega
      · exact fun h => h.1


theorem minOpt_none {a b : Option Nat} : minOpt a b = none ↔ a = none ∧ b = none := by
  cases a <;> cases b <;> simp [minOpt]

theorem minOpt_some {a b : Option Nat} {s : Nat} (h : minOpt a b = some s) :
    (a = some s ∨ b = some s) ∧ (∀ x, a = some x → s ≤ x) ∧ (∀ x, b = some x → s ≤ x) := by
  have none_le : ∀ x : Nat, (none : Option Nat) = some x → s ≤ x := fun x hx => by cases hx
  have self_le : ∀ x : Nat, some s = some x → s ≤ x := fun x hx => by cases hx; exact Nat.le_refl _
  cases a with
  | none => cases b with
    | none => cases h
    | some y => cases h; exact ⟨Or.inr rfl, none_le, self_le⟩
  | some x => cases b with
    | none => cases h; exact ⟨Or.inl rfl, self_le, none_le⟩
    | some y =>
      simp only [minOpt] at h
      split at h
      · cases h; exact ⟨Or.inl rfl, self_le, fun z hz => by cases hz; assumption⟩
      · cases h; exact ⟨Or.inr rfl, fun z hz => by cases hz; omega, self_le⟩

theorem minOpt_left {a b : Option Nat} {y : Nat} (h : a = some y) : ∃ z, minOpt a b = some z ∧ z ≤ y := by
  subst h
  cases b with
  | none => exact ⟨y, rfl, Nat.le_refl _⟩
  | some x => simp only [minOpt]; split
              · exact ⟨y, rfl, Nat.le_refl _⟩
              · exact ⟨x, rfl, by omega⟩

theorem minOpt_right {a b : Option Nat} {y : Nat} (h : b = some y) : ∃ z, minOpt a b = some z ∧ z ≤ y := by
  subst h
  cases a with
  | none => exact ⟨y, rfl, Nat.le_refl _⟩
  | some x => simp only [minOpt]; split
              · exact ⟨x, rfl, by omega⟩
              · exact ⟨y, rfl, Nat.le_refl _⟩

theorem head?_none {l : List Nat} : l.head? = none ↔ l = [] := by cases l <;> simp

theorem mem_of_head {l : List Nat} {s : Nat} (h : l.head? = some s) : s ∈ l := by
  cases l with
  | nil => simp at h
  | cons y ys => simp at h; subst h; exact List.mem_cons_self ..

/-- The least head heads one of the lists and is at most every member of all three. -/
theorem min3_spec {e a v : List Nat} {s : Nat} (se : e.Pairwise (· < ·)) (sa : a.Pairwise (· < ·))
    (sv : v.Pairwise (· < ·)) (h : minOpt (minOpt e.head? a.head?) v.head? = some s) :
    (e.head? = some s ∨ a.head? = some s ∨ v.head? = some s) ∧
      ∀ x, (x ∈ e ∨ x ∈ a ∨ x ∈ v) → s ≤ x := by
  obtain ⟨hin, h1, hv⟩ := minOpt_some h
  refine ⟨?_, ?_⟩
  · rcases hin with h' | h'
    · rcases (minOpt_some h').1 with h'' | h''
      · exact Or.inl h''
      · exact Or.inr (Or.inl h'')
    · exact Or.inr (Or.inr h')
  · have below : ∀ l : List Nat, l.Pairwise (· < ·) → (∀ y, l.head? = some y → s ≤ y) →
        ∀ x ∈ l, s ≤ x := fun l hl hy x hx => by
      cases hh : l.head? with
      | none => rw [head?_none] at hh; subst hh; simp at hx
      | some y => exact Nat.le_trans (hy y hh) (head_le hl hh hx)
    rintro x (hx | hx | hx)
    · refine below e se (fun y hy => ?_) x hx
      obtain ⟨z, hz, hzy⟩ := minOpt_left (b := a.head?) hy
      have := h1 z hz; omega
    · refine below a sa (fun y hy => ?_) x hx
      obtain ⟨z, hz, hzy⟩ := minOpt_right (a := e.head?) hy
      have := h1 z hz; omega
    · exact below v sv hv x hx

/-- The walk yields, in slot order, exactly the visible slots of the three lists below `lim`. -/
theorem walk_spec (lim : Nat) (vis : Nat → Bool) : ∀ (fuel : Nat) (e a v : List Nat),
    e.Pairwise (· < ·) → a.Pairwise (· < ·) → v.Pairwise (· < ·) →
    e.length + a.length + v.length ≤ fuel →
    (walk lim vis fuel e a v).Pairwise (· < ·) ∧
      ∀ x, x ∈ walk lim vis fuel e a v ↔ x < lim ∧ vis x = true ∧ (x ∈ e ∨ x ∈ a ∨ x ∈ v) := by
  intro fuel
  induction fuel with
  | zero =>
    intro e a v _ _ _ hf
    have he : e = [] := List.eq_nil_of_length_eq_zero (by omega)
    have ha : a = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hv : v = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst he ha hv
    simp [walk]
  | succ fuel ih =>
    intro e a v se sa sv hf
    cases hm : minOpt (minOpt e.head? a.head?) v.head? with
    | none =>
      obtain ⟨hea, hv⟩ := minOpt_none.mp hm
      obtain ⟨he, ha⟩ := minOpt_none.mp hea
      rw [head?_none] at he ha hv; subst he ha hv
      simp [walk, minOpt]
    | some s =>
      obtain ⟨hhead, hmin⟩ := min3_spec se sa sv hm
      have me := mem_adv se (fun y hy => hmin y (Or.inl hy))
      have ma := mem_adv sa (fun y hy => hmin y (Or.inr (Or.inl hy)))
      have mv := mem_adv sv (fun y hy => hmin y (Or.inr (Or.inr hy)))
      have hf' : (adv s e).length + (adv s a).length + (adv s v).length ≤ fuel := by
        have := adv_length_le s e; have := adv_length_le s a; have := adv_length_le s v
        rcases hhead with h | h | h <;> (have := adv_length_lt h; omega)
      obtain ⟨ihs, ihm⟩ := ih _ _ _ (adv_sorted s se) (adv_sorted s sa) (adv_sorted s sv) hf'
      have hsU : s ∈ e ∨ s ∈ a ∨ s ∈ v := by
        rcases hhead with h | h | h
        · exact Or.inl (mem_of_head h)
        · exact Or.inr (Or.inl (mem_of_head h))
        · exact Or.inr (Or.inr (mem_of_head h))
      have rest : ∀ x, x ∈ walk lim vis fuel (adv s e) (adv s a) (adv s v) ↔
          x < lim ∧ vis x = true ∧ (x ∈ e ∨ x ∈ a ∨ x ∈ v) ∧ x ≠ s := by
        intro x
        rw [ihm x, me x, ma x, mv x]
        constructor
        · rintro ⟨h1, h2, ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩⟩
          · exact ⟨h1, h2, Or.inl h3, h4⟩
          · exact ⟨h1, h2, Or.inr (Or.inl h3), h4⟩
          · exact ⟨h1, h2, Or.inr (Or.inr h3), h4⟩
        · rintro ⟨h1, h2, h3 | h3 | h3, h4⟩
          · exact ⟨h1, h2, Or.inl ⟨h3, h4⟩⟩
          · exact ⟨h1, h2, Or.inr (Or.inl ⟨h3, h4⟩)⟩
          · exact ⟨h1, h2, Or.inr (Or.inr ⟨h3, h4⟩)⟩
      simp only [walk, hm]
      by_cases hl : lim ≤ s
      · rw [if_pos hl]
        refine ⟨List.Pairwise.nil, fun x => ?_⟩
        simp only [List.not_mem_nil, false_iff]
        rintro ⟨hx, _, hU⟩
        have := hmin x hU; omega
      · rw [if_neg hl]
        by_cases hvis : vis s = true
        · rw [if_pos hvis]
          refine ⟨List.pairwise_cons.mpr ⟨fun y hy => ?_, ihs⟩, fun x => ?_⟩
          · obtain ⟨_, _, hU, hne⟩ := (rest y).mp hy
            have := hmin y hU; omega
          · rw [List.mem_cons, rest x]
            constructor
            · rintro (h | ⟨h1, h2, h3, _⟩)
              · subst h; exact ⟨by omega, hvis, hsU⟩
              · exact ⟨h1, h2, h3⟩
            · rintro ⟨h1, h2, h3⟩
              by_cases hx : x = s
              · exact Or.inl hx
              · exact Or.inr ⟨h1, h2, h3, hx⟩
        · rw [if_neg hvis]
          refine ⟨ihs, fun x => ?_⟩
          rw [rest x]
          constructor
          · rintro ⟨h1, h2, h3, _⟩; exact ⟨h1, h2, h3⟩
          · rintro ⟨h1, h2, h3⟩
            refine ⟨h1, h2, h3, fun hx => ?_⟩
            subst hx; exact hvis h2

/-! ## The cursor reads what the scan reads -/

/-- The cursor over the log `rows`, for a pattern of length `n` whose element `p` has key `k`,
in a snapshot of length `lim`: the walk over the exact, keyless and variable lists. -/
def cursor (n p : Nat) (k : Bool × String) (rows : List Atom) (lim : Nat) (vis : Nat → Bool) :
    List Nat :=
  walk lim vis ((slots (isExact n p k) rows).length + (slots (isAny n p) rows).length +
      (slots isVar rows).length)
    (slots (isExact n p k) rows) (slots (isAny n p) rows) (slots isVar rows)

def matchesAt (m : Atom → Bool) (rows : List Atom) (i : Nat) : Bool := (rows[i]?).any m

/-- The scan: every visible slot below `lim` whose row the matcher accepts, in slot order. -/
def scan (rows : List Atom) (lim : Nat) (vis : Nat → Bool) (m : Atom → Bool) : List Nat :=
  (List.range lim).filter (fun i => vis i && matchesAt m rows i)

/-- Filtered by the matcher, the cursor yields the scan's rows in the scan's order. `sound`: the
matcher accepts only rows that unify with the pattern. -/
theorem cursor_eq_scan {ps : List Atom} {p : Nat} {k} (hp : p < ps.length)
    (hk : keyAt ps p = some k) (m : Atom → Bool) (sound : ∀ a, m a = true → Unifies (.expr ps) a)
    (rows : List Atom) (lim : Nat) (hlim : lim ≤ rows.length) (vis : Nat → Bool) :
    (cursor ps.length p k rows lim vis).filter (matchesAt m rows) = scan rows lim vis m := by
  obtain ⟨srt, mem⟩ := walk_spec lim vis _ _ _ _ (slots_sorted _ rows) (slots_sorted _ rows)
    (slots_sorted _ rows) (Nat.le_refl _)
  apply eq_of_sorted_mem (srt.filter _) ((range_sorted _).filter _)
  intro x
  simp only [List.mem_filter, List.mem_range, Bool.and_eq_true]
  rw [mem x]
  constructor
  · rintro ⟨⟨h1, h2, _⟩, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2, ?_⟩, h3⟩
    have hx : x < rows.length := Nat.lt_of_lt_of_le h1 hlim
    have hm : m rows[x] = true := by simpa [matchesAt, List.getElem?_eq_getElem hx] using h3
    have hc := candidate_of_unifies hp hk (sound _ hm)
    simp only [candidate, Bool.or_eq_true] at hc
    rcases hc with (hc | hc) | hc
    · exact Or.inl (mem_slots.mpr ⟨hx, hc⟩)
    · exact Or.inr (Or.inl (mem_slots.mpr ⟨hx, hc⟩))
    · exact Or.inr (Or.inr (mem_slots.mpr ⟨hx, hc⟩))

/-- The planner may read any exact position of the pattern: the results are the same. -/
theorem any_position_same {ps : List Atom} {p q : Nat} {k k'} (hp : p < ps.length)
    (hk : keyAt ps p = some k) (hq : q < ps.length) (hk' : keyAt ps q = some k')
    (m : Atom → Bool) (sound : ∀ a, m a = true → Unifies (.expr ps) a)
    (rows : List Atom) (lim : Nat) (hlim : lim ≤ rows.length) (vis : Nat → Bool) :
    (cursor ps.length p k rows lim vis).filter (matchesAt m rows) =
      (cursor ps.length q k' rows lim vis).filter (matchesAt m rows) := by
  rw [cursor_eq_scan hp hk m sound rows lim hlim vis, cursor_eq_scan hq hk' m sound rows lim hlim vis]

/-- The slot lists grow only at their ends, by slots at or past the old length: a cursor's
indexes into them keep pointing at the same slots. -/
theorem slots_append (q : Atom → Bool) : ∀ (ext rows : List Atom),
    ∃ tail, slots q (rows ++ ext) = slots q rows ++ tail ∧ ∀ x ∈ tail, rows.length ≤ x
  | [], rows => ⟨[], by simp, by simp⟩
  | b :: ext, rows => by
    obtain ⟨tail, ht, hge⟩ := slots_append q ext (rows ++ [b])
    refine ⟨(if q b then [rows.length] else []) ++ tail, ?_, ?_⟩
    · rw [show rows ++ b :: ext = (rows ++ [b]) ++ ext by simp, ht, slots_push, List.append_assoc]
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · by_cases hb : q b <;> simp [hb] at hx; omega
      · have := hge x hx; simp at this; omega

/-! ## An open cursor does not see later edits -/

/-- Slot `i` is visible to a snapshot of version `ver` unless it was removed at or before it
(`removed_at > c->version`; `none` stands for the live mark). -/
def visAt (ver : Nat) (removedAt : Nat → Option Nat) (i : Nat) : Bool :=
  match removedAt i with
  | none => true
  | some w => decide (ver < w)

structure Log where
  rows : List Atom
  removedAt : Nat → Option Nat
  version : Nat

/-- The overlay's edits, as far as its added rows go. Each advances the version and stamps what
it changes with the new version. -/
inductive Edit : Log → Log → Prop
  /-- An admission appends a row. -/
  | add (L : Log) (a : Atom) : Edit L ⟨L.rows ++ [a], L.removedAt, L.version + 1⟩
  /-- A removal marks the selected added rows that are still live. -/
  | remove (L : Log) (sel : Nat → Bool) :
      Edit L ⟨L.rows, fun j => if (sel j && (L.removedAt j).isNone) = true then
        some (L.version + 1) else L.removedAt j, L.version + 1⟩
  /-- Removing a stored row leaves the added rows alone. -/
  | stone (L : Log) : Edit L ⟨L.rows, L.removedAt, L.version + 1⟩

inductive Steps : Log → Log → Prop
  | refl (L : Log) : Steps L L
  | step {L₁ L₂ L₃ : Log} : Edit L₁ L₂ → Steps L₂ L₃ → Steps L₁ L₃

theorem edit_keeps (ver : Nat) {L L' : Log} (h : Edit L L') (hv : ver ≤ L.version) :
    ver ≤ L'.version ∧ (∃ ext, L'.rows = L.rows ++ ext) ∧
      ∀ i, visAt ver L'.removedAt i = visAt ver L.removedAt i := by
  cases h with
  | add a => exact ⟨by simp; omega, ⟨[a], rfl⟩, fun _ => rfl⟩
  | remove sel =>
    refine ⟨by simp; omega, ⟨[], by simp⟩, fun i => ?_⟩
    simp only [visAt]
    by_cases hs : (sel i && (L.removedAt i).isNone) = true
    · rw [if_pos hs]
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hs
      rw [hs.2]; simp; omega
    · rw [if_neg hs]
  | stone => exact ⟨by simp; omega, ⟨[], by simp⟩, fun _ => rfl⟩

theorem steps_keep (ver : Nat) {L L' : Log} (h : Steps L L') (hv : ver ≤ L.version) :
    (∃ ext, L'.rows = L.rows ++ ext) ∧ ∀ i, visAt ver L'.removedAt i = visAt ver L.removedAt i := by
  induction h with
  | refl => exact ⟨⟨[], by simp⟩, fun _ => rfl⟩
  | step he _ ih =>
    obtain ⟨hv', ⟨ext1, hr1⟩, hvis1⟩ := edit_keeps ver he hv
    obtain ⟨⟨ext2, hr2⟩, hvis2⟩ := ih hv'
    exact ⟨⟨ext1 ++ ext2, by rw [hr2, hr1, List.append_assoc]⟩, fun i => by rw [hvis2, hvis1]⟩

/-- A cursor opened on `L` (its length and version), read after any later edits, yields what
the scan of `L` yielded. -/
theorem open_cursor_unchanged {ps : List Atom} {p : Nat} {k} (hp : p < ps.length)
    (hk : keyAt ps p = some k) (m : Atom → Bool) (sound : ∀ a, m a = true → Unifies (.expr ps) a)
    {L L' : Log} (h : Steps L L') :
    (cursor ps.length p k L'.rows L.rows.length (visAt L.version L'.removedAt)).filter
        (matchesAt m L'.rows) =
      scan L.rows L.rows.length (visAt L.version L.removedAt) m := by
  obtain ⟨⟨ext, hr⟩, hvis⟩ := steps_keep L.version h (Nat.le_refl _)
  rw [cursor_eq_scan hp hk m sound L'.rows L.rows.length (by rw [hr]; simp) _]
  unfold scan
  apply List.filter_congr
  intro i hi
  have hi' := List.mem_range.mp hi
  rw [hvis i]
  simp only [matchesAt, hr, List.getElem?_append_left hi']

/-! ## Removed stored rows: a hash set instead of a scan -/

section Tombstones
variable {α : Type} [DecidableEq α]

/-- Insertion keeps the first removal of an identity: it returns when it finds an equal one. -/
def insertFirst (f : α → Option Nat) (x : α × Nat) : α → Option Nat :=
  fun y => match f y with
    | some w => some w
    | none => if y = x.1 then some x.2 else none

/-- The set after inserting the removal log in order. -/
def stones (log : List (α × Nat)) : α → Option Nat := log.foldl insertFirst (fun _ => none)

/-- A cursor of version `ver` skips a stored row whose identity the set holds with a version at
or before `ver`. -/
def hidden (f : α → Option Nat) (ver : Nat) (y : α) : Bool :=
  match f y with
  | some w => decide (w ≤ ver)
  | none => false

theorem foldl_insertFirst (y : α) : ∀ (r : List (α × Nat)) (f : α → Option Nat),
    r.foldl insertFirst f y = match f y with | some w => some w | none => stones r y
  | [], f => by cases h : f y <;> simp [stones, h]
  | x :: r, f => by
    simp only [List.foldl_cons]
    rw [foldl_insertFirst y r (insertFirst f x)]
    have e2 : stones (x :: r) y = match insertFirst (fun _ => none) x y with
        | some w => some w | none => stones r y := by
      simp only [stones, List.foldl_cons]; exact foldl_insertFirst y r _
    rw [e2]
    cases h : f y <;> simp [insertFirst, h]

theorem stones_cons (x : α × Nat) (r : List (α × Nat)) (y : α) :
    stones (x :: r) y = if y = x.1 then some x.2 else stones r y := by
  simp only [stones, List.foldl_cons]
  rw [foldl_insertFirst y r]
  by_cases h : y = x.1 <;> simp [insertFirst, h, stones]

theorem stones_some : ∀ {l : List (α × Nat)} {y : α} {w : Nat}, stones l y = some w → (y, w) ∈ l
  | [], _, _, h => by simp [stones] at h
  | x :: r, y, w, h => by
    rw [stones_cons] at h
    split at h
    · rename_i e; cases h; subst e; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (stones_some h)

theorem stones_none : ∀ {l : List (α × Nat)} {y : α}, stones l y = none → ∀ x ∈ l, x.1 ≠ y
  | [], _, _, x, hx => by simp at hx
  | x :: r, y, h, z, hz => by
    rw [stones_cons] at h
    split at h
    · cases h
    · rename_i e
      rcases List.mem_cons.mp hz with hz | hz
      · subst hz; exact fun h' => e h'.symm
      · exact stones_none h z hz

theorem stones_append (l r : List (α × Nat)) (y : α) :
    stones (l ++ r) y = match stones l y with | some w => some w | none => stones r y := by
  simp only [stones, List.foldl_append]
  exact foldl_insertFirst y r _

/-- The removal log at a cursor's opening (`old`, every version at or before the cursor's) and
the removals after it (`later`, each with a later version): the set's answer for the log so far
is the old scan of the rows the cursor had copied. -/
theorem tombstone_eq_scan (old later : List (α × Nat)) (ver : Nat)
    (hold : ∀ x ∈ old, x.2 ≤ ver) (hlater : ∀ x ∈ later, ver < x.2) (y : α) :
    hidden (stones (old ++ later)) ver y = old.any (fun x => decide (x.1 = y)) := by
  simp only [hidden, stones_append]
  cases h : stones old y with
  | some w =>
    have hm := stones_some h
    have := hold _ hm
    simp only [this, decide_true]
    exact (List.any_eq_true.mpr ⟨_, hm, by simp⟩).symm
  | none =>
    have hn := stones_none h
    have hf : old.any (fun x => decide (x.1 = y)) = false :=
      List.any_eq_false.mpr (fun x hx => by simpa using hn x hx)
    rw [hf]
    cases h' : stones later y with
    | none => rfl
    | some w =>
      have := hlater _ (stones_some h')
      simp only [decide_eq_false_iff_not]; omega

end Tombstones

/-! ## Commit: the live rows in slot order are the rows erasure kept -/

inductive Op where
  | add
  | remove (i : Nat)

/-- The old array: append the new slot; erase a removed slot where it stands (slots are unique,
so erasing the one occurrence is filtering it out). State: the array and the next slot. -/
def eagerStep : List Nat × Nat → Op → List Nat × Nat
  | (arr, n), .add => (arr ++ [n], n + 1)
  | (arr, n), .remove i => (arr.filter (fun j => decide (j ≠ i)), n)

/-- The new log: a removal marks an existing slot. State: the marks and the next slot. -/
def lazyStep : (Nat → Bool) × Nat → Op → (Nat → Bool) × Nat
  | (rem, n), .add => (rem, n + 1)
  | (rem, n), .remove i => (fun j => rem j || (decide (j = i) && decide (i < n)), n)

/-- What commit reports from the log: the unremoved slots in slot order. -/
def committed (st : (Nat → Bool) × Nat) : List Nat := (List.range st.2).filter (fun j => !st.1 j)

theorem lazy_eq_eager_from : ∀ (ops : List Op) (arr : List Nat) (rem : Nat → Bool) (n : Nat),
    arr = committed (rem, n) → (∀ j, n ≤ j → rem j = false) →
    (ops.foldl eagerStep (arr, n)).1 = committed (ops.foldl lazyStep (rem, n)) ∧
      (ops.foldl eagerStep (arr, n)).2 = (ops.foldl lazyStep (rem, n)).2
  | [], arr, rem, n, h, _ => ⟨h, rfl⟩
  | .add :: ops, arr, rem, n, h, hfresh => by
    simp only [List.foldl_cons, eagerStep, lazyStep]
    apply lazy_eq_eager_from ops
    · rw [h]; simp [committed, List.range_succ, List.filter_append, hfresh n (Nat.le_refl _)]
    · intro j hj; exact hfresh j (by omega)
  | .remove i :: ops, arr, rem, n, h, hfresh => by
    simp only [List.foldl_cons, eagerStep, lazyStep]
    apply lazy_eq_eager_from ops
    · rw [h]
      simp only [committed, List.filter_filter]
      apply List.filter_congr
      intro j hj
      have hj' := List.mem_range.mp hj
      by_cases e : j = i
      · subst e; simp [hj']
      · simp [e]
    · intro j hj
      have hi : ¬ (j = i ∧ i < n) := fun ⟨e, hi⟩ => by omega
      simp only [Bool.or_eq_false_iff, hfresh j hj, true_and, Bool.and_eq_false_iff,
        decide_eq_false_iff_not]
      by_cases e : j = i
      · exact Or.inr (fun hi' => hi ⟨e, hi'⟩)
      · exact Or.inl e

/-- From an empty transaction, any sequence of additions and removals: the rows commit reports
are the rows the old array kept, in the same order. -/
theorem lazy_eq_eager (ops : List Op) :
    (ops.foldl eagerStep ([], 0)).1 = committed (ops.foldl lazyStep (fun _ => false, 0)) :=
  (lazy_eq_eager_from ops [] (fun _ => false) 0 (by simp [committed]) (fun _ _ => rfl)).1

/-! ## The cost: a read visits the pattern's bucket -/

theorem filter_nil_of {q : Nat → Bool} : ∀ {l : List Nat}, (∀ a ∈ l, q a = false) → l.filter q = []
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filter_cons, if_neg (by rw [h a (List.mem_cons_self ..)]; exact Bool.false_ne_true)]
    exact filter_nil_of (fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- When every added row is an expression of length `n` with a key at `p`, the keyless and
variable lists are empty: the walk takes at most as many steps as the bucket of the pattern's
key has rows, whatever else the transaction added. -/
theorem ground_rows_read_bucket (n p : Nat) (k : Bool × String) (rows : List Atom)
    (h : ∀ a ∈ rows, ∃ es, a = .expr es ∧ es.length = n ∧ (keyAt es p).isSome) :
    (slots (isExact n p k) rows).length + (slots (isAny n p) rows).length +
      (slots isVar rows).length = (slots (isExact n p k) rows).length := by
  have hany : slots (isAny n p) rows = [] := by
    apply filter_nil_of
    intro i hi
    have hi' := List.mem_range.mp hi
    obtain ⟨es, he, hl, hs⟩ := h _ (List.getElem_mem hi')
    simp only [List.getElem?_eq_getElem hi', Option.any_some, he, isAny]
    cases hk : keyAt es p with
    | none => simp [hk] at hs
    | some _ => simp
  have hvar : slots isVar rows = [] := by
    apply filter_nil_of
    intro i hi
    have hi' := List.mem_range.mp hi
    obtain ⟨es, he, _, _⟩ := h _ (List.getElem_mem hi')
    simp [List.getElem?_eq_getElem hi', he, isVar]
  rw [hany, hvar]; rfl

end OverlayIndex

#print axioms OverlayIndex.candidate_of_unifies
#print axioms OverlayIndex.walk_spec
#print axioms OverlayIndex.cursor_eq_scan
#print axioms OverlayIndex.any_position_same
#print axioms OverlayIndex.open_cursor_unchanged
#print axioms OverlayIndex.tombstone_eq_scan
#print axioms OverlayIndex.lazy_eq_eager
#print axioms OverlayIndex.ground_rows_read_bucket
