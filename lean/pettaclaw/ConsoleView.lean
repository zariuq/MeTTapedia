/-!
# ConsoleView — what the operator console promises about copying and its status row

The terminal console prints an agent's commands into tmux scrollback and keeps
a one-line status row under the editor. This file states the promises an
operator relies on and proves them for a model of the renderer:

* **Copying a command is exact.** A command is printed one line per source line
  at column 0, so the copied lines join back to the command (`copy_exact`). An
  indented rendering breaks this: a copied here-document's terminator no longer
  ends it (`indented_heredoc_never_ends`).
* **The status row degrades predictably.** Every field has an importance
  (0 is essential). The fields that may be dropped are dropped in one fixed
  order, least important first and the later one on a tie, which does not
  depend on the width. The row drops the shortest prefix of that order that
  makes it fit. Then:
  - essential fields are never dropped (`fit_keeps_essentials`);
  - the kept fields keep their order (`fit_sublist`);
  - the row fits whenever something remained to drop (`fit_fits`);
  - a wider terminal never hides a field a narrower one showed (`fit_monotone`).

Widths are cell counts. The model does not cover terminal reflow or colour.
-/

namespace ConsoleView

/-! ## Copying commands -/

/-- A command as its source lines, printed with an indent before each. -/
def render (indent : String) (lines : List String) : List String :=
  lines.map (indent ++ ·)

/-- What tmux copy mode returns for the printed lines: the lines, joined. -/
def copied (printed : List String) : String := "\n".intercalate printed

/-- Printed at column 0, the copied text is the command. -/
theorem copy_exact (lines : List String) :
    copied (render "" lines) = "\n".intercalate lines := by
  simp [copied, render]

/-- A here-document ends at a line that is exactly its delimiter. -/
def heredocEnds (delimiter : String) (lines : List String) : Bool :=
  lines.any (· == delimiter)

def probe : List String := ["cat > probe.metta <<'EOF'", "!(println! ok)", "EOF"]

/-- The command ends its here-document; the same command copied from a
two-space-indented rendering does not, so pasting it leaves the shell waiting. -/
theorem indented_heredoc_never_ends :
    heredocEnds "EOF" probe = true ∧ heredocEnds "EOF" (render "  " probe) = false := by
  decide

/-! ## The status row -/

/-- A status field: a distinct identifier, its importance (0 = essential) and
its width in cells. -/
structure Field where
  id : Nat
  rank : Nat
  width : Nat
  deriving DecidableEq, Repr

def sep : Nat := 3   -- " · "

def rowWidth : List Field → Nat
  | [] => 0
  | [f] => f.width
  | f :: g :: fs => f.width + sep + rowWidth (g :: fs)

/-- The row without the fields whose identifiers are dropped. -/
def without (dropped : List Nat) (fs : List Field) : List Field :=
  fs.filter (fun f => !(dropped.contains f.id))

/-- The row after dropping the first `k` fields of the drop order. -/
def kept (order : List Nat) (k : Nat) (fs : List Field) : List Field :=
  without (order.take k) fs

/-- Stop at `k` once the row fits or nothing is left to drop. -/
def done (width : Nat) (order : List Nat) (fs : List Field) (k : Nat) : Bool :=
  decide (rowWidth (kept order k fs) ≤ width) || decide (order.length ≤ k)

def search (width : Nat) (order : List Nat) (fs : List Field) : Nat → Nat → Nat
  | 0, k => k
  | fuel + 1, k => if done width order fs k then k else search width order fs fuel (k + 1)

/-- How many fields of the drop order the row drops. -/
def dropCount (width : Nat) (order : List Nat) (fs : List Field) : Nat :=
  search width order fs order.length 0

def fitRow (width : Nat) (order : List Nat) (fs : List Field) : List Field :=
  kept order (dropCount width order fs) fs

/-! ### The search stops at the first `k` that is done -/

theorem search_done (width : Nat) (order : List Nat) (fs : List Field) :
    ∀ fuel k, order.length ≤ fuel + k → done width order fs (search width order fs fuel k) = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro k h
    have hk : order.length ≤ k := by simpa using h
    simp [search, done, hk]
  | succ n ih =>
    intro k h
    unfold search
    split
    · assumption
    · exact ih (k + 1) (by omega)

theorem search_least (width : Nat) (order : List Nat) (fs : List Field) :
    ∀ fuel k j, k ≤ j → j < search width order fs fuel k → done width order fs j = false := by
  intro fuel
  induction fuel with
  | zero => intro k j h1 h2; simp [search] at h2; omega
  | succ n ih =>
    intro k j h1 h2
    unfold search at h2
    split at h2
    · omega
    · rename_i hk
      rcases Nat.lt_or_ge j (k + 1) with hlt | hge
      · have : j = k := by omega
        subst this; simpa using hk
      · exact ih (k + 1) j hge h2

theorem dropCount_done (width : Nat) (order : List Nat) (fs : List Field) :
    done width order fs (dropCount width order fs) = true :=
  search_done width order fs order.length 0 (by omega)

/-! ### Kept fields keep their order, and essentials stay -/

theorem fit_sublist (width : Nat) (order : List Nat) (fs : List Field) :
    (fitRow width order fs).Sublist fs :=
  List.filter_sublist ..

/-- A field outside the drop order is never dropped; the drop order lists only
fields that may be dropped, so essential fields always remain. -/
theorem fit_keeps_essentials (width : Nat) (order : List Nat) (fs : List Field) (f : Field)
    (hf : f ∈ fs) (hout : f.id ∉ order) : f ∈ fitRow width order fs := by
  unfold fitRow kept without
  apply List.mem_filter.mpr
  refine ⟨hf, ?_⟩
  have : f.id ∉ order.take (dropCount width order fs) := fun h => hout (List.mem_of_mem_take h)
  simpa using this

/-! ### The row fits whenever something remained to drop -/

theorem fit_fits (width : Nat) (order : List Nat) (fs : List Field)
    (hleft : dropCount width order fs < order.length) :
    rowWidth (fitRow width order fs) ≤ width := by
  have h := dropCount_done width order fs
  simp only [done, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact h
  · omega

/-! ### A wider terminal shows at least as much -/

theorem filter_sublist_of_imp {α} (l : List α) (p q : α → Bool) (h : ∀ x, p x = true → q x = true) :
    (l.filter p).Sublist (l.filter q) := by
  induction l with
  | nil => exact List.Sublist.refl _
  | cons x xs ih =>
    simp only [List.filter_cons]
    by_cases hp : p x = true
    · simpa [hp, h x hp] using ih
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      by_cases hq : q x = true
      · simp [hq]; exact ih.cons x
      · simp [hq]; exact ih

/-- A longer prefix contains what a shorter one does (by structure: the library's prefix and
membership lemmas use choice). -/
theorem take_contains_mono : ∀ (order : List Nat) (a b : Nat), a ≤ b → ∀ (i : Nat),
    (order.take a).contains i = true → (order.take b).contains i = true
  | [], _, _, _, _, h => by simp at h
  | _ :: _, 0, _, _, _, h => by simp at h
  | _ :: _, _ + 1, 0, hab, _, _ => absurd hab (by omega)
  | x :: xs, a + 1, b + 1, hab, i, h => by
    simp only [List.take_succ_cons, List.contains_cons, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (take_contains_mono xs a b (by omega) i h)

theorem fit_monotone (narrow wide : Nat) (order : List Nat) (fs : List Field) (hw : narrow ≤ wide) :
    (fitRow narrow order fs).Sublist (fitRow wide order fs) := by
  -- The wide row stops no later than the narrow one: the narrow row's stopping
  -- point is also done at the wider width.
  have hdone : done wide order fs (dropCount narrow order fs) = true := by
    have h := dropCount_done narrow order fs
    simp only [done, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
    rcases h with h | h
    · exact Or.inl (Nat.le_trans h hw)
    · exact Or.inr h
  have hle : dropCount wide order fs ≤ dropCount narrow order fs := by
    rcases Nat.lt_or_ge (dropCount narrow order fs) (dropCount wide order fs) with hlt | hge
    · have := search_least wide order fs order.length 0 (dropCount narrow order fs) (Nat.zero_le _) hlt
      rw [hdone] at this; exact absurd this (by decide)
    · exact hge
  unfold fitRow kept without
  apply filter_sublist_of_imp
  intro f hf
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hf ⊢
  cases hc : (order.take (dropCount wide order fs)).contains f.id with
  | false => rfl
  | true =>
    have := take_contains_mono order _ _ hle f.id hc
    rw [this] at hf; exact absurd hf (by decide)

end ConsoleView

#print axioms ConsoleView.copy_exact
#print axioms ConsoleView.indented_heredoc_never_ends
#print axioms ConsoleView.fit_sublist
#print axioms ConsoleView.fit_keeps_essentials
#print axioms ConsoleView.fit_fits
#print axioms ConsoleView.fit_monotone
