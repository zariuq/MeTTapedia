import Mathlib.Tactic

/-!
# Cursors over a relation's facts read the live table up to a ceiling

An occurrence cursor over the facts a relation keeps copied the facts its
pattern selects when it opened, and registered the copy as a root, so that
the facts it had yet to lend stayed as they were through any later change.
Under a recursion that keeps a match open at every level, those copies and
registrations stood beside each other for the whole run.

A relation's table adds a fact at its end and moves facts only when one is
removed or the table is renumbered.  So a cursor can read the live table:
it keeps the table's length when it opened (its ceiling) and its position,
and passes over what was added after it opened.  Only a removal, or a
renumbering, makes it copy what it has still to read, once, as the snapshot
would have held it.  While attached, the facts it has yet to read are the
table's own, which the relation holds.

The model: a table as a list, reads, adds at the end and removals by
position, and two cursors opened on the same table: the eager one with its
copy, the lazy one attached at the table's length.  This file proves:
* `lazy_run_eq_eager_run`: under any sequence of reads, adds and removals,
  the lazy cursor yields exactly what the eager one yields;
* `lazy_copies_le`: the lazy cursor copies at most the facts the eager one
  copied at open, and `lazy_copies_eq_zero` none where no removal comes.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.KeptCursorCeiling

variable {τ : Type}

/-- What happens next: the cursor reads a position, a fact is added at the
table's end, or the fact at a position is removed. -/
inductive Event (τ : Type) where
  | read
  | add (fact : τ)
  | remove (position : ℕ)

/-- The eager cursor: the facts it copied at open and has yet to read.  A
read lends the next one if the pattern selects it. -/
def eagerStep (sel : τ → Bool) : List τ → Event τ → List τ × Option τ
  | [], .read => ([], none)
  | fact :: rest, .read => (rest, if sel fact then some fact else none)
  | rest, .add _ => (rest, none)
  | rest, .remove _ => (rest, none)

/-- The lazy cursor: attached to the live table at its ceiling and position,
or detached with the facts it copied. -/
inductive Cursor (τ : Type) where
  | attached (ceiling position : ℕ)
  | detached (rest : List τ)

/-- The facts a cursor has yet to read. -/
def Cursor.rest (table : List τ) : Cursor τ → List τ
  | .attached ceiling position => (table.take ceiling).drop position
  | .detached rest => rest

/-- A step of the lazy cursor and its table.  A removal detaches the cursor
first, copying what it has yet to read. -/
def lazyStep (sel : τ → Bool) :
    List τ × Cursor τ → Event τ → (List τ × Cursor τ) × Option τ
  | (table, .attached ceiling position), .read =>
    match (table.take ceiling).drop position with
    | [] => ((table, .attached ceiling position), none)
    | fact :: _ =>
      ((table, .attached ceiling (position + 1)), if sel fact then some fact else none)
  | (table, .detached []), .read => ((table, .detached []), none)
  | (table, .detached (fact :: rest)), .read =>
    ((table, .detached rest), if sel fact then some fact else none)
  | (table, cursor), .add fact => ((table ++ [fact], cursor), none)
  | (table, cursor), .remove position =>
    ((table.eraseIdx position, .detached (cursor.rest table)), none)

/-- What the eager cursor yields over a run of events. -/
def eagerRun (sel : τ → Bool) : List τ → List (Event τ) → List (Option τ)
  | _, [] => []
  | rest, event :: events =>
    (eagerStep sel rest event).2 :: eagerRun sel (eagerStep sel rest event).1 events

/-- What the lazy cursor yields over a run of events. -/
def lazyRun (sel : τ → Bool) : List τ × Cursor τ → List (Event τ) → List (Option τ)
  | _, [] => []
  | state, event :: events =>
    (lazyStep sel state event).2 :: lazyRun sel (lazyStep sel state event).1 events

/-- The lazy cursor corresponds to the eager one holding `rest`: they have
the same facts yet to read, and an attached cursor's ceiling lies within the
table. -/
def Corresponds (state : List τ × Cursor τ) (rest : List τ) : Prop :=
  state.2.rest state.1 = rest ∧
    ∀ ceiling position, state.2 = .attached ceiling position → ceiling ≤ state.1.length

theorem corresponds_step (sel : τ → Bool) (state : List τ × Cursor τ) (rest : List τ)
    (event : Event τ) (h : Corresponds state rest) :
    (lazyStep sel state event).2 = (eagerStep sel rest event).2 ∧
      Corresponds (lazyStep sel state event).1 (eagerStep sel rest event).1 := by
  obtain ⟨table, cursor⟩ := state
  obtain ⟨hrest, hceil⟩ := h
  cases event with
  | read =>
    cases cursor with
    | attached ceiling position =>
      have hle : ceiling ≤ table.length := hceil ceiling position rfl
      simp only [Cursor.rest] at hrest
      subst hrest
      cases hfacts : (table.take ceiling).drop position with
      | nil =>
        simp [lazyStep, eagerStep, hfacts, Corresponds, Cursor.rest, hle]
      | cons fact more =>
        have hmore : (table.take ceiling).drop (position + 1) = more := by
          rw [← List.tail_drop, hfacts]
          rfl
        simp [lazyStep, eagerStep, hfacts, Corresponds, Cursor.rest, hle, hmore]
    | detached facts =>
      simp only [Cursor.rest] at hrest
      subst hrest
      cases facts with
      | nil => simp [lazyStep, eagerStep, Corresponds, Cursor.rest]
      | cons fact more => simp [lazyStep, eagerStep, Corresponds, Cursor.rest]
  | add fact =>
    cases cursor with
    | attached ceiling position =>
      have hle : ceiling ≤ table.length := hceil ceiling position rfl
      simp only [Cursor.rest] at hrest
      subst hrest
      simp only [lazyStep, eagerStep, Corresponds, Cursor.rest,
        List.take_append_of_le_length hle, true_and]
      intro c p hcp
      cases hcp
      simp only [List.length_append, List.length_singleton]
      omega
    | detached facts =>
      simp only [Cursor.rest] at hrest
      subst hrest
      simp [lazyStep, eagerStep, Corresponds, Cursor.rest]
  | remove position =>
    subst hrest
    simp [lazyStep, eagerStep, Corresponds, Cursor.rest]

/-- Under any run of reads, adds and removals, the lazy cursor yields
exactly what the eager cursor yields. -/
theorem lazy_run_eq_eager_run (sel : τ → Bool) (events : List (Event τ)) :
    ∀ (state : List τ × Cursor τ) (rest : List τ),
      Corresponds state rest → lazyRun sel state events = eagerRun sel rest events := by
  induction events with
  | nil => intro state rest _; rfl
  | cons event events ih =>
    intro state rest h
    obtain ⟨hyield, hnext⟩ := corresponds_step sel state rest event h
    simp only [lazyRun, eagerRun]
    rw [hyield, ih _ _ hnext]

/-- A cursor opened on `table` attaches at the table's length; the eager one
copies the whole table. -/
theorem opened_corresponds (table : List τ) :
    Corresponds (table, Cursor.attached table.length 0) table := by
  refine ⟨by simp [Cursor.rest], ?_⟩
  intro c p hcp
  cases hcp
  exact le_rfl

/-- The facts the lazy cursor copies over a run: what it has yet to read at
the first removal that finds it attached. -/
def lazyCopies : List τ × Cursor τ → List (Event τ) → ℕ
  | _, [] => 0
  | (table, .attached ceiling position), .remove p :: events =>
    ((table.take ceiling).drop position).length +
      lazyCopies (table.eraseIdx p, .detached ((table.take ceiling).drop position)) events
  | (_, .detached _), .remove _ :: _ => 0
  | (table, cursor), .read :: events =>
    lazyCopies (lazyStep (fun _ => true) (table, cursor) .read).1 events
  | (table, cursor), .add fact :: events => lazyCopies (table ++ [fact], cursor) events

theorem lazyCopies_detached (table : List τ) (facts : List τ) (events : List (Event τ)) :
    lazyCopies (table, .detached facts) events = 0 := by
  induction events generalizing table facts with
  | nil => rfl
  | cons event events ih =>
    cases event with
    | read =>
      cases facts with
      | nil => simp only [lazyCopies, lazyStep]; exact ih _ _
      | cons fact more => simp only [lazyCopies, lazyStep]; exact ih _ _
    | add fact => simp only [lazyCopies]; exact ih _ _
    | remove p => rfl

/-- The lazy cursor copies at most what the eager one copied at open. -/
theorem lazy_copies_le (events : List (Event τ)) :
    ∀ (table : List τ) (ceiling position : ℕ), ceiling ≤ table.length →
      lazyCopies (table, .attached ceiling position) events ≤ ceiling := by
  induction events with
  | nil => intro _ _ _ _; exact Nat.zero_le _
  | cons event events ih =>
    intro table ceiling position hle
    cases event with
    | read =>
      simp only [lazyCopies, lazyStep]
      cases (table.take ceiling).drop position with
      | nil => exact ih table ceiling position hle
      | cons fact more => exact ih table ceiling (position + 1) hle
    | add fact =>
      simp only [lazyCopies]
      exact ih (table ++ [fact]) ceiling position
        (by simp only [List.length_append, List.length_singleton]; omega)
    | remove p =>
      simp only [lazyCopies]
      rw [lazyCopies_detached, add_zero]
      calc ((table.take ceiling).drop position).length
          ≤ (table.take ceiling).length := by simp
        _ ≤ ceiling := List.length_take_le _ _

/-- Without a removal the lazy cursor copies nothing. -/
theorem lazy_copies_eq_zero (events : List (Event τ))
    (none_removed : ∀ event ∈ events, ∀ p, event ≠ Event.remove p) :
    ∀ (table : List τ) (cursor : Cursor τ), lazyCopies (table, cursor) events = 0 := by
  induction events with
  | nil => intro _ _; rfl
  | cons event events ih =>
    intro table cursor
    have rest_none : ∀ e ∈ events, ∀ p, e ≠ Event.remove p :=
      fun e he p => none_removed e (List.mem_cons_of_mem _ he) p
    cases event with
    | read =>
      cases cursor with
      | attached ceiling position => simp only [lazyCopies]; exact ih rest_none _ _
      | detached facts => exact lazyCopies_detached table facts _
    | add fact =>
      cases cursor with
      | attached ceiling position => simp only [lazyCopies]; exact ih rest_none _ _
      | detached facts => exact lazyCopies_detached _ facts _
    | remove p => exact absurd rfl (none_removed _ (List.mem_cons_self) p)

/-! ## Examples -/

/-- A fact added after the cursor opened is not lent: both cursors lend 1
and 2, then nothing. -/
example :
    lazyRun (fun _ => true) ([1, 2], Cursor.attached 2 0)
        [.read, .add (3 : ℕ), .read, .read] =
      [some 1, none, some 2, none] := by decide

/-- A removal after the cursor opened does not hide a fact it has yet to
lend. -/
example :
    lazyRun (fun _ => true) ([1, 2], Cursor.attached 2 0)
        [.read, .remove 1, .read, .read] =
      [some (1 : ℕ), none, some 2, none] := by decide

end Mettapedia.Machines.KeptCursorCeiling
