import Mathlib.Data.List.Basic

/-! # When a selected stream may be evaluated while it is read

Comparing a row chooses a body and its witnesses. Evaluation of that body
can change the world. This module distinguishes two questions:

* For an aligned selection trace (one slot per candidate), when does
  selecting everything at the entry cut agree with interleaving selection
  and effects? Exactly when each still-pending decision agrees at its
  turn. The effects need not preserve already-consumed decisions.
* What part of the selection trace survives if the caller sees only
  the evaluated bodies and their effects? Absent slots disappear; for
  arbitrary observers of bodies the ordered list of selected bodies is
  the exact information needed. Neither count nor a set of bodies is enough.

The candidate stream is supplied at entry. No scheduling, memory lifetime,
or acquisition of that entry cut is assumed by either theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Equations.SelectedEffects

variable {World Row Body Out : Type*}

/-- An absent selection is not a body execution. -/
def fire (execute : World → Body → World × List Out) (w : World) :
    Option Body → World × List Out
  | none => (w, [])
  | some body => execute w body

def bodies (execute : World → Body → World × List Out) : List Body → World → World × List Out
  | [], w => (w, [])
  | body :: rest, w =>
    let now := execute w body
    let tail := bodies execute rest now.1
    (tail.1, now.2 ++ tail.2)

def runSelected (execute : World → Body → World × List Out)
    (selected : List (Option Body)) (w : World) : World × List Out :=
  bodies execute (selected.filterMap id) w

theorem runSelected_cons (execute : World → Body → World × List Out)
    (head : Option Body) (tail : List (Option Body)) (w : World) :
    runSelected execute (head :: tail) w =
      let now := fire execute w head
      let rest := runSelected execute tail now.1
      (rest.1, now.2 ++ rest.2) := by
  cases head <;> simp [runSelected, fire, bodies]

structure LiveResult (World Body Out : Type*) where
  selected : List (Option Body)
  finish : World
  delivered : List Out

def live (select : World → Row → Option Body) (execute : World → Body → World × List Out) :
    List Row → World → LiveResult World Body Out
  | [], w => ⟨[], w, []⟩
  | row :: rest, w =>
    let pick := select w row
    let now := fire execute w pick
    let later := live select execute rest now.1
    ⟨pick :: later.selected, later.finish, now.2 ++ later.delivered⟩

theorem replay (select : World → Row → Option Body) (execute : World → Body → World × List Out)
    (rows : List Row) (w : World) :
    runSelected execute (live select execute rows w).selected w =
      ((live select execute rows w).finish, (live select execute rows w).delivered) := by
  induction rows generalizing w with
  | nil => rfl
  | cons row rest ih =>
    simp only [live, runSelected_cons, ih]

/-- The exact test for agreement of decisions on a particular run. It is
indexed by the world reached after executing the earlier entry selections,
not universally quantified over all future worlds. -/
inductive Stable (select : World → Row → Option Body)
    (execute : World → Body → World × List Out) (entry : World) : List Row → World → Prop where
  | nil (w : World) : Stable select execute entry [] w
  | cons {row : Row} {rest : List Row} {w : World} :
      select w row = select entry row →
      Stable select execute entry rest (fire execute w (select entry row)).1 →
      Stable select execute entry (row :: rest) w

theorem selections_iff_stable (select : World → Row → Option Body)
    (execute : World → Body → World × List Out) (entry : World)
    (rows : List Row) (w : World) :
    (live select execute rows w).selected = rows.map (select entry) ↔
      Stable select execute entry rows w := by
  induction rows generalizing w with
  | nil => exact ⟨fun _ => .nil _, fun _ => rfl⟩
  | cons row rest ih =>
    simp only [live, List.map_cons, List.cons.injEq]
    constructor
    · rintro ⟨decision, later⟩
      apply Stable.cons decision
      rw [← decision]
      exact (ih _).mp later
    · intro stable
      cases stable with
      | cons decision later =>
        exact ⟨decision, decision.symm ▸ (ih _).mpr later⟩

theorem same_execution_of_stable (select : World → Row → Option Body)
    (execute : World → Body → World × List Out) {entry w : World} {rows : List Row}
    (stable : Stable select execute entry rows w) :
    ((live select execute rows w).finish, (live select execute rows w).delivered) =
      runSelected execute (rows.map (select entry)) w := by
  rw [← replay, (selections_iff_stable select execute entry rows w).mpr stable]

/-- Commutation local to the suffix. One effect can change the validity
of its own row or a previously chosen row without changing the result. -/
theorem stable_of_suffix_frame (select : World → Row → Option Body)
    (execute : World → Body → World × List Out) (entry w : World) (rows : List Row)
    (agrees : ∀ r ∈ rows, select w r = select entry r)
    (frame : ∀ past row rest, rows = past ++ row :: rest →
      ∀ (s : World) (r : Row), r ∈ rest →
        select (fire execute s (select entry row)).1 r = select s r) :
    Stable select execute entry rows w := by
  induction rows generalizing w with
  | nil => exact .nil w
  | cons row rest ih =>
    refine .cons (agrees row (by simp)) (ih _ ?_ ?_)
    · intro r member
      exact (frame [] row rest rfl w r member).trans (agrees r (List.mem_cons_of_mem _ member))
    · intro past next later split
      exact frame (row :: past) next later (congrArg (List.cons row) split)

/-- No observable absent slot is needed by this class of consumers. The
converse follows by choosing the interpreter that echoes every body; this
also prevents erasing order or collapsing two equal body occurrences.
This does not cover an observer that sees silent ticks or refusals. -/
theorem selected_stream_exact {B : Type*} (left right : List (Option B)) :
    (∀ execute : Unit → B → Unit × List B, runSelected execute left () =
      runSelected execute right ()) ↔ left.filterMap id = right.filterMap id := by
  constructor
  · intro equal
    let echo : Unit → B → Unit × List B := fun _ b => ((), [b])
    have replayEcho : ∀ xs : List B, (bodies echo xs ()).2 = xs := by
      intro xs
      induction xs with
      | nil => rfl
      | cons x xs ih => simp [bodies, echo, ih]
    simpa only [runSelected, replayEcho] using congrArg Prod.snd (equal echo)
  · intro same execute
    simp only [runSelected, same]

namespace Examples

private def visible (yes : Bool) (r : Nat) : Option Nat := if yes then some r else none
private def revoke (yes : Bool) (r : Nat) : Bool × List Nat := (if r = 0 then false else yes, [r])

/-- The first body withdraws the reading license. The second body of the
entered query still runs, but an interleaved reader would miss it. -/
theorem alias_retraction_separates_the_readings :
    runSelected revoke ([0, 1].map (visible true)) true = (false, [0, 1]) ∧
    (live visible revoke [0, 1] true).delivered = [0] := ⟨rfl, rfl⟩

private def localVisibility (yes : Bool) (r : Nat) : Option Nat :=
  if r = 0 then visible yes r else some r

/-- Leaving the first row's region changes its earlier decision but
preserves the suffix. A global disjointness requirement would reject this
correct interchange. -/
theorem a_consumed_decision_can_change :
    Stable localVisibility revoke true [0, 1] true ∧
    localVisibility (revoke true 0).1 0 ≠ localVisibility true 0 := by
  refine ⟨.cons rfl (.cons rfl (.nil _)), ?_⟩
  decide

theorem silent_slots_have_no_body_effect :
    ∀ execute : Unit → Nat → Unit × List Nat,
      runSelected execute [some 3, none] () = runSelected execute [none, some 3] () :=
  (selected_stream_exact _ _).mpr rfl

theorem equal_counts_cannot_reorder_effects :
    ¬ (∀ execute : Unit → Nat → Unit × List Nat,
      runSelected execute [some 0, some 1] () = runSelected execute [some 1, some 0] ()) := by
  intro assumed
  have impossible := (selected_stream_exact _ _).mp assumed
  change [0, 1] = [1, 0] at impossible
  cases impossible

end Examples

end Mettapedia.GSLT.Equations.SelectedEffects
