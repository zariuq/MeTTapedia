import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Sharing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.Composition
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Located

/-!
# Two notions of a shared row, and what a none check reads: controls on first-order atoms

At the one frame of first-order atoms (`RuleSyntax.Examples`), with the rule that asks the none query
of `9`.

## The two notions of a shared row

* **A located row: the term is shared, the knowledge about it is not** (`located_row_two_readings`).
  In the candidate with a store at each location (`Hosting.Alternatives.Located.LState`), one shared
  row labelled by the unknown `x` is seen by a location that knows `x = 5` and by one that knows
  `x = 9`. The none query of `9` is admitted at the first and refused at the second, and the two stores
  have no common solution: the row is used under knowledge that is not joint.
* **A closed row: the row carries the knowledge** (`import_admitted`, `copy_passes_none`). In a
  bag of worlds the same row is published with the knowledge `x = 5`. A reader that knows nothing
  fires it (an instance of `snapshot_importable`) and then passes the none check of `9` on its
  copy, as the publisher does on the row; with the located row, a reader that does not know `x = 5`
  fails it (`RuleSyntax.Examples.noNine_refused_when_open`).

## What a none check reads

* `none_reads_its_own_world`: in a bag of worlds, the world that knows `x = 5` passes the none query
  check of `9` while another world holds the row `9`; the two can be merged (their joint knowledge is
  solvable, `besideJoining`); and in the merged world the check is refused.
-/

set_option autoImplicit false

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples
  (Tm X E x c demo shift everywhere boundRequest noNineFiring noNine_fresh noNine_admitted_when_bound)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls (atoms)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence (System)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Located (LState)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Worlds
  (snapshot)
open Mettapedia.Logic.LP

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Controls

open Interface (Frames)

/-! ## A located row -/

/-- One shared row labelled by the unknown `x`; one location knows `x = 5`, the other `x = 9`. -/
def twoReadings : LState Tm ℕ Bool where
  frame := PUnit.unit
  stores ℓ := cond ℓ [(x, c 5)] [(x, c 9)]
  live := {true, false}
  present := {0}
  label _ := x
  place _ := none

/-- Both locations see the shared row. -/
theorem twoReadings_visible (ℓ : Bool) : twoReadings.visible ℓ = {0} :=
  Finset.filter_true_of_mem fun _ _ => Or.inr rfl

/-- The row `x`, with the knowledge `x = 9`. -/
def nineRequest : State Tm ℕ := ⟨PUnit.unit, [(x, c 9)], {0}, fun _ => x⟩

/-- The location that knows `x = 5` sees the row `x` with that knowledge. -/
theorem view_five : twoReadings.view true = boundRequest := by
  show (⟨PUnit.unit, [(x, c 5)], twoReadings.visible true, fun _ => x⟩ : State Tm ℕ) = boundRequest
  rw [twoReadings_visible]
  rfl

/-- The location that knows `x = 9` sees the row `x` with that knowledge. -/
theorem view_nine : twoReadings.view false = nineRequest := by
  show (⟨PUnit.unit, [(x, c 9)], twoReadings.visible false, fun _ => x⟩ : State Tm ℕ) = nineRequest
  rw [twoReadings_visible]
  rfl

/-- **The none query of `9` is refused where the row is known to be `9`.** -/
theorem none_refused_when_nine : ¬ (step X ℕ E demo).Admits (s := nineRequest) noNineFiring := by
  intro admitted
  obtain ⟨-, -, -, -, checks, -⟩ := (admits_iff noNineFiring).mp admitted
  have solved : X.Models (a := PUnit.unit) (b := PUnit.unit) (everywhere 9)
      (noNineFiring.information X nineRequest) := by
    intro e inside
    have known : noNineFiring.information X nineRequest = [(x, c 9)] := rfl
    rw [known, List.mem_singleton] at inside
    subst inside
    rfl
  have holds := checks (.predicate .none (c 9)) (List.mem_singleton_self _) PUnit.unit _ solved
  exact holds 0 (Finset.mem_singleton_self 0) rfl

/-- The two stores, joined. -/
theorem twoReadings_joint :
    twoReadings.stores true ++ twoReadings.stores false = [(x, c 5), (x, c 9)] := rfl

/-- **A located row: the term is shared, the knowledge about it is not.** The two locations see the
states named; the none query of `9` is admitted at the one that knows `x = 5` and refused at the one
that knows `x = 9`; and the two stores have no common solution. -/
theorem located_row_two_readings :
    twoReadings.view true = boundRequest ∧ twoReadings.view false = nineRequest ∧
      (step X ℕ E demo).Admits (s := boundRequest) noNineFiring ∧
      ¬ (step X ℕ E demo).Admits (s := nineRequest) noNineFiring ∧
      ¬ X.Solvable (a := PUnit.unit) (twoReadings.stores true ++ twoReadings.stores false) := by
  refine ⟨view_five, view_nine, noNine_admitted_when_bound, none_refused_when_nine, ?_⟩
  rw [twoReadings_joint]
  rintro ⟨_, σ, solved⟩
  have five : σ 0 = c 5 := solved (x, c 5) List.mem_cons_self
  have nine : σ 0 = c 9 := solved (x, c 9) (List.mem_cons_of_mem _ List.mem_cons_self)
  exact absurd (Term.const.inj (five.symm.trans nine)) (by decide)

/-! ## A closed row -/

/-- The closed row published from the world that knows `x = 5`: the row `x` with that knowledge. -/
abbrev fiveRow : Rule Tm := snapshot boundRequest x

/-- A reader that knows nothing and holds no row. -/
def emptyReader : State Tm ℕ := ⟨PUnit.unit, [], ∅, fun _ => c 0⟩

/-- The reader's rules: the rules of `demo`, and the space that holds the closed row. -/
abbrev readerProgram : Program Tm := demo ∪ {fiveRow}

/-- The reader fires the closed row, its unknown opened apart, and makes the copy at identity `0`. -/
def importFiring : Firing ℕ E readerProgram PUnit.unit :=
  ⟨fiveRow, Set.mem_union_right _ (Set.mem_singleton _), PUnit.unit, shift, ⟨[], [], [0]⟩, []⟩

theorem import_fresh : importFiring.Fresh X emptyReader := by
  intro b g h
  refine ⟨fun _ => h 0, ?_, ?_⟩
  · rintro t (member | member | ⟨o, present, -⟩)
    · exact absurd member List.not_mem_nil
    · exact absurd member List.not_mem_nil
    · exact absurd present (Finset.notMem_empty o)
  · intro t member
    change t ∈ [x, c 5, x] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl

/-- **The reader fires the closed row**: its own knowledge is solvable, and so was the publisher's.
An instance of `snapshot_importable`. -/
theorem import_admitted : importFiring.Admits X emptyReader :=
  (snapshot_importable (X := X) (E := E) (P := readerProgram) (terminalFrame := PUnit.unit)
    (fun _ => ⟨Subst.id atoms⟩) boundRequest emptyReader x
    (Set.mem_union_right _ (Set.mem_singleton _)) PUnit.unit shift 0 import_fresh
    (Finset.notMem_empty 0)).mpr
    ⟨⟨PUnit.unit, Subst.id atoms, fun _ member => absurd member List.not_mem_nil⟩,
      ⟨PUnit.unit, everywhere 5, fun e member => by
        change e ∈ [(x, c 5)] at member
        rw [List.mem_singleton] at member
        subst member
        rfl⟩⟩

/-- **The row carries the knowledge**: after firing the closed row, the reader, who knew nothing,
passes the none check of `9` on its copy. -/
theorem copy_passes_none :
    (widen (Q := readerProgram) Set.subset_union_left noNineFiring).Admits X
      (importFiring.result X emptyReader) := by
  refine ⟨⟨noNine_fresh _, List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [widen, noNineFiring, Selection.commit]
  · refine ⟨PUnit.unit, everywhere 5, fun e inside => ?_⟩
    change e ∈ [((Term.var 1 : Term atoms), c 5)] at inside
    rw [List.mem_singleton] at inside
    subst inside
    rfl
  · intro b σ solved
    have known : X.Models (a := PUnit.unit) (b := b) σ [((Term.var 1 : Term atoms), c 5)] := solved
    have bound : σ 1 = c 5 := known ((Term.var 1 : Term atoms), c 5) List.mem_cons_self
    refine ⟨fun check inside => ?_, fun q inside => absurd inside List.not_mem_nil⟩
    have isNone : check = Check.predicate .none (c 9) := List.mem_singleton.mp inside
    subst isNone
    intro o present equated
    have isCopy : o = 0 := by
      rcases MeTTaCalculus.OccurrenceCommits.mem_fire.mp present with ⟨inReader, -⟩ | made
      · exact absurd inReader (Finset.notMem_empty o)
      · exact List.mem_singleton.mp (List.mem_toFinset.mp made)
    subst isCopy
    have nine : (c 9 : Term atoms) = σ 1 := equated
    rw [bound] at nine
    exact absurd (Term.const.inj nine) (by decide)

/-! ## What a none check reads -/

/-- **Merging at the one frame**: the knowledge of both and the rows of both
(`RuleSyntax.Scope.beside`); alive only if both were. -/
def besideJoining : Joining X ℕ where
  join := Scope.beside
  left_alive _ _ alive :=
    Frames.solvable_of_subset (fun _ member => List.mem_append_left _ member) alive
  right_alive _ _ alive :=
    Frames.solvable_of_subset (fun _ member => List.mem_append_right _ member) alive

/-- A world that holds the row `9`, with no rule. -/
def nineHolder : State Tm ℕ := ⟨PUnit.unit, [], {1}, fun _ => c 9⟩

/-- **A none check reads the rows of its own world.** Beside a world that holds the row `9`, the
world that knows `x = 5` passes the none check of `9`; the two can be merged; and in the merged
world the check is refused. -/
theorem none_reads_its_own_world :
    Move X besideJoining (events X ℕ E)
        ⟨(⟨demo, boundRequest⟩ : System Tm ℕ) ::ₘ (⟨∅, nineHolder⟩ : System Tm ℕ) ::ₘ 0, ∅⟩
        ⟨(⟨demo, noNineFiring.result X boundRequest⟩ : System Tm ℕ) ::ₘ
          (⟨∅, nineHolder⟩ : System Tm ℕ) ::ₘ 0, ∅⟩ ∧
      X.Solvable (besideJoining.join boundRequest nineHolder).knowledge ∧
      ¬ (step X ℕ E demo).Admits (s := Scope.beside boundRequest nineHolder) noNineFiring := by
  refine ⟨Move.fire (family := events X ℕ E) ((⟨∅, nineHolder⟩ : System Tm ℕ) ::ₘ 0) ∅ ⟨demo, boundRequest⟩
    ⟨widen Set.subset_union_left noNineFiring, noNine_admitted_when_bound⟩, ?_, ?_⟩
  · refine ⟨PUnit.unit, everywhere 5, fun e member => ?_⟩
    change e ∈ [(x, c 5)] at member
    rw [List.mem_singleton] at member
    subst member
    rfl
  · intro admitted
    obtain ⟨-, -, -, -, checks, -⟩ := (admits_iff noNineFiring).mp admitted
    have solved : X.Models (a := PUnit.unit) (b := PUnit.unit) (everywhere 5)
        (noNineFiring.information X (Scope.beside boundRequest nineHolder)) := by
      intro e inside
      change e ∈ [(x, c 5)] at inside
      rw [List.mem_singleton] at inside
      subst inside
      rfl
    have holds := checks (.predicate .none (c 9)) (List.mem_singleton_self _) PUnit.unit _ solved
    exact holds 1 (Finset.mem_union_right _ (Finset.mem_singleton_self 1)) rfl

#print axioms twoReadings_visible
#print axioms none_refused_when_nine
#print axioms located_row_two_readings
#print axioms import_fresh
#print axioms import_admitted
#print axioms copy_passes_none
#print axioms besideJoining
#print axioms none_reads_its_own_world

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Controls
