import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Spaces

/-!
# Creating a space: a firing that makes a fresh handle

A space is **born** when an occurrence marking it is present: a marker is an occurrence that
`marker` selects, and the born handles of a store are the handles of its markers (`born`). The
**birth law** (`Births`) restricts the firings of any instance of the interface:

* no firing takes a marker, so a born space stays born;
* each marker a firing makes is at a handle not born before it, and it makes at most one marker
  per handle;
* every occurrence it takes, reads or makes lies at a handle born before it or born by it.

`spaced` is the restriction. Creating a space is a firing that makes a marker at a fresh handle, and
it may make the space's first rows in the same firing.

* **Born spaces stay born** (`born_subset_result`, `born_mono_run`), and the present occurrences of a
  store whose occurrences all lie at born handles keep that property (`wellBorn_result`).
* **Fresh means never born** (`created_never_born`): a handle created by a firing after a run was
  born at no state the run started from; since every suffix of a run is a run, at no state it
  visits.

## Controls (`Controls`), on the located first-order step

Space `1` is born at the start. Creating space `2` is admitted (`create_admitted`), also together with
its first row (`create_with_row_admitted`); making a row at space `2` before it is born is refused
(`row_before_birth_refused`) and admitted after (`row_after_birth_admitted`); creating space `2` a
second time is refused (`second_birth_refused`); taking a marker is refused
(`taking_marker_refused`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpacesCreation

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Commit Enabled fire mem_fire)

section Generic

universe uO uT uH uOcc uS uF uN

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  (P : Interface.Step X O State Firing) {H : Type uN} [DecidableEq H] (space : O → H)
  (marker : O → Bool)

/-- **The spaces born at a store**: the handles of its markers. -/
def born (store : Finset O) : Finset H := (store.filter fun o => marker o = true).image space

omit [DecidableEq O] in
theorem mem_born {store : Finset O} {h : H} :
    h ∈ born space marker store ↔ ∃ o ∈ store, marker o = true ∧ space o = h := by
  simp only [born, Finset.mem_image, Finset.mem_filter, and_assoc]

/-- **The birth law.** -/
structure Births {s : State} (f : Firing s) : Prop where
  keeps : ∀ o ∈ (P.selection f).taken, marker o = false
  fresh : ∀ o ∈ (P.selection f).made, marker o = true → space o ∉ born space marker (P.present s)
  single : ∀ o ∈ (P.selection f).made, ∀ o' ∈ (P.selection f).made, marker o = true →
    marker o' = true → space o = space o' → o = o'
  located : ∀ o ∈ (P.selection f).taken ++ (P.selection f).read ++ (P.selection f).made,
    space o ∈ born space marker (P.present s) ∨
      ∃ m ∈ (P.selection f).made, marker m = true ∧ space m = space o

/-- **The step whose firings obey the birth law.** -/
abbrev spaced := Spaces.restrict P (fun {_} f => Births P space marker f)

theorem present_result_mem {s : State} {f : Firing s} (admitted : P.Admits f) {o : O} :
    o ∈ P.present (P.result f admitted) ↔
      (o ∈ P.present s ∧ o ∉ (P.selection f).taken) ∨ o ∈ (P.selection f).made := by
  rw [P.present_result f admitted, mem_fire]
  simp [Selection.commit]

/-- **Born spaces stay born.** -/
theorem born_subset_result {s : State} {f : Firing s} (admitted : (spaced P space marker).Admits f) :
    born space marker (P.present s) ⊆ born space marker (P.present (P.result f admitted.1)) := by
  intro h member
  obtain ⟨o, present, isMarker, rfl⟩ := (mem_born space marker).mp member
  refine (mem_born space marker).mpr ⟨o, ?_, isMarker, rfl⟩
  refine (present_result_mem P admitted.1).mpr (Or.inl ⟨present, fun taken => ?_⟩)
  have kept := admitted.2.keeps o taken
  rw [isMarker] at kept
  cases kept

theorem born_mono_run : ∀ {s : State} (r : (spaced P space marker).Run s),
    born space marker (P.present s) ⊆ born space marker (P.present r.last)
  | _, .nil _ => le_refl _
  | _, .cons _ admitted rest => subset_trans (born_subset_result P space marker admitted)
      (born_mono_run rest)

/-- Every present occurrence lies at a born space. -/
def WellBorn (store : Finset O) : Prop := ∀ o ∈ store, space o ∈ born space marker store

/-- **The birth law keeps every occurrence at a born space.** -/
theorem wellBorn_result {s : State} {f : Firing s} (admitted : (spaced P space marker).Admits f)
    (wellBorn : WellBorn space marker (P.present s)) :
    WellBorn space marker (P.present (P.result f admitted.1)) := by
  intro o member
  rcases (present_result_mem P admitted.1).mp member with ⟨old, _⟩ | made
  · exact born_subset_result P space marker admitted (wellBorn o old)
  · rcases admitted.2.located o (List.mem_append_right _ made) with before | ⟨m, madeM, isMarker, same⟩
    · exact born_subset_result P space marker admitted before
    · rw [← same]
      exact (mem_born space marker).mpr
        ⟨m, (present_result_mem P admitted.1).mpr (Or.inr madeM), isMarker, rfl⟩

/-- **Fresh means never born**: a handle created by a firing after a run was not born where the
run started. -/
theorem created_never_born {s : State} (r : (spaced P space marker).Run s) {f : Firing r.last}
    (admitted : (spaced P space marker).Admits f) {o : O} (made : o ∈ (P.selection f).made)
    (isMarker : marker o = true) : space o ∉ born space marker (P.present s) :=
  fun before => admitted.2.fresh o made isMarker (born_mono_run P space marker r before)

end Generic

/-! ## Controls -/

namespace Controls

open Mettapedia.Logic.LP
open Disequality.Controls (signature app)
open Spaces (located label)

abbrev B := FirstOrder.action signature

/-- Rows `0`, `2` and `4` are markers, of spaces `1`, `2` and `2`; rows `1` and `3` are data at
spaces `1` and `2`. -/
def space : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | _ => 0

def payload : Nat → Term signature
  | 1 => app 0 (.const 7)
  | 3 => app 0 (.const 7)
  | _ => .const 0

def marker : Nat → Bool
  | 0 => true
  | 2 => true
  | 4 => true
  | _ => false

abbrev L := located B space payload
abbrev Fir := AnnotatedRuns.Firing (Nat × Term signature) (Subst signature) Nat
abbrev Q := spaced L.toStep space marker

/-- Space `1` is born; nothing else is present. -/
def start : Configuration (Nat × Term signature) Nat := ⟨[], {0}⟩

/-- Make the rows `made`. -/
def make (made : List Nat) : Fir := ⟨⟨[], [], [], [], made.map (label space payload)⟩, [], ⟨[], [], made⟩⟩

/-- Take row `0`, the marker of space `1`. -/
def takeMarker : Fir := ⟨⟨[(1, .const 0)], [], [], [], []⟩, [], ⟨[0], [], []⟩⟩

theorem make_admitted (C : Configuration (Nat × Term signature) Nat) (made : List Nat)
    (nodup : made.Nodup) (equations : C.equations = []) (fresh : ∀ o ∈ made, o ∉ C.present) :
    L.Admits (s := C) (make made) :=
  (PredicateQueryAdmission.valid_empty_iff _ _ _ _ _).mpr
    ⟨List.nodup_nil, nodup, rfl, rfl, rfl,
      ⟨by simp [make, Selection.commit], by simp [make, Selection.commit],
        by simp [make, Selection.commit], by
          rw [Finset.disjoint_left]
          intro o member present
          exact fresh o (by simpa [make, Selection.commit] using member) present,
        by simp [Selection.commit]⟩,
      ⟨B.identity, by
        intro e member
        simp [make, Selection.problem, Selection.equations, equations] at member⟩,
      by simp [make]⟩

/-- **Creating space `2`** is admitted. -/
theorem create_admitted : Q.Admits (s := start) (make [2]) :=
  ⟨make_admitted start [2] (List.nodup_singleton _) rfl (by decide),
    ⟨by decide, by decide, by decide, by decide⟩⟩

/-- **Creating space `2` with its first row**, in one firing. -/
theorem create_with_row_admitted : Q.Admits (s := start) (make [2, 3]) :=
  ⟨make_admitted start [2, 3] (by decide) rfl (by decide),
    ⟨by decide, by decide, by decide, by decide⟩⟩

/-- **A row at an unborn space is refused.** -/
theorem row_before_birth_refused : ¬ Q.Admits (s := start) (make [3]) := by
  rintro ⟨-, births⟩
  have located := births.located 3 (by decide)
  revert located
  decide

/-- The configuration after creating space `2`. -/
def afterBirth : Configuration (Nat × Term signature) Nat := L.result (make [2]) create_admitted.1

theorem row_after_birth_admitted : Q.Admits (s := afterBirth) (make [3]) :=
  ⟨make_admitted afterBirth [3] (List.nodup_singleton _) rfl (by decide),
    ⟨by decide, by decide, by decide, by decide⟩⟩

/-- **A space is born once.** -/
theorem second_birth_refused : ¬ Q.Admits (s := afterBirth) (make [4]) := by
  rintro ⟨-, births⟩
  have fresh := births.fresh 4 (by decide) rfl
  revert fresh
  decide

/-- **A marker cannot be taken.** -/
theorem taking_marker_refused : ¬ Q.Admits (s := start) takeMarker := by
  rintro ⟨-, births⟩
  have kept := births.keeps 0 (by decide)
  revert kept
  decide

/-- **The created handle was never born**: along the run creating space `2`, then making a row
there, space `2` was not born at the start. -/
theorem creation_run :
    ∃ r : Q.Run start, r.word.map Sigma.snd = [make [2], make [3]] ∧
      2 ∉ born space marker start.present ∧ 2 ∈ born space marker r.last.present :=
  ⟨.cons (make [2]) create_admitted (.cons (make [3]) row_after_birth_admitted (.nil _)), rfl,
    by decide, by decide⟩

end Controls

#print axioms mem_born
#print axioms born_subset_result
#print axioms born_mono_run
#print axioms wellBorn_result
#print axioms created_never_born
#print axioms Controls.create_admitted
#print axioms Controls.create_with_row_admitted
#print axioms Controls.row_before_birth_refused
#print axioms Controls.row_after_birth_admitted
#print axioms Controls.second_birth_refused
#print axioms Controls.taking_marker_refused
#print axioms Controls.creation_run

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpacesCreation
