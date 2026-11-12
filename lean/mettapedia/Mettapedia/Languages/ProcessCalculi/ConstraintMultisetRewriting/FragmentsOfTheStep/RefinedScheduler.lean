import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.MonotoneInference

/-!
# Refined schedulers: refinements of the step, sound by construction

A **scheduler** keeps bookkeeping beside the state (an active stack, a propagation history, rule
priorities) and moves by two kinds of transition (`Scheduler.Transition`): it fires a firing the
step admits, updating its bookkeeping, or it moves bookkeeping only. This is the shape of the refined
operational semantics of CHR, which Duck, Stuckey, García de la Banda and Holzbaur prove implements
the theoretical operational semantics: the refined semantics only chooses among what the theoretical
one allows.

* `Scheduler.refines`: every scheduler path erases to a run of the step from the same state to the
  same state. **A scheduler is a refinement of the step.**
* `Scheduler.sound`: along every scheduler path, every solution of the last knowledge pulls back to
  a solution of the first (`Interface.Step.Run.models_start`). Soundness is the step's, inherited.

Both hold by construction: a scheduler fires only firings the step admits. CHR's refined semantics
itself (the active stack, occurrence order, Activate, Drop and Default) is not modelled here, and no
theorem maps it onto `Scheduler`; once modelled it would be one such scheduler.

## An instance in the style of the refined semantics

`priority program`: over ground terms, rule `i` of the program fires with heads `h` only when
`(i, h)` is not yet in the propagation history, and no earlier rule has an admitted firing whose heads
are new to the history; the entry is then recorded. The active stack and the order of occurrences
are not modelled; the instance keeps rule priority and the propagation history.

## Controls

* Positive: `Controls.history_stops_propagation`: a propagation rule (keep `a`, make `b`) is admitted
  again by the step, making another copy; the scheduler fires it once and has no further transition.
* Negative: `Controls.priority_incomplete`: with two rules taking `item`, the step reaches a store
  holding `right`, and no path of the scheduler ever does. A refinement is sound, not complete: the
  scheduler's states are among the step's, and the converse fails.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep

namespace RefinedScheduler

universe uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Interface.Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS}
  {Firing : State → Type uF}

/-- **A scheduler over a step**: bookkeeping, the firings it may fire with their bookkeeping update,
and bookkeeping-only moves. -/
structure Scheduler (P : Interface.Step X O State Firing) where
  Book : Type
  fires : (s : State) → Book → (f : Firing s) → P.Admits f → Book → Prop
  moves : State → Book → Book → Prop

namespace Scheduler

variable {P : Interface.Step X O State Firing} (Q : Scheduler P)

/-- One transition of a scheduler. -/
inductive Transition : State × Q.Book → State × Q.Book → Prop
  | fire {s : State} {b b' : Q.Book} (f : Firing s) (admitted : P.Admits f) :
      Q.fires s b f admitted b' → Transition (s, b) (P.result f admitted, b')
  | move {s : State} {b b' : Q.Book} : Q.moves s b b' → Transition (s, b) (s, b')

variable {Q}

/-- **A scheduler is a refinement of the step**: every path erases to a run of the step. -/
theorem refines {x y : State × Q.Book} (path : Relation.ReflTransGen Q.Transition x y) :
    ∃ r : P.Run x.1, r.last = y.1 := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨.nil _, rfl⟩
  | head step _ later =>
      obtain ⟨r, last⟩ := later
      cases step with
      | fire f admitted _ => exact ⟨.cons f admitted r, last⟩
      | move _ => exact ⟨r, last⟩

/-- **A scheduler is sound**: its paths erase to runs, along which knowledge only refines. -/
theorem sound {x y : State × Q.Book} (path : Relation.ReflTransGen Q.Transition x y) :
    ∃ r : P.Run x.1, r.last = y.1 ∧ ∀ {b : Obj} (σ : Hom (P.frame r.last) b),
      X.Models σ (P.knowledge r.last) → X.Models (X.comp σ r.toLast) (P.knowledge x.1) := by
  obtain ⟨r, last⟩ := refines path
  exact ⟨r, last, fun σ solved => r.models_start σ solved⟩

end Scheduler

end RefinedScheduler

/-! ## Priority with a propagation history -/

namespace RefinedScheduler

open NamesOnTheStep NamesOnTheStep.IssuingControls GroundFirings

/-- The heads of a firing: what it takes and what it reads. -/
def heads (f : Fir) : List Occ := f.selection.taken ++ f.selection.read

/-- **The priority scheduler with a propagation history** over a program. -/
abbrev priority (program : List (RuleInstance Expr)) : Scheduler base where
  Book := List (ℕ × List Occ)
  fires s history f _ history' :=
    ∃ i, program[i]? = some f.rule ∧ f.queries = [] ∧ (i, heads f) ∉ history ∧
      history' = (i, heads f) :: history ∧
      ∀ j < i, ∀ g : Fir, program[j]? = some g.rule → g.queries = [] → (j, heads g) ∉ history →
        ¬ base.Admits (s := s) g
  moves _ _ _ := False

theorem valid_of_admits {C : Conf} {f : Fir} (noQueries : f.queries = [])
    (admitted : base.Admits (s := C) f) : f.selection.Valid ground Prod.fst f.rule C := by
  have valid : PredicateQueryAdmission.Valid ground Prod.fst f.rule f.queries C f.selection := admitted
  rw [noQueries] at valid
  exact (PredicateQueryAdmission.valid_empty_iff ground Prod.fst _ _ _).mp valid

theorem admits_of_valid {C : Conf} {r : RuleInstance Expr} {sel : Selection Occ}
    (valid : sel.Valid ground Prod.fst r C) : base.Admits (s := C) (⟨r, [], sel⟩ : Fir) :=
  (PredicateQueryAdmission.valid_empty_iff ground Prod.fst _ _ _).mpr valid

end RefinedScheduler

namespace RefinedScheduler.Controls

open NamesOnTheStep NamesOnTheStep.IssuingControls GroundFirings

def itemA : Expr := .sym 70
def itemB : Expr := .sym 71

/-- A propagation rule: keep `a`, make `b`. -/
def propagate : RuleInstance Expr := rule [] [itemA] [itemB]

def start : Conf := ⟨[], {(itemA, 0)}⟩

def firstAt : Fir := ⟨propagate, [], ⟨[], [(itemA, 0)], [(itemB, 0)]⟩⟩
def secondAt : Fir := ⟨propagate, [], ⟨[], [(itemA, 0)], [(itemB, 1)]⟩⟩

theorem first_admitted : base.Admits (s := start) firstAt :=
  admits_of_valid (ground_valid (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl
    (no_checks rfl))

/-- The store after the first firing. -/
def afterFirst : Conf := firstAt.selection.result Prod.fst propagate start

theorem afterFirst_present : afterFirst.present = {(itemA, 0), (itemB, 0)} := by decide

theorem second_admitted : base.Admits (s := afterFirst) secondAt :=
  admits_of_valid (ground_valid (by decide) (by decide) rfl rfl rfl (by decide)
    (result_knowledge (valid_of_admits rfl first_admitted)) rfl (no_checks rfl))

/-- The scheduler over the one-rule program. -/
abbrev once : Scheduler base := priority [propagate]

theorem first_scheduled :
    (once).Transition (start, []) (afterFirst, [(0, [(itemA, 0)])]) :=
  Scheduler.Transition.fire (Q := once) firstAt first_admitted
    ⟨0, rfl, rfl, by simp, rfl, fun j less => absurd less (Nat.not_lt_zero j)⟩

theorem only_propagate {g : Fir} {i : ℕ} (inProgram : [propagate][i]? = some g.rule) :
    i = 0 ∧ g.rule = propagate := by
  rcases i with _ | i
  · exact ⟨rfl, (Option.some.inj (show some propagate = some g.rule from inProgram)).symm⟩
  · simp at inProgram

/-- After the first firing, the scheduler has no transition. -/
theorem once_stops (y : Conf × (once).Book) :
    ¬ (once).Transition (afterFirst, [(0, [(itemA, 0)])]) y := by
  intro transition
  cases transition with
  | move impossible => exact impossible
  | fire g admitted chosen =>
      obtain ⟨i, inProgram, noQueries, fresh, _, _⟩ := chosen
      obtain ⟨rfl, isPropagate⟩ := only_propagate inProgram
      have valid := valid_of_admits noQueries admitted
      rw [isPropagate] at valid
      have lengths := valid.take_length
      have taken : g.selection.taken = [] := List.length_eq_zero_iff.mp (by rw [← lengths]; rfl)
      have reads : List.Forall₂ (fun p (o : Occ) => p = o.1) [itemA] g.selection.read :=
        reads_match valid
      obtain ⟨o, readOne, labelled⟩ := match_one reads
      have present := read_present valid (o := o) (by simp [readOne])
      rw [afterFirst_present] at present
      have isA : o = (itemA, 0) := by
        rcases Finset.mem_insert.mp present with same | other
        · exact same
        · rw [Finset.mem_singleton.mp other] at labelled
          exact absurd labelled (by decide)
      apply fresh
      simp [heads, taken, readOne, isA]

/-- **Positive control.** The step fires the propagation rule again on the same `a`; the scheduler
fires it once and stops. -/
theorem history_stops_propagation :
    base.Admits (s := start) firstAt ∧ base.Admits (s := afterFirst) secondAt ∧
      (once).Transition (start, []) (afterFirst, [(0, [(itemA, 0)])]) ∧
      ∀ y, ¬ (once).Transition (afterFirst, [(0, [(itemA, 0)])]) y :=
  ⟨first_admitted, second_admitted, first_scheduled, once_stops⟩

open MonotoneInference MonotoneInference.Controls

/-- The scheduler over `toLeft` before `toRight`. -/
abbrev leftFirst : Scheduler base := priority [toLeft, toRight]

def leftFir : Fir := ⟨toLeft, [], leftAt⟩

theorem left_admitted : base.Admits (s := single) leftFir :=
  admits_of_valid (ground_valid (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl
    (no_checks rfl))

/-- What every scheduler state reached from `single` satisfies. -/
def Reached (x : Conf × (leftFirst).Book) : Prop :=
  (x.1 = single ∧ x.2 = []) ∨ ∀ o ∈ x.1.present, o.1 ≠ item ∧ o.1 ≠ right

theorem in_program {g : Fir} {i : ℕ} (inProgram : [toLeft, toRight][i]? = some g.rule) :
    (i = 0 ∧ g.rule = toLeft) ∨ (i = 1 ∧ g.rule = toRight) := by
  rcases i with _ | _ | i
  · exact Or.inl ⟨rfl, (Option.some.inj (show some toLeft = some g.rule from inProgram)).symm⟩
  · exact Or.inr ⟨rfl, (Option.some.inj (show some toRight = some g.rule from inProgram)).symm⟩
  · simp at inProgram

theorem reached_step {x y : Conf × (leftFirst).Book} (before : Reached x)
    (transition : (leftFirst).Transition x y) : Reached y := by
  cases transition with
  | move impossible => exact absurd impossible id
  | fire g admitted chosen =>
      obtain ⟨i, inProgram, noQueries, _, _, earlier⟩ := chosen
      have valid := valid_of_admits noQueries admitted
      have takesItem : g.rule.take = [item] := by
        rcases in_program inProgram with ⟨_, isLeft⟩ | ⟨_, isRight⟩
        · rw [isLeft]; rfl
        · rw [isRight]; rfl
      have takes := takes_match valid
      rw [takesItem] at takes
      obtain ⟨o, takenOne, labelled⟩ := match_one takes
      have present := taken_present valid (o := o) (by simp [takenOne])
      rcases before with ⟨isSingle, isEmpty⟩ | clear
      · dsimp only at isSingle isEmpty
        subst isSingle isEmpty
        rcases in_program inProgram with ⟨_, isLeft⟩ | ⟨rfl, _⟩
        · refine Or.inr fun o' member => ?_
          change o' ∈ MeTTaCalculus.OccurrenceCommits.fire single.present
            (g.selection.commit (T := Expr)) at member
          rw [MeTTaCalculus.OccurrenceCommits.mem_fire] at member
          rcases member with ⟨old, notTaken⟩ | made
          · have isItem : o' = (item, 0) := Finset.mem_singleton.mp old
            have takenItem : o = (item, 0) := Finset.mem_singleton.mp present
            exact absurd (by simp [Selection.commit, takenOne, takenItem, isItem]) notTaken
          · have produced := made_label valid (by simpa [Selection.commit] using made)
            rw [isLeft] at produced
            have isLeftLabel : o'.1 = left := List.mem_singleton.mp produced
            rw [isLeftLabel]
            exact ⟨by decide, by decide⟩
        · exact absurd left_admitted (earlier 0 (by decide) leftFir rfl rfl (by simp))
      · exact absurd labelled.symm (clear o present).1

/-- **Negative control.** The step reaches a store holding `right`; no path of the scheduler does. -/
theorem priority_incomplete :
    Relation.ReflTransGen (GroundStep choice) single afterRight ∧ right ∈ facts afterRight ∧
      ∀ y, Relation.ReflTransGen (leftFirst).Transition (single, []) y → right ∉ facts y.1 := by
  obtain ⟨_, _, toRightRun, _, _⟩ := choice_not_confluent
  refine ⟨toRightRun,
    ⟨(right, 0), made_present (r := toRight) (sel := rightAt) (C := single) (by simp [rightAt]), rfl⟩,
    fun y path => ?_⟩
  have invariant : Reached y := by
    induction path with
    | refl => exact Or.inl ⟨rfl, rfl⟩
    | tail _ transition earlier => exact reached_step earlier transition
  rintro ⟨o, present, labelled⟩
  rcases invariant with ⟨isSingle, _⟩ | clear
  · rw [isSingle] at present
    rw [Finset.mem_singleton.mp present] at labelled
    exact absurd labelled (by decide)
  · exact (clear o present).2 labelled

end RefinedScheduler.Controls

open RefinedScheduler in
#print axioms Scheduler.refines
open RefinedScheduler in
#print axioms Scheduler.sound
#print axioms RefinedScheduler.Controls.history_stops_propagation
#print axioms RefinedScheduler.Controls.priority_incomplete

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep
