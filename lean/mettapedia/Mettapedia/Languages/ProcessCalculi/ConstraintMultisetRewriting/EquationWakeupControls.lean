import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EquationWakeups
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CheckStability
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls

/-!
# A shared row wakes a ground absence query through bindings alone

The one physical row remains present. Its shared variable is constrained by
an actual tell-only step. Every physical region has no write event, while
the original universal absence check becomes certain. Equal equation counts
in different branches do not certify equal model sets.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EquationWakeupControls

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

abbrev signature := Controls.signature
abbrev A := FirstOrder.action signature
abbrev f := Controls.f

def x : Term signature := .var 0
def zeroTerm : Term signature := .const 0
def oneTerm : Term signature := .const 1
def label (occurrence : Nat) : Term signature := if occurrence = 0 then f x else .const 2

def before : Configuration (Term signature) Nat := ⟨[], {0}⟩
def tell : RuleInstance (Term signature) := ⟨[], [], [(x, oneTerm)], [], []⟩
def tellSelection : Selection Nat := ⟨[], [], []⟩
def after : Configuration (Term signature) Nat := tellSelection.result label tell before
def pending : RuleInstance (Term signature) := ⟨[], [], [], [.absent (f zeroTerm)], [.const 2]⟩
def pendingSelection : Selection Nat := ⟨[], [], [1]⟩

theorem tell_valid : tellSelection.Valid A label tell before := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · refine ⟨Controls.one, ?_⟩
    intro equation member
    have same : equation = (x, oneTerm) := by
      simpa [Selection.problem, Selection.equations, tellSelection, tell, before] using member
    subst equation
    rfl
  · simp [tell]

theorem tell_step : Step A label tell before after := ⟨tellSelection, tell_valid, rfl⟩

theorem same_physical_world : before.present = after.present := by decide

theorem no_region_writes (region : Term signature → Bool) :
    ¬ Writes label (tellSelection.commit (T := Term signature)) region := by
  simp [Writes, Selection.commit, tellSelection]

theorem pending_cannot_fire_before : ¬ pendingSelection.Valid A label pending before := by
  intro valid
  have asked := valid.checks (.absent (f zeroTerm)) (by simp [pending])
  have holds := asked Controls.zero (by
    intro equation member
    simp [Selection.problem, Selection.equations, pendingSelection, pending, before] at member)
  exact holds 0 (by simp [before]) rfl

theorem pending_can_fire_after : pendingSelection.Valid A label pending after := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · refine ⟨Controls.one, ?_⟩
    intro equation member
    have same : equation = (x, oneTerm) := by
      simpa [Selection.problem, Selection.equations, Selection.result, pendingSelection, pending,
        after, tellSelection, tell, before] using member
    subst equation
    rfl
  · intro check member assignment solved
    have sameCheck : check = .absent (f zeroTerm) := by simpa [pending] using member
    subst check
    have value := solved (x, oneTerm) (by
      simp [Selection.problem, Selection.equations, Selection.result, pendingSelection, pending,
        after, tellSelection, tell, before])
    change assignment 0 = Term.const (σ := signature) 1 at value
    intro occurrence present equal
    have atZero : occurrence = 0 := by
      rw [← same_physical_world] at present
      simpa [before] using present
    subst occurrence
    change f zeroTerm = f (assignment 0) at equal
    have argument := congr_fun (eq_of_heq (Term.app.inj equal).2) (0 : Fin 1)
    change zeroTerm = assignment 0 at argument
    rw [value] at argument
    cases argument

theorem equation_only_wakeup :
    Step A label tell before after ∧ before.present = after.present ∧
      (∀ region, ¬ Writes label (tellSelection.commit (T := Term signature)) region) ∧
      ¬ pendingSelection.Valid A label pending before ∧
      pendingSelection.Valid A label pending after :=
  ⟨tell_step, same_physical_world, no_region_writes, pending_cannot_fire_before, pending_can_fire_after⟩

theorem physical_store_predicate_cannot_represent_readiness :
    ¬ ∃ guard : Finset Nat → Prop,
      (guard before.present ↔ pendingSelection.Valid A label pending before) ∧
      (guard after.present ↔ pendingSelection.Valid A label pending after) := by
  rintro ⟨guard, first, second⟩
  apply pending_cannot_fire_before
  apply first.mp
  rw [same_physical_world]
  exact second.mpr pending_can_fire_after

def zeroBranch : Configuration (Term signature) Nat := ⟨[(x, zeroTerm)], {0}⟩
def oneBranch : Configuration (Term signature) Nat := ⟨[(x, oneTerm)], {0}⟩

theorem equal_counts_do_not_identify_branches :
    zeroBranch.equations.length = oneBranch.equations.length ∧
      zeroBranch.present = oneBranch.present ∧
      ¬ A.Equivalent zeroBranch.equations oneBranch.equations := by
  refine ⟨rfl, rfl, ?_⟩
  intro equivalent
  have old : A.Models Controls.zero zeroBranch.equations := by
    intro equation member
    have same : equation = (x, zeroTerm) := by simpa [zeroBranch] using member
    subst equation
    rfl
  have late := (equivalent Controls.zero).mp old
  have impossible := late (x, oneTerm) (by simp [oneBranch])
  change Term.const (σ := signature) 0 = .const 1 at impossible
  cases impossible

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EquationWakeupControls
