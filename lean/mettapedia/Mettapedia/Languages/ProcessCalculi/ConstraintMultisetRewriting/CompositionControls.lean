import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ConditionalComposition
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SafetyControls

/-!
# A later binding cannot discharge an earlier blocking guard retroactively

These are state guards (asks). A language may separately retain a type
obligation on a conditional answer; that policy is not identified with
executing a rule whose blocking precondition has not been established.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CompositionControls

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (fire)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls
  (signature A zero one label)

def noneSelected : Selection Nat := ⟨[], [], []⟩
def emptyState : Configuration (Term signature) Nat := ⟨[], ∅⟩

def earlyGuard : RuleInstance (Term signature) :=
  ⟨[], [], [], [.equal (.var 0) (.const 0)], []⟩

def laterBinding : RuleInstance (Term signature) :=
  ⟨[], [], [(.var 0, .const 0)], [], []⟩

def guardedPair : ConditionalComposite (Term signature) Nat :=
  ConditionalComposite.compilePair label earlyGuard laterBinding noneSelected noneSelected

theorem final_equations_are_consistent : A.Consistent guardedPair.equations := by
  refine ⟨zero, ?_⟩
  intro equation member
  have same : equation = (Term.var (σ := signature) 0, Term.const (σ := signature) 0) := by
    simpa [guardedPair, ConditionalComposite.compilePair, ConditionalComposite.addedEquations,
      earlyGuard, laterBinding, noneSelected, Selection.equations] using member
  subst equation
  rfl

theorem final_equations_do_establish_the_guard : A.Entails guardedPair.equations
    (fun σ => (Check.equal (.var 0) (.const 0)).Holds A σ label ∅) := by
  intro σ model
  exact model (.var 0, .const 0) (by
    simp [guardedPair, ConditionalComposite.compilePair, ConditionalComposite.addedEquations,
      earlyGuard, laterBinding, noneSelected, Selection.equations])

/-- Evaluating every guard only in the final constraints would add behavior. -/
theorem original_guard_prefix_is_retained : ¬ guardedPair.Holds A label emptyState := by
  intro admitted
  obtain ⟨first, _⟩ :=
    (ConditionalComposite.holds_pair_iff A label earlyGuard laterBinding
      noneSelected noneSelected emptyState).mp admitted
  have incorrect := first.checks (.equal (.var 0) (.const 0)) (by simp [earlyGuard]) one
    (A.models_nil one)
  change (Term.const (σ := signature) 1) = .const 0 at incorrect
  cases incorrect

def consume : RuleInstance (Term signature) := ⟨[.const 0], [], [], [], []⟩
def checkAbsent : RuleInstance (Term signature) := ⟨[], [], [], [.absent (.const 0)], []⟩
def consumeThree : Selection Nat := ⟨[3], [], []⟩
def oneBlocker : Configuration (Term signature) Nat := ⟨[], {3}⟩

theorem consume_valid : consumeThree.Valid A Controls.blockerLabel consume oneBlocker := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · refine ⟨zero, ?_⟩
    intro equation member
    have same : equation = (Term.const (σ := signature) 0, Term.const (σ := signature) 0) := by
      simpa [Selection.problem, Selection.equations, consumeThree, consume, oneBlocker,
        Controls.blockerLabel] using member
    subst equation
    rfl
  · simp [consume]

theorem absence_valid_after_consume : noneSelected.Valid A Controls.blockerLabel checkAbsent
    (consumeThree.result Controls.blockerLabel consume oneBlocker) := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · exact consume_valid.consistent
  · intro check member σ model
    have same : check = Check.absent (.const (σ := signature) 0) := by simpa [checkAbsent] using member
    subst check
    intro o inWorld
    simp [Selection.result, fire, Selection.commit, consumeThree, oneBlocker] at inWorld

theorem absence_pair_is_admitted :
    (ConditionalComposite.compilePair Controls.blockerLabel consume checkAbsent
      consumeThree noneSelected).Holds A Controls.blockerLabel oneBlocker :=
  (ConditionalComposite.holds_pair_iff A Controls.blockerLabel consume checkAbsent
    consumeThree noneSelected oneBlocker).mpr ⟨consume_valid, absence_valid_after_consume⟩

theorem absence_pair_reaches_the_same_configuration :
    (ConditionalComposite.compilePair Controls.blockerLabel consume checkAbsent
      consumeThree noneSelected).result oneBlocker =
      noneSelected.result Controls.blockerLabel checkAbsent
        (consumeThree.result Controls.blockerLabel consume oneBlocker) :=
  ConditionalComposite.result_pair A Controls.blockerLabel consume checkAbsent
    consumeThree noneSelected oneBlocker absence_pair_is_admitted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CompositionControls
