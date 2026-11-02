import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingWorklist
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameControls

/-!
# Executed worklist controls for open contextual equations

The queue can bind a swapped spine and then a closed hole. It can also skip
an initially unrecoverable repeated spine, solve a later equation and return
to discharge the first one. A repeated or compound application by itself
remains explicit. Rigid conflicts are refuted; an undeclared ambient capture
does not get admitted by the binding pass.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingWorklist.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual

abbrev base := ContextualFrame.Controls.signature
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)
def declaration (identity : Bool) : MetaArity base := if identity then ([], ()) else ([(), ()], ())
abbrev extended := signature base declaration
private def extendedOperators : (sort : extended.Srt) → DecidableEq (extended.Op sort) := fun sort =>
  inferInstanceAs (DecidableEq (base.Op sort ⊕ ContextualFamily.Operator (S := base) declaration sort))

def constant {Γ : Ctx base} : Term extended Γ () := .op (.inl .constant) .nil
def call {Γ : Ctx base} (first second : Term extended Γ ()) : Term extended Γ () :=
  .op (.inr (.mk false)) (.cons first (.cons second .nil))
def closed {Γ : Ctx base} : Term extended Γ () := .op (.inr (.mk true)) .nil

def pendingCount {problem : Problem declaration} : Result problem → Option Nat
  | .residual update => some update.remaining.length
  | .refuted _ => none

def image? {problem : Problem declaration} (result : Result problem) (identity : Bool) :
    Option (Term extended (declaration identity).1 (declaration identity).2) :=
  match result with
  | .residual update => some (update.answer identity)
  | .refuted _ => none

def swappedProblem : Problem declaration :=
  [(observe (call (Γ := [(), ()]) (.var (.succ .zero)) (.var .zero)), observe (Term.var (S := extended) (.zero : Var [(), ()] ()))),
   (observe (closed (Γ := [])), observe (constant (Γ := [])))]

theorem the_swapped_and_closed_equations_finish : pendingCount (run 3 swappedProblem) = some 0 := by decide +kernel

theorem the_computed_open_image_uses_the_swapped_formal_parameter :
    image? (run 3 swappedProblem) false = some (.var (.succ .zero)) := by decide +kernel

theorem the_computed_closed_image_is_the_ground_constructor :
    image? (run 3 swappedProblem) true = some (constant (Γ := [])) := by
  let verdict : Decidable (image? (run 3 swappedProblem) true = some (constant (Γ := []))) :=
    @Option.instDecidableEq (Term extended [] ()) (@decEqTerm extended extendedOperators [] ())
      (image? (run 3 swappedProblem) true) (some constant)
  exact @of_decide_eq_true _ verdict (by decide +kernel)

theorem the_executed_answer_solves_every_original_equation :
    ∃ update, run 3 swappedProblem = .residual update ∧ update.remaining = [] ∧ Models update.answer swappedProblem := by
  have count := the_swapped_and_closed_equations_finish
  generalize computed : run 3 swappedProblem = result at count
  cases result with
  | refuted proof => cases count
  | residual update =>
      have empty : update.remaining = [] := by simpa using (Option.some.inj count)
      exact ⟨update, rfl, empty, completed_sound update empty⟩

def repeatedProblem : Problem declaration :=
  [(observe (call (Γ := [()]) (.var .zero) (.var .zero)), observe (Term.var (S := extended) (.zero : Var [()] ())))]

theorem repetition_does_not_get_a_false_unique_binding : pendingCount (run 3 repeatedProblem) = some 1 := by decide +kernel

def compoundProblem : Problem declaration :=
  [(observe (call (constant (Γ := [])) constant), observe (constant (Γ := [])))]

theorem compound_arguments_stay_available_as_residual_syntax : pendingCount (run 3 compoundProblem) = some 1 := by decide +kernel

def captureProblem : Problem declaration :=
  [(observe (call (Γ := [(), (), ()]) (.var (.succ .zero)) (.var (.succ (.succ .zero)))),
    observe (Term.var (S := extended) (.zero : Var [(), (), ()] ())))]

theorem an_undeclared_ambient_variable_is_not_captured : pendingCount (run 3 captureProblem) = some 1 := by decide +kernel

def unblockProblem : Problem declaration :=
  [(observe (call (Γ := [(), ()]) (.var .zero) (.var .zero)), observe (closed (Γ := [(), ()]))),
   (observe (call (Γ := [(), ()]) (.var .zero) (.var (.succ .zero))), observe (constant (Γ := [(), ()])))]

theorem a_later_binding_unblocks_the_initial_repeated_spine : pendingCount (run 4 unblockProblem) = some 0 := by decide +kernel

theorem the_unblocked_answer_actually_binds_both_holes :
    image? (run 4 unblockProblem) false = some (constant (Γ := [(), ()])) ∧
    image? (run 4 unblockProblem) true = some (constant (Γ := [])) := by
  constructor
  · let verdict : Decidable (image? (run 4 unblockProblem) false = some (constant (Γ := [(), ()]))) :=
      @Option.instDecidableEq (Term extended [(), ()] ()) (@decEqTerm extended extendedOperators [(), ()] ())
        (image? (run 4 unblockProblem) false) (some constant)
    exact @of_decide_eq_true _ verdict (by decide +kernel)
  · let verdict : Decidable (image? (run 4 unblockProblem) true = some (constant (Γ := []))) :=
      @Option.instDecidableEq (Term extended [] ()) (@decEqTerm extended extendedOperators [] ())
        (image? (run 4 unblockProblem) true) (some constant)
    exact @of_decide_eq_true _ verdict (by decide +kernel)

def conflictProblem : Problem declaration :=
  [(observe (closed (Γ := [])), observe (constant (Γ := []))),
   (observe (closed (Γ := [])), observe (Term.op (S := extended) (Γ := []) (s := ()) (.inl .pair) (.cons constant (.cons constant .nil))))]

theorem conflicting_uses_of_the_same_hole_are_refuted : pendingCount (run 3 conflictProblem) = none := by decide +kernel

theorem the_conflict_refutes_models_in_every_later_frame {Next : Type} (next : Next → MetaArity base)
    (candidate : Assignment declaration next) : ¬ Models candidate conflictProblem := by
  have count := conflicting_uses_of_the_same_hole_are_refuted
  generalize computed : run 3 conflictProblem = result at count
  cases result with
  | refuted proof => exact proof next candidate
  | residual update => cases count

theorem no_fuel_retains_the_whole_original_queue : pendingCount (run 0 swappedProblem) = some 2 := rfl

theorem one_pass_retains_the_still_unsolved_closed_equation : pendingCount (run 1 swappedProblem) = some 1 := by decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingWorklist.Controls
