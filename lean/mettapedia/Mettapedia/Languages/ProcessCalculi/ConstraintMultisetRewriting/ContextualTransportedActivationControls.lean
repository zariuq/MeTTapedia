import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTransportedActivation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedStepControls

/-!
# Fresh helpers supply a model absent from the original endomorphic frame

With no rigid constructors and only a binary declaration, a swapped-spine
equation has no endomorphic model: a solution would require a closed term.
The actual worklist introduces a nullary helper and completes the guarded
activation in its explicit extended frame. An unjustified guard still
cannot manufacture the equality it asks for.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTransportedActivationControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualResidual
open ContextualTransportedActivation

def base : Signature where
  Srt := Unit
  Op _ := Empty
  arity operator := nomatch operator

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq Empty)

def locals : Empty → MetaArity base := fun impossible => nomatch impossible
def captures (_ : Unit) : MetaArity base := ([(), ()], ())
abbrev raw := ContextualActivatedStep.source locals captures
abbrev active := ContextualActivatedStep.target locals captures
abbrev RawTerm := Term (signature base raw) [(), ()] ()
abbrev ActiveTerm := Term (signature base active) [(), ()] ()

def identityMap : Ren base [(), ()] [(), ()] := fun _ position => position
def swap : Ren base [(), ()] [(), ()]
  | _, .zero => .succ .zero
  | _, .succ .zero => .zero

def rawFormal : RawTerm := generator raw (.inr ())
def rawSwapped : RawTerm := rename (S := signature base raw) swap rawFormal
def formal : ActiveTerm := generator active (.inr ())
def swapped : ActiveTerm := rename (S := signature base active) swap formal

def occupied : Finset Nat := {0, 2}
def selection : Selection Nat := ⟨[], [], []⟩
def rule : RuleInstance RawTerm := ⟨[], [], [(rawFormal, rawSwapped)], [.equal rawFormal rawSwapped], []⟩
def rows (_ : Nat) : ContextualStoredRows.Row locals captures [(), ()] () := .shared (.var .zero)
def before : Configuration (Term (signature base captures) [(), ()] ()) Nat := ⟨[], ∅⟩
def outputs (_ : Nat) : ActiveTerm := .var .zero
def problem := ContextualActivatedStep.problem locals captures occupied selection rule rows before

theorem the_actual_prepared_problem_is_the_swapped_equation : problem = [(formal, swapped)] := by
  with_unfolding_all rfl

theorem physical_and_guard_admission_does_not_supply_a_model :
    ContextualGuardedStep.Requirements locals captures occupied selection rule rows before outputs := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ?_⟩
  intro check member
  have only : check = .equal formal swapped := List.mem_singleton.mp member
  subst check
  apply ContextualGuardSemantics.Ask.equal_of_mem locals
  exact List.mem_singleton_self _

theorem the_original_frame_has_no_closed_term : ∀ _term : Term (signature base active) [] (), False
  | .var impossible => nomatch impossible
  | .op (.inl impossible) _ => nomatch impossible
  | .op (.inr (.mk (.inl ⟨_, impossible⟩))) _ => nomatch impossible
  | .op (.inr (.mk (.inr ()))) (.cons first (.cons _ .nil)) => the_original_frame_has_no_closed_term first
termination_by term => termSize term
decreasing_by simp only [termSize, argsSize]; omega

theorem the_original_endomorphic_equation_has_no_model (candidate : Assignment active active) :
    ¬ ContextualFrameUnifier.Models candidate problem := by
  intro solved
  let update := ContextualNamedSelfPair.apply (S := base) active (.inr ()) identityMap swap []
  have modeled : Models candidate
      [(observe (rename (S := signature base active) identityMap (generator active (.inr ()))),
        observe (rename (S := signature base active) swap (generator active (.inr ()))))] := by
    apply (models_observed_iff (S := base) (source := active) candidate _ _).mpr
    have equation := solved _ (by rw [the_actual_prepared_problem_is_the_swapped_equation]; exact List.mem_singleton_self _)
    change instantiate candidate (rename (S := signature base active) identityMap formal) = instantiate candidate swapped
    have identity : rename (S := signature base active) identityMap formal = formal := by with_unfolding_all rfl
    rw [identity]
    exact equation
  obtain ⟨residual, _, _⟩ := update.valid.complete active candidate modeled
  have closed := residual (.inl ())
  have emptyContext : (ScopeEqualizer.Finite.build (S := base) identityMap swap).context = [] := by
    with_unfolding_all rfl
  change Term (signature base active) (ScopeEqualizer.Finite.build (S := base) identityMap swap).context () at closed
  rw [emptyContext] at closed
  exact the_original_frame_has_no_closed_term closed

theorem the_original_small_frame_is_inconsistent :
    ¬ (ContextualFamilies.action active [(), ()] ()).Consistent problem := by
  rintro ⟨candidate, solved⟩
  exact the_original_endomorphic_equation_has_no_model candidate solved

def helpers (_ : Unit) : MetaArity base := ([], ())
def helperModel : Assignment active helpers
  | .inl ⟨_, impossible⟩ => nomatch impossible
  | .inr () => .op (.inr (.mk ())) .nil

theorem a_later_helper_supplies_an_independent_model : Models helperModel (observeProblem problem) := by
  apply (models_observeProblem (S := base) (source := active) helperModel problem).mpr
  intro equation member
  rw [the_actual_prepared_problem_is_the_swapped_equation] at member
  have only := List.mem_singleton.mp member
  subst equation
  with_unfolding_all rfl

def pending {equations : Problem active} : ContextualFrameWorklist.Result equations → Option Nat
  | .refuted _ => none
  | .residual update => some update.remaining.length

theorem the_actual_worklist_finishes_using_its_fresh_helper :
    pending (ContextualFrameWorklist.run (S := base) 1 active (observeProblem problem)) = some 0 := by
  rw [ContextualFrameWorklist.run_eq_local_on_model 1 (observeProblem problem) helpers helperModel
    a_later_helper_supplies_an_independent_model]
  decide +kernel

theorem the_actual_guarded_activation_has_a_genuine_consistent_helper_frame :
    ∃ update, FromRun locals captures 1 occupied selection rule rows before outputs update ∧
      (ContextualFamilies.action (ContextualComputedFreshFrame.active active update.declaration) [(), ()] ()).Consistent
        (ContextualTransportedActivation.result locals captures (ContextualComputedFreshFrame.includeSource update)
          occupied selection rule rows before).equations := by
  have count := the_actual_worklist_finishes_using_its_fresh_helper
  cases computed : ContextualFrameWorklist.run (S := base) 1 active (observeProblem problem) with
  | refuted impossible => simp only [computed, pending, reduceCtorEq] at count
  | residual update =>
      have empty : update.remaining = [] := by
        simpa only [computed, pending, Option.some.injEq, List.length_eq_zero_iff] using count
      have formed := from_run locals captures physical_and_guard_admission_does_not_supply_a_model update computed empty
      exact ⟨update, formed, formed.valid.consistent⟩

theorem an_unjustified_guard_still_has_no_admission :
    ¬ ContextualGuardedStep.Requirements ContextualSelectionViews.Controls.locals ContextualSelectionViews.Controls.captures
      ContextualGuardedStep.Controls.occupied ContextualGuardedStep.Controls.selection
      ContextualGuardedStep.Controls.equalityRule ContextualGuardedStep.Controls.rows
      ContextualGuardedStep.Controls.bare ContextualGuardedStep.Controls.outputs := by
  intro admitted
  apply ContextualGuardedStep.Controls.an_unjustified_equality_guard_refuses_even_with_a_closed_output
  refine ⟨admitted, ?_⟩
  exact ContextualFrameUnifier.solvable_of_consistent
    ⟨generator _, fun _ member => False.elim (List.not_mem_nil member)⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTransportedActivationControls
