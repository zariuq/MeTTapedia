import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofUseAuthority
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PublicationAuthorityControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderChecks

/-!
# Inferred dependencies, closed outputs and retained guard constraints

The interleaved publication run infers precisely its used initial theorem
occurrence. Its public copy and unrelated frame are excluded from that logical
dependency set. A second run has a closed conclusion, a retained local theorem
assumption and a guard variable absent from both. Erasing the guard's equation
store invalidates the compiled condition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofUse.Controls

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.TierZeroKernel (Derivable)
open ConstraintMultisetRewriting.Controls (signature A f initial callRule callSelection)
open PublicationAuthority.Controls
  (label protectedOccurrence kernel client system producer publicSelection publicState finalState
    the_same_producer_can_publish_publicly the_client_can_form_the_public_output
    the_kernel_rule_is_valid_after_the_public_write)

def schedule : List (ConditionalSchedule.Firing (Term signature) Nat) :=
  [(producer, publicSelection), (callRule, callSelection)]

theorem the_actual_schedule_is_executable : ConditionalSchedule.Executable A label initial schedule :=
  ⟨the_same_producer_can_publish_publicly, the_kernel_rule_is_valid_after_the_public_write,
    the_kernel_rule_is_valid_after_the_public_write.consistent⟩

theorem the_compiled_interface_preserves_the_actual_schedule :
    (ConditionalSchedule.compile label schedule).Holds A label initial :=
  (ConditionalSchedule.compile_holds_iff A label initial schedule).mpr the_actual_schedule_is_executable

theorem each_firing_has_its_actors_actual_publication_rights :
    ∀ firing ∈ schedule, ∃ actor, firing.1 ∈ (system.process actor).rules ∧
      PublicationAuthority.Formed (system.process actor).rights PublicationAuthority.Controls.location firing.2 := by
  intro firing member
  simp [schedule] at member
  rcases member with rfl | rfl
  · exact ⟨true, by simp [system, client], the_client_can_form_the_public_output⟩
  · refine ⟨false, by simp [system, kernel], ?_⟩
    intro occurrence made
    rfl

theorem the_closed_conclusion_retains_its_used_initial_assumption :
    followOrigins protectedOccurrence initialOrigins schedule 2 = {0} := by decide

theorem unrelated_frame_and_public_copy_are_not_logical_assumptions :
    1 ∉ followOrigins protectedOccurrence initialOrigins schedule 2 ∧
      3 ∉ followOrigins protectedOccurrence initialOrigins schedule 2 := by
  rw [the_closed_conclusion_retains_its_used_initial_assumption]
  decide

theorem inferred_contextual_cut (assignment : Subst signature)
    (solved : A.Models assignment finalState.equations) (replacement : Term signature → Prop)
    (supply : Derivable replacement (Provenance.Infers A label protectedOccurrence kernel.rules) (f (assignment 0))) :
    Derivable replacement (Provenance.Infers A label protectedOccurrence kernel.rules) (Term.const (σ := signature) 1) := by
  apply ProofUseAuthority.compiled_cut system A label initial schedule
    the_compiled_interface_preserves_the_actual_schedule each_firing_has_its_actors_actual_publication_rights
      assignment solved 2 (by decide) (by decide) replacement
  intro source member
  rw [the_closed_conclusion_retains_its_used_initial_assumption] at member
  have same : source = 0 := Finset.mem_singleton.mp member
  subst source
  exact supply

namespace RetainedGuard

def protectedAll (_ : Nat) : Prop := True
instance : DecidablePred protectedAll := fun _ => isTrue trivial

def label (occurrence : Nat) : Term signature := .const occurrence
def before : Configuration (Term signature) Nat := ⟨[(.var 7, .const 0)], {0, 9}⟩
def rule : RuleInstance (Term signature) := ⟨[], [.const 0], [], [.equal (.var 7) (.const 0)], [.const 2]⟩
def selected : Selection Nat := ⟨[], [0], [2]⟩
def after := selected.result label rule before
def schedule : List (ConditionalSchedule.Firing (Term signature) Nat) := [(rule, selected)]

theorem the_guarded_firing_is_valid : selected.Valid A label rule before := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · refine ⟨Subst.single 7 (.const 0), ?_⟩
    intro equation member
    have choices : equation = (Term.var (σ := signature) 7, Term.const (σ := signature) 0) ∨ equation = (.const 0, .const 0) := by
      simpa [Selection.problem, Selection.equations, before, rule, selected, label] using member
    rcases choices with rfl | rfl <;> rfl
  · intro check member assignment solved
    have only : check = Check.equal (Term.var (σ := signature) 7) (.const 0) := by simpa [rule] using member
    subst check
    exact solved (.var 7, .const 0) (by
      simp [Selection.problem, Selection.equations, before, rule, selected])

theorem the_guarded_schedule_is_executable : ConditionalSchedule.Executable A label before schedule :=
  ⟨the_guarded_firing_is_valid, the_guarded_firing_is_valid.consistent⟩

theorem the_compiled_guarded_interface_is_admitted :
    (ConditionalSchedule.compile label schedule).Holds A label before :=
  (ConditionalSchedule.compile_holds_iff A label before schedule).mpr the_guarded_schedule_is_executable

theorem the_used_local_assumption_survives_the_closed_conclusion :
    followOrigins protectedAll initialOrigins schedule 2 = {0} := by decide

theorem the_unused_local_assumption_is_not_inferred :
    9 ∉ followOrigins protectedAll initialOrigins schedule 2 := by
  rw [the_used_local_assumption_survives_the_closed_conclusion]
  decide

def erased : Configuration (Term signature) Nat := ⟨[], before.present⟩

theorem erasing_the_unseen_guard_equation_invalidates_the_firing : ¬ selected.Valid A label rule erased := by
  intro valid
  have solved : A.Models (Subst.id signature) (selected.problem label rule erased) := by
    intro equation member
    have only : equation = (Term.const (σ := signature) 0, Term.const (σ := signature) 0) := by
      simpa [Selection.problem, Selection.equations, erased, rule, selected, label] using member
    subst equation
    rfl
  have bad := valid.checks (.equal (.var 7) (.const 0)) (by simp [rule]) (Subst.id signature) solved
  change Term.var (σ := signature) 7 = Term.const (σ := signature) 0 at bad
  cases bad

theorem the_compiled_interface_cannot_erase_that_equation :
    ¬ (ConditionalSchedule.compile label schedule).Holds A label erased := by
  intro held
  have executable := (ConditionalSchedule.compile_holds_iff A label erased schedule).mp held
  exact erasing_the_unseen_guard_equation_invalidates_the_firing executable.1

theorem admitted_schedule : Admitted protectedAll [rule] schedule := by
  intro firing member
  have only := List.mem_singleton.mp member
  subst firing
  exact Or.inl (List.mem_singleton_self _)

theorem the_inferred_local_context_derives_the_closed_output (assignment : Subst signature)
    (solved : A.Models assignment after.equations) :
    Derivable (fun judgment => judgment = Term.const (σ := signature) 0)
      (Provenance.Infers A label protectedAll [rule]) (Term.const (σ := signature) 2) := by
  apply compiled_cut protectedAll A label [rule] before schedule the_compiled_guarded_interface_is_admitted
    admitted_schedule assignment solved 2 (by decide) trivial (fun judgment => judgment = Term.const (σ := signature) 0)
  intro source member
  rw [the_used_local_assumption_survives_the_closed_conclusion] at member
  have same : source = 0 := Finset.mem_singleton.mp member
  subst source
  exact Derivable.initial rfl

private theorem every_inference_retains_a_premise (premises : Multiset (Term signature)) (conclusion : Term signature)
    (inference : Provenance.Infers A label protectedAll [rule] premises conclusion) :
    ∃ premise ∈ premises, True := by
  obtain ⟨usedRule, installed, beforeState, selection, assignment, valid, _, samePremises, _⟩ := inference
  have only := List.mem_singleton.mp installed
  subst usedRule
  cases reads : selection.read with
  | nil =>
      have lengths := valid.read_length
      simp only [rule, List.length_cons, List.length_nil, reads] at lengths
      cases lengths
  | cons source rest =>
      have sourceSelected : source ∈ Provenance.premises selection protectedAll := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_union.mpr (Or.inr ?_), trivial⟩
        apply List.mem_toFinset.mpr
        rw [reads]
        exact List.mem_cons_self
      refine ⟨A.apply assignment (label source), ?_, trivial⟩
      rw [samePremises]
      exact Multiset.mem_map.mpr ⟨source, by simpa using sourceSelected, rfl⟩

private theorem no_derivation_from_no_assumptions {conclusion : Term signature}
    (proof : Derivable (fun _ => False) (Provenance.Infers A label protectedAll [rule]) conclusion) : False := by
  induction proof with
  | initial hypothesis => exact hypothesis
  | @infer premises conclusion inference _ ih =>
      obtain ⟨premise, member, _⟩ := every_inference_retains_a_premise premises conclusion inference
      exact ih premise member

theorem the_closed_output_cannot_drop_its_used_assumption :
    ¬ Derivable (fun _ => False) (Provenance.Infers A label protectedAll [rule]) (Term.const (σ := signature) 2) :=
  no_derivation_from_no_assumptions

end RetainedGuard

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofUse.Controls
