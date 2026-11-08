import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseOccurrenceRenaming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleCutRenaming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualAtomicIdentityControls

/-!
# Renamed conditional rows retain multiplicity, pending equations and old cuts

Two physically distinct schemas carry the same latent equation and value.
Injective allocation names preserve their count; collapsing both names does
not. A computed clause retains both pending row uses and has an actual
native firing. A conflicting read and a previously false guard stay refused.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualOccurrenceRenamingControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualConditionalGuards
open ContextualSourceSchedules

namespace Counts

open ContextualPrefixPublicationControls (DataOperator base captures symbol)

abbrev localDecl (_ : Unit) : MetaArity base := ([], ())
def hole : Term (signature base localDecl) [] () := generator localDecl ()
def conditions : ContextualResidual.Problem localDecl := [(observe hole, observe (symbol 7))]
def answer : ContextualConditionalAnswers.Answer localDecl [] () := ⟨conditions, hole⟩
def row : Row localDecl captures [] () := ContextualConditionalPublication.store localDecl captures answer

theorem matches_iff {V : Type} (decl : V → MetaArity base) (candidate : Assignment captures decl)
    (pattern : Term (signature base decl) [] ()) :
    Matches localDecl captures candidate pattern row ↔ pattern = symbol 7 := by
  rw [row, ContextualConditionalPublication.store_matches_iff]
  change ContextualPublication.SourceInstances conditions hole decl pattern ↔ _
  constructor
  · rintro ⟨extension, images, model, same⟩
    have fixed := (ContextualResidual.models_observed_iff images hole (symbol 7)).mp model
    apply extension.instantiate_injective
    change instantiate extension.assignment pattern = symbol 7
    exact same.symm.trans fixed
  · rintro rfl
    refine ⟨ContextualGuardMatching.Extension.identity decl, (fun _ => symbol 7), ?_, rfl⟩
    rw [conditions, ContextualResidual.models_observed_iff]
    rfl

theorem region_full {V O : Type} (decl : V → MetaArity base) (candidate : Assignment captures decl)
    (world : Finset O) : region localDecl candidate (fun _ : O => row) world (symbol 7) = world := by
  classical
  ext occurrence
  rw [mem_region]
  change (occurrence ∈ world ∧ Matches localDecl captures candidate (symbol 7) row) ↔ occurrence ∈ world
  rw [matches_iff]
  simp

theorem two_equal_schemas_are_two_occurrences {V : Type} (decl : V → MetaArity base)
    (candidate : Assignment captures decl) :
    Holds localDecl candidate (fun _ : Nat => row) {0, 1} (.count (symbol 7) 2) := by
  rw [Holds, region_full]
  decide +kernel

theorem injective_names_keep_both {V : Type} (decl : V → MetaArity base) (candidate : Assignment captures decl)
    (cursor : OccurrenceAllocationRenaming.Cursor Nat) :
    Holds localDecl candidate (fun _ : OccurrenceAllocationRenaming.Name Nat => row)
      (({0, 1} : Finset Nat).image cursor.current) (.count (symbol 7) 2) :=
  (ContextualOccurrenceRenaming.holds_iff localDecl cursor.current cursor.injective candidate
    (fun _ : Nat => row) (fun _ => row) {0, 1} (by intro _ _; rfl) _).mpr
    (two_equal_schemas_are_two_occurrences decl candidate)

def collapse (_ : Nat) : OccurrenceAllocationRenaming.Name Nat := .inl 0

theorem collapsing_names_changes_the_count {V : Type} (decl : V → MetaArity base)
    (candidate : Assignment captures decl) :
    ¬ Holds localDecl candidate (fun _ : OccurrenceAllocationRenaming.Name Nat => row)
      (({0, 1} : Finset Nat).image collapse) (.count (symbol 7) 2) := by
  intro counted
  rw [Holds, region_full] at counted
  have size : (({0, 1} : Finset Nat).image collapse).card = 1 := by decide +kernel
  rw [size] at counted
  omega

end Counts

namespace EarlierGuard

open ContextualScheduleControls.EarlierSchema

theorem original_checks_survive : body.AllocatedCutsHold :=
  body.allocated_cuts_iff.mpr compiled_accepts.2.2.2

theorem a_later_binding_still_cannot_repair_the_old_check : ¬ guardedBody.AllocatedCutsHold := by
  intro renamed
  have cuts := guardedBody.allocated_cuts_iff.mp renamed
  have shapes : ∀ shape ∈ guardedBody.compile.shapes, shape.Holds := by
    with_unfolding_all exact compiled_accepts.1
  exact a_later_binding_does_not_repair_the_compiled_earlier_check
    ⟨shapes, the_guard_refusal_is_not_a_terminal_conflict.1,
      the_guard_refusal_is_not_a_terminal_conflict.2, cuts⟩

end EarlierGuard

namespace SourceFreshness

open ContextualPrefixPublicationControls (base none captures actor symbol firstFamily)
open ContextualAtomicIdentityControls (initial)

def code : RuleInstance (Term (signature base actor) [] ()) := ⟨[], [], [], [], [symbol 2]⟩
def plan : ContextualPublication.Plan (Term (signature base actor) [] ()) := ⟨code, [false], rfl⟩
def picked : Selection Nat := ⟨[], [], [0]⟩
def cursor : OccurrenceAllocationRenaming.Cursor Nat := .initial

theorem the_original_overwrite_is_refused : ¬ ContextualClauseSourceState.Admitted none none initial plan picked := by
  intro admitted
  have produced : (0 : Nat) ∈ picked.made.toFinset := by decide +kernel
  have present : (0 : Nat) ∈ initial.present := by decide +kernel
  exact Finset.disjoint_left.mp admitted.fresh produced present

/-- The source freshness check cannot be inferred from freshness of a renamed output. -/
theorem the_renamed_creation_is_fresh : ContextualClauseSourceState.Admitted none none
    (ContextualClauseOccurrenceRenaming.world none cursor initial) plan (cursor.rename picked) := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · refine ⟨_, firstFamily, generator firstFamily, ?_⟩
    change ContextualResidual.Models (generator firstFamily) []
    intro equation member
    cases member
  · intro check member
    cases member

end SourceFreshness

namespace ComputedClause

open ContextualClausePublication.BinderControls (DataOperator dataSignature base locals captures queries origin)
open ContextualComputedJoinControls (world plan picked)
open ContextualClauseSequencingControls (afterFirst rowLocals nextPlan selection source_next_admitted)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (result : base.Srt) : DecidableEq (base.Op result) := by
  change DecidableEq (DataOperator ⊕ Operator (SchematicReach.spaceDeclaration dataSignature () (Name := Nat)) result)
  infer_instance
local instance : DecidableEq world.Names := world.equality

def cursor : OccurrenceAllocationRenaming.Cursor Nat :=
  OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial [picked]

theorem both_reads_have_pending_conditions :
    (ContextualConditionalSourceProblem.latent captures rowLocals origin selection afterFirst.rows).length = 6 := by
  with_unfolding_all decide +kernel

theorem renaming_keeps_all_six_pending_equations :
    (ContextualConditionalSourceProblem.latent captures rowLocals origin (cursor.rename selection)
      (fun physical => afterFirst.rows (OccurrenceAllocationRenaming.erase physical))).length = 6 := by
  erw [ContextualClauseOccurrenceRenaming.latent_conditions captures rowLocals afterFirst.declarations
    cursor selection afterFirst.rows]
  exact both_reads_have_pending_conditions

theorem the_pending_clause_has_an_actual_renamed_firing (fuel : Nat) :
    ∃ compiled : ContextualConditionalClauses.Compiled captures rowLocals
      (before := (ContextualClauseOccurrenceRenaming.world rowLocals cursor afterFirst).native ∅)
      nextPlan (cursor.rename selection), compiled.firing.fuel = fuel ∧
      ∀ (Next : Type) (next : Next → MetaArity base)
        (candidate : Assignment compiled.firing.target.declarations next) (pattern : SchematicReach.Closed next),
        Matches (ContextualClauseSourceState.resultLocals captures rowLocals afterFirst)
          (ContextualClauseSourceState.resultFamily captures rowLocals afterFirst)
          (Assignment.compose candidate compiled.sourceFrame.assignment) pattern
          ((ContextualClauseSourceState.target captures rowLocals afterFirst nextPlan selection).rows 5) ↔
        Matches (ContextualPublication.privateFamily (ContextualClauseFrames.bank captures rowLocals) compiled.firing.update.declaration)
          compiled.firing.target.declarations candidate pattern
          (compiled.firing.target.rows ((cursor.advance selection).current 5)) := by
  obtain ⟨compiled, budget⟩ := ContextualClauseOccurrenceRenaming.realize cursor afterFirst captures nextPlan selection
    source_next_admitted ∅ fuel
  refine ⟨compiled, budget, ?_⟩
  intro Next next candidate pattern
  exact ContextualClauseOccurrenceRenaming.all_row_observations cursor afterFirst captures nextPlan selection
    source_next_admitted ∅ compiled 5 next candidate pattern

theorem the_conflicting_renamed_clause_still_cannot_fire :
    ¬ Nonempty (ContextualConditionalClauses.Compiled captures rowLocals
      (before := (ContextualClauseOccurrenceRenaming.world rowLocals cursor afterFirst).native ∅)
      ContextualClauseSequencingControls.conflictingPlan (cursor.rename selection)) := by
  rintro ⟨compiled⟩
  apply ContextualClauseSequencingControls.a_conflicting_second_read_cannot_fire
  exact (ContextualClauseOccurrenceRenaming.admitted_iff cursor afterFirst captures
    ContextualClauseSequencingControls.conflictingPlan selection).mpr
    ⟨source_next_admitted.fresh, compiled.source_admitted⟩

end ComputedClause

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualOccurrenceRenamingControls
