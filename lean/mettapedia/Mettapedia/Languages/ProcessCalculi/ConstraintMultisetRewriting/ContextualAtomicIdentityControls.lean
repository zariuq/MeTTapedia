import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleCompilation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleAllocation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixPublicationControls

/-!
# A recycled source identity is not a fresh single-firing output

A selected private body consumes occurrence 0 carrying symbol 1 and later
uses 0 for a newly produced symbol 2. Both source steps are admitted.
Every existing single conditional firing from the original state must
retain the old row meaning at 0 whenever that identity is observed.

Thus atomic assembly with exact numeric identities needs either a lifetime
representation or an explicit stronger allocation contract. The finite
resource-set summary alone does not identify these two row histories.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualAtomicIdentityControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualSourceSchedules
open ContextualPrefixPublicationControls (DataOperator base none captures actor symbol firstFamily)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq DataOperator)

abbrev initial : ContextualClauseSourceState.World none Nat [] () :=
  ⟨Unit, inferInstance, captures, [], {0}, fun _ => ofStored none captures (.shared (symbol 1))⟩

def consumeCode : RuleInstance (Term (signature base actor) [] ()) := ⟨[symbol 1], [], [], [], []⟩
def consumePlan : ContextualPublication.Plan (Term (signature base actor) [] ()) := ⟨consumeCode, [], rfl⟩
def consumed : Selection Nat := ⟨[0], [], []⟩
abbrev middle := ContextualClauseSourceState.target none none initial consumePlan consumed
abbrev middleLocals := ContextualClauseSourceState.resultLocals none none initial

def produceCode : RuleInstance (Term (signature base (queryFamily none firstFamily)) [] ()) :=
  ⟨[], [], [], [], [symbol 2]⟩
def producePlan : ContextualPublication.Plan (Term (signature base (queryFamily none firstFamily)) [] ()) :=
  ⟨produceCode, [false], rfl⟩
def recycled : Selection Nat := ⟨[], [], [0]⟩
abbrev final := ContextualClauseSourceState.target none middleLocals middle producePlan recycled
abbrev finalLocals := ContextualClauseSourceState.resultLocals none middleLocals middle

theorem consume_information :
    ContextualClauseSourceState.information none none initial consumePlan consumed =
      [(observe (symbol 1), observe (symbol 1))] := by
  with_unfolding_all rfl

theorem consume_admitted : ContextualClauseSourceState.Admitted none none initial consumePlan consumed := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · refine ⟨_, firstFamily, generator firstFamily, ?_⟩
    change ContextualResidual.Models (generator firstFamily)
      (ContextualClauseSourceState.information none none initial consumePlan consumed)
    erw [consume_information, ContextualResidual.models_observed_iff]
  · intro check member
    cases member

theorem produce_information :
    ContextualClauseSourceState.information none middleLocals middle producePlan recycled =
      [(observe (symbol 1), observe (symbol 1))] := by
  with_unfolding_all rfl

theorem produce_admitted : ContextualClauseSourceState.Admitted none middleLocals middle producePlan recycled := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · refine ⟨_, final.declarations, generator final.declarations, ?_⟩
    change ContextualResidual.Models (generator final.declarations)
      (ContextualClauseSourceState.information none middleLocals middle producePlan recycled)
    erw [produce_information, ContextualResidual.models_observed_iff]
  · intro check member
    cases member

def body : Schedule base Nat [] () initial final :=
  .snoc (.snoc (.nil initial) none consumePlan consumed) none producePlan recycled

theorem admitted_body : body.Admitted := by
  have consistent := (Schedule.snoc (Schedule.nil initial) none consumePlan consumed).source_solvable consume_admitted.solvable
  exact ⟨⟨consistent, consume_admitted⟩, produce_admitted⟩

theorem compiled_accepts : body.compile.Holds initial.present := body.compile_exact.mpr admitted_body

theorem the_net_resource_set_is_unchanged : final.present = initial.present := by decide +kernel

theorem source_row_is_two {V : Type} (decl : V → MetaArity base)
    (candidate : Assignment final.declarations decl) :
    Matches finalLocals final.declarations candidate (symbol 2) (final.rows 0) := by
  have row := ContextualClauseSourceState.shared_output_row produce_admitted ⟨0, by decide +kernel⟩ rfl
  change final.rows 0 = _ at row
  rw [row]
  apply (ofStored_matches_iff _ _ candidate _ _).mpr
  rfl

/-- An existing native firing cannot overwrite an entry occurrence with a fresh output. -/
theorem every_single_firing_keeps_the_old_row_at_zero
    (firing : ContextualConditionalExecution.Firing none (initial.native ∅))
    {V : Type} (decl : V → MetaArity base) (candidate : Assignment firing.target.declarations decl) :
    ¬ Matches (ContextualPublication.privateFamily none firing.update.declaration)
      firing.target.declarations candidate (symbol 2) (firing.target.rows 0) := by
  intro matched
  have notMade : 0 ∉ firing.selection.made := by
    intro made
    exact Finset.disjoint_left.mp firing.admitted.fresh
      (by simpa only [List.mem_toFinset] using made) (by decide +kernel)
  have original := (firing.retained_matches 0 notMade decl candidate (symbol 2)).mp matched
  obtain ⟨extension, images, _conditions, same⟩ := original
  change symbol (decl := extension.declarations) 1 = symbol 2 at same
  have impossible : (1 : Nat) = 2 := DataOperator.symbol.inj (Sum.inl.inj (Term.op.inj same).1)
  omega

def freshSelection : Selection Nat := ⟨[0], [], [1]⟩
def fusedRule : RuleInstance (Term (signature base (ContextualActivatedStep.source none captures)) [] ()) :=
  ⟨[symbol 1], [], [], [], [symbol 2]⟩
def fusedOutputs (_ : Nat) : Term (signature base (ContextualActivatedStep.target none captures)) [] () := symbol 2

theorem fused_information :
    ContextualConditionalExecution.information none captures ∅ freshSelection fusedRule initial.rows [] =
      [(observe (symbol 1), observe (symbol 1))] := by
  with_unfolding_all rfl

theorem fresh_native_admission : ContextualConditionalExecution.Admitted none
    (initial.native ∅) fusedRule freshSelection fusedOutputs := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, ?_,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · with_unfolding_all rfl
  · refine ⟨_, ContextualActivatedStep.target none captures,
      generator (ContextualActivatedStep.target none captures), ?_⟩
    change ContextualResidual.Models _
      (ContextualConditionalExecution.information none captures ∅ freshSelection fusedRule initial.rows [])
    erw [fused_information, ContextualResidual.models_observed_iff]
  · intro check member
    cases member

/-- Renaming only the new creation gives an actual existing firing at every solver budget. -/
theorem fresh_name_repair (fuel : Nat) :
    ∃ firing : ContextualConditionalExecution.Firing none (initial.native ∅),
      firing.fuel = fuel ∧ firing.target.present = {1} ∧
      ∀ (V : Type) (decl : V → MetaArity base) (candidate : Assignment firing.target.declarations decl)
        (pattern : Term (signature base decl) [] ()),
        Matches (ContextualPublication.privateFamily none firing.update.declaration)
          firing.target.declarations candidate pattern (firing.target.rows 1) ↔ pattern = symbol 2 := by
  obtain ⟨firing, _rule, selected, outputs, kinds, budget⟩ :=
    ContextualConditionalExecution.realize_at_fuel none (initial.native ∅) fusedRule freshSelection
      fusedOutputs (fun _ => false) fresh_native_admission fuel
  refine ⟨firing, budget, ?_, ?_⟩
  · rw [firing.physical_result, selected]
    decide +kernel
  · intro V decl candidate pattern
    have made : 1 ∈ firing.selection.made := by rw [selected]; decide +kernel
    have isShared : firing.reusable 1 = false := by rw [kinds]
    rw [firing.shared_row 1 made isShared, outputs]
    change Matches _ _ candidate pattern (ofStored _ _ (.shared (symbol 2))) ↔ _
    rw [ofStored_matches_iff, ContextualGuardMatching.shared_matches_iff]
    rfl

theorem source_row_instances {V : Type} (decl : V → MetaArity base)
    (candidate : Assignment final.declarations decl) (pattern : Term (signature base decl) [] ()) :
    Matches finalLocals final.declarations candidate pattern (final.rows 0) ↔ pattern = symbol 2 := by
  have row := ContextualClauseSourceState.shared_output_row produce_admitted ⟨0, by decide +kernel⟩ rfl
  change final.rows 0 = _ at row
  rw [row, ofStored_matches_iff, ContextualGuardMatching.shared_matches_iff]
  rfl

def renamedNet : MeTTaCalculus.OccurrenceCommits.Commit (OccurrenceAllocationRenaming.Name Nat) Unit :=
  (MeTTaCalculus.OccurrenceCommits.CompiledSchedule.compile OccurrenceAllocationRenaming.label
    (OccurrenceAllocationRenaming.commits body.allocated)).effect

/-- The original set summary loses the replacement, while bound allocation names retain it. -/
theorem allocation_names_keep_the_resource_replacement :
    body.compile.resources.effect.taken = ∅ ∧ body.compile.resources.effect.made = ∅ ∧
      renamedNet.taken = {Sum.inl 0} ∧ renamedNet.made = {Sum.inr (1, 0)} := by
  decide +kernel

theorem allocated_trace_keeps_the_source_choices :
    body.allocated.map OccurrenceAllocationRenaming.project = [consumed, recycled] :=
  body.allocated_trace

theorem allocated_net_keeps_the_source_result :
    MeTTaCalculus.OccurrenceCommits.Enabled OccurrenceAllocationRenaming.label {Sum.inl 0} renamedNet ∧
      (MeTTaCalculus.OccurrenceCommits.fire {Sum.inl 0} renamedNet).image OccurrenceAllocationRenaming.erase = {0} := by
  exact body.allocated_net_commit compiled_accepts

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualAtomicIdentityControls
