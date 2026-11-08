import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalClauses
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReachControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutationNames

/-!
# A pending value is published, read with its equation, and consumed atomically

The producer has not spent a solver step: x = 1 is still pending. Its
published row keeps that equation with x. A later take of 1 opens both in
one fresh row frame and can publish 7. Taking 2 cannot be admitted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalExecution.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching ContextualConditionalRows
open SchematicReach.Controls (spaceSignature DataOperator symbol)

abbrev base := spaceSignature
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := by
  change DecidableEq (DataOperator ⊕ Operator (SchematicReach.spaceDeclaration
    SchematicReach.Controls.dataSignature () (Name := Nat)) sort)
  infer_instance

abbrev locals (_ : Nat) : MetaArity base := ([], ())
abbrev queries (_ : Nat) : MetaArity base := ([], ())
abbrev captures (_ : Nat) : MetaArity base := ([], ())
abbrev raw := ContextualActivatedStep.source locals captures
abbrev active := ContextualActivatedStep.target locals captures
def x : SchematicReach.Closed captures := generator captures 0

def constantAt {V : Type} (decl : V → MetaArity base) (number : Nat) (arity : MetaArity base) :
    Term (signature base decl) arity.1 arity.2 := .op (.inl (.inl (.symbol number))) .nil

def firstModel : Assignment active captures := fun name => constantAt captures 1 (active name)

def before : State locals Nat [] () where
  Names := Nat
  equality := inferInstance
  declarations := captures
  occupied := ∅
  equations := [(observe x, observe (symbol 1))]
  present := ∅
  rows _ := ofStored locals captures (.shared x)

def rule : RuleInstance (SchematicReach.Closed raw) :=
  ⟨[], [], [], [], [generator raw (.inr 0)]⟩
def selected : Selection Nat := ⟨[], [], [1]⟩
def outputs (_ : Nat) : SchematicReach.Closed active := generator active (.inr 0)
def problem := information locals captures ∅ selected rule before.rows before.equations

theorem problem_explicit : problem = [(observe (generator active (.inr 0)), observe (symbol 1))] := by
  with_unfolding_all rfl

theorem source_admitted : Admitted locals before rule selected outputs := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, ?_,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    ⟨Nat, captures, firstModel, ?_⟩, ?_⟩
  · with_unfolding_all rfl
  · change ContextualResidual.Models firstModel problem
    rw [problem_explicit]
    apply (ContextualResidual.models_observed_iff _ _ _).mpr
    rw [instantiate_generator]
    rfl
  · intro check member
    cases member

def update := ContextualFrameWorklist.identity problem
def producer : Firing locals before :=
  ⟨rule, selected, outputs, (fun _ => true), source_admitted, 0, update, rfl⟩

theorem the_generic_constructor_accepts_zero_fuel :
    ∃ firing : Firing locals before, firing.rule = rule ∧ firing.selection = selected ∧
      firing.outputs = outputs ∧ firing.reusable = (fun _ => true) ∧ firing.fuel = 0 :=
  realize_at_fuel locals before rule selected outputs (fun _ => true) source_admitted 0

theorem publication_has_a_real_pending_equation :
    producer.update.remaining.length = 1 ∧ producer.target.present = {1} := by
  exact ⟨rfl, rfl⟩

private theorem instantiate_symbol {V Next : Type} {decl : V → MetaArity base} {next : Next → MetaArity base}
    (assignment : Assignment decl next) (number : Nat) : instantiate assignment (symbol number) = symbol number := rfl

theorem the_stored_conditional_row_accepts_one
    {Next : Type} (next : Next → MetaArity base) (candidate : Assignment producer.target.declarations next) :
    Matches (ContextualPublication.privateFamily locals producer.update.declaration) producer.target.declarations
      candidate (symbol 1) (producer.target.rows 1) := by
  apply (producer.ordinary_matches_source 1 (by decide +kernel) rfl next candidate (symbol 1)).mpr
  refine ⟨Extension.identity next, (fun name => constantAt next 1 (active name)), ?_, ?_⟩
  · change ContextualResidual.Models (fun name => constantAt next 1 (active name)) problem
    rw [problem_explicit]
    apply (ContextualResidual.models_observed_iff _ _ _).mpr
    rw [instantiate_generator]
    rfl
  · change instantiate (fun name => constantAt next 1 (active name)) (generator active (.inr 0)) =
      instantiate (Extension.identity next).assignment (symbol 1)
    rw [instantiate_generator]
    rfl

theorem the_stored_conditional_row_rejects_two
    {Next : Type} (next : Next → MetaArity base) (candidate : Assignment producer.target.declarations next) :
    ¬ Matches (ContextualPublication.privateFamily locals producer.update.declaration) producer.target.declarations
      candidate (symbol 2) (producer.target.rows 1) := by
  intro matched
  obtain ⟨extension, images, model, same⟩ :=
    (producer.ordinary_matches_source 1 (by decide +kernel) rfl next candidate (symbol 2)).mp matched
  change ContextualResidual.Models images problem at model
  rw [problem_explicit] at model
  have required := (ContextualResidual.models_observed_iff images _ _).mp model
  change instantiate images (generator active (.inr 0)) = instantiate extension.assignment (symbol 2) at same
  erw [instantiate_generator, instantiate_symbol] at required same
  have impossible : (1 : Nat) = 2 := SchematicReach.Controls.symbol_injective (required.symm.trans same)
  omega

/-- Guards use the row conditions, even when the displayed value is open. -/
theorem the_count_guard_sees_exactly_one_one
    {Next : Type} (next : Next → MetaArity base) (candidate : Assignment producer.target.declarations next) :
    ContextualConditionalGuards.Holds (ContextualPublication.privateFamily locals producer.update.declaration)
      candidate producer.target.rows producer.target.present
      (.count (symbol 1) 1) := by
  classical
  have same : ContextualConditionalGuards.region
      (ContextualPublication.privateFamily locals producer.update.declaration)
      candidate producer.target.rows producer.target.present (symbol 1) = {1} := by
    ext occurrence
    rw [ContextualConditionalGuards.mem_region]
    change (occurrence ∈ ({1} : Finset Nat) ∧ _) ↔ occurrence ∈ ({1} : Finset Nat)
    constructor
    · exact And.left
    · intro member
      refine ⟨member, ?_⟩
      have only := Finset.mem_singleton.mp member
      subst occurrence
      exact the_stored_conditional_row_accepts_one next candidate
  change (ContextualConditionalGuards.region _ candidate _ _ (symbol 1)).card = 1
  rw [same]
  exact Finset.card_singleton _

theorem the_absence_guard_excludes_two
    {Next : Type} (next : Next → MetaArity base) (candidate : Assignment producer.target.declarations next) :
    ContextualConditionalGuards.Holds (ContextualPublication.privateFamily locals producer.update.declaration)
      candidate producer.target.rows producer.target.present (.absent (symbol 2)) := by
  intro occurrence member
  have only : occurrence = 1 := Finset.mem_singleton.mp member
  subst occurrence
  exact the_stored_conditional_row_rejects_two next candidate

abbrev laterLocals := ContextualPublication.privateFamily locals producer.update.declaration
local instance : DecidableEq producer.update.Variables := producer.update.equality
local instance : DecidableEq producer.target.Names := producer.target.equality
abbrev laterCaptures := producer.target.declarations
abbrev laterRaw := ContextualActivatedStep.source laterLocals laterCaptures
abbrev laterActive := ContextualActivatedStep.target laterLocals laterCaptures

def consumerRule (number : Nat) : RuleInstance (SchematicReach.Closed laterRaw) :=
  ⟨[symbol number], [], [], [], [symbol 7]⟩
def consumerSelection : Selection Nat := ⟨[1], [], [2]⟩
def consumerOutputs (_ : Nat) : SchematicReach.Closed laterActive := symbol 7
def consumerProblem (number : Nat) := information laterLocals laterCaptures producer.target.occupied consumerSelection
  (consumerRule number) producer.target.rows producer.target.equations

def laterModel : Assignment laterActive captures := fun name => constantAt captures 1 (laterActive name)

theorem taking_one_has_a_joint_model : ContextualResidual.Models laterModel (consumerProblem 1) := by
  intro equation member
  change equation ∈ [_, _, _] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

theorem taking_one_is_admitted :
    Admitted laterLocals producer.target (consumerRule 1) consumerSelection consumerOutputs := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, ?_,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    ⟨Nat, captures, laterModel, taking_one_has_a_joint_model⟩, ?_⟩
  · with_unfolding_all rfl
  · intro check member
    cases member

def consumer : Firing laterLocals producer.target :=
  ⟨consumerRule 1, consumerSelection, consumerOutputs, (fun _ => true), taking_one_is_admitted,
    0, ContextualFrameWorklist.identity (consumerProblem 1), rfl⟩

theorem a_second_actual_firing_consumes_the_conditional_row :
    consumer.target.present = {2} ∧ 1 ∉ consumer.target.present ∧
      consumer.update.remaining.length = 3 := by
  exact ⟨rfl, by decide +kernel, rfl⟩

theorem the_second_firing_publishes_seven
    {Next : Type} (next : Next → MetaArity base) (candidate : Assignment consumer.target.declarations next) :
    Matches (ContextualPublication.privateFamily laterLocals consumer.update.declaration)
      consumer.target.declarations candidate (symbol 7) (consumer.target.rows 2) := by
  apply (consumer.ordinary_matches_source 2 (by decide +kernel) rfl next candidate (symbol 7)).mpr
  refine ⟨Extension.identity next, (fun name => constantAt next 1 (laterActive name)), ?_, rfl⟩
  intro equation member
  change equation ∈ [_, _, _] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

theorem taking_two_has_no_conditional_firing :
    ¬ Admitted laterLocals producer.target (consumerRule 2) consumerSelection consumerOutputs := by
  intro admitted
  obtain ⟨Future, future, candidate, model⟩ := admitted.solvable
  have rowMatch := take_matches laterLocals admitted candidate model ⟨0, by decide +kernel⟩
  change Matches laterLocals laterCaptures
    (Assignment.compose candidate (ContextualSelectionViews.capturedTarget laterLocals laterCaptures))
    (symbol 2) (producer.target.rows 1) at rowMatch
  exact the_stored_conditional_row_rejects_two future _ rowMatch

def readerRule : RuleInstance (SchematicReach.Closed laterRaw) :=
  ⟨[], [symbol 1], [], [], [symbol 7]⟩
def readerSelection : Selection Nat := ⟨[], [1], [2]⟩
def readerProblem := information laterLocals laterCaptures producer.target.occupied readerSelection
  readerRule producer.target.rows producer.target.equations

theorem reading_one_is_admitted :
    Admitted laterLocals producer.target readerRule readerSelection consumerOutputs := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, ?_,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    ⟨Nat, captures, laterModel, ?_⟩, ?_⟩
  · with_unfolding_all rfl
  · intro equation member
    change equation ∈ [_, _, _] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  · intro check member
    cases member

def reader : Firing laterLocals producer.target :=
  ⟨readerRule, readerSelection, consumerOutputs, (fun _ => true), reading_one_is_admitted,
    0, ContextualFrameWorklist.identity readerProblem, rfl⟩

theorem an_actual_read_keeps_the_row_and_produces_another :
    reader.target.present = {1, 2} ∧ reader.update.remaining.length = 3 := ⟨rfl, rfl⟩

theorem the_read_preserves_the_retained_rows_condition
    {Next : Type} (next : Next → MetaArity base) (candidate : Assignment reader.target.declarations next) :
    Matches (ContextualPublication.privateFamily laterLocals reader.update.declaration)
        reader.target.declarations candidate (symbol 1) (reader.target.rows 1) ∧
      ¬ Matches (ContextualPublication.privateFamily laterLocals reader.update.declaration)
        reader.target.declarations candidate (symbol 2) (reader.target.rows 1) := by
  constructor
  · apply (reader.retained_matches 1 (by decide +kernel) next candidate (symbol 1)).mpr
    exact the_stored_conditional_row_accepts_one next _
  · intro matched
    exact the_stored_conditional_row_rejects_two next _
      ((reader.retained_matches 1 (by decide +kernel) next candidate (symbol 2)).mp matched)

def initialScopes (_ : Nat) : Finset Nat := ∅

theorem initial_formed : ContextualConditionalScopes.Formed locals before initialScopes := by
  refine ⟨?_, ?_⟩
  · intro equation member
    have only := List.mem_singleton.mp member
    subst equation
    constructor <;> unfold ContextualScopeSupport.Covered <;> decide +kernel
  · intro occurrence member
    cases member

theorem producer_rule_covered :
    ContextualWorldScopeLedger.RuleCovered (ContextualScopeSupport.privateScopes (Local := Nat) initialScopes) ∅ rule := by
  intro value member
  change value ∈ [generator raw (.inr 0)] at member
  have only := List.mem_singleton.mp member
  subst value
  unfold ContextualScopeSupport.Covered
  decide +kernel

theorem actual_conditional_publication_preserves_formation :
    ContextualConditionalScopes.Formed laterLocals producer.target
      (ContextualConditionalScopes.targetScopes locals producer initialScopes) :=
  ContextualConditionalScopes.firing_preserves_formation locals producer initialScopes initial_formed producer_rule_covered

theorem consumer_rule_covered :
    ContextualWorldScopeLedger.RuleCovered
      (ContextualScopeSupport.privateScopes (Local := Nat ⊕ producer.update.Variables)
        (ContextualConditionalScopes.targetScopes locals producer initialScopes))
      producer.target.occupied (consumerRule 1) := by
  intro value member
  change value ∈ [symbol 1, symbol 7] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> unfold ContextualScopeSupport.Covered <;> decide +kernel

theorem taking_the_conditional_row_preserves_formation :
    ContextualConditionalScopes.Formed (ContextualPublication.privateFamily laterLocals consumer.update.declaration)
      consumer.target (ContextualConditionalScopes.targetScopes laterLocals consumer
        (ContextualConditionalScopes.targetScopes locals producer initialScopes)) :=
  ContextualConditionalScopes.firing_preserves_formation laterLocals consumer _
    actual_conditional_publication_preserves_formation consumer_rule_covered

theorem the_resolved_clause_compiler_publishes_without_waiting_for_completion :
    ∃ compiled : ContextualConditionalClauses.Compiled queries locals
        (before := ofEndpoint locals ContextualClausePublication.Controls.before)
        ContextualClausePublication.Controls.plan ContextualClausePublication.Controls.selected,
      compiled.firing.fuel = 0 ∧ compiled.firing.target.present = {7, 90, 91} := by
  obtain ⟨compiled, budget⟩ := ContextualConditionalClauses.realize queries locals
    (before := ofEndpoint locals ContextualClausePublication.Controls.before)
    ContextualClausePublication.Controls.plan ContextualClausePublication.Controls.selected
    ((ContextualConditionalSourceAdmission.admitted_ofEndpoint_iff queries locals ContextualClausePublication.Controls.before
      ContextualClausePublication.Controls.selected ContextualClausePublication.Controls.code).mpr
        ContextualClausePublication.Controls.source_admitted) 0
  refine ⟨compiled, budget, ?_⟩
  rw [compiled.physical_result]
  rfl

theorem the_same_source_guard_cannot_publish_through_the_conditional_compiler :
    ¬ Nonempty (ContextualConditionalClauses.Compiled queries locals
      (before := ofEndpoint locals ContextualClausePublication.Controls.before)
      ContextualClausePublication.Controls.refusedPlan ContextualClausePublication.Controls.selected) := by
  rintro ⟨compiled⟩
  exact ContextualClausePublication.Controls.a_contradictory_body_guard_is_refused
    ((ContextualConditionalSourceAdmission.admitted_ofEndpoint_iff queries locals ContextualClausePublication.Controls.before
      ContextualClausePublication.Controls.selected ContextualClausePublication.Controls.refusedCode).mp compiled.source_admitted)

namespace ScopeRelocation

def guardedRule (number : Nat) : RuleInstance (SchematicReach.Closed laterRaw) :=
  {consumerRule number with checks := [.count (symbol 1) 1, .absent (symbol 2)]}

theorem guarded_one_admitted :
    Admitted laterLocals producer.target (guardedRule 1) consumerSelection consumerOutputs := by
  refine ⟨taking_one_is_admitted.take_distinct, taking_one_is_admitted.output_distinct,
    taking_one_is_admitted.take_length, taking_one_is_admitted.read_length, taking_one_is_admitted.outputs,
    taking_one_is_admitted.taken_present, taking_one_is_admitted.read_present,
    taking_one_is_admitted.apart, taking_one_is_admitted.fresh, taking_one_is_admitted.solvable, ?_⟩
  intro check member Future future candidate _model
  change check ∈ [.count (symbol 1) 1, .absent (symbol 2)] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact (ContextualConditionalGuards.holds_transport laterLocals
      (ContextualSelectionViews.capturedTarget laterLocals laterCaptures) candidate
      producer.target.rows producer.target.present (.count (symbol 1) 1)).mpr
        (the_count_guard_sees_exactly_one_one future _)
  · exact (ContextualConditionalGuards.holds_transport laterLocals
      (ContextualSelectionViews.capturedTarget laterLocals laterCaptures) candidate
      producer.target.rows producer.target.present (.absent (symbol 2))).mpr
        (the_absence_guard_excludes_two future _)

def guardedFiring : Firing laterLocals producer.target :=
  ⟨guardedRule 1, consumerSelection, consumerOutputs, (fun _ => true), guarded_one_admitted,
    0, ContextualFrameWorklist.identity (consumerProblem 1), rfl⟩

def reservedScopes : Finset Nat := producer.target.occupied ∪ {100}

def relocatedBefore : State laterLocals Nat [] () := {producer.target with occupied := reservedScopes}

theorem original_and_relocated_scopes_differ :
    ContextualActivationScopes.scopeAt producer.target.occupied (ContextualActivationScopes.takePort consumerSelection ⟨0, by decide⟩) ≠
      ContextualActivationScopes.scopeAt reservedScopes (ContextualActivationScopes.takePort consumerSelection ⟨0, by decide⟩) := by
  decide +kernel

theorem relocated_input_keeps_scope_coverage :
    ContextualConditionalScopes.Formed laterLocals relocatedBefore
      (ContextualConditionalScopes.targetScopes locals producer initialScopes) :=
  actual_conditional_publication_preserves_formation.mono laterLocals reservedScopes Finset.subset_union_left

/-- A genuine pending conditional input is consumed after scope relocation;
count and absence still check the original inventory, at every budget. -/
theorem relocated_guarded_firing_exists (fuel : Nat) :
    ∃ permutation : Equiv.Perm Nat,
      (∀ port : ContextualActivationScopes.Port consumerSelection,
        permutation (ContextualActivationScopes.scopeAt producer.target.occupied port) =
          ContextualActivationScopes.scopeAt reservedScopes port) ∧
      ∃ moved : Firing laterLocals relocatedBefore,
        moved.rule = guardedRule 1 ∧ moved.selection = consumerSelection ∧
          moved.fuel = fuel ∧ moved.target.present = {2} ∧
          ∀ (Next : Type) (next : Next → MetaArity base) (candidate : Assignment moved.target.declarations next),
            Matches (ContextualPublication.privateFamily laterLocals moved.update.declaration)
              moved.target.declarations candidate (symbol 7) (moved.target.rows 2) := by
  obtain ⟨permutation, aligned⟩ := ContextualPairFrames.exists_scope_relocation consumerSelection
    producer.target.occupied reservedScopes
  obtain ⟨moved, rule, selection, outputs, reuse, budget, physical⟩ :=
    guardedFiring.relocate_exists laterLocals reservedScopes permutation aligned fuel
  refine ⟨permutation, aligned, moved, rule, selection, budget, physical, ?_⟩
  intro Next next candidate
  let original : Assignment guardedFiring.target.declarations next :=
    fun name => constantAt next 0 (guardedFiring.target.declarations name)
  have compared := guardedFiring.relocated_ordinary_matches reservedScopes permutation aligned
    moved rule selection 2 (by decide +kernel) (congrFun outputs 2) rfl
    (by rw [reuse]; rfl) next original candidate (symbol 7)
  exact compared.mp (the_second_firing_publishes_seven next original)

/-- Renaming fresh scopes cannot repair an incompatible selected row. -/
theorem taking_two_still_has_no_relocated_firing
    (permutation : Equiv.Perm Nat)
    (aligned : ∀ port : ContextualActivationScopes.Port consumerSelection,
      permutation (ContextualActivationScopes.scopeAt producer.target.occupied port) =
        ContextualActivationScopes.scopeAt reservedScopes port) :
    ¬ Admitted laterLocals relocatedBefore (consumerRule 2) consumerSelection
      (fun occurrence => instantiate (ContextualEventViewRelocation.assignment laterLocals laterCaptures permutation)
        (consumerOutputs occurrence)) := by
  intro admitted
  exact taking_two_has_no_conditional_firing
    ((admitted_relocation_iff laterLocals producer.target (consumerRule 2) consumerSelection consumerOutputs
      reservedScopes permutation aligned).mp admitted)

end ScopeRelocation

namespace PrivateTransport

abbrev doubled (name : Bool × (Nat ⊕ producer.update.Variables)) : MetaArity base :=
  laterLocals name.2

/-- The actual pending answer survives a nonidentity embedding of its
private bank. Its equation still excludes the incompatible answer. -/
theorem actual_pending_answer_survives_private_reindexing
    {Next : Type} (next : Next → MetaArity base) (candidate : Assignment laterCaptures next) :
    let moved := ContextualConditionalPublication.reindexPrivate laterLocals doubled laterCaptures
      (fun name => (true, name)) (fun _ => rfl) (producer.target.rows 1)
    Matches doubled laterCaptures candidate (symbol 1) moved ∧
      ¬ Matches doubled laterCaptures candidate (symbol 2) moved := by
  have preserved (number : Nat) := ContextualConditionalPublication.reindexPrivate_matches_iff
    laterLocals doubled laterCaptures (fun name => (true, name)) Prod.snd
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) candidate (producer.target.rows 1) (symbol number)
  exact ⟨(preserved 1).mpr (the_stored_conditional_row_accepts_one next candidate),
    fun matched => the_stored_conditional_row_rejects_two next candidate ((preserved 2).mp matched)⟩

def capturedOnes : Assignment laterCaptures captures :=
  fun name => constantAt captures 1 (laterCaptures name)

def openedOnes : Assignment (ContextualActivatedStep.target laterLocals captures) captures :=
  fun name => constantAt captures 1 (ContextualActivatedStep.target laterLocals captures name)

/-- The complete prepared information of the actual consuming rule,
including the pending row equation, survives a caller refinement. -/
theorem refined_consumer_information_has_a_model :
    ContextualResidual.Models openedOnes
      (information laterLocals captures producer.target.occupied consumerSelection
        ((consumerRule 1).map (instantiate (ContextualStoredRows.liftCaptures laterLocals capturedOnes)))
        (fun occurrence => (producer.target.rows occurrence).map laterLocals laterCaptures capturedOnes)
        (ContextualResidual.mapProblem capturedOnes producer.target.equations)) := by
  rw [← information_transport]
  apply (ContextualResidual.models_mapProblem _ _ _).mpr
  have square : Assignment.compose openedOnes (ContextualViewNaturality.activeLift laterLocals capturedOnes) =
      laterModel := by
    funext name
    cases name with
    | inl name => exact instantiate_generator _ _
    | inr name => rfl
  rw [square]
  exact taking_one_has_a_joint_model

def capturedZeros : Assignment captures captures := fun name => constantAt captures 0 (captures name)

/-- Guard transport alone cannot justify admission: a noninvertible caller
refinement may contradict the firing's incoming information. -/
theorem capture_refinement_can_destroy_solvability :
    ¬ Solvable (information locals captures ∅ selected
      (rule.map (instantiate (ContextualStoredRows.liftCaptures locals capturedZeros)))
      (fun occurrence => (before.rows occurrence).map locals captures capturedZeros)
      (ContextualResidual.mapProblem capturedZeros before.equations)) := by
  erw [← information_transport locals captures capturedZeros ∅ selected rule before.rows before.equations]
  change ¬ Solvable (ContextualResidual.mapProblem
    (ContextualViewNaturality.activeLift locals capturedZeros) problem)
  rw [problem_explicit]
  rintro ⟨Future, future, candidate, modeled⟩
  change ContextualResidual.Models candidate [(observe (symbol 0), observe (symbol 1))] at modeled
  have same := (ContextualResidual.models_observed_iff candidate _ _).mp modeled
  change symbol (decl := future) 0 = symbol 1 at same
  exact (by decide : (0 : Nat) ≠ 1) (SchematicReach.Controls.symbol_injective same)

end PrivateTransport

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalExecution.Controls
