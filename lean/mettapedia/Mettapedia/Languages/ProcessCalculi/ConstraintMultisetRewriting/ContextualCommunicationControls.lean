import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunication
import Mettapedia.OSLF.Syntax.ContextualRigidTerms
import Mettapedia.OSLF.Syntax.RhoQuotationClassFibres

/-!
# Two-sided COMM answers reach retained sender continuations

Pure communication binds the sender's shared channel. A separately stated
receiver payload equation additionally binds its shared data. The receiver
schema's private payload local is opened in a different scope from the
rule's payload local, and its lexical channel remains an explicit capture.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunicationControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualCommunication
open ContextualResidual

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq RhoSchema.Srt)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := operatorEquality sort

inductive Shared where
  | sendChannel
  | lexicalChannel
  | sendPayload
  deriving DecidableEq, Repr

def captures : Shared → MetaArity base
  | .sendChannel | .lexicalChannel => ([], .nm)
  | .sendPayload => ([], .pr)

abbrev raw := source captures
abbrev active := target captures
abbrev RawTerm := Term (signature base raw) [] .pr
abbrev ActiveTerm := Term (signature base active) [] .pr

def sharedChannel {Γ : Ctx base} : Term (signature base captures) Γ .nm := .op (.inr (Operator.mk (declaration := captures) Shared.sendChannel)) .nil
def sharedPayload {Γ : Ctx base} : Term (signature base captures) Γ .pr := .op (.inr (Operator.mk (declaration := captures) Shared.sendPayload)) .nil
def lexical {Γ : Ctx base} : Term (signature base raw) Γ .nm := .op (.inr (Operator.mk (declaration := raw) (Sum.inr Shared.lexicalChannel))) .nil
def receiver : RawTerm := input (quote zero)
  (parallel (output (.var .zero) (payload captures)) (output lexical zero))
def sender : Term (signature base captures) [] .pr := output sharedChannel sharedPayload
def retained : Term (signature base captures) [] .pr := output sharedChannel (parallel sharedPayload zero)
def rows (occurrence : Nat) : ContextualStoredRows.Row locals captures [] .pr :=
  if occurrence = 10 then .schema receiver else if occurrence = 20 then .shared sender else .shared retained

def occupied : Finset Nat := {0, 2, 7}
def selection : Selection Nat := ⟨[10, 20], [], [40]⟩
def before : Configuration (Term (signature base captures) [] .pr) Nat := ⟨[], {10, 20, 30}⟩
def plainRule := rule captures
def dataRule := constrainedRule captures zero
def ruleScope := ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.rulePort selection)
def receiverScope := ContextualActivationScopes.scopeAt occupied
  (ContextualActivationScopes.takePort selection ⟨0, by decide⟩)
def produced : ActiveTerm := ContextualFreshening.termAt locals captures ruleScope
  (continuation captures (quote (payload captures)))
def outputs (_ : Nat) : ActiveTerm := produced
def plainProblem := ContextualActivatedStep.problem locals captures occupied selection plainRule rows before
def dataProblem := ContextualActivatedStep.problem locals captures occupied selection dataRule rows before

theorem rule_and_receiver_locals_use_different_fresh_scopes : ruleScope = 8 ∧ receiverScope = 9 := by decide +kernel

theorem pure_communication_has_physical_admission :
    ContextualGuardedStep.Requirements locals captures occupied selection plainRule rows before outputs := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ?_⟩
  intro check member
  exact False.elim (List.not_mem_nil member)

theorem the_data_constraint_is_an_additional_admitted_equation :
    ContextualGuardedStep.Requirements locals captures occupied selection dataRule rows before outputs := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ?_⟩
  intro check member
  exact False.elim (List.not_mem_nil member)

def witness : Assignment active active
  | .inl ⟨_, .channel⟩ => quote zero
  | .inl ⟨_, .payload⟩ => zero
  | .inl ⟨_, .continuation⟩ => parallel (output (.var .zero) zero) (output (quote zero) zero)
  | .inr .sendChannel | .inr .lexicalChannel => quote zero
  | .inr .sendPayload => zero

theorem witness_models_plain : Models witness (observeProblem plainProblem) := by
  apply (models_observeProblem (S := base) (source := active) witness plainProblem).mpr
  intro equation member
  change equation ∈ [(_, _), (_, _)] at member
  rcases List.mem_cons.mp member with same | tail
  · subst equation
    with_unfolding_all rfl
  · have same := List.mem_singleton.mp tail
    subst equation
    with_unfolding_all rfl

theorem witness_models_data : Models witness (observeProblem dataProblem) := by
  apply (models_observeProblem (S := base) (source := active) witness dataProblem).mpr
  intro equation member
  change equation ∈ [(_, _), (_, _), (_, _)] at member
  rcases List.mem_cons.mp member with same | tail
  · subst equation
    with_unfolding_all rfl
  · rcases List.mem_cons.mp tail with same | tail
    · subst equation
      with_unfolding_all rfl
    · have same := List.mem_singleton.mp tail
      subst equation
      with_unfolding_all rfl

def separatedPayload {Γ : Ctx base} : Term (signature base active) Γ .pr := output (quote zero) zero

def separatedWitness : Assignment active active
  | .inl ⟨_, .channel⟩ => quote zero
  | .inl ⟨scope, .payload⟩ => if scope = receiverScope then separatedPayload else zero
  | .inl ⟨_, .continuation⟩ =>
      parallel (output (.var .zero) separatedPayload) (output (quote separatedPayload) zero)
  | .inr .sendChannel => quote zero
  | .inr .lexicalChannel => quote separatedPayload
  | .inr .sendPayload => zero

theorem separated_model_keeps_receiver_locals_and_lexical_capture_independent :
    Models separatedWitness (observeProblem plainProblem) := by
  apply (models_observeProblem (S := base) (source := active) separatedWitness plainProblem).mpr
  intro equation member
  change equation ∈ [(_, _), (_, _)] at member
  rcases List.mem_cons.mp member with same | tail
  · subst equation
    with_unfolding_all rfl
  · have same := List.mem_singleton.mp tail
    subst equation
    with_unfolding_all rfl

theorem a_principal_update_cannot_capture_the_receiver_payload
    (update : ContextualFrameUpdate.Update (observeProblem plainProblem)) :
    update.answer (.inl (ScopedVar.at receiverScope .payload)) ≠ update.answer (.inr .sendPayload) := by
  intro same
  obtain ⟨residual, _, factors⟩ := update.factors active separatedWitness
    separated_model_keeps_receiver_locals_and_lexical_capture_independent
  have identified := (factors (.inl (ScopedVar.at receiverScope .payload))).trans
    ((congrArg (instantiate residual) same).trans (factors (.inr .sendPayload)).symm)
  exact (by decide +kernel : termSize (separatedWitness (.inl (ScopedVar.at receiverScope .payload))) ≠
    termSize (separatedWitness (.inr .sendPayload))) (congrArg termSize identified)

theorem a_principal_update_cannot_capture_the_lexical_channel
    (update : ContextualFrameUpdate.Update (observeProblem plainProblem)) :
    update.answer (.inr .lexicalChannel) ≠ update.answer (.inr .sendChannel) := by
  intro same
  obtain ⟨residual, _, factors⟩ := update.factors active separatedWitness
    separated_model_keeps_receiver_locals_and_lexical_capture_independent
  have identified := (factors (.inr .lexicalChannel)).trans
    ((congrArg (instantiate residual) same).trans (factors (.inr .sendChannel)).symm)
  exact (by decide +kernel : termSize (separatedWitness (.inr .lexicalChannel)) ≠
    termSize (separatedWitness (.inr .sendChannel))) (congrArg termSize identified)

theorem every_plain_solution_binds_the_sender_channel {W : Type} (next : W → MetaArity base)
    (assignment : Assignment active next) (models : Models assignment (observeProblem plainProblem)) :
    assignment (.inr .sendChannel) = quote zero := by
  have solved := (models_observeProblem (S := base) (source := active) assignment plainProblem).mp models
  have first := solved (plainProblem.get ⟨0, by decide⟩) (List.get_mem _ _)
  have second := solved (plainProblem.get ⟨1, by decide⟩) (List.get_mem _ _)
  have receiverChannel := input_channel first
  have senderChannel := output_channel second
  change instantiate assignment (generator active (.inl (ScopedVar.at ruleScope .channel))) = quote zero at receiverChannel
  change instantiate assignment (generator active (.inl (ScopedVar.at ruleScope .channel))) =
    instantiate assignment (generator active (.inr .sendChannel)) at senderChannel
  rw [instantiate_generator] at receiverChannel
  rw [instantiate_generator, instantiate_generator] at senderChannel
  exact senderChannel.symm.trans receiverChannel

theorem every_data_solution_binds_the_sender_payload {W : Type} (next : W → MetaArity base)
    (assignment : Assignment active next) (models : Models assignment (observeProblem dataProblem)) :
    assignment (.inr .sendPayload) = zero := by
  have solved := (models_observeProblem (S := base) (source := active) assignment dataProblem).mp models
  have second := solved (dataProblem.get ⟨1, by decide⟩) (List.get_mem _ _)
  have constraint := solved (dataProblem.get ⟨2, by decide⟩) (List.get_mem _ _)
  have senderPayload := output_payload second
  change instantiate assignment (generator active (.inl (ScopedVar.at ruleScope .payload))) = zero at constraint
  change instantiate assignment (generator active (.inl (ScopedVar.at ruleScope .payload))) =
    instantiate assignment (generator active (.inr .sendPayload)) at senderPayload
  rw [instantiate_generator] at constraint
  rw [instantiate_generator, instantiate_generator] at senderPayload
  exact senderPayload.symm.trans constraint

theorem every_plain_solution_reaches_the_retained_continuation {W : Type} (next : W → MetaArity base)
    (assignment : Assignment active next) (models : Models assignment (observeProblem plainProblem)) :
    instantiate assignment (instantiate (ContextualSelectionViews.capturedTarget locals captures) retained) =
      output (quote zero) (parallel (assignment (.inr .sendPayload)) zero) := by
  have channelBound := every_plain_solution_binds_the_sender_channel next assignment models
  change output (instantiate assignment (generator active (.inr .sendChannel)))
    (parallel (instantiate assignment (generator active (.inr .sendPayload))) zero) = _
  exact (congrArg₂ (fun (channel : Term (signature base next) [] .nm)
      (payload : Term (signature base next) [] .pr) => output channel (parallel payload zero))
    (instantiate_generator assignment (.inr .sendChannel))
    (instantiate_generator assignment (.inr .sendPayload))).trans
      (congrArg (fun channel : Term (signature base next) [] .nm =>
        output channel (parallel (assignment (.inr .sendPayload)) zero)) channelBound)

def pending {equations : Problem active} : ContextualFrameWorklist.Result equations → Option Nat
  | .refuted _ => none
  | .residual update => some update.remaining.length

theorem the_actual_pure_comm_run_finishes :
    pending (ContextualFrameWorklist.run (S := base) 4 active (observeProblem plainProblem)) = some 0 := by
  rw [ContextualFrameWorklist.run_eq_local_on_model 4 (observeProblem plainProblem) active witness witness_models_plain]
  decide +kernel

theorem the_actual_constrained_comm_run_finishes :
    pending (ContextualFrameWorklist.run (S := base) 5 active (observeProblem dataProblem)) = some 0 := by
  rw [ContextualFrameWorklist.run_eq_local_on_model 5 (observeProblem dataProblem) active witness witness_models_data]
  decide +kernel


theorem pure_comm_has_an_actual_guarded_helper_active_formation :
    ∃ update, ContextualTransportedActivation.FromRun locals captures 4 occupied selection plainRule rows before outputs update := by
  have count := the_actual_pure_comm_run_finishes
  cases computed : ContextualFrameWorklist.run (S := base) 4 active (observeProblem plainProblem) with
  | refuted impossible => simp only [computed, pending, reduceCtorEq] at count
  | residual update =>
      have empty : update.remaining = [] := by
        simpa only [computed, pending, Option.some.injEq, List.length_eq_zero_iff] using count
      exact ⟨update, ContextualTransportedActivation.from_run locals captures pure_communication_has_physical_admission update computed empty⟩

theorem the_actual_pure_comm_answer_reaches_the_retained_continuation :
    ∃ update, ContextualTransportedActivation.FromRun locals captures 4 occupied selection plainRule rows before outputs update ∧
      update.answer (.inr .sendChannel) = quote zero ∧
      instantiate update.answer (instantiate (ContextualSelectionViews.capturedTarget locals captures) retained) =
        output (quote zero) (parallel (update.answer (.inr .sendPayload)) zero) := by
  obtain ⟨update, formed⟩ := pure_comm_has_an_actual_guarded_helper_active_formation
  have models := update.completed formed.empty
  exact ⟨update, formed, every_plain_solution_binds_the_sender_channel update.declaration update.answer models,
    every_plain_solution_reaches_the_retained_continuation update.declaration update.answer models⟩

theorem the_actual_constrained_comm_answer_binds_the_output_data :
    ∃ update, ContextualTransportedActivation.FromRun locals captures 5 occupied selection dataRule rows before outputs update ∧
      update.answer (.inr .sendPayload) = zero := by
  have count := the_actual_constrained_comm_run_finishes
  cases computed : ContextualFrameWorklist.run (S := base) 5 active (observeProblem dataProblem) with
  | refuted impossible => simp only [computed, pending, reduceCtorEq] at count
  | residual update =>
      have empty : update.remaining = [] := by
        simpa only [computed, pending, Option.some.injEq, List.length_eq_zero_iff] using count
      exact ⟨update, ContextualTransportedActivation.from_run locals captures the_data_constraint_is_an_additional_admitted_equation update computed empty,
        every_data_solution_binds_the_sender_payload update.declaration update.answer (update.completed empty)⟩

theorem the_send_is_consumed_and_its_distinct_continuation_survives :
    20 ∉ (ContextualActivatedStep.result locals captures occupied selection plainRule rows before).present ∧
      30 ∈ (ContextualActivatedStep.result locals captures occupied selection plainRule rows before).present ∧
      40 ∈ (ContextualActivatedStep.result locals captures occupied selection plainRule rows before).present := by
  decide +kernel

def duplicateSelection : Selection Nat := ⟨[20, 20], [], [40]⟩

theorem one_send_cannot_be_consumed_twice :
    ¬ ContextualGuardedStep.Requirements locals captures occupied duplicateSelection plainRule rows before outputs := by
  intro admitted
  have distinct := admitted.take_distinct
  exact (by decide : ¬ ([20, 20] : List Nat).Nodup) distinct

namespace SemanticPorts

/-- Separating name occurrences from active dereferences adds a process
parameter. Inferring that abstraction from its readout is not unique. -/
def declaration (_ : Unit) : MetaArity base := ([.nm, .pr], .pr)
abbrev Value := Term (signature base declaration) [] .pr

def dropName {Γ : Ctx base} (name : Term (signature base declaration) Γ .nm) :
    Term (signature base declaration) Γ .pr := .op (.inl .drp) (.cons name .nil)

def call {Γ : Ctx base} (name : Term (signature base declaration) Γ .nm)
    (process : Term (signature base declaration) Γ .pr) : Term (signature base declaration) Γ .pr :=
  .op (.inr (.mk ())) (.cons name (.cons process .nil))

def byProcess : Assignment declaration declaration := fun _ => .var (.succ .zero)
def byName : Assignment declaration declaration := fun _ => dropName (.var .zero)

def packet : Value := Rigid.includeTerm declaration RhoSourceOutputPredicate.output
def receiverPattern : Value := input (quote zero) (call (.var .zero) (dropName (.var .zero)))
def receiverValue : Value := input (quote zero) (dropName (.var .zero))
def senderValue : Value := output (quote zero) packet
def produced : Value := call (quote packet) packet
def selected : Selection Nat := ⟨[0, 1], [], [2]⟩
def initial : Configuration Value Nat := ⟨[], {0, 1}⟩
def rule : RuleInstance Value := ⟨[receiverPattern, senderValue], [], [], [], [produced]⟩
def label (occurrence : Nat) : Value :=
  if occurrence = 0 then receiverValue else if occurrence = 1 then senderValue else produced
def problem := selected.problem label rule initial

theorem both_factorizations_solve_the_actual_selected_problem :
    (ContextualFamilies.action declaration [] .pr).Models byProcess problem ∧
      (ContextualFamilies.action declaration [] .pr).Models byName problem := by
  constructor <;> intro equation member
  all_goals
    change equation ∈ [(receiverPattern, receiverValue), (senderValue, senderValue)] at member
    rcases List.mem_cons.mp member with first | last
    · subst equation; rfl
    · have only := List.mem_singleton.mp last
      subst equation; rfl

theorem the_proposed_raw_rule_is_semantically_admitted :
    selected.Valid (ContextualFamilies.action declaration [] .pr) label rule initial := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, ?_,
    ⟨byProcess, both_factorizations_solve_the_actual_selected_problem.1⟩, ?_⟩
  · refine ⟨by decide, by decide, by decide, by decide, ?_⟩
    intro query member; cases member
  · intro check member; cases member

theorem the_process_projection_activates_the_payload : instantiate byProcess produced = packet := rfl

theorem the_name_projection_leaves_a_drop : instantiate byName produced = dropName (quote packet) := rfl

theorem the_two_outputs_are_distinct : instantiate byProcess produced ≠ instantiate byName produced := by
  intro same
  cases (Term.op.inj same).1

theorem the_old_body_does_not_determine_the_requested_output :
    ¬ ∀ candidate, (ContextualFamilies.action declaration [] .pr).Models candidate problem →
      instantiate candidate produced = packet := by
  intro determined
  exact the_two_outputs_are_distinct
    (the_process_projection_activates_the_payload.trans
      (determined byName both_factorizations_solve_the_actual_selected_problem.2).symm)

theorem the_source_classes_also_distinguish_the_outputs :
    RhoEquationConstructorControls.project RhoSourceOutputPredicate.output ≠
      RhoEquationConstructorControls.project RhoQuotationClassFibres.suspendedRaw :=
  Ne.symm RhoQuotationClassFibres.suspended_not_visible

theorem the_compound_continuation_spine_is_not_a_structural_pattern :
    ContextualPatternFragment.check receiverPattern = false := by
  decide +kernel

end SemanticPorts

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunicationControls
