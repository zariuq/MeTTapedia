import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.QuotedLambdaExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionEndpoints
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixPrincipals
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LambdaExecution

/-!
# Retained states for mixed quoted and active lambda programs

This client uses the existing activation inventories and scope ledger.
Beta and activation share one declaration family and one running equation
store. Source recognition and output uniqueness are supplied by the proved
mixed-language comparison, through an explicit restriction of each actual
selected equation problem. No intermediate state is replaced by a freshly
encoded source reduct.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.QuotedLambdaRetained

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open QuotedLambda (sig Op Context Redex)
open LambdaContextualRung (Srt)
open QuotedLambdaExecution (Kind kind encode plug instantiate_plug instantiate_inst plug_encode)
open Mettapedia.Logic.LP (ScopedVar)
open ContextualWorldScopeLedger ContextualScopeSupport

local instance : DecidableEq sig.Srt := inferInstanceAs (DecidableEq Srt)

abbrev Local := Ctx sig × Bool
abbrev locals (key : Local) : MetaArity sig := QuotedLambdaExecution.locals key.1 key.2

variable {V W : Type} (captures : V → MetaArity sig)

abbrev raw := ContextualActivatedStep.source locals captures
abbrev active := ContextualActivatedStep.target locals captures

def schemaMap (Δ : Ctx sig) : Assignment (QuotedLambdaExecution.raw Δ) (raw captures)
  | .inl role => generator (raw captures) (.inl (Δ, role))
  | .inr impossible => nomatch impossible

def schemaAt (Δ : Ctx sig) (scope : Nat) : Assignment (QuotedLambdaExecution.raw Δ) (active captures)
  | .inl role => generator (active captures) (.inl ⟨scope, (Δ, role)⟩)
  | .inr impossible => nomatch impossible

theorem fresh_schema_map (Δ : Ctx sig) (scope : Nat) {Γ : Ctx sig}
    (term : Term (signature sig (QuotedLambdaExecution.raw Δ)) Γ .term) :
    ContextualFreshening.termAt locals captures scope (instantiate (schemaMap captures Δ) term) =
      instantiate (schemaAt captures Δ scope) term := by
  unfold ContextualFreshening.termAt
  rw [instantiate_comp]
  congr 1
  funext key
  cases key with
  | inl role => exact instantiate_generator _ _
  | inr impossible => exact nomatch impossible

def rule {Γ Δ : Ctx sig} (selected : Kind) (context : Context Γ Δ) : RuleInstance (Term (signature sig (raw captures)) Γ .term) :=
  (QuotedLambdaExecution.rule selected context).map (instantiate (schemaMap captures Δ))

def selection (current : Nat) : Selection Nat := ⟨[current], [], [current + 1]⟩

def ruleScope (occupied : Finset Nat) (current : Nat) :=
  ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.rulePort (selection current))

def output {Γ Δ : Ctx sig} (occupied : Finset Nat) (current : Nat) (selected : Kind) (context : Context Γ Δ) :
    Term (signature sig (active captures)) Γ .term :=
  instantiate (schemaAt captures Δ (ruleScope occupied current)) (QuotedLambdaExecution.rhs selected context)

def State (Γ : Ctx sig) : Type 1 := ContextualExecution.Endpoint locals Nat Γ .term × Nat

variable {captures}

def Represents {Γ : Ctx sig} (state : State Γ) (source : Term sig Γ .term) : Prop :=
  state.1.inventory.configuration.present = {state.2} ∧
  (ContextualFamilies.action state.1.declarations Γ .term).Consistent state.1.inventory.configuration.equations ∧
  ∃ value : Term (signature sig state.1.declarations) Γ .term,
    state.1.inventory.rows state.2 = .shared value ∧
    ∀ (Future : Type) (future : Future → MetaArity sig) (candidate : Assignment state.1.declarations future),
      ContextualFrameUnifier.Models candidate state.1.inventory.configuration.equations →
        instantiate candidate value = encode future source

theorem actual_problem {Γ Δ : Ctx sig} (state : State Γ) (selected : Kind) (context : Context Γ Δ)
    (value : Term (signature sig state.1.declarations) Γ .term)
    (isShared : state.1.inventory.rows state.2 = .shared value) :
    ContextualActivatedStep.problem locals state.1.declarations state.1.occupied (selection state.2)
        (rule state.1.declarations selected context) state.1.inventory.rows state.1.inventory.configuration =
      ContextualFrameUnifier.mapProblem (ContextualSelectionViews.capturedTarget locals state.1.declarations)
        state.1.inventory.configuration.equations ++
      [(instantiate (schemaAt state.1.declarations Δ (ruleScope state.1.occupied state.2)) (QuotedLambdaExecution.lhs selected context),
        instantiate (ContextualSelectionViews.capturedTarget locals state.1.declarations) value)] := by
  change _ ++ [(ContextualFreshening.termAt locals _ _ (instantiate (schemaMap _ _) (QuotedLambdaExecution.lhs selected context)),
    ContextualFreshening.termAt locals _ _ (ContextualStoredRows.asTemplate locals _ (state.1.inventory.rows state.2)))] ++ [] ++ [] = _
  rw [isShared, fresh_schema_map]
  simp only [ContextualStoredRows.asTemplate, List.append_nil]
  rw [← ContextualSelectionViews.shared_value_at_port locals state.1.declarations state.1.occupied
    (ContextualActivationScopes.takePort (selection state.2) ⟨0, by simp [selection]⟩) value]
  rfl

theorem admission {Γ Δ : Ctx sig} (state : State Γ) (selected : Kind) (context : Context Γ Δ)
    (present : state.1.inventory.configuration.present = {state.2}) :
    ContextualGuardedStep.Requirements locals state.1.declarations state.1.occupied (selection state.2)
      (rule state.1.declarations selected context) state.1.inventory.rows state.1.inventory.configuration
      (fun _ => output state.1.declarations state.1.occupied state.2 selected context) := by
  refine ⟨by simp [selection], by simp [selection], rfl, rfl, ?_, ?_, ?_⟩
  · change [_] = [ContextualFreshening.termAt locals _ _ (instantiate (schemaMap _ _) (QuotedLambdaExecution.rhs selected context))]
    rw [fresh_schema_map]
    rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change ({state.2} : Finset Nat) ⊆ _
      rw [present]
    · exact Finset.empty_subset _
    · exact Finset.disjoint_empty_right _
    · change Disjoint ({state.2 + 1} : Finset Nat) _
      rw [present, Finset.disjoint_singleton_left, Finset.mem_singleton]
      omega
    · intro check member; cases member
  · intro check member; cases member

variable {next : W → MetaArity sig}

def extendModel (old : Assignment captures next) {Δ : Ctx sig}
    (redex : Redex Δ) :
    Assignment (active captures) (active next)
  | .inr name => instantiate (ContextualSelectionViews.capturedTarget locals next) (old name)
  | .inl ⟨scope, (context, false)⟩ =>
      if same : context = Δ then same.symm ▸ (match redex with
        | .beta body _ => encode (active next) body
        | .activation code => encode (active next) (weaken code))
      else generator (active next) (.inl ⟨scope, (context, false)⟩)
  | .inl ⟨scope, (context, true)⟩ =>
      if same : context = Δ then same.symm ▸ (match redex with
        | .beta _ argument => encode (active next) argument
        | .activation code => encode (active next) code)
      else generator (active next) (.inl ⟨scope, (context, true)⟩)

theorem extendModel_captures (old : Assignment captures next) {Δ : Ctx sig} (redex : Redex Δ) :
    Assignment.compose (extendModel old redex) (ContextualSelectionViews.capturedTarget locals captures) =
      Assignment.compose (ContextualSelectionViews.capturedTarget locals next) old := by
  funext name
  rw [Assignment.compose, ContextualSelectionViews.capturedTarget, instantiate_generator]
  rfl

/-- Compare one selected activation with the independent one-step schema.
The comparison forgets unused private names but never changes the stored
endpoint or its actual declaration ledger. -/
def restrict (Δ : Ctx sig) (scope : Nat) (candidate : Assignment (active captures) next) :
    Assignment (QuotedLambdaExecution.active Δ) next
  | .inl ⟨_, role⟩ => candidate (.inl ⟨scope, (Δ, role)⟩)
  | .inr impossible => nomatch impossible

theorem restricted_open (Δ : Ctx sig) (scope : Nat) (candidate : Assignment (active captures) next)
    {Γ : Ctx sig} (value : Term (signature sig (QuotedLambdaExecution.raw Δ)) Γ .term) :
    instantiate (restrict Δ scope candidate) (QuotedLambdaExecution.openTerm value) =
      instantiate candidate (instantiate (schemaAt captures Δ scope) value) := by
  unfold QuotedLambdaExecution.openTerm ContextualFreshening.termAt
  rw [instantiate_comp, instantiate_comp]
  congr 1
  funext name
  cases name with
  | inl role =>
      simp only [ContextualFreshening.assignment, schemaAt, instantiate_generator, restrict]
      rfl
  | inr impossible => exact nomatch impossible

def emptyInclusion (next : W → MetaArity sig) : Assignment QuotedLambdaExecution.captures next :=
  fun impossible => nomatch impossible

theorem restricted_extended_model (old : Assignment captures next) {Δ : Ctx sig} (redex : Redex Δ) (scope : Nat) :
    restrict Δ scope (extendModel old redex) =
      Assignment.compose (emptyInclusion (active next)) (QuotedLambdaExecution.model redex) := by
  funext name
  cases name with
  | inl key =>
      rcases key with ⟨_, role⟩
      cases role <;> cases redex <;>
        simp only [restrict, extendModel, dite_true, Assignment.compose, QuotedLambdaExecution.model,
          Rigid.instantiate_include]
  | inr impossible => exact nomatch impossible

theorem extended_model_solves {Γ Δ : Ctx sig} (state : State Γ) (context : Context Γ Δ) (redex : Redex Δ)
    (value : Term (signature sig state.1.declarations) Γ .term)
    (isShared : state.1.inventory.rows state.2 = .shared value)
    (old : Assignment state.1.declarations next)
    (solved : ContextualFrameUnifier.Models old state.1.inventory.configuration.equations)
    (observed : instantiate old value = encode next (context.plug redex.source)) :
    ContextualFrameUnifier.Models (extendModel old redex)
      (ContextualActivatedStep.problem locals state.1.declarations state.1.occupied (selection state.2)
        (rule state.1.declarations (kind redex) context) state.1.inventory.rows state.1.inventory.configuration) := by
  rw [actual_problem state (kind redex) context value isShared]
  apply (ContextualFrameUnifier.models_append _ _ _).mpr
  constructor
  · apply (ContextualFrameUnifier.models_mapProblem _ _ _).mpr
    rw [extendModel_captures]
    exact ContextualFrameUnifier.models_compose solved _
  · intro equation member
    have only := List.mem_singleton.mp member
    subst equation
    dsimp only [Prod.fst, Prod.snd]
    rw [← restricted_open, restricted_extended_model]
    have retained : instantiate (extendModel old redex)
        (instantiate (ContextualSelectionViews.capturedTarget locals state.1.declarations) value) =
          encode (active next) (context.plug redex.source) := by
      calc
        _ = instantiate (Assignment.compose (extendModel old redex)
            (ContextualSelectionViews.capturedTarget locals state.1.declarations)) value :=
          (Assignment.instantiate_compose _ _ _).symm
        _ = instantiate (Assignment.compose (ContextualSelectionViews.capturedTarget locals next) old) value :=
          congrArg (fun change => instantiate change value) (extendModel_captures old redex)
        _ = instantiate (ContextualSelectionViews.capturedTarget locals next) (instantiate old value) :=
          Assignment.instantiate_compose _ _ _
        _ = instantiate (ContextualSelectionViews.capturedTarget locals next)
            (encode next (context.plug redex.source)) := congrArg _ observed
        _ = _ := Rigid.instantiate_include _ _
    rw [retained]
    have sourceModel := ContextualFrameUnifier.models_compose (QuotedLambdaExecution.input_model context redex)
      (emptyInclusion (active next))
    have selected := sourceModel _ (by rw [QuotedLambdaExecution.problem_eq]; exact List.mem_singleton_self _)
    simpa only [Rigid.instantiate_include] using selected

theorem valid_of_source {Γ Δ : Ctx sig} (state : State Γ) (context : Context Γ Δ) (redex : Redex Δ)
    (represented : Represents state (context.plug redex.source)) :
    ContextualGuardedStep.Valid locals state.1.declarations state.1.occupied (selection state.2)
      (rule state.1.declarations (kind redex) context) state.1.inventory.rows state.1.inventory.configuration
      (fun _ => output state.1.declarations state.1.occupied state.2 (kind redex) context) := by
  obtain ⟨present, ⟨old, solved⟩, value, isShared, observes⟩ := represented
  have formation := admission state (kind redex) context present
  refine ⟨formation, ?_⟩
  apply ContextualFrameUnifier.solvable_of_consistent
  exact ⟨extendModel old redex, extended_model_solves state context redex value isShared old solved
    (observes _ state.1.declarations old solved)⟩

theorem restrict_actual_model {Γ Δ : Ctx sig} (state : State Γ) (selected : Kind) (context : Context Γ Δ)
    (source : Term sig Γ .term) (represented : Represents state source)
    {Future : Type} {future : Future → MetaArity sig} (candidate : Assignment (active state.1.declarations) future)
    (solved : ContextualFrameUnifier.Models candidate
      (ContextualActivatedStep.problem locals state.1.declarations state.1.occupied (selection state.2)
        (rule state.1.declarations selected context) state.1.inventory.rows state.1.inventory.configuration)) :
    ContextualFrameUnifier.Models (restrict Δ (ruleScope state.1.occupied state.2) candidate)
      (QuotedLambdaExecution.problem selected context source) := by
  obtain ⟨_, _, value, isShared, observes⟩ := represented
  rw [actual_problem state selected context value isShared] at solved
  obtain ⟨old, current⟩ := (ContextualFrameUnifier.models_append _ _ _).mp solved
  have oldModel := (ContextualFrameUnifier.models_mapProblem _ _ _).mp old
  have oldValue := observes Future future _ oldModel
  rw [Assignment.instantiate_compose] at oldValue
  intro equation member
  rw [QuotedLambdaExecution.problem_eq] at member
  have only := List.mem_singleton.mp member
  subst equation
  change instantiate _ (QuotedLambdaExecution.openTerm (QuotedLambdaExecution.lhs selected context)) = _
  rw [restricted_open, Rigid.instantiate_include]
  exact (current _ (List.mem_singleton_self _)).trans oldValue

theorem source_output_in_every_model {Γ Δ : Ctx sig} (state : State Γ) (context : Context Γ Δ) (redex : Redex Δ)
    (represented : Represents state (context.plug redex.source))
    {Future : Type} {future : Future → MetaArity sig} (candidate : Assignment (active state.1.declarations) future)
    (solved : ContextualFrameUnifier.Models candidate
      (ContextualActivatedStep.problem locals state.1.declarations state.1.occupied (selection state.2)
        (rule state.1.declarations (kind redex) context) state.1.inventory.rows state.1.inventory.configuration)) :
    instantiate candidate (output state.1.declarations state.1.occupied state.2 (kind redex) context) =
      encode future (context.plug redex.target) := by
  have exactOutput := QuotedLambdaExecution.output_for_every_solution context redex
    (restrict Δ (ruleScope state.1.occupied state.2) candidate)
    (restrict_actual_model state (kind redex) context _ represented candidate solved)
  exact (restricted_open Δ _ candidate (QuotedLambdaExecution.rhs (kind redex) context)).symm.trans exactOutput

theorem input_model_recovers_source {Γ Δ : Ctx sig} (state : State Γ) (selected : Kind) (context : Context Γ Δ)
    (source : Term sig Γ .term) (represented : Represents state source)
    {Future : Type} {future : Future → MetaArity sig} (candidate : Assignment (active state.1.declarations) future)
    (solved : ContextualFrameUnifier.Models candidate
      (ContextualActivatedStep.problem locals state.1.declarations state.1.occupied (selection state.2)
        (rule state.1.declarations selected context) state.1.inventory.rows state.1.inventory.configuration)) :
    ∃ redex : Redex Δ, kind redex = selected ∧ source = context.plug redex.source :=
  QuotedLambdaExecution.model_recovers_source selected context source _
    (restrict_actual_model state selected context source represented candidate solved)

theorem schema_covered (scopes : V → Finset Nat) (occupied : Finset Nat) {Γ Δ : Ctx sig}
    (value : Term (signature sig (QuotedLambdaExecution.raw Δ)) Γ .term) :
    Covered (privateScopes scopes) occupied (instantiate (schemaMap captures Δ) value) := by
  apply covered_instantiate
  intro name _
  cases name with
  | inl role =>
      change term (privateScopes scopes) (generator (raw captures) (.inl (Δ, role))) ⊆ occupied
      rw [term_generator]
      exact Finset.empty_subset _
  | inr impossible => exact nomatch impossible

theorem rule_covered {Γ Δ : Ctx sig} (state : State Γ) (selected : Kind) (context : Context Γ Δ) :
    RuleCovered (privateScopes state.1.scopes) state.1.occupied (rule state.1.declarations selected context) := by
  intro value member
  rw [rule, ruleTerms_map] at member
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  exact schema_covered state.1.scopes state.1.occupied original

def destination {Γ Δ : Ctx sig} (state : State Γ) (selected : Kind) (context : Context Γ Δ)
    (valid : ContextualGuardedStep.Valid locals state.1.declarations state.1.occupied (selection state.2)
      (rule state.1.declarations selected context) state.1.inventory.rows state.1.inventory.configuration
      (fun _ => output state.1.declarations state.1.occupied state.2 selected context)) : State Γ :=
  (⟨ScopedVar Local ⊕ state.1.Names, by letI := state.1.equality; infer_instance,
      active state.1.declarations, activeScopes state.1.scopes,
      ContextualActivationScopes.after state.1.occupied (selection state.2),
      afterInventory locals state.1.declarations state.1.occupied (selection state.2)
        (rule state.1.declarations selected context) state.1.inventory
        (fun _ => output state.1.declarations state.1.occupied state.2 selected context),
      afterInventory_covered locals state.1.declarations state.1.scopes state.1.occupied (selection state.2)
        (rule state.1.declarations selected context) state.1.inventory
        (fun _ => output state.1.declarations state.1.occupied state.2 selected context)
        state.1.covered (rule_covered state selected context) valid.occurrences valid.outputs⟩, state.2 + 1)

/-- A client restriction of the existing contextual step, with the target
inventory computed by that step. Its definition contains no source reduction
premise or requirement that the output already represents a source term. -/
def Transition {Γ : Ctx sig} (before after : State Γ) : Prop :=
  ∃ (selected : Kind) (Δ : Ctx sig) (context : Context Γ Δ)
    (valid : ContextualGuardedStep.Valid locals before.1.declarations before.1.occupied (selection before.2)
      (rule before.1.declarations selected context) before.1.inventory.rows before.1.inventory.configuration
      (fun _ => output before.1.declarations before.1.occupied before.2 selected context)),
    after = destination before selected context valid

theorem destination_is_core_step {Γ Δ : Ctx sig} (state : State Γ) (selected : Kind) (context : Context Γ Δ)
    (valid : ContextualGuardedStep.Valid locals state.1.declarations state.1.occupied (selection state.2)
      (rule state.1.declarations selected context) state.1.inventory.rows state.1.inventory.configuration
      (fun _ => output state.1.declarations state.1.occupied state.2 selected context)) :
    ContextualGuardedStep.Step locals state.1.declarations state.1.occupied
      (rule state.1.declarations selected context) state.1.inventory.rows state.1.inventory.configuration
      (fun _ => output state.1.declarations state.1.occupied state.2 selected context)
      (destination state selected context valid).1.inventory.configuration
      (destination state selected context valid).1.inventory.rows (destination state selected context valid).1.occupied :=
  ⟨selection state.2, (ContextualGuardedStep.valid_iff_factors locals state.1.declarations _ _ _ _ _ _).mp valid,
    rfl, rfl, rfl⟩

theorem destination_represents {Γ Δ : Ctx sig} (state : State Γ) (context : Context Γ Δ) (redex : Redex Δ)
    (represented : Represents state (context.plug redex.source))
    (valid : ContextualGuardedStep.Valid locals state.1.declarations state.1.occupied (selection state.2)
      (rule state.1.declarations (kind redex) context) state.1.inventory.rows state.1.inventory.configuration
      (fun _ => output state.1.declarations state.1.occupied state.2 (kind redex) context)) :
    Represents (destination state (kind redex) context valid) (context.plug redex.target) := by
  have consistent := (ContextualFrameUnifier.solvable_iff_consistent
    (source := active state.1.declarations)
    (fun | .term => QuotedLambdaExecution.lam (active state.1.declarations) (.var .zero)) _).mp valid.solvable
  refine ⟨?_, consistent, output state.1.declarations state.1.occupied state.2 (kind redex) context, ?_, ?_⟩
  · change (state.1.inventory.configuration.present \ {state.2}) ∪ {state.2 + 1} = {state.2 + 1}
    rw [represented.1, Finset.sdiff_self, Finset.empty_union]
  · exact ContextualActivatedStep.produced_row_is_shared locals state.1.declarations (selection state.2)
      (fun _ => output state.1.declarations state.1.occupied state.2 (kind redex) context) state.1.inventory.rows
      (List.mem_singleton_self _)
  · intro Future future candidate solved
    exact source_output_in_every_model state context redex represented candidate solved

theorem source_step_preserved {Γ : Ctx sig} {source target : Term sig Γ .term}
    (step : QuotedLambda.Step Γ source target) (state : State Γ) (represented : Represents state source) :
    ∃ after, Transition state after ∧ Represents after target := by
  obtain ⟨Δ, context, redex, rfl, rfl⟩ := QuotedLambda.step_iff_context_redex.mp step
  let valid := valid_of_source state context redex represented
  exact ⟨destination state (kind redex) context valid, ⟨kind redex, Δ, context, valid, rfl⟩,
    destination_represents state context redex represented valid⟩

theorem source_step_reflected {Γ : Ctx sig} {state after : State Γ}
    (transition : Transition state after) (source : Term sig Γ .term) (represented : Represents state source) :
    ∃ target, QuotedLambda.Step Γ source target ∧ Represents after target := by
  obtain ⟨selected, Δ, context, valid, rfl⟩ := transition
  obtain ⟨Future, future, candidate, solved⟩ := valid.solvable
  obtain ⟨redex, rfl, shape⟩ := input_model_recovers_source state selected context source represented candidate solved
  refine ⟨context.plug redex.target, ?_, ?_⟩
  · rw [shape]
    exact context.congr_step redex.step
  · exact destination_represents state context redex (shape ▸ represented) valid

theorem represents_unique {Γ : Ctx sig} {state : State Γ} {first second : Term sig Γ .term}
    (left : Represents state first) (right : Represents state second) : first = second := by
  obtain ⟨_, ⟨candidate, solved⟩, value, isShared, observes⟩ := left
  obtain ⟨_, _, other, otherLive, otherObserves⟩ := right
  have same : value = other := ContextualStoredRows.Row.shared.inj (isShared.symm.trans otherLive)
  have firstValue := observes _ state.1.declarations candidate solved
  have secondValue := otherObserves _ state.1.declarations candidate solved
  rw [← same] at secondValue
  exact Rigid.include_injective _ first second (firstValue.symm.trans secondValue)

theorem source_path_preserved {Γ : Ctx sig} {source target : Term sig Γ .term}
    (path : Relation.ReflTransGen (QuotedLambda.Step Γ) source target)
    (state : State Γ) (represented : Represents state source) :
    ∃ after, Relation.ReflTransGen Transition state after ∧ Represents after target := by
  induction path with
  | refl => exact ⟨state, .refl, represented⟩
  | tail prior step ih =>
      obtain ⟨middle, executed, middleRep⟩ := ih
      obtain ⟨after, transition, result⟩ := source_step_preserved step middle middleRep
      exact ⟨after, executed.tail transition, result⟩

theorem source_path_reflected {Γ : Ctx sig} {state after : State Γ}
    (path : Relation.ReflTransGen Transition state after) (source : Term sig Γ .term)
    (represented : Represents state source) :
    ∃ target, Relation.ReflTransGen (QuotedLambda.Step Γ) source target ∧ Represents after target := by
  induction path with
  | refl => exact ⟨source, .refl, represented⟩
  | tail prior transition ih =>
      obtain ⟨middle, steps, middleRep⟩ := ih
      obtain ⟨target, step, result⟩ := source_step_reflected transition middle middleRep
      exact ⟨target, steps.tail step, result⟩

theorem source_path_iff_execution {Γ : Ctx sig} (state : State Γ)
    (source target : Term sig Γ .term) (represented : Represents state source) :
    Relation.ReflTransGen (QuotedLambda.Step Γ) source target ↔
      ∃ after, Relation.ReflTransGen Transition state after ∧ Represents after target := by
  constructor
  · exact fun path => source_path_preserved path state represented
  · rintro ⟨after, path, result⟩
    obtain ⟨actual, steps, exactResult⟩ := source_path_reflected path source represented
    exact represents_unique exactResult result ▸ steps

def initial {Γ : Ctx sig} (source : Term sig Γ .term) : State Γ := by
  refine (⟨Empty, inferInstance, QuotedLambdaExecution.captures, (fun impossible => nomatch impossible), ∅,
    ⟨⟨[], {0}⟩, (fun _ => .shared (encode QuotedLambdaExecution.captures source)), [], []⟩, ?_⟩, 0)
  refine ⟨Finset.empty_subset _, ?_, Finset.empty_subset _, Finset.empty_subset _⟩
  intro occurrence _
  apply row_shared
  apply (covered_iff _ _ _).mpr
  intro impossible _
  exact nomatch impossible

theorem initial_represents {Γ : Ctx sig} (source : Term sig Γ .term) : Represents (initial source) source := by
  refine ⟨rfl, ⟨generator _, ?_⟩, encode QuotedLambdaExecution.captures source, rfl, ?_⟩
  · intro equation member; cases member
  · intro Future future candidate _
    exact Rigid.instantiate_include candidate source

/-- Every finite mixed source reduction sequence corresponds to a path
through actual retained activation endpoints, and conversely. -/
theorem finite_execution_iff {Γ : Ctx sig} (source target : Term sig Γ .term) :
    Relation.ReflTransGen (QuotedLambda.Step Γ) source target ↔
      ∃ after, Relation.ReflTransGen Transition (initial source) after ∧ Represents after target :=
  source_path_iff_execution (initial source) source target (initial_represents source)

theorem every_old_solution_extends {Γ Δ : Ctx sig} (state : State Γ) (context : Context Γ Δ) (redex : Redex Δ)
    (represented : Represents state (context.plug redex.source))
    (old : Assignment state.1.declarations next)
    (solved : ContextualFrameUnifier.Models old state.1.inventory.configuration.equations) :
    ContextualFrameUnifier.Models (extendModel old redex)
      (ContextualActivatedStep.problem locals state.1.declarations state.1.occupied (selection state.2)
        (rule state.1.declarations (kind redex) context) state.1.inventory.rows state.1.inventory.configuration) ∧
    ∀ {objectContext : Ctx sig} {sort : Srt}
      (value : Term (signature sig state.1.declarations) objectContext sort),
      instantiate (extendModel old redex)
        (instantiate (ContextualSelectionViews.capturedTarget locals state.1.declarations) value) =
      instantiate (ContextualSelectionViews.capturedTarget locals next) (instantiate old value) := by
  obtain ⟨_, _, value, isShared, observes⟩ := represented
  refine ⟨extended_model_solves state context redex value isShared old solved (observes _ next old solved), ?_⟩
  intro objectContext sort value
  rw [← Assignment.instantiate_compose, extendModel_captures, Assignment.instantiate_compose]

theorem equation_count_increases {Γ : Ctx sig} {state after : State Γ}
    (transition : Transition state after) (source : Term sig Γ .term) (represented : Represents state source) :
    after.1.inventory.configuration.equations.length = state.1.inventory.configuration.equations.length + 1 ∧
      after.2 = state.2 + 1 := by
  obtain ⟨selected, Δ, context, valid, rfl⟩ := transition
  obtain ⟨_, _, value, isShared, _⟩ := represented
  constructor
  · change (ContextualActivatedStep.problem locals _ _ _ _ _ _).length = _
    rw [actual_problem state selected context value isShared]
    simp only [List.length_append, ContextualFrameUnifier.mapProblem, List.length_map,
      List.length_cons, List.length_nil, Nat.zero_add]
  · rfl

theorem schema_pattern (captures : V → MetaArity sig) (Δ : Ctx sig) (scope : Nat)
    {Γ : Ctx sig} (selected : Kind) (context : Context Γ Δ) :
    ContextualPatternFragment.Pattern sig (active captures)
      (instantiate (schemaAt captures Δ scope) (QuotedLambdaExecution.lhs selected context)) := by
  unfold QuotedLambdaExecution.lhs
  rw [instantiate_plug]
  apply QuotedLambdaExecution.plug_pattern
  cases selected with
  | beta =>
      simp only [QuotedLambdaExecution.rootInput, QuotedLambdaExecution.app, QuotedLambdaExecution.lam,
        instantiate, instantiateArgs, instantiate_generator, schemaAt]
      exact .rigid (S := sig) Op.app _
        (.cons _ _ (.rigid (S := sig) Op.lam _ (.cons _ _
          (ContextualPatternFragment.generator_pattern _) .nil))
          (.cons _ _ (ContextualPatternFragment.generator_pattern _) .nil))
  | activation =>
      simp only [QuotedLambdaExecution.rootInput, QuotedLambdaExecution.activate, QuotedLambdaExecution.quote,
        instantiate, instantiateArgs, instantiate_generator, schemaAt]
      exact .rigid (S := sig) Op.activate _ (.cons _ _ (.rigid (S := sig) Op.quote _
        (.cons _ _ (ContextualPatternFragment.generator_pattern _) .nil)) .nil)

abbrev scopedLocals (key : ScopedVar Local) : MetaArity sig := locals key.name

theorem lifted_schema {Δ Γ : Ctx sig} (scope : Nat) (change : Assignment captures next)
    (value : Term (signature sig (QuotedLambdaExecution.raw Δ)) Γ .term) :
    instantiate (ContextualStoredRows.liftCaptures scopedLocals change)
      (instantiate (schemaAt captures Δ scope) value) = instantiate (schemaAt next Δ scope) value := by
  rw [instantiate_comp]
  congr 1
  funext name
  cases name with
  | inl role => exact instantiate_generator _ _
  | inr impossible => exact nomatch impossible

abbrev Cache {Γ : Ctx sig} (state : State Γ) :=
  ContextualFrameUpdate.Update (ContextualResidual.observeProblem state.1.inventory.configuration.equations)

def extendedCache {Γ : Ctx sig} (state : State Γ) (cache : Cache state) (complete : cache.remaining = []) :=
  ContextualPrefixModels.completedUpdateWithUnused scopedLocals state.1.inventory.configuration.equations cache complete

def addedProblem {Γ Δ : Ctx sig} (state : State Γ) (selected : Kind) (context : Context Γ Δ) :=
  ContextualResidual.observeProblem (ContextualActivatedStep.addedEquations locals state.1.declarations
    state.1.occupied (selection state.2) (rule state.1.declarations selected context) state.1.inventory.rows)

theorem observed_problem_split {Γ Δ : Ctx sig} (state : State Γ) (selected : Kind) (context : Context Γ Δ) :
    ContextualResidual.observeProblem (ContextualActivatedStep.problem locals state.1.declarations
      state.1.occupied (selection state.2) (rule state.1.declarations selected context)
      state.1.inventory.rows state.1.inventory.configuration) =
    ContextualResidual.observeProblem (ContextualFrameUnifier.mapProblem
      (ContextualPrefixModels.inclusion scopedLocals state.1.declarations) state.1.inventory.configuration.equations) ++
      addedProblem state selected context := by
  rw [ContextualActivatedStep.problem_eq_frame_append]
  exact List.map_append

theorem added_problem_of_shared {Γ Δ : Ctx sig} (state : State Γ) (selected : Kind) (context : Context Γ Δ)
    (value : Term (signature sig state.1.declarations) Γ .term)
    (isShared : state.1.inventory.rows state.2 = .shared value) :
    addedProblem state selected context =
      [(observe (instantiate (schemaAt state.1.declarations Δ (ruleScope state.1.occupied state.2))
          (QuotedLambdaExecution.lhs selected context)),
        observe (instantiate (ContextualSelectionViews.capturedTarget locals state.1.declarations) value))] := by
  have equations := actual_problem state selected context value isShared
  rw [ContextualActivatedStep.problem_eq_frame_append] at equations
  have suffix := List.append_cancel_left equations
  exact congrArg ContextualResidual.observeProblem suffix

/-- The cache reparametrizes the genuinely retained shared input. The result
is a pattern problem because that input is determined by the old equations,
not because compound raw applications were declared to be patterns. -/
theorem cached_problem_is_pattern {Γ Δ : Ctx sig} (state : State Γ) (selected : Kind) (context : Context Γ Δ)
    (source : Term sig Γ .term) (represented : Represents state source)
    (cache : Cache state) (complete : cache.remaining = []) :
    ContextualPatternFragment.ProblemPattern
      ((extendedCache state cache complete).remaining ++
        ContextualResidual.mapProblem (extendedCache state cache complete).answer (addedProblem state selected context)) := by
  obtain ⟨_, _, value, isShared, observes⟩ := represented
  have valueSolved := observes cache.Variables cache.declaration cache.answer
    ((ContextualResidual.models_observeProblem _ _).mp (cache.completed complete))
  change ContextualPatternFragment.ProblemPattern
    (ContextualResidual.mapProblem (ContextualStoredRows.liftCaptures scopedLocals cache.answer) (addedProblem state selected context))
  rw [added_problem_of_shared state selected context value isShared]
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  change ContextualPatternFragment.Pattern sig (active cache.declaration)
      (instantiate (ContextualStoredRows.liftCaptures scopedLocals cache.answer)
        (instantiate (schemaAt state.1.declarations Δ (ruleScope state.1.occupied state.2)) (QuotedLambdaExecution.lhs selected context))) ∧
    ContextualPatternFragment.Pattern sig (active cache.declaration)
      (instantiate (ContextualStoredRows.liftCaptures scopedLocals cache.answer)
        (instantiate (ContextualSelectionViews.capturedTarget locals state.1.declarations) value))
  constructor
  · rw [lifted_schema]
    exact schema_pattern cache.declaration Δ _ selected context
  · have transported := ContextualStoredRows.liftCaptures_on_shared_value scopedLocals cache.answer value
    have exactValue : instantiate (ContextualSelectionViews.capturedSource scopedLocals cache.declaration)
        (instantiate cache.answer value) = encode (active cache.declaration) source := by
      rw [valueSolved, Rigid.instantiate_include]
    exact (transported.trans exactValue).symm ▸ ContextualPatternFragment.rigid_inclusion_pattern _ source

local instance (sort : sig.Srt) : DecidableEq (sig.Op sort) := inferInstanceAs (DecidableEq (Op sort))

/-- Actual incremental solving for the next selected contextual rule. The
completed saved prefix is transported across fresh local declarations;
the original new equations are then run through the existing worklist. -/
def solveCached {Γ Δ : Ctx sig} (state : State Γ) (selected : Kind) (context : Context Γ Δ)
    (cache : Cache state) (complete : cache.remaining = []) (fuel : Nat) :
    ContextualFrameWorklist.Result (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals state.1.declarations state.1.occupied (selection state.2)
        (rule state.1.declarations selected context) state.1.inventory.rows state.1.inventory.configuration)) :=
  ((ContextualFrameWorklist.Result.residual (extendedCache state cache complete)).resume fuel
    (addedProblem state selected context)).cast (observed_problem_split state selected context).symm

theorem solveCached_finishes {Γ Δ : Ctx sig} (state : State Γ) (selected : Kind) (context : Context Γ Δ)
    (source : Term sig Γ .term) (represented : Represents state source)
    (cache : Cache state) (complete : cache.remaining = []) :
    ∃ fuel, ContextualPatternTermination.Finished (solveCached state selected context cache complete fuel) := by
  obtain ⟨fuel, finished⟩ := ContextualPatternTermination.finishes_resuming (extendedCache state cache complete)
    (addedProblem state selected context) (cached_problem_is_pattern state selected context source represented cache complete)
  exact ⟨fuel, finished.cast (observed_problem_split state selected context).symm⟩

theorem solveCached_completes_valid {Γ Δ : Ctx sig} (state : State Γ) (selected : Kind) (context : Context Γ Δ)
    (source : Term sig Γ .term) (represented : Represents state source)
    (cache : Cache state) (complete : cache.remaining = [])
    (valid : ContextualGuardedStep.Valid locals state.1.declarations state.1.occupied (selection state.2)
      (rule state.1.declarations selected context) state.1.inventory.rows state.1.inventory.configuration
      (fun _ => output state.1.declarations state.1.occupied state.2 selected context)) :
    ∃ fuel result, solveCached state selected context cache complete fuel = .residual result ∧ result.remaining = [] := by
  obtain ⟨fuel, finished⟩ := solveCached_finishes state selected context source represented cache complete
  generalize computed : solveCached state selected context cache complete fuel = result at finished
  cases finished with
  | solved result empty => exact ⟨fuel, result, computed, empty⟩
  | refuted proof =>
      obtain ⟨Future, future, candidate, model⟩ := valid.solvable
      exact False.elim (proof future candidate
        ((ContextualResidual.models_observeProblem _ _).mpr model))

def initialCache {Γ : Ctx sig} (source : Term sig Γ .term) : Cache (initial source) :=
  @ContextualFrameWorklist.identity sig Empty inferInstance QuotedLambdaExecution.captures []

theorem initialCache_is_the_actual_zero_run {Γ : Ctx sig} (source : Term sig Γ .term) :
    ContextualFrameWorklist.run 0 QuotedLambdaExecution.captures [] = .residual (initialCache source) := rfl

/-- A retained execution with the actual incremental solver computation at
each event. Neither its constructor nor its cache is supplied a source
reduction or a precomputed source reduct. -/
inductive SolverPath {Γ : Ctx sig} (source : Term sig Γ .term) :
    (state : State Γ) → Cache state → Prop where
  | initial : SolverPath source (initial source) (initialCache source)
  | step {state : State Γ} {cache : Cache state} (prior : SolverPath source state cache)
      (complete : cache.remaining = []) {Δ : Ctx sig} (selected : Kind) (context : Context Γ Δ)
      (valid : ContextualGuardedStep.Valid locals state.1.declarations state.1.occupied (selection state.2)
        (rule state.1.declarations selected context) state.1.inventory.rows state.1.inventory.configuration
        (fun _ => output state.1.declarations state.1.occupied state.2 selected context))
      (fuel : Nat) (nextCache : Cache (destination state selected context valid))
      (computed : solveCached state selected context cache complete fuel = .residual nextCache)
      (finished : nextCache.remaining = []) :
      SolverPath source (destination state selected context valid) nextCache

theorem SolverPath.complete {Γ : Ctx sig} {source : Term sig Γ .term} {state : State Γ} {cache : Cache state}
    (path : SolverPath source state cache) : cache.remaining = [] := by
  cases path with
  | initial => rfl
  | step prior complete selected context valid fuel nextCache computed finished => exact finished

theorem SolverPath.semantic {Γ : Ctx sig} {source : Term sig Γ .term} {state : State Γ} {cache : Cache state}
    (path : SolverPath source state cache) : Relation.ReflTransGen Transition (QuotedLambdaRetained.initial source) state := by
  induction path with
  | initial => exact .refl
  | step prior complete selected context valid fuel nextCache computed finished ih =>
      exact ih.tail ⟨selected, _, context, valid, rfl⟩

theorem source_path_with_actual_solvers {Γ : Ctx sig} {source target : Term sig Γ .term}
    (path : Relation.ReflTransGen (QuotedLambda.Step Γ) source target) :
    ∃ state cache, SolverPath source state cache ∧ Represents state target := by
  induction path with
  | refl => exact ⟨initial source, initialCache source, .initial, initial_represents source⟩
  | tail prior step ih =>
      obtain ⟨state, cache, computedPast, represented⟩ := ih
      obtain ⟨Δ, context, redex, rfl, rfl⟩ := QuotedLambda.step_iff_context_redex.mp step
      let valid := valid_of_source state context redex represented
      obtain ⟨fuel, nextCache, computed, finished⟩ := solveCached_completes_valid state (kind redex) context
        _ represented cache computedPast.complete valid
      exact ⟨destination state (kind redex) context valid, nextCache,
        .step computedPast computedPast.complete (kind redex) context valid fuel nextCache computed finished,
        destination_represents state context redex represented valid⟩

/-- The complete finite-path comparison for this mixed source profile:
actual worklist histories, earlier constraints and raw scoped endpoints
are retained across both beta reduction and explicit activation. -/
theorem finite_execution_with_solvers_iff {Γ : Ctx sig} (source target : Term sig Γ .term) :
    Relation.ReflTransGen (QuotedLambda.Step Γ) source target ↔
      ∃ state cache, SolverPath source state cache ∧ Represents state target := by
  constructor
  · exact source_path_with_actual_solvers
  · rintro ⟨state, cache, path, result⟩
    exact (finite_execution_iff source target).mpr ⟨state, path.semantic, result⟩

theorem completed_cached_return_is_source {Γ Δ : Ctx sig} (state : State Γ) (selected : Kind) (context : Context Γ Δ)
    (source : Term sig Γ .term) (represented : Represents state source)
    (cache : Cache state) (complete : cache.remaining = []) (fuel : Nat)
    (result : ContextualFrameUpdate.Update (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals state.1.declarations state.1.occupied (selection state.2)
        (rule state.1.declarations selected context) state.1.inventory.rows state.1.inventory.configuration)))
    (_computed : solveCached state selected context cache complete fuel = .residual result)
    (finished : result.remaining = []) :
    ∃ target, QuotedLambda.Step Γ source target ∧
      instantiate result.answer (output state.1.declarations state.1.occupied state.2 selected context) =
        encode result.declaration target := by
  have model := (ContextualResidual.models_observeProblem _ _).mp (result.completed finished)
  obtain ⟨redex, sameKind, shape⟩ := input_model_recovers_source state selected context source represented result.answer model
  subst selected
  refine ⟨context.plug redex.target, ?_, ?_⟩
  · rw [shape]
    exact context.congr_step redex.step
  · exact source_output_in_every_model state context redex (shape ▸ represented) result.answer model

theorem solveCached_refutes_inert_source {Γ Δ : Ctx sig} (state : State Γ) (selected : Kind) (context : Context Γ Δ)
    (source : Term sig Γ .term) (represented : Represents state source)
    (cache : Cache state) (complete : cache.remaining = [])
    (inert : ∀ target, ¬ QuotedLambda.Step Γ source target) :
    ∃ fuel proof, solveCached state selected context cache complete fuel = .refuted proof := by
  obtain ⟨fuel, finished⟩ := solveCached_finishes state selected context source represented cache complete
  generalize computed : solveCached state selected context cache complete fuel = result at finished
  cases finished with
  | solved result empty =>
      obtain ⟨target, step, _⟩ := completed_cached_return_is_source state selected context source represented
        cache complete fuel result computed empty
      exact False.elim (inert target step)
  | refuted proof => exact ⟨fuel, proof, computed⟩

/-- The conservative extension agrees with the already qualified pure-lambda
solver-path comparison. This compares represented source answers; it does
not identify the two clients' private declaration tables. -/
theorem pure_fragment_agrees_with_original_execution {Γ : Ctx sig}
    (source target : Term LambdaContextualRung.sig Γ .term) :
    (∃ state cache, SolverPath (QuotedLambda.includeLambda source) state cache ∧
      Represents state (QuotedLambda.includeLambda target)) ↔
    (∃ state cache, LambdaExecution.SolverPath source state cache ∧ LambdaExecution.Represents state target) :=
  ((finite_execution_with_solvers_iff (QuotedLambda.includeLambda source) (QuotedLambda.includeLambda target)).symm.trans
    (QuotedLambda.pure_lambda_paths_iff source target).symm).trans
      (LambdaExecution.finite_execution_with_solvers_iff source target)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.QuotedLambdaRetained
