import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LambdaComparison
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionEndpoints
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixPrincipals

/-!
# Retained contextual states for ordinary lambda reduction

All object contexts use one declaration family. Each event freshens its
schema, consumes the current program occurrence and emits its contextual
application. Earlier equations, shared values and the scope inventory use
the existing activation operations. In particular, reading a source reduct
does not replace the actual stored term by a fresh encoding.

The selected one-step worklist realization is in `LambdaComparison`.
The finite-path comparison here includes actual incremental solver runs:
a completed prefix is transported across each fresh local frame, and its
answer exposes the next ordinary source input as a structural pattern.
The context-indexed rule family does not choose a demanded evaluation
strategy or supply the effects and sharing of the full Prime language.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LambdaExecution

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open LambdaContextualRung (sig Srt Context appT lamT)
open LambdaComparison (encode app lam plug instantiate_encode instantiate_plug instantiate_inst
  encode_inst plug_encode app_inj lam_inj plug_injective plug_recovers encode_app_recovers encode_lam_recovers)
open Mettapedia.Logic.LP (ScopedVar)
open ContextualWorldScopeLedger ContextualScopeSupport

local instance : DecidableEq sig.Srt := inferInstanceAs (DecidableEq Srt)

abbrev Local := Ctx sig × Bool
abbrev locals (key : Local) : MetaArity sig := LambdaComparison.locals key.1 key.2

variable {V W : Type} (captures : V → MetaArity sig)

abbrev raw := ContextualActivatedStep.source locals captures
abbrev active := ContextualActivatedStep.target locals captures

def schemaMap (Δ : Ctx sig) : Assignment (LambdaComparison.raw Δ) (raw captures)
  | .inl role => generator (raw captures) (.inl (Δ, role))
  | .inr impossible => nomatch impossible

def schemaAt (Δ : Ctx sig) (scope : Nat) : Assignment (LambdaComparison.raw Δ) (active captures)
  | .inl role => generator (active captures) (.inl ⟨scope, (Δ, role)⟩)
  | .inr impossible => nomatch impossible

theorem fresh_schema_map (Δ : Ctx sig) (scope : Nat) {Γ : Ctx sig}
    (term : Term (signature sig (LambdaComparison.raw Δ)) Γ .term) :
    ContextualFreshening.termAt locals captures scope (instantiate (schemaMap captures Δ) term) =
      instantiate (schemaAt captures Δ scope) term := by
  unfold ContextualFreshening.termAt
  rw [instantiate_comp]
  congr 1
  funext key
  cases key with
  | inl role => exact instantiate_generator _ _
  | inr impossible => exact nomatch impossible

def rule {Γ Δ : Ctx sig} (context : Context Γ Δ) : RuleInstance (Term (signature sig (raw captures)) Γ .term) :=
  (LambdaComparison.rule context).map (instantiate (schemaMap captures Δ))

def selection (current : Nat) : Selection Nat := ⟨[current], [], [current + 1]⟩

def ruleScope (occupied : Finset Nat) (current : Nat) :=
  ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.rulePort (selection current))

def output {Γ Δ : Ctx sig} (occupied : Finset Nat) (current : Nat) (context : Context Γ Δ) :
    Term (signature sig (active captures)) Γ .term :=
  instantiate (schemaAt captures Δ (ruleScope occupied current)) (LambdaComparison.rhs context)

theorem opened_lhs {Γ Δ : Ctx sig} (scope : Nat) (context : Context Γ Δ) :
    instantiate (schemaAt captures Δ scope) (LambdaComparison.lhs context) =
      plug (active captures) context
        (app (active captures) (lam (active captures) (generator (active captures) (.inl ⟨scope, (Δ, false)⟩)))
          (generator (active captures) (.inl ⟨scope, (Δ, true)⟩))) := by
  unfold LambdaComparison.lhs
  rw [instantiate_plug]
  simp only [app, lam, instantiate, instantiateArgs, instantiate_generator, schemaAt]

theorem opened_rhs {Γ Δ : Ctx sig} (scope : Nat) (context : Context Γ Δ) :
    instantiate (schemaAt captures Δ scope) (LambdaComparison.rhs context) =
      plug (active captures) context
        (inst (generator (active captures) (.inl ⟨scope, (Δ, false)⟩))
          (generator (active captures) (.inl ⟨scope, (Δ, true)⟩))) := by
  unfold LambdaComparison.rhs
  rw [instantiate_plug, instantiate_inst, instantiate_generator, instantiate_generator]
  rfl

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

theorem actual_problem {Γ Δ : Ctx sig} (state : State Γ) (context : Context Γ Δ)
    (value : Term (signature sig state.1.declarations) Γ .term)
    (isShared : state.1.inventory.rows state.2 = .shared value) :
    ContextualActivatedStep.problem locals state.1.declarations state.1.occupied (selection state.2)
        (rule state.1.declarations context) state.1.inventory.rows state.1.inventory.configuration =
      ContextualFrameUnifier.mapProblem (ContextualSelectionViews.capturedTarget locals state.1.declarations)
        state.1.inventory.configuration.equations ++
      [(instantiate (schemaAt state.1.declarations Δ (ruleScope state.1.occupied state.2)) (LambdaComparison.lhs context),
        instantiate (ContextualSelectionViews.capturedTarget locals state.1.declarations) value)] := by
  change _ ++ [(ContextualFreshening.termAt locals _ _ (instantiate (schemaMap _ _) (LambdaComparison.lhs context)),
    ContextualFreshening.termAt locals _ _ (ContextualStoredRows.asTemplate locals _ (state.1.inventory.rows state.2)))] ++ [] ++ [] = _
  rw [isShared, fresh_schema_map]
  simp only [ContextualStoredRows.asTemplate, List.append_nil]
  rw [← ContextualSelectionViews.shared_value_at_port locals state.1.declarations state.1.occupied
    (ContextualActivationScopes.takePort (selection state.2) ⟨0, by simp [selection]⟩) value]
  rfl

theorem admission {Γ Δ : Ctx sig} (state : State Γ) (context : Context Γ Δ)
    (present : state.1.inventory.configuration.present = {state.2}) :
    ContextualGuardedStep.Requirements locals state.1.declarations state.1.occupied (selection state.2)
      (rule state.1.declarations context) state.1.inventory.rows state.1.inventory.configuration
      (fun _ => output state.1.declarations state.1.occupied state.2 context) := by
  refine ⟨by simp [selection], by simp [selection], rfl, rfl, ?_, ?_, ?_⟩
  · change [_] = [ContextualFreshening.termAt locals _ _ (instantiate (schemaMap _ _) (LambdaComparison.rhs context))]
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
    (body : Term sig (.term :: Δ) .term) (argument : Term sig Δ .term) :
    Assignment (active captures) (active next)
  | .inr name => instantiate (ContextualSelectionViews.capturedTarget locals next) (old name)
  | .inl ⟨scope, (context, false)⟩ =>
      if same : context = Δ then same.symm ▸ encode (active next) body
      else generator (active next) (.inl ⟨scope, (context, false)⟩)
  | .inl ⟨scope, (context, true)⟩ =>
      if same : context = Δ then same.symm ▸ encode (active next) argument
      else generator (active next) (.inl ⟨scope, (context, true)⟩)

theorem extendModel_captures (old : Assignment captures next) {Δ : Ctx sig}
    (body : Term sig (.term :: Δ) .term) (argument : Term sig Δ .term) :
    Assignment.compose (extendModel old body argument) (ContextualSelectionViews.capturedTarget locals captures) =
      Assignment.compose (ContextualSelectionViews.capturedTarget locals next) old := by
  funext name
  rw [Assignment.compose, ContextualSelectionViews.capturedTarget, instantiate_generator]
  rfl

theorem extended_model_solves {Γ Δ : Ctx sig} (state : State Γ) (context : Context Γ Δ)
    (body : Term sig (.term :: Δ) .term) (argument : Term sig Δ .term)
    (value : Term (signature sig state.1.declarations) Γ .term)
    (isShared : state.1.inventory.rows state.2 = .shared value)
    (old : Assignment state.1.declarations next)
    (solved : ContextualFrameUnifier.Models old state.1.inventory.configuration.equations)
    (observed : instantiate old value = encode next (context.plug (appT (lamT body) argument))) :
    ContextualFrameUnifier.Models (extendModel old body argument)
      (ContextualActivatedStep.problem locals state.1.declarations state.1.occupied (selection state.2)
        (rule state.1.declarations context) state.1.inventory.rows state.1.inventory.configuration) := by
  rw [actual_problem state context value isShared]
  apply (ContextualFrameUnifier.models_append _ _ _).mpr
  constructor
  · apply (ContextualFrameUnifier.models_mapProblem _ _ _).mpr
    rw [extendModel_captures]
    exact ContextualFrameUnifier.models_compose solved _
  · intro equation member
    have only := List.mem_singleton.mp member
    subst equation
    dsimp only [Prod.fst, Prod.snd]
    rw [opened_lhs, instantiate_plug, ← Assignment.instantiate_compose,
      extendModel_captures, Assignment.instantiate_compose, observed, instantiate_encode]
    simp only [app, lam, instantiate, instantiateArgs, instantiate_generator, extendModel, dite_true]
    exact plug_encode _ context (appT (lamT body) argument)

theorem valid_of_source {Γ Δ : Ctx sig} (state : State Γ) (context : Context Γ Δ)
    (body : Term sig (.term :: Δ) .term) (argument : Term sig Δ .term)
    (represented : Represents state (context.plug (appT (lamT body) argument))) :
    ContextualGuardedStep.Valid locals state.1.declarations state.1.occupied (selection state.2)
      (rule state.1.declarations context) state.1.inventory.rows state.1.inventory.configuration
      (fun _ => output state.1.declarations state.1.occupied state.2 context) := by
  obtain ⟨present, ⟨old, solved⟩, value, isShared, observes⟩ := represented
  have formation := admission state context present
  refine ⟨formation, ?_⟩
  exact ContextualFrameUnifier.solvable_of_model
    (extended_model_solves state context body argument value isShared old solved
      (observes _ state.1.declarations old solved))

theorem source_output_in_every_model {Γ Δ : Ctx sig} (state : State Γ) (context : Context Γ Δ)
    (body : Term sig (.term :: Δ) .term) (argument : Term sig Δ .term)
    (represented : Represents state (context.plug (appT (lamT body) argument)))
    {Future : Type} {future : Future → MetaArity sig} (candidate : Assignment (active state.1.declarations) future)
    (solved : ContextualFrameUnifier.Models candidate
      (ContextualActivatedStep.problem locals state.1.declarations state.1.occupied (selection state.2)
        (rule state.1.declarations context) state.1.inventory.rows state.1.inventory.configuration)) :
    instantiate candidate (output state.1.declarations state.1.occupied state.2 context) =
      encode future (context.plug (inst body argument)) := by
  obtain ⟨_, _, value, isShared, observes⟩ := represented
  rw [actual_problem state context value isShared] at solved
  obtain ⟨old, selected⟩ := (ContextualFrameUnifier.models_append _ _ _).mp solved
  have oldModel := (ContextualFrameUnifier.models_mapProblem _ _ _).mp old
  have oldValue := observes Future future _ oldModel
  rw [Assignment.instantiate_compose] at oldValue
  have matched := selected _ (List.mem_singleton_self _)
  dsimp only [Prod.fst, Prod.snd] at matched
  rw [opened_lhs, instantiate_plug, oldValue, ← plug_encode] at matched
  have root := plug_injective context matched
  have parts := app_inj root
  have body_eq := lam_inj parts.1
  unfold output
  rw [opened_rhs, instantiate_plug, instantiate_inst, body_eq, parts.2, ← encode_inst, plug_encode]

theorem schema_covered (scopes : V → Finset Nat) (occupied : Finset Nat) {Γ Δ : Ctx sig}
    (value : Term (signature sig (LambdaComparison.raw Δ)) Γ .term) :
    Covered (privateScopes scopes) occupied (instantiate (schemaMap captures Δ) value) := by
  apply covered_instantiate
  intro name _
  cases name with
  | inl role =>
      change term (privateScopes scopes) (generator (raw captures) (.inl (Δ, role))) ⊆ occupied
      rw [term_generator]
      exact Finset.empty_subset _
  | inr impossible => exact nomatch impossible

theorem rule_covered {Γ Δ : Ctx sig} (state : State Γ) (context : Context Γ Δ) :
    RuleCovered (privateScopes state.1.scopes) state.1.occupied (rule state.1.declarations context) := by
  intro value member
  rw [rule, ruleTerms_map] at member
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  exact schema_covered state.1.scopes state.1.occupied original

def destination {Γ Δ : Ctx sig} (state : State Γ) (context : Context Γ Δ)
    (valid : ContextualGuardedStep.Valid locals state.1.declarations state.1.occupied (selection state.2)
      (rule state.1.declarations context) state.1.inventory.rows state.1.inventory.configuration
      (fun _ => output state.1.declarations state.1.occupied state.2 context)) : State Γ :=
  (⟨ScopedVar Local ⊕ state.1.Names, by letI := state.1.equality; infer_instance,
      active state.1.declarations, activeScopes state.1.scopes,
      ContextualActivationScopes.after state.1.occupied (selection state.2),
      afterInventory locals state.1.declarations state.1.occupied (selection state.2)
        (rule state.1.declarations context) state.1.inventory
        (fun _ => output state.1.declarations state.1.occupied state.2 context),
      afterInventory_covered locals state.1.declarations state.1.scopes state.1.occupied (selection state.2)
        (rule state.1.declarations context) state.1.inventory
        (fun _ => output state.1.declarations state.1.occupied state.2 context)
        state.1.covered (rule_covered state context) valid.occurrences valid.outputs⟩, state.2 + 1)

/-- A client restriction of the existing contextual step, with the target
inventory computed by that step. Its definition contains no source reduction
premise or requirement that the output already represents a source term. -/
def Transition {Γ : Ctx sig} (before after : State Γ) : Prop :=
  ∃ (Δ : Ctx sig) (context : Context Γ Δ)
    (valid : ContextualGuardedStep.Valid locals before.1.declarations before.1.occupied (selection before.2)
      (rule before.1.declarations context) before.1.inventory.rows before.1.inventory.configuration
      (fun _ => output before.1.declarations before.1.occupied before.2 context)),
    after = destination before context valid

theorem destination_is_core_step {Γ Δ : Ctx sig} (state : State Γ) (context : Context Γ Δ)
    (valid : ContextualGuardedStep.Valid locals state.1.declarations state.1.occupied (selection state.2)
      (rule state.1.declarations context) state.1.inventory.rows state.1.inventory.configuration
      (fun _ => output state.1.declarations state.1.occupied state.2 context)) :
    ContextualGuardedStep.Step locals state.1.declarations state.1.occupied
      (rule state.1.declarations context) state.1.inventory.rows state.1.inventory.configuration
      (fun _ => output state.1.declarations state.1.occupied state.2 context)
      (destination state context valid).1.inventory.configuration
      (destination state context valid).1.inventory.rows (destination state context valid).1.occupied :=
  ⟨selection state.2, (ContextualGuardedStep.valid_iff_factors locals state.1.declarations _ _ _ _ _ _).mp valid,
    rfl, rfl, rfl⟩

theorem destination_represents {Γ Δ : Ctx sig} (state : State Γ) (context : Context Γ Δ)
    (body : Term sig (.term :: Δ) .term) (argument : Term sig Δ .term)
    (represented : Represents state (context.plug (appT (lamT body) argument)))
    (valid : ContextualGuardedStep.Valid locals state.1.declarations state.1.occupied (selection state.2)
      (rule state.1.declarations context) state.1.inventory.rows state.1.inventory.configuration
      (fun _ => output state.1.declarations state.1.occupied state.2 context)) :
    Represents (destination state context valid) (context.plug (inst body argument)) := by
  have consistent := (ContextualFrameUnifier.solvable_iff_consistent
    (source := active state.1.declarations)
    (fun | .term => lam (active state.1.declarations) (.var .zero)) _).mp valid.solvable
  refine ⟨?_, consistent, output state.1.declarations state.1.occupied state.2 context, ?_, ?_⟩
  · change (state.1.inventory.configuration.present \ {state.2}) ∪ {state.2 + 1} = {state.2 + 1}
    rw [represented.1, Finset.sdiff_self, Finset.empty_union]
  · exact ContextualActivatedStep.produced_row_is_shared locals state.1.declarations (selection state.2)
      (fun _ => output state.1.declarations state.1.occupied state.2 context) state.1.inventory.rows
      (List.mem_singleton_self _)
  · intro Future future candidate solved
    exact source_output_in_every_model state context body argument represented candidate solved

theorem source_step_preserved {Γ : Ctx sig} {source target : Term sig Γ .term}
    (step : LambdaContextualRung.Step Γ source target) (state : State Γ) (represented : Represents state source) :
    ∃ after, Transition state after ∧ Represents after target := by
  obtain ⟨Δ, context, body, argument, rfl, rfl⟩ := LambdaContextualRung.step_iff_context_beta.mp step
  let valid := valid_of_source state context body argument represented
  exact ⟨destination state context valid, ⟨Δ, context, valid, rfl⟩,
    destination_represents state context body argument represented valid⟩

theorem input_model_recovers_source {Γ Δ : Ctx sig} (state : State Γ) (context : Context Γ Δ)
    (source : Term sig Γ .term) (represented : Represents state source)
    {Future : Type} {future : Future → MetaArity sig} (candidate : Assignment (active state.1.declarations) future)
    (solved : ContextualFrameUnifier.Models candidate
      (ContextualActivatedStep.problem locals state.1.declarations state.1.occupied (selection state.2)
        (rule state.1.declarations context) state.1.inventory.rows state.1.inventory.configuration)) :
    ∃ (body : Term sig (.term :: Δ) .term) (argument : Term sig Δ .term),
      source = context.plug (appT (lamT body) argument) := by
  obtain ⟨_, _, value, isShared, observes⟩ := represented
  rw [actual_problem state context value isShared] at solved
  obtain ⟨old, selected⟩ := (ContextualFrameUnifier.models_append _ _ _).mp solved
  have oldModel := (ContextualFrameUnifier.models_mapProblem _ _ _).mp old
  have oldValue := observes Future future _ oldModel
  rw [Assignment.instantiate_compose] at oldValue
  have matched := selected _ (List.mem_singleton_self _)
  dsimp only [Prod.fst, Prod.snd] at matched
  rw [opened_lhs, instantiate_plug, oldValue] at matched
  obtain ⟨inner, source_eq, root_eq⟩ := plug_recovers context _ source matched
  obtain ⟨function, argument, root_eq, function_eq, _⟩ := encode_app_recovers inner _ _ root_eq
  obtain ⟨body, function_eq, _⟩ := encode_lam_recovers function _ function_eq
  exact ⟨body, argument, by rw [source_eq, root_eq, function_eq]⟩

theorem source_step_reflected {Γ : Ctx sig} {state after : State Γ}
    (transition : Transition state after) (source : Term sig Γ .term) (represented : Represents state source) :
    ∃ target, LambdaContextualRung.Step Γ source target ∧ Represents after target := by
  obtain ⟨Δ, context, valid, rfl⟩ := transition
  obtain ⟨Future, future, candidate, solved⟩ := valid.solvable
  obtain ⟨body, argument, source_shape⟩ := input_model_recovers_source state context source represented candidate solved
  refine ⟨context.plug (inst body argument), ?_, ?_⟩
  · rw [source_shape]
    exact context.congr_step (.beta body argument)
  · exact destination_represents state context body argument (source_shape ▸ represented) valid

theorem represents_unique {Γ : Ctx sig} {state : State Γ} {first second : Term sig Γ .term}
    (left : Represents state first) (right : Represents state second) : first = second := by
  obtain ⟨_, ⟨candidate, solved⟩, value, isShared, observes⟩ := left
  obtain ⟨_, _, other, otherLive, otherObserves⟩ := right
  have same : value = other := ContextualStoredRows.Row.shared.inj (isShared.symm.trans otherLive)
  have firstValue := observes _ state.1.declarations candidate solved
  have secondValue := otherObserves _ state.1.declarations candidate solved
  rw [← same] at secondValue
  exact LambdaComparison.encode_injective first second (firstValue.symm.trans secondValue)

theorem source_step_iff_transition {Γ : Ctx sig} (state : State Γ)
    (source target : Term sig Γ .term) (represented : Represents state source) :
    LambdaContextualRung.Step Γ source target ↔ ∃ after, Transition state after ∧ Represents after target := by
  constructor
  · exact fun step => source_step_preserved step state represented
  · rintro ⟨after, transition, result⟩
    obtain ⟨actual, step, exactResult⟩ := source_step_reflected transition source represented
    exact represents_unique exactResult result ▸ step

theorem source_path_preserved {Γ : Ctx sig} {source target : Term sig Γ .term}
    (path : Relation.ReflTransGen (LambdaContextualRung.Step Γ) source target)
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
    ∃ target, Relation.ReflTransGen (LambdaContextualRung.Step Γ) source target ∧ Represents after target := by
  induction path with
  | refl => exact ⟨source, .refl, represented⟩
  | tail prior transition ih =>
      obtain ⟨middle, steps, middleRep⟩ := ih
      obtain ⟨target, step, result⟩ := source_step_reflected transition middle middleRep
      exact ⟨target, steps.tail step, result⟩

theorem source_path_iff_execution {Γ : Ctx sig} (state : State Γ)
    (source target : Term sig Γ .term) (represented : Represents state source) :
    Relation.ReflTransGen (LambdaContextualRung.Step Γ) source target ↔
      ∃ after, Relation.ReflTransGen Transition state after ∧ Represents after target := by
  constructor
  · exact fun path => source_path_preserved path state represented
  · rintro ⟨after, path, result⟩
    obtain ⟨actual, steps, exactResult⟩ := source_path_reflected path source represented
    exact represents_unique exactResult result ▸ steps

def initial {Γ : Ctx sig} (source : Term sig Γ .term) : State Γ := by
  refine (⟨Empty, inferInstance, LambdaComparison.captures, (fun impossible => nomatch impossible), ∅,
    ⟨⟨[], {0}⟩, (fun _ => .shared (encode LambdaComparison.captures source)), [], []⟩, ?_⟩, 0)
  refine ⟨Finset.empty_subset _, ?_, Finset.empty_subset _, Finset.empty_subset _⟩
  intro occurrence _
  apply row_shared
  apply (covered_iff _ _ _).mpr
  intro impossible _
  exact nomatch impossible

theorem initial_represents {Γ : Ctx sig} (source : Term sig Γ .term) :
    Represents (initial source) source := by
  refine ⟨rfl, ⟨generator _, ?_⟩, encode LambdaComparison.captures source, rfl, ?_⟩
  · intro equation member; cases member
  · intro Future future candidate _
    exact instantiate_encode candidate source

/-- Finite source programs and finite paths in the selected transform
profile have exactly the same represented answers. Intermediate endpoints
are the original activation results with their equations and inventories. -/
theorem finite_execution_iff {Γ : Ctx sig} (source target : Term sig Γ .term) :
    Relation.ReflTransGen (LambdaContextualRung.Step Γ) source target ↔
      ∃ after, Relation.ReflTransGen Transition (initial source) after ∧ Represents after target :=
  source_path_iff_execution (initial source) source target (initial_represents source)

/-- Each old joint solution extends through a source reduction. The new
solution agrees with it on every old term, after the explicit declaration
inclusion. This is stronger than preserving each old variable's marginal. -/
theorem every_old_solution_extends {Γ Δ : Ctx sig} (state : State Γ) (context : Context Γ Δ)
    (body : Term sig (.term :: Δ) .term) (argument : Term sig Δ .term)
    (represented : Represents state (context.plug (appT (lamT body) argument)))
    (old : Assignment state.1.declarations next)
    (solved : ContextualFrameUnifier.Models old state.1.inventory.configuration.equations) :
    ContextualFrameUnifier.Models (extendModel old body argument)
      (ContextualActivatedStep.problem locals state.1.declarations state.1.occupied (selection state.2)
        (rule state.1.declarations context) state.1.inventory.rows state.1.inventory.configuration) ∧
    ∀ {objectContext : Ctx sig} {sort : Srt}
      (value : Term (signature sig state.1.declarations) objectContext sort),
      instantiate (extendModel old body argument)
        (instantiate (ContextualSelectionViews.capturedTarget locals state.1.declarations) value) =
      instantiate (ContextualSelectionViews.capturedTarget locals next) (instantiate old value) := by
  obtain ⟨_, _, value, isShared, observes⟩ := represented
  refine ⟨extended_model_solves state context body argument value isShared old solved (observes _ next old solved), ?_⟩
  intro objectContext sort value
  rw [← Assignment.instantiate_compose, extendModel_captures, Assignment.instantiate_compose]

theorem equation_count_increases {Γ : Ctx sig} {state after : State Γ}
    (transition : Transition state after) (source : Term sig Γ .term) (represented : Represents state source) :
    after.1.inventory.configuration.equations.length = state.1.inventory.configuration.equations.length + 1 ∧
      after.2 = state.2 + 1 := by
  obtain ⟨Δ, context, valid, rfl⟩ := transition
  obtain ⟨_, _, value, isShared, _⟩ := represented
  constructor
  · change (ContextualActivatedStep.problem locals _ _ _ _ _ _).length = _
    rw [actual_problem state context value isShared]
    simp only [List.length_append, ContextualFrameUnifier.mapProblem, List.length_map,
      List.length_cons, List.length_nil, Nat.zero_add]
  · rfl

abbrev scopedLocals (key : ScopedVar Local) : MetaArity sig := locals key.name

theorem lifted_schema {Δ Γ : Ctx sig} (scope : Nat) (change : Assignment captures next)
    (value : Term (signature sig (LambdaComparison.raw Δ)) Γ .term) :
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

def addedProblem {Γ Δ : Ctx sig} (state : State Γ) (context : Context Γ Δ) :=
  ContextualResidual.observeProblem (ContextualActivatedStep.addedEquations locals state.1.declarations
    state.1.occupied (selection state.2) (rule state.1.declarations context) state.1.inventory.rows)

theorem observed_problem_split {Γ Δ : Ctx sig} (state : State Γ) (context : Context Γ Δ) :
    ContextualResidual.observeProblem (ContextualActivatedStep.problem locals state.1.declarations
      state.1.occupied (selection state.2) (rule state.1.declarations context)
      state.1.inventory.rows state.1.inventory.configuration) =
    ContextualResidual.observeProblem (ContextualFrameUnifier.mapProblem
      (ContextualPrefixModels.inclusion scopedLocals state.1.declarations) state.1.inventory.configuration.equations) ++
      addedProblem state context := by
  rw [ContextualActivatedStep.problem_eq_frame_append]
  exact List.map_append

theorem added_problem_of_shared {Γ Δ : Ctx sig} (state : State Γ) (context : Context Γ Δ)
    (value : Term (signature sig state.1.declarations) Γ .term)
    (isShared : state.1.inventory.rows state.2 = .shared value) :
    addedProblem state context =
      [(observe (instantiate (schemaAt state.1.declarations Δ (ruleScope state.1.occupied state.2))
          (LambdaComparison.lhs context)),
        observe (instantiate (ContextualSelectionViews.capturedTarget locals state.1.declarations) value))] := by
  have equations := actual_problem state context value isShared
  rw [ContextualActivatedStep.problem_eq_frame_append] at equations
  have suffix := List.append_cancel_left equations
  exact congrArg ContextualResidual.observeProblem suffix

/-- The cache reparametrizes the genuinely retained shared input. The result
is a pattern problem because that input is determined by the old equations,
not because compound raw applications were declared to be patterns. -/
theorem cached_problem_is_pattern {Γ Δ : Ctx sig} (state : State Γ) (context : Context Γ Δ)
    (source : Term sig Γ .term) (represented : Represents state source)
    (cache : Cache state) (complete : cache.remaining = []) :
    ContextualPatternFragment.ProblemPattern
      ((extendedCache state cache complete).remaining ++
        ContextualResidual.mapProblem (extendedCache state cache complete).answer (addedProblem state context)) := by
  obtain ⟨_, _, value, isShared, observes⟩ := represented
  have valueSolved := observes cache.Variables cache.declaration cache.answer
    ((ContextualResidual.models_observeProblem _ _).mp (cache.completed complete))
  change ContextualPatternFragment.ProblemPattern
    (ContextualResidual.mapProblem (ContextualStoredRows.liftCaptures scopedLocals cache.answer) (addedProblem state context))
  rw [added_problem_of_shared state context value isShared]
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  change ContextualPatternFragment.Pattern sig (active cache.declaration)
      (instantiate (ContextualStoredRows.liftCaptures scopedLocals cache.answer)
        (instantiate (schemaAt state.1.declarations Δ (ruleScope state.1.occupied state.2)) (LambdaComparison.lhs context))) ∧
    ContextualPatternFragment.Pattern sig (active cache.declaration)
      (instantiate (ContextualStoredRows.liftCaptures scopedLocals cache.answer)
        (instantiate (ContextualSelectionViews.capturedTarget locals state.1.declarations) value))
  constructor
  · rw [lifted_schema, opened_lhs]
    apply LambdaComparison.plug_pattern
    exact .rigid (S := sig) LambdaContextualRung.Op.app _
      (.cons _ _ (.rigid (S := sig) LambdaContextualRung.Op.lam _
        (.cons _ _ (ContextualPatternFragment.generator_pattern _) .nil))
        (.cons _ _ (ContextualPatternFragment.generator_pattern _) .nil))
  · have transported := ContextualStoredRows.liftCaptures_on_shared_value scopedLocals cache.answer value
    have exactValue : instantiate (ContextualSelectionViews.capturedSource scopedLocals cache.declaration)
        (instantiate cache.answer value) = encode (active cache.declaration) source := by
      rw [valueSolved, instantiate_encode]
    exact (transported.trans exactValue).symm ▸ LambdaComparison.encode_pattern source

local instance (sort : sig.Srt) : DecidableEq (sig.Op sort) := by
  cases sort
  intro first second
  cases first <;> cases second
  · exact isTrue rfl
  · exact isFalse (by intro same; cases same)
  · exact isFalse (by intro same; cases same)
  · exact isTrue rfl

/-- Actual incremental solving for the next selected contextual rule. The
completed saved prefix is transported across fresh local declarations;
the original new equations are then run through the existing worklist. -/
def solveCached {Γ Δ : Ctx sig} (state : State Γ) (context : Context Γ Δ)
    (cache : Cache state) (complete : cache.remaining = []) (fuel : Nat) :
    ContextualFrameWorklist.Result (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals state.1.declarations state.1.occupied (selection state.2)
        (rule state.1.declarations context) state.1.inventory.rows state.1.inventory.configuration)) :=
  ((ContextualFrameWorklist.Result.residual (extendedCache state cache complete)).resume fuel
    (addedProblem state context)).cast (observed_problem_split state context).symm

theorem solveCached_finishes {Γ Δ : Ctx sig} (state : State Γ) (context : Context Γ Δ)
    (source : Term sig Γ .term) (represented : Represents state source)
    (cache : Cache state) (complete : cache.remaining = []) :
    ∃ fuel, ContextualPatternTermination.Finished (solveCached state context cache complete fuel) := by
  obtain ⟨fuel, finished⟩ := ContextualPatternTermination.finishes_resuming (extendedCache state cache complete)
    (addedProblem state context) (cached_problem_is_pattern state context source represented cache complete)
  exact ⟨fuel, finished.cast (observed_problem_split state context).symm⟩

theorem solveCached_completes_valid {Γ Δ : Ctx sig} (state : State Γ) (context : Context Γ Δ)
    (source : Term sig Γ .term) (represented : Represents state source)
    (cache : Cache state) (complete : cache.remaining = [])
    (valid : ContextualGuardedStep.Valid locals state.1.declarations state.1.occupied (selection state.2)
      (rule state.1.declarations context) state.1.inventory.rows state.1.inventory.configuration
      (fun _ => output state.1.declarations state.1.occupied state.2 context)) :
    ∃ fuel result, solveCached state context cache complete fuel = .residual result ∧ result.remaining = [] := by
  obtain ⟨fuel, finished⟩ := solveCached_finishes state context source represented cache complete
  generalize computed : solveCached state context cache complete fuel = result at finished
  cases finished with
  | solved result empty => exact ⟨fuel, result, computed, empty⟩
  | refuted proof =>
      obtain ⟨Future, future, candidate, model⟩ := valid.solvable
      exact False.elim (proof future candidate
        ((ContextualResidual.models_observeProblem _ _).mpr model))

def initialCache {Γ : Ctx sig} (source : Term sig Γ .term) : Cache (initial source) :=
  @ContextualFrameWorklist.identity sig Empty inferInstance LambdaComparison.captures []

theorem initialCache_is_the_actual_zero_run {Γ : Ctx sig} (source : Term sig Γ .term) :
    ContextualFrameWorklist.run 0 LambdaComparison.captures [] = .residual (initialCache source) := rfl

/-- A retained execution with the actual incremental solver computation at
each event. Neither its constructor nor its cache is supplied a source
reduction or a precomputed source reduct. -/
inductive SolverPath {Γ : Ctx sig} (source : Term sig Γ .term) :
    (state : State Γ) → Cache state → Prop where
  | initial : SolverPath source (initial source) (initialCache source)
  | step {state : State Γ} {cache : Cache state} (prior : SolverPath source state cache)
      (complete : cache.remaining = []) {Δ : Ctx sig} (context : Context Γ Δ)
      (valid : ContextualGuardedStep.Valid locals state.1.declarations state.1.occupied (selection state.2)
        (rule state.1.declarations context) state.1.inventory.rows state.1.inventory.configuration
        (fun _ => output state.1.declarations state.1.occupied state.2 context))
      (fuel : Nat) (nextCache : Cache (destination state context valid))
      (computed : solveCached state context cache complete fuel = .residual nextCache)
      (finished : nextCache.remaining = []) :
      SolverPath source (destination state context valid) nextCache

theorem SolverPath.complete {Γ : Ctx sig} {source : Term sig Γ .term} {state : State Γ} {cache : Cache state}
    (path : SolverPath source state cache) : cache.remaining = [] := by
  cases path with
  | initial => rfl
  | step prior complete context valid fuel nextCache computed finished => exact finished

theorem SolverPath.semantic {Γ : Ctx sig} {source : Term sig Γ .term} {state : State Γ} {cache : Cache state}
    (path : SolverPath source state cache) : Relation.ReflTransGen Transition (LambdaExecution.initial source) state := by
  induction path with
  | initial => exact .refl
  | step prior complete context valid fuel nextCache computed finished ih =>
      exact ih.tail ⟨_, context, valid, rfl⟩

theorem source_path_with_actual_solvers {Γ : Ctx sig} {source target : Term sig Γ .term}
    (path : Relation.ReflTransGen (LambdaContextualRung.Step Γ) source target) :
    ∃ state cache, SolverPath source state cache ∧ Represents state target := by
  induction path with
  | refl => exact ⟨initial source, initialCache source, .initial, initial_represents source⟩
  | tail prior step ih =>
      obtain ⟨state, cache, computedPast, represented⟩ := ih
      obtain ⟨Δ, context, body, argument, rfl, rfl⟩ := LambdaContextualRung.step_iff_context_beta.mp step
      let valid := valid_of_source state context body argument represented
      obtain ⟨fuel, nextCache, computed, finished⟩ := solveCached_completes_valid state context _ represented
        cache computedPast.complete valid
      exact ⟨destination state context valid, nextCache,
        .step computedPast computedPast.complete context valid fuel nextCache computed finished,
        destination_represents state context body argument represented valid⟩

/-- The finite source correspondence includes an actual sequence of
worklist computations, transported completed prefixes and retained raw
endpoints. It does not claim a finite installed context-selection policy. -/
theorem finite_execution_with_solvers_iff {Γ : Ctx sig} (source target : Term sig Γ .term) :
    Relation.ReflTransGen (LambdaContextualRung.Step Γ) source target ↔
      ∃ state cache, SolverPath source state cache ∧ Represents state target := by
  constructor
  · exact source_path_with_actual_solvers
  · rintro ⟨state, cache, path, result⟩
    exact (finite_execution_iff source target).mpr ⟨state, path.semantic, result⟩

/-- A completed solver result recovers a source reduction and its exact
output without assuming the selected semantic transform was valid. -/
theorem completed_cached_return_is_source {Γ Δ : Ctx sig} (state : State Γ) (context : Context Γ Δ)
    (source : Term sig Γ .term) (represented : Represents state source)
    (cache : Cache state) (complete : cache.remaining = []) (fuel : Nat)
    (result : ContextualFrameUpdate.Update (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals state.1.declarations state.1.occupied (selection state.2)
        (rule state.1.declarations context) state.1.inventory.rows state.1.inventory.configuration)))
    (_computed : solveCached state context cache complete fuel = .residual result)
    (finished : result.remaining = []) :
    ∃ target, LambdaContextualRung.Step Γ source target ∧
      instantiate result.answer (output state.1.declarations state.1.occupied state.2 context) =
        encode result.declaration target := by
  have model := (ContextualResidual.models_observeProblem _ _).mp (result.completed finished)
  obtain ⟨body, argument, shape⟩ := input_model_recovers_source state context source represented result.answer model
  refine ⟨context.plug (inst body argument), ?_, ?_⟩
  · rw [shape]
    exact context.congr_step (.beta body argument)
  · exact source_output_in_every_model state context body argument (shape ▸ represented) result.answer model

theorem solveCached_refutes_inert_source {Γ Δ : Ctx sig} (state : State Γ) (context : Context Γ Δ)
    (source : Term sig Γ .term) (represented : Represents state source)
    (cache : Cache state) (complete : cache.remaining = [])
    (inert : ∀ target, ¬ LambdaContextualRung.Step Γ source target) :
    ∃ fuel proof, solveCached state context cache complete fuel = .refuted proof := by
  obtain ⟨fuel, finished⟩ := solveCached_finishes state context source represented cache complete
  generalize computed : solveCached state context cache complete fuel = result at finished
  cases finished with
  | solved result empty =>
      obtain ⟨target, step, _⟩ := completed_cached_return_is_source state context source represented cache complete
        fuel result computed empty
      exact False.elim (inert target step)
  | refuted proof => exact ⟨fuel, proof, computed⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LambdaExecution
