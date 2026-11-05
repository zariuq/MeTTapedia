import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalGuards
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalPublication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionEndpoints

/-!
# Solver-backed conditional binding and one occurrence update

Every selected row opens its value and latent equations at its actual port
scope. The joint information problem retains the incoming heterogeneous
equations, matched values, body equations and all selected latent equations.
An admitted event can retain an unfinished actual solver result: reusable
outputs store its value and pending equations together; live outputs keep
the original references in the returned world.

This indexed information/resource execution does not infer client authority
or textual scope ownership. Those remain formation refinements. A solver
return alone does not replace the semantic guard and solvability evidence
required for a committed firing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalExecution

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConditionalRows
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {Local Shared O : Type}
    (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
    {Γ : Ctx S} {sort : S.Srt}

def latent (occupied : Finset Nat) (selection : Selection O) (rows : O → Row locals captures Γ sort) :
    ContextualResidual.Problem (ContextualActivatedStep.target locals captures) :=
  (List.ofFn fun port : Fin selection.taken.length =>
    (rows (selection.taken.get port)).obligationsAt locals captures
      (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.takePort selection port))).flatten ++
  (List.ofFn fun port : Fin selection.read.length =>
    (rows (selection.read.get port)).obligationsAt locals captures
      (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.readPort selection port))).flatten

def information (occupied : Finset Nat) (selection : Selection O)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort))
    (rows : O → Row locals captures Γ sort) (before : ContextualResidual.Problem captures) :
    ContextualResidual.Problem (ContextualActivatedStep.target locals captures) :=
  ContextualResidual.mapProblem (ContextualSelectionViews.capturedTarget locals captures) before ++
    ContextualResidual.observeProblem (ContextualActivatedStep.addedEquations locals captures occupied selection rule
      (fun occurrence => (rows occurrence).value)) ++ latent locals captures occupied selection rows

theorem latent_ofStored (occupied : Finset Nat) (selection : Selection O)
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) :
    latent locals captures occupied selection (fun occurrence => ofStored locals captures (rows occurrence)) = [] := by
  simp [latent, Row.obligationsAt, ofStored, ContextualResidual.mapProblem]

/-- The old value-only binding problem embeds exactly, rather than merely
having a selected example with the same result. -/
theorem information_ofStored (occupied : Finset Nat) (selection : Selection O)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O) :
    information locals captures occupied selection rule (fun occurrence => ofStored locals captures (rows occurrence))
      (ContextualResidual.observeProblem before.equations) =
    ContextualResidual.observeProblem (ContextualActivatedStep.problem locals captures occupied selection rule rows before) := by
  rw [information, latent_ofStored, List.append_nil, ContextualActivatedStep.problem_eq_frame_append]
  change ContextualResidual.mapProblem (ContextualSelectionViews.capturedTarget locals captures)
      (ContextualResidual.observeProblem before.equations) ++
      ContextualResidual.observeProblem (ContextualActivatedStep.addedEquations locals captures occupied selection rule rows) =
    ContextualResidual.observeProblem (ContextualFrameUnifier.mapProblem (ContextualSelectionViews.capturedTarget locals captures)
      before.equations ++ ContextualActivatedStep.addedEquations locals captures occupied selection rule rows)
  rw [← ContextualResidual.observeProblem_mapProblem]
  exact List.map_append .. |>.symm

structure State (O : Type) (context : Ctx S) (sort : S.Srt) : Type 1 where
  Names : Type
  equality : DecidableEq Names
  declarations : Names → MetaArity S
  occupied : Finset Nat
  equations : ContextualResidual.Problem declarations
  present : Finset O
  rows : O → Row locals declarations context sort

def ofEndpoint (before : ContextualExecution.Endpoint locals O Γ sort) : State locals O Γ sort :=
  ⟨before.Names, before.equality, before.declarations, before.occupied,
    ContextualResidual.observeProblem before.inventory.configuration.equations, before.inventory.configuration.present,
    fun occurrence => ofStored locals before.declarations (before.inventory.rows occurrence)⟩

def guardRows (rows : O → Row locals captures Γ sort) :=
  fun occurrence => (rows occurrence).map locals captures (ContextualSelectionViews.capturedTarget locals captures)

def Solvable {V : Type} {declaration : V → MetaArity S} (problem : ContextualResidual.Problem declaration) : Prop :=
  ∃ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment declaration future),
    ContextualResidual.Models candidate problem

structure Admitted [DecidableEq O] (before : State locals O Γ sort)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals before.declarations)) Γ sort))
    (selection : Selection O)
    (outputs : O → Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort) : Prop where
  take_distinct : selection.taken.Nodup
  output_distinct : selection.made.Nodup
  take_length : rule.take.length = selection.taken.length
  read_length : rule.read.length = selection.read.length
  outputs : selection.made.map outputs =
    (ContextualActivatedStep.prepared locals before.declarations before.occupied selection rule
      (fun occurrence => (before.rows occurrence).value)).rule.produce
  taken_present : selection.taken.toFinset ⊆ before.present
  read_present : selection.read.toFinset ⊆ before.present
  apart : Disjoint selection.taken.toFinset selection.read.toFinset
  fresh : Disjoint selection.made.toFinset before.present
  solvable : Solvable (information locals before.declarations before.occupied selection rule before.rows before.equations)
  checks : ∀ check ∈ (ContextualActivatedStep.prepared locals before.declarations before.occupied selection rule
      (fun occurrence => (before.rows occurrence).value)).rule.checks,
    ContextualConditionalGuards.Ask locals
      (information locals before.declarations before.occupied selection rule before.rows before.equations)
      (guardRows locals before.declarations before.rows) before.present check

/-- Empty latent conditions recover the previous semantic admission,
including its all-future guards and its physical occurrence discipline. -/
theorem admitted_ofEndpoint_iff [DecidableEq O] (before : ContextualExecution.Endpoint locals O Γ sort)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals before.declarations)) Γ sort))
    (selection : Selection O)
    (outputs : O → Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort) :
    Admitted locals (ofEndpoint locals before) rule selection outputs ↔
      ContextualTransportedActivation.SemanticAdmission locals before.declarations before.occupied selection rule
        before.inventory.rows before.inventory.configuration outputs := by
  have sameProblem := information_ofStored locals before.declarations before.occupied selection rule
    before.inventory.rows before.inventory.configuration
  have sameChecks (check : Check (Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort)) :
      ContextualConditionalGuards.Ask locals
        (information locals before.declarations before.occupied selection rule
          (ofEndpoint locals before).rows (ofEndpoint locals before).equations)
        (guardRows locals before.declarations (ofEndpoint locals before).rows)
        before.inventory.configuration.present check ↔
      ContextualGuardSemantics.Ask locals
        (ContextualActivatedStep.problem locals before.declarations before.occupied selection rule
          before.inventory.rows before.inventory.configuration)
        (ContextualGuardedStep.guardRows locals before.declarations before.inventory.rows)
        before.inventory.configuration.present check := by
    rw [show information locals before.declarations before.occupied selection rule
      (ofEndpoint locals before).rows (ofEndpoint locals before).equations = _ from sameProblem]
    exact ContextualConditionalGuards.ask_ofStored locals _ _ _ _
  constructor
  · intro admitted
    refine ⟨⟨admitted.take_distinct, admitted.output_distinct, admitted.take_length, admitted.read_length,
      admitted.outputs, ⟨admitted.taken_present, admitted.read_present, admitted.apart, admitted.fresh, ?_⟩,
      (fun check member => (sameChecks check).mp (admitted.checks check member))⟩, ?_⟩
    · intro query member
      cases member
    · obtain ⟨Future, future, candidate, model⟩ := admitted.solvable
      refine ⟨Future, future, candidate, ?_⟩
      exact (ContextualResidual.models_observeProblem candidate _).mp (sameProblem ▸ model)
  · intro admitted
    refine ⟨admitted.take_distinct, admitted.output_distinct, admitted.take_length, admitted.read_length,
      admitted.outputs, admitted.occurrences.taken_subset, admitted.occurrences.kept_subset,
      admitted.occurrences.apart, admitted.occurrences.fresh, ?_,
      (fun check member => (sameChecks check).mpr (admitted.checks check member))⟩
    obtain ⟨Future, future, candidate, model⟩ := admitted.solvable
    refine ⟨Future, future, candidate, ?_⟩
    exact sameProblem.symm ▸ (ContextualResidual.models_observeProblem candidate _).mpr model

section Matching

variable [DecidableEq O] {before : State locals O Γ sort}
    {rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals before.declarations)) Γ sort)}
    {selection : Selection O}
    {outputs : O → Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort}

omit [DecidableEq O] in
theorem take_conditions {Next : Type} {next : Next → MetaArity S}
    (candidate : Assignment (ContextualActivatedStep.target locals before.declarations) next)
    (model : ContextualResidual.Models candidate
      (information locals before.declarations before.occupied selection rule before.rows before.equations))
    (port : Fin selection.taken.length) :
    ContextualResidual.Models candidate ((before.rows (selection.taken.get port)).obligationsAt locals before.declarations
      (ContextualActivationScopes.scopeAt before.occupied (ContextualActivationScopes.takePort selection port))) := by
  have selected := (ContextualResidual.models_append candidate _ _).mp model |>.2
  have takes := (ContextualResidual.models_append candidate _ _).mp selected |>.1
  intro equation member
  exact takes equation (List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨port, rfl⟩, member⟩)

theorem take_matches {Next : Type} {next : Next → MetaArity S}
    (admitted : Admitted locals before rule selection outputs)
    (candidate : Assignment (ContextualActivatedStep.target locals before.declarations) next)
    (model : ContextualResidual.Models candidate
      (information locals before.declarations before.occupied selection rule before.rows before.equations))
    (port : Fin selection.taken.length) :
    Matches locals before.declarations (Assignment.compose candidate (ContextualSelectionViews.capturedTarget locals before.declarations))
      (instantiate candidate ((ContextualActivatedStep.prepared locals before.declarations before.occupied selection rule
        (fun occurrence => (before.rows occurrence).value)).rule.take.get
          ⟨port.val, by simpa only [ContextualActivatedStep.prepared, ContextualSelectionViews.prepare,
            ContextualFreshening.ruleAt, RuleInstance.map, List.length_map, admitted.take_length] using port.isLt⟩))
      (before.rows (selection.taken.get port)) := by
  have initial := (ContextualResidual.models_append candidate _ _).mp model |>.1
  have observed := (ContextualResidual.models_append candidate _ _).mp initial |>.2
  have equations := (ContextualResidual.models_observeProblem candidate _).mp observed
  have takes := (ContextualFrameUnifier.models_append candidate _ _).mp
    ((ContextualFrameUnifier.models_append candidate _ _).mp equations).1 |>.1
  have shape : (ContextualActivatedStep.prepared locals before.declarations before.occupied selection rule
      (fun occurrence => (before.rows occurrence).value)).rule.take.length =
      (List.ofFn (ContextualActivatedStep.prepared locals before.declarations before.occupied selection rule
        (fun occurrence => (before.rows occurrence).value)).taken).length := by
    simpa only [ContextualActivatedStep.prepared, ContextualSelectionViews.prepare, ContextualFreshening.ruleAt,
      RuleInstance.map, List.length_map, List.length_ofFn] using admitted.take_length
  have paired := (ContextualActivatedStep.models_useEquations_iff locals before.declarations candidate _ _ shape).mp takes
  have valueBound : port.val < (List.ofFn (ContextualActivatedStep.prepared locals before.declarations before.occupied selection rule
      (fun occurrence => (before.rows occurrence).value)).taken).length := by simpa only [List.length_ofFn] using port.isLt
  have patternBound : port.val < (ContextualActivatedStep.prepared locals before.declarations before.occupied selection rule
      (fun occurrence => (before.rows occurrence).value)).rule.take.length := shape.symm ▸ valueBound
  have equal := paired.get patternBound valueBound
  apply matches_of_open locals before.declarations _ candidate _ _ (take_conditions locals candidate model port)
  have value := (List.get_ofFn _ ⟨port.val, by simpa only [List.length_ofFn] using port.isLt⟩).trans
    (ContextualActivatedStep.prepared_taken_view locals before.declarations before.occupied selection rule
      (fun occurrence => (before.rows occurrence).value) port)
  exact (congrArg (instantiate candidate) value).symm.trans equal.symm

omit [DecidableEq O] in
theorem read_conditions {Next : Type} {next : Next → MetaArity S}
    (candidate : Assignment (ContextualActivatedStep.target locals before.declarations) next)
    (model : ContextualResidual.Models candidate
      (information locals before.declarations before.occupied selection rule before.rows before.equations))
    (port : Fin selection.read.length) :
    ContextualResidual.Models candidate ((before.rows (selection.read.get port)).obligationsAt locals before.declarations
      (ContextualActivationScopes.scopeAt before.occupied (ContextualActivationScopes.readPort selection port))) := by
  have selected := (ContextualResidual.models_append candidate _ _).mp model |>.2
  have reads := (ContextualResidual.models_append candidate _ _).mp selected |>.2
  intro equation member
  exact reads equation (List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨port, rfl⟩, member⟩)

theorem read_matches {Next : Type} {next : Next → MetaArity S}
    (admitted : Admitted locals before rule selection outputs)
    (candidate : Assignment (ContextualActivatedStep.target locals before.declarations) next)
    (model : ContextualResidual.Models candidate
      (information locals before.declarations before.occupied selection rule before.rows before.equations))
    (port : Fin selection.read.length) :
    Matches locals before.declarations (Assignment.compose candidate (ContextualSelectionViews.capturedTarget locals before.declarations))
      (instantiate candidate ((ContextualActivatedStep.prepared locals before.declarations before.occupied selection rule
        (fun occurrence => (before.rows occurrence).value)).rule.read.get
          ⟨port.val, by simpa only [ContextualActivatedStep.prepared, ContextualSelectionViews.prepare,
            ContextualFreshening.ruleAt, RuleInstance.map, List.length_map, admitted.read_length] using port.isLt⟩))
      (before.rows (selection.read.get port)) := by
  have initial := (ContextualResidual.models_append candidate _ _).mp model |>.1
  have observed := (ContextualResidual.models_append candidate _ _).mp initial |>.2
  have equations := (ContextualResidual.models_observeProblem candidate _).mp observed
  have reads := (ContextualFrameUnifier.models_append candidate _ _).mp
    ((ContextualFrameUnifier.models_append candidate _ _).mp equations).1 |>.2
  have shape : (ContextualActivatedStep.prepared locals before.declarations before.occupied selection rule
      (fun occurrence => (before.rows occurrence).value)).rule.read.length =
      (List.ofFn (ContextualActivatedStep.prepared locals before.declarations before.occupied selection rule
        (fun occurrence => (before.rows occurrence).value)).read).length := by
    simpa only [ContextualActivatedStep.prepared, ContextualSelectionViews.prepare, ContextualFreshening.ruleAt,
      RuleInstance.map, List.length_map, List.length_ofFn] using admitted.read_length
  have paired := (ContextualActivatedStep.models_useEquations_iff locals before.declarations candidate _ _ shape).mp reads
  have valueBound : port.val < (List.ofFn (ContextualActivatedStep.prepared locals before.declarations before.occupied selection rule
      (fun occurrence => (before.rows occurrence).value)).read).length := by simpa only [List.length_ofFn] using port.isLt
  have patternBound : port.val < (ContextualActivatedStep.prepared locals before.declarations before.occupied selection rule
      (fun occurrence => (before.rows occurrence).value)).rule.read.length := shape.symm ▸ valueBound
  have equal := paired.get patternBound valueBound
  apply matches_of_open locals before.declarations _ candidate _ _ (read_conditions locals candidate model port)
  have value := (List.get_ofFn _ ⟨port.val, by simpa only [List.length_ofFn] using port.isLt⟩).trans
    (ContextualActivatedStep.prepared_read_view locals before.declarations before.occupied selection rule
      (fun occurrence => (before.rows occurrence).value) port)
  exact (congrArg (instantiate candidate) value).symm.trans equal.symm

end Matching

section Execution

variable [DecidableEq Local] [DecidableEq O] [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]

structure Firing (before : State locals O Γ sort) : Type 1 where
  rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals before.declarations)) Γ sort)
  selection : Selection O
  outputs : O → Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort
  reusable : O → Bool
  admitted : Admitted locals before rule selection outputs
  fuel : Nat
  update : ContextualFrameUpdate.Update
    (information locals before.declarations before.occupied selection rule before.rows before.equations)
  computed : letI := before.equality
    ContextualFrameWorklist.run fuel (ContextualActivatedStep.target locals before.declarations)
      (information locals before.declarations before.occupied selection rule before.rows before.equations) = .residual update

namespace Firing

variable {locals} {before : State locals O Γ sort}

abbrev target (firing : Firing locals before) :
    State (ContextualPublication.privateFamily locals firing.update.declaration) O Γ sort where
  Names := (Mettapedia.Logic.LP.ScopedVar Local ⊕ before.Names) ⊕ (firing.update.Variables ⊕ Empty)
  equality := by let _ := before.equality; let _ := firing.update.equality; infer_instance
  declarations := ContextualComputedFreshFrame.active (ContextualActivatedStep.target locals before.declarations) firing.update.declaration
  occupied := ContextualFreshFrameScopeLedger.helperLedger (ContextualActivationScopes.after before.occupied firing.selection)
  equations := ContextualResidual.mapProblem (ContextualComputedFreshFrame.includeSource firing.update)
    (information locals before.declarations before.occupied firing.selection firing.rule before.rows before.equations)
  present := fire before.present (firing.selection.commit (T := Unit))
  rows occurrence :=
    if occurrence ∈ firing.selection.made then
      if firing.reusable occurrence then
        ContextualConditionalPublication.ordinary locals firing.update.declaration _
          (ContextualResidualAnswers.ofUpdate firing.update (firing.outputs occurrence))
      else ofStored _ _ (.live (instantiate (ContextualComputedFreshFrame.includeSource firing.update) (firing.outputs occurrence)))
    else ContextualConditionalPublication.extendPrivate locals firing.update.declaration _
      ((before.rows occurrence).map locals before.declarations
        (Assignment.compose (ContextualComputedFreshFrame.includeSource firing.update)
          (ContextualSelectionViews.capturedTarget locals before.declarations)))

theorem physical_result (firing : Firing locals before) :
    firing.target.present = fire before.present (firing.selection.commit (T := Unit)) := rfl

theorem ordinary_matches_source (firing : Firing locals before) (occurrence : O)
    (made : occurrence ∈ firing.selection.made) (ordinary : firing.reusable occurrence = true)
    {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment firing.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    Matches (ContextualPublication.privateFamily locals firing.update.declaration) firing.target.declarations candidate pattern
      (firing.target.rows occurrence) ↔
    ContextualPublication.SourceInstances
      (information locals before.declarations before.occupied firing.selection firing.rule before.rows before.equations)
      (firing.outputs occurrence) next pattern := by
  change Matches _ _ candidate pattern (if _ then (if _ then _ else _) else _) ↔ _
  rw [if_pos made, if_pos ordinary]
  exact ContextualConditionalPublication.update_matches_source locals firing.target.declarations firing.update candidate _ pattern

theorem retained_matches (firing : Firing locals before) (occurrence : O)
    (notMade : occurrence ∉ firing.selection.made) {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment firing.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    Matches (ContextualPublication.privateFamily locals firing.update.declaration) firing.target.declarations
      candidate pattern (firing.target.rows occurrence) ↔
    Matches locals before.declarations
      (Assignment.compose candidate (Assignment.compose (ContextualComputedFreshFrame.includeSource firing.update)
        (ContextualSelectionViews.capturedTarget locals before.declarations))) pattern (before.rows occurrence) := by
  change Matches _ _ candidate pattern (if _ then _ else _) ↔ _
  rw [if_neg notMade, ContextualConditionalPublication.extendPrivate_matches_iff, matches_map_iff]

theorem live_row (firing : Firing locals before) (occurrence : O)
    (made : occurrence ∈ firing.selection.made) (live : firing.reusable occurrence = false) :
    firing.target.rows occurrence = ofStored _ _ (.live
      (instantiate (ContextualComputedFreshFrame.includeSource firing.update) (firing.outputs occurrence))) := by
  change (if _ then (if _ then _ else _) else _) = _
  rw [if_pos made, live]
  rfl

end Firing

/-- Every admitted source operation has an actual conditional solver return
at every finite budget. A nonempty residual queue is preserved in outputs;
it is not interpreted as a completion certificate. -/
theorem realize_at_fuel (before : State locals O Γ sort)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals before.declarations)) Γ sort))
    (selection : Selection O)
    (outputs : O → Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort)
    (reusable : O → Bool) (admitted : Admitted locals before rule selection outputs) (fuel : Nat) :
    ∃ firing : Firing locals before, firing.rule = rule ∧ firing.selection = selection ∧
      firing.outputs = outputs ∧ firing.reusable = reusable ∧ firing.fuel = fuel := by
  let _ := before.equality
  cases computed : ContextualFrameWorklist.run fuel (ContextualActivatedStep.target locals before.declarations)
      (information locals before.declarations before.occupied selection rule before.rows before.equations) with
  | refuted impossible =>
      obtain ⟨Future, future, candidate, model⟩ := admitted.solvable
      exact False.elim (impossible future candidate model)
  | residual update => exact ⟨⟨rule, selection, outputs, reusable, admitted, fuel, update, computed⟩, rfl, rfl, rfl, rfl, rfl⟩

end Execution

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalExecution
