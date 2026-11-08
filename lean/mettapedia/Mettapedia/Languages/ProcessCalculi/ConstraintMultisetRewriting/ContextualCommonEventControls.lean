import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommonEventExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectionViewControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedStepControls

/-!
# Two indexed events read one schema under one common model

The common allocator distinguishes the two row-use ports. Each event's
common data also construct an actual original worklist return. Replacing
the schema by one shared value makes the joint equations impossible;
explicit caller captures likewise remain shared across event scopes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommonEventControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualSelectionViews.Controls
  (base locals captures raw active RawTerm ActiveTerm atom pair p a b rawA rawB universalRow occupied)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)

def selections (_ : Fin 2) : Selection Nat := ⟨[], [7], []⟩
def rule (event : Fin 2) : RuleInstance RawTerm :=
  ⟨[], [p (if event = 0 then rawA else rawB)], [], [], []⟩
def rows (_ : Nat) : ContextualStoredRows.Row locals captures [] () := .schema universalRow
def before : Configuration (Term (signature base captures) [] ()) Nat := ⟨[], {7}⟩
def outputs (_ : Nat) : ActiveTerm := a
def equations (event : Fin 2) :=
  ContextualCommonEventProblems.problem locals captures selections occupied event (rule event) rows before
def Y9 : ActiveTerm := generator active (.inl (ScopedVar.at 9 0))
def Y11 : ActiveTerm := generator active (.inl (ScopedVar.at 11 0))

theorem the_computed_common_inventory_has_four_fresh_scopes :
    ContextualEventViewScopes.reserved selections occupied = {8, 9, 10, 11} ∧
      ContextualEventViewScopes.scope selections occupied (ContextualEventViewScopes.readUse selections 0 ⟨0, by decide⟩) = 9 ∧
      ContextualEventViewScopes.scope selections occupied (ContextualEventViewScopes.readUse selections 1 ⟨0, by decide⟩) = 11 := by
  decide +kernel

theorem the_two_common_problems_keep_separate_read_instances :
    equations 0 = [(p a, p Y9)] ∧ equations 1 = [(p b, p Y11)] := by
  constructor <;> with_unfolding_all rfl

def candidate : Assignment active active
  | .inl name => if name.scope = 11 then b else a
  | .inr name => generator active (.inr name)

theorem one_model_solves_both_events_and_keeps_callers_fixed :
    ContextualFrameUnifier.Models candidate (equations 0 ++ equations 1) ∧
      ∀ name, candidate (.inr name) = generator active (.inr name) := by
  constructor
  · rw [the_two_common_problems_keep_separate_read_instances.1,
      the_two_common_problems_keep_separate_read_instances.2]
    intro equation member
    simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> with_unfolding_all rfl
  · intro name
    rfl

theorem each_common_event_constructs_an_actual_original_return (event : Fin 2) :
    ∃ permutation : Equiv.Perm Nat,
      ∃ fuel update, ContextualTransportedActivation.FromRun locals captures fuel occupied (selections event)
        (rule event) rows before
        (ContextualCommonEventExecution.pullOutputs locals captures permutation outputs) update := by
  obtain ⟨permutation, aligned⟩ := ContextualEventViewRelocation.exists_alignment selections occupied occupied event
  refine ⟨permutation, ?_⟩
  apply ContextualCommonEventExecution.actual_return_from_common locals captures occupied occupied event permutation aligned
    (rule event) rows before outputs (future := active) (candidate := candidate)
  · dsimp only [selections]
    decide +kernel
  · dsimp only [selections]
    decide +kernel
  · rfl
  · rfl
  · rfl
  · dsimp only [selections, before]
    decide +kernel
  · dsimp only [selections, before]
    decide +kernel
  · dsimp only [selections]
    decide +kernel
  · dsimp only [selections, before]
    decide +kernel
  · intro check member
    cases member
  · apply (ContextualPatternFragment.checkProblem_iff _).mp
    fin_cases event <;> decide +kernel
  · fin_cases event
    · exact (ContextualFrameUnifier.models_append _ _ _).mp one_model_solves_both_events_and_keeps_callers_fixed.1 |>.1
    · exact (ContextualFrameUnifier.models_append _ _ _).mp one_model_solves_both_events_and_keeps_callers_fixed.1 |>.2

def sharedRows (_ : Nat) : ContextualStoredRows.Row locals captures [] () :=
  .shared (p (generator captures 0))
def sharedEquations (event : Fin 2) :=
  ContextualCommonEventProblems.problem locals captures selections occupied event (rule event) sharedRows before
def shared : ActiveTerm := generator active (.inr 0)

theorem shared_rows_keep_the_same_capture_at_both_ports :
    sharedEquations 0 = [(p a, p shared)] ∧ sharedEquations 1 = [(p b, p shared)] := by
  constructor <;> with_unfolding_all rfl

theorem a_shared_row_cannot_supply_the_two_distinct_instances
    {Future : Type} {future : Future → MetaArity base} (model : Assignment active future) :
    ¬ ContextualFrameUnifier.Models model (sharedEquations 0 ++ sharedEquations 1) := by
  intro solved
  rw [shared_rows_keep_the_same_capture_at_both_ports.1,
    shared_rows_keep_the_same_capture_at_both_ports.2] at solved
  have first := solved (p a, p shared) (by simp)
  have second := solved (p b, p shared) (by simp)
  have same := first.trans second.symm
  have sizes := congrArg termSize same
  change 3 = 5 at sizes
  omega

def captureRule (event : Fin 2) : RuleInstance RawTerm :=
  ⟨[], [], [(generator raw (.inr 0), if event = 0 then rawA else rawB)], [], []⟩
def captureSelections (_ : Fin 2) : Selection Nat := ⟨[], [], []⟩
def captureEquations (event : Fin 2) :=
  ContextualCommonEventProblems.problem locals captures captureSelections occupied event (captureRule event) rows before

theorem an_explicit_capture_keeps_one_identity_across_event_scopes :
    captureEquations 0 = [(shared, a)] ∧ captureEquations 1 = [(shared, b)] := by
  constructor <;> with_unfolding_all rfl

theorem separate_event_scopes_do_not_independently_solve_a_shared_capture
    {Future : Type} {future : Future → MetaArity base} (model : Assignment active future) :
    ¬ ContextualFrameUnifier.Models model (captureEquations 0 ++ captureEquations 1) := by
  intro solved
  rw [an_explicit_capture_keeps_one_identity_across_event_scopes.1,
    an_explicit_capture_keeps_one_identity_across_event_scopes.2] at solved
  have first := solved (shared, a) (by simp)
  have second := solved (shared, b) (by simp)
  have same := first.symm.trans second
  have sizes := congrArg termSize same
  change 1 = 3 at sizes
  omega

theorem zero_events_allocate_no_scopes (emptySelections : Fin 0 → Selection Nat) :
    ContextualEventViewScopes.reserved emptySelections occupied = ∅ := by
  simp [ContextualEventViewScopes.reserved, ContextualEventViewScopes.total]

namespace Checks

def selections (_ : Fin 1) := ContextualGuardedStep.Controls.selection
def rows := ContextualGuardedStep.Controls.rows
def before := ContextualGuardedStep.Controls.bare
def rule := ContextualGuardedStep.Controls.countRule

theorem a_common_scope_change_keeps_the_true_count_and_refuses_a_caller_binding :
    ∃ permutation : Equiv.Perm Nat,
      (∀ port : ContextualActivationScopes.Port (selections 0),
        permutation (ContextualActivationScopes.scopeAt occupied port) =
          ContextualEventViewScopes.scope selections occupied ⟨0, port⟩) ∧
      ContextualGuardSemantics.Ask locals
        (ContextualCommonEventProblems.problem locals captures selections occupied 0 rule rows before)
        (ContextualGuardedStep.guardRows locals captures rows) before.present
        ((Check.count (p (atom active)) 1).map
          (instantiate (ContextualEventViewRelocation.assignment locals captures permutation))) ∧
      ¬ ContextualGuardSemantics.Ask locals
        (ContextualCommonEventProblems.problem locals captures selections occupied 0 rule rows before)
        (ContextualGuardedStep.guardRows locals captures rows) before.present
        ((Check.equal (generator active (.inr 0)) (atom active)).map
          (instantiate (ContextualEventViewRelocation.assignment locals captures permutation))) := by
  obtain ⟨permutation, aligned⟩ := ContextualEventViewRelocation.exists_alignment selections occupied occupied 0
  refine ⟨permutation, aligned, ?_, ?_⟩
  · exact (ContextualCommonEventProblems.original_ask_relocated_iff locals captures occupied occupied 0
      permutation aligned rule rows before _).mpr
        ContextualGuardedStep.Controls.the_schematic_count_guard_asks_over_every_future_model
  · intro extended
    have original := (ContextualCommonEventProblems.original_ask_relocated_iff locals captures occupied occupied 0
      permutation aligned rule rows before _).mp extended
    have same := original (ScopedVar Nat ⊕ Nat) active (generator active)
      (fun _ member => False.elim (List.not_mem_nil member))
    change generator active (.inr 0) = atom active at same
    have heads := (Term.op.inj same).1
    cases heads

end Checks

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommonEventControls

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPairExecutionControls

set_option backward.isDefEq.respectTransparency false

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ContextualScopeSupport ContextualWorldScopeLedger ContextualExecution ContextualSchedulePromotion

abbrev base := ContextualFrame.Controls.signature
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)

def locals (_ : Nat) : MetaArity base := ([], ())
def captures : Unit ⊕ Fin 3 → MetaArity base
  | .inl () => ([(), ()], ())
  | .inr _ => ([], ())
abbrev raw := ContextualSelectionViews.source locals captures
abbrev active := ContextualSelectionViews.target locals captures
abbrev shared := ContextualPairFrames.common locals captures
abbrev RawTerm := Term (signature base raw) [(), ()] ()
abbrev ActiveTerm := Term (signature base active) [(), ()] ()
def ground : Empty → MetaArity base := Empty.elim

def atom {V : Type} (declarations : V → MetaArity base) {Γ : Ctx base} :
    Term (signature base declarations) Γ () := .op (.inl .constant) .nil
def pair {V : Type} {declarations : V → MetaArity base} {Γ : Ctx base}
    (left right : Term (signature base declarations) Γ ()) : Term (signature base declarations) Γ () :=
  .op (.inl .pair) (.cons left (.cons right .nil))
def closedLambda {V : Type} (declarations : V → MetaArity base) {Γ : Ctx base} :
    Term (signature base declarations) Γ () := .op (.inl .lam) (.cons (.var .zero) .nil)
def hole {Γ : Ctx base} (name : Fin 3) : Term (signature base captures) Γ () :=
  .op (.inr (.mk (.inr name))) .nil
def rawHole (name : Fin 3) : RawTerm := .op (.inr (.mk (.inr (.inr name)))) .nil
def rawFormal : RawTerm := .op (.inr (.mk (.inr (.inl ()))))
  (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil))
def rawSwapped : RawTerm := .op (.inr (.mk (.inr (.inl ()))))
  (.cons (.var (.succ .zero)) (.cons (.var .zero) .nil))
def p {V : Type} {declarations : V → MetaArity base} {Γ : Ctx base}
    (value : Term (signature base declarations) Γ ()) := pair (atom declarations) value
def b {V : Type} (declarations : V → MetaArity base) {Γ : Ctx base} := pair (atom declarations) (atom declarations) (Γ := Γ)

def selection (bind : Bool) : Selection Nat :=
  if bind then ⟨[1], [7], [100]⟩ else ⟨[0], [7, 7], [99]⟩
def equations (bind : Bool) : EquationStore RawTerm :=
  if bind then [(rawHole 1, atom raw), (rawFormal, closedLambda raw)]
  else [(rawFormal, rawSwapped), (rawHole 0, pair (rawHole 1) (rawHole 1))]
def output : RawTerm := pair (b raw) (rawHole 0)
def rule (bind : Bool) : RuleInstance RawTerm :=
  ⟨[atom raw], if bind then [p (atom raw)] else [p (atom raw), p (b raw)], equations bind,
    if bind then [.equal (rawHole 1) (atom raw)] else [.equal rawFormal rawSwapped], [output]⟩
def rows (occurrence : Nat) : ContextualStoredRows.Row locals captures [(), ()] () :=
  if occurrence = 7 then .schema (p (.op (.inr (.mk (.inl 0))) .nil))
  else if occurrence = 8 then .shared (hole 2) else .shared (atom captures)
def before : Configuration (Term (signature base captures) [(), ()] ()) Nat :=
  ⟨[(hole 2, atom captures)], {0, 1, 7, 8}⟩
def occupied : Finset Nat := ∅
def oldScopes (_ : Unit ⊕ Fin 3) : Finset Nat := ∅
def inventory : Inventory locals captures (O := Nat) [(), ()] () := ⟨before, rows, [], []⟩
def initial : Endpoint locals Nat [(), ()] () where
  Names := Unit ⊕ Fin 3
  equality := inferInstance
  declarations := captures
  scopes := oldScopes
  occupied := occupied
  inventory := inventory
  covered := (coveredWorld_iff locals captures oldScopes occupied inventory).mpr (by decide +kernel)

local instance : Quiver (Endpoint locals Nat [(), ()] ()) := ContextualExecution.graph locals Nat
def outputs (bind : Bool) (_ : Nat) : ActiveTerm :=
  ContextualFreshening.termAt locals captures
    (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.rulePort (selection bind))) output
def problem (bind : Bool) :=
  ContextualActivatedStep.problem locals captures occupied (selection bind) (rule bind) rows before
def joint (bindFirst : Bool) :=
  ContextualPairFrames.jointProblem locals captures occupied (selection (!bindFirst)) (rule (!bindFirst)) rows
    (selection bindFirst) (rule bindFirst) before

def callerBody : Assignment captures ground
  | .inl () => closedLambda ground
  | .inr name => if name = 0 then b ground else atom ground
def localBody (bind : Bool) (name : ScopedVar Nat) : Term (signature base ground) [] () :=
  if !bind && name.scope == 4 then b ground else atom ground
def model (bind : Bool) : Assignment active ground
  | .inl name => localBody bind name
  | .inr name => callerBody name
def jointModel (bindFirst : Bool) : Assignment shared ground
  | .inl name => localBody bindFirst name
  | .inr (.inl name) => localBody (!bindFirst) name
  | .inr (.inr name) => callerBody name

theorem original_rule_covered (bind : Bool) : RuleCovered (privateScopes oldScopes) occupied (rule bind) := by
  apply (ruleRoots_covered_iff _ _ _).mp
  cases bind <;> decide +kernel

theorem original_problem_pattern (bind : Bool) :
    ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem (problem bind)) := by
  apply (ContextualPatternFragment.checkProblem_iff _).mp
  cases bind <;> decide +kernel

theorem joint_problem_pattern (bind : Bool) :
    ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem (joint bind)) := by
  apply (ContextualPatternFragment.checkProblem_iff _).mp
  cases bind <;> decide +kernel

theorem original_problem_has_model (bind : Bool) : ContextualFrameUnifier.Models (model bind) (problem bind) := by
  have verified : List.Forall (fun equation =>
      instantiate (model bind) equation.1 = instantiate (model bind) equation.2) (problem bind) := by
    cases bind <;> repeat' constructor
  intro equation member
  exact (List.forall_iff_forall_mem.mp verified) equation member

set_option maxHeartbeats 1800000 in
theorem joint_problem_has_model (bind : Bool) : ContextualFrameUnifier.Models (jointModel bind) (joint bind) := by
  have verified : List.Forall (fun equation =>
      instantiate (jointModel bind) equation.1 = instantiate (jointModel bind) equation.2) (joint bind) := by
    cases bind <;> repeat' constructor
  intro equation member
  exact (List.forall_iff_forall_mem.mp verified) equation member

theorem original_guard_is_an_equation (bind : Bool)
    (check : Check ActiveTerm)
    (member : check ∈ (ContextualActivatedStep.prepared locals captures occupied (selection bind) (rule bind) rows).rule.checks) :
    ∃ left right, check = .equal left right ∧
      (left, right) ∈ ContextualActivatedStep.addedEquations locals captures occupied (selection bind) (rule bind) rows := by
  cases bind <;> obtain rfl := List.mem_singleton.mp member
  all_goals
    refine ⟨_, _, rfl, ?_⟩
    apply List.mem_append_right
    exact List.mem_cons_self

theorem original_admission (bind : Bool) : ContextualGuardedStep.Valid
    locals captures occupied (selection bind) (rule bind) rows before (outputs bind) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ContextualFrameUnifier.solvable_of_model (original_problem_has_model bind)⟩
  · cases bind <;> decide +kernel
  · cases bind <;> decide +kernel
  · cases bind <;> rfl
  · cases bind <;> rfl
  · cases bind <;> rfl
  · cases bind <;> decide +kernel
  · intro check member
    obtain ⟨left, right, rfl, inAdded⟩ := original_guard_is_an_equation bind check member
    apply ContextualGuardSemantics.Ask.equal_of_mem
    rw [ContextualActivatedStep.problem_eq_frame_append]
    exact List.mem_append_right _ inAdded

theorem second_formation (bind : Bool) : ContextualInteractionFactors.Formation
    locals captures occupied (selection (!bind)) (rule (!bind)) rows (outputs (!bind)) := by
  cases bind <;> exact ⟨rfl, rfl, rfl⟩

theorem second_resources (bind : Bool) : ContextualInteractionFactors.Resources (selection (!bind))
    (fire before.present ((selection bind).commit (T := Unit))) := by
  apply (ContextualInteractionFactors.resources_iff (outputs (!bind)) _ _).mpr
  cases bind <;> decide +kernel

theorem selected_rows_are_unchanged (bind : Bool) :
    ∀ occurrence ∈ (selection (!bind)).taken ++ (selection (!bind)).read, occurrence ∉ (selection bind).made := by
  cases bind <;> decide +kernel

theorem joint_guards (bind : Bool)
    (check : Check ActiveTerm)
    (member : check ∈ (ContextualActivatedStep.prepared locals captures occupied
      (selection (!bind)) (rule (!bind)) rows).rule.checks) :
    ContextualGuardSemantics.Ask locals (joint bind)
      (ContextualPairFrames.rowsAfterFirst locals captures rows (selection bind) (outputs bind))
      (fire before.present ((selection bind).commit (T := Unit)))
      (check.map (instantiate (ContextualPairFrames.second locals captures).assignment)) := by
  obtain ⟨left, right, rfl, inAdded⟩ := original_guard_is_an_equation (!bind) check member
  apply ContextualGuardSemantics.Ask.equal_of_mem
  exact List.mem_append_right _ (List.mem_map.mpr ⟨(left, right), inAdded, rfl⟩)

theorem both_actual_orders_exist (bindFirst : Bool) :
    ∃ final : Endpoint locals Nat [(), ()] (), ∃ path : Quiver.Path initial final,
      selections path = [selection bindFirst, selection (!bindFirst)] := by
  obtain ⟨first, second, _relocation, _firstRule, _firstSelection, _firstOutputs, _secondRule, _secondSelection,
    _secondOutputs, _aligned, _firstChecks, _secondChecks, ⟨path, picked⟩, _observations⟩ :=
    ContextualPairFrames.realize_ordered_pair locals initial (selection bindFirst) (selection (!bindFirst))
      (rule bindFirst) (rule (!bindFirst)) (outputs bindFirst) (outputs (!bindFirst))
      (original_rule_covered bindFirst) (original_rule_covered (!bindFirst)) (original_admission bindFirst)
      (original_problem_pattern bindFirst) (second_formation bindFirst) (second_resources bindFirst)
      (selected_rows_are_unchanged bindFirst) (ContextualFrameUnifier.solvable_of_model (joint_problem_has_model bindFirst))
      (joint_guards bindFirst) (joint_problem_pattern bindFirst)
  exact ⟨second.target, path, picked⟩

def commonHole (name : Fin 3) : Term (signature base shared) [(), ()] () :=
  .op (.inr (.mk (.inr (.inr (.inr name))))) .nil
def commonFormal : Term (signature base shared) [(), ()] () :=
  .op (.inr (.mk (.inr (.inr (.inl ())))))
    (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil))

theorem joint_models_keep_the_original_constraint_and_solve_the_shared_bindings (bind : Bool)
    {Future : Type} (future : Future → MetaArity base) (candidate : Assignment shared future)
    (solved : ContextualFrameUnifier.Models candidate (joint bind)) :
    instantiate candidate (commonHole 0) = b future ∧
    instantiate candidate (commonHole 1) = atom future ∧
    instantiate candidate (commonHole 2) = atom future ∧
    instantiate candidate commonFormal = closedLambda future := by
  have xMember : (commonHole 0, pair (commonHole 1) (commonHole 1)) ∈ joint bind := by
    cases bind
    · exact List.getElem_mem (l := joint false) (n := 5) (by decide +kernel)
    · exact List.getElem_mem (l := joint true) (n := 9) (by decide +kernel)
  have yMember : (commonHole 1, atom shared) ∈ joint bind := by
    cases bind
    · exact List.getElem_mem (l := joint false) (n := 8) (by decide +kernel)
    · exact List.getElem_mem (l := joint true) (n := 3) (by decide +kernel)
  have zMember : (commonHole 2, atom shared) ∈ joint bind := by
    cases bind
    · exact List.getElem_mem (l := joint false) (n := 0) (by decide +kernel)
    · exact List.getElem_mem (l := joint true) (n := 0) (by decide +kernel)
  have mMember : (commonFormal, closedLambda shared) ∈ joint bind := by
    cases bind
    · exact List.getElem_mem (l := joint false) (n := 9) (by decide +kernel)
    · exact List.getElem_mem (l := joint true) (n := 4) (by decide +kernel)
  have x := solved _ xMember
  have y := solved _ yMember
  have z := solved _ zMember
  have m := solved _ mMember
  change instantiate candidate (commonHole 0) = pair
    (instantiate candidate (commonHole 1)) (instantiate candidate (commonHole 1)) at x
  change instantiate candidate (commonHole 1) = atom future at y
  rw [y] at x
  exact ⟨x, y, z, m⟩

set_option maxHeartbeats 1800000 in
/-- This uses the general construction twice. Both paths perform actual
worklist returns, take different requests, alias the same schema row, and
publish distinct physical outputs. Every final all-future Check agrees
under the explicit exchange of private event names. -/
theorem actual_orders_preserve_final_observations :
    ∃ forward backward : Endpoint locals Nat [(), ()] (),
      ∃ forwardPath : Quiver.Path initial forward, ∃ backwardPath : Quiver.Path initial backward,
      ∃ forwardView : Assignment shared forward.declarations, ∃ backwardView : Assignment shared backward.declarations,
        selections forwardPath = [selection false, selection true] ∧
        selections backwardPath = [selection true, selection false] ∧
        (∀ check : Check (Term (signature base shared) [(), ()] ()),
          ContextualGuardSemantics.Ask locals forward.inventory.configuration.equations
            forward.inventory.rows forward.inventory.configuration.present
            (check.map (instantiate forwardView)) ↔
          ContextualGuardSemantics.Ask locals backward.inventory.configuration.equations
            backward.inventory.rows backward.inventory.configuration.present
            (check.map (instantiate (Assignment.compose backwardView
              (ContextualPairFrames.exchangeEvents locals captures).assignment)))) := by
  exact ContextualPairFrames.realize_two_orders locals initial selection rule outputs
    original_rule_covered original_admission original_problem_pattern second_resources
    (fun event => ContextualFrameUnifier.solvable_of_model (joint_problem_has_model event))
    joint_guards joint_problem_pattern

def prematureModel : Assignment active ground
  | .inl _ => atom ground
  | .inr (.inl ()) => closedLambda ground
  | .inr (.inr _) => atom ground

theorem the_second_event_alone_does_not_justify_the_later_joint_answer :
    ¬ ContextualGuardSemantics.Ask locals (problem true)
      (ContextualGuardedStep.guardRows locals captures rows) before.present
      (.equal (ContextualFreshening.termAt locals captures 1 (rawHole 0)) (b active)) := by
  have solved : ContextualFrameUnifier.Models prematureModel (problem true) := by
    have verified : List.Forall (fun equation => instantiate prematureModel equation.1 =
        instantiate prematureModel equation.2) (problem true) := by repeat' constructor
    exact List.forall_iff_forall_mem.mp verified
  intro asked
  have wrong := asked Empty ground prematureModel solved
  have sizes := congrArg termSize wrong
  change 1 = 3 at sizes
  omega

theorem dropping_the_first_equations_loses_a_required_joint_observation :
    ContextualGuardSemantics.Ask locals (joint false)
      (ContextualPairFrames.rowsAfterBoth locals captures rows (selection false) (selection true) (outputs false) (outputs true))
      (fire (fire before.present ((selection false).commit (T := Unit))) ((selection true).commit (T := Unit)))
      (.equal (commonHole 0) (b shared)) := by
  intro Future future candidate solved
  exact (joint_models_keep_the_original_constraint_and_solve_the_shared_bindings false future candidate solved).1

theorem a_conflicting_shared_binding_has_no_joint_completion :
    ¬ ContextualFrameUnifier.Solvable (joint false ++ [(commonHole 0, atom shared)]) := by
  rintro ⟨Future, future, candidate, solved⟩
  obtain ⟨jointSolved, added⟩ := (ContextualFrameUnifier.models_append candidate _ _).mp solved
  have correct := (joint_models_keep_the_original_constraint_and_solve_the_shared_bindings false future candidate jointSolved).1
  have wrong := added _ (List.mem_singleton_self _)
  have clash := correct.symm.trans wrong
  have sizes := congrArg termSize clash
  change 3 = 1 at sizes
  omega

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPairExecutionControls

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCausalExecutionControls

set_option backward.isDefEq.respectTransparency false

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ContextualScopeSupport ContextualWorldScopeLedger ContextualExecution ContextualSchedulePromotion
open ContextualPairExecutionControls
  (base locals captures raw active shared RawTerm ActiveTerm atom pair p b closedLambda ground
    rawHole rawFormal rawSwapped rows before occupied oldScopes initial callerBody localBody)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)
local instance : Quiver (Endpoint locals Nat [(), ()] ()) := ContextualExecution.graph locals Nat

def producer := ContextualPairExecutionControls.selection false
def privateVariable : RawTerm := .op (.inr (.mk (.inl 0))) .nil
def producerRule : RuleInstance RawTerm := { ContextualPairExecutionControls.rule false with produce := [privateVariable] }
def produced (_ : Nat) : ActiveTerm := ContextualFreshening.termAt locals captures 1 privateVariable
def consumer (consume : Bool) : Selection Nat :=
  if consume then ⟨[1, 99], [7], [100]⟩ else ⟨[1], [7, 99, 99], [100]⟩
def consumerRule (consume : Bool) : RuleInstance RawTerm := {
  take := if consume then [atom raw, closedLambda raw] else [atom raw]
  read := if consume then [p (atom raw)] else [p (atom raw), closedLambda raw, closedLambda raw]
  tell := ContextualPairExecutionControls.equations true
  checks := [.equal (rawHole 1) (atom raw), .count (closedLambda raw) 1]
  produce := [ContextualPairExecutionControls.output] }
def outputs := ContextualPairExecutionControls.outputs true
def problem (consume : Bool) := ContextualPairFrames.causalProblem locals captures rows producer produced occupied
  (consumer consume) (consumerRule consume) producerRule before
def sharedProducer : Term (signature base shared) [(), ()] () :=
  instantiate (ContextualPairFrames.first locals captures).assignment (produced 99)

def model : Assignment shared ground
  | .inl name => if name.scope = 1 then closedLambda ground else localBody false name
  | .inr (.inl name) => localBody true name
  | .inr (.inr name) => callerBody name

theorem producer_admitted : ContextualGuardedStep.Valid
    locals captures occupied producer producerRule rows before produced := by
  have old := ContextualPairExecutionControls.original_admission false
  exact ⟨⟨old.take_distinct, old.output_distinct, old.take_length, old.read_length,
    by with_unfolding_all rfl,
    ⟨old.occurrences.taken_subset, old.occurrences.kept_subset, old.occurrences.apart, old.occurrences.fresh,
      fun query member => by cases member⟩, old.checks⟩, old.solvable⟩

theorem producer_pattern : ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem
    (ContextualActivatedStep.problem locals captures occupied producer producerRule rows before)) :=
  ContextualPairExecutionControls.original_problem_pattern false

theorem producer_covered : RuleCovered (privateScopes oldScopes) occupied producerRule := by
  apply (ruleRoots_covered_iff _ _ _).mp
  decide +kernel

theorem consumer_covered (consume : Bool) : RuleCovered (privateScopes oldScopes) occupied (consumerRule consume) := by
  apply (ruleRoots_covered_iff _ _ _).mp
  cases consume <;> decide +kernel

theorem consumer_formed (consume : Bool) : ContextualInteractionFactors.Formation
    locals captures occupied (consumer consume) (consumerRule consume) rows outputs := by
  cases consume <;> exact ⟨rfl, rfl, rfl⟩

theorem consumer_available_after_production (consume : Bool) : ContextualInteractionFactors.Resources
    (consumer consume) (fire before.present (producer.commit (T := Unit))) := by
  apply (ContextualInteractionFactors.resources_iff outputs _ _).mpr
  cases consume <;> decide +kernel

theorem consumer_unavailable_before_production (consume : Bool) :
    ¬ ContextualInteractionFactors.Resources (consumer consume) before.present := by
  rw [ContextualInteractionFactors.resources_iff outputs]
  cases consume <;> decide +kernel

theorem causal_patterns (consume : Bool) :
    ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem (problem consume)) := by
  apply (ContextualPatternFragment.checkProblem_iff _).mp
  cases consume <;> decide +kernel

set_option maxHeartbeats 2200000 in
theorem causal_model (consume : Bool) : ContextualFrameUnifier.Models model (problem consume) := by
  have verified : List.Forall (fun equation => instantiate model equation.1 = instantiate model equation.2) (problem consume) := by
    cases consume <;> repeat' constructor
  exact List.forall_iff_forall_mem.mp verified

theorem every_model_keeps_one_producer_identity (consume : Bool)
    {Future : Type} (future : Future → MetaArity base) (candidate : Assignment shared future)
    (solved : ContextualFrameUnifier.Models candidate (problem consume)) :
    instantiate candidate sharedProducer = closedLambda future := by
  have member : (closedLambda shared, sharedProducer) ∈ problem consume := by
    cases consume
    · exact List.getElem_mem (l := problem false) (n := 8) (by decide +kernel)
    · exact List.getElem_mem (l := problem true) (n := 7) (by decide +kernel)
  exact (solved _ member).symm

def middleRows := ContextualPairFrames.rowsAfterFirst locals captures rows producer produced
def middleWorld := fire before.present (producer.commit (T := Unit))

/-- The count is about physical occurrences. Two read ports share the one
produced occurrence, and a take observes that occurrence before removing it. -/
theorem matching_lambdas_at_admission (consume : Bool)
    {Future : Type} (future : Future → MetaArity base) (candidate : Assignment shared future)
    (solved : ContextualFrameUnifier.Models candidate (problem consume)) :
    ContextualGuardSemantics.region locals candidate middleRows middleWorld (closedLambda shared) = {99} := by
  classical
  have oldEquation : (ContextualPairExecutionControls.commonHole 2, atom shared) ∈ problem consume := by
    cases consume
    · exact List.getElem_mem (l := problem false) (n := 0) (by decide +kernel)
    · exact List.getElem_mem (l := problem true) (n := 0) (by decide +kernel)
  have oldBinding := solved _ oldEquation
  have requestApart : ¬ ContextualGuardMatching.Matches locals candidate
      (instantiate candidate (closedLambda shared)) (middleRows 1) := by
    intro matched
    change closedLambda future = atom future at matched
    cases (Term.op.inj matched).1
  have schemaApart : ¬ ContextualGuardMatching.Matches locals candidate
      (instantiate candidate (closedLambda shared)) (middleRows 7) := by
    rintro ⟨extension, localBodies, matched⟩
    cases (Term.op.inj matched).1
  have oldApart : ¬ ContextualGuardMatching.Matches locals candidate
      (instantiate candidate (closedLambda shared)) (middleRows 8) := by
    intro matched
    change closedLambda future = instantiate candidate (ContextualPairExecutionControls.commonHole 2) at matched
    have same := matched.trans oldBinding
    cases (Term.op.inj same).1
  have producedMatch : ContextualGuardMatching.Matches locals candidate
      (instantiate candidate (closedLambda shared)) (middleRows 99) :=
    (every_model_keeps_one_producer_identity consume future candidate solved).symm
  have matchedSet : ContextualGuardSemantics.region locals candidate middleRows middleWorld (closedLambda shared) = {99} := by
    ext occurrence
    constructor
    · intro matched
      obtain ⟨present, agrees⟩ := (ContextualGuardSemantics.mem_region locals candidate middleRows middleWorld
        (closedLambda shared) occurrence).mp matched
      have world : middleWorld = {1, 7, 8, 99} := by decide +kernel
      rw [world] at present
      simp only [Finset.mem_insert, Finset.mem_singleton] at present
      rcases present with rfl | rfl | rfl | rfl
      · exact False.elim (requestApart agrees)
      · exact False.elim (schemaApart agrees)
      · exact False.elim (oldApart agrees)
      · exact Finset.mem_singleton_self _
    · intro member
      have same := Finset.mem_singleton.mp member
      subst occurrence
      exact (ContextualGuardSemantics.mem_region locals candidate middleRows middleWorld (closedLambda shared) 99).mpr
        ⟨by decide +kernel, producedMatch⟩
  exact matchedSet


theorem exactly_one_live_lambda_at_admission (consume : Bool)
    {Future : Type} (future : Future → MetaArity base) (candidate : Assignment shared future)
    (solved : ContextualFrameUnifier.Models candidate (problem consume)) :
    ContextualGuardSemantics.Holds locals candidate middleRows middleWorld (.count (closedLambda shared) 1) := by
  change (ContextualGuardSemantics.region locals candidate middleRows middleWorld (closedLambda shared)).card = 1
  rw [matching_lambdas_at_admission consume future candidate solved]
  decide +kernel

theorem consumer_guards (consume : Bool) (check : Check ActiveTerm)
    (member : check ∈ (ContextualActivatedStep.prepared locals captures occupied
      (consumer consume) (consumerRule consume) rows).rule.checks) :
    ContextualGuardSemantics.Ask locals (problem consume) middleRows middleWorld
      (check.map (instantiate (ContextualPairFrames.second locals captures).assignment)) := by
  rcases List.mem_cons.mp member with rfl | remaining
  · apply ContextualGuardSemantics.Ask.equal_of_mem
    apply List.mem_append_right
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨_, List.mem_cons_self, rfl⟩
  · obtain rfl := List.mem_singleton.mp remaining
    intro Future future candidate solved
    exact exactly_one_live_lambda_at_admission consume future candidate solved

set_option maxHeartbeats 2200000 in
/-- The consumer starts unavailable, then uses a newly produced variable.
Repeated reads preserve one shared value; taking removes the same physical
occurrence. Both paths come from the general causal realization theorem. -/
theorem actual_producer_consumer_path (consume : Bool) :
    ∃ final : Endpoint locals Nat [(), ()] (), ∃ path : Quiver.Path initial final,
      ∃ view : Assignment shared final.declarations,
        selections path = [producer, consumer consume] ∧
        final.inventory.configuration.present = (if consume then {7, 8, 100} else {7, 8, 99, 100}) ∧
        ContextualGuardSemantics.Ask locals final.inventory.configuration.equations final.inventory.rows
          final.inventory.configuration.present
          ((Check.equal sharedProducer (closedLambda shared)).map (instantiate view)) := by
  obtain ⟨first, second, relocation, _firstRule, firstSelected, _firstOutputs, _secondRule, secondSelected,
    _secondOutputs, _aligned, firstChecked, secondChecked, ⟨path, picked⟩, observations⟩ :=
    ContextualPairFrames.realize_causal_pair locals initial producer (consumer consume) producerRule (consumerRule consume)
      produced outputs producer_covered (consumer_covered consume) producer_admitted producer_pattern
      (consumer_formed consume) (consumer_available_after_production consume)
      (ContextualFrameUnifier.solvable_of_model (causal_model consume)) (consumer_guards consume) (causal_patterns consume)
  let view := Assignment.compose (ContextualComputedFreshFrame.includeSource second.update)
    (ContextualPairFrames.secondActive locals captures first.update.declaration relocation).assignment
  refine ⟨second.target, path, view, picked, ?_, ?_⟩
  · have firstWorld := (first.firing firstChecked).physical_result
    have secondWorld := (second.firing secondChecked).physical_result
    change first.target.inventory.configuration.present = fire before.present (first.selection.commit (T := Unit)) at firstWorld
    change second.target.inventory.configuration.present =
      fire first.target.inventory.configuration.present (second.selection.commit (T := Unit)) at secondWorld
    rw [firstSelected] at firstWorld
    rw [secondSelected] at secondWorld
    rw [secondWorld, firstWorld]
    cases consume <;> decide +kernel
  · apply (observations (.equal sharedProducer (closedLambda shared))).mpr
    intro Future future candidate solved
    exact every_model_keeps_one_producer_identity consume future candidate solved

def incompatibleConsumer : RuleInstance RawTerm :=
  { consumerRule false with read := [p (atom raw), closedLambda raw, atom raw] }
def incompatibleProblem := ContextualPairFrames.causalProblem locals captures rows producer produced occupied
  (consumer false) incompatibleConsumer producerRule before

theorem repeated_reads_cannot_rebind_one_produced_value_independently :
    ¬ ContextualFrameUnifier.Solvable incompatibleProblem := by
  rintro ⟨Future, future, candidate, solved⟩
  have first : (closedLambda shared, sharedProducer) ∈ incompatibleProblem :=
    List.getElem_mem (l := incompatibleProblem) (n := 8) (by decide +kernel)
  have second : (atom shared, sharedProducer) ∈ incompatibleProblem :=
    List.getElem_mem (l := incompatibleProblem) (n := 9) (by decide +kernel)
  have same := (solved _ first).trans (solved _ second).symm
  have sizes := congrArg termSize same
  change 2 = 1 at sizes
  omega

def finalRows := ContextualPairFrames.rowsAfterBoth locals captures rows producer (consumer true) produced outputs
def finalWorld := fire middleWorld ((consumer true).commit (T := Unit))

theorem the_consumed_lambda_is_absent_at_the_final_cut :
    ContextualGuardSemantics.Ask locals (problem true) finalRows finalWorld (.absent (closedLambda shared)) := by
  intro Future future candidate solved occurrence present matched
  have world : finalWorld = {7, 8, 100} := by decide +kernel
  rw [world] at present
  simp only [Finset.mem_insert, Finset.mem_singleton] at present
  by_cases made : occurrence = 100
  · subst occurrence
    cases (Term.op.inj matched).1
  · have old : occurrence = 7 ∨ occurrence = 8 := by tauto
    have oldPresent : occurrence ∈ middleWorld := by rcases old with rfl | rfl <;> decide +kernel
    have notMade : occurrence ∉ (consumer true).made := by
      change occurrence ∉ ([100] : List Nat)
      simpa only [List.mem_singleton] using made
    have retained : finalRows occurrence = middleRows occurrence := by
      change (if occurrence ∈ (consumer true).made then _ else middleRows occurrence) = middleRows occurrence
      rw [if_neg notMade]
    rw [retained] at matched
    have inMatched := (ContextualGuardSemantics.mem_region locals candidate middleRows middleWorld
      (closedLambda shared) occurrence).mpr ⟨oldPresent, matched⟩
    rw [matching_lambdas_at_admission true future candidate solved] at inMatched
    have wrong := Finset.mem_singleton.mp inMatched
    subst occurrence
    norm_num at old

/-- Moving the consumer's original count guard to its final world rejects
this valid consuming execution. The guard must stay at its admission cut. -/
theorem the_original_count_cannot_be_rebased_to_the_final_cut :
    ContextualGuardSemantics.Ask locals (problem true) middleRows middleWorld (.count (closedLambda shared) 1) ∧
      ¬ ContextualGuardSemantics.Ask locals (problem true) finalRows finalWorld (.count (closedLambda shared) 1) := by
  refine ⟨fun _ future candidate solved => exactly_one_live_lambda_at_admission true future candidate solved, ?_⟩
  intro rebased
  have counted := rebased Empty ground model (causal_model true)
  have absent := the_consumed_lambda_is_absent_at_the_final_cut Empty ground model (causal_model true)
  have empty := (ContextualGuardSemantics.absent_iff_empty locals model finalRows finalWorld (closedLambda shared)).mp absent
  change (ContextualGuardSemantics.region locals model finalRows finalWorld (closedLambda shared)).card = 1 at counted
  rw [empty] at counted
  exact Nat.zero_ne_one counted

/-- Refusal of the later incompatible constraints does not undo the earlier
valid publication. An atomic whole-chain refusal and this executed prefix
therefore have observably different occurrence worlds. -/
theorem joint_refusal_does_not_erase_the_executed_producer_prefix :
    ∃ after : Endpoint locals Nat [(), ()] (), ∃ path : Quiver.Path initial after,
      selections path = [producer] ∧ 99 ∉ before.present ∧ 99 ∈ after.inventory.configuration.present ∧
      ¬ ContextualFrameUnifier.Solvable incompatibleProblem := by
  obtain ⟨after, firing, _ruleEq, selected, _outputsEq⟩ := ContextualExecution.realize_semantic_admission
    locals initial producerRule producer produced producer_covered producer_admitted producer_pattern
  let path : Quiver.Path initial after := .cons .nil firing
  refine ⟨after, path, ?_, by decide +kernel, ?_, repeated_reads_cannot_rebind_one_produced_value_independently⟩
  · change [firing.selection] = [producer]
    rw [selected]
  · rw [firing.physical_result, selected]
    change 99 ∈ fire before.present (producer.commit (T := Unit))
    decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCausalExecutionControls
