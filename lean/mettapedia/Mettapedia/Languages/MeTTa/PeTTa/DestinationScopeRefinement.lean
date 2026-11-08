import Mettapedia.Languages.MeTTa.PeTTa.DestinationRefinement

/-!
# Refinement of retained Destination scopes

Each active work item and saved caller retains its context's own initial
constraints. Collected answers retain their producing context's certificate.
The proofs use the complete source rule family,
including independently selected equation frontiers and collection return.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks

structure ScopeGood {Context : Type} (initial : BindingPredicate Context) (scope : CollectionScope Context) : Prop where
  work : ∀ item ∈ scope.frontier, initial.holds item.2.1 item.1.bindings
  answers : ∀ answer ∈ scope.collected, ∃ context, initial.holds context answer.bindings
  caller : ∀ caller, scope.caller = some caller → initial.holds caller.2.2.1 caller.1.bindings

def ScopesGood {Context : Type} (initial : BindingPredicate Context) (scopes : List (CollectionScope Context)) : Prop :=
  ∀ scope ∈ scopes, ScopeGood initial scope

def actionStates {Supply Context : Type} : Source.ScopeAction Supply Context → List (Source.ScopeState Supply Context)
  | .silent next => [next]
  | .publish _ next => [next]
  | .finish final => [final]
  | .call _ retained => [retained]
  | .fail _ => []

def ActionGood {Supply Context : Type} (initial : BindingPredicate Context) (action : Source.ScopeAction Supply Context) : Prop :=
  ∀ state ∈ actionStates action, ScopesGood initial state.2.scopes

theorem action_silent {Supply Context : Type} {initial : BindingPredicate Context} (next : Source.ScopeState Supply Context)
    (good : ScopesGood initial next.2.scopes) : ActionGood initial (.silent next) := by
  simpa only [ActionGood, actionStates, List.mem_singleton, forall_eq] using good

theorem action_call {Supply Context : Type} {initial : BindingPredicate Context} (retained : Source.ScopeState Supply Context)
    (request : ScopeBoundary) (good : ScopesGood initial retained.2.scopes) :
    ActionGood initial (.call request retained) := by
  simpa only [ActionGood, actionStates, List.mem_singleton, forall_eq] using good

theorem scopes_cons {Context : Type} {initial : BindingPredicate Context} {scope : CollectionScope Context}
    {parents : List (CollectionScope Context)} (first : ScopeGood initial scope)
    (rest : ScopesGood initial parents) : ScopesGood initial (scope :: parents) := by
  intro found present
  rcases List.mem_cons.mp present with rfl | older
  · exact first
  · exact rest found older

theorem ScopeGood.frontier {Context : Type} {initial : BindingPredicate Context} {scope : CollectionScope Context}
    (good : ScopeGood initial scope) (frontier : List (CollectionWork Context))
    (works : ∀ item ∈ frontier, initial.holds item.2.1 item.1.bindings) :
    ScopeGood initial {scope with frontier} := ⟨works, good.answers, good.caller⟩

theorem ScopeGood.record {Context : Type} {initial : BindingPredicate Context} {scope : CollectionScope Context}
    (good : ScopeGood initial scope) (pending : List (CollectionWork Context))
    (works : ∀ item ∈ pending, initial.holds item.2.1 item.1.bindings)
    (answer : CollectedAnswer) (context : Context) (valid : initial.holds context answer.bindings) :
    ScopeGood initial (Scope.record scope pending answer) := by
  refine ⟨works, ?_, good.caller⟩
  intro item present
  rcases List.mem_append.mp present with old | current
  · exact good.answers item old
  · cases List.mem_singleton.mp current
    exact ⟨context, valid⟩

theorem focus_good {Context : Type} {initial : BindingPredicate Context} {scope : CollectionScope Context}
    {parents : List (CollectionScope Context)} {control : Control} {context : Context}
    {origins : List Nat} {pending : List (CollectionWork Context)}
    (good : ScopesGood initial (scope :: parents))
    (frontier : scope.frontier = (control, context, origins) :: pending) :
    ScopeGood initial scope ∧ ScopesGood initial parents ∧ initial.holds context control.bindings ∧
      (∀ item ∈ pending, initial.holds item.2.1 item.1.bindings) := by
  have selected := good scope List.mem_cons_self
  refine ⟨selected, fun parent member => good parent (List.mem_cons_of_mem _ member), ?_, ?_⟩
  · exact selected.work _ (by rw [frontier]; exact List.mem_cons_self)
  · intro item present
    exact selected.work item (by rw [frontier]; exact List.mem_cons_of_mem _ present)

theorem primitive_work_good {Context : Type} {initial : BindingPredicate Context} (control : Control)
    (context : Context) (good : initial.holds context control.bindings) (origins : List Nat)
    (destination : Atom) (older : List Goal) (values : List Atom) :
    ∀ work ∈ primitiveWork control context origins destination older values,
      initial.holds work.2.1 work.1.bindings := by
  intro work present
  obtain ⟨pair, _member, rfl⟩ := List.mem_map.mp present
  exact good

theorem superpose_work_good {Context : Type} {initial : BindingPredicate Context} (control : Control)
    (context : Context) (good : initial.holds context control.bindings) (origins : List Nat)
    (alternatives : List Atom) (destination : Atom) (older : List Goal) :
    ∀ work ∈ superposeWork control context origins alternatives destination older,
      initial.holds work.2.1 work.1.bindings := by
  intro work present
  obtain ⟨pair, _member, rfl⟩ := List.mem_map.mp present
  exact good

theorem selected_frontier_good {initial : Equations} (program : SpaceSemantics.Program)
    (control : Control) (good : Extends initial control.bindings)
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (selected : List (Nat × Control))
    (source : ClauseChoice.Frontier program control head arguments destination older
      (List.range program.equations.length) selected) :
    ∀ choice ∈ selected, Extends initial choice.2.bindings := by
  have computed := (ClauseChoice.choices_iff_frontier _ _ _ _ _ _ _).mpr source
  intro choice present
  rw [← computed] at present
  obtain ⟨equation, _row, accepted⟩ := (ClauseChoice.mem_choices_iff _ _ _ _ _ _ _ _).mp present
  have fields := ClauseChoice.attempt_preserves_caller _ _ _ _ _ _ _ _ accepted
  rw [fields.2.2.2]
  exact good.trans (append_extends _ _)

theorem query_frontier_good {control : Control} {pattern template destination : Atom} {older : List Goal}
    {start : Nat} {rows : List Atom} {selected : List (Nat × Control)}
    (source : QueryFrontier control pattern template destination older start rows selected) :
    ∀ choice ∈ selected, Extends control.bindings choice.2.bindings := by
  induction source with
  | nil => simp
  | selected start row rest bindings tail accepted following ih =>
      intro choice present
      rcases List.mem_cons.mp present with rfl | later
      · exact accepted_extends accepted
      · exact ih choice later
  | refused start row rest tail rejected following ih => exact ih

theorem invocation_preserves {Supply Context : Type} {initial : BindingPredicate Context}
    {fresh : Source.FreshOperations Supply} {program : SpaceSemantics.Program}
    {supply : Supply} {world : World} {scope : CollectionScope Context}
    {parents : List (CollectionScope Context)} {control : Control} {context : Context}
    {origins : List Nat} {pending : List (CollectionWork Context)}
    {head : String} {arguments : List Atom} {destination : Atom} {older : List Goal}
    {environment : Environment} {action : Source.ScopeAction Supply Context}
    (source : Source.Invocation fresh program supply world scope parents control context origins pending
      head arguments destination older environment action)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (good : ScopesGood initial (scope :: parents)) : ActionGood initial action := by
  obtain ⟨scopeGood, parentsGood, controlGood, pendingGood⟩ := focus_good good frontier
  cases source with
  | parsed text value after parseHead input returned =>
      apply action_silent
      apply scopes_cons _ parentsGood
      apply scopeGood.frontier
      intro work present
      rcases List.mem_append.mp present with new | old
      · exact primitive_work_good control context controlGood origins destination older [value] work new
      · exact pendingGood work old
  | primitive state values ordinary known returned =>
      apply action_silent
      apply scopes_cons _ parentsGood
      apply scopeGood.frontier
      intro work present
      rcases List.mem_append.mp present with new | old
      · exact primitive_work_good control context controlGood origins destination older values work new
      · exact pendingGood work old
  | equations selected ordinary known notIO declared selectedRows =>
      have selectedGood := selected_frontier_good program
        (protectControl control (collectionSupport ⟨world, scope :: parents⟩)) (Extends.refl control.bindings)
        head (arguments.map (read environment)) destination older selected selectedRows
      apply action_silent
      apply scopes_cons _ parentsGood
      apply scopeGood.frontier
      intro work present
      rcases List.mem_append.mp present with new | old
      · obtain ⟨choice, member, rfl⟩ := List.mem_map.mp new
        exact initial.closed context _ _ controlGood (selectedGood choice member)
      · exact pendingGood work old
  | parseFault | parseAllocation | parseArity | primitiveFault | unserved => exact action_call _ _ good

theorem active_preserves {Supply Context : Type} {initial : BindingPredicate Context}
    {fresh : Source.FreshOperations Supply} {policy : Policy} {program : SpaceSemantics.Program}
    {supply : Supply} {world : World} {scope : CollectionScope Context}
    {parents : List (CollectionScope Context)} {control : Control} {context : Context}
    {origins : List Nat} {pending : List (CollectionWork Context)} {action : Source.ScopeAction Supply Context}
    (source : Source.ActiveStep fresh policy program supply world scope parents control context origins pending action)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (good : ScopesGood initial (scope :: parents)) : ActionGood initial action := by
  obtain ⟨scopeGood, parentsGood, controlGood, pendingGood⟩ := focus_good good frontier
  cases source with
  | opening older atGoal =>
      apply action_silent
      apply scopes_cons _ parentsGood
      apply scopeGood.frontier
      intro work present
      rcases List.mem_cons.mp present with rfl | old
      · exact controlGood
      · exact pendingGood work old
  | committing older younger kept atGoal partition boundary =>
      apply action_silent
      apply scopes_cons _ parentsGood
      apply scopeGood.frontier
      intro work present
      rcases List.mem_cons.mp present with rfl | old
      · exact controlGood
      · apply pendingGood work
        rw [partition]
        exact List.mem_append_right _ old
  | invalidCommit => exact action_call _ _ good
  | next reached localStep =>
      have extended := local_step_extends localStep reached.control.bindings (by simp [localRecords])
      apply action_silent
      apply scopes_cons _ parentsGood
      apply scopeGood.frontier
      intro work present
      rcases List.mem_cons.mp present with rfl | old
      · change initial.holds reached.context reached.control.bindings
        rw [silent_context_preserved localStep]
        exact initial.closed context _ _ controlGood extended
      · exact pendingGood work old
  | refused bindings reached localStep =>
      exact action_silent _ (scopes_cons (scopeGood.frontier _ pendingGood) parentsGood)
  | answered value bindings reached localStep =>
      have extended := local_step_extends localStep reached.control.bindings (by simp [localRecords])
      have record : bindings = reached.control.bindings := finished_record_is_reached localStep
      have returnedGood : initial.holds context bindings := by
        rw [record]
        exact initial.closed context _ _ controlGood extended
      have afterGood := scopes_cons (scopeGood.record pending pendingGood ⟨value, bindings, origins, []⟩ context returnedGood) parentsGood
      split <;> simpa only [ActionGood, actionStates, List.mem_singleton, forall_eq] using afterGood
  | boundary => exact action_call _ _ good
  | invocation head arguments destination older environment action atCall resolved notPrint served =>
      exact invocation_preserves served frontier good
  | queried location pattern template destination older environment rows selected atQuery resolved readRows selectedRows =>
      have selectedGood := query_frontier_good selectedRows
      apply action_silent
      apply scopes_cons _ parentsGood
      apply scopeGood.frontier
      intro work present
      rcases List.mem_append.mp present with new | old
      · obtain ⟨choice, member, rfl⟩ := List.mem_map.mp new
        exact initial.closed context _ _ controlGood (selectedGood choice member)
      · exact pendingGood work old
  | queryFault => exact action_call _ _ good
  | collapsed expression destination older atGoal =>
      apply action_silent
      apply scopes_cons
      · refine ⟨?_, ?_, ?_⟩
        · intro work present
          cases List.mem_singleton.mp present
          exact controlGood
        · intro answer present
          cases present
        · intro caller retained
          cases Option.some.inj retained
          exact controlGood
      · exact scopes_cons (scopeGood.frontier _ pendingGood) parentsGood
  | choice alternatives destination older atGoal =>
      apply action_silent
      apply scopes_cons _ parentsGood
      apply scopeGood.frontier
      intro work present
      rcases List.mem_append.mp present with new | old
      · exact superpose_work_good control context controlGood origins alternatives destination older work new
      · exact pendingGood work old
  | empty => exact action_silent _ (scopes_cons (scopeGood.frontier _ pendingGood) parentsGood)

/-- Collection restores the saved caller's own record, not a chosen child's
record. The common initial constraints therefore survive generative copying. -/
theorem collection_preserves {Supply Context : Type} {initial : BindingPredicate Context}
    {fresh : Source.FreshOperations Supply} {before after : Source.ScopeState Supply Context}
    (source : Source.CollectionReturn fresh before after)
    (good : ScopesGood initial before.2.scopes) : ScopesGood initial after.2.scopes := by
  cases source with
  | complete supply after world answers caller parent parents copied ready returned valid =>
      have childGood := good ⟨[], answers, some caller⟩ List.mem_cons_self
      have callerGood := childGood.caller caller rfl
      have parentGood := good parent (by simp)
      have parentsGood : ScopesGood initial parents := fun scope member => good scope (by simp [member])
      apply scopes_cons _ parentsGood
      apply parentGood.frontier
      intro work present
      rcases List.mem_cons.mp present with rfl | old
      · exact callerGood
      · exact parentGood.work work old

/-- Every retained state of the complete scoped source operation preserves
the initial constraints: success, publication, refusal and retained faults. -/
theorem scoped_preserves {Supply Context : Type} {initial : BindingPredicate Context}
    {fresh : Source.FreshOperations Supply} {policy : Policy} {program : SpaceSemantics.Program}
    {before : Source.ScopeState Supply Context} {action : Source.ScopeAction Supply Context}
    (source : Source.ScopedStep fresh policy program before action)
    (good : ScopesGood initial before.2.scopes) : ActionGood initial action := by
  cases source with
  | active supply world scope parents control context origins pending action frontier source =>
      exact active_preserves source frontier good
  | finished => simpa only [ActionGood, actionStates, List.mem_singleton, forall_eq] using good
  | collected source => exact action_silent _ (collection_preserves source good)
  | associated | allocation => exact action_call _ _ good

theorem actual_scope_preserves {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (initial : BindingPredicate Context) (before : ScopedCursor Context)
    (valid : ScopesValid before.2.scopes) (good : ScopesGood initial before.2.scopes) :
    ActionGood initial (scopeStep policy program before) := by
  obtain ⟨action, source⟩ := Source.scoped_has_source policy program before valid
  rw [source.execution]
  exact scoped_preserves source good

/-- Continuing source steps only: retained requests and final states do not
become invented progress transitions. Publication carries its exact events. -/
def Continues {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (before after : ScopedCursor Context) : Prop :=
  scopeStep policy program before = .silent after ∨
    ∃ events, scopeStep policy program before = .publish events after

theorem continuing_preserves {Context : Type} {policy : Policy} {program : SpaceSemantics.Program}
    {initial : BindingPredicate Context} {before after : ScopedCursor Context}
    (step : Continues policy program before after) (valid : ScopesValid before.2.scopes)
    (good : ScopesGood initial before.2.scopes) :
    ScopesValid after.2.scopes ∧ ScopesGood initial after.2.scopes := by
  have nested := scopeStep_scopes_valid policy program before valid
  have preserved := actual_scope_preserves policy program initial before valid good
  rcases step with silent | ⟨events, published⟩
  · rw [silent] at nested preserved
    exact ⟨nested, preserved after (by simp [actionStates])⟩
  · rw [published] at nested preserved
    exact ⟨nested, preserved after (by simp [actionStates])⟩

theorem path_preserves {Context : Type} {policy : Policy} {program : SpaceSemantics.Program}
    {initial : BindingPredicate Context} {before after : ScopedCursor Context}
    (path : Relation.ReflTransGen (Continues policy program) before after)
    (valid : ScopesValid before.2.scopes) (good : ScopesGood initial before.2.scopes) :
    ScopesValid after.2.scopes ∧ ScopesGood initial after.2.scopes := by
  induction path with
  | refl => exact ⟨valid, good⟩
  | tail previous step induction => exact continuing_preserves step induction.1 induction.2

/-- Every published answer has a producing context and its actual record
refines that context's own initial equations. Saved siblings need not share
the active call's stronger initial record. -/
theorem published_record_refines {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (initial : Context → Equations) (before after : ScopedCursor Context) (events : List CollectedAnswer)
    (good : ScopesGood (BindingPredicate.initialRows initial) before.2.scopes)
    (published : scopeStep policy program before = .publish events after) :
    ∃ context value bindings origins environment,
      events = [⟨value, bindings, origins, []⟩] ∧
      Solves environment bindings ∧ Extends (initial context) bindings := by
  obtain ⟨scope, parents, control, context, pending, value, bindings, origins, environment,
    scopes, frontier, _goals, _resolved, eventsEq, record, _readout, solved⟩ :=
    scope_published_origin policy program before after events published
  have reached := (focus_good (scopes ▸ good) frontier).2.2.1
  refine ⟨context, value, bindings, origins, environment, eventsEq, solved, ?_⟩
  rw [record]
  exact reached

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport
