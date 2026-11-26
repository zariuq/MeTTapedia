import Mettapedia.Languages.CHR.MachineTick
import Mettapedia.Languages.CHR.MachinePolicySteps

/-! Machine runs refine the newest-first policy. Every tick is a finite run
of policy steps that keeps the simulation; the search case uses
`search_simulates_policy`, and every run keeps each slot newest first. So
every bounded machine run is a run of the policy-qualified refined
semantics, with the operational outcome. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

theorem skip_other_key_policy (program : Program) (state : CHR.State) (active cursor : Nat) (tail : List CHR.Task)
    (key : Key) (values : List Value)
    (tasks : state.tasks = .scan active cursor :: tail) (running : state.status = .running)
    (occurrence : RuleOccurrence) (atCursor : (occurrences program)[cursor]? = some occurrence)
    (other : atOf program key occurrence = none)
    (activeStored : ∀ stored ∈ state.store, stored.id = active → stored.constraint = ⟨key.1, values⟩)
    (arity : values.length = key.2) : PolicyStep program state { state with tasks := .scan active (cursor + 1) :: tail } := by
  obtain ⟨rule, head, ruleAt, headAt⟩ :=
    occurrence_valid program occurrence (List.mem_of_getElem? atCursor)
  have different : Head.key head ≠ key := by
    intro same
    simp [atOf, ruleAt, headAt, same] at other
  apply PolicyStep.skip state active cursor tail occurrence rule tasks running atCursor ruleAt
  intro environment selection matched activeAt
  exfalso
  obtain ⟨split, _, keptMatch, removedMatch, _, _⟩ := matched
  obtain ⟨chosen, chosenAt, isActive⟩ := activeAt
  have instantiated := forall₂_at (forall₂_append keptMatch removedMatch) headAt chosenAt
  have inStore : chosen ∈ state.store := by
    apply split.symm.subset
    have inHeads : chosen ∈ selection.heads := List.mem_of_getElem? chosenAt
    simp only [Selection.heads, List.mem_append] at inHeads ⊢
    rcases inHeads with kept | removed
    · exact .inl (.inl kept)
    · exact .inl (.inr removed)
  have stored := activeStored chosen inStore isActive
  rw [stored] at instantiated
  obtain ⟨sameName, arguments⟩ := head_instantiate_some instantiated
  rw [instantiateTerms_eq] at arguments
  have length := mapM_length arguments
  apply different
  simp only [Head.key] at sameName ⊢
  rw [sameName, ← length, arity]

theorem skip_until_policy (program : Program) (key : Key) (values : List Value) (active : Nat) (tail : List CHR.Task)
    (arity : values.length = key.2) :
    ∀ (distance cursor : Nat) (state : CHR.State),
      state.tasks = .scan active cursor :: tail → state.status = .running →
      (∀ stored ∈ state.store, stored.id = active → stored.constraint = ⟨key.1, values⟩) →
      (∀ offset < distance, ∃ occurrence, (occurrences program)[cursor + offset]? = some occurrence ∧
        atOf program key occurrence = none) →
      Relation.ReflTransGen (PolicyStep program) state { state with tasks := .scan active (cursor + distance) :: tail }
  | 0, cursor, state, tasks, _, _, _ => by
    have same : { state with tasks := CHR.Task.scan active (cursor + 0) :: tail } = state := by
      rw [Nat.add_zero, ← tasks]
    rw [same]
  | distance + 1, cursor, state, tasks, running, stored, others => by
    obtain ⟨occurrence, atCursor, other⟩ := others 0 (Nat.succ_pos _)
    rw [Nat.add_zero] at atCursor
    have first := skip_other_key_policy program state active cursor tail key values tasks running occurrence atCursor
      other stored arity
    have rest := skip_until_policy program key values active tail arity distance (cursor + 1)
      { state with tasks := .scan active (cursor + 1) :: tail } rfl running stored
      (fun offset bounded => by
        obtain ⟨later, atLater, otherLater⟩ := others (offset + 1) (by omega)
        exact ⟨later, by rwa [show cursor + 1 + offset = cursor + (offset + 1) by omega], otherLater⟩)
    have joined := Relation.ReflTransGen.head first rest
    simpa [show cursor + 1 + distance = cursor + (distance + 1) by omega] using joined

theorem introduce_simulates_policy (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (running : state.status = .running)
    (head : Head) (environment other : Environment) (agree : Agree environment other)
    (resume : Task) (goals : List Goal) (tail : List Task) (tailAbstract : List CHR.Task) (seeds : List Nat)
    (abstractTasks : abstract.tasks = .goals other (.tell head :: goals) :: tailAbstract)
    (machineTasks : state.tasks.drop 1 = tail)
    (resumeRel : TaskRel program state.store state.history state.next resume (.goals other goals))
    (resumeNotSearch : resume.isSearch = false)
    (tailRel : List.Forall₂ (TaskRel program state.store state.history state.next) tail tailAbstract) :
    ∃ abstract', Relation.ReflTransGen (PolicyStep program) abstract abstract' ∧
      Simulates program (introduce (table program) head environment resume state.tasks tail state seeds) abstract' := by
  obtain ⟨next, step, related⟩ := introduce_step_simulates
    program state abstract simulates running head environment other agree
      resume goals tail tailAbstract seeds abstractTasks machineTasks resumeRel resumeNotSearch tailRel
  exact ⟨next, .single (PolicyStep.of_goal_task abstractTasks step), related⟩

theorem endGoals_simulates_policy (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (running : state.status = .running)
    (task : Task) (tail : List Task) (tasks : state.tasks = task :: tail)
    (environment : Environment) (tailAbstract : List CHR.Task)
    (abstractTasks : abstract.tasks = .goals environment [] :: tailAbstract)
    (tailRel : List.Forall₂ (TaskRel program state.store state.history state.next) tail tailAbstract) :
    ∃ abstract', Relation.ReflTransGen (PolicyStep program) abstract abstract' ∧
      Simulates program { state with tasks := tail } abstract' := by
  obtain ⟨next, step, related⟩ := endGoals_step_simulates
    program state abstract simulates running task tail tasks
      environment tailAbstract abstractTasks tailRel
  exact ⟨next, .single (PolicyStep.of_goal_task abstractTasks step), related⟩

theorem seed_simulates_policy (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (running : state.status = .running)
    (head : Head) (heads : List Head) (tail : List Task) (tailAbstract : List CHR.Task)
    (tasks : state.tasks = .seeds (head :: heads) :: tail)
    (abstractTasks : abstract.tasks = .goals [] ((head :: heads).map Goal.tell) :: tailAbstract)
    (ground : ∀ seed ∈ head :: heads, (instantiateTerms [] seed.arguments).isSome)
    (tailRel : List.Forall₂ (TaskRel program state.store state.history state.next) tail tailAbstract) :
    ∃ abstract', Relation.ReflTransGen (PolicyStep program) abstract abstract' ∧
      Simulates program
        (introduce (table program) head [] (.seeds heads) state.tasks tail state (state.next :: state.seeds))
        abstract' := by
  obtain ⟨next, step, related⟩ := seed_step_simulates
    program state abstract simulates running head heads tail tailAbstract
      tasks abstractTasks ground tailRel
  exact ⟨next, .single (PolicyStep.of_goal_task abstractTasks step), related⟩

theorem tell_simulates_policy (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (running : state.status = .running)
    (environment other : Environment) (agree : Agree environment other)
    (head : Head) (goals : List Goal) (tail : List Task) (tailAbstract : List CHR.Task)
    (tasks : state.tasks = .goals environment (.tell head :: goals) :: tail)
    (abstractTasks : abstract.tasks = .goals other (.tell head :: goals) :: tailAbstract)
    (tailRel : List.Forall₂ (TaskRel program state.store state.history state.next) tail tailAbstract) :
    ∃ abstract', Relation.ReflTransGen (PolicyStep program) abstract abstract' ∧
      Simulates program (goal (table program) environment (.tell head) goals tail state) abstract' := by
  obtain ⟨next, step, related⟩ := tell_step_simulates
    program state abstract simulates running environment other agree head goals tail tailAbstract
      tasks abstractTasks tailRel
  exact ⟨next, .single (PolicyStep.of_goal_task abstractTasks step), related⟩

theorem assign_simulates_policy (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (running : state.status = .running)
    (environment other : Environment) (agree : Agree environment other)
    (index : Nat) (expression : IntExpr) (goals : List Goal) (tail : List Task) (tailAbstract : List CHR.Task)
    (tasks : state.tasks = .goals environment (.assign index expression :: goals) :: tail)
    (abstractTasks : abstract.tasks = .goals other (.assign index expression :: goals) :: tailAbstract)
    (tailRel : List.Forall₂ (TaskRel program state.store state.history state.next) tail tailAbstract) :
    ∃ abstract', Relation.ReflTransGen (PolicyStep program) abstract abstract' ∧
      Simulates program (goal (table program) environment (.assign index expression) goals tail state)
        abstract' := by
  obtain ⟨next, step, related⟩ := assign_step_simulates
    program state abstract simulates running environment other agree index expression
      goals tail tailAbstract tasks abstractTasks tailRel
  exact ⟨next, .single (PolicyStep.of_goal_task abstractTasks step), related⟩

theorem fail_simulates_policy (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (running : state.status = .running)
    (environment other : Environment) (goals : List Goal) (tail : List Task) (tailAbstract : List CHR.Task)
    (abstractTasks : abstract.tasks = .goals other (.fail :: goals) :: tailAbstract) :
    ∃ abstract', Relation.ReflTransGen (PolicyStep program) abstract abstract' ∧
      Simulates program (goal (table program) environment .fail goals tail state) abstract' := by
  obtain ⟨next, step, related⟩ := fail_step_simulates
    program state abstract simulates running environment other goals tail tailAbstract abstractTasks
  exact ⟨next, .single (PolicyStep.of_goal_task abstractTasks step), related⟩

theorem scan_simulates_policy (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (running : state.status = .running)
    (active : Nat) (key : Key) (values : List Value) (cursor : Nat) (tail : List Task)
    (tailAbstract : List CHR.Task)
    (tasks : state.tasks = .scan active key values (keyAtsFrom program key cursor) :: tail)
    (abstractTasks : abstract.tasks = .scan active cursor :: tailAbstract)
    (below : active < state.next) (stored : ActiveStored state.store active key values)
    (tailRel : List.Forall₂ (TaskRel program state.store state.history state.next) tail tailAbstract) :
    ∃ abstract', Relation.ReflTransGen (PolicyStep program) abstract abstract' ∧
      Simulates program (scan active key values (keyAtsFrom program key cursor) tail state) abstract' := by
  have abstractRunning : abstract.status = .running := statusRel_running (running ▸ simulates.status)
  have shallow := tail_shallow simulates tasks
  have abstractStored := abstract_active simulates stored
  unfold scan
  by_cases living : alive active (slot key state.store) = true
  · rw [if_neg (by simp [living])]
    cases listed : keyAtsFrom program key cursor with
    | nil =>
      have others := keyAtsFrom_nil program key ((occurrences program).length - cursor) cursor (Nat.le_refl _) listed
      have skipped := skip_until_policy program key values active tailAbstract stored.1
        ((occurrences program).length - cursor) cursor abstract abstractTasks abstractRunning abstractStored others
      have ended : PolicyStep program
          { abstract with tasks := .scan active (cursor + ((occurrences program).length - cursor)) :: tailAbstract }
          { abstract with tasks := tailAbstract } :=
        PolicyStep.endScan _ active _ tailAbstract rfl abstractRunning (List.getElem?_eq_none_iff.mpr (by omega))
      refine ⟨{ abstract with tasks := tailAbstract }, skipped.tail ended, ?_⟩
      exact ⟨simulates.store, simulates.coherent, simulates.fresh, simulates.history, simulates.next,
        simulates.status, fun _ => tailRel, fun task inside => shallow task (List.mem_of_mem_drop inside)⟩
    | cons occurrence after =>
      obtain ⟨distance, before, found, atFound, matched, afterEq⟩ :=
        keyAtsFrom_cons program key ((occurrences program).length - cursor) cursor (Nat.le_refl _) occurrence after listed
      have skipped := skip_until_policy program key values active tailAbstract stored.1 distance cursor abstract
        abstractTasks abstractRunning abstractStored before
      obtain ⟨_, _, _, head, headAt, _⟩ := atOf_some matched
      dsimp only
      cases heads : occurrence.body.kept ++ occurrence.body.removed with
      | nil =>
        exfalso
        have empty : occurrence.body.heads = [] := heads
        rw [empty] at headAt
        simp at headAt
      | cons first later =>
        refine ⟨{ abstract with tasks := .scan active (cursor + distance) :: tailAbstract }, skipped, ?_⟩
        have enumerated : [] ++ pending state.store occurrence.head active values
            [⟨0, first :: later, candidates 0 occurrence.head active values first state.store, [], [], []⟩] =
            selections state.store occurrence.head active values 0 occurrence.body.heads [] [] [] := by
          rw [List.nil_append, pending_start]
          show _ = selections _ _ _ _ 0 (occurrence.body.kept ++ occurrence.body.removed) [] [] []
          rw [heads]
        refine ⟨simulates.store, simulates.coherent, simulates.fresh, simulates.history, simulates.next,
          simulates.status, fun _ => .cons ?_ tailRel, fun task inside => shallow task (by simpa using inside)⟩
        rw [afterEq]
        exact .search active key values (cursor + distance) occurrence _ found atFound matched below stored
          (alive_lift stored living) [] enumerated (fun _ impossible => by cases impossible)
  · rw [if_pos (by simp [living])]
    have missing : ∀ occurrence ∈ abstract.store, occurrence.id ≠ active := by
      intro occurrence member same
      apply living
      have inContents := simulates.store.subset member
      have equal := stored.2 occurrence inContents same
      have inSlot := slot_of_contents simulates.coherent inContents
      simp only [equal, lift] at inSlot
      rw [stored.1] at inSlot
      exact (alive_iff active _).mpr ⟨_, inSlot, rfl⟩
    refine ⟨{ abstract with tasks := tailAbstract },
      .single (PolicyStep.missingActive abstract active cursor tailAbstract abstractTasks abstractRunning missing), ?_⟩
    exact ⟨simulates.store, simulates.coherent, simulates.fresh, simulates.history, simulates.next,
      simulates.status, fun _ => tailRel, fun task inside => shallow task (List.mem_of_mem_drop inside)⟩

theorem tick_simulates_policy (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (descending : Descending state.store) :
    ∃ abstract', Relation.ReflTransGen (PolicyStep program) abstract abstract' ∧
      Simulates program (tick (table program) state) abstract' := by
  cases running : state.status with
  | failed =>
    have same : tick (table program) state = state := by
      unfold tick
      rw [running]
    rw [same]
    exact ⟨abstract, .refl, simulates⟩
  | faulted reason =>
    have same : tick (table program) state = state := by
      unfold tick
      rw [running]
    rw [same]
    exact ⟨abstract, .refl, simulates⟩
  | running =>
    cases tasks : state.tasks with
    | nil =>
      have same : tick (table program) state = state := by
        unfold tick
        rw [running, tasks]
      rw [same]
      exact ⟨abstract, .refl, simulates⟩
    | cons task tail =>
      have related := simulates.tasks running
      rw [tasks] at related
      obtain ⟨abstractTask, tailAbstract, first, tailRel, abstractTasks⟩ :=
        List.forall₂_cons_left_iff.mp related
      cases first with
      | seeds heads ground =>
        cases heads with
        | nil =>
          have ticked : tick (table program) state = { state with tasks := tail } := by
            unfold tick
            rw [running, tasks]
          rw [ticked]
          exact endGoals_simulates_policy program state abstract simulates running _ tail tasks [] tailAbstract
            abstractTasks tailRel
        | cons head heads =>
          have ticked : tick (table program) state =
              introduce (table program) head [] (.seeds heads) state.tasks tail state
                (state.next :: state.seeds) := by
            unfold tick
            rw [running, tasks]
          rw [ticked]
          exact seed_simulates_policy program state abstract simulates running head heads tail tailAbstract tasks
            abstractTasks ground tailRel
      | goals environment other goals agree =>
        cases goals with
        | nil =>
          have ticked : tick (table program) state = { state with tasks := tail } := by
            unfold tick
            rw [running, tasks]
          rw [ticked]
          exact endGoals_simulates_policy program state abstract simulates running _ tail tasks other tailAbstract
            abstractTasks tailRel
        | cons current goals =>
          have ticked : tick (table program) state = goal (table program) environment current goals tail state := by
            unfold tick
            rw [running, tasks]
          rw [ticked]
          cases current with
          | tell head =>
            exact tell_simulates_policy program state abstract simulates running environment other agree head goals tail
              tailAbstract tasks abstractTasks tailRel
          | assign index expression =>
            exact assign_simulates_policy program state abstract simulates running environment other agree index
              expression goals tail tailAbstract tasks abstractTasks tailRel
          | fail =>
            exact fail_simulates_policy program state abstract simulates running environment other goals tail tailAbstract
              abstractTasks
      | scan active key values cursor below stored =>
        have ticked : tick (table program) state =
            scan active key values (keyAtsFrom program key cursor) tail state := by
          unfold tick
          rw [running, tasks]
        rw [ticked]
        exact scan_simulates_policy program state abstract simulates running active key values cursor tail tailAbstract
          tasks abstractTasks below stored tailRel
      | search active key values cursor occurrence frames found atCursor matched below stored alive consumed
          enumerated rejected =>
        have ticked : tick (table program) state =
            search active key values occurrence (keyAtsFrom program key (cursor + 1)) frames tail state := by
          unfold tick
          rw [running, tasks]
        rw [ticked]
        exact search_simulates_policy program state abstract simulates descending running active key values cursor occurrence frames
          found tail tailAbstract tasks abstractTasks atCursor matched below stored alive consumed enumerated
          rejected tailRel

theorem advance_simulates_policy (program : Program) :
    ∀ (budget : Nat) (state : State) (abstract : CHR.State), Simulates program state abstract →
      Descending state.store →
      ∃ abstract', Relation.ReflTransGen (PolicyStep program) abstract abstract' ∧
        Simulates program (advance (table program) budget state) abstract'
  | 0, _, abstract, simulates, _ => ⟨abstract, .refl, simulates⟩
  | budget + 1, state, abstract, simulates, descending => by
    unfold advance
    split
    · obtain ⟨middle, first, related⟩ := tick_simulates_policy program state abstract simulates descending
      obtain ⟨final, rest, finalRelated⟩ := advance_simulates_policy program budget _ middle related
        (tick_descending _ state descending simulates.fresh)
      exact ⟨final, first.trans rest, finalRelated⟩
    · exact ⟨abstract, .refl, simulates⟩

/-- **The machine runs the newest-first policy.** A bounded machine run from
the seeds of `constraints` is a run of the policy-qualified refined semantics
from the initial state, and the machine shows the outcome of the state it
reaches. -/
theorem advance_refines_policy (program : Program) (constraints : List Constraint) (budget : Nat) :
    ∃ abstract, Relation.ReflTransGen (PolicyStep program) (initial constraints) abstract ∧
      Simulates program (advance (table program) budget (start (constraints.map Constraint.asHead))) abstract ∧
      OutcomeRel (outcome (advance (table program) budget (start (constraints.map Constraint.asHead))))
        (observe abstract) := by
  obtain ⟨abstract, run, related⟩ := advance_simulates_policy program budget _ _ (start_simulates program constraints)
    (start_descending _)
  exact ⟨abstract, run, related, outcome_simulates program _ abstract related⟩

#print axioms advance_refines_policy

end Mettapedia.Languages.CHR.Machine
