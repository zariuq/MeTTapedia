import Mettapedia.Languages.CHR.MachinePolicyRuns

/-! The machine makes progress. A goal tick is at least one policy step; a
scan or search tick is at least one policy step, or it keeps the operational
state while the work left before the next step decreases. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

theorem introduce_progress (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (running : state.status = .running)
    (head : Head) (environment other : Environment) (agree : Agree environment other)
    (resume : Task) (goals : List Goal) (tail : List Task) (tailAbstract : List CHR.Task) (seeds : List Nat)
    (abstractTasks : abstract.tasks = .goals other (.tell head :: goals) :: tailAbstract)
    (machineTasks : state.tasks.drop 1 = tail)
    (resumeRel : TaskRel program state.store state.history state.next resume (.goals other goals))
    (resumeNotSearch : resume.isSearch = false)
    (tailRel : List.Forall₂ (TaskRel program state.store state.history state.next) tail tailAbstract) :
    ∃ abstract', Relation.TransGen (PolicyStep program) abstract abstract' ∧
      Simulates program (introduce (table program) head environment resume state.tasks tail state seeds) abstract' := by
  obtain ⟨next, step, related⟩ := introduce_step_simulates
    program state abstract simulates running head environment other agree
      resume goals tail tailAbstract seeds abstractTasks machineTasks resumeRel resumeNotSearch tailRel
  exact ⟨next, .single (PolicyStep.of_goal_task abstractTasks step), related⟩

theorem endGoals_progress (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (running : state.status = .running)
    (task : Task) (tail : List Task) (tasks : state.tasks = task :: tail)
    (environment : Environment) (tailAbstract : List CHR.Task)
    (abstractTasks : abstract.tasks = .goals environment [] :: tailAbstract)
    (tailRel : List.Forall₂ (TaskRel program state.store state.history state.next) tail tailAbstract) :
    ∃ abstract', Relation.TransGen (PolicyStep program) abstract abstract' ∧
      Simulates program { state with tasks := tail } abstract' := by
  obtain ⟨next, step, related⟩ := endGoals_step_simulates
    program state abstract simulates running task tail tasks
      environment tailAbstract abstractTasks tailRel
  exact ⟨next, .single (PolicyStep.of_goal_task abstractTasks step), related⟩

theorem seed_progress (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (running : state.status = .running)
    (head : Head) (heads : List Head) (tail : List Task) (tailAbstract : List CHR.Task)
    (tasks : state.tasks = .seeds (head :: heads) :: tail)
    (abstractTasks : abstract.tasks = .goals [] ((head :: heads).map Goal.tell) :: tailAbstract)
    (ground : ∀ seed ∈ head :: heads, (instantiateTerms [] seed.arguments).isSome)
    (tailRel : List.Forall₂ (TaskRel program state.store state.history state.next) tail tailAbstract) :
    ∃ abstract', Relation.TransGen (PolicyStep program) abstract abstract' ∧
      Simulates program
        (introduce (table program) head [] (.seeds heads) state.tasks tail state (state.next :: state.seeds))
        abstract' := by
  obtain ⟨next, step, related⟩ := seed_step_simulates
    program state abstract simulates running head heads tail tailAbstract
      tasks abstractTasks ground tailRel
  exact ⟨next, .single (PolicyStep.of_goal_task abstractTasks step), related⟩

theorem tell_progress (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (running : state.status = .running)
    (environment other : Environment) (agree : Agree environment other)
    (head : Head) (goals : List Goal) (tail : List Task) (tailAbstract : List CHR.Task)
    (tasks : state.tasks = .goals environment (.tell head :: goals) :: tail)
    (abstractTasks : abstract.tasks = .goals other (.tell head :: goals) :: tailAbstract)
    (tailRel : List.Forall₂ (TaskRel program state.store state.history state.next) tail tailAbstract) :
    ∃ abstract', Relation.TransGen (PolicyStep program) abstract abstract' ∧
      Simulates program (goal (table program) environment (.tell head) goals tail state) abstract' := by
  obtain ⟨next, step, related⟩ := tell_step_simulates
    program state abstract simulates running environment other agree head goals tail tailAbstract
      tasks abstractTasks tailRel
  exact ⟨next, .single (PolicyStep.of_goal_task abstractTasks step), related⟩

theorem assign_progress (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (running : state.status = .running)
    (environment other : Environment) (agree : Agree environment other)
    (index : Nat) (expression : IntExpr) (goals : List Goal) (tail : List Task) (tailAbstract : List CHR.Task)
    (tasks : state.tasks = .goals environment (.assign index expression :: goals) :: tail)
    (abstractTasks : abstract.tasks = .goals other (.assign index expression :: goals) :: tailAbstract)
    (tailRel : List.Forall₂ (TaskRel program state.store state.history state.next) tail tailAbstract) :
    ∃ abstract', Relation.TransGen (PolicyStep program) abstract abstract' ∧
      Simulates program (goal (table program) environment (.assign index expression) goals tail state)
        abstract' := by
  obtain ⟨next, step, related⟩ := assign_step_simulates
    program state abstract simulates running environment other agree index expression
      goals tail tailAbstract tasks abstractTasks tailRel
  exact ⟨next, .single (PolicyStep.of_goal_task abstractTasks step), related⟩

theorem fail_progress (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (running : state.status = .running)
    (environment other : Environment) (goals : List Goal) (tail : List Task) (tailAbstract : List CHR.Task)
    (abstractTasks : abstract.tasks = .goals other (.fail :: goals) :: tailAbstract) :
    ∃ abstract', Relation.TransGen (PolicyStep program) abstract abstract' ∧
      Simulates program (goal (table program) environment .fail goals tail state) abstract' := by
  obtain ⟨next, step, related⟩ := fail_step_simulates
    program state abstract simulates running environment other goals tail tailAbstract abstractTasks
  exact ⟨next, .single (PolicyStep.of_goal_task abstractTasks step), related⟩

/-- The work before the first operational step of a rule occurrence's search. -/
def startWork (store : Store) (active : Nat) (values : List Value) (occurrence : At) : Nat :=
  match occurrence.body.kept ++ occurrence.body.removed with
  | [] => 0
  | first :: later => weight store occurrence.head active values
      [⟨0, first :: later, candidates 0 occurrence.head active values first store, [], [], []⟩]

/-- The work a scan can do before its next operational step. -/
def scanWork (store : Store) (active : Nat) (values : List Value) : List At → Nat
  | [] => 0
  | occurrence :: after => startWork store active values occurrence + 1 + scanWork store active values after

theorem scan_progress (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (running : state.status = .running)
    (active : Nat) (key : Key) (values : List Value) (cursor : Nat) (tail : List Task)
    (tailAbstract : List CHR.Task)
    (tasks : state.tasks = .scan active key values (keyAtsFrom program key cursor) :: tail)
    (abstractTasks : abstract.tasks = .scan active cursor :: tailAbstract)
    (below : active < state.next) (stored : ActiveStored state.store active key values)
    (tailRel : List.Forall₂ (TaskRel program state.store state.history state.next) tail tailAbstract) :
    (∃ abstract', Relation.TransGen (PolicyStep program) abstract abstract' ∧
      Simulates program (scan active key values (keyAtsFrom program key cursor) tail state) abstract') ∨
    (Simulates program (scan active key values (keyAtsFrom program key cursor) tail state) abstract ∧
      ∃ occurrence after frames, (scan active key values (keyAtsFrom program key cursor) tail state).tasks =
          .search active key values occurrence after frames :: tail ∧
        (scan active key values (keyAtsFrom program key cursor) tail state).store = state.store ∧
        weight state.store occurrence.head active values frames <
          scanWork state.store active values (keyAtsFrom program key cursor)) := by
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
      refine .inl ⟨{ abstract with tasks := tailAbstract }, Relation.TransGen.tail' skipped ended, ?_⟩
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
        suffices related : Simulates program { state with tasks := (Task.search active key values occurrence after
            [⟨0, first :: later, candidates 0 occurrence.head active values first state.store, [], [], []⟩] :: tail) }
            { abstract with tasks := (.scan active (cursor + distance) :: tailAbstract) } by
          rcases Relation.reflTransGen_iff_eq_or_transGen.mp skipped with same | moved
          · refine .inr ⟨same ▸ related, occurrence, after, _, rfl, rfl, ?_⟩
            simp only [scanWork, startWork, heads]
            omega
          · exact .inl ⟨_, moved, related⟩
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
    refine .inl ⟨{ abstract with tasks := tailAbstract },
      .single (PolicyStep.missingActive abstract active cursor tailAbstract abstractTasks abstractRunning missing), ?_⟩
    exact ⟨simulates.store, simulates.coherent, simulates.fresh, simulates.history, simulates.next,
      simulates.status, fun _ => tailRel, fun task inside => shallow task (List.mem_of_mem_drop inside)⟩

#print axioms scan_progress

/-- The work the machine can do before its next operational step. -/
def admin (state : State) : Nat :=
  match state.tasks with
  | .search active _ values occurrence _ frames :: _ => weight state.store occurrence.head active values frames
  | .scan active _ values remaining :: _ => scanWork state.store active values remaining
  | _ => 0

/-- **Every tick progresses.** A running tick takes at least one policy step,
or keeps the operational state while the work before the next step drops. -/
theorem tick_progress (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (descending : Descending state.store)
    (isRunning : state.status = .running) (busy : state.tasks ≠ []) :
    (∃ abstract', Relation.TransGen (PolicyStep program) abstract abstract' ∧
      Simulates program (tick (table program) state) abstract') ∨
    (Simulates program (tick (table program) state) abstract ∧ admin (tick (table program) state) < admin state) := by
  cases running : state.status with
  | failed =>
    have same : tick (table program) state = state := by
      unfold tick
      rw [running]
    rw [isRunning] at running
    cases running
  | faulted reason =>
    have same : tick (table program) state = state := by
      unfold tick
      rw [running]
    rw [isRunning] at running
    cases running
  | running =>
    cases tasks : state.tasks with
    | nil =>
      have same : tick (table program) state = state := by
        unfold tick
        rw [running, tasks]
      exact absurd tasks busy
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
          exact .inl <| endGoals_progress program state abstract simulates running _ tail tasks [] tailAbstract
            abstractTasks tailRel
        | cons head heads =>
          have ticked : tick (table program) state =
              introduce (table program) head [] (.seeds heads) state.tasks tail state
                (state.next :: state.seeds) := by
            unfold tick
            rw [running, tasks]
          rw [ticked]
          exact .inl <| seed_progress program state abstract simulates running head heads tail tailAbstract tasks
            abstractTasks ground tailRel
      | goals environment other goals agree =>
        cases goals with
        | nil =>
          have ticked : tick (table program) state = { state with tasks := tail } := by
            unfold tick
            rw [running, tasks]
          rw [ticked]
          exact .inl <| endGoals_progress program state abstract simulates running _ tail tasks other tailAbstract
            abstractTasks tailRel
        | cons current goals =>
          have ticked : tick (table program) state = goal (table program) environment current goals tail state := by
            unfold tick
            rw [running, tasks]
          rw [ticked]
          cases current with
          | tell head =>
            exact .inl <| tell_progress program state abstract simulates running environment other agree head goals tail
              tailAbstract tasks abstractTasks tailRel
          | assign index expression =>
            exact .inl <| assign_progress program state abstract simulates running environment other agree index
              expression goals tail tailAbstract tasks abstractTasks tailRel
          | fail =>
            exact .inl <| fail_progress program state abstract simulates running environment other goals tail tailAbstract
              abstractTasks
      | scan active key values cursor below stored =>
        have ticked : tick (table program) state =
            scan active key values (keyAtsFrom program key cursor) tail state := by
          unfold tick
          rw [running, tasks]
        rw [ticked]
        rcases scan_progress program state abstract simulates running active key values cursor tail tailAbstract
            tasks abstractTasks below stored tailRel with moved | ⟨related', occurrence, after, frames, tasksEq, storeEq,
              less⟩
        · exact .inl moved
        · refine .inr ⟨related', ?_⟩
          simp only [admin, tasksEq, tasks, storeEq]
          exact less
      | search active key values cursor occurrence frames found atCursor matched below stored alive consumed
          enumerated rejected =>
        have ticked : tick (table program) state =
            search active key values occurrence (keyAtsFrom program key (cursor + 1)) frames tail state := by
          unfold tick
          rw [running, tasks]
        rw [ticked]
        rcases search_progress program state abstract simulates descending running active key values cursor occurrence
            frames found tail tailAbstract tasks abstractTasks atCursor matched below stored alive consumed enumerated
            rejected tailRel with moved | ⟨related', next, tasksEq, storeEq, less⟩
        · exact .inl moved
        · refine .inr ⟨related', ?_⟩
          simp only [admin, tasksEq, tasks, storeEq]
          exact less

#print axioms tick_progress

end Mettapedia.Languages.CHR.Machine
