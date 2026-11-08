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
  have abstractRunning : abstract.status = .running := statusRel_running (running ▸ simulates.status)
  have tailShallow : ∀ task ∈ tail, task.isSearch = false := by
    rw [← machineTasks]
    exact simulates.shallow
  unfold introduce
  cases instantiated : instantiateTerms environment head.arguments with
  | none =>
    dsimp only
    have otherNone : head.instantiate other = none := by
      unfold Head.instantiate
      rw [← instantiateTerms_eq, ← instantiateTerms_agree agree, instantiated]
      rfl
    refine ⟨{ abstract with status := .fault (.uninstantiated (.tuple head.arguments)) },
      Relation.TransGen.single (PolicyStep.tellFault abstract other head goals tailAbstract abstractTasks
        abstractRunning otherNone), ?_⟩
    exact ⟨simulates.store, simulates.coherent, simulates.fresh, simulates.history, simulates.next,
      .faulted _, (fun impossible => by simp at impossible), simulates.shallow⟩
  | some values =>
    dsimp only
    let key := Head.key head
    let added : Occurrence := ⟨state.next, ⟨head.name, values⟩⟩
    have arity : values.length = key.2 := by
      have length := mapM_length (by rw [← instantiateTerms_eq]; exact instantiated)
      simpa [key, Head.key] using length
    have freshId : state.next ∉ (contents state.store).map Occurrence.id := by
      intro inside
      obtain ⟨member, inStore, same⟩ := List.mem_map.mp inside
      have below := simulates.fresh member inStore
      omega
    obtain ⟨coherent', perm'⟩ := introduce_store state.store simulates.coherent key ⟨state.next, values⟩ freshId arity
    have liftAdded : lift key ⟨state.next, values⟩ = added := rfl
    have grown : ∀ member, member ∈ contents (put key (⟨state.next, values⟩ :: slot key state.store) state.store) ↔
        member ∈ contents state.store ∨ member = added := by
      intro member
      rw [perm'.mem_iff, List.mem_append, List.mem_singleton, liftAdded]
    have otherSome : head.instantiate other = some ⟨head.name, values⟩ := by
      unfold Head.instantiate
      rw [← instantiateTerms_eq, ← instantiateTerms_agree agree, instantiated]
      rfl
    refine ⟨{ abstract with
        tasks := .scan abstract.nextId 0 :: .goals other goals :: tailAbstract
        store := abstract.store ++ [⟨abstract.nextId, ⟨head.name, values⟩⟩]
        nextId := abstract.nextId + 1 },
      Relation.TransGen.single (PolicyStep.introduce abstract other head goals tailAbstract _ abstractTasks
        abstractRunning otherSome), ?_⟩
    have nextEq := simulates.next
    refine ⟨?_, coherent', ?_, simulates.history, by simp [nextEq], simulates.status, ?_, ?_⟩
    · show (abstract.store ++ [(⟨abstract.nextId, ⟨head.name, values⟩⟩ : Occurrence)]).Perm _
      rw [nextEq]
      exact (simulates.store.append_right _).trans perm'.symm
    · intro member inside
      rcases (grown member).mp inside with old | rfl
      · have below := simulates.fresh member old
        show member.id < state.next + 1
        omega
      · show state.next < state.next + 1
        omega
    · intro _
      show List.Forall₂ _ (Task.scan state.next key values (occurrencesOf key (table program)) :: resume :: tail)
        (CHR.Task.scan abstract.nextId 0 :: .goals other goals :: tailAbstract)
      rw [table_entry, nextEq]
      refine .cons (.scan state.next key values 0 (Nat.lt_succ_self state.next) ⟨arity, ?_⟩)
        (.cons (taskRel_grow resumeRel resumeNotSearch added rfl grown)
          (forall₂_grow added rfl grown tailRel tailShallow))
      intro member inside same
      rcases (grown member).mp inside with old | rfl
      · have below := simulates.fresh member old
        omega
      · rfl
    · intro task inside
      simp only [List.drop_succ_cons, List.drop_zero, List.mem_cons] at inside
      rcases inside with rfl | inTail
      · exact resumeNotSearch
      · exact tailShallow task inTail

theorem endGoals_progress (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (running : state.status = .running)
    (task : Task) (tail : List Task) (tasks : state.tasks = task :: tail)
    (environment : Environment) (tailAbstract : List CHR.Task)
    (abstractTasks : abstract.tasks = .goals environment [] :: tailAbstract)
    (tailRel : List.Forall₂ (TaskRel program state.store state.history state.next) tail tailAbstract) :
    ∃ abstract', Relation.TransGen (PolicyStep program) abstract abstract' ∧
      Simulates program { state with tasks := tail } abstract' := by
  have abstractRunning : abstract.status = .running := statusRel_running (running ▸ simulates.status)
  refine ⟨{ abstract with tasks := tailAbstract },
    .single (PolicyStep.endGoals abstract environment tailAbstract abstractTasks abstractRunning), ?_⟩
  exact ⟨simulates.store, simulates.coherent, simulates.fresh, simulates.history, simulates.next,
    simulates.status, fun _ => tailRel,
    fun other inside => tail_shallow simulates tasks other (List.mem_of_mem_drop inside)⟩

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
        abstract' :=
  introduce_progress program state abstract simulates running head [] [] (agree_refl []) (.seeds heads)
    (heads.map Goal.tell) tail tailAbstract (state.next :: state.seeds) abstractTasks (by rw [tasks]; rfl)
    (.seeds heads (fun seed member => ground seed (List.mem_cons_of_mem _ member))) rfl tailRel

theorem tell_progress (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (running : state.status = .running)
    (environment other : Environment) (agree : Agree environment other)
    (head : Head) (goals : List Goal) (tail : List Task) (tailAbstract : List CHR.Task)
    (tasks : state.tasks = .goals environment (.tell head :: goals) :: tail)
    (abstractTasks : abstract.tasks = .goals other (.tell head :: goals) :: tailAbstract)
    (tailRel : List.Forall₂ (TaskRel program state.store state.history state.next) tail tailAbstract) :
    ∃ abstract', Relation.TransGen (PolicyStep program) abstract abstract' ∧
      Simulates program (goal (table program) environment (.tell head) goals tail state) abstract' := by
  have unfolded : goal (table program) environment (.tell head) goals tail state =
      introduce (table program) head environment (.goals environment goals) state.tasks tail state state.seeds := by
    rw [tasks]
    rfl
  rw [unfolded]
  exact introduce_progress program state abstract simulates running head environment other agree
    (.goals environment goals) goals tail tailAbstract state.seeds abstractTasks (by rw [tasks]; rfl)
    (.goals environment other goals agree) rfl tailRel

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
  have abstractRunning : abstract.status = .running := statusRel_running (running ▸ simulates.status)
  have shallow := tail_shallow simulates tasks
  have evaluated := eval_agree agree expression
  have looked := agree index
  cases result : expression.eval environment with
  | error reason =>
    have stopped : goal (table program) environment (.assign index expression) goals tail state =
        { state with status := .faulted reason } := by
      simp only [goal, result]
    rw [stopped]
    refine ⟨{ abstract with status := .fault reason },
      .single (PolicyStep.assignFault abstract other index expression goals tailAbstract reason abstractTasks
        abstractRunning (by rw [← evaluated, result])), ?_⟩
    exact ⟨simulates.store, simulates.coherent, simulates.fresh, simulates.history, simulates.next,
      .faulted reason, (fun impossible => by simp at impossible), simulates.shallow⟩
  | ok value =>
    cases bound : lookup environment index with
    | none =>
      have extended : goal (table program) environment (.assign index expression) goals tail state =
          { state with tasks := .goals ((index, .integer value) :: environment) goals :: tail } := by
        simp only [goal, result, bound]
      rw [extended]
      refine ⟨{ abstract with tasks := .goals ((index, .integer value) :: other) goals :: tailAbstract },
        .single (PolicyStep.assign abstract other index expression goals tailAbstract value abstractTasks
          abstractRunning (by rw [← evaluated, result]) (.inl (by rw [← looked, bound]))), ?_⟩
      exact ⟨simulates.store, simulates.coherent, simulates.fresh, simulates.history, simulates.next,
        simulates.status, fun _ => .cons (.goals _ _ goals (agree_cons agree index _)) tailRel,
        fun task inside => shallow task (by simpa using inside)⟩
    | some old =>
      by_cases same : old = .integer value
      · have checked : goal (table program) environment (.assign index expression) goals tail state =
            { state with tasks := .goals environment goals :: tail } := by
          simp only [goal, result, bound, same, if_true]
        rw [checked]
        refine ⟨{ abstract with tasks := .goals ((index, .integer value) :: other) goals :: tailAbstract },
          .single (PolicyStep.assign abstract other index expression goals tailAbstract value abstractTasks
            abstractRunning (by rw [← evaluated, result]) (.inr (by rw [← looked, bound, same]))), ?_⟩
        have shadow : Agree environment ((index, .integer value) :: other) :=
          agree_shadow agree (by rw [bound, same])
        exact ⟨simulates.store, simulates.coherent, simulates.fresh, simulates.history, simulates.next,
          simulates.status, fun _ => .cons (.goals _ _ goals shadow) tailRel,
          fun task inside => shallow task (by simpa using inside)⟩
      · have failed : goal (table program) environment (.assign index expression) goals tail state =
            { state with status := .failed } := by
          simp only [goal, result, bound, same, if_false]
        rw [failed]
        refine ⟨{ abstract with status := .failed },
          .single (PolicyStep.assignFailed abstract other index expression goals tailAbstract value old abstractTasks
            abstractRunning (by rw [← evaluated, result]) (by rw [← looked, bound]) same), ?_⟩
        exact ⟨simulates.store, simulates.coherent, simulates.fresh, simulates.history, simulates.next,
          .failed, (fun impossible => by simp at impossible), simulates.shallow⟩

theorem fail_progress (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (running : state.status = .running)
    (environment other : Environment) (goals : List Goal) (tail : List Task) (tailAbstract : List CHR.Task)
    (abstractTasks : abstract.tasks = .goals other (.fail :: goals) :: tailAbstract) :
    ∃ abstract', Relation.TransGen (PolicyStep program) abstract abstract' ∧
      Simulates program (goal (table program) environment .fail goals tail state) abstract' := by
  have abstractRunning : abstract.status = .running := statusRel_running (running ▸ simulates.status)
  refine ⟨{ abstract with status := .failed },
    .single (PolicyStep.fail abstract other goals tailAbstract abstractTasks abstractRunning), ?_⟩
  show Simulates program { state with status := .failed } _
  exact ⟨simulates.store, simulates.coherent, simulates.fresh, simulates.history, simulates.next,
    .failed, (fun impossible => by simp at impossible), simulates.shallow⟩

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
