import Mettapedia.Languages.CHR.MachineRefinement

/-! Goal-list ticks. Finishing a seed or goal list ends the operational goal
task; a seed or a tell introduces a constraint; an assignment binds, checks
or faults; `fail` fails. Bindings agree up to `lookup`, so each tick is the
operational step on the related environment. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

/-- Below the first task there is no search. -/
theorem tail_shallow {program : Program} {state : State} {abstract : CHR.State}
    (simulates : Simulates program state abstract) {task : Task} {tail : List Task}
    (tasks : state.tasks = task :: tail) : ∀ other ∈ tail, other.isSearch = false := by
  intro other inside
  apply simulates.shallow
  rw [tasks]
  simpa using inside

theorem agree_shadow {environment other : Environment} (same : Agree environment other) {index : Nat}
    {value : Value} (bound : lookup environment index = some value) :
    Agree environment ((index, value) :: other) := by
  intro looked
  rw [lookup_cons]
  by_cases here : index = looked
  · subst here
    rw [if_pos rfl, bound]
  · rw [if_neg here, same looked]

theorem endGoals_simulates (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (running : state.status = .running)
    (task : Task) (tail : List Task) (tasks : state.tasks = task :: tail)
    (environment : Environment) (tailAbstract : List CHR.Task)
    (abstractTasks : abstract.tasks = .goals environment [] :: tailAbstract)
    (tailRel : List.Forall₂ (TaskRel program state.store state.history state.next) tail tailAbstract) :
    ∃ abstract', Relation.ReflTransGen (Step program) abstract abstract' ∧
      Simulates program { state with tasks := tail } abstract' := by
  have abstractRunning : abstract.status = .running := statusRel_running (running ▸ simulates.status)
  refine ⟨{ abstract with tasks := tailAbstract },
    .single (Step.endGoals abstract environment tailAbstract abstractTasks abstractRunning), ?_⟩
  exact ⟨simulates.store, simulates.coherent, simulates.fresh, simulates.history, simulates.next,
    simulates.status, fun _ => tailRel,
    fun other inside => tail_shallow simulates tasks other (List.mem_of_mem_drop inside)⟩

theorem seed_simulates (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (running : state.status = .running)
    (head : Head) (heads : List Head) (tail : List Task) (tailAbstract : List CHR.Task)
    (tasks : state.tasks = .seeds (head :: heads) :: tail)
    (abstractTasks : abstract.tasks = .goals [] ((head :: heads).map Goal.tell) :: tailAbstract)
    (ground : ∀ seed ∈ head :: heads, (instantiateTerms [] seed.arguments).isSome)
    (tailRel : List.Forall₂ (TaskRel program state.store state.history state.next) tail tailAbstract) :
    ∃ abstract', Relation.ReflTransGen (Step program) abstract abstract' ∧
      Simulates program
        (introduce (table program) head [] (.seeds heads) state.tasks tail state (state.next :: state.seeds))
        abstract' :=
  introduce_simulates program state abstract simulates running head [] [] (agree_refl []) (.seeds heads)
    (heads.map Goal.tell) tail tailAbstract (state.next :: state.seeds) abstractTasks (by rw [tasks]; rfl)
    (.seeds heads (fun seed member => ground seed (List.mem_cons_of_mem _ member))) rfl tailRel

theorem tell_simulates (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (running : state.status = .running)
    (environment other : Environment) (agree : Agree environment other)
    (head : Head) (goals : List Goal) (tail : List Task) (tailAbstract : List CHR.Task)
    (tasks : state.tasks = .goals environment (.tell head :: goals) :: tail)
    (abstractTasks : abstract.tasks = .goals other (.tell head :: goals) :: tailAbstract)
    (tailRel : List.Forall₂ (TaskRel program state.store state.history state.next) tail tailAbstract) :
    ∃ abstract', Relation.ReflTransGen (Step program) abstract abstract' ∧
      Simulates program (goal (table program) environment (.tell head) goals tail state) abstract' := by
  have unfolded : goal (table program) environment (.tell head) goals tail state =
      introduce (table program) head environment (.goals environment goals) state.tasks tail state state.seeds := by
    rw [tasks]
    rfl
  rw [unfolded]
  exact introduce_simulates program state abstract simulates running head environment other agree
    (.goals environment goals) goals tail tailAbstract state.seeds abstractTasks (by rw [tasks]; rfl)
    (.goals environment other goals agree) rfl tailRel

theorem assign_simulates (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (running : state.status = .running)
    (environment other : Environment) (agree : Agree environment other)
    (index : Nat) (expression : IntExpr) (goals : List Goal) (tail : List Task) (tailAbstract : List CHR.Task)
    (tasks : state.tasks = .goals environment (.assign index expression :: goals) :: tail)
    (abstractTasks : abstract.tasks = .goals other (.assign index expression :: goals) :: tailAbstract)
    (tailRel : List.Forall₂ (TaskRel program state.store state.history state.next) tail tailAbstract) :
    ∃ abstract', Relation.ReflTransGen (Step program) abstract abstract' ∧
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
      .single (Step.assignFault abstract other index expression goals tailAbstract reason abstractTasks
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
        .single (Step.assign abstract other index expression goals tailAbstract value abstractTasks
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
          .single (Step.assign abstract other index expression goals tailAbstract value abstractTasks
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
          .single (Step.assignFailed abstract other index expression goals tailAbstract value old abstractTasks
            abstractRunning (by rw [← evaluated, result]) (by rw [← looked, bound]) same), ?_⟩
        exact ⟨simulates.store, simulates.coherent, simulates.fresh, simulates.history, simulates.next,
          .failed, (fun impossible => by simp at impossible), simulates.shallow⟩

theorem fail_simulates (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (running : state.status = .running)
    (environment other : Environment) (goals : List Goal) (tail : List Task) (tailAbstract : List CHR.Task)
    (abstractTasks : abstract.tasks = .goals other (.fail :: goals) :: tailAbstract) :
    ∃ abstract', Relation.ReflTransGen (Step program) abstract abstract' ∧
      Simulates program (goal (table program) environment .fail goals tail state) abstract' := by
  have abstractRunning : abstract.status = .running := statusRel_running (running ▸ simulates.status)
  refine ⟨{ abstract with status := .failed },
    .single (Step.fail abstract other goals tailAbstract abstractTasks abstractRunning), ?_⟩
  show Simulates program { state with status := .failed } _
  exact ⟨simulates.store, simulates.coherent, simulates.fresh, simulates.history, simulates.next,
    .failed, (fun impossible => by simp at impossible), simulates.shallow⟩

#print axioms endGoals_simulates
#print axioms seed_simulates
#print axioms tell_simulates
#print axioms assign_simulates
#print axioms fail_simulates

end Mettapedia.Languages.CHR.Machine
