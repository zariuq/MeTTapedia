import Mettapedia.Languages.CHR.TupleNormal

/-! Tuple normal form does not change behaviour. A refined step sees a
program and a state only through their normal forms: a program and state
with the same normal forms take a matching step to a state with the same
normal form. So a normalized program runs as the program from the same
initial constraints, with the same stores, failures and pending work, and
the same faults up to the normalized term that an `uninstantiated` fault
names. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.TupleNormal

def normalTask : Task → Task
  | .goals environment goals => .goals environment (goals.map normalGoal)
  | .scan active cursor => .scan active cursor

def normalStatus : Status → Status
  | .fault reason => .fault (normalFault reason)
  | other => other

def normalState (state : State) : State :=
  { state with tasks := state.tasks.map normalTask, status := normalStatus state.status }

def normalOutcome : Outcome → Outcome
  | .fault reason => .fault (normalFault reason)
  | other => other

/-! ## The program's static data -/

theorem visitOrder_normal (rule : Rule) : (normalRule rule).visitOrder = rule.visitOrder := by
  simp [Rule.visitOrder, normalRule]

theorem occurrences_normal (program : Program) : occurrences (normalProgram program) = occurrences program := by
  simp [occurrences, normalProgram, List.zipIdx_map, List.flatMap_map, visitOrder_normal]

theorem rules_normal (program : Program) (index : Nat) :
    (normalProgram program).rules[index]? = program.rules[index]?.map normalRule := by
  simp [normalProgram]

theorem rules_normal_some {program : Program} {index : Nat} {rule : Rule}
    (found : (normalProgram program).rules[index]? = some rule) :
    ∃ original, program.rules[index]? = some original ∧ normalRule original = rule := by
  rw [rules_normal] at found
  cases listed : program.rules[index]? with
  | none => simp [listed] at found
  | some original =>
    simp only [listed, Option.map_some, Option.some.injEq] at found
    exact ⟨original, rfl, found⟩

theorem forall₂_normalHead (environment : Environment) (heads : List Head) (occurrences : List Occurrence) :
    List.Forall₂ (fun head occurrence => head.instantiate environment = some occurrence.constraint)
        (heads.map normalHead) occurrences ↔
      List.Forall₂ (fun head occurrence => head.instantiate environment = some occurrence.constraint)
        heads occurrences := by
  rw [List.forall₂_map_left_iff]
  simp only [normalHead_instantiate]

theorem matches_normal (selection : Selection) (rule : Rule) (environment : Environment)
    (store : List Occurrence) :
    selection.Matches (normalRule rule) environment store ↔ selection.Matches rule environment store := by
  unfold Selection.Matches
  rw [normalRule_variables]
  simp only [normalRule, forall₂_normalHead]

theorem fresh_normal (selection : Selection) (rule : Rule) (index : Nat) (history : List Key) :
    selection.Fresh (normalRule rule) index history ↔ selection.Fresh rule index history := by
  simp [Selection.Fresh, normalRule]

theorem guardsEval_normal_ok (environment : Environment) (rule : Rule) (holds : Bool) :
    guardsEval environment (normalRule rule).guards = .ok holds ↔ guardsEval environment rule.guards = .ok holds := by
  simp only [normalRule, normalGuards_eval]
  cases guardsEval environment rule.guards <;> simp [Except.mapError]

theorem guardsEval_normal_error (environment : Environment) (rule : Rule) (reason : ArithmeticFault)
    (failed : guardsEval environment rule.guards = .error reason) :
    guardsEval environment (normalRule rule).guards = .error (normalFault reason) := by
  simp only [normalRule, normalGuards_eval, failed]
  rfl

theorem guardsEval_normal_error_inv (environment : Environment) (rule : Rule) (reason : ArithmeticFault)
    (failed : guardsEval environment (normalRule rule).guards = .error reason) :
    ∃ original, guardsEval environment rule.guards = .error original ∧ normalFault original = reason := by
  simp only [normalRule, normalGuards_eval] at failed
  cases computed : guardsEval environment rule.guards with
  | error original =>
    rw [computed] at failed
    simp only [Except.mapError, Except.error.injEq] at failed
    exact ⟨original, rfl, failed⟩
  | ok holds =>
    rw [computed] at failed
    simp [Except.mapError] at failed

theorem commit_normal (state : State) (rule : Rule) (index : Nat) (environment : Environment)
    (selection : Selection) (active cursor : Nat) (tail : List Task) :
    commit (normalState state) (normalRule rule) index environment selection active cursor (tail.map normalTask) =
      normalState (commit state rule index environment selection active cursor tail) := by
  unfold commit normalState
  by_cases consumed : selection.removed.any (fun occurrence => occurrence.id == active)
  · simp [consumed, normalRule, normalTask]
  · simp [consumed, normalRule, normalTask]

/-! ## Inverting normal forms -/

theorem map_normalTask_cons {tasks : List Task} {first : Task} {rest : List Task}
    (same : tasks.map normalTask = first :: rest) :
    ∃ task tail, tasks = task :: tail ∧ normalTask task = first ∧ tail.map normalTask = rest := by
  cases tasks with
  | nil => cases same
  | cons task tail => exact ⟨task, tail, rfl, (List.cons.inj same).1, (List.cons.inj same).2⟩

theorem normalTask_goals {task : Task} {environment : Environment} {goals : List Goal}
    (same : normalTask task = .goals environment goals) :
    ∃ original, task = .goals environment original ∧ original.map normalGoal = goals := by
  cases task with
  | goals environment' original =>
    simp only [normalTask, Task.goals.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    exact ⟨original, rfl, rfl⟩
  | scan => simp [normalTask] at same

theorem normalTask_scan {task : Task} {active cursor : Nat} (same : normalTask task = .scan active cursor) :
    task = .scan active cursor := by
  cases task with
  | goals => simp [normalTask] at same
  | scan => simpa [normalTask] using same

theorem map_normalGoal_cons {goals : List Goal} {first : Goal} {rest : List Goal}
    (same : goals.map normalGoal = first :: rest) :
    ∃ goal tail, goals = goal :: tail ∧ normalGoal goal = first ∧ tail.map normalGoal = rest := by
  cases goals with
  | nil => cases same
  | cons goal tail => exact ⟨goal, tail, rfl, (List.cons.inj same).1, (List.cons.inj same).2⟩

theorem map_normalGoal_nil {goals : List Goal} (same : goals.map normalGoal = []) : goals = [] :=
  List.map_eq_nil_iff.mp same

theorem normalGoal_tell {goal : Goal} {head : Head} (same : normalGoal goal = .tell head) :
    ∃ original, goal = .tell original ∧ normalHead original = head := by
  cases goal with
  | tell original =>
    simp only [normalGoal, Goal.tell.injEq] at same
    exact ⟨original, rfl, same⟩
  | assign => simp [normalGoal] at same
  | fail => simp [normalGoal] at same

theorem normalGoal_assign {goal : Goal} {index : Nat} {expression : IntExpr}
    (same : normalGoal goal = .assign index expression) : goal = .assign index expression := by
  cases goal with
  | tell => simp [normalGoal] at same
  | assign => simpa [normalGoal] using same
  | fail => simp [normalGoal] at same

theorem normalGoal_fail {goal : Goal} (same : normalGoal goal = .fail) : goal = .fail := by
  cases goal with
  | tell => simp [normalGoal] at same
  | assign => simp [normalGoal] at same
  | fail => rfl

theorem normalStatus_running {status : Status} (same : normalStatus status = .running) : status = .running := by
  cases status <;> simp [normalStatus] at same ⊢

/-! ## One step -/

/-- A step of a program is a step of its normal form between the normal forms. -/
theorem step_normal {program : Program} {state next : State} (step : Step program state next) :
    Step (normalProgram program) (normalState state) (normalState next) := by
  cases step with
  | endGoals environment tail tasks running =>
    exact .endGoals (normalState state) environment (tail.map normalTask)
      (by simp [normalState, tasks, normalTask]) (by simp [normalState, running, normalStatus])
  | introduce environment head goals tail constraint tasks running grounded =>
    exact .introduce (normalState state) environment (normalHead head) (goals.map normalGoal) (tail.map normalTask)
      constraint (by simp [normalState, tasks, normalTask, normalGoal]) (by simp [normalState, running, normalStatus])
      (by rw [normalHead_instantiate]; exact grounded)
  | tellFault environment head goals tail tasks running ungrounded =>
    exact .tellFault (normalState state) environment (normalHead head) (goals.map normalGoal) (tail.map normalTask)
      (by simp [normalState, tasks, normalTask, normalGoal]) (by simp [normalState, running, normalStatus])
      (by rw [normalHead_instantiate]; exact ungrounded)
  | assign environment index expression goals tail result tasks running evaluated compatible =>
    exact .assign (normalState state) environment index expression (goals.map normalGoal) (tail.map normalTask) result
      (by simp [normalState, tasks, normalTask, normalGoal]) (by simp [normalState, running, normalStatus])
      evaluated compatible
  | assignFailed environment index expression goals tail result old tasks running evaluated bound different =>
    exact .assignFailed (normalState state) environment index expression (goals.map normalGoal) (tail.map normalTask)
      result old (by simp [normalState, tasks, normalTask, normalGoal]) (by simp [normalState, running, normalStatus])
      evaluated bound different
  | assignFault environment index expression goals tail reason tasks running evaluated =>
    have fixed := intExpr_fault environment expression reason evaluated
    have step := Step.assignFault (program := normalProgram program) (normalState state) environment index
      expression (goals.map normalGoal) (tail.map normalTask) reason
      (by simp [normalState, tasks, normalTask, normalGoal]) (by simp [normalState, running, normalStatus]) evaluated
    show Step _ _ { normalState state with status := .fault (normalFault reason) }
    rw [fixed]
    exact step
  | fail environment goals tail tasks running =>
    exact .fail (normalState state) environment (goals.map normalGoal) (tail.map normalTask)
      (by simp [normalState, tasks, normalTask, normalGoal]) (by simp [normalState, running, normalStatus])
  | missingActive active cursor tail tasks running missing =>
    exact .missingActive (normalState state) active cursor (tail.map normalTask)
      (by simp [normalState, tasks, normalTask]) (by simp [normalState, running, normalStatus]) missing
  | endScan active cursor tail tasks running finished =>
    exact .endScan (normalState state) active cursor (tail.map normalTask)
      (by simp [normalState, tasks, normalTask]) (by simp [normalState, running, normalStatus])
      (by rw [occurrences_normal]; exact finished)
  | skip active cursor tail occurrence rule tasks running atCursor atRule unusable =>
    exact .skip (normalState state) active cursor (tail.map normalTask) occurrence (normalRule rule)
      (by simp [normalState, tasks, normalTask]) (by simp [normalState, running, normalStatus])
      (by rw [occurrences_normal]; exact atCursor) (by rw [rules_normal, atRule]; rfl)
      (fun environment selection matched activeHead => by
        rcases unusable environment selection ((matches_normal selection rule environment state.store).mp matched)
          activeHead with stale | rejected
        · exact .inl (by rwa [fresh_normal])
        · exact .inr ((guardsEval_normal_ok environment rule false).mpr rejected))
  | fire active cursor tail occurrence rule environment selection tasks running atCursor atRule matched
      activeHead fresh guarded =>
    have step := Step.fire (normalState state) active cursor (tail.map normalTask) occurrence (normalRule rule)
      environment selection (by simp [normalState, tasks, normalTask]) (by simp [normalState, running, normalStatus])
      (by rw [occurrences_normal]; exact atCursor) (by rw [rules_normal, atRule]; rfl)
      ((matches_normal selection rule environment state.store).mpr matched) activeHead
      ((fresh_normal selection rule occurrence.rule state.history).mpr fresh)
      ((guardsEval_normal_ok environment rule true).mpr guarded)
    rw [← commit_normal]
    exact step
  | guardFault active cursor tail occurrence rule environment selection reason tasks running atCursor atRule
      matched activeHead fresh fault =>
    exact .guardFault (normalState state) active cursor (tail.map normalTask) occurrence (normalRule rule)
      environment selection (normalFault reason) (by simp [normalState, tasks, normalTask])
      (by simp [normalState, running, normalStatus]) (by rw [occurrences_normal]; exact atCursor)
      (by rw [rules_normal, atRule]; rfl) ((matches_normal selection rule environment state.store).mpr matched)
      activeHead ((fresh_normal selection rule occurrence.rule state.history).mpr fresh)
      (guardsEval_normal_error environment rule reason fault)

/-- A step of a normalized program from a normalized state is the normal
form of a step of the program. -/
theorem step_reflect {program : Program} {state next : State}
    (step : Step (normalProgram program) (normalState state) next) :
    ∃ original, Step program state original ∧ next = normalState original := by
  generalize normalized : normalState state = source at step
  cases step with
  | endGoals environment tail tasks running =>
    subst normalized
    obtain ⟨first, rest, listed, firstSame, restSame⟩ := map_normalTask_cons tasks
    obtain ⟨goals, rfl, goalsSame⟩ := normalTask_goals firstSame
    subst restSame
    obtain rfl := map_normalGoal_nil goalsSame
    exact ⟨_, .endGoals state environment rest listed (normalStatus_running running), rfl⟩
  | introduce environment head goals tail constraint tasks running grounded =>
    subst normalized
    obtain ⟨first, rest, listed, firstSame, restSame⟩ := map_normalTask_cons tasks
    obtain ⟨originalGoals, rfl, goalsSame⟩ := normalTask_goals firstSame
    obtain ⟨goal, others, rfl, goalSame, othersSame⟩ := map_normalGoal_cons goalsSame
    obtain ⟨original, rfl, headSame⟩ := normalGoal_tell goalSame
    subst restSame othersSame headSame
    rw [normalHead_instantiate] at grounded
    exact ⟨_, .introduce state environment original others rest constraint listed (normalStatus_running running)
      grounded, rfl⟩
  | tellFault environment head goals tail tasks running ungrounded =>
    subst normalized
    obtain ⟨first, rest, listed, firstSame, restSame⟩ := map_normalTask_cons tasks
    obtain ⟨originalGoals, rfl, goalsSame⟩ := normalTask_goals firstSame
    obtain ⟨goal, others, rfl, goalSame, othersSame⟩ := map_normalGoal_cons goalsSame
    obtain ⟨original, rfl, headSame⟩ := normalGoal_tell goalSame
    subst restSame othersSame headSame
    rw [normalHead_instantiate] at ungrounded
    exact ⟨_, .tellFault state environment original others rest listed (normalStatus_running running) ungrounded, rfl⟩
  | assign environment index expression goals tail result tasks running evaluated compatible =>
    subst normalized
    obtain ⟨first, rest, listed, firstSame, restSame⟩ := map_normalTask_cons tasks
    obtain ⟨originalGoals, rfl, goalsSame⟩ := normalTask_goals firstSame
    obtain ⟨goal, others, rfl, goalSame, othersSame⟩ := map_normalGoal_cons goalsSame
    obtain rfl := normalGoal_assign goalSame
    subst restSame othersSame
    exact ⟨_, .assign state environment index expression others rest result listed (normalStatus_running running)
      evaluated compatible, rfl⟩
  | assignFailed environment index expression goals tail result old tasks running evaluated bound different =>
    subst normalized
    obtain ⟨first, rest, listed, firstSame, restSame⟩ := map_normalTask_cons tasks
    obtain ⟨originalGoals, rfl, goalsSame⟩ := normalTask_goals firstSame
    obtain ⟨goal, others, rfl, goalSame, othersSame⟩ := map_normalGoal_cons goalsSame
    obtain rfl := normalGoal_assign goalSame
    exact ⟨_, .assignFailed state environment index expression others rest result old listed
      (normalStatus_running running) evaluated bound different, rfl⟩
  | assignFault environment index expression goals tail reason tasks running evaluated =>
    subst normalized
    obtain ⟨first, rest, listed, firstSame, restSame⟩ := map_normalTask_cons tasks
    obtain ⟨originalGoals, rfl, goalsSame⟩ := normalTask_goals firstSame
    obtain ⟨goal, others, rfl, goalSame, othersSame⟩ := map_normalGoal_cons goalsSame
    obtain rfl := normalGoal_assign goalSame
    have fixed := intExpr_fault environment expression reason evaluated
    refine ⟨_, .assignFault state environment index expression others rest reason listed
      (normalStatus_running running) evaluated, ?_⟩
    show _ = { normalState state with status := .fault (normalFault reason) }
    rw [fixed]
  | fail environment goals tail tasks running =>
    subst normalized
    obtain ⟨first, rest, listed, firstSame, restSame⟩ := map_normalTask_cons tasks
    obtain ⟨originalGoals, rfl, goalsSame⟩ := normalTask_goals firstSame
    obtain ⟨goal, others, rfl, goalSame, othersSame⟩ := map_normalGoal_cons goalsSame
    obtain rfl := normalGoal_fail goalSame
    exact ⟨_, .fail state environment others rest listed (normalStatus_running running), rfl⟩
  | missingActive active cursor tail tasks running missing =>
    subst normalized
    obtain ⟨first, rest, listed, firstSame, restSame⟩ := map_normalTask_cons tasks
    obtain rfl := normalTask_scan firstSame
    subst restSame
    exact ⟨_, .missingActive state active cursor rest listed (normalStatus_running running) missing, rfl⟩
  | endScan active cursor tail tasks running finished =>
    subst normalized
    obtain ⟨first, rest, listed, firstSame, restSame⟩ := map_normalTask_cons tasks
    obtain rfl := normalTask_scan firstSame
    subst restSame
    rw [occurrences_normal] at finished
    exact ⟨_, .endScan state active cursor rest listed (normalStatus_running running) finished, rfl⟩
  | skip active cursor tail occurrence rule tasks running atCursor atRule unusable =>
    subst normalized
    obtain ⟨first, rest, listed, firstSame, restSame⟩ := map_normalTask_cons tasks
    obtain rfl := normalTask_scan firstSame
    subst restSame
    obtain ⟨original, found, rfl⟩ := rules_normal_some atRule
    rw [occurrences_normal] at atCursor
    refine ⟨_, .skip state active cursor rest occurrence original listed (normalStatus_running running) atCursor
      found (fun environment selection matched activeHead => ?_), rfl⟩
    rcases unusable environment selection ((matches_normal selection original environment state.store).mpr matched)
      activeHead with stale | rejected
    · exact .inl (by rwa [fresh_normal] at stale)
    · exact .inr ((guardsEval_normal_ok environment original false).mp rejected)
  | fire active cursor tail occurrence rule environment selection tasks running atCursor atRule matched
      activeHead fresh guarded =>
    subst normalized
    obtain ⟨first, rest, listed, firstSame, restSame⟩ := map_normalTask_cons tasks
    obtain rfl := normalTask_scan firstSame
    subst restSame
    obtain ⟨original, found, rfl⟩ := rules_normal_some atRule
    rw [occurrences_normal] at atCursor
    refine ⟨_, .fire state active cursor rest occurrence original environment selection listed
      (normalStatus_running running) atCursor found
      ((matches_normal selection original environment state.store).mp matched) activeHead
      ((fresh_normal selection original occurrence.rule state.history).mp fresh)
      ((guardsEval_normal_ok environment original true).mp guarded), ?_⟩
    exact commit_normal state original occurrence.rule environment selection active cursor rest
  | guardFault active cursor tail occurrence rule environment selection reason tasks running atCursor atRule
      matched activeHead fresh fault =>
    subst normalized
    obtain ⟨first, rest, listed, firstSame, restSame⟩ := map_normalTask_cons tasks
    obtain rfl := normalTask_scan firstSame
    subst restSame
    obtain ⟨original, found, rfl⟩ := rules_normal_some atRule
    rw [occurrences_normal] at atCursor
    obtain ⟨originalReason, faulted, rfl⟩ := guardsEval_normal_error_inv environment original reason fault
    exact ⟨_, .guardFault state active cursor rest occurrence original environment selection originalReason listed
      (normalStatus_running running) atCursor found
      ((matches_normal selection original environment state.store).mp matched) activeHead
      ((fresh_normal selection original occurrence.rule state.history).mp fresh) faulted, rfl⟩

/-! ## Runs and outcomes -/

/-- **Behaviour depends only on normal forms.** -/
theorem step_equivalent {first second : Program} (sameProgram : normalProgram first = normalProgram second)
    {state next other : State} (step : Step first state next) (sameState : normalState state = normalState other) :
    ∃ otherNext, Step second other otherNext ∧ normalState next = normalState otherNext := by
  have forward := step_normal step
  rw [sameProgram, sameState] at forward
  exact step_reflect forward

theorem steps_equivalent {first second : Program} (sameProgram : normalProgram first = normalProgram second)
    {state final other : State} (run : Relation.ReflTransGen (Step first) state final)
    (sameState : normalState state = normalState other) :
    ∃ otherFinal, Relation.ReflTransGen (Step second) other otherFinal ∧
      normalState final = normalState otherFinal := by
  induction run with
  | refl => exact ⟨other, .refl, sameState⟩
  | tail _ step reached =>
    obtain ⟨middle, run, sameMiddle⟩ := reached
    obtain ⟨next, step', sameNext⟩ := step_equivalent sameProgram step sameMiddle
    exact ⟨next, run.tail step', sameNext⟩

theorem observe_equivalent {state other : State} (same : normalState state = normalState other) :
    normalOutcome (observe state) = normalOutcome (observe other) := by
  have tasksSame : state.tasks.map normalTask = other.tasks.map normalTask := congrArg State.tasks same
  have storeSame : state.store = other.store := by
    have stores := congrArg State.store same
    exact stores
  have statusSame : normalStatus state.status = normalStatus other.status := congrArg State.status same
  have emptySame : state.tasks.isEmpty = other.tasks.isEmpty := by
    have lengths := congrArg List.length tasksSame
    simp only [List.length_map] at lengths
    cases listed : state.tasks <;> cases others : other.tasks <;> simp_all
  unfold observe
  cases first : state.status <;> cases second : other.status <;>
    simp_all [normalStatus, normalOutcome]

/-- A normalized program runs as the program, from the same initial
constraints. -/
theorem normal_runs (program : Program) (constraints : List Constraint) {final : State}
    (run : Relation.ReflTransGen (Step (normalProgram program)) (initial constraints) final) :
    ∃ original, Relation.ReflTransGen (Step program) (initial constraints) original ∧
      normalState final = normalState original ∧ normalOutcome (observe final) = normalOutcome (observe original) := by
  obtain ⟨original, reached, same⟩ := steps_equivalent (normalProgram_idem program) run rfl
  exact ⟨original, reached, same, observe_equivalent same⟩

theorem runs_normal (program : Program) (constraints : List Constraint) {final : State}
    (run : Relation.ReflTransGen (Step program) (initial constraints) final) :
    ∃ normalized, Relation.ReflTransGen (Step (normalProgram program)) (initial constraints) normalized ∧
      normalState final = normalState normalized ∧
        normalOutcome (observe final) = normalOutcome (observe normalized) := by
  obtain ⟨normalized, reached, same⟩ := steps_equivalent (normalProgram_idem program).symm run rfl
  exact ⟨normalized, reached, same, observe_equivalent same⟩

#print axioms step_normal
#print axioms step_reflect
#print axioms normal_runs
#print axioms runs_normal

end Mettapedia.Languages.CHR.TupleNormal
