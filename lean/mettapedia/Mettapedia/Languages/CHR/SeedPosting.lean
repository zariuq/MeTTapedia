import Mettapedia.Languages.CHR.Operational

/-! Posting initial constraints under the refined relation. The initial
constraints are told from one bottom goal task, in order. That task stays at
the bottom until its last constraint is told, and it is the only task exactly
when its next constraint is introduced. The introduction gives that
constraint the state's next identifier.

A package that records `nextId` whenever the task list is a single goal task
starting with a tell therefore records, in posting order, the identifier of
every initial constraint posted so far. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.SeedPosting

def tells (seeds : List Constraint) : List Goal := seeds.map (Goal.tell ∘ Constraint.asHead)

/-- States reachable from posting `seeds` by refined steps. -/
inductive Reach (program : Program) (seeds : List Constraint) : State → Prop
  | start : Reach program seeds (initial seeds)
  | step {first second : State} :
      Reach program seeds first → Step program first second → Reach program seeds second

/-- The unposted suffix of the seeds is the bottom goal task, until every
seed has been posted and that task has been finished. -/
def Posting (seeds : List Constraint) (state : State) : Prop :=
  state.tasks = [] ∨ ∃ posted above, posted ≤ seeds.length ∧
    state.tasks = above ++ [.goals [] (tells (seeds.drop posted))]

theorem tells_drop_cons {seeds : List Constraint} {posted : Nat} {goal : Goal} {rest : List Goal}
    (split : tells (seeds.drop posted) = goal :: rest) :
    ∃ seed, seeds[posted]? = some seed ∧ goal = .tell seed.asHead ∧
      rest = tells (seeds.drop (posted + 1)) ∧ posted + 1 ≤ seeds.length := by
  unfold tells at split
  cases dropped : seeds.drop posted with
  | nil => simp [dropped] at split
  | cons seed tail =>
    rw [dropped] at split
    simp only [List.map_cons, Function.comp, List.cons.injEq] at split
    have lengthBound : posted < seeds.length := by
      by_contra outside
      have empty : seeds.drop posted = [] := List.drop_eq_nil_of_le (by omega)
      simp [empty] at dropped
    refine ⟨seed, ?_, split.1.symm, ?_, by omega⟩
    · rw [← List.head?_drop, dropped]
      rfl
    · rw [← List.drop_drop, dropped]
      simp [tells, split.2]

theorem tells_not_assign {seeds : List Constraint} {index : Nat} {expression : IntExpr}
    {rest : List Goal} : tells seeds ≠ .assign index expression :: rest := by
  intro same
  cases seeds with
  | nil => simp [tells] at same
  | cons seed tail => simp [tells] at same

theorem tells_not_fail {seeds : List Constraint} {rest : List Goal} : tells seeds ≠ .fail :: rest := by
  intro same
  cases seeds with
  | nil => simp [tells] at same
  | cons seed tail => simp [tells] at same

theorem tells_nil_of_drop {seeds : List Constraint} {posted : Nat}
    (empty : tells (seeds.drop posted) = []) : seeds.drop posted = [] := by
  simpa [tells] using empty

theorem initial_posting (seeds : List Constraint) : Posting seeds (initial seeds) :=
  .inr ⟨0, [], Nat.zero_le _, by simp [initial, tells]⟩

/-- Every refined step keeps the unposted seeds as the bottom task. -/
theorem step_posting {program : Program} {seeds : List Constraint} {first second : State}
    (posting : Posting seeds first) (step : Step program first second) : Posting seeds second := by
  rcases posting with empty | ⟨posted, above, bound, tasks⟩
  · cases step <;> simp_all
  cases step with
  | endGoals environment tail current running =>
    rw [tasks] at current
    cases above with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Task.goals.injEq] at current
      left
      exact current.2.symm
    | cons top rest =>
      simp only [List.cons_append, List.cons.injEq] at current
      exact .inr ⟨posted, rest, bound, current.2.symm⟩
  | introduce environment head goals tail constraint current running grounded =>
    rw [tasks] at current
    cases above with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Task.goals.injEq] at current
      obtain ⟨⟨environmentEmpty, split⟩, tailEmpty⟩ := current
      obtain ⟨seed, _, _, rest, nextBound⟩ := tells_drop_cons split
      right
      refine ⟨posted + 1, [.scan first.nextId 0], nextBound, ?_⟩
      simp only [← tailEmpty, ← environmentEmpty, rest, List.cons_append, List.nil_append]
    | cons top above =>
      simp only [List.cons_append, List.cons.injEq] at current
      right
      refine ⟨posted, .scan first.nextId 0 :: .goals environment goals :: above, bound, ?_⟩
      simp [current.2]
  | tellFault environment head goals tail current running ungrounded =>
    exact .inr ⟨posted, above, bound, by simpa using tasks⟩
  | assign environment index expression goals tail result current running evaluated compatible =>
    rw [tasks] at current
    cases above with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Task.goals.injEq] at current
      exact absurd current.1.2 (fun same => tells_not_assign same)
    | cons top above =>
      simp only [List.cons_append, List.cons.injEq] at current
      right
      refine ⟨posted, .goals ((index, .integer result) :: environment) goals :: above, bound, ?_⟩
      simp [current.2]
  | assignFailed environment index expression goals tail result old current running evaluated bound' different =>
    exact .inr ⟨posted, above, bound, by simpa using tasks⟩
  | assignFault environment index expression goals tail reason current running evaluated =>
    exact .inr ⟨posted, above, bound, by simpa using tasks⟩
  | fail environment goals tail current running =>
    exact .inr ⟨posted, above, bound, by simpa using tasks⟩
  | missingActive active cursor tail current running missing =>
    rw [tasks] at current
    cases above with
    | nil => simp at current
    | cons top above =>
      simp only [List.cons_append, List.cons.injEq] at current
      exact .inr ⟨posted, above, bound, current.2.symm⟩
  | endScan active cursor tail current running finished =>
    rw [tasks] at current
    cases above with
    | nil => simp at current
    | cons top above =>
      simp only [List.cons_append, List.cons.injEq] at current
      exact .inr ⟨posted, above, bound, current.2.symm⟩
  | skip active cursor tail occurrence rule current running atCursor atRule unusable =>
    rw [tasks] at current
    cases above with
    | nil => simp at current
    | cons top above =>
      simp only [List.cons_append, List.cons.injEq] at current
      right
      refine ⟨posted, .scan active (cursor + 1) :: above, bound, ?_⟩
      simp [current.2]
  | fire active cursor tail occurrence rule environment selection current running atCursor atRule
      matched activeHead fresh guarded =>
    rw [tasks] at current
    cases above with
    | nil => simp at current
    | cons top above =>
      simp only [List.cons_append, List.cons.injEq] at current
      right
      unfold commit
      split
      · exact ⟨posted, .goals environment rule.body :: above, bound, by simp [current.2]⟩
      · exact ⟨posted, .goals environment rule.body :: .scan active cursor :: above, bound, by simp [current.2]⟩
  | guardFault active cursor tail occurrence rule environment selection reason current running atCursor
      atRule matched activeHead fresh fault =>
    exact .inr ⟨posted, above, bound, by simpa using tasks⟩

theorem reach_posting {program : Program} {seeds : List Constraint} {state : State}
    (reach : Reach program seeds state) : Posting seeds state := by
  induction reach with
  | start => exact initial_posting seeds
  | step _ step posting => exact step_posting posting step

/-- A single goal task that starts with a tell is the seed task: it tells the
next unposted seed, from the empty environment. -/
theorem sole_task_is_seed {program : Program} {seeds : List Constraint} {state : State}
    {environment : Environment} {head : Head} {rest : List Goal}
    (reach : Reach program seeds state)
    (sole : state.tasks = [.goals environment (.tell head :: rest)]) :
    environment = [] ∧ ∃ posted seed, seeds[posted]? = some seed ∧ head = seed.asHead ∧
      rest = tells (seeds.drop (posted + 1)) := by
  rcases reach_posting reach with empty | ⟨posted, above, _, tasks⟩
  · simp [empty] at sole
  rw [sole] at tasks
  cases above with
  | nil =>
    simp only [List.nil_append, List.cons.injEq, Task.goals.injEq, and_true] at tasks
    obtain ⟨environmentEmpty, split⟩ := tasks
    obtain ⟨seed, found, told, remaining, _⟩ := tells_drop_cons split.symm
    exact ⟨environmentEmpty, posted, seed, found, by simpa using told, remaining⟩
  | cons top above =>
    have lengths := congrArg List.length tasks
    simp at lengths

theorem values_instantiate (environment : Environment) :
    ∀ values : List Value, (values.map Term.value).mapM (Term.instantiate environment) = some values
  | [] => rfl
  | first :: rest => by
    simp only [List.map_cons, List.mapM_cons, Term.instantiate, values_instantiate environment rest]
    rfl

theorem asHead_instantiate (constraint : Constraint) (environment : Environment) :
    constraint.asHead.instantiate environment = some constraint := by
  cases constraint with
  | mk name arguments =>
    simp only [Constraint.asHead, Head.instantiate, values_instantiate environment arguments]
    rfl

/-- The step from that state introduces the seed with the state's next
identifier and leaves the rest of the seed task below the new scan. -/
theorem seed_introduction {program : Program} {seeds : List Constraint} {first second : State}
    {environment : Environment} {head : Head} {rest : List Goal}
    (reach : Reach program seeds first)
    (sole : first.tasks = [.goals environment (.tell head :: rest)]) (step : Step program first second) :
    ∃ posted seed, seeds[posted]? = some seed ∧
      second.store = first.store ++ [⟨first.nextId, seed⟩] ∧ second.nextId = first.nextId + 1 ∧
      second.tasks = [.scan first.nextId 0, .goals [] (tells (seeds.drop (posted + 1)))] := by
  obtain ⟨environmentEmpty, posted, seed, found, told, remaining⟩ := sole_task_is_seed reach sole
  cases step with
  | introduce environment' head' goals tail constraint current running grounded =>
    rw [sole] at current
    simp only [List.cons.injEq, Task.goals.injEq, Goal.tell.injEq] at current
    obtain ⟨⟨environmentSame, headSame, goalsSame⟩, tailEmpty⟩ := current
    rw [← headSame, told, asHead_instantiate] at grounded
    obtain rfl := Option.some.inj grounded
    refine ⟨posted, seed, found, rfl, rfl, ?_⟩
    simp [← environmentSame, environmentEmpty, ← goalsSame, remaining, ← tailEmpty]
  | tellFault environment' head' goals tail current running ungrounded =>
    rw [sole] at current
    simp only [List.cons.injEq, Task.goals.injEq, Goal.tell.injEq] at current
    obtain ⟨⟨_, headSame, _⟩, _⟩ := current
    rw [← headSame, told, asHead_instantiate] at ungrounded
    cases ungrounded
  | endGoals environment' tail current running => simp [sole] at current
  | assign environment' index expression goals tail result current => simp [sole] at current
  | assignFailed environment' index expression goals tail result old current => simp [sole] at current
  | assignFault environment' index expression goals tail reason current => simp [sole] at current
  | fail environment' goals tail current => simp [sole] at current
  | missingActive active cursor tail current => simp [sole] at current
  | endScan active cursor tail current => simp [sole] at current
  | skip active cursor tail occurrence rule current => simp [sole] at current
  | fire active cursor tail occurrence rule environment' selection current => simp [sole] at current
  | guardFault active cursor tail occurrence rule environment' selection reason current =>
    simp [sole] at current

#print axioms reach_posting
#print axioms sole_task_is_seed
#print axioms seed_introduction

end Mettapedia.Languages.CHR.SeedPosting
