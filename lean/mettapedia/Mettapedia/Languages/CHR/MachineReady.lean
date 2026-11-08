import Mettapedia.Languages.CHR.Machine

/-! Machine states whose rule occurrences all have heads: every scanned or
searched occurrence lists at least one head, and every search frame has a
head to try. A program's occurrence table has this property, and every tick
keeps it. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

/-- A rule occurrence whose rule has at least one head. -/
def Headed (occurrence : At) : Prop := occurrence.body.kept ++ occurrence.body.removed ≠ []

/-- The rule occurrences a task still visits. -/
def Task.occurrences : Task → List At
  | .seeds _ => []
  | .goals _ _ => []
  | .scan _ _ _ remaining => remaining
  | .search _ _ _ occurrence after _ => occurrence :: after

/-- The frames of a search task. -/
def Task.frames : Task → List Frame
  | .search _ _ _ _ _ frames => frames
  | _ => []

/-- Every occurrence of the table has heads. -/
def TableHeaded (table : Table) : Prop := ∀ entry ∈ table, ∀ occurrence ∈ entry.2, Headed occurrence

/-- Every occurrence a task visits has heads, and every frame has a head. -/
def TaskReady (task : Task) : Prop :=
  (∀ occurrence ∈ task.occurrences, Headed occurrence) ∧ ∀ frame ∈ task.frames, frame.heads ≠ []

def Ready (state : State) : Prop := ∀ task ∈ state.tasks, TaskReady task

theorem occurrencesOf_mem {key : Key} : ∀ {table : Table} {occurrence : At},
    occurrence ∈ occurrencesOf key table → ∃ entry ∈ table, occurrence ∈ entry.2
  | [], _, inside => by simp [occurrencesOf] at inside
  | (other, occurrences) :: rest, occurrence, inside => by
    unfold occurrencesOf at inside
    by_cases same : other = key
    · simp only [same, if_true] at inside
      exact ⟨_, List.mem_cons_self, inside⟩
    · simp only [same, if_false] at inside
      obtain ⟨entry, member, found⟩ := occurrencesOf_mem inside
      exact ⟨entry, List.mem_cons_of_mem _ member, found⟩

/-- The table the preparer emits has heads at every occurrence. -/
theorem table_headed (program : Program) : TableHeaded (table program) := by
  intro entry inTable occurrence member
  unfold table at inTable
  obtain ⟨key, _, rfl⟩ := List.mem_map.mp inTable
  obtain ⟨source, _, built⟩ := List.mem_filterMap.mp member
  cases ruleAt : program.rules[source.rule]? with
  | none => simp [ruleAt] at built
  | some rule =>
    cases headAt : rule.heads[source.head]? with
    | none => simp [ruleAt, headAt] at built
    | some head =>
      by_cases same : Head.key head = key
      · simp only [ruleAt, headAt, same, Option.bind_eq_bind, Option.bind_some, if_true,
          Option.some.injEq] at built
        subst built
        intro empty
        have none : rule.heads = [] := empty
        rw [none] at headAt
        simp at headAt
      · simp [ruleAt, headAt, same] at built

theorem ready_tail {state : State} {task : Task} {tail : List Task} (ready : Ready state)
    (tasks : state.tasks = task :: tail) : ∀ other ∈ tail, TaskReady other := by
  intro other inside
  exact ready other (by rw [tasks]; exact List.mem_cons_of_mem _ inside)

theorem ready_head {state : State} {task : Task} {tail : List Task} (ready : Ready state)
    (tasks : state.tasks = task :: tail) : TaskReady task :=
  ready task (by rw [tasks]; exact List.mem_cons_self)

theorem plain_ready (task : Task) (occurrences : task.occurrences = []) (frames : task.frames = []) :
    TaskReady task :=
  ⟨by simp [occurrences], by simp [frames]⟩

theorem ready_cons {task : Task} {tail : List Task} (first : TaskReady task)
    (rest : ∀ other ∈ tail, TaskReady other) : ∀ other ∈ task :: tail, TaskReady other := by
  intro other inside
  rcases List.mem_cons.mp inside with rfl | later
  · exact first
  · exact rest other later

theorem introduce_ready (table : Table) (headed : TableHeaded table) (head : Head) (environment : Environment)
    (resume : Task) (original tail : List Task) (state : State) (seeds : List Nat)
    (originalReady : ∀ task ∈ original, TaskReady task) (resumeReady : TaskReady resume)
    (tailReady : ∀ task ∈ tail, TaskReady task) :
    Ready (introduce table head environment resume original tail state seeds) := by
  unfold introduce
  cases instantiateTerms environment head.arguments with
  | none => exact originalReady
  | some values =>
    apply ready_cons _ (ready_cons resumeReady tailReady)
    refine ⟨fun occurrence member => ?_, by simp [Task.frames]⟩
    obtain ⟨entry, inTable, found⟩ := occurrencesOf_mem member
    exact headed entry inTable occurrence found

theorem tick_ready (table : Table) (headed : TableHeaded table) (state : State) (ready : Ready state) :
    Ready (tick table state) := by
  unfold tick
  cases running : state.status with
  | failed => exact ready
  | faulted reason => exact ready
  | running =>
    cases tasks : state.tasks with
    | nil => exact ready
    | cons task tail =>
      have tailReady := ready_tail ready tasks
      have taskReady := ready_head ready tasks
      cases task with
      | seeds heads =>
        cases heads with
        | nil => exact tailReady
        | cons head heads =>
          exact introduce_ready table headed head [] (.seeds heads) _ tail state _
            (ready_cons taskReady tailReady) (plain_ready _ (by rfl) (by rfl)) tailReady
      | goals environment goals =>
        cases goals with
        | nil => exact tailReady
        | cons current goals =>
          cases current with
          | tell head =>
            exact introduce_ready table headed head environment (.goals environment goals) _ tail state _
              (ready_cons taskReady tailReady) (plain_ready _ (by rfl) (by rfl)) tailReady
          | assign index expression =>
            show Ready (goal table environment (.assign index expression) goals tail state)
            unfold goal
            dsimp only
            split
            · exact ready
            · split
              · exact ready_cons (plain_ready _ (by rfl) (by rfl)) tailReady
              · split
                · exact ready_cons (plain_ready _ (by rfl) (by rfl)) tailReady
                · exact ready
          | fail => exact ready
      | scan active key values remaining =>
        show Ready (scan active key values remaining tail state)
        unfold scan
        split
        · exact tailReady
        · cases remaining with
          | nil => exact tailReady
          | cons occurrence after =>
            dsimp only
            have occurrencesReady := taskReady.1
            cases heads : occurrence.body.kept ++ occurrence.body.removed with
            | nil => exact absurd heads (occurrencesReady occurrence List.mem_cons_self)
            | cons first later =>
              apply ready_cons _ tailReady
              refine ⟨occurrencesReady, ?_⟩
              intro frame inside
              simp only [Task.frames, List.mem_singleton] at inside
              subst inside
              simp
      | search active key values occurrence after frames =>
        show Ready (search active key values occurrence after frames tail state)
        have occurrencesReady := taskReady.1
        have framesReady := taskReady.2
        simp only [Task.occurrences, Task.frames] at occurrencesReady framesReady
        unfold search
        cases frames with
        | nil =>
          apply ready_cons _ tailReady
          refine ⟨fun other member => occurrencesReady other (List.mem_cons_of_mem _ member), by simp [Task.frames]⟩
        | cons frame below =>
          obtain ⟨index, heads, candidates, environment, picks, used⟩ := frame
          dsimp only
          have frameReady := framesReady _ List.mem_cons_self
          have belowReady : ∀ other ∈ below, other.heads ≠ [] :=
            fun other member => framesReady other (List.mem_cons_of_mem _ member)
          cases candidates with
          | nil =>
            apply ready_cons _ tailReady
            exact ⟨occurrencesReady, belowReady⟩
          | cons candidate others =>
            dsimp only
            have stay : TaskReady (.search active key values occurrence after
                (⟨index, heads, others, environment, picks, used⟩ :: below)) := by
              refine ⟨occurrencesReady, ?_⟩
              intro other member
              rcases List.mem_cons.mp member with rfl | later
              · exact frameReady
              · exact belowReady other later
            split
            · exact ready_cons stay tailReady
            · cases heads with
              | nil => exact ready_cons stay tailReady
              | cons head later =>
                dsimp only
                cases matchTerms head.arguments candidate.values environment with
                | none => exact ready_cons stay tailReady
                | some bound =>
                  dsimp only
                  cases later with
                  | nil =>
                    unfold complete
                    dsimp only
                    split
                    · exact ready_cons stay tailReady
                    · cases guardsEval bound occurrence.body.guards with
                      | error reason => exact ready_cons stay tailReady
                      | ok holds =>
                        cases holds with
                        | true =>
                          unfold fire
                          dsimp only
                          apply ready_cons (plain_ready _ (by rfl) (by rfl))
                          split
                          · exact tailReady
                          · exact ready_cons ⟨occurrencesReady, by simp [Task.frames]⟩ tailReady
                        | false => exact ready_cons stay tailReady
                  | cons nextHead rest =>
                    apply ready_cons _ tailReady
                    refine ⟨occurrencesReady, ?_⟩
                    intro other member
                    rcases List.mem_cons.mp member with rfl | inStay
                    · simp
                    · exact stay.2 other inStay

theorem start_ready (seeds : List Head) : Ready (start seeds) := by
  intro task inside
  simp only [start, List.mem_singleton] at inside
  subst inside
  exact plain_ready _ (by rfl) (by rfl)

#print axioms table_headed
#print axioms tick_ready

end Mettapedia.Languages.CHR.Machine
